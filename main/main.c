/*
 * SPDX-FileCopyrightText: 2010-2022 Espressif Systems (Shanghai) CO LTD
 *
 * SPDX-License-Identifier: CC0-1.0
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <inttypes.h>
#include <stdarg.h>
#include <assert.h>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/semphr.h"

#include "esp_log.h"
#include "esp_system.h"
#include "esp_err.h"
#include "esp_event.h"
#include "esp_netif.h"
#include "esp_wifi.h"
#include "esp_http_server.h"
#include "esp_timer.h"
#include "esp_rom_sys.h"
#include "lwip/ip4_addr.h"

#include "nvs_flash.h"
#include "nvs.h"

#include "driver/ledc.h"
#include "driver/gpio.h"

#define WIFI_SSID "node_led"
#define WIFI_PASS "node12345"

#define WIFI_AP_IP1 192
#define WIFI_AP_IP2 168
#define WIFI_AP_IP3 4
#define WIFI_AP_IP4 1

#define GPIO_DS1302_CE   27
#define GPIO_DS1302_IO   26
#define GPIO_DS1302_SCLK 25

#define GPIO_PWM_RED  18
#define GPIO_PWM_BLUE 19
#define GPIO_BOOT_BTN 0
#define GPIO_STATUS_LED 2

#define LEDC_TIMER_RESOLUTION LEDC_TIMER_12_BIT
#define LEDC_MAX_DUTY ((1 << LEDC_TIMER_RESOLUTION) - 1)
#define PWM_SCALE 100
#define HTML_BUF_SIZE 8192

#define SETTINGS_MAGIC_V1 0x4C45444E /* "LEDN" */
#define SETTINGS_MAGIC_V2 0x4C454432 /* "LED2" */

typedef struct {
    uint32_t magic;
    uint8_t on_hour;
    uint8_t on_min;
    uint8_t off_hour;
    uint8_t off_min;
    uint8_t on2_hour;
    uint8_t on2_min;
    uint8_t off2_hour;
    uint8_t off2_min;
    uint8_t red_pct;
    uint8_t blue_pct;
    uint16_t pwm_freq_hz;
    uint16_t ramp_sec;
} settings_t;

typedef struct {
    int year;
    int month;
    int day;
    int hour;
    int min;
    int sec;
    int dow;
} rtc_time_t;

static const char *TAG = "node_led";

static settings_t g_settings;
static SemaphoreHandle_t g_settings_mutex;
static SemaphoreHandle_t g_rtc_mutex;
static SemaphoreHandle_t g_test_mutex;

static int32_t g_actual_red = 0;
static int32_t g_actual_blue = 0;
static int64_t g_test_start_us = 0;
static int64_t g_test_until_us = 0;
static int g_test_stage = -1;

#define TEST_STEP_SEC 3
#define TEST_TOTAL_SEC (TEST_STEP_SEC * 2)
#define WEB_IDLE_TIMEOUT_SEC 300
#define WEB_LONG_PRESS_SEC 5

static httpd_handle_t g_http_server = NULL;
static esp_netif_t *g_ap_netif = NULL;
static bool g_wifi_inited = false;
static int64_t g_last_http_activity_us = 0;
static bool g_web_active = false;
static portMUX_TYPE g_activity_mux = portMUX_INITIALIZER_UNLOCKED;

static void ds1302_delay(void)
{
    esp_rom_delay_us(2);
}

static void ds1302_ce(int level)
{
    gpio_set_level(GPIO_DS1302_CE, level);
}

static void ds1302_sclk(int level)
{
    gpio_set_level(GPIO_DS1302_SCLK, level);
}

static void ds1302_io_out(void)
{
    gpio_set_direction(GPIO_DS1302_IO, GPIO_MODE_OUTPUT);
}

static void ds1302_io_in(void)
{
    gpio_set_direction(GPIO_DS1302_IO, GPIO_MODE_INPUT);
}

static void ds1302_write_byte(uint8_t value)
{
    ds1302_io_out();
    for (int i = 0; i < 8; i++) {
        gpio_set_level(GPIO_DS1302_IO, value & 0x01);
        ds1302_delay();
        ds1302_sclk(1);
        ds1302_delay();
        ds1302_sclk(0);
        ds1302_delay();
        value >>= 1;
    }
}

static uint8_t ds1302_read_byte(void)
{
    uint8_t value = 0;
    ds1302_io_in();
    for (int i = 0; i < 8; i++) {
        value |= (gpio_get_level(GPIO_DS1302_IO) & 0x01) << i;
        ds1302_delay();
        ds1302_sclk(1);
        ds1302_delay();
        ds1302_sclk(0);
        ds1302_delay();
    }
    return value;
}

static void ds1302_write_reg(uint8_t reg, uint8_t value)
{
    ds1302_ce(1);
    ds1302_delay();
    ds1302_write_byte(reg & 0xFE);
    ds1302_write_byte(value);
    ds1302_ce(0);
    ds1302_delay();
}

static uint8_t ds1302_read_reg(uint8_t reg)
{
    uint8_t value;
    ds1302_ce(1);
    ds1302_delay();
    ds1302_write_byte(reg | 0x01);
    value = ds1302_read_byte();
    ds1302_ce(0);
    ds1302_delay();
    return value;
}

static void ds1302_read_burst(uint8_t *data, size_t len)
{
    ds1302_ce(1);
    ds1302_delay();
    ds1302_write_byte(0xBF); /* clock burst read */
    for (size_t i = 0; i < len; i++) {
        data[i] = ds1302_read_byte();
    }
    ds1302_ce(0);
    ds1302_delay();
}

static uint8_t bin2bcd(uint8_t value)
{
    return (uint8_t)(((value / 10) << 4) | (value % 10));
}

static uint8_t bcd2bin(uint8_t value)
{
    return (uint8_t)(((value >> 4) * 10) + (value & 0x0F));
}

static int calc_dow(int y, int m, int d)
{
    static const int t[] = { 0, 3, 2, 5, 0, 3, 5, 1, 4, 6, 2, 4 };
    if (m < 3) {
        y -= 1;
    }
    int dow = (y + y / 4 - y / 100 + y / 400 + t[m - 1] + d) % 7; /* 0=Sunday */
    return (dow == 0) ? 1 : (dow + 1); /* 1..7 */
}

static bool is_leap_year(int y)
{
    return ((y % 4 == 0) && (y % 100 != 0)) || (y % 400 == 0);
}

static int days_in_month(int y, int m)
{
    static const int days[] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 };
    if (m == 2 && is_leap_year(y)) {
        return 29;
    }
    return days[m - 1];
}

static void ds1302_init(void)
{
    gpio_config_t io_conf = {
        .pin_bit_mask = (1ULL << GPIO_DS1302_CE) | (1ULL << GPIO_DS1302_SCLK) | (1ULL << GPIO_DS1302_IO),
        .mode = GPIO_MODE_OUTPUT,
        .pull_up_en = GPIO_PULLUP_DISABLE,
        .pull_down_en = GPIO_PULLDOWN_DISABLE,
        .intr_type = GPIO_INTR_DISABLE,
    };
    gpio_config(&io_conf);

    ds1302_ce(0);
    ds1302_sclk(0);
    ds1302_io_out();
}

static bool ds1302_get_time(rtc_time_t *t)
{
    uint8_t data[8] = {0};
    ds1302_read_burst(data, sizeof(data));

    uint8_t sec = data[0];
    uint8_t min = data[1];
    uint8_t hour = data[2];
    uint8_t date = data[3];
    uint8_t month = data[4];
    uint8_t day = data[5];
    uint8_t year = data[6];

    if (sec & 0x80) {
        sec &= 0x7F;
        ds1302_write_reg(0x80, sec);
    }

    if (hour & 0x80) {
        int pm = hour & 0x20;
        hour = bcd2bin(hour & 0x1F);
        if (pm && hour < 12) {
            hour += 12;
        } else if (!pm && hour == 12) {
            hour = 0;
        }
    } else {
        hour = bcd2bin(hour & 0x3F);
    }

    t->sec = bcd2bin(sec & 0x7F);
    t->min = bcd2bin(min & 0x7F);
    t->hour = hour;
    t->day = bcd2bin(date & 0x3F);
    t->month = bcd2bin(month & 0x1F);
    t->dow = bcd2bin(day & 0x07);
    t->year = 2000 + bcd2bin(year);
    return true;
}

static void ds1302_set_time(const rtc_time_t *t)
{
    ds1302_write_reg(0x8E, 0x00); /* write protect off */

    uint8_t sec = bin2bcd(t->sec) & 0x7F;
    ds1302_write_reg(0x80, sec);
    ds1302_write_reg(0x82, bin2bcd(t->min));
    ds1302_write_reg(0x84, bin2bcd(t->hour)); /* 24h mode */
    ds1302_write_reg(0x86, bin2bcd(t->day));
    ds1302_write_reg(0x88, bin2bcd(t->month));
    ds1302_write_reg(0x8A, bin2bcd(t->dow));
    ds1302_write_reg(0x8C, bin2bcd((uint8_t)(t->year - 2000)));

    ds1302_write_reg(0x8E, 0x80); /* write protect on */
}

static void settings_set_defaults(settings_t *s)
{
    s->magic = SETTINGS_MAGIC_V2;
    s->on_hour = 7;
    s->on_min = 0;
    s->off_hour = 9;
    s->off_min = 0;
    s->on2_hour = 18;
    s->on2_min = 0;
    s->off2_hour = 20;
    s->off2_min = 0;
    s->red_pct = 80;
    s->blue_pct = 60;
    s->pwm_freq_hz = 1000;
    s->ramp_sec = 300;
}

static void settings_save(const settings_t *s);

static void settings_load(settings_t *s)
{
    nvs_handle_t handle;
    esp_err_t err = nvs_open("node_led", NVS_READONLY, &handle);
    if (err != ESP_OK) {
        settings_set_defaults(s);
        return;
    }

    size_t size = 0;
    err = nvs_get_blob(handle, "settings", NULL, &size);
    if (err != ESP_OK) {
        nvs_close(handle);
        settings_set_defaults(s);
        return;
    }

    if (size == sizeof(settings_t)) {
        err = nvs_get_blob(handle, "settings", s, &size);
        nvs_close(handle);
        if (err != ESP_OK || s->magic != SETTINGS_MAGIC_V2) {
            settings_set_defaults(s);
        }
        return;
    }

    typedef struct {
        uint32_t magic;
        uint8_t on_hour;
        uint8_t on_min;
        uint8_t off_hour;
        uint8_t off_min;
        uint8_t red_pct;
        uint8_t blue_pct;
        uint16_t pwm_freq_hz;
        uint16_t ramp_sec;
    } settings_v1_t;

    if (size == sizeof(settings_v1_t)) {
        settings_v1_t v1 = {0};
        err = nvs_get_blob(handle, "settings", &v1, &size);
        nvs_close(handle);
        if (err == ESP_OK && v1.magic == SETTINGS_MAGIC_V1) {
            settings_set_defaults(s);
            s->on_hour = v1.on_hour;
            s->on_min = v1.on_min;
            s->off_hour = v1.off_hour;
            s->off_min = v1.off_min;
            s->red_pct = v1.red_pct;
            s->blue_pct = v1.blue_pct;
            s->pwm_freq_hz = v1.pwm_freq_hz;
            s->ramp_sec = v1.ramp_sec;
            settings_save(s);
            return;
        }
        settings_set_defaults(s);
        return;
    }

    nvs_close(handle);
    settings_set_defaults(s);
}

static void settings_save(const settings_t *s)
{
    nvs_handle_t handle;
    if (nvs_open("node_led", NVS_READWRITE, &handle) != ESP_OK) {
        return;
    }
    nvs_set_blob(handle, "settings", s, sizeof(settings_t));
    nvs_commit(handle);
    nvs_close(handle);
}

static void pwm_apply_frequency(uint16_t freq_hz)
{
    ledc_timer_config_t timer = {
        .speed_mode = LEDC_LOW_SPEED_MODE,
        .duty_resolution = LEDC_TIMER_RESOLUTION,
        .timer_num = LEDC_TIMER_0,
        .freq_hz = freq_hz,
        .clk_cfg = LEDC_AUTO_CLK,
    };
    ledc_timer_config(&timer);
}

static void pwm_init(uint16_t freq_hz)
{
    pwm_apply_frequency(freq_hz);

    ledc_channel_config_t red = {
        .speed_mode = LEDC_LOW_SPEED_MODE,
        .channel = LEDC_CHANNEL_0,
        .timer_sel = LEDC_TIMER_0,
        .intr_type = LEDC_INTR_DISABLE,
        .gpio_num = GPIO_PWM_RED,
        .duty = 0,
        .hpoint = 0,
    };
    ledc_channel_config(&red);

    ledc_channel_config_t blue = {
        .speed_mode = LEDC_LOW_SPEED_MODE,
        .channel = LEDC_CHANNEL_1,
        .timer_sel = LEDC_TIMER_0,
        .intr_type = LEDC_INTR_DISABLE,
        .gpio_num = GPIO_PWM_BLUE,
        .duty = 0,
        .hpoint = 0,
    };
    ledc_channel_config(&blue);
}

static uint32_t percent_to_duty(int32_t pct)
{
    if (pct < 0) pct = 0;
    if (pct > 100) pct = 100;
    return (uint32_t)((pct * LEDC_MAX_DUTY) / 100);
}

static void pwm_set_percent(int32_t red_pct, int32_t blue_pct)
{
    ledc_set_duty(LEDC_LOW_SPEED_MODE, LEDC_CHANNEL_0, percent_to_duty(red_pct));
    ledc_update_duty(LEDC_LOW_SPEED_MODE, LEDC_CHANNEL_0);
    ledc_set_duty(LEDC_LOW_SPEED_MODE, LEDC_CHANNEL_1, percent_to_duty(blue_pct));
    ledc_update_duty(LEDC_LOW_SPEED_MODE, LEDC_CHANNEL_1);
}

static bool schedule_is_on_interval(int on_hour, int on_min, int off_hour, int off_min,
                                    int hour, int min)
{
    int now = hour * 60 + min;
    int on = on_hour * 60 + on_min;
    int off = off_hour * 60 + off_min;

    if (on == off) {
        return false;
    }
    if (on < off) {
        return (now >= on && now < off);
    }
    return (now >= on || now < off);
}

static bool schedule_is_on(const settings_t *s, int hour, int min)
{
    if (schedule_is_on_interval(s->on_hour, s->on_min, s->off_hour, s->off_min, hour, min)) {
        return true;
    }
    return schedule_is_on_interval(s->on2_hour, s->on2_min, s->off2_hour, s->off2_min, hour, min);
}

static void control_task(void *arg)
{
    (void)arg;
    const int32_t scale = PWM_SCALE; /* 0.01% */

    while (true) {
        rtc_time_t now = {0};
        settings_t s;
        bool test_active = false;
        int64_t now_us = esp_timer_get_time();

        if (xSemaphoreTake(g_rtc_mutex, pdMS_TO_TICKS(100)) == pdTRUE) {
            ds1302_get_time(&now);
            xSemaphoreGive(g_rtc_mutex);
        }

        if (xSemaphoreTake(g_settings_mutex, pdMS_TO_TICKS(100)) == pdTRUE) {
            s = g_settings;
            xSemaphoreGive(g_settings_mutex);
        } else {
            settings_set_defaults(&s);
        }

        if (xSemaphoreTake(g_test_mutex, pdMS_TO_TICKS(20)) == pdTRUE) {
            if (g_test_until_us != 0 && now_us >= g_test_until_us) {
                g_test_until_us = 0;
                g_test_stage = -1;
            }
            test_active = (g_test_until_us != 0 && now_us < g_test_until_us);
            xSemaphoreGive(g_test_mutex);
        }

        int32_t target_red = 0;
        int32_t target_blue = 0;

        if (test_active) {
            int64_t elapsed = now_us - g_test_start_us;
            int step = (elapsed >= 0) ? (int)(elapsed / ((int64_t)TEST_STEP_SEC * 1000000)) : 0;
            if (step < 0) step = 0;
            if (step > 1) step = 1;

            target_red = (step == 0) ? s.red_pct : 0;
            target_blue = (step == 1) ? s.blue_pct : 0;

            if (step != g_test_stage) {
                g_test_stage = step;
                pwm_set_percent(target_red, target_blue);
                vTaskDelay(pdMS_TO_TICKS(20));
                int red_level = gpio_get_level(GPIO_PWM_RED);
                int blue_level = gpio_get_level(GPIO_PWM_BLUE);
                ESP_LOGI(TAG, "Тест %s: GPIO red=%d blue=%d (%%=%d/%d)",
                         (step == 0) ? "красный" : "синий",
                         red_level, blue_level, target_red, target_blue);
            } else {
                pwm_set_percent(target_red, target_blue);
            }

            g_actual_red = target_red * scale;
            g_actual_blue = target_blue * scale;
            vTaskDelay(pdMS_TO_TICKS(200));
            continue;
        } else {
            bool is_on = schedule_is_on(&s, now.hour, now.min);
            target_red = is_on ? s.red_pct : 0;
            target_blue = is_on ? s.blue_pct : 0;
        }

        int32_t target_red_scaled = target_red * scale;
        int32_t target_blue_scaled = target_blue * scale;

        int32_t step = (s.ramp_sec == 0) ? 100 * scale : (100 * scale) / s.ramp_sec;
        if (step < 1) step = 1;

        if (g_actual_red < target_red_scaled) {
            g_actual_red += step;
            if (g_actual_red > target_red_scaled) g_actual_red = target_red_scaled;
        } else if (g_actual_red > target_red_scaled) {
            g_actual_red -= step;
            if (g_actual_red < target_red_scaled) g_actual_red = target_red_scaled;
        }

        if (g_actual_blue < target_blue_scaled) {
            g_actual_blue += step;
            if (g_actual_blue > target_blue_scaled) g_actual_blue = target_blue_scaled;
        } else if (g_actual_blue > target_blue_scaled) {
            g_actual_blue -= step;
            if (g_actual_blue < target_blue_scaled) g_actual_blue = target_blue_scaled;
        }

        pwm_set_percent(g_actual_red / scale, g_actual_blue / scale);

        vTaskDelay(pdMS_TO_TICKS(1000));
    }
}

static void wifi_init_ap(void)
{
    if (!g_wifi_inited) {
        ESP_ERROR_CHECK(esp_netif_init());
        ESP_ERROR_CHECK(esp_event_loop_create_default());

        g_ap_netif = esp_netif_create_default_wifi_ap();
        assert(g_ap_netif);

        wifi_init_config_t cfg = WIFI_INIT_CONFIG_DEFAULT();
        ESP_ERROR_CHECK(esp_wifi_init(&cfg));
        g_wifi_inited = true;
    }

    wifi_config_t wifi_config = {0};
    strncpy((char *)wifi_config.ap.ssid, WIFI_SSID, sizeof(wifi_config.ap.ssid));
    strncpy((char *)wifi_config.ap.password, WIFI_PASS, sizeof(wifi_config.ap.password));
    wifi_config.ap.ssid_len = strlen(WIFI_SSID);
    wifi_config.ap.channel = 1;
    wifi_config.ap.max_connection = 4;
    wifi_config.ap.authmode = WIFI_AUTH_WPA2_PSK;
    if (strlen(WIFI_PASS) == 0) {
        wifi_config.ap.authmode = WIFI_AUTH_OPEN;
    }

    ESP_ERROR_CHECK(esp_wifi_set_mode(WIFI_MODE_AP));
    ESP_ERROR_CHECK(esp_wifi_set_config(WIFI_IF_AP, &wifi_config));

    esp_netif_ip_info_t ip_info = {0};
    IP4_ADDR(&ip_info.ip, WIFI_AP_IP1, WIFI_AP_IP2, WIFI_AP_IP3, WIFI_AP_IP4);
    IP4_ADDR(&ip_info.gw, WIFI_AP_IP1, WIFI_AP_IP2, WIFI_AP_IP3, WIFI_AP_IP4);
    IP4_ADDR(&ip_info.netmask, 255, 255, 255, 0);

    esp_netif_dhcps_stop(g_ap_netif);
    esp_netif_set_ip_info(g_ap_netif, &ip_info);
    esp_netif_dhcps_start(g_ap_netif);

    ESP_ERROR_CHECK(esp_wifi_start());

    ESP_LOGI(TAG, "Wi-Fi AP started. SSID=%s IP=%d.%d.%d.%d", WIFI_SSID,
             WIFI_AP_IP1, WIFI_AP_IP2, WIFI_AP_IP3, WIFI_AP_IP4);
}

static void wifi_stop_ap(void)
{
    if (g_wifi_inited) {
        esp_wifi_stop();
        ESP_LOGI(TAG, "Wi-Fi AP stopped");
    }
}

static void html_append(char **p, size_t *left, const char *fmt, ...)
{
    if (*left == 0) {
        return;
    }
    va_list args;
    va_start(args, fmt);
    int written = vsnprintf(*p, *left, fmt, args);
    va_end(args);
    if (written < 0) {
        return;
    }
    if ((size_t)written >= *left) {
        *p += *left;
        *left = 0;
    } else {
        *p += written;
        *left -= written;
    }
}

static esp_err_t http_root_get_handler(httpd_req_t *req)
{
    portENTER_CRITICAL(&g_activity_mux);
    g_last_http_activity_us = esp_timer_get_time();
    portEXIT_CRITICAL(&g_activity_mux);
    settings_t s;
    rtc_time_t now = {0};

    if (xSemaphoreTake(g_settings_mutex, pdMS_TO_TICKS(100)) == pdTRUE) {
        s = g_settings;
        xSemaphoreGive(g_settings_mutex);
    } else {
        settings_set_defaults(&s);
    }

    if (xSemaphoreTake(g_rtc_mutex, pdMS_TO_TICKS(100)) == pdTRUE) {
        ds1302_get_time(&now);
        xSemaphoreGive(g_rtc_mutex);
    }

    bool is_on = schedule_is_on(&s, now.hour, now.min);
    const char *status_class = is_on ? "badge" : "badge off";
    const char *status_text = is_on ? "Включено" : "Выключено";

    char *html = calloc(1, HTML_BUF_SIZE);
    if (!html) {
        httpd_resp_send_err(req, HTTPD_500_INTERNAL_SERVER_ERROR, "Недостаточно памяти");
        return ESP_FAIL;
    }
    char *ptr = html;
    size_t left = HTML_BUF_SIZE;

    html_append(&ptr, &left,
                "<!DOCTYPE html><html lang=\"ru\"><head><meta charset=\"utf-8\">"
                "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">"
                "<title>Фитосвет</title>"
                "<style>"
                ":root{--bg1:#0b1220;--bg2:#101b2d;--card:#111827;--accent:#34d399;"
                "--accent2:#60a5fa;--text:#e5e7eb;--muted:#9ca3af;}"
                "*{box-sizing:border-box;}"
                "body{margin:0;font-family:\"Trebuchet MS\",\"Verdana\",sans-serif;color:var(--text);"
                "background:radial-gradient(1200px 400px at 15%% -10%%,#1f2937,transparent),"
                "linear-gradient(160deg,var(--bg1),var(--bg2));min-height:100vh;}"
                ".container{max-width:860px;margin:0 auto;padding:18px 14px 36px;}"
                "header{display:flex;flex-direction:column;gap:10px;margin-bottom:14px;}"
                ".title{font-family:\"Georgia\",\"Times New Roman\",serif;font-size:26px;letter-spacing:.2px;}"
                ".sub{color:var(--muted);font-size:13px;}"
                ".badge{display:inline-flex;align-items:center;gap:8px;padding:6px 12px;border-radius:999px;"
                "background:rgba(52,211,153,.18);color:#a7f3d0;font-weight:700;font-size:12px;}"
                ".badge.off{background:rgba(248,113,113,.18);color:#fecaca;}"
                ".grid{display:grid;grid-template-columns:1fr;gap:14px;}"
                ".card{background:rgba(17,24,39,.92);border:1px solid rgba(148,163,184,.18);"
                "border-radius:16px;padding:16px;box-shadow:0 12px 30px rgba(0,0,0,.25);}"
                ".card h2{margin:0 0 12px;font-size:16px;color:#f9fafb;}"
                ".time{font-size:20px;font-weight:700;letter-spacing:.4px;}"
                "label{display:block;margin-top:10px;font-size:12px;color:var(--muted);}"
                "input,select,button{width:100%%;padding:10px 12px;border-radius:10px;"
                "border:1px solid rgba(148,163,184,.2);background:#0b1220;color:var(--text);font-size:15px;}"
                "input:focus,select:focus{outline:none;border-color:var(--accent2);"
                "box-shadow:0 0 0 3px rgba(96,165,250,.2);}"
                ".row{display:grid;grid-template-columns:1fr 1fr;gap:10px;}"
                ".button{margin-top:14px;background:linear-gradient(135deg,var(--accent),#22c55e);"
                "border:none;color:#062a1f;font-weight:800;}"
                ".button.alt{background:linear-gradient(135deg,var(--accent2),#38bdf8);color:#041322;}"
                ".button.ghost{background:transparent;border:1px dashed rgba(148,163,184,.4);color:var(--text);}"
                ".note{margin-top:8px;font-size:12px;color:var(--muted);}"
                ".footer{margin-top:12px;font-size:12px;color:var(--muted);}"
                "@media(min-width:760px){header{flex-direction:row;align-items:center;justify-content:space-between;}"
                ".grid{grid-template-columns:1fr 1fr;}"
                ".card.full{grid-column:1/-1;}}"
                "</style></head><body><div class=\"container\">"
                "<header><div>"
                "<div class=\"title\">Фитосвет • контроллер</div>"
                "<div class=\"sub\">ESP32 + DS1302</div>"
                "</div>"
                "<div class=\"%s\">Статус: %s</div></header>",
                status_class, status_text);

    html_append(&ptr, &left,
                "<div class=\"grid\">"
                "<div class=\"card full\">"
                "<h2>Текущее время</h2>"
                "<div class=\"time\">%04d-%02d-%02d %02d:%02d:%02d</div>"
                "<div class=\"note\">Расписание действует каждый день.</div>"
                "</div>",
                now.year, now.month, now.day, now.hour, now.min, now.sec);

    html_append(&ptr, &left,
                "<div class=\"card\">"
                "<h2>Расписание</h2>"
                "<form method=\"POST\" action=\"/save\">"
                "<div class=\"row\">"
                "<div><label>Интервал 1: включение</label>"
                "<input type=\"time\" name=\"on_time\" value=\"%02d:%02d\"></div>"
                "<div><label>Интервал 1: выключение</label>"
                "<input type=\"time\" name=\"off_time\" value=\"%02d:%02d\"></div>"
                "</div>"
                "<div class=\"row\">"
                "<div><label>Интервал 2: включение</label>"
                "<input type=\"time\" name=\"on_time2\" value=\"%02d:%02d\"></div>"
                "<div><label>Интервал 2: выключение</label>"
                "<input type=\"time\" name=\"off_time2\" value=\"%02d:%02d\"></div>"
                "</div>",
                s.on_hour, s.on_min, s.off_hour, s.off_min,
                s.on2_hour, s.on2_min, s.off2_hour, s.off2_min);

    html_append(&ptr, &left,
                "<label>Время плавного перехода (сек)</label>"
                "<input type=\"number\" min=\"0\" max=\"3600\" name=\"ramp_sec\" value=\"%u\">"
                "<button class=\"button\" type=\"submit\">Сохранить расписание</button>"
                "</form>"
                "</div>",
                s.ramp_sec);

    html_append(&ptr, &left,
                "<div class=\"card\">"
                "<h2>Мощность</h2>"
                "<form method=\"POST\" action=\"/save\">"
                "<div class=\"row\">"
                "<div><label>Красный канал (%%)</label>"
                "<input type=\"number\" min=\"0\" max=\"100\" name=\"red_pct\" value=\"%u\"></div>"
                "<div><label>Синий канал (%%)</label>"
                "<input type=\"number\" min=\"0\" max=\"100\" name=\"blue_pct\" value=\"%u\"></div>"
                "</div>"
                "<label>Частота ШИМ (Гц)</label>"
                "<select name=\"pwm_freq\">"
                "<option value=\"500\" %s>500</option>"
                "<option value=\"1000\" %s>1000</option>"
                "<option value=\"2000\" %s>2000</option>"
                "<option value=\"5000\" %s>5000</option>"
                "<option value=\"10000\" %s>10000</option>"
                "</select>"
                "<button class=\"button alt\" type=\"submit\">Сохранить мощность</button>"
                "</form>"
                "</div>",
                s.red_pct, s.blue_pct,
                (s.pwm_freq_hz == 500) ? "selected" : "",
                (s.pwm_freq_hz == 1000) ? "selected" : "",
                (s.pwm_freq_hz == 2000) ? "selected" : "",
                (s.pwm_freq_hz == 5000) ? "selected" : "",
                (s.pwm_freq_hz == 10000) ? "selected" : "");

    html_append(&ptr, &left,
                "<div class=\"card\">"
                "<h2>Время RTC</h2>"
                "<form method=\"POST\" action=\"/set_time\">"
                "<label>Дата</label>"
                "<input type=\"date\" name=\"set_date\" value=\"%04d-%02d-%02d\">"
                "<label>Время</label>"
                "<input type=\"time\" name=\"set_time\" value=\"%02d:%02d\">"
                "<button class=\"button alt\" type=\"submit\">Установить дату и время</button>"
                "</form>"
                "</div>",
                now.year, now.month, now.day, now.hour, now.min);

    html_append(&ptr, &left,
                "<div class=\"card\">"
                "<h2>Проверка</h2>"
                "<form method=\"POST\" action=\"/test\">"
                "<button class=\"button ghost\" type=\"submit\">Тест светодиодов</button>"
                "</form>"
                "<div class=\"note\">Тест: 3 секунды красный, затем 3 секунды синий.</div>"
                "</div>"
                "</div>"
                "<div class=\"footer\">GPIO: DS1302 CE=%d IO=%d SCLK=%d, PWM красный=%d, PWM синий=%d</div>"
                "</div></body></html>",
                GPIO_DS1302_CE, GPIO_DS1302_IO, GPIO_DS1302_SCLK, GPIO_PWM_RED, GPIO_PWM_BLUE);

    httpd_resp_set_type(req, "text/html; charset=utf-8");
    httpd_resp_send(req, html, HTTPD_RESP_USE_STRLEN);
    free(html);
    return ESP_OK;
}

static void status_led_blink_once(void)
{
    gpio_set_level(GPIO_STATUS_LED, 1);
    vTaskDelay(pdMS_TO_TICKS(80));
    gpio_set_level(GPIO_STATUS_LED, 0);
}

static void url_decode(char *dst, const char *src, size_t dst_len)
{
    size_t di = 0;
    for (size_t i = 0; src[i] != '\0' && di + 1 < dst_len; i++) {
        if (src[i] == '%' && src[i + 1] && src[i + 2]) {
            char hex[3] = { src[i + 1], src[i + 2], 0 };
            dst[di++] = (char)strtol(hex, NULL, 16);
            i += 2;
        } else if (src[i] == '+') {
            dst[di++] = ' ';
        } else {
            dst[di++] = src[i];
        }
    }
    dst[di] = '\0';
}

static bool get_param(const char *body, const char *key, char *out, size_t out_len)
{
    size_t key_len = strlen(key);
    const char *p = body;
    while (p && *p) {
        const char *eq = strchr(p, '=');
        if (!eq) break;
        size_t len = (size_t)(eq - p);
        if (len == key_len && strncmp(p, key, key_len) == 0) {
            const char *val = eq + 1;
            const char *end = strchr(val, '&');
            size_t val_len = end ? (size_t)(end - val) : strlen(val);
            char temp[128];
            if (val_len >= sizeof(temp)) val_len = sizeof(temp) - 1;
            memcpy(temp, val, val_len);
            temp[val_len] = '\0';
            url_decode(out, temp, out_len);
            return true;
        }
        p = strchr(p, '&');
        if (p) p++;
    }
    return false;
}

static void start_led_test(uint32_t duration_sec)
{
    int64_t now = esp_timer_get_time();
    int64_t until = now + (int64_t)duration_sec * 1000000;
    if (xSemaphoreTake(g_test_mutex, pdMS_TO_TICKS(50)) == pdTRUE) {
        g_test_start_us = now;
        g_test_until_us = until;
        g_test_stage = -1;
        xSemaphoreGive(g_test_mutex);
    }
    g_actual_red = 0;
    g_actual_blue = 0;
    pwm_set_percent(0, 0);
}

static bool parse_hhmm(const char *str, int *hour, int *min)
{
    if (!str || strlen(str) < 4) return false;
    int h = 0, m = 0;
    if (sscanf(str, "%d:%d", &h, &m) != 2) return false;
    if (h < 0 || h > 23 || m < 0 || m > 59) return false;
    *hour = h;
    *min = m;
    return true;
}

static bool parse_ymd(const char *str, int *y, int *m, int *d)
{
    if (!str || strlen(str) < 8) return false;
    int yy = 0, mm = 0, dd = 0;
    if (sscanf(str, "%d-%d-%d", &yy, &mm, &dd) != 3) return false;
    if (yy < 2000 || yy > 2099 || mm < 1 || mm > 12 || dd < 1 || dd > 31) return false;
    if (dd > days_in_month(yy, mm)) return false;
    *y = yy; *m = mm; *d = dd;
    return true;
}

static int read_req_body(httpd_req_t *req, char *buf, size_t buf_len)
{
    int total = req->content_len;
    int received = 0;
    int stored = 0;
    char dump[128];

    if (buf_len == 0) {
        return -1;
    }

    while (received < total) {
        int remaining = total - received;
        char *dest = NULL;
        int max = 0;

        if (stored < (int)buf_len - 1) {
            dest = buf + stored;
            max = (int)buf_len - 1 - stored;
            if (max > remaining) {
                max = remaining;
            }
        } else {
            dest = dump;
            max = remaining > (int)sizeof(dump) ? (int)sizeof(dump) : remaining;
        }

        int r = httpd_req_recv(req, dest, max);
        if (r <= 0) {
            return -1;
        }
        received += r;

        if (dest != dump) {
            stored += r;
            if (stored > (int)buf_len - 1) {
                stored = (int)buf_len - 1;
            }
        }
    }

    buf[stored] = '\0';
    return stored;
}

static bool apply_rtc_from_body(const char *body)
{
    char buf[64];
    rtc_time_t t = {0};
    bool has_date = false;
    bool has_time = false;

    if (get_param(body, "set_date", buf, sizeof(buf))) {
        int yy, mm, dd;
        if (parse_ymd(buf, &yy, &mm, &dd)) {
            t.year = yy;
            t.month = mm;
            t.day = dd;
            has_date = true;
        }
    }

    if (get_param(body, "set_time", buf, sizeof(buf))) {
        int hh, mn;
        if (parse_hhmm(buf, &hh, &mn)) {
            t.hour = hh;
            t.min = mn;
            t.sec = 0;
            has_time = true;
        }
    }

    if (!has_date && !has_time) {
        return false;
    }

    if (!has_date || !has_time) {
        rtc_time_t current = {0};
        if (xSemaphoreTake(g_rtc_mutex, pdMS_TO_TICKS(200)) == pdTRUE) {
            ds1302_get_time(&current);
            xSemaphoreGive(g_rtc_mutex);
        } else {
            return false;
        }

        if (!has_date) {
            t.year = current.year;
            t.month = current.month;
            t.day = current.day;
        }
        if (!has_time) {
            t.hour = current.hour;
            t.min = current.min;
            t.sec = current.sec;
        }
    }

    t.dow = calc_dow(t.year, t.month, t.day);

    if (xSemaphoreTake(g_rtc_mutex, pdMS_TO_TICKS(200)) == pdTRUE) {
        ds1302_set_time(&t);
        xSemaphoreGive(g_rtc_mutex);
        return true;
    }

    return false;
}

static esp_err_t http_save_post_handler(httpd_req_t *req)
{
    portENTER_CRITICAL(&g_activity_mux);
    g_last_http_activity_us = esp_timer_get_time();
    portEXIT_CRITICAL(&g_activity_mux);
    status_led_blink_once();
    char body[512];
    if (read_req_body(req, body, sizeof(body)) < 0) {
        httpd_resp_send_err(req, HTTPD_500_INTERNAL_SERVER_ERROR, "Ошибка чтения");
        return ESP_FAIL;
    }

    settings_t s;
    if (xSemaphoreTake(g_settings_mutex, pdMS_TO_TICKS(100)) == pdTRUE) {
        s = g_settings;
        xSemaphoreGive(g_settings_mutex);
    } else {
        settings_set_defaults(&s);
    }

    char buf[64];
    int h, m;

    if (get_param(body, "on_time", buf, sizeof(buf)) && parse_hhmm(buf, &h, &m)) {
        s.on_hour = h;
        s.on_min = m;
    }
    if (get_param(body, "off_time", buf, sizeof(buf)) && parse_hhmm(buf, &h, &m)) {
        s.off_hour = h;
        s.off_min = m;
    }
    if (get_param(body, "on_time2", buf, sizeof(buf)) && parse_hhmm(buf, &h, &m)) {
        s.on2_hour = h;
        s.on2_min = m;
    }
    if (get_param(body, "off_time2", buf, sizeof(buf)) && parse_hhmm(buf, &h, &m)) {
        s.off2_hour = h;
        s.off2_min = m;
    }
    if (get_param(body, "red_pct", buf, sizeof(buf))) {
        int v = atoi(buf);
        if (v < 0) v = 0;
        if (v > 100) v = 100;
        s.red_pct = v;
    }
    if (get_param(body, "blue_pct", buf, sizeof(buf))) {
        int v = atoi(buf);
        if (v < 0) v = 0;
        if (v > 100) v = 100;
        s.blue_pct = v;
    }
    if (get_param(body, "pwm_freq", buf, sizeof(buf))) {
        int v = atoi(buf);
        if (v == 500 || v == 1000 || v == 2000 || v == 5000 || v == 10000) {
            s.pwm_freq_hz = v;
        }
    }
    if (get_param(body, "ramp_sec", buf, sizeof(buf))) {
        int v = atoi(buf);
        if (v < 0) v = 0;
        if (v > 3600) v = 3600;
        s.ramp_sec = v;
    }

    if (xSemaphoreTake(g_settings_mutex, pdMS_TO_TICKS(200)) == pdTRUE) {
        g_settings = s;
        xSemaphoreGive(g_settings_mutex);
    }
    settings_save(&s);
    pwm_apply_frequency(s.pwm_freq_hz);

    httpd_resp_set_status(req, "303 See Other");
    httpd_resp_set_hdr(req, "Location", "/");
    httpd_resp_send(req, "", 0);
    return ESP_OK;
}

static esp_err_t http_set_time_post_handler(httpd_req_t *req)
{
    portENTER_CRITICAL(&g_activity_mux);
    g_last_http_activity_us = esp_timer_get_time();
    portEXIT_CRITICAL(&g_activity_mux);
    status_led_blink_once();
    char body[256];
    if (read_req_body(req, body, sizeof(body)) < 0) {
        httpd_resp_send_err(req, HTTPD_500_INTERNAL_SERVER_ERROR, "Ошибка чтения");
        return ESP_FAIL;
    }

    if (!apply_rtc_from_body(body)) {
        httpd_resp_send_err(req, HTTPD_400_BAD_REQUEST, "Неверные данные даты/времени");
        return ESP_FAIL;
    }

    httpd_resp_set_status(req, "303 See Other");
    httpd_resp_set_hdr(req, "Location", "/");
    httpd_resp_send(req, "", 0);
    return ESP_OK;
}

static esp_err_t http_test_post_handler(httpd_req_t *req)
{
    portENTER_CRITICAL(&g_activity_mux);
    g_last_http_activity_us = esp_timer_get_time();
    portEXIT_CRITICAL(&g_activity_mux);
    status_led_blink_once();
    char body[64];
    if (read_req_body(req, body, sizeof(body)) < 0) {
        httpd_resp_send_err(req, HTTPD_500_INTERNAL_SERVER_ERROR, "Ошибка чтения");
        return ESP_FAIL;
    }

    start_led_test(TEST_TOTAL_SEC);

    httpd_resp_set_status(req, "303 See Other");
    httpd_resp_set_hdr(req, "Location", "/");
    httpd_resp_send(req, "", 0);
    return ESP_OK;
}

static httpd_handle_t start_webserver(void)
{
    httpd_config_t config = HTTPD_DEFAULT_CONFIG();
    config.max_uri_handlers = 10;
    config.stack_size = 12288;
    config.lru_purge_enable = true;
    config.max_open_sockets = 4;

    httpd_handle_t server = NULL;
    esp_err_t err = httpd_start(&server, &config);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "HTTP server start failed: %s", esp_err_to_name(err));
        return NULL;
    }

    httpd_uri_t root = {
        .uri = "/",
        .method = HTTP_GET,
        .handler = http_root_get_handler,
        .user_ctx = NULL
    };
    httpd_register_uri_handler(server, &root);

    httpd_uri_t save = {
        .uri = "/save",
        .method = HTTP_POST,
        .handler = http_save_post_handler,
        .user_ctx = NULL
    };
    httpd_register_uri_handler(server, &save);

    httpd_uri_t set_time = {
        .uri = "/set_time",
        .method = HTTP_POST,
        .handler = http_set_time_post_handler,
        .user_ctx = NULL
    };
    httpd_register_uri_handler(server, &set_time);

    httpd_uri_t test = {
        .uri = "/test",
        .method = HTTP_POST,
        .handler = http_test_post_handler,
        .user_ctx = NULL
    };
    httpd_register_uri_handler(server, &test);

    ESP_LOGI(TAG, "HTTP server started on port %d", config.server_port);
    return server;
}

static void web_start(void)
{
    if (g_web_active) {
        return;
    }
    wifi_init_ap();
    g_http_server = start_webserver();
    if (g_http_server) {
        g_web_active = true;
        portENTER_CRITICAL(&g_activity_mux);
        g_last_http_activity_us = esp_timer_get_time();
        portEXIT_CRITICAL(&g_activity_mux);

        for (int i = 0; i < 3; i++) {
            gpio_set_level(GPIO_STATUS_LED, 1);
            vTaskDelay(pdMS_TO_TICKS(150));
            gpio_set_level(GPIO_STATUS_LED, 0);
            vTaskDelay(pdMS_TO_TICKS(150));
        }
    }
}

static void web_stop(void)
{
    if (!g_web_active) {
        return;
    }
    if (g_http_server) {
        httpd_stop(g_http_server);
        g_http_server = NULL;
    }
    wifi_stop_ap();
    g_web_active = false;
}

static void button_task(void *arg)
{
    (void)arg;
    int64_t press_start = 0;
    bool triggered = false;

    while (true) {
        int level = gpio_get_level(GPIO_BOOT_BTN);
        if (level == 0) {
            if (press_start == 0) {
                press_start = esp_timer_get_time();
                triggered = false;
            } else if (!triggered) {
                int64_t held_us = esp_timer_get_time() - press_start;
                if (held_us >= (int64_t)WEB_LONG_PRESS_SEC * 1000000) {
                    triggered = true;
                    web_start();
                }
            }
        } else {
            press_start = 0;
            triggered = false;
        }
        vTaskDelay(pdMS_TO_TICKS(100));
    }
}

static void web_idle_task(void *arg)
{
    (void)arg;
    while (true) {
        if (g_web_active) {
            int64_t now = esp_timer_get_time();
            int64_t last;
            portENTER_CRITICAL(&g_activity_mux);
            last = g_last_http_activity_us;
            portEXIT_CRITICAL(&g_activity_mux);
            int64_t idle_us = now - last;
            if (idle_us > (int64_t)WEB_IDLE_TIMEOUT_SEC * 1000000) {
                web_stop();
            }
        }
        vTaskDelay(pdMS_TO_TICKS(1000));
    }
}

void app_main(void)
{
    esp_err_t err = nvs_flash_init();
    if (err == ESP_ERR_NVS_NO_FREE_PAGES || err == ESP_ERR_NVS_NEW_VERSION_FOUND) {
        ESP_ERROR_CHECK(nvs_flash_erase());
        err = nvs_flash_init();
    }
    ESP_ERROR_CHECK(err);

    g_settings_mutex = xSemaphoreCreateMutex();
    g_rtc_mutex = xSemaphoreCreateMutex();
    g_test_mutex = xSemaphoreCreateMutex();

    settings_load(&g_settings);

    gpio_config_t status_led = {
        .pin_bit_mask = (1ULL << GPIO_STATUS_LED),
        .mode = GPIO_MODE_OUTPUT,
        .pull_up_en = GPIO_PULLUP_DISABLE,
        .pull_down_en = GPIO_PULLDOWN_DISABLE,
        .intr_type = GPIO_INTR_DISABLE,
    };
    gpio_config(&status_led);
    gpio_set_level(GPIO_STATUS_LED, 0);

    ds1302_init();
    pwm_init(g_settings.pwm_freq_hz);

    {
        rtc_time_t now = {0};
        if (ds1302_get_time(&now)) {
            bool is_on = schedule_is_on(&g_settings, now.hour, now.min);
            int32_t red = is_on ? g_settings.red_pct : 0;
            int32_t blue = is_on ? g_settings.blue_pct : 0;
            g_actual_red = red * PWM_SCALE;
            g_actual_blue = blue * PWM_SCALE;
            pwm_set_percent(red, blue);
        }
    }

    gpio_config_t btn = {
        .pin_bit_mask = (1ULL << GPIO_BOOT_BTN),
        .mode = GPIO_MODE_INPUT,
        .pull_up_en = GPIO_PULLUP_ENABLE,
        .pull_down_en = GPIO_PULLDOWN_DISABLE,
        .intr_type = GPIO_INTR_DISABLE,
    };
    gpio_config(&btn);

    xTaskCreate(control_task, "control_task", 4096, NULL, 5, NULL);
    xTaskCreate(button_task, "button_task", 4096, NULL, 4, NULL);
    xTaskCreate(web_idle_task, "web_idle_task", 2048, NULL, 3, NULL);

    ESP_LOGI(TAG, "Готово. Удерживайте BOOT %d сек для запуска веб-сервера.", WEB_LONG_PRESS_SEC);
}
