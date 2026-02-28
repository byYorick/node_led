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
#include "lwip/ip4_addr.h"

#include "nvs_flash.h"
#include "nvs.h"

#include "driver/ledc.h"
#include "driver/gpio.h"
#include "driver/i2c.h"

#define WIFI_SSID "node_led"
#define WIFI_PASS "node12345"

#define WIFI_AP_IP1 192
#define WIFI_AP_IP2 168
#define WIFI_AP_IP3 4
#define WIFI_AP_IP4 1

#define I2C_MASTER_NUM I2C_NUM_0
#define I2C_MASTER_FREQ_HZ 100000
#define I2C_MASTER_TIMEOUT_MS 600
#define I2C_GPIO_SDA_DEFAULT 5
#define I2C_GPIO_SCL_DEFAULT 6
#define RTC_I2C_ADDR 0x68
#define MEM_I2C_ADDR 0x50
#define OLED_WIDTH 72
#define OLED_HEIGHT 40
#define OLED_PAGES (OLED_HEIGHT / 8)
#define OLED_X_OFFSET 28
#define OLED_Y_OFFSET 0
#define OLED_ADDR_PRIMARY 0x3C
#define OLED_ADDR_SECONDARY 0x3D

#define GPIO_PWM_RED  1
#define GPIO_PWM_BLUE 2
#define GPIO_BOOT_BTN_PRIMARY 9
#define GPIO_BOOT_BTN_ALT 0
#define GPIO_STATUS_LED 8
#define STATUS_LED_ON_LEVEL 0
#define STATUS_LED_OFF_LEVEL 1

#define LEDC_TIMER_RESOLUTION LEDC_TIMER_11_BIT
#define LEDC_MAX_DUTY ((1 << LEDC_TIMER_RESOLUTION) - 1)
#define PWM_SCALE 100
#define HTML_BUF_SIZE 12288
#define HTTP_MAX_BODY_SIZE 1024

#define SETTINGS_MAGIC_V1 0x4C45444E /* "LEDN" */
#define SETTINGS_MAGIC_V2 0x4C454432 /* "LED2" */
#define SETTINGS_MAGIC_V3 0x4C454433 /* "LED3" */

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
    uint8_t on3_hour;
    uint8_t on3_min;
    uint8_t off3_hour;
    uint8_t off3_min;
    uint8_t power1_pct;
    uint8_t power2_pct;
    uint8_t power3_pct;
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
static SemaphoreHandle_t g_i2c_mutex;

static int32_t g_actual_red = 0;
static int32_t g_actual_blue = 0;
static int64_t g_test_start_us = 0;
static int64_t g_test_until_us = 0;
static int g_test_stage = -1;

#define TEST_STEP_SEC 3
#define TEST_TOTAL_SEC (TEST_STEP_SEC * 2)
#define WEB_IDLE_TIMEOUT_SEC 300
#define WEB_LONG_PRESS_SEC 2

static httpd_handle_t g_http_server = NULL;
static esp_netif_t *g_ap_netif = NULL;
static bool g_wifi_inited = false;
static int64_t g_last_http_activity_us = 0;
static bool g_web_active = false;
static portMUX_TYPE g_activity_mux = portMUX_INITIALIZER_UNLOCKED;
static bool g_i2c_inited = false;
static bool g_oled_ready = false;
static uint8_t g_oled_fb[OLED_WIDTH * OLED_PAGES];
static uint8_t g_oled_addr = OLED_ADDR_PRIMARY;
static int g_i2c_sda = I2C_GPIO_SDA_DEFAULT;
static int g_i2c_scl = I2C_GPIO_SCL_DEFAULT;
static volatile bool g_rtc_set_in_progress = false;
static esp_err_t i2c_master_init_if_needed(void);

static inline void status_led_set(bool on)
{
    gpio_set_level(GPIO_STATUS_LED, on ? STATUS_LED_ON_LEVEL : STATUS_LED_OFF_LEVEL);
}

static bool boot_button_pressed(void)
{
    return (gpio_get_level(GPIO_BOOT_BTN_PRIMARY) == 0) || (gpio_get_level(GPIO_BOOT_BTN_ALT) == 0);
}

static bool i2c_lock(TickType_t timeout_ticks)
{
    if (!g_i2c_mutex) {
        return false;
    }
    return xSemaphoreTake(g_i2c_mutex, timeout_ticks) == pdTRUE;
}

static void i2c_unlock(void)
{
    if (g_i2c_mutex) {
        xSemaphoreGive(g_i2c_mutex);
    }
}

static bool i2c_probe_addr(uint8_t addr)
{
    if (!i2c_lock(pdMS_TO_TICKS(I2C_MASTER_TIMEOUT_MS))) {
        return false;
    }

    i2c_cmd_handle_t cmd = i2c_cmd_link_create();
    if (!cmd) {
        i2c_unlock();
        ESP_LOGW(TAG, "I2C cmd link allocation failed while probing 0x%02X", addr);
        return false;
    }
    i2c_master_start(cmd);
    i2c_master_write_byte(cmd, (addr << 1) | I2C_MASTER_WRITE, true);
    i2c_master_stop(cmd);
    esp_err_t err = i2c_master_cmd_begin(I2C_MASTER_NUM, cmd, pdMS_TO_TICKS(I2C_MASTER_TIMEOUT_MS));
    i2c_cmd_link_delete(cmd);

    i2c_unlock();
    return err == ESP_OK;
}

static void i2c_scan_bus(void)
{
    if (i2c_master_init_if_needed() != ESP_OK) {
        ESP_LOGW(TAG, "I2C scan skipped: init failed");
        return;
    }

    int found = 0;
    for (uint8_t addr = 0x03; addr <= 0x77; addr++) {
        if (i2c_probe_addr(addr)) {
            ESP_LOGI(TAG, "I2C device found at 0x%02X", addr);
            found++;
        }
    }

    if (found == 0) {
        ESP_LOGW(TAG, "I2C scan: no devices found");
    } else {
        ESP_LOGI(TAG, "I2C scan complete: %d device(s)", found);
    }
}

static esp_err_t i2c_master_init_if_needed(void)
{
    if (g_i2c_inited) {
        return ESP_OK;
    }

    i2c_config_t conf = {
        .mode = I2C_MODE_MASTER,
        .sda_io_num = g_i2c_sda,
        .scl_io_num = g_i2c_scl,
        .sda_pullup_en = GPIO_PULLUP_ENABLE,
        .scl_pullup_en = GPIO_PULLUP_ENABLE,
        .master.clk_speed = I2C_MASTER_FREQ_HZ,
    };
    esp_err_t err = i2c_param_config(I2C_MASTER_NUM, &conf);
    if (err != ESP_OK) {
        return err;
    }

    err = i2c_driver_install(I2C_MASTER_NUM, conf.mode, 0, 0, 0);
    if (err == ESP_OK) {
        g_i2c_inited = true;
    }
    return err;
}

static esp_err_t ds1307_read_regs(uint8_t start_reg, uint8_t *data, size_t len)
{
    if (!i2c_lock(pdMS_TO_TICKS(I2C_MASTER_TIMEOUT_MS))) {
        return ESP_ERR_TIMEOUT;
    }
    esp_err_t err = i2c_master_write_read_device(I2C_MASTER_NUM,
                                                 RTC_I2C_ADDR,
                                                 &start_reg,
                                                 1,
                                                 data,
                                                 len,
                                                 pdMS_TO_TICKS(I2C_MASTER_TIMEOUT_MS));
    i2c_unlock();
    return err;
}

static esp_err_t ds1307_write_regs(uint8_t start_reg, const uint8_t *data, size_t len)
{
    if (len > 15) {
        return ESP_ERR_INVALID_SIZE;
    }

    uint8_t buf[16];
    buf[0] = start_reg;
    if (len > 0) {
        memcpy(&buf[1], data, len);
    }
    if (!i2c_lock(pdMS_TO_TICKS(I2C_MASTER_TIMEOUT_MS))) {
        return ESP_ERR_TIMEOUT;
    }
    esp_err_t err = i2c_master_write_to_device(I2C_MASTER_NUM,
                                               RTC_I2C_ADDR,
                                               buf,
                                               len + 1,
                                               pdMS_TO_TICKS(I2C_MASTER_TIMEOUT_MS));
    i2c_unlock();
    return err;
}

static esp_err_t ds1307_write_reg(uint8_t reg, uint8_t value)
{
    return ds1307_write_regs(reg, &value, 1);
}

static bool i2c_pins_conflict_with_pwm(int sda, int scl)
{
    return (sda == GPIO_PWM_RED) || (sda == GPIO_PWM_BLUE) ||
           (scl == GPIO_PWM_RED) || (scl == GPIO_PWM_BLUE);
}

static void oled_glyph5x7(char c, uint8_t out[5])
{
    memset(out, 0, 5);
    if (c >= 'a' && c <= 'z') {
        c = (char)(c - 'a' + 'A');
    }

    switch (c) {
        case '0': out[0]=0x3E; out[1]=0x51; out[2]=0x49; out[3]=0x45; out[4]=0x3E; break;
        case '1': out[0]=0x00; out[1]=0x42; out[2]=0x7F; out[3]=0x40; out[4]=0x00; break;
        case '2': out[0]=0x42; out[1]=0x61; out[2]=0x51; out[3]=0x49; out[4]=0x46; break;
        case '3': out[0]=0x21; out[1]=0x41; out[2]=0x45; out[3]=0x4B; out[4]=0x31; break;
        case '4': out[0]=0x18; out[1]=0x14; out[2]=0x12; out[3]=0x7F; out[4]=0x10; break;
        case '5': out[0]=0x27; out[1]=0x45; out[2]=0x45; out[3]=0x45; out[4]=0x39; break;
        case '6': out[0]=0x3C; out[1]=0x4A; out[2]=0x49; out[3]=0x49; out[4]=0x30; break;
        case '7': out[0]=0x01; out[1]=0x71; out[2]=0x09; out[3]=0x05; out[4]=0x03; break;
        case '8': out[0]=0x36; out[1]=0x49; out[2]=0x49; out[3]=0x49; out[4]=0x36; break;
        case '9': out[0]=0x06; out[1]=0x49; out[2]=0x49; out[3]=0x29; out[4]=0x1E; break;
        case 'A': out[0]=0x7E; out[1]=0x11; out[2]=0x11; out[3]=0x11; out[4]=0x7E; break;
        case 'B': out[0]=0x7F; out[1]=0x49; out[2]=0x49; out[3]=0x49; out[4]=0x36; break;
        case 'D': out[0]=0x7F; out[1]=0x41; out[2]=0x41; out[3]=0x22; out[4]=0x1C; break;
        case 'E': out[0]=0x7F; out[1]=0x49; out[2]=0x49; out[3]=0x49; out[4]=0x41; break;
        case 'F': out[0]=0x7F; out[1]=0x09; out[2]=0x09; out[3]=0x09; out[4]=0x01; break;
        case 'I': out[0]=0x00; out[1]=0x41; out[2]=0x7F; out[3]=0x41; out[4]=0x00; break;
        case 'L': out[0]=0x7F; out[1]=0x40; out[2]=0x40; out[3]=0x40; out[4]=0x40; break;
        case 'M': out[0]=0x7F; out[1]=0x02; out[2]=0x04; out[3]=0x02; out[4]=0x7F; break;
        case 'N': out[0]=0x7F; out[1]=0x04; out[2]=0x08; out[3]=0x10; out[4]=0x7F; break;
        case 'O': out[0]=0x3E; out[1]=0x41; out[2]=0x41; out[3]=0x41; out[4]=0x3E; break;
        case 'R': out[0]=0x7F; out[1]=0x09; out[2]=0x19; out[3]=0x29; out[4]=0x46; break;
        case 'S': out[0]=0x46; out[1]=0x49; out[2]=0x49; out[3]=0x49; out[4]=0x31; break;
        case 'T': out[0]=0x01; out[1]=0x01; out[2]=0x7F; out[3]=0x01; out[4]=0x01; break;
        case 'W': out[0]=0x7F; out[1]=0x20; out[2]=0x18; out[3]=0x20; out[4]=0x7F; break;
        case ':': out[0]=0x00; out[1]=0x36; out[2]=0x36; out[3]=0x00; out[4]=0x00; break;
        case '.': out[0]=0x00; out[1]=0x60; out[2]=0x60; out[3]=0x00; out[4]=0x00; break;
        case '-': out[0]=0x08; out[1]=0x08; out[2]=0x08; out[3]=0x08; out[4]=0x08; break;
        case '%': out[0]=0x63; out[1]=0x13; out[2]=0x08; out[3]=0x64; out[4]=0x63; break;
        case '/': out[0]=0x20; out[1]=0x10; out[2]=0x08; out[3]=0x04; out[4]=0x02; break;
        default: break;
    }
}

static esp_err_t oled_write(uint8_t control, const uint8_t *data, size_t len)
{
    if (!i2c_lock(pdMS_TO_TICKS(I2C_MASTER_TIMEOUT_MS))) {
        return ESP_ERR_TIMEOUT;
    }

    esp_err_t err = ESP_OK;
    while (len > 0) {
        uint8_t tx[17];
        size_t chunk = (len > 16) ? 16 : len;
        tx[0] = control;
        memcpy(&tx[1], data, chunk);
        err = i2c_master_write_to_device(I2C_MASTER_NUM, g_oled_addr, tx, chunk + 1,
                                         pdMS_TO_TICKS(I2C_MASTER_TIMEOUT_MS));
        if (err != ESP_OK) {
            break;
        }
        data += chunk;
        len -= chunk;
    }

    i2c_unlock();
    return err;
}

static esp_err_t oled_cmd_list(const uint8_t *cmds, size_t len)
{
    return oled_write(0x00, cmds, len);
}

static void oled_clear_fb(void)
{
    memset(g_oled_fb, 0, sizeof(g_oled_fb));
}

static void oled_draw_char(int page, int x, char c)
{
    if (page < 0 || page >= OLED_PAGES || x >= OLED_WIDTH) {
        return;
    }

    uint8_t glyph[5];
    oled_glyph5x7(c, glyph);
    int base = page * OLED_WIDTH;
    for (int i = 0; i < 5; i++) {
        int px = x + i;
        if (px >= 0 && px < OLED_WIDTH) {
            g_oled_fb[base + px] = glyph[i];
        }
    }
    if (x + 5 >= 0 && x + 5 < OLED_WIDTH) {
        g_oled_fb[base + x + 5] = 0x00;
    }
}

static void oled_draw_text(int page, int x, const char *text)
{
    int cursor = x;
    for (size_t i = 0; text[i] != '\0'; i++) {
        oled_draw_char(page, cursor, text[i]);
        cursor += 6;
        if (cursor >= OLED_WIDTH) {
            break;
        }
    }
}

static esp_err_t oled_flush(void)
{
    esp_err_t err = ESP_OK;
    for (int page = 0; page < OLED_PAGES; page++) {
        int col = OLED_X_OFFSET;
        uint8_t page_addr[] = {
            (uint8_t)(0xB0 | page),
            (uint8_t)(0x00 | (col & 0x0F)),
            (uint8_t)(0x10 | ((col >> 4) & 0x0F))
        };
        err = oled_cmd_list(page_addr, sizeof(page_addr));
        if (err != ESP_OK) {
            return err;
        }
        err = oled_write(0x40, &g_oled_fb[page * OLED_WIDTH], OLED_WIDTH);
        if (err != ESP_OK) {
            return err;
        }
    }
    return err;
}

static bool oled_probe_addr(uint8_t addr)
{
    return i2c_probe_addr(addr);
}

static bool oled_init(void)
{
    if (i2c_master_init_if_needed() != ESP_OK) {
        return false;
    }
    if (g_i2c_sda != I2C_GPIO_SDA_DEFAULT || g_i2c_scl != I2C_GPIO_SCL_DEFAULT) {
        ESP_LOGW(TAG, "I2C pins are SDA=%d SCL=%d, expected fixed SDA=%d SCL=%d",
                 g_i2c_sda, g_i2c_scl, I2C_GPIO_SDA_DEFAULT, I2C_GPIO_SCL_DEFAULT);
    }

    if (oled_probe_addr(OLED_ADDR_PRIMARY)) {
        g_oled_addr = OLED_ADDR_PRIMARY;
    } else if (oled_probe_addr(OLED_ADDR_SECONDARY)) {
        g_oled_addr = OLED_ADDR_SECONDARY;
    } else {
        ESP_LOGW(TAG, "OLED not found at 0x%02X/0x%02X on SDA=%d SCL=%d",
                 OLED_ADDR_PRIMARY, OLED_ADDR_SECONDARY, g_i2c_sda, g_i2c_scl);
        return false;
    }

    if (i2c_pins_conflict_with_pwm(g_i2c_sda, g_i2c_scl)) {
        ESP_LOGW(TAG, "I2C pins SDA=%d SCL=%d conflict with PWM pins RED=%d BLUE=%d",
                 g_i2c_sda, g_i2c_scl, GPIO_PWM_RED, GPIO_PWM_BLUE);
    }

    const uint8_t init_cmds[] = {
        0xAE, 0xD5, 0x80, 0xA8, (OLED_HEIGHT - 1), 0xD3, OLED_Y_OFFSET, 0x40, 0x8D, 0x14,
        0x20, 0x00, 0xA1, 0xC8, 0xDA, 0x12, 0x81, 0x7F, 0xD9, 0xF1, 0xDB, 0x20,
        0xA4, 0xA6, 0x2E, 0xAF
    };
    if (oled_cmd_list(init_cmds, sizeof(init_cmds)) != ESP_OK) {
        return false;
    }

    oled_clear_fb();
    oled_draw_text(1, 0, "OLED READY");
    if (oled_flush() != ESP_OK) {
        return false;
    }
    ESP_LOGI(TAG, "OLED initialized at 0x%02X (SDA=%d SCL=%d)", g_oled_addr, g_i2c_sda, g_i2c_scl);
    g_oled_ready = true;
    return true;
}

static void oled_render_status(const rtc_time_t *now, bool schedule_on, bool test_active,
                               int red_pct, int blue_pct, bool web_active)
{
    if (!g_oled_ready || !now) {
        return;
    }

    char line0[16];
    char line1[16];
    char line2[16];
    char line3[16];

    if (red_pct < 0) red_pct = 0;
    if (red_pct > 100) red_pct = 100;
    if (blue_pct < 0) blue_pct = 0;
    if (blue_pct > 100) blue_pct = 100;

    snprintf(line0, sizeof(line0), "%02d:%02d:%02d", now->hour, now->min, now->sec);
    snprintf(line1, sizeof(line1), "%02d.%02d.%02d", now->day, now->month, now->year % 100);

    char mode = test_active ? 'T' : (schedule_on ? 'O' : '-');
    snprintf(line2, sizeof(line2), "%c %03d/%03d", mode, red_pct, blue_pct);
    snprintf(line3, sizeof(line3), "W:%c", web_active ? '1' : '0');

    oled_clear_fb();
    oled_draw_text(0, 0, line0);
    oled_draw_text(1, 0, line1);
    oled_draw_text(2, 0, line2);
    oled_draw_text(3, 0, line3);
    oled_flush();
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

static bool rtc_init(void)
{
    esp_err_t err = i2c_master_init_if_needed();
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "I2C init failed: %s", esp_err_to_name(err));
        return false;
    }

    if (!i2c_probe_addr(RTC_I2C_ADDR)) {
        ESP_LOGW(TAG, "RTC not found at 0x%02X", RTC_I2C_ADDR);
        return false;
    }

    uint8_t ctrl = 0x00; /* SQW/OUT off */
    err = ds1307_write_regs(0x07, &ctrl, 1);
    if (err != ESP_OK) {
        ESP_LOGW(TAG, "DS1307 control write failed: %s", esp_err_to_name(err));
        return false;
    }
    return true;
}

static bool rtc_get_time(rtc_time_t *t)
{
    if (!t) {
        return false;
    }
    if (i2c_master_init_if_needed() != ESP_OK) {
        return false;
    }

    uint8_t data[7] = {0};
    if (ds1307_read_regs(0x00, data, sizeof(data)) != ESP_OK) {
        return false;
    }

    uint8_t sec = data[0];
    uint8_t min = data[1];
    uint8_t hour = data[2];
    if (sec & 0x80) {
        sec &= 0x7F;
        ds1307_write_regs(0x00, &sec, 1);
    }

    if (hour & 0x40) { /* 12h mode */
        int pm = hour & 0x20;
        hour = bcd2bin(hour & 0x1F);
        if (pm && hour < 12) {
            hour += 12;
        } else if (!pm && hour == 12) {
            hour = 0;
        }
    } else { /* 24h mode */
        hour = bcd2bin(hour & 0x3F);
    }

    t->sec = bcd2bin(sec & 0x7F);
    t->min = bcd2bin(min & 0x7F);
    t->hour = hour;
    t->dow = bcd2bin(data[3] & 0x07);
    t->day = bcd2bin(data[4] & 0x3F);
    t->month = bcd2bin(data[5] & 0x1F);
    t->year = 2000 + bcd2bin(data[6]);
    return true;
}

static bool rtc_set_time(const rtc_time_t *t)
{
    if (!t) {
        return false;
    }
    if (i2c_master_init_if_needed() != ESP_OK) {
        return false;
    }

    int year = t->year;
    if (year < 2000) {
        year = 2000;
    } else if (year > 2099) {
        year = 2099;
    }

    uint8_t regs[7] = {
        (uint8_t)(bin2bcd((uint8_t)t->sec) & 0x7F),
        bin2bcd((uint8_t)t->min),
        bin2bcd((uint8_t)t->hour), /* 24h mode */
        bin2bcd((uint8_t)t->dow),
        bin2bcd((uint8_t)t->day),
        bin2bcd((uint8_t)t->month),
        bin2bcd((uint8_t)(year - 2000))
    };

    for (int i = 0; i < 7; i++) {
        bool ok = false;
        for (int attempt = 1; attempt <= 3; attempt++) {
            esp_err_t err = ds1307_write_reg((uint8_t)i, regs[i]);
            if (err == ESP_OK) {
                ok = true;
                break;
            }
            ESP_LOGW(TAG, "RTC write reg 0x%02X attempt %d failed: %s",
                     i, attempt, esp_err_to_name(err));
            vTaskDelay(pdMS_TO_TICKS(20));
        }
        if (!ok) {
            return false;
        }
    }
    return true;
}

static void settings_set_defaults(settings_t *s)
{
    s->magic = SETTINGS_MAGIC_V3;
    s->on_hour = 7;
    s->on_min = 0;
    s->off_hour = 9;
    s->off_min = 0;
    s->power1_pct = 80;
    s->on2_hour = 9;
    s->on2_min = 0;
    s->off2_hour = 18;
    s->off2_min = 0;
    s->power2_pct = 20;
    s->on3_hour = 18;
    s->on3_min = 0;
    s->off3_hour = 21;
    s->off3_min = 0;
    s->power3_pct = 70;
    s->red_pct = 80;
    s->blue_pct = 60;
    s->pwm_freq_hz = 1000;
    s->ramp_sec = 300;
}

static bool settings_save(const settings_t *s);

static void settings_load(settings_t *s)
{
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
    } settings_v2_t;

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
        if (err != ESP_OK || s->magic != SETTINGS_MAGIC_V3) {
            settings_set_defaults(s);
        }
        return;
    }

    if (size == sizeof(settings_v2_t)) {
        settings_v2_t v2 = {0};
        err = nvs_get_blob(handle, "settings", &v2, &size);
        nvs_close(handle);
        if (err == ESP_OK && v2.magic == SETTINGS_MAGIC_V2) {
            settings_set_defaults(s);
            s->on_hour = v2.on_hour;
            s->on_min = v2.on_min;
            s->off_hour = v2.off_hour;
            s->off_min = v2.off_min;
            s->on2_hour = v2.on2_hour;
            s->on2_min = v2.on2_min;
            s->off2_hour = v2.off2_hour;
            s->off2_min = v2.off2_min;
            s->power1_pct = 100;
            s->power2_pct = 100;
            s->power3_pct = 0;
            s->on3_hour = 0;
            s->on3_min = 0;
            s->off3_hour = 0;
            s->off3_min = 0;
            s->red_pct = v2.red_pct;
            s->blue_pct = v2.blue_pct;
            s->pwm_freq_hz = v2.pwm_freq_hz;
            s->ramp_sec = v2.ramp_sec;
            if (!settings_save(s)) {
                ESP_LOGW(TAG, "Failed to persist migrated V2 settings");
            }
            return;
        }
        settings_set_defaults(s);
        return;
    }

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
            if (!settings_save(s)) {
                ESP_LOGW(TAG, "Failed to persist migrated V1 settings");
            }
            return;
        }
        settings_set_defaults(s);
        return;
    }

    nvs_close(handle);
    settings_set_defaults(s);
}

static bool settings_save(const settings_t *s)
{
    nvs_handle_t handle;
    esp_err_t err = nvs_open("node_led", NVS_READWRITE, &handle);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "NVS open failed: %s", esp_err_to_name(err));
        return false;
    }
    err = nvs_set_blob(handle, "settings", s, sizeof(settings_t));
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "NVS set settings failed: %s", esp_err_to_name(err));
        nvs_close(handle);
        return false;
    }
    err = nvs_commit(handle);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "NVS commit failed: %s", esp_err_to_name(err));
        nvs_close(handle);
        return false;
    }
    nvs_close(handle);
    return true;
}

static bool pwm_apply_frequency(uint16_t freq_hz)
{
    ledc_timer_config_t timer = {
        .speed_mode = LEDC_LOW_SPEED_MODE,
        .duty_resolution = LEDC_TIMER_RESOLUTION,
        .timer_num = LEDC_TIMER_0,
        .freq_hz = freq_hz,
        .clk_cfg = LEDC_AUTO_CLK,
    };
    esp_err_t err = ledc_timer_config(&timer);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "PWM timer config failed for %u Hz: %s", freq_hz, esp_err_to_name(err));
        return false;
    }
    return true;
}

static void pwm_init(uint16_t freq_hz)
{
    if (!pwm_apply_frequency(freq_hz)) {
        ESP_LOGW(TAG, "Falling back to 1000 Hz PWM");
        (void)pwm_apply_frequency(1000);
    }

    ledc_channel_config_t red = {
        .speed_mode = LEDC_LOW_SPEED_MODE,
        .channel = LEDC_CHANNEL_0,
        .timer_sel = LEDC_TIMER_0,
        .intr_type = LEDC_INTR_DISABLE,
        .gpio_num = GPIO_PWM_RED,
        .duty = 0,
        .hpoint = 0,
    };
    esp_err_t err = ledc_channel_config(&red);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "LEDC red channel init failed: %s", esp_err_to_name(err));
    }

    ledc_channel_config_t blue = {
        .speed_mode = LEDC_LOW_SPEED_MODE,
        .channel = LEDC_CHANNEL_1,
        .timer_sel = LEDC_TIMER_0,
        .intr_type = LEDC_INTR_DISABLE,
        .gpio_num = GPIO_PWM_BLUE,
        .duty = 0,
        .hpoint = 0,
    };
    err = ledc_channel_config(&blue);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "LEDC blue channel init failed: %s", esp_err_to_name(err));
    }
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

static int schedule_power_pct(const settings_t *s, int hour, int min)
{
    if (schedule_is_on_interval(s->on_hour, s->on_min, s->off_hour, s->off_min, hour, min)) {
        return s->power1_pct;
    }
    if (schedule_is_on_interval(s->on2_hour, s->on2_min, s->off2_hour, s->off2_min, hour, min)) {
        return s->power2_pct;
    }
    if (schedule_is_on_interval(s->on3_hour, s->on3_min, s->off3_hour, s->off3_min, hour, min)) {
        return s->power3_pct;
    }
    return 0;
}

static void control_task(void *arg)
{
    (void)arg;
    const int32_t scale = PWM_SCALE; /* 0.01% */
    int64_t prev_loop_us = esp_timer_get_time();
    int64_t ramp_accum = 0;

    while (true) {
        rtc_time_t now = {0};
        settings_t s;
        bool test_active = false;
        int schedule_power = 0;
        bool is_on = false;
        int64_t now_us = esp_timer_get_time();
        int64_t dt_us = now_us - prev_loop_us;
        if (dt_us < 0) {
            dt_us = 0;
        } else if (dt_us > 5 * 1000000LL) {
            dt_us = 5 * 1000000LL;
        }
        prev_loop_us = now_us;

        if (xSemaphoreTake(g_rtc_mutex, pdMS_TO_TICKS(100)) == pdTRUE) {
            rtc_get_time(&now);
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
            if (!g_rtc_set_in_progress) {
                oled_render_status(&now, false, true, target_red, target_blue, g_web_active);
            }
            ramp_accum = 0;
            vTaskDelay(pdMS_TO_TICKS(200));
            continue;
        } else {
            schedule_power = schedule_power_pct(&s, now.hour, now.min);
            if (schedule_power < 0) schedule_power = 0;
            if (schedule_power > 100) schedule_power = 100;
            is_on = (schedule_power > 0);
            target_red = (s.red_pct * schedule_power) / 100;
            target_blue = (s.blue_pct * schedule_power) / 100;
        }

        int32_t target_red_scaled = target_red * scale;
        int32_t target_blue_scaled = target_blue * scale;

        int32_t step = 100 * scale;
        if (s.ramp_sec > 0) {
            int64_t denom = (int64_t)s.ramp_sec * 1000000LL;
            ramp_accum += dt_us * (100 * scale);
            step = (int32_t)(ramp_accum / denom);
            ramp_accum %= denom;
        } else {
            ramp_accum = 0;
        }

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
        if (!g_rtc_set_in_progress) {
            oled_render_status(&now, is_on, false, g_actual_red / scale, g_actual_blue / scale, g_web_active);
        }

        vTaskDelay(pdMS_TO_TICKS(1000));
    }
}

static bool wifi_init_ap(void)
{
    esp_err_t err;

    if (!g_wifi_inited) {
        err = esp_netif_init();
        if (err != ESP_OK && err != ESP_ERR_INVALID_STATE) {
            ESP_LOGE(TAG, "esp_netif_init failed: %s", esp_err_to_name(err));
            return false;
        }
        err = esp_event_loop_create_default();
        if (err != ESP_OK && err != ESP_ERR_INVALID_STATE) {
            ESP_LOGE(TAG, "event loop init failed: %s", esp_err_to_name(err));
            return false;
        }

        if (!g_ap_netif) {
            g_ap_netif = esp_netif_create_default_wifi_ap();
        }
        if (!g_ap_netif) {
            ESP_LOGE(TAG, "Failed to create default AP netif");
            return false;
        }

        wifi_init_config_t cfg = WIFI_INIT_CONFIG_DEFAULT();
        err = esp_wifi_init(&cfg);
        if (err != ESP_OK && err != ESP_ERR_INVALID_STATE) {
            ESP_LOGE(TAG, "esp_wifi_init failed: %s", esp_err_to_name(err));
            return false;
        }
        g_wifi_inited = true;
    }

    wifi_config_t wifi_config = {0};
    snprintf((char *)wifi_config.ap.ssid, sizeof(wifi_config.ap.ssid), "%s", WIFI_SSID);
    snprintf((char *)wifi_config.ap.password, sizeof(wifi_config.ap.password), "%s", WIFI_PASS);
    wifi_config.ap.ssid_len = strlen(WIFI_SSID);
    wifi_config.ap.channel = 1;
    wifi_config.ap.max_connection = 4;
    wifi_config.ap.authmode = WIFI_AUTH_WPA2_PSK;
    if (strlen(WIFI_PASS) == 0) {
        wifi_config.ap.authmode = WIFI_AUTH_OPEN;
    }

    err = esp_wifi_set_mode(WIFI_MODE_AP);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "esp_wifi_set_mode(AP) failed: %s", esp_err_to_name(err));
        return false;
    }
    err = esp_wifi_set_config(WIFI_IF_AP, &wifi_config);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "esp_wifi_set_config(AP) failed: %s", esp_err_to_name(err));
        return false;
    }

    esp_netif_ip_info_t ip_info = {0};
    IP4_ADDR(&ip_info.ip, WIFI_AP_IP1, WIFI_AP_IP2, WIFI_AP_IP3, WIFI_AP_IP4);
    IP4_ADDR(&ip_info.gw, WIFI_AP_IP1, WIFI_AP_IP2, WIFI_AP_IP3, WIFI_AP_IP4);
    IP4_ADDR(&ip_info.netmask, 255, 255, 255, 0);

    err = esp_netif_dhcps_stop(g_ap_netif);
    if (err != ESP_OK) {
        ESP_LOGW(TAG, "DHCP server stop failed: %s", esp_err_to_name(err));
    }
    err = esp_netif_set_ip_info(g_ap_netif, &ip_info);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "esp_netif_set_ip_info failed: %s", esp_err_to_name(err));
        return false;
    }
    err = esp_netif_dhcps_start(g_ap_netif);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "DHCP server start failed: %s", esp_err_to_name(err));
        return false;
    }

    err = esp_wifi_start();
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "esp_wifi_start failed: %s", esp_err_to_name(err));
        return false;
    }

    ESP_LOGI(TAG, "Wi-Fi AP started. SSID=%s IP=%d.%d.%d.%d", WIFI_SSID,
             WIFI_AP_IP1, WIFI_AP_IP2, WIFI_AP_IP3, WIFI_AP_IP4);
    return true;
}

static void wifi_stop_ap(void)
{
    if (g_wifi_inited) {
        esp_err_t err = esp_wifi_stop();
        if (err == ESP_OK) {
            ESP_LOGI(TAG, "Wi-Fi AP stopped");
        } else {
            ESP_LOGW(TAG, "Wi-Fi AP stop failed: %s", esp_err_to_name(err));
        }
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
        rtc_get_time(&now);
        xSemaphoreGive(g_rtc_mutex);
    }

    int active_power = schedule_power_pct(&s, now.hour, now.min);
    if (active_power < 0) active_power = 0;
    if (active_power > 100) active_power = 100;
    bool is_on = (active_power > 0);
    const char *status_class = is_on ? "badge" : "badge off";
    char status_text[32];
    if (is_on) {
        snprintf(status_text, sizeof(status_text), "Включено %d%%", active_power);
    } else {
        snprintf(status_text, sizeof(status_text), "Выключено");
    }

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
                "<div class=\"sub\">ESP32-C3 + DS1307 (I2C)</div>"
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
                "<input type=\"text\" name=\"on_time\" value=\"%02d:%02d\" inputmode=\"numeric\" "
                "pattern=\"^([01][0-9]|2[0-3]):[0-5][0-9]$\" placeholder=\"HH:MM\" title=\"24ч HH:MM\"></div>"
                "<div><label>Интервал 1: выключение</label>"
                "<input type=\"text\" name=\"off_time\" value=\"%02d:%02d\" inputmode=\"numeric\" "
                "pattern=\"^([01][0-9]|2[0-3]):[0-5][0-9]$\" placeholder=\"HH:MM\" title=\"24ч HH:MM\"></div>"
                "</div>"
                "<label>Интервал 1: мощность (%%)</label>"
                "<input type=\"number\" min=\"0\" max=\"100\" name=\"power1_pct\" value=\"%u\">"
                "<div class=\"row\">"
                "<div><label>Интервал 2: включение</label>"
                "<input type=\"text\" name=\"on_time2\" value=\"%02d:%02d\" inputmode=\"numeric\" "
                "pattern=\"^([01][0-9]|2[0-3]):[0-5][0-9]$\" placeholder=\"HH:MM\" title=\"24ч HH:MM\"></div>"
                "<div><label>Интервал 2: выключение</label>"
                "<input type=\"text\" name=\"off_time2\" value=\"%02d:%02d\" inputmode=\"numeric\" "
                "pattern=\"^([01][0-9]|2[0-3]):[0-5][0-9]$\" placeholder=\"HH:MM\" title=\"24ч HH:MM\"></div>"
                "</div>"
                "<label>Интервал 2: мощность (%%)</label>"
                "<input type=\"number\" min=\"0\" max=\"100\" name=\"power2_pct\" value=\"%u\">"
                "<div class=\"row\">"
                "<div><label>Интервал 3: включение</label>"
                "<input type=\"text\" name=\"on_time3\" value=\"%02d:%02d\" inputmode=\"numeric\" "
                "pattern=\"^([01][0-9]|2[0-3]):[0-5][0-9]$\" placeholder=\"HH:MM\" title=\"24ч HH:MM\"></div>"
                "<div><label>Интервал 3: выключение</label>"
                "<input type=\"text\" name=\"off_time3\" value=\"%02d:%02d\" inputmode=\"numeric\" "
                "pattern=\"^([01][0-9]|2[0-3]):[0-5][0-9]$\" placeholder=\"HH:MM\" title=\"24ч HH:MM\"></div>"
                "</div>"
                "<label>Интервал 3: мощность (%%)</label>"
                "<input type=\"number\" min=\"0\" max=\"100\" name=\"power3_pct\" value=\"%u\">",
                s.on_hour, s.on_min, s.off_hour, s.off_min,
                s.power1_pct,
                s.on2_hour, s.on2_min, s.off2_hour, s.off2_min,
                s.power2_pct,
                s.on3_hour, s.on3_min, s.off3_hour, s.off3_min,
                s.power3_pct);

    html_append(&ptr, &left,
                "<label>Время плавного перехода (сек)</label>"
                "<input type=\"number\" min=\"0\" max=\"3600\" name=\"ramp_sec\" value=\"%u\">"
                "<div class=\"note\">Формат времени: 24ч (HH:MM)</div>"
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
                "<option value=\"20000\" %s>20000</option>"
                "</select>"
                "<button class=\"button alt\" type=\"submit\">Сохранить мощность</button>"
                "</form>"
                "</div>",
                s.red_pct, s.blue_pct,
                (s.pwm_freq_hz == 500) ? "selected" : "",
                (s.pwm_freq_hz == 1000) ? "selected" : "",
                (s.pwm_freq_hz == 2000) ? "selected" : "",
                (s.pwm_freq_hz == 5000) ? "selected" : "",
                (s.pwm_freq_hz == 10000) ? "selected" : "",
                (s.pwm_freq_hz == 20000) ? "selected" : "");

    html_append(&ptr, &left,
                "<div class=\"card\">"
                "<h2>Время RTC</h2>"
                "<form method=\"POST\" action=\"/set_time\">"
                "<label>Дата</label>"
                "<input type=\"date\" name=\"set_date\" value=\"%04d-%02d-%02d\">"
                "<label>Время</label>"
                "<input type=\"text\" name=\"set_time\" value=\"%02d:%02d\" inputmode=\"numeric\" "
                "pattern=\"^([01][0-9]|2[0-3]):[0-5][0-9]$\" placeholder=\"HH:MM\" title=\"24ч HH:MM\">"
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
                "<div class=\"footer\">I2C: SDA=%d SCL=%d, RTC=0x%02X MEM=0x%02X, PWM красный=%d, PWM синий=%d</div>"
                "</div>"
                "<script>"
                "(function(){"
                "var sel='input[name=\"on_time\"],input[name=\"off_time\"],input[name=\"on_time2\"],"
                "input[name=\"off_time2\"],input[name=\"on_time3\"],input[name=\"off_time3\"],"
                "input[name=\"set_time\"]';"
                "var fields=document.querySelectorAll(sel);"
                "for(var i=0;i<fields.length;i++){"
                "var el=fields[i];"
                "el.setAttribute('maxlength','5');"
                "el.addEventListener('input',function(e){"
                "if(e&&e.inputType&&e.inputType.indexOf('delete')===0){return;}"
                "var d=this.value.replace(/\\D/g,'').slice(0,4);"
                "if(d.length>=2){this.value=d.slice(0,2)+':'+d.slice(2);}else{this.value=d;}"
                "});"
                "}"
                "})();"
                "</script>"
                "</body></html>",
                g_i2c_sda, g_i2c_scl, RTC_I2C_ADDR, MEM_I2C_ADDR, GPIO_PWM_RED, GPIO_PWM_BLUE);

    httpd_resp_set_type(req, "text/html; charset=utf-8");
    httpd_resp_send(req, html, HTTPD_RESP_USE_STRLEN);
    free(html);
    return ESP_OK;
}

static void status_led_blink_once(void)
{
    if (g_web_active) {
        /* Keep status LED steadily on while web server is active. */
        status_led_set(true);
        return;
    }
    status_led_set(true);
    vTaskDelay(pdMS_TO_TICKS(80));
    status_led_set(false);
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
    if (total < 0 || total > HTTP_MAX_BODY_SIZE) {
        return -2;
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
    rtc_time_t readback = {0};
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
            bool ok = rtc_get_time(&current);
            xSemaphoreGive(g_rtc_mutex);
            if (!ok) {
                return false;
            }
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

    g_rtc_set_in_progress = true;
    if (xSemaphoreTake(g_rtc_mutex, pdMS_TO_TICKS(400)) == pdTRUE) {
        bool write_ok = rtc_set_time(&t);
        bool read_ok = write_ok ? rtc_get_time(&readback) : false;
        xSemaphoreGive(g_rtc_mutex);
        g_rtc_set_in_progress = false;
        if (!write_ok || !read_ok) {
            ESP_LOGW(TAG, "RTC apply failed write_ok=%d read_ok=%d", write_ok, read_ok);
            return false;
        }

        /* Minute-level verification to ensure write landed on RTC. */
        if (readback.year != t.year || readback.month != t.month || readback.day != t.day ||
            readback.hour != t.hour || readback.min != t.min) {
            ESP_LOGW(TAG, "RTC verify mismatch set=%04d-%02d-%02d %02d:%02d got=%04d-%02d-%02d %02d:%02d",
                     t.year, t.month, t.day, t.hour, t.min,
                     readback.year, readback.month, readback.day, readback.hour, readback.min);
            return true;
        }
        ESP_LOGI(TAG, "RTC updated to %04d-%02d-%02d %02d:%02d", t.year, t.month, t.day, t.hour, t.min);
        return true;
    }
    g_rtc_set_in_progress = false;

    return false;
}

static esp_err_t http_save_post_handler(httpd_req_t *req)
{
    portENTER_CRITICAL(&g_activity_mux);
    g_last_http_activity_us = esp_timer_get_time();
    portEXIT_CRITICAL(&g_activity_mux);
    status_led_blink_once();
    char body[512];
    int body_len = read_req_body(req, body, sizeof(body));
    if (body_len < 0) {
        if (body_len == -2) {
            httpd_resp_send_err(req, HTTPD_413_CONTENT_TOO_LARGE, "Слишком большой запрос");
        } else {
            httpd_resp_send_err(req, HTTPD_500_INTERNAL_SERVER_ERROR, "Ошибка чтения");
        }
        return ESP_FAIL;
    }

    settings_t s;
    if (xSemaphoreTake(g_settings_mutex, pdMS_TO_TICKS(100)) == pdTRUE) {
        s = g_settings;
        xSemaphoreGive(g_settings_mutex);
    } else {
        httpd_resp_set_status(req, "503 Service Unavailable");
        httpd_resp_send(req, "Система занята", HTTPD_RESP_USE_STRLEN);
        return ESP_FAIL;
    }
    settings_t prev = s;

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
    if (get_param(body, "on_time3", buf, sizeof(buf)) && parse_hhmm(buf, &h, &m)) {
        s.on3_hour = h;
        s.on3_min = m;
    }
    if (get_param(body, "off_time3", buf, sizeof(buf)) && parse_hhmm(buf, &h, &m)) {
        s.off3_hour = h;
        s.off3_min = m;
    }
    if (get_param(body, "power1_pct", buf, sizeof(buf))) {
        int v = atoi(buf);
        if (v < 0) v = 0;
        if (v > 100) v = 100;
        s.power1_pct = v;
    }
    if (get_param(body, "power2_pct", buf, sizeof(buf))) {
        int v = atoi(buf);
        if (v < 0) v = 0;
        if (v > 100) v = 100;
        s.power2_pct = v;
    }
    if (get_param(body, "power3_pct", buf, sizeof(buf))) {
        int v = atoi(buf);
        if (v < 0) v = 0;
        if (v > 100) v = 100;
        s.power3_pct = v;
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
        if (v == 500 || v == 1000 || v == 2000 || v == 5000 || v == 10000 || v == 20000) {
            s.pwm_freq_hz = v;
        }
    }
    if (get_param(body, "ramp_sec", buf, sizeof(buf))) {
        int v = atoi(buf);
        if (v < 0) v = 0;
        if (v > 3600) v = 3600;
        s.ramp_sec = v;
    }

    if (!pwm_apply_frequency(s.pwm_freq_hz)) {
        httpd_resp_send_err(req, HTTPD_500_INTERNAL_SERVER_ERROR, "Ошибка применения ШИМ");
        return ESP_FAIL;
    }
    if (!settings_save(&s)) {
        (void)pwm_apply_frequency(prev.pwm_freq_hz);
        httpd_resp_send_err(req, HTTPD_500_INTERNAL_SERVER_ERROR, "Ошибка сохранения");
        return ESP_FAIL;
    }
    if (xSemaphoreTake(g_settings_mutex, pdMS_TO_TICKS(200)) == pdTRUE) {
        g_settings = s;
        xSemaphoreGive(g_settings_mutex);
    } else {
        (void)settings_save(&prev);
        (void)pwm_apply_frequency(prev.pwm_freq_hz);
        httpd_resp_set_status(req, "503 Service Unavailable");
        httpd_resp_send(req, "Система занята", HTTPD_RESP_USE_STRLEN);
        return ESP_FAIL;
    }

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
    int body_len = read_req_body(req, body, sizeof(body));
    if (body_len < 0) {
        if (body_len == -2) {
            httpd_resp_send_err(req, HTTPD_413_CONTENT_TOO_LARGE, "Слишком большой запрос");
        } else {
            httpd_resp_send_err(req, HTTPD_500_INTERNAL_SERVER_ERROR, "Ошибка чтения");
        }
        return ESP_FAIL;
    }
    ESP_LOGI(TAG, "POST /set_time body: %s", body);

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
    int body_len = read_req_body(req, body, sizeof(body));
    if (body_len < 0) {
        if (body_len == -2) {
            httpd_resp_send_err(req, HTTPD_413_CONTENT_TOO_LARGE, "Слишком большой запрос");
        } else {
            httpd_resp_send_err(req, HTTPD_500_INTERNAL_SERVER_ERROR, "Ошибка чтения");
        }
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
    err = httpd_register_uri_handler(server, &root);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to register / handler: %s", esp_err_to_name(err));
        httpd_stop(server);
        return NULL;
    }

    httpd_uri_t save = {
        .uri = "/save",
        .method = HTTP_POST,
        .handler = http_save_post_handler,
        .user_ctx = NULL
    };
    err = httpd_register_uri_handler(server, &save);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to register /save handler: %s", esp_err_to_name(err));
        httpd_stop(server);
        return NULL;
    }

    httpd_uri_t set_time = {
        .uri = "/set_time",
        .method = HTTP_POST,
        .handler = http_set_time_post_handler,
        .user_ctx = NULL
    };
    err = httpd_register_uri_handler(server, &set_time);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to register /set_time handler: %s", esp_err_to_name(err));
        httpd_stop(server);
        return NULL;
    }

    httpd_uri_t test = {
        .uri = "/test",
        .method = HTTP_POST,
        .handler = http_test_post_handler,
        .user_ctx = NULL
    };
    err = httpd_register_uri_handler(server, &test);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to register /test handler: %s", esp_err_to_name(err));
        httpd_stop(server);
        return NULL;
    }

    ESP_LOGI(TAG, "HTTP server started on port %d", config.server_port);
    return server;
}

static void web_start(void)
{
    if (g_web_active) {
        return;
    }
    if (!wifi_init_ap()) {
        ESP_LOGE(TAG, "Web start aborted: AP init failed");
        status_led_set(false);
        return;
    }
    g_http_server = start_webserver();
    if (!g_http_server) {
        wifi_stop_ap();
        status_led_set(false);
        return;
    }
    g_web_active = true;
    portENTER_CRITICAL(&g_activity_mux);
    g_last_http_activity_us = esp_timer_get_time();
    portEXIT_CRITICAL(&g_activity_mux);

    for (int i = 0; i < 3; i++) {
        status_led_set(true);
        vTaskDelay(pdMS_TO_TICKS(150));
        status_led_set(false);
        vTaskDelay(pdMS_TO_TICKS(150));
    }
    status_led_set(true);
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
    status_led_set(false);
}

static void button_task(void *arg)
{
    (void)arg;
    int64_t press_start = 0;
    bool triggered = false;

    while (true) {
        if (boot_button_pressed()) {
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
    g_i2c_mutex = xSemaphoreCreateMutex();
    if (!g_settings_mutex || !g_rtc_mutex || !g_test_mutex || !g_i2c_mutex) {
        ESP_LOGE(TAG, "Failed to create synchronization primitives");
        while (true) {
            vTaskDelay(pdMS_TO_TICKS(1000));
        }
    }

    settings_load(&g_settings);

    gpio_config_t status_led = {
        .pin_bit_mask = (1ULL << GPIO_STATUS_LED),
        .mode = GPIO_MODE_OUTPUT,
        .pull_up_en = GPIO_PULLUP_DISABLE,
        .pull_down_en = GPIO_PULLDOWN_DISABLE,
        .intr_type = GPIO_INTR_DISABLE,
    };
    err = gpio_config(&status_led);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Status LED gpio_config failed: %s", esp_err_to_name(err));
        while (true) {
            vTaskDelay(pdMS_TO_TICKS(1000));
        }
    }
    status_led_set(false);

    if (!rtc_init()) {
        ESP_LOGW(TAG, "RTC init failed, continue with default/fallback time handling");
    }
    i2c_scan_bus();
    if (!oled_init()) {
        ESP_LOGW(TAG, "OLED init failed");
    }
    if (i2c_pins_conflict_with_pwm(g_i2c_sda, g_i2c_scl)) {
        ESP_LOGW(TAG, "I2C pins SDA=%d SCL=%d overlap PWM pins RED=%d BLUE=%d; RTC access can timeout",
                 g_i2c_sda, g_i2c_scl, GPIO_PWM_RED, GPIO_PWM_BLUE);
    }
    pwm_init(g_settings.pwm_freq_hz);

    {
        rtc_time_t now = {0};
        if (rtc_get_time(&now)) {
            int power_pct = schedule_power_pct(&g_settings, now.hour, now.min);
            if (power_pct < 0) power_pct = 0;
            if (power_pct > 100) power_pct = 100;
            bool is_on = (power_pct > 0);
            int32_t red = (g_settings.red_pct * power_pct) / 100;
            int32_t blue = (g_settings.blue_pct * power_pct) / 100;
            g_actual_red = red * PWM_SCALE;
            g_actual_blue = blue * PWM_SCALE;
            pwm_set_percent(red, blue);
            oled_render_status(&now, is_on, false, red, blue, g_web_active);
        }
    }

    gpio_config_t btn = {
        .pin_bit_mask = (1ULL << GPIO_BOOT_BTN_PRIMARY) | (1ULL << GPIO_BOOT_BTN_ALT),
        .mode = GPIO_MODE_INPUT,
        .pull_up_en = GPIO_PULLUP_ENABLE,
        .pull_down_en = GPIO_PULLDOWN_DISABLE,
        .intr_type = GPIO_INTR_DISABLE,
    };
    err = gpio_config(&btn);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Button gpio_config failed: %s", esp_err_to_name(err));
        while (true) {
            vTaskDelay(pdMS_TO_TICKS(1000));
        }
    }

    TaskHandle_t control_task_handle = NULL;
    TaskHandle_t button_task_handle = NULL;
    TaskHandle_t web_idle_task_handle = NULL;
    if (xTaskCreate(control_task, "control_task", 4096, NULL, 5, &control_task_handle) != pdPASS) {
        ESP_LOGE(TAG, "Failed to create control_task");
        while (true) {
            vTaskDelay(pdMS_TO_TICKS(1000));
        }
    }
    if (xTaskCreate(button_task, "button_task", 4096, NULL, 4, &button_task_handle) != pdPASS) {
        ESP_LOGE(TAG, "Failed to create button_task");
        vTaskDelete(control_task_handle);
        while (true) {
            vTaskDelay(pdMS_TO_TICKS(1000));
        }
    }
    if (xTaskCreate(web_idle_task, "web_idle_task", 2048, NULL, 3, &web_idle_task_handle) != pdPASS) {
        ESP_LOGE(TAG, "Failed to create web_idle_task");
        vTaskDelete(button_task_handle);
        vTaskDelete(control_task_handle);
        ESP_LOGE(TAG, "Failed to create one or more tasks");
        while (true) {
            vTaskDelay(pdMS_TO_TICKS(1000));
        }
    }

    ESP_LOGI(TAG, "Готово. Удерживайте BOOT %d сек для запуска веб-сервера.", WEB_LONG_PRESS_SEC);
}
