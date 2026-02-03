idf_component_register(SRCS "main.c"
                       PRIV_REQUIRES spi_flash esp_http_server esp_wifi esp_netif nvs_flash driver esp_timer esp_event
                       INCLUDE_DIRS "")
