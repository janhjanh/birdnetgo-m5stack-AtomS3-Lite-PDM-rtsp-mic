#include <WiFi.h>
#include <WiFiManager.h>
#include <WiFiUdp.h>
#include <ArduinoOTA.h>
#include <ESPmDNS.h>
#include <esp_err.h>
#include <Wire.h>               // TILFØJET: Nødvendig for I2C kommunikation med ES8311
#include "driver/i2s_common.h"
#include "driver/i2s_std.h"     // ÆNDRET: Skiftet fra i2s_pdm.h til i2s_std.h (Standard I2S)
#include <Preferences.h>
#include <math.h>
#include <time.h>
#include <errno.h>
#include <lwip/sockets.h>
#include <esp32-hal-rgb-led.h>
#include "PdmProbeResult.h"
#include "WebUI.h"

// ================== DUAL-CORE AUDIO ARCHITECTURE ==================
// Core 1: Complete audio pipeline (I2S → process → RTP → WiFi)
// Core 0: Web UI, diagnostics, RTSP protocol, client management
// Standard I2S master codec outputs 16-bit PCM samples directly

enum RtspTransportMode : uint8_t {
    RTSP_TRANSPORT_TCP_INTERLEAVED = 0,
    RTSP_TRANSPORT_UDP_UNICAST = 1,
};

struct RtspSession {
    WiFiClient client;
    bool occupied = false;
    volatile bool streaming = false;
    bool setupDone = false;
    String sessionId = "";
    String remoteAddr = "";
    RtspTransportMode transport = RTSP_TRANSPORT_TCP_INTERLEAVED;
    uint16_t rtpSequence = 0;
    uint32_t rtpTimestamp = 0;
    uint32_t rtpSSRC = 0;
    unsigned long connectedAt = 0;
    unsigned long lastActivity = 0;
    unsigned long playStartedAt = 0;
    uint8_t parseBuffer[1024] = {0};
    int parseBufferPos = 0;
    char streamingRtspBuf[512] = {0};
    size_t streamingRtspBufPos = 0;
    uint16_t streamingInterleavedDiscard = 0;
    uint32_t consecutiveWriteFailures = 0;
    unsigned long firstWriteFailureAt = 0;
};

static const uint8_t MAX_RTSP_CLIENTS = 2;

WiFiClient* volatile streamClient = NULL;
TaskHandle_t audioCaptureTaskHandle = NULL;
volatile bool audioTaskRunning = false;

// Cross-core synchronization primitives
portMUX_TYPE logMux = portMUX_INITIALIZER_UNLOCKED;  
portMUX_TYPE hpfMux = portMUX_INITIALIZER_UNLOCKED;  
portMUX_TYPE diagMux = portMUX_INITIALIZER_UNLOCKED; 
volatile bool stopStreamRequested = false;   
volatile bool streamCleanupDone = false;     
SemaphoreHandle_t taskExitSemaphore = NULL;  
volatile bool core1OwnsLED = false;          

static inline void crossCoreMemoryBarrier() {
    __asm__ __volatile__("memw" ::: "memory");
}

// ================== SETTINGS (ESP32 RTSP Mic for BirdNET-Go) ==================
#define FW_VERSION "4.1.0"
const char* FW_VERSION_STR = FW_VERSION;
static const uint16_t OTA_PORT = 3232;
static const char SETTINGS_NAMESPACE[] = "audioPrefs";
static const char LEGACY_SETTINGS_NAMESPACE[] = "audio";
static const char LOG_TIMEZONE_POSIX[] = "UTC0";
static const char LOG_TIMEZONE_LABEL[] = "UTC";

// -- DEFAULT PARAMETERS
#define DEFAULT_SAMPLE_RATE 48000  
#define DEFAULT_GAIN_FACTOR 1.0f
#define DEFAULT_BUFFER_SIZE 1024   
#define DEFAULT_WIFI_TX_DBM 19.5f  
#define DEFAULT_NETWORK_HOSTNAME "atoms3mic"
static const uint32_t SUPPORTED_PDM_SAMPLE_RATES[] = {16000, 24000, 32000, 48000};

#define DEFAULT_HPF_ENABLED true
#define DEFAULT_HPF_CUTOFF_HZ 180

// Thermal protection defaults
#define DEFAULT_OVERHEAT_PROTECTION true
#define DEFAULT_OVERHEAT_LIMIT_C 80
#define OVERHEAT_MIN_LIMIT_C 30
#define OVERHEAT_MAX_LIMIT_C 95
#define OVERHEAT_LIMIT_STEP_C 5

// ================== ÆNDRET: ATOMS3 LITE + ATOMIC ECHO BASE PINS ==================
#define I2S_BCK_PIN       5  // Bit Clock (G5 på Echo Base)
#define I2S_WS_PIN       39  // Word Select / LRCK (G39 på Echo Base)
#define I2S_DATA_IN_PIN  2  // Data In fra mikrofon (G2 på Echo Base)
#define I2S_DATA_OUT_PIN -1  // Bruges ikke til ren mikrofon (G1 på Echo Base er forbundet til Speaker TX, sættes til -1 her)

#define I2C_SDA_PIN      1  // Groove/Internal SDA (G1) til ES8311 kontrol [3]
#define I2C_SCL_PIN      2  // Groove/Internal SCL (G2) til ES8311 kontrol (Delet med I2S Data) [3]
#define ES8311_ADDR   0x18  // Standard I2C adresse for ES8311 codec [3]

#define WS2812_LED_PIN  35  // AtomS3 Lite built-in RGB LED

struct CRGB {
    uint8_t r;
    uint8_t g;
    uint8_t b;
    constexpr CRGB(uint8_t red = 0, uint8_t green = 0, uint8_t blue = 0)
        : r(red), g(green), b(blue) {}
};

static bool statusLedNeedsRefresh = true;
static CRGB lastStatusLed = CRGB(0, 0, 0);
static uint8_t statusLedBrightness = 32;

static uint8_t scaleLedChannel(uint8_t channel) {
    return (uint8_t)(((uint16_t)channel * (uint16_t)statusLedBrightness + 127U) / 255U);
}

inline void setStatusLed(const CRGB& color) {
    if (!statusLedNeedsRefresh &&
        lastStatusLed.r == color.r &&
        lastStatusLed.g == color.g &&
        lastStatusLed.b == color.b) {
        return;
    }
    rgbLedWriteOrdered(WS2812_LED_PIN, LED_COLOR_ORDER_GRB,
                       scaleLedChannel(color.r),
                       scaleLedChannel(color.g),
                       scaleLedChannel(color.b));
    lastStatusLed = color;
    statusLedNeedsRefresh = false;
}

// -- Servers
WiFiServer rtspServer(8554);
String networkHostname = DEFAULT_NETWORK_HOSTNAME;
bool otaPreviousRtspEnabled = true;

// -- RTSP Streaming
volatile bool isStreaming = false;
unsigned long lastRTSPActivity = 0;
static const bool RTSP_ENABLE_UDP_UNICAST = false;
static RtspSession rtspSessions[MAX_RTSP_CLIENTS];

static int parseRtspCSeqValue(const char* request);
static uint16_t parseRtspContentLengthValue(const char* request);
static bool writeRtspSimpleResponse(RtspSession &session, int cseqVal, const char* extraHeaders = NULL);
static bool handleStreamingRtspCommand(RtspSession &session, const char* request);
static void pollStreamingRtspCommands(RtspSession &session);
static void closeRtspSession(RtspSession &session, bool stopClient);
static void updateStreamingStateFromSessions();
static uint8_t countRtspClients();
static uint8_t countStreamingRtspClients();
static RtspSession* firstStreamingSession();
static void clearAudioDiagnostics();
static void sendRTPPacket(RtspSession &session, int16_t* audioData, int numSamples);
static void sendRTPPacketsToActiveSessions(int16_t* audioData, int numSamples);
static esp_err_t i2sMicRead(void* dest, size_t size, size_t* bytesRead, uint32_t timeoutMs);

// -- Global state
unsigned long audioPacketsSent = 0;
unsigned long audioPacketsDropped = 0;  
unsigned long audioBlocksSent = 0;      
unsigned long lastStatsReset = 0;
bool rtspServerEnabled = true;

bool isSupportedPdmSampleRate(uint32_t rate) {
    for (size_t i = 0; i < (sizeof(SUPPORTED_PDM_SAMPLE_RATES) / sizeof(SUPPORTED_PDM_SAMPLE_RATES[0])); ++i) {
        if (SUPPORTED_PDM_SAMPLE_RATES[i] == rate) return true;
    }
    return false;
}

static uint32_t sanitizePdmSampleRate(uint32_t rate) {
    return isSupportedPdmSampleRate(rate) ? rate : (uint32_t)DEFAULT_SAMPLE_RATE;
}

// -- Audio parameters
uint32_t currentSampleRate = DEFAULT_SAMPLE_RATE;
float currentGainFactor = DEFAULT_GAIN_FACTOR;
uint16_t currentBufferSize = DEFAULT_BUFFER_SIZE;
uint8_t i2sShiftBits = 0;  

// -- Audio metering / clipping diagnostics
uint16_t lastPeakAbs16 = 0;       
uint32_t audioClipCount = 0;      
bool audioClippedLastBlock = false; 
uint16_t peakHoldAbs16 = 0;       
unsigned long peakHoldUntilMs = 0; 

// -- I2S raw capture diagnostics
volatile uint32_t i2sReadOkCount = 0;
volatile uint32_t i2sReadErrCount = 0;
volatile uint32_t i2sReadZeroCount = 0;
volatile uint16_t i2sLastSamplesRead = 0;
volatile int16_t i2sLastRawMin = 0;
volatile int16_t i2sLastRawMax = 0;
volatile uint16_t i2sLastRawPeakAbs = 0;
volatile uint16_t i2sLastRawRms = 0;

// ================== TILFØJET: INITIALISERING AF ES8311 CODEC CHIP VIA I2C ==================
void initAtomicEchoBaseCodec() {
    Wire.begin(I2C_SDA_PIN, I2C_SCL_PIN, 100000); // Start I2C på AtomS3 Lite porten [3]
    
    // Væk chippen op af dvale (Power Management)
    Wire.beginTransmission(ES8311_ADDR);
    Wire.write(0x01); // CSM Power Control Register
    Wire.write(0x30); // Normal tilstand (Tænd ADC og analog kredsløb)
    Wire.endTransmission();
    
    // Sæt I2S formatet til standard Philips Master Mode i stedet for PDM
    Wire.beginTransmission(ES8311_ADDR);
    Wire.write(0x03); // SDP Interface Format Register
    Wire.write(0x00); // 16-bit Philips Standard I2S tilstand
    Wire.endTransmission();

    // Sæt ADC System Clock og delefaktorer (Auto-clocking)
    Wire.beginTransmission(ES8311_ADDR);
    Wire.write(0x04); // System Clock Register
    Wire.write(0x10); // Aktivér indbygget digital clock-styring
    Wire.endTransmission();

    // Juster mikrofonforstærkningen (Gain) for ren optagelse
    Wire.beginTransmission(ES8311_ADDR);
    Wire.write(0x14); // ADC Volume/Gain control register [3]
    Wire.write(0xBF); // +30dB forstærkning (Perfekt til svage lyde/fuglekald) [3]
    Wire.endTransmission();
}
