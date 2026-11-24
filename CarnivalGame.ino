/*
  CARNIVAL GAME - ESP32 firmware
  ------------------------------------------------------------------
  Hardware (ESP32 DevKit, 3.3 V logic)
    OLED 128x64 I2C (SSD1306) .... SDA 21, SCL 22, address 0x3C
    IR obstacle sensor RED hole ... GPIO 32   (OUT pin)
    IR obstacle sensor YELLOW ..... GPIO 33
    IR obstacle sensor GREEN ...... GPIO 25
    LED RED hole (+220 ohm) ....... GPIO 26
    LED YELLOW hole (+220 ohm) .... GPIO 27
    LED GREEN hole (+220 ohm) ..... GPIO 23
    Passive buzzer ................ GPIO 18

  Libraries (Arduino Library Manager): "Adafruit SSD1306" and "Adafruit GFX Library".
  Board: "ESP32 Dev Module" (esp32 core 2.x or 3.x both work).

  How it plays
    - Level 1 = Easy   = 1 ball  (red)
      Level 2 = Normal = 2 balls (red, yellow)
      Level 3 = Hard   = 3 balls (red, yellow, green)
    - 30 seconds on the clock. The first ball thrown starts the clock
      (or press Start on the web page / phone remote).
    - The laptop camera tells this board which colour ball left the table.
      An IR sensor inside each hole tells this board where a ball landed.
    - Ball lands in the hole of its own colour -> LED lights, score +1.
    - Ball lands in a hole of ANOTHER colour -> game over ("Wrong hole!").
    - Holes can be taught from the web page (which sensor is which colour); saved in flash.
    - Win  = every ball of the level scored before time runs out.
    - Lose = time is up, a ball is lost (gone from the camera and not in its own hole),
      or all the balls are used up without winning.
    - Buzzer: ball-in sound, win / lose jingles, ticking in the last 5 s.

  Links
    USB serial 115200 baud: talks to index.html (Chrome / Edge, Web Serial).
    Bluetooth LE: device "CarnivalGame" (Nordic UART service) - same messages as USB,
    use the "Connect Bluetooth" button on the page.
    NOTE: Wi-Fi + Bluetooth make the program big. In the Arduino IDE choose
    Tools > Partition Scheme > "Huge APP (3MB No OTA/1MB SPIFFS)" before uploading.
    Wi-Fi: access point "CarnivalGame", remote page at http://192.168.1.1
*/

#include <Arduino.h>
#include <Wire.h>
#include <WiFi.h>
#include <WebServer.h>
#include <Adafruit_GFX.h>
#include <Adafruit_SSD1306.h>
#include <Preferences.h>
#include <stdarg.h>
#include <BLEDevice.h>
#include <BLEServer.h>
#include <BLEUtils.h>
#include <BLE2902.h>

// ===================== SETTINGS YOU MAY WANT TO CHANGE =====================
const uint8_t  PIN_IR[3]     = {25, 33, 32};   // Red = GPIO25, Yellow = GPIO33, Green = GPIO32
const uint8_t  PIN_LED[3]    = {23, 27, 26};   // Red = GPIO23, Yellow = GPIO27, Green = GPIO26
const uint8_t  PIN_BUZZER    = 18;
const uint8_t  PIN_SDA       = 21;
const uint8_t  PIN_SCL       = 22;
const bool     IR_ACTIVE_LOW = true;           // FC-51 style sensors pull OUT low when blocked
// Reverse the reading of a sensor (Red, Yellow, Green). true = that sensor works the opposite way round.
const bool     IR_INVERT[3]  = {false, false, false};
const bool     IR_SWAP_RED_GREEN = false;      // only if the Red and Green sensor WIRES are plugged in swapped
const bool     BUZZER_ACTIVE_LOW = false;      // ACTIVE buzzer module that sounds when its pin goes LOW (only used when BUZZER_ACTIVE = true)
const bool     SOUND_ON      = true;           // false = silent game (the hardware test still beeps)
const bool     ATTRACT_JINGLE = true;          // play a short fairground tune now and then while waiting for a player
const uint32_t ATTRACT_EVERY_MS = 40000;
const bool     BUZZER_ACTIVE = false;          // false = PASSIVE buzzer (plays tones); true = ACTIVE buzzer (simple beeper)
const bool     LED_ACTIVE_LOW = false;         // true if the LEDs are wired from 3.3 V to the pin

const char*    AP_SSID       = "CarnivalGame";
const char*    AP_PASS       = "carnival123";  // at least 8 characters, or "" for an open network

const uint16_t GAME_SECONDS    = 30;
const uint32_t MISS_TIMEOUT_MS = 6000;         // ball gone from the camera and not in its hole after this = lost
const uint32_t RESULT_SHOW_MS  = 8000;         // win / game-over screen time before next round
const uint32_t IR_DEBOUNCE_MS  = 40;
// ===========================================================================

enum GameState : uint8_t { ST_READY, ST_PLAYING, ST_WIN, ST_LOSE };
enum BallState : uint8_t { BALL_OFF, BALL_TABLE, BALL_FLIGHT, BALL_SCORED, BALL_MISSED };

// types must be defined before the first function (the Arduino IDE auto-generates prototypes above it)
struct Note { uint16_t freq; uint16_t ms; };

const char* const STATE_NAME[4] = {"READY", "PLAYING", "WIN", "LOSE"};
const char* const LEVEL_NAME[4] = {"", "Easy", "Normal", "Hard"};
const char BALL_CH[3]   = {'R', 'Y', 'G'};
const char BALL_CODE[5] = {'n', 't', 'f', 's', 'm'};   // matches BallState order

// ---------- globals ----------
Adafruit_SSD1306 display(128, 64, &Wire, -1);
WebServer server(80);
bool oledOk = false;

GameState state = ST_READY;
uint8_t   level = 1;             // 1..3, also the number of balls
uint8_t   needed = 1;
uint8_t   score = 0;
BallState ball[3];
uint32_t  thrownAt[3];
bool      ledScored[3];
uint32_t  gameStart = 0, endAt = 0;
int       secsAtEnd = 0, lastTickSec = -1;
const char* loseReason = "";

bool optMatch = true;            // ball colour must match the hole colour
bool optAllGone = true;          // lose when every ball is used up
uint8_t requireMask = 0;          // holes (bit0 red, bit1 yellow, bit2 green) whose sensor only counts when the camera saw a ball close to that hole
int8_t  nearC[3] = {-1, -1, -1};  // colour of the ball the camera last saw close to each hole
uint32_t nearAt[3] = {0, 0, 0};
const uint32_t NEAR_WINDOW_MS = 1500;   // the camera "ball is close to the hole" report stays valid this long
bool optLoseOnMiss = true;       // game over the moment a ball is lost (gone from the screen, not scored)
bool optAutoStart = false;       // first thrown ball starts the clock

bool     holeRaw[3], holeStable[3];
uint32_t holeChange[3];

// hole teaching: which physical IR sensor belongs to which colour (saved in flash)
uint8_t  holeMap[3] = {0, 1, 2};     // holeMap[sensor] = colour index
int      teachColor = -1;            // >= 0 while waiting for a ball in that colour's hole
uint32_t teachStart = 0;
int      orphanHole = -1;            // wrong-colour hole hit while no ball was known to be in the air
uint32_t orphanAt = 0;
Preferences prefs;

uint32_t holeFlashUntil[3] = {0, 0, 0};   // a hole's LED blinks whenever its sensor is blocked

uint32_t lastOled = 0, lastSend = 0;
String   rxLine;

// milliseconds since time t, never negative (t can be a few ms newer than 'now' inside one loop pass)
uint32_t since(uint32_t now, uint32_t t) {
  int32_t d = (int32_t)(now - t);
  return d < 0 ? 0 : (uint32_t)d;
}

// ---------- sound ----------
// carnival sound effects (all original little tunes; frequencies in Hz, times in ms)
const Note TUNE_START[]  = {{523, 90}, {659, 90}, {784, 90}, {1047, 260}};                                  // bugle: ta-ta-ta-TAAA
const Note TUNE_SCORE_R[] = {{1047, 80}, {1319, 70}, {1568, 200}};                                          // bell dings, one pitch per colour
const Note TUNE_SCORE_Y[] = {{1175, 80}, {1480, 70}, {1760, 200}};
const Note TUNE_SCORE_G[] = {{1319, 80}, {1661, 70}, {2093, 240}};
const Note TUNE_SCORE[]  = {{880, 80}, {1320, 80}, {1760, 160}};                                            // generic ding (teaching)
const Note TUNE_WRONG[]  = {{500, 50}, {420, 50}, {340, 50}, {260, 50}, {200, 90}, {0, 40}, {150, 300}};    // cartoon "boing-wom"
const Note TUNE_TICK[]   = {{1800, 70}};                                                                    // last 5 seconds
const Note TUNE_WARN[]   = {{1500, 70}, {0, 60}, {1500, 70}};                                               // 10 seconds left
const Note TUNE_CLICK[]  = {{1200, 50}};
const Note TUNE_WIN[]    = {{523, 110}, {659, 110}, {784, 110}, {1047, 220}, {0, 50},                       // fanfare + calliope run
                            {988, 90}, {1047, 90}, {1175, 90}, {1319, 90}, {1568, 90}, {1760, 90}, {2093, 520}};
const Note TUNE_LOSE[]   = {{392, 260}, {370, 260}, {349, 260}, {330, 760}};                                // sad trombone: wah wah wah waaah
const Note TUNE_ATTRACT[] = {{523, 140}, {659, 140}, {784, 140}, {659, 140}, {523, 140}, {659, 140}, {784, 280}, {0, 80},   // merry-go-round
                             {698, 140}, {880, 140}, {1047, 140}, {880, 140}, {698, 140}, {880, 140}, {1047, 280}};
#define PLAY(t) playTune(t, sizeof(t) / sizeof(t[0]))

const Note* tunePtr = nullptr;
uint8_t tuneLen = 0, tuneIdx = 0;
uint32_t noteEnd = 0;

#if ESP_ARDUINO_VERSION_MAJOR >= 3
void buzzerInit() {
  if (BUZZER_ACTIVE) { pinMode(PIN_BUZZER, OUTPUT); digitalWrite(PIN_BUZZER, BUZZER_ACTIVE_LOW ? HIGH : LOW); return; }
  ledcAttach(PIN_BUZZER, 2000, 8); ledcWriteTone(PIN_BUZZER, 0);
}
void buzzerTone(uint16_t f) {
  if (BUZZER_ACTIVE) { digitalWrite(PIN_BUZZER, (f != 0) != BUZZER_ACTIVE_LOW ? HIGH : LOW); return; }
  ledcWriteTone(PIN_BUZZER, f);
}
#else
const uint8_t BUZZER_CH = 0;
void buzzerInit() {
  if (BUZZER_ACTIVE) { pinMode(PIN_BUZZER, OUTPUT); digitalWrite(PIN_BUZZER, BUZZER_ACTIVE_LOW ? HIGH : LOW); return; }
  ledcSetup(BUZZER_CH, 2000, 8); ledcAttachPin(PIN_BUZZER, BUZZER_CH); ledcWriteTone(BUZZER_CH, 0);
}
void buzzerTone(uint16_t f) {
  if (BUZZER_ACTIVE) { digitalWrite(PIN_BUZZER, (f != 0) != BUZZER_ACTIVE_LOW ? HIGH : LOW); return; }
  ledcWriteTone(BUZZER_CH, f);
}
#endif

void ledWrite(int i, bool on) { digitalWrite(PIN_LED[i], (on != LED_ACTIVE_LOW) ? HIGH : LOW); }

// ---- hardware self-test: each LED lights with its own beep, then all together ----
int hwStep = -1;
uint32_t hwAt = 0;
void applyHwStep() {
  const uint16_t f[3] = {523, 659, 784};
  for (int i = 0; i < 3; i++) ledWrite(i, false);
  if (hwStep >= 0 && hwStep < 3) { ledWrite(hwStep, true); buzzerTone(f[hwStep]); }
  else if (hwStep == 3)          { for (int i = 0; i < 3; i++) ledWrite(i, true); buzzerTone(1047); }
  else                           { buzzerTone(0); hwStep = -1; }
}
/* PINTEST (type it in the Serial Monitor): every free GPIO in turn gets a 2 kHz signal for 0.7 s and its number is printed.
   Whichever number makes your buzzer beep or your LED glow is the pin it is wired to. Then put that number in PIN_BUZZER / PIN_LED. */
void pinFinder() {
  const uint8_t cand[] = {4, 5, 13, 14, 15, 16, 17, 18, 19, 23, 26, 27};
#if ESP_ARDUINO_VERSION_MAJOR >= 3
  if (!BUZZER_ACTIVE) ledcDetach(PIN_BUZZER);
#else
  if (!BUZZER_ACTIVE) ledcDetachPin(PIN_BUZZER);
#endif
  Serial.println("PINTEST start - watch the LEDs and listen to the buzzer");
  for (uint8_t k = 0; k < sizeof(cand); k++) {
    uint8_t p = cand[k];
    Serial.printf("PINTEST pin %u\n", p);
    pinMode(p, OUTPUT);
    for (int n = 0; n < 1400; n++) { digitalWrite(p, HIGH); delayMicroseconds(250); digitalWrite(p, LOW); delayMicroseconds(250); }
    digitalWrite(p, LOW);
    delay(250);
  }
  Serial.println("PINTEST done");
  buzzerInit();
  for (int i = 0; i < 3; i++) { pinMode(PIN_LED[i], OUTPUT); ledWrite(i, false); }
}
void startHwTest() { hwStep = 0; hwAt = millis(); applyHwStep(); }
void hwTick(uint32_t now) {
  if (hwStep < 0 || (int32_t)(now - hwAt) < 500) return;
  hwStep++; hwAt = now; applyHwStep();
}

void startNote() {
  buzzerTone(tunePtr[tuneIdx].freq);
  noteEnd = millis() + tunePtr[tuneIdx].ms;
}

uint32_t lastPlayAt = 0;
void playTune(const Note* t, uint8_t n) {
  lastPlayAt = millis();
  if (!SOUND_ON) return;
  tunePtr = t; tuneLen = n; tuneIdx = 0;
  startNote();
}
void playScore(int colour) {
  if (colour == 1) PLAY(TUNE_SCORE_Y);
  else if (colour == 2) PLAY(TUNE_SCORE_G);
  else PLAY(TUNE_SCORE_R);
}

void soundUpdate() {
  if (!tunePtr) {                                      // quiet: now and then play the fairground tune while waiting for a player
    if (ATTRACT_JINGLE && SOUND_ON && state == ST_READY && hwStep < 0 && teachColor < 0 &&
        since(millis(), lastPlayAt) >= ATTRACT_EVERY_MS) PLAY(TUNE_ATTRACT);
    return;
  }
  if ((int32_t)(millis() - noteEnd) < 0) return;
  tuneIdx++;
  if (tuneIdx >= tuneLen) { buzzerTone(0); tunePtr = nullptr; return; }
  startNote();
}

// ---------- Bluetooth LE link (Nordic UART style) + USB serial output ----------
#define SERVICE_UUID "6E400001-B5A3-F393-E0A9-E50E24DCCA9E"
#define RX_UUID      "6E400002-B5A3-F393-E0A9-E50E24DCCA9E"   // web page -> ESP32 (write)
#define TX_UUID      "6E400003-B5A3-F393-E0A9-E50E24DCCA9E"   // ESP32 -> web page (notify)

BLECharacteristic* bleTx = nullptr;
volatile bool bleConnected = false;
char bleRing[512];                                   // bytes received over Bluetooth (filled by the BLE task)
volatile uint16_t bleHead = 0, bleTail = 0;
String bleOut;                                       // text waiting to be sent, 20 bytes at a time
uint32_t bleLastTx = 0;

class BleServerCb : public BLEServerCallbacks {
public:
  void onConnect(BLEServer*) override    { bleConnected = true; }
  void onDisconnect(BLEServer*) override { bleConnected = false; BLEDevice::startAdvertising(); }
};
class BleRxCb : public BLECharacteristicCallbacks {
public:
  void onWrite(BLECharacteristic* c) override {
    auto v = c->getValue();
    for (size_t i = 0; i < v.length(); i++) {
      uint16_t n = (bleHead + 1) % sizeof(bleRing);
      if (n == bleTail) break;                       // buffer full: drop
      bleRing[bleHead] = v[i];
      bleHead = n;
    }
  }
};

void bleSetup() {
  BLEDevice::init("CarnivalGame");
  BLEServer* server = BLEDevice::createServer();
  server->setCallbacks(new BleServerCb());
  BLEService* svc = server->createService(SERVICE_UUID);
  bleTx = svc->createCharacteristic(TX_UUID, BLECharacteristic::PROPERTY_NOTIFY);
  bleTx->addDescriptor(new BLE2902());
  BLECharacteristic* rx = svc->createCharacteristic(RX_UUID,
      BLECharacteristic::PROPERTY_WRITE | BLECharacteristic::PROPERTY_WRITE_NR);
  rx->setCallbacks(new BleRxCb());
  svc->start();
  BLEAdvertising* adv = BLEDevice::getAdvertising();
  adv->addServiceUUID(SERVICE_UUID);
  adv->setScanResponse(true);
  BLEDevice::startAdvertising();
}

void bleFlush(uint32_t now) {                        // one small packet per call keeps the radio from overflowing
  if (!bleConnected || !bleTx || bleOut.length() == 0 || now - bleLastTx < 12) return;
  size_t n = bleOut.length() < 20 ? bleOut.length() : 20;
  String chunk = bleOut.substring(0, n);
  bleOut = bleOut.substring(n);
  bleTx->setValue((uint8_t*)chunk.c_str(), n);
  bleTx->notify();
  bleLastTx = now;
}

// one protocol line -> USB serial and (if connected) Bluetooth
void linef(const char* fmt, ...) {
  char b[160];
  va_list a; va_start(a, fmt); vsnprintf(b, sizeof(b) - 1, fmt, a); va_end(a);
  size_t n = strlen(b);
  if (n == 0 || b[n - 1] != '\n') { b[n++] = '\n'; b[n] = 0; }
  Serial.print(b);
  if (bleConnected) {
    if (bleOut.length() > 600) bleOut = "";
    bleOut += b;
  }
}

// ---------- serial output to the web page ----------
int secsLeft() {
  if (state == ST_PLAYING) {
    uint32_t el = since(millis(), gameStart);
    int left = (int)GAME_SECONDS - (int)(el / 1000);
    return left < 0 ? 0 : left;
  }
  if (state == ST_READY) return GAME_SECONDS;
  return secsAtEnd;
}

void sendState() {
  char balls[4], leds[4];
  for (int i = 0; i < 3; i++) {
    balls[i] = BALL_CODE[ball[i]];
    leds[i]  = ledScored[i] ? '1' : '0';
  }
  balls[3] = 0; leds[3] = 0;
  linef("S,%s,%u,%u,%u,%d,%s,%s\n", STATE_NAME[state], level, needed, score,
                secsLeft(), balls, leds);
}

void sendEvent(const char* name)               { linef("E,%s\n", name); }
void sendEventCh(const char* name, int idx)    { linef("E,%s,%c\n", name, BALL_CH[idx]); }

// ---------- hole teaching ----------
void sendMap() {
  linef("M,%c%c%c\n", BALL_CH[holeMap[0]], BALL_CH[holeMap[1]], BALL_CH[holeMap[2]]);
}

void saveMap() {
  prefs.begin("carnival", false);
  prefs.putBytes("map", holeMap, 3);
  prefs.end();
}

void loadMap() {
  uint8_t m[3] = {0, 1, 2};
  prefs.begin("carnival", true);
  size_t n = prefs.getBytes("map", m, 3);
  prefs.end();
  bool valid = (n == 3);
  for (int i = 0; i < 3 && valid; i++) {
    if (m[i] > 2) valid = false;
    for (int j = 0; j < i; j++) if (m[i] == m[j]) valid = false;
  }
  if (valid) for (int i = 0; i < 3; i++) holeMap[i] = m[i];
}

void learnHole(int sensor) {                         // a sensor was blocked while teaching
  int c = teachColor;
  teachColor = -1;
  for (int p = 0; p < 3; p++) {                      // keep the map one-to-one: swap with the old owner
    if (p != sensor && holeMap[p] == c) holeMap[p] = holeMap[sensor];
  }
  holeMap[sensor] = c;
  saveMap();
  sendMap();
  sendEventCh("TAUGHT", c);
  PLAY(TUNE_SCORE);
}

// ---------- game logic ----------
void resetToReady() {
  state = ST_READY;
  needed = level;
  score = 0;
  for (int i = 0; i < 3; i++) {
    ball[i] = (i < needed) ? BALL_TABLE : BALL_OFF;
    ledScored[i] = false;
  }
  orphanHole = -1;
  for (int i = 0; i < 3; i++) nearC[i] = -1;
  tunePtr = nullptr; buzzerTone(0);
  sendEvent("READY");
  sendState();
}

void startGame() {
  state = ST_PLAYING;
  gameStart = millis();
  score = 0;
  needed = level;
  lastTickSec = -1;
  orphanHole = -1;
  for (int i = 0; i < 3; i++) {
    ball[i] = (i < needed) ? BALL_TABLE : BALL_OFF;
    ledScored[i] = false;
  }
  PLAY(TUNE_START);
  sendEvent("START");
  sendState();
}

void endGame(bool win, const char* reason) {
  secsAtEnd = secsLeft();
  state = win ? ST_WIN : ST_LOSE;
  endAt = millis();
  loseReason = reason;
  if (win) {
    PLAY(TUNE_WIN);
    sendEvent("WIN");
  } else {
    PLAY(TUNE_LOSE);
    linef("E,LOSE,%s\n", reason);
  }
  sendState();
}

void checkAllGone() {
  if (state != ST_PLAYING || !optAllGone) return;
  for (int i = 0; i < needed; i++) {
    if (ball[i] != BALL_SCORED && ball[i] != BALL_MISSED) return;   // still something to play
  }
  if (score < needed) endGame(false, "BALLS");
}

void setLevel(int n) {
  if (n < 1 || n > 3) return;
  level = n;
  resetToReady();
  PLAY(TUNE_CLICK);
  linef("E,LEVEL,%d\n", n);
}

void onThrow(int c) {
  if (c < 0 || c >= needed) return;                 // that ball is not used in this level
  if (state == ST_READY) {
    if (!optAutoStart) return;
    startGame();
  }
  if (state != ST_PLAYING) return;
  if (ball[c] == BALL_TABLE) {
    ball[c] = BALL_FLIGHT;
    thrownAt[c] = millis();
    sendEventCh("THROW", c);
    if (optMatch && orphanHole >= 0 && since(millis(), orphanAt) < 2000) {
      sendEventCh("WRONG", orphanHole);              // that ball went into a hole of another colour
      orphanHole = -1;
      ball[c] = BALL_MISSED;
      PLAY(TUNE_WRONG);
      endGame(false, "WRONG");
      return;
    }
    sendState();
  }
}

void onBack(int c) {                                // camera sees the ball on the table again
  if (c < 0 || c >= 3) return;
  if (state == ST_PLAYING && (ball[c] == BALL_FLIGHT || ball[c] == BALL_MISSED)) {
    ball[c] = BALL_TABLE;           // it was only moved / balanced, not thrown
    sendEventCh("BACK", c);
    sendState();
  }
}

int oldestInFlight() {
  int best = -1;
  uint32_t t = 0;
  for (int i = 0; i < needed; i++) {
    if (ball[i] == BALL_FLIGHT && (best < 0 || (int32_t)(thrownAt[i] - t) < 0)) {
      best = i; t = thrownAt[i];
    }
  }
  return best;
}

void onHole(int sensor) {                           // a ball just blocked an IR sensor
  if (teachColor >= 0) { learnHole(sensor); return; }
  int h = holeMap[sensor];                           // colour of that hole
  sendEventCh("HOLE", h);
  holeFlashUntil[h] = millis() + 350;                // visible + audible proof that the sensor works
  if (state != ST_PLAYING) PLAY(TUNE_CLICK);
  if (state != ST_PLAYING) return;

  // The hole sensor is the real proof of a score. The camera only helps to tell WHICH ball it was:
  // a ball seen leaving the table is preferred, but a ball whose "thrown" signal has not arrived yet
  // (camera delay, or dropped in by hand) still counts when no other ball is in the air.
  int b = -1;
  int flying = oldestInFlight();
  if (requireMask & (1 << h)) {
    // Camera-checked hole: the ball the camera saw close to this hole decides everything.
    bool seen = nearC[h] >= 0 && since(millis(), nearAt[h]) <= NEAR_WINDOW_MS;
    int c = seen ? nearC[h] : -1;
    nearC[h] = -1;
    if (c < 0) {                                       // sensor fired but no ball was near the hole (hand, object, cheating)
      sendEventCh("NOBALL", h);
      PLAY(TUNE_WRONG);
      sendState();
      endGame(false, "NOBALL");
      return;
    }
    if (c != h) {                                      // e.g. green ball in the red hole
      if (c < 3 && ball[c] != BALL_OFF) ball[c] = BALL_MISSED;
      sendEventCh("WRONG", h);
      PLAY(TUNE_WRONG);
      sendState();
      endGame(false, "WRONG");
      return;
    }
    if (h >= needed || ball[h] == BALL_SCORED) return; // not in this level, or the same ball still sitting in the hole
    b = h;
  } else if (optMatch) {
    if (h < needed) {
      if (ball[h] == BALL_FLIGHT) b = h;
      else if (ball[h] == BALL_TABLE && flying < 0) b = h;
    }
  } else {
    if (flying >= 0) b = flying;
    else if (h < needed && ball[h] == BALL_TABLE) b = h;
    else for (int i = 0; i < needed && b < 0; i++) if (ball[i] == BALL_TABLE) b = i;
  }

  if (b >= 0) {
    ball[b] = BALL_SCORED;
    ledScored[h] = true;
    score++;
    sendEventCh("SCORE", b);
    playScore(b);
    sendState();
    if (score >= needed) endGame(true, "");
    else checkAllGone();
    return;
  }

  // not a scoring hit: if some other ball is in the air it went into the wrong hole
  // Ball colour and hole colour do not match -> game over.
  int w = oldestInFlight();
  if (w >= 0) {
    ball[w] = BALL_MISSED;
    sendEventCh("WRONG", h);
    PLAY(TUNE_WRONG);
    sendState();
    endGame(false, "WRONG");
  } else if (optMatch) {
    orphanHole = h;                                  // the camera has not reported which ball yet
    orphanAt = millis();
  }
}

void gameTick(uint32_t now) {
  if (teachColor >= 0 && since(now, teachStart) > 20000) { teachColor = -1; sendEvent("TEACHEND"); }
  if (state == ST_PLAYING) {
    for (int i = 0; i < needed; i++) {              // balls that never reached a hole
      if (ball[i] == BALL_FLIGHT && since(now, thrownAt[i]) > MISS_TIMEOUT_MS) {
        ball[i] = BALL_MISSED;
        sendEventCh("MISS", i);
        PLAY(TUNE_WRONG);
        sendState();
        if (optLoseOnMiss) { endGame(false, "LOST"); return; }
        checkAllGone();
        if (state != ST_PLAYING) return;
      }
    }
    if (since(now, gameStart) >= (uint32_t)GAME_SECONDS * 1000UL) {
      endGame(false, "TIME");
      return;
    }
    int left = secsLeft();
    if (left <= 5 && left > 0 && left != lastTickSec) {   // time running out
      lastTickSec = left;
      PLAY(TUNE_TICK);
    } else if (left == 10 && left != lastTickSec) {
      lastTickSec = left;
      PLAY(TUNE_WARN);
    }
  } else if (state == ST_WIN || state == ST_LOSE) {
    if (since(now, endAt) >= RESULT_SHOW_MS) resetToReady();
  }
}

// ---------- IR sensors ----------
uint8_t irPin(int i) {                               // which pin really belongs to this colour's sensor
  if (IR_SWAP_RED_GREEN && i == 0) return PIN_IR[2];
  if (IR_SWAP_RED_GREEN && i == 2) return PIN_IR[0];
  return PIN_IR[i];
}
bool irActiveLow(int i) { return IR_ACTIVE_LOW != IR_INVERT[i]; }
bool readHole(int i) {
  bool low = digitalRead(irPin(i)) == LOW;
  return irActiveLow(i) ? low : !low;
}

void pollHoles(uint32_t now) {
  for (int i = 0; i < 3; i++) {
    bool raw = readHole(i);
    if (raw != holeRaw[i]) { holeRaw[i] = raw; holeChange[i] = now; }
    if (holeStable[i] != holeRaw[i] && since(now, holeChange[i]) >= IR_DEBOUNCE_MS) {
      holeStable[i] = holeRaw[i];
      if (holeStable[i]) onHole(i);                 // only the "ball arrives" edge counts
    }
  }
}

// ---------- LEDs ----------
void updateLeds(uint32_t now) {
  if (hwStep >= 0) return;                           // self-test is driving the LEDs
  bool on[3];
  bool anim = (state == ST_WIN || state == ST_LOSE) && (since(now, endAt) < 3000);
  if (anim && state == ST_WIN) {
    int idx = (now / 150) % 3;
    for (int i = 0; i < 3; i++) on[i] = (i == idx);
  } else if (anim && state == ST_LOSE) {
    bool blink = ((now / 400) % 2) == 0;
    for (int i = 0; i < 3; i++) on[i] = blink;
  } else {
    bool slow = ((now / 400) % 2) == 0;
    for (int i = 0; i < 3; i++) {
      bool waiting = (state == ST_PLAYING) && i < needed && !ledScored[i] && slow;   // colours still to score blink while playing
      on[i] = ledScored[i] || waiting || (int32_t)(holeFlashUntil[i] - now) > 0;
    }
  }
  for (int i = 0; i < 3; i++) ledWrite(i, on[i]);
}

// ---------- OLED ----------
void drawOled() {
  if (!oledOk) return;
  display.clearDisplay();
  display.setTextColor(SSD1306_WHITE);
  if (teachColor >= 0) {
    display.setTextSize(1); display.setCursor(0, 0);  display.print("TEACH HOLE");
    display.setTextSize(2); display.setCursor(0, 18);
    display.print(teachColor == 0 ? "RED" : teachColor == 1 ? "YELLOW" : "GREEN");
    display.setTextSize(1); display.setCursor(0, 44); display.print("Put a ball in that");
    display.setCursor(0, 54); display.print("hole to teach it");
    display.display();
    return;
  }
  switch (state) {
    case ST_READY:
      display.setTextSize(1); display.setCursor(0, 0);  display.print("CARNIVAL GAME");
      display.setTextSize(2); display.setCursor(0, 16); display.print(LEVEL_NAME[level]);
      display.setTextSize(1); display.setCursor(0, 40); display.printf("Balls: %u  Time: %us", needed, GAME_SECONDS);
      display.setCursor(0, 54); display.print("Throw a ball to start");
      break;
    case ST_PLAYING:
      display.setTextSize(3); display.setCursor(0, 0);  display.printf("%ds", secsLeft());
      display.setTextSize(1); display.setCursor(86, 8); display.printf("Goal:%u", needed);
      display.setTextSize(2); display.setCursor(0, 28); display.printf("Score:%u", score);
      display.setTextSize(1); display.setCursor(0, 52); display.printf("Level: %s", LEVEL_NAME[level]);
      break;
    case ST_WIN:
      display.setTextSize(3); display.setCursor(0, 6);  display.print("YOU WIN");
      display.setTextSize(1); display.setCursor(0, 40); display.printf("Score: %u/%u", score, needed);
      display.setCursor(0, 54); display.printf("Level: %s", LEVEL_NAME[level]);
      break;
    case ST_LOSE:
      display.setTextSize(2); display.setCursor(0, 6);  display.print("GAME OVER");
      display.setTextSize(1); display.setCursor(0, 32);
      display.print(strcmp(loseReason, "TIME") == 0 ? "Time is up!" :
                    strcmp(loseReason, "LOST") == 0 ? "Ball lost!" :
                    strcmp(loseReason, "WRONG") == 0 ? "Wrong hole!" :
                    strcmp(loseReason, "NOBALL") == 0 ? "No ball near!" : "No balls left!");
      display.setCursor(0, 46); display.printf("Score: %u/%u", score, needed);
      break;
  }
  display.display();
}

// ---------- commands (from USB serial) ----------
String field(const String& s, int n) {
  int start = 0;
  for (int i = 0; i < n; i++) {
    int p = s.indexOf(',', start);
    if (p < 0) return "";
    start = p + 1;
  }
  int e = s.indexOf(',', start);
  return e < 0 ? s.substring(start) : s.substring(start, e);
}

int colorIndex(const String& s) {
  if (s.length() < 1) return -1;
  switch (s[0]) { case 'R': return 0; case 'Y': return 1; case 'G': return 2; }
  return -1;
}

void doStart() {
  if (state == ST_PLAYING) return;
  if (state != ST_READY) resetToReady();
  startGame();
}

void handleCommand(String line) {
  line.trim();
  if (!line.length()) return;
  String cmd = field(line, 0);
  if      (cmd == "LEVEL") setLevel(field(line, 1).toInt());
  else if (cmd == "START") doStart();
  else if (cmd == "RESET") resetToReady();
  else if (cmd == "T")     onThrow(colorIndex(field(line, 1)));
  else if (cmd == "B")     onBack(colorIndex(field(line, 1)));
  else if (cmd == "CFG") {
    optMatch     = field(line, 1) != "0";
    optAllGone   = field(line, 2) != "0";
    optAutoStart = field(line, 3) != "0";
    optLoseOnMiss = field(line, 4) != "0";
    requireMask = field(line, 5).toInt() & 7;
  }
  else if (cmd == "NEAR") {                             // NEAR,<hole colour>,<ball colour>: the camera sees that ball close to that hole
    int h = colorIndex(field(line, 1)), c = colorIndex(field(line, 2));
    if (h >= 0 && h < 3 && c >= 0 && c < 3) { nearC[h] = c; nearAt[h] = millis(); }
  }
  else if (cmd == "TEACH") {
    int c = colorIndex(field(line, 1));
    if (c >= 0 && state != ST_PLAYING) { teachColor = c; teachStart = millis(); PLAY(TUNE_CLICK); sendEventCh("TEACH", c); }
  }
  else if (cmd == "PINTEST") { if (state != ST_PLAYING) pinFinder(); }
  else if (cmd == "TESTHW") { if (state != ST_PLAYING) { startHwTest(); sendEvent("TESTHW"); } }
  else if (cmd == "TEACHCANCEL") { teachColor = -1; sendEvent("TEACHEND"); }
  else if (cmd == "MAPRESET")    { for (int i = 0; i < 3; i++) holeMap[i] = i; saveMap(); sendMap(); sendEvent("MAPRESET"); }
  else if (cmd == "SYNC")  { linef("HELLO,CarnivalGame\n"); sendState(); sendMap(); }
}

void feedChar(String& line, char c) {
  if (c == '\n' || c == '\r') {
    if (line.length()) { handleCommand(line); line = ""; }
  } else if (line.length() < 64) {
    line += c;
  }
}

String bleLine;
void serialPoll() {
  while (Serial.available()) feedChar(rxLine, (char)Serial.read());
  while (bleTail != bleHead) {                       // commands that arrived over Bluetooth
    char c = bleRing[bleTail];
    bleTail = (bleTail + 1) % sizeof(bleRing);
    feedChar(bleLine, c);
  }
}

// ---------- Wi-Fi remote (http://192.168.1.1) ----------
const char REMOTE_HTML[] PROGMEM = R"rawliteral(<!DOCTYPE html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Carnival Remote</title>
<style>
body{font-family:system-ui,sans-serif;background:#120f33;color:#fff;margin:0;padding:18px;text-align:center}
h1{font-size:22px;margin:4px 0 14px}
.box{background:#201a58;border-radius:14px;padding:14px;margin:0 auto 16px;max-width:420px}
button{display:block;width:100%;margin:10px 0;padding:18px;font-size:20px;font-weight:700;border:0;border-radius:12px;color:#fff;background:#3b6bff}
button.hard{background:#d6336c}button.normal{background:#e6a100}button.easy{background:#2f9e44}
button.go{background:#6741d9}button.rs{background:#495057}
#st{font-size:20px;line-height:1.5}
</style></head><body>
<h1>Carnival Game Remote</h1>
<div class="box"><div id="st">Connecting...</div></div>
<div class="box"><div>Select Level</div>
<button class="easy" onclick="go('/level?n=1')">Easy - 1 ball</button>
<button class="normal" onclick="go('/level?n=2')">Normal - 2 balls</button>
<button class="hard" onclick="go('/level?n=3')">Hard - 3 balls</button>
<button class="go" onclick="go('/start')">Start</button>
<button class="rs" onclick="go('/reset')">Reset</button></div>
<script>
function go(u){fetch(u).then(poll).catch(function(){});}
function poll(){fetch('/state').then(function(r){return r.json()}).then(function(s){
document.getElementById('st').innerHTML='<b>'+s.state+'</b><br>Level: '+s.levelName+' ('+s.needed+' ball'+(s.needed>1?'s':'')+')<br>Score: '+s.score+'/'+s.needed+'<br>Time: '+s.secs+'s';
}).catch(function(){document.getElementById('st').textContent='No connection';});}
setInterval(poll,700);poll();
</script></body></html>)rawliteral";

void setupWeb() {
  WiFi.mode(WIFI_AP);
  WiFi.softAPConfig(IPAddress(192, 168, 1, 1), IPAddress(192, 168, 1, 1), IPAddress(255, 255, 255, 0));
  if (strlen(AP_PASS) >= 8) WiFi.softAP(AP_SSID, AP_PASS);
  else                      WiFi.softAP(AP_SSID);

  server.on("/", HTTP_GET, []() { server.send_P(200, "text/html", REMOTE_HTML); });
  server.on("/level", HTTP_GET, []() { setLevel(server.arg("n").toInt()); server.send(200, "text/plain", "ok"); });
  server.on("/start", HTTP_GET, []() { doStart();       server.send(200, "text/plain", "ok"); });
  server.on("/reset", HTTP_GET, []() { resetToReady();  server.send(200, "text/plain", "ok"); });
  server.on("/state", HTTP_GET, []() {
    char buf[160];
    snprintf(buf, sizeof(buf),
             "{\"state\":\"%s\",\"level\":%u,\"levelName\":\"%s\",\"needed\":%u,\"score\":%u,\"secs\":%d}",
             STATE_NAME[state], level, LEVEL_NAME[level], needed, score, secsLeft());
    server.send(200, "application/json", buf);
  });
  server.begin();
}

// ---------- setup / loop ----------
void setup() {
  Serial.begin(115200);

  for (int i = 0; i < 3; i++) {
    pinMode(irPin(i), irActiveLow(i) ? INPUT_PULLUP : INPUT_PULLDOWN);
    pinMode(PIN_LED[i], OUTPUT);
    ledWrite(i, false);
  }
  buzzerInit();

  Wire.begin(PIN_SDA, PIN_SCL);
  Wire.setClock(400000);
  oledOk = display.begin(SSD1306_SWITCHCAPVCC, 0x3C);

  loadMap();
  setupWeb();
  bleSetup();

  delay(400);
  for (int i = 0; i < 3; i++) {
    holeRaw[i] = holeStable[i] = readHole(i);       // a ball already sitting in a hole is not a new hit
    holeChange[i] = millis();
  }

  resetToReady();
  startHwTest();                                     // power-up self-test: you should see and hear it
  linef("HELLO,CarnivalGame\n");
  sendMap();
}

void loop() {
  uint32_t now = millis();
  server.handleClient();
  serialPoll();
  now = millis();                 // commands above may have started the game just now
  pollHoles(now);
  gameTick(now);
  updateLeds(now);
  hwTick(now);
  soundUpdate();
  bleFlush(now);

  if (now - lastOled >= 150) { lastOled = now; drawOled(); }
  if (now - lastSend >= (state == ST_PLAYING ? 250UL : 1000UL)) { lastSend = now; sendState(); }
}
