
/*
   This is Rev 45 (Labeled 4510) of the Silkrip Mark IV ORR Computer
   Written by Tom King 250415  
This is based on the successful Sim and Test version of 3/25/25.  It maintains the conversion to scaled integer, 
the separated "distance between" function subroutine, the conversion to thousandths of a mile as the 
distance representation, and the careful tuning of the integrated distance algorithm that
were part of the successful simulation.
  Note: Rev 45 eliminates the Dual Speed option and eliminates the Mileage Factor array
*/

// INCLUDE LIBRARIES:

#include <NoiascaLedControl.h>
#include <NoiascaLedControlCommon.h>
#include <NoiascaLedControlSpi.h>
#include <SPI.h>
#include <SD.h>
#include <Timer5.h>
#include <Adafruit_PMTK.h>
#include <TinyGPS++.h>
#include <Adafruit_GPS.h>
#include <Wire.h>
#include <math.h>
#include <stdio.h>

// DEFINE PINS ON THE ARDUINO MKRZERO:
#define CS_PIN SDCARD_SS_PIN
#define PB_PIN 4
#define SWPOS_PIN A6  //this pin is gnd when stopwatch switch is to the left
#define SPPOS_PIN 12  // this pin is gnd when stopwatch switch is to the right
#define REDLED_PIN A3
#define YELLED_PIN A4
#define PPS_PIN 6

// CREATE GPS OBJECT AND ATTACH TO SERIAL COMMUNICATION:
TinyGPSPlus tinyGPS;         // Create a TinyGPSPlus object
Adafruit_GPS GPS(&Serial1);  // Note that the "&" symbol
// points to the address of Serial1, so this connects
// the Adafruit_GPS library to the GPS Serial port
// You must have the Arduino MKRZero board as the target or the compile will fail here:
// "Serial1 not declared."

// DEFINE VARIABLES:
// Integers:
int timeSecs = 0;
int timeMin = 0;
int timeHr = 0;
int ToDStartSeconds = 0;
int ToDSeconds = 0;
int thousandthsDisplay = 0;
int milesDisplay = 0;
int ones = 0;
int tens = 0;
int Mones = 0;
int Mtens = 0;
int colno = 0;  // column number for array pointer calculations
int ABSABTime = 0;
int ABSecs = 0;
int ABCents = 0;
int hLat = 1;           // 1 = northern hemisphere; -1 = southern hemisphere
int hLng = -1;          // 1 = eastern hemisphere; -1 = western hemisphere
int L1brg = 0;          // 0 = bearing north, 1 = east, 2 = south, 3 = west
int L2brg = 0;          // bearing code for Leg 2
int currDay = 1;        // the current day from the GPS
int currMonth = 1;      // the current month from the GPS
int currYear = 25;      // the current year from the GPS
int ToDSecsOnly = 0;    // variable to allow display of seconds prior to a start
int perfectTime = 0;    // used for safeguard to ensure beyond finish
int spdMPH = 0;         // the integral portion of mph in the speed function
int spdThouMPH = 0;     // the thousandths portion of mph in the speed function
int targetSpeed = 120;  // TARGET SPEED (will change based on SD card if present)
int wayptTol = 20;      // Within this number of thousandths mile distance from a waypoint,
// take action at the waypoint (e.g., start, adjust mileage, etc.); 20 thousandths = 0.020 miles
int L1WP0LatDec = 0;
int L1WP0LngDec = 0;

float L1WP3LatDeg = 0.0;
float L1WP3LatDec = 0.0;
float L1WP3Lat = 0.0;
float L1WP3LngDeg = 0.0;
float L1WP3LngDec = 0.0;
float L1WP3Lng = 0.0;
float L2WP3LatDeg = 0.0;
float L2WP3LatDec = 0.0;
float L2WP3Lat = 0.0;
float L2WP3LngDeg = 0.0;
float L2WP3LngDec = 0.0;
float L2WP3Lng = 0.0;
float L1WP4LatDeg = 0.0;
float L1WP4LatDec = 0.0;
float L1WP4Lat = 0.0;
float L1WP4LngDeg = 0.0;
float L1WP4LngDec = 0.0;
float L1WP4Lng = 0.0;
float L2WP4LatDeg = 0.0;
float L2WP4LatDec = 0.0;
float L2WP4Lat = 0.0;
float L2WP4LngDeg = 0.0;
float L2WP4LngDec = 0.0;
float L2WP4Lng = 0.0;
float WPLat = 0.0;  // latitude of the upcoming waypoint
float WPLng = 0.0;  // longitude of the upcoming waypoint

float L1latDelta = 0.0;  // latitude difference between L1WP4 and L1WP3
float L1lngDelta = 0.0;  // longitude difference between L1WP4 and L1WP3
float L2latDelta = 0.0;  // latitude difference between L2WP4 and L2WP3
float L2lngDelta = 0.0;  // longitude difference between L2WP4 and L2WP3
float speedMPH = 0.0;    // the speed in miles per hour including decimals
float smMPH = 0.0;

// REV 45 variables:
volatile boolean justWriteOnce = false;
volatile int Deg = 0;
volatile int DecDeg = 0;

//Characters:
char latLetter = 'N';  // Note: " " is string, ' ' is character
char lngLetter = 'W';

// Boolean:
boolean initFlag = true;  // Initial flag to print first GPS data just once at beginning
boolean Milesdp = false;
boolean L1 = false;             // Flag to indicate Leg 1 is active
boolean L2 = false;             // Flag to indicate Leg 2 is active
boolean nearWP = false;         // flag to indicate nearing a waypoint mileage
boolean wayptNearOnce = false;  // flag to just take waypoint action once
boolean writeOnce = false;      // flag to ensure we just write errorOut once to SD card
boolean ABSnapshot = false;     // flag to snapshot final ABTime once
int ABSnap = 0;                 // snapshot of final ABTime
boolean freeRun = false;
boolean ABdp = false;
boolean locFlag = false;    // DIAGNOSTIC for single printout of location
boolean locFlagFR = false;  // location flag for Free Run mode
boolean noSD = false;       // Flag to indicate there is no SD card in the slot
boolean swSwitch = false;   // Flag indicating true if stopwatch switch is in left position
boolean spSwitch = false;   // flag indicating true if stopwatch switch is in the right position

int arrayLogDist[5];  // array to store thousandths from each waypoint when detected (or PB pushed)

// VOLATILES: (i.e., used in Interrupt Service Routines):

volatile int Miles = 0;        // start the mileage at 0
volatile int thousandths = 0;  // start the thousandths of a mile at 0
volatile int TenHzCtr = 0;
volatile int TenHertzCtr = 0;
volatile int incrDistSum = 0;
volatile int incrDist = 0;
volatile int waypt = 0;     // Each race has 5 waypoints: 0,1,2,3,4 where 0 is the start and 4 the finish
volatile int errorOut = 0;  // The number of centiseconds off in Leg 1
volatile int PPSCount = 0;
volatile int countTenPPS = 0;  // used for timing the red LED until it goes off in Race Mode
volatile int countTwoPPS = 0;  // used for timing the red LED in Free Run mode when PB is pushed
volatile int ABTime = 0;
volatile int actualTime = 0;      // actual time in centiseconds
volatile int actualTimeTS = 0;    // use this in REV 23X to close dynLAF vulnerability window
volatile int targetTime = 0;      // target time in centiseconds
volatile int oldMiles = 0;        // used for FRLogging to prevent duplicates
volatile int oldThousandths = 0;  // used for FRLogging to prevent duplicates
volatile int swCount = 0;         // the stopwatch count
volatile float latC = 35.0;
volatile float lngC = -120.0;
volatile float latCP = 0.0;     // frozen latitude after the finish
volatile float lngCP = 0.0;     // frozen longitude after the finish
volatile float distPast = 0.0;  // distance in thousandths of a mile past the finish line
volatile float velocityMPH = 0.0;
volatile float milesF = 0;
volatile float thousandthsF = 0;
volatile float targetM = 0;
volatile float targetMTime = 0;
volatile float targetT = 0;
volatile float targetTTime = 0;
// REV 23Y ADDITIONS:
volatile int actualTimeAtPF = 0;  // actual time snapshot after "past finish" is detected
//volatile int MilesAtPF = 0;         // Miles snapshot after "past finish"
volatile int thousandthsAtPF = 0;   // total thousandths miles snapshot after "past finish"
volatile float velocityAtPF = 0.0;  // velocity in mph per sec snapshot after "past finish"
volatile int dynLAFatPF = 0;        // dynLAF snapshot after "past finish"
volatile float actTimeAdj = 0.0;    // used to try to fix actualTime adjustment at finish
// END REV 23Y ADDITIONS.
volatile int currThous = 0;
volatile int distToWP = 0;      // this is the distance to the upcoming waypoint in thousandths of a mile
volatile int prevDistToWP = 0;  // this is the previous distance to Waypoint in thousandths of a mile for filtering
volatile int oldTimeSeconds = 0;
int adjTime = 0;  // used for PPS-based time correction
int WPThous = 0;  // the thousandths mile of the next waypoint
volatile boolean TenHzInt = false;
volatile boolean TenHertzInt = false;

volatile boolean PBInt = false;
volatile boolean Started = false;     // Set true when leg has started
volatile boolean nearStart1 = false;  // Within x thousandths of a mile of Start Line for Leg 1
volatile boolean nearStart2 = false;  // Within x thousandths of a mile of Start Line for Leg 2
volatile boolean nearTime = false;    // Within 30 seconds of start (when PB is pushed)
volatile boolean oneSec = false;
volatile boolean oneSecFlag = false;  // Flag to just log once at start
volatile boolean Finished = false;    // Set true when leg has finished
volatile boolean redLED = false;      // flag to track the state of the red LED
volatile boolean yellowLED = false;   // flag to track the state of the yellow LED
volatile boolean PPSInt = false;      // flag to show PPS interrupt has occurred
volatile boolean PFFlag = false;      // flag to show past the finish line
volatile boolean swEnable = false;    // flag to show that stopwatch counting is enabled
volatile boolean clockInt = false;

// Rev 45 Waypoint 3 variables:
int L1WP3Thous = 88019;
int L2WP3Thous = 62011;

volatile int antD = 5;  // Default antenna distance from front of car 5 feet

volatile int dynLAF = -5;     // Dynamic LAF to be calculated at each point needing adjustment
volatile int actTimeRem = 0;  // This will be the remainder of actualTime divided by 100
volatile int timeMS = 0;      // This is the GPS.milliseconds

int diffPrevToNow = 0;  // difference between previous and current distance to waypoint

int Rev = 4510;  // The software revision number.

int latDeg;
int latCurrDeg = 37;
int latDecDeg;
int latCurrDecDeg = 0;
int lngDeg;
int lngCurrDeg = -122;
int lngDecDeg;
int lngCurrDecDeg = 0;

int distToWPadj = 0;
int finishL1Thous = 90000;
int finishL2Thous = 62380;
int finishThous = 0;  // the finish thousandths miles
int WPLatDeg = 0;
int WPLatDecDeg = 0;
int WPLngDeg = 0;
int WPLngDecDeg = 0;

int previousDistToWP = 0;  // this is a record of the old distance to the waypoint before updating the value
volatile float distBwt;
boolean printJustOnce = false;
boolean snapshotOnce = false;  // flag to just snapshot the currThous once
int currThousSnap = 0;         // the thousandths of a mile snapshot when nearWP flag comes true
int distToWPcount = 0;
int cummDistToWP = 0;
int avgDistToWP = 0;    // the average of 10 distance between readings
int predThousAtWP = 0;  // the predicted thousandths at the upcoming waypoint

volatile float latNow;
volatile char latDirection;
volatile float lngNow;
volatile char lngDirection;
// SET UP THE TWO LED NUMERIC DISPLAYS:
LedControl lc1 = LedControl(3, 2, A2, 1);    // Specify control pins for the Ahead-Behind Display
LedControl lc2 = LedControl(A0, A5, A1, 1);  // Specify control pins for the Mileage Display

// DEFINE SOME SUBROUTINES FOR THE LED DISPLAY OPERATIONS:
static int GetDigit(int number, int digit) {
  return (number / (int)pow(10, digit - 1)) % 10;
}
static char setChar(int addr, int digit, char value, boolean dp);  // for the minus sign and the blank


// DEFINE THE ARRAYS:
#define ROWWP_DIM 6   // The Waypoint Array: 6 rows, 3 for Leg 1, 3 for Leg 2
#define COLWP_DIM 10  // Miles, Lat, Lng for 5 waypoints in each of two legs
#define ROWE_DIM 1    // This will hold the errorOut centiseconds
#define COLE_DIM 1
#define ROWTS_DIM 1  // This is for the target speed
#define COLTS_DIM 1
#define ROWL_DIM 8  // Log arrays (7 rows for each of the 2 log arrays)
#define COLL_DIM 5  // Log arrays (5 columns for each of the 2 log arrays)
#define ROWANT_DIM 1
#define COLANT_DIM 1
int arrayWP[ROWWP_DIM][COLWP_DIM];     // The Waypoint Array
int arrayE[ROWE_DIM][COLE_DIM];        // The errorOut Array for the Ahead/Behind error on the first leg
int arrayTS[ROWTS_DIM][COLTS_DIM];     // The Target Speed Array for your targetSpeed for the event
int WPArray[ROWWP_DIM][COLWP_DIM];     // The working waypoint array
float arrayL1[ROWL_DIM][COLL_DIM];     // Log array for Leg 1
float arrayL2[ROWL_DIM][COLL_DIM];     // Log array for Leg 2
int arrayLogM[5];                      // array to hold actual Miles at each waypoint
float arrayLogORRMileage[5];           // array to hold official ORR.txt mileage of each waypoint
int arrayLogT[5];                      // array to hold actual thousandths of a mile at each waypoint
float arrayLogMileage[5];              // array to hold mileage of each waypoint as measured in race or practice
int arrayLogToD[5];                    // array to hold UTC Time of Day at each waypoint detection
int arrayLogAT[5];                     // array to hold actualTime in centi-seconds at each waypoint detection
volatile int arrayLogAB[5];            // array to hold Ahead/Behind Time at each waypoint detection
volatile int arrayLogSW[5];            // array to hold stopwatch count at each waypoint detection and at finish
float arrayLogSpeed[5];                // array to hold speed in mph at each waypoint detection
int arrayANT[ROWANT_DIM][COLANT_DIM];  // array for the antenna distance (default 5 feet)
// SET UP THE FILES ON THE SD CARD:
File file;   // This is for the waypoint array
File err;    // This is for the errorOut value
File ts;     // This is for the target speed value
File L1Log;  // This is for the log to save data from Leg 1 (only read from laptop afterwards)
File L2Log;  // This is for the log to save data from Leg 2 (only read from laptop afterwards)
File FRLog;  // This is for the log of waypoints in Free Run Mode for each Pushbutton push
File ant;    // This is for the GPS antenna distance from the front of the car
/*
   Note: Integers in MKR Zero have a range of -2,147,483,648 to + 2,147,483,647
   Read a file one field at a time.
   NOTE: File names are LIMITED to 8 CHARACTERS!!

   file - File to read.

   str - Character array for the field.

   size - Size of str array.

   delim - String containing field delimiters.

   return - length of field including terminating delimiter.

   Note, the last character of str will not be a delimiter if
   a read error occurs, the field is too long, or the file
   does not end with a delimiter.  Consider this an error
   if not at end-of-file.
*/

// SET UP SOME PARAMETERS FOR THE ARRAYS:
size_t readField(File *file, char *str, size_t size, char *delim) {
  char ch;
  size_t n = 0;
  while ((n + 1) < size && file->read(&ch, 1) == 1) {
    // Delete CR.
    if (ch == '\r') {
      continue;
    }
    str[n++] = ch;
    if (strchr(delim, ch)) {
      break;
    }
  }
  str[n] = '\0';
  return n;
}
size_t readFld(File *err, char *str, size_t size, char *delim) {
  char ch;
  size_t n = 0;
  while ((n + 1) < size && err->read(&ch, 1) == 1) {
    // Delete CR.
    if (ch == '\r') {
      continue;
    }
    str[n++] = ch;
    if (strchr(delim, ch)) {
      break;
    }
  }
  str[n] = '\0';
  return n;
}

//------------------------------------------------------------------------------
#define errorHalt(msg) \
  { \
    Serial.println(F(msg)); \
    while (1) \
      ; \
  }
//------------------------------------------------------------------------------

// SETUP
void setup() {
  //REV 45 SETUP
  L1WP3Thous = (WPArray[0][3]) * 1000 + WPArray[1][3];
  finishL1Thous = (WPArray[0][4]) * 1000 + WPArray[1][4];
  distToWP = finishL1Thous - L1WP3Thous;  // initial distance from WP3 to Finish for Leg 1
  // Later, in the Loop, change this if L2 == true and at WP3



  // SET UP PIN MODES FOR THE INPUT/OUTPUT PINS:
  //pinMode(DD_PIN, INPUT_PULLUP);     // this is for the DD Pulses (2.64 feet) from Pulser or Test Rig
  pinMode(PPS_PIN, INPUT);           // this is for the GPS PPS signal
  pinMode(PB_PIN, INPUT_PULLUP);     // this is for the Pushbutton ("PB") input
  pinMode(SWPOS_PIN, INPUT_PULLUP);  // this is for the Stopwatch switch position to display clock count
  pinMode(SPPOS_PIN, INPUT_PULLUP);  // this is for the Stopwatch switch position to display speed
  pinMode(REDLED_PIN, OUTPUT);       // this is for the red LED ("passed a waypoint")
  pinMode(YELLED_PIN, OUTPUT);       // For the yellow LED to indicate "near a waypoint"

  // INITIALIZE THE STATE OF THE INDICATOR LEDS TO OFF:
  digitalWrite(REDLED_PIN, HIGH);  // Initialize the Red LED off
  digitalWrite(YELLED_PIN, HIGH);  // Initialize the Yellow LED off

  // SET UP THE SERIAL MONITOR:
  Serial.begin(115200);  // Note that I use 115200 baud although 9600 is more common

  delay(3000);     // WAIT FOR 3 SECONDS TO ALLOW USER TIME TO BRING UP THE SERIAL MONITOR
  Serial.flush();  // GET ALL THE CHARACTERS OUT OF THE SERIAL STREAM TO SHOW ON THE MONITOR

  attachInterrupt(digitalPinToInterrupt(PPS_PIN), PPS, RISING);  // attach the PPS interrupt

  // SET UP THE REAL TIME CLOCK:
  // define frequency of interrupt
  MyTimer5.begin(100);  // 100 = 100Hz, 10 = 10Hz, 50 = 50Hz, 20 = 20Hz

  // define the interrupt callback function
  MyTimer5.attachInterrupt(Timer5_IRQ);

  // start the timer
  MyTimer5.start();

  // INITIALIZE THE TWO MAX7219 LED DISPLAY DEVICES:
  lc1.shutdown(0, false);   // Enable Ahead-Behind display (DISABLE IT WITH "true")
  lc1.setIntensity(0, 10);  // Set brightness level (0 is min, 15 is max)
  lc1.clearDisplay(0);      // Clear Ahead-Behind display register

  lc2.shutdown(0, false);   // Enable Mileage display - (DISABLE it with "true")
  lc2.setIntensity(0, 10);  // Set brightness level (0 is min, 15 is max)
  lc2.clearDisplay(0);      // Clear Mileage display register

  // INITIALIZE THE SD CARD:
  if (!SD.begin(SDCARD_SS_PIN))  // This is where you specify the CS Pin for MKR Zero
  // Yes, I know, I did a #define up above, but I wanted to make it clear and specific here
  {
    freeRun = true;  // set to true if no SD card is found
    noSD = true;     // this indicates that there is no SD card in the slot
    Serial.println("No SD card in slot.");
    Serial.print("Free Run is ");  //This shows value of freeRun as 1 if no SD card present
    Serial.println(freeRun);
    // errorHalt("begin failed"); // NOTE: This error halt is commented out because
    // we do NOT want the CPU to halt if no SD card!!!
  } else {  // START READING THE ARRAYS FROM THE SD CARD:
    // Open the race information file
    file = SD.open("RaceInfo.txt");
    // read from the file until there's nothing else in it:
    while (file.available()) {
      Serial.write(file.read());
    }
    Serial.println();
    if (!file) {
      // errorHalt("RaceInfo failed to open.");
      freeRun = true;  // set Free Run mode if the SD card has no Race Info file
      Serial.println("No RaceInfo file, going into Free Run Logging Mode.");
    } else {
      // close the file:
      file.close();
    }
    // Open the race data file.

    file = SD.open("ORR.txt");  // File names limited to 8 characters!
    if (!file) {
      // errorHalt("first open failed");  // You'll see this message if your file name > 8 chars
      freeRun = true;  // set Free Run mode if the SD card has no ORR.txt file
      Serial.println("No ORR.txt file, going into Free Run Logging Mode.");
    } else {  // ORR.txt EXISTS
      // Rewind the file for read.
      file.seek(0);
      Serial.println("Start of Waypoint data array: ");
      // Array for waypoint data.
      int arrayWP[ROWWP_DIM][COLWP_DIM];
      int i = 0;     // First array index.
      int j = 0;     // Second array index
      size_t n;      // Length of returned field with delimiter.
      char str[20];  // Must hold longest field with delimiter and zero byte.
      char *ptr;     // Test for valid field.

      // Read the file and store the data.

      for (i = 0; i < ROWWP_DIM; i++) {
        for (j = 0; j < COLWP_DIM; j++) {
          n = readField(&file, str, sizeof(str), ",\n");
          if (n == 0) {
            errorHalt("Too few lines WP");
          }
          arrayWP[i][j] = strtol(str, &ptr, 10);
          if (ptr == str) {
            errorHalt("bad number");
          }
          if (j < (COLWP_DIM - 1) && str[n - 1] != ',') {
            errorHalt("line with too few fields");
          }
        }
        // Allow missing endl at eof.
        if (str[n - 1] != '\n' && file.available()) {
          errorHalt("missing endl");
        }
      }

      // Print the array.
      for (i = 0; i < ROWWP_DIM; i++) {
        for (j = 0; j < COLWP_DIM; j++) {
          if (j) {
            Serial.print(' ');
          }
          Serial.print(arrayWP[i][j]);
        }
        Serial.println();
      }


      file.close();  // have to close the file before trying to open a new one.

      //USE THE WORKING WAYPOINT ARRAY (WPArray[][]) to store the waypoint values for retrieval
      for (i = 0; i < ROWWP_DIM; i++) {
        for (j = 0; j < COLWP_DIM; j++) {
          WPArray[i][j] = arrayWP[i][j];
        }
      }

      L1WP0LatDec = (WPArray[3][0]);


      L1WP0LngDec = (WPArray[5][0]);


      L1WP3LatDeg = float(WPArray[2][3]);
      L1WP3LatDec = float((WPArray[3][3]) / 1000000.0);
      L1WP3Lat = L1WP3LatDeg + L1WP3LatDec;
      L1WP3LngDeg = float((WPArray[4][3]));
      L1WP3LngDec = float((WPArray[5][3]) / 1000000.0);
      L1WP3Lng = L1WP3LngDeg + L1WP3LngDec;

      L1WP4LatDeg = float(WPArray[2][4]);
      L1WP4LatDec = float((WPArray[3][4]) / 1000000.0);
      L1WP4Lat = L1WP4LatDeg + L1WP4LatDec;
      L1WP4LngDeg = float((WPArray[4][4]));
      L1WP4LngDec = float((WPArray[5][4]) / 1000000.0);
      L1WP4Lng = L1WP4LngDeg + L1WP4LngDec;

      // Determine the quadrasphere of the earth in which the race occurs:
      if (L1WP4Lat > 0) {
        hLat = 1;  // northern hemisphere
      } else {
        hLat = -1;  // southern hemisphere
      }
      if (L1WP4Lng > 0) {
        hLng = 1;  // eastern hemisphere
      } else {
        hLng = -1;  // western hemisphere
      }
      // ADDED THIS TO AVOID INT(INT) PROBLEMS:
      int L1LatDeg = WPArray[2][0];
      int L1LatDecDeg = WPArray[3][0];
      int L1LngDeg = WPArray[4][0];
      int L1LngDecDeg = WPArray[5][0];

      int L2LatDeg = WPArray[2][5];
      int L2LatDecDeg = WPArray[3][5];
      int L2LngDeg = WPArray[4][5];
      int L2LngDecDeg = WPArray[5][5];



      L2WP3LatDeg = WPArray[2][8];
      L2WP3LatDec = (WPArray[3][8]);

      L2WP3LngDeg = (WPArray[4][8]);
      L2WP3LngDec = (WPArray[5][8]);

      L2WP4LatDeg = WPArray[2][9];
      L2WP4LatDec = (WPArray[3][9]);

      L2WP4LngDeg = (WPArray[4][9]);
      L2WP4LngDec = (WPArray[5][9]);

      finishL1Thous = (WPArray[0][4]) * 1000 + (WPArray[1][4]);
      finishL2Thous = ((WPArray[0][9]) * 1000 + (WPArray[1][9]));


      // Rev 45 Waypoint 3 mileages:
      L1WP3Thous = (WPArray[0][3]) * 1000 + (WPArray[1][3]);
      L2WP3Thous = (WPArray[0][8]) * 1000 + (WPArray[1][8]);

    }  // END ORR.txt EXISTS ON SD CARD

    // READ THE err.txt FILE (on the first leg, it will NOT exist)

    // TRY TO READ THE err.txt FILE:
    err = SD.open("ERR.txt");  // This tries to open the "ERR.txt" file
    if (!err) {                //IF THERE IS NO ERR.TXT FILE ON THE SD CARD:
      // errorHalt("open err failed");
      Serial.println("No ERR.txt file on SD card.");
    } else {  // i.e., if there IS a ERR.txt file on the SD card:
      // Rewind the file for read.
      err.seek(0);
      // Array for errorOut
      // int arrayE[ROWE_DIM][COLE_DIM];
      int p = 0;     // First array index.
      int q = 0;     // Second array index
      size_t n;      // Length of returned field with delimiter.
      char str[20];  // Must hold longest field with delimiter and zero byte.
      char *ptr;     // Test for valid field.

      // Read the file and store the data.

      for (p = 0; p < ROWE_DIM; p++) {
        for (q = 0; q < COLE_DIM; q++) {
          n = readFld(&err, str, sizeof(str), ",\n");
          if (n == 0) {
            errorHalt("Too few lines E");
          }
          arrayE[p][q] = strtol(str, &ptr, 10);
          if (ptr == str) {
            errorHalt("bad number");
          }
          if (q < (COLE_DIM - 1) && str[n - 1] != ',') {
            errorHalt("line with too few fields");
          }
        }
        // Allow missing endl at eof.
        if (str[n - 1] != '\n' && err.available()) {
          errorHalt("missing endl");
        }
      }
      errorOut = arrayE[0][0];  // This should set the errorOut to the
      // value from the SD card for the start of Leg 2
      // Print the array.
      for (p = 0; p < ROWE_DIM; p++) {
        for (q = 0; q < COLE_DIM; q++) {
          if (q) {
            Serial.print(' ');
          }
          Serial.print("Error Out = ");
          Serial.println(errorOut);
        }
        Serial.println();
      }
      err.close();
    }


    // The targetSpeed value is stored in a separate file called "ts.txt"

    ts = SD.open("ts.txt");  // This opens the "ts.txt" file
    if (!ts) {
      // errorHalt("open ts failed");
      freeRun = true;  // set the Free Run mode if no target speed file exists
      Serial.println("No ts.txt file found.  Free Run is True.");
    } else {  // TS file exists
      // Rewind the file for read.
      ts.seek(0);

      // Array for target speed
      int arrayTS[ROWTS_DIM][COLTS_DIM];
      int p = 0;     // First array index.
      int q = 0;     // Second array index
      size_t n;      // Length of returned field with delimiter.
      char str[20];  // Must hold longest field with delimiter and zero byte.
      char *ptr;     // Test for valid field.

      // Read the file and store the data.

      for (p = 0; p < ROWTS_DIM; p++) {
        for (q = 0; q < COLTS_DIM; q++) {
          n = readFld(&ts, str, sizeof(str), ",\n");
          if (n == 0) {
            errorHalt("Too few lines TS");
          }
          arrayTS[p][q] = strtol(str, &ptr, 10);
          if (ptr == str) {
            errorHalt("bad number");
          }
          if (q < (COLTS_DIM - 1) && str[n - 1] != ',') {
            errorHalt("line with too few fields");
          }
        }
        // Allow missing endl at eof.
        if (str[n - 1] != '\n' && ts.available()) {
          errorHalt("missing endl");
        }
      }

      // Print the array.
      for (p = 0; p < ROWTS_DIM; p++) {
        for (q = 0; q < COLTS_DIM; q++) {
          if (q) {
            Serial.print(' ');
          }
          Serial.print("Target Speed = ");
          Serial.println(arrayTS[p][q]);
        }
        targetSpeed = arrayTS[0][0];  // This sets the target speed to what's on the SD card
      }
    }


    // READ THE ANT.txt FILE if it exists; otherwise, use the default value for antenna distance

    // TRY TO READ THE ANT.txt FILE:
    ant = SD.open("ANT.txt");  // This tries to open the "ANT.txt" file
    if (!ant) {                //IF THERE IS NO ANT.TXT FILE ON THE SD CARD:
      Serial.println("No ANT.txt file on SD card. Using the default value for GPS antenna distance.");
    } else {  // i.e., if there IS an ANT.txt file on the SD card:
      // Rewind the file for read.
      ant.seek(0);
      int p = 0;     // First array index.
      int q = 0;     // Second array index
      size_t n;      // Length of returned field with delimiter.
      char str[20];  // Must hold longest field with delimiter and zero byte.
      char *ptr;     // Test for valid field.

      // Read the file and store the data.

      for (p = 0; p < ROWANT_DIM; p++) {
        for (q = 0; q < COLANT_DIM; q++) {
          n = readFld(&ant, str, sizeof(str), ",\n");
          if (n == 0) {
            errorHalt("Too few lines ANT");
          }
          arrayANT[p][q] = strtol(str, &ptr, 10);
          if (ptr == str) {
            errorHalt("Bad ANT number.");
          }
          if (q < (COLANT_DIM - 1) && str[n - 1] != ',') {
            errorHalt("Line with too few fields in ANT.");
          }
        }
        // Allow missing endl at eof.
        if (str[n - 1] != '\n' && ant.available()) {
          errorHalt("Missing endl in ANT.");
        }
      }
      antD = arrayANT[0][0];  // This should change the antenna distance ("antD") from its
      // default value to the value read from the ANT.txt file on the SD card
      // Print the array.
      for (p = 0; p < ROWANT_DIM; p++) {
        for (q = 0; q < COLANT_DIM; q++) {
          if (q) {
            Serial.print(' ');
          }
          Serial.print("GPS antenna distance = ");
          Serial.println(antD);
        }
        Serial.println();
      }
      ant.close();
    }

    Serial.print("Software Rev is: ");
    Serial.println(Rev);

  }  // END READING OF THE ARRAYS

  // DETERMINE THE BEARING FOR LEG 1 (direction of travel as you cross the Finish)
  L1latDelta = L1WP4Lat * hLat - L1WP3Lat * hLat;
  L1lngDelta = L1WP4Lng * hLng - L1WP3Lng * hLng;

  if (abs(L1latDelta) > abs(L1lngDelta))  // latitude prevails on Leg 1
  {
    if (L1latDelta > 0)  // i.e., if latitude gets larger as you cross the Finish line
    {
      L1brg = 0;  // north
    } else {
      L1brg = 2;  // south
    }

  } else  // longitude prevails on Leg 1
  {
    if (L1lngDelta > 0) {
      L1brg = 3;  // west
    } else {
      L1brg = 1;  // east
    }
  }

  // DETERMINE THE BEARING FOR LEG 2 (direction of travel as you cross the Finish)
  L2latDelta = L2WP4Lat * hLat - L2WP3Lat * hLat;
  L2lngDelta = L2WP4Lng * hLng - L2WP3Lng * hLng;

  if (abs(L2latDelta) > abs(L2lngDelta))  // latitude prevails on Leg 2
  {
    if (L2latDelta > 0)  // i.e., if latitude gets larger as you cross the Finish line
    {
      L2brg = 0;  // north
    } else {
      L2brg = 2;  // south
    }

  } else  // longitude prevails on Leg 2
  {
    if (L2lngDelta > 0) {
      L2brg = 3;  // west
    } else {
      L2brg = 1;  // east
    }
  }



  // SET UP THE GPS READ FREQUENCY AND DATA CONTENT:

  GPS.begin(9600);

  // turn on only the "minimum recommended" data:
  GPS.sendCommand(PMTK_SET_NMEA_OUTPUT_RMCONLY);

  // Set the update rate:
  GPS.sendCommand(PMTK_SET_NMEA_UPDATE_10HZ);  // 1 Hz or 2 Hz or 5 Hz or 10 Hz update rate

  //INITIALIZE THE RED AND YELLOW LEDs:
  digitalWrite(REDLED_PIN, HIGH);  // Initialize the Red LED off
  redLED = false;
  digitalWrite(YELLED_PIN, HIGH);  // Initialize the Yellow LED off
  yellowLED = false;
}


//------------------------------------------------------------------------------
// LOOP

void loop() {

  if (Finished == false) {  // FINISHED == FALSE


    // GET CURRENT LOCATION FROM GPS
    char c = GPS.read();  // Read the NMEA characters

    if (GPS.newNMEAreceived()) {  // NEW NMEA RECEIVED

      if (!GPS.parse(GPS.lastNMEA()))  // this also sets the newNMEAreceived() flag to false
        return;                        // we can fail to parse a sentence in which case we should just wait for another

      // approximately every 0.1 second or so, capture the current stats
      if (TenHzInt == true)

      {  // EVERY TENTH SECOND

        TenHzInt = false;
        timeMS = (GPS.milliseconds);  // used for calculating dynLAF
        timeSecs = (GPS.seconds);
        timeMin = (GPS.minute);
        timeHr = (GPS.hour);
        currDay = (GPS.day);
        currMonth = (GPS.month);
        currYear = (GPS.year);

        velocityMPH = 1.15077945 * (GPS.speed);  // this gives mph from knots, used for distance
        actualTimeTS = actualTime;               // for time stamping actual time


        // LIMIT MILEAGE CREEP WHEN STANDING STILL:
        if (velocityMPH < 2) {
          velocityMPH = 0;
        }
        // CAPTURE THE NOW VALUES OF GPS COORDINATES EVERY 1/10TH SECOND:
        //SNAPSHOT THE NOW VALUES OF GPS COORDINATES in DDMM.mm format:
        latNow = GPS.latitude;
        latDirection = GPS.lat;
        lngNow = GPS.longitude;
        lngDirection = GPS.lon;


        convertDDMMToInt(latNow, latDirection, latDeg, latDecDeg);
        latCurrDeg = latDeg;
        latCurrDecDeg = latDecDeg;


        convertDDMMToInt(lngNow, lngDirection, lngDeg, lngDecDeg);
        lngCurrDeg = lngDeg;
        lngCurrDecDeg = lngDecDeg;
        smMPH = ((0.2 * velocityMPH) + (0.8 * smMPH));

        speedMPH = smMPH;
        spdMPH = smMPH;                            // integer portion of mph
        spdThouMPH = int(1000 * speedMPH) % 1000;  // thousandths portion of mph in integer form

        smMPH = ((0.2 * velocityMPH) + (0.8 * smMPH));

        // speed updated every 0.1 second and smoothed over a 1-second period
      }
      // END THE RETRIEVAL FROM GPS every 1/10 sec.

      //DIAGNOSTIC: PRINT OUT THE INITIAL COORDINATES

      if (initFlag == true) {

        int L1LatDeg = WPArray[2][0];
        int L1LatDecDeg = WPArray[3][0];
        int L1LngDeg = WPArray[4][0];
        int L1LngDecDeg = WPArray[5][0];

        int L2LatDeg = WPArray[2][5];
        int L2LatDecDeg = WPArray[3][5];
        int L2LngDeg = WPArray[4][5];
        int L2LngDecDeg = WPArray[5][5];

        Serial.print("GPS day = ");
        Serial.println(currDay);
        Serial.print("GPS month = ");
        Serial.println(currMonth);
        Serial.print("GPS year = ");
        Serial.println(currYear);
        Serial.print("Leg 1 Official Start Latitude = ");
        Serial.print(L1LatDeg);
        Serial.print('.');
        Serial.println(L1LatDecDeg);
        Serial.print("Leg 1 Start measured Latitude = ");
        Serial.print(latDeg);
        Serial.print('.');
        Serial.println(latDecDeg);
        Serial.flush();
        initFlag = false;

      }  // END INITFLAG = TRUE (to just snapshot the initial readings once)

      // BEGIN LOGIC FOR NORMAL RACE OPERATION (i.e., freeRun == false)
      if (freeRun == false) {
        // BEGIN START LINE LOGIC (i.e., Started == false)

        // FIND OUT IF NEAR ONE OF THE START LINES IF NOT YET STARTED
        if (Started == false) {

          // Added this snippet to display UTC seconds in A/B Display before a start

          if ((PPSInt == true) && (oneSec == false)) {

            ToDSecsOnly = 100 * (timeSecs + 1);
            ABTime = ToDSecsOnly;
            PPSInt = false;
          }
          // THE FOLLOWING CODE COMPARES CURRENT LAT/LNG WITH START LINE LAT/LNGS
          // FIND OUT IF NEAR THE START LINE FOR LEG 1:
          int L1LatDeg = WPArray[2][0];
          int L1LatDecDeg = WPArray[3][0];
          int L1LngDeg = WPArray[4][0];
          int L1LngDecDeg = WPArray[5][0];

          getDistBwt(latCurrDeg, latCurrDecDeg, lngCurrDeg, lngCurrDecDeg, L1LatDeg, L1LatDecDeg, L1LngDeg, L1LngDecDeg);
          distToWP = distBwt;  // this sets the distance to Leg 1 Start line as "distToWP"


          if (distToWP <= 5 * wayptTol) {
            nearStart1 = true;
            wayptNearOnce = true;
            L1 = true;
            errorOut = 0;  // DON'T USE AN OLD ERROROUT VALUE IN TIME CORRECTION LEG 1
            // TURN ON Yellow LED
            if (yellowLED == false) {
              digitalWrite(YELLED_PIN, LOW);  // Turn on the Yellow LED
              yellowLED = true;
            }
          }
          // FIND OUT IF NEAR THE START LINE FOR LEG 2:
          int L2LatDeg = WPArray[2][5];
          int L2LatDecDeg = WPArray[3][5];
          int L2LngDeg = WPArray[4][5];
          int L2LngDecDeg = WPArray[5][5];

          getDistBwt(latCurrDeg, latCurrDecDeg, lngCurrDeg, lngCurrDecDeg, L2LatDeg, L2LatDecDeg, L2LngDeg, L2LngDecDeg);
          distToWP = distBwt;
          if (distToWP <= 5 * wayptTol) {
            nearStart2 = true;
            wayptNearOnce = true;
            L2 = true;
            if (yellowLED == false) {
              digitalWrite(YELLED_PIN, LOW);  // Turn on the Yellow LED
              yellowLED = true;
            }
            errorOut = arrayE[0][0];  // This should already be done in setup, but this repeats it
          }

          // Check if more than 1 mile away from start line


          getDistBwt(latCurrDeg, latCurrDecDeg, lngCurrDeg, lngCurrDecDeg, L1LatDeg, L1LatDecDeg, L1LngDeg, L1LngDecDeg);
          if ((nearStart1 == true) && (distBwt > 1000)) {

            nearStart1 = false;
            digitalWrite(YELLED_PIN, HIGH);  // Turn off the Yellow LED
            yellowLED = false;
          }

          // Now check if more than 1 mile away from Leg 2 Start when nearStart2 is true:

          getDistBwt(latCurrDeg, latCurrDecDeg, lngCurrDeg, lngCurrDecDeg, L2LatDeg, L2LatDecDeg, L2LngDeg, L2LngDecDeg);
          if ((nearStart2 == true) && (distBwt > 1000)) {
            nearStart2 = false;
            digitalWrite(YELLED_PIN, HIGH);  // Turn off the Yellow LED
            yellowLED = false;
          }

          // WHEN NEAR THE START, IF PBINT, THEN LOOK FOR TOP OR BOTTOM OF MINUTE
          if ((nearStart1 == true) || (nearStart2 == true)) {
            attachInterrupt(digitalPinToInterrupt(PB_PIN), PB, FALLING);  // attach the PB interrupt
            if (PBInt == true) {
              nearTime = true;  // set the nearTime flag
              detachInterrupt(PB_PIN);

              if (nearStart1 == true) {
                getDistBwt(latCurrDeg, latCurrDecDeg, lngCurrDeg, lngCurrDecDeg, L1LatDeg, L1LatDecDeg, L1LngDeg, L1LngDecDeg);
                distToWP = distBwt;
              }
              if (nearStart2 == true) {
                getDistBwt(latCurrDeg, latCurrDecDeg, lngCurrDeg, lngCurrDecDeg, L2LatDeg, L2LatDecDeg, L2LngDeg, L2LngDecDeg);
                distToWP = distBwt;
              }

              arrayLogDist[0] = distToWP;
            }

            if (nearTime == true) {
              if (timeSecs == 59 || timeSecs == 29) {

                if (digitalRead(PPS_PIN) == LOW)  // if the PPS signal is low
                {                                 // START PPS LOW
                  if (oneSec == false) {
                    if (oneSecFlag == false) {

                      // THIS IS WHERE WE SET THE STARTING VALUES IN THE LOG:
                      if (nearStart1 == true) {
                        for (int i = 0; i < COLL_DIM; i++) {
                          arrayLogORRMileage[i] = ((WPArray[0][i]) * 1000 + WPArray[1][i]);  // Thousandths
                        }
                      }
                      if (nearStart2 == true) {
                        for (int i = 0; i < COLL_DIM; i++) {
                          arrayLogORRMileage[i] = ((WPArray[0][i + 5]) * 1000 + WPArray[1][i + 5]);
                        }
                      }
                      arrayLogMileage[0] = 0.0;

                      // only log -errorOut for Leg 2, not Leg 1
                      if (L1 == true) {
                        arrayLogAT[0] = 0;
                      }
                      if (L2 == true) {
                        arrayLogAT[0] = -errorOut;
                      }
                      arrayLogSpeed[0] = velocityMPH;  // speed in mph
                      oneSecFlag = true;               // then when PPS interrupt occurs, start
                      PBInt = false;
                    }
                    oneSec = true;
                  }
                }   // END PPS LOW
              }     // END time == 29 or 59
              else  // Start to blink the Red LED
              {

                if (digitalRead(PPS_PIN) == LOW)  // if the PPS signal is low
                {
                  digitalWrite(REDLED_PIN, LOW);  // start to blink the red LED by turning it on
                  redLED = true;
                } else  // if the PPS signal is high
                {
                  digitalWrite(REDLED_PIN, HIGH);  // blink the red LED off
                  redLED = false;
                }
              }  // END THE BLINKING RED LED LOGIC
            }    // END THE nearTime == true LOGIC
          }      // END (nearStart1 == true OR nearStart2 == true)
          // REV 22X ADDITION:
          if ((PPSInt == true) && (Started == false)) {
            if ((waypt == 0) && (nearTime == true) && (oneSec == true)) {
              Started = true;
              // CAPTURE THE TIME OF DAY STARTING SECONDS UTC
              ToDStartSeconds = ((3600 * timeHr) + (60 * timeMin) + timeSecs + 1);
              arrayLogToD[0] = ToDStartSeconds;
              Miles = 0;
              thousandths = 0;
              incrDistSum = 0;
              targetTime = 0;
              actualTime = 0;
              swEnable = true;
              swCount = 0;  // zero out the stopwatch count
              if (L2 == true) {
                actualTime = -errorOut;
                ABTime = errorOut;
                arrayLogAB[0] = ABTime;
              }
              nearTime = false;
              digitalWrite(YELLED_PIN, HIGH);  // turn off the yellow LED
              yellowLED = false;
              nearStart1 = false;
              nearStart2 = false;
              oneSec = false;
              oneSecFlag = false;
              PPSCount = 0;
              currThous = 0;
              waypt = waypt + 1;

              if (L1 == true) {
                colno = 0;
              }
              if (L2 == true) {
                colno = 5;
              }
              WPThous = (WPArray[0][colno + waypt]) * 1000 + (WPArray[1][colno + waypt]);


            }  // END waypt == 0 and nearTime == true and oneSec == true
            PPSInt = false;
          }  // END PPSInt == true and Started == false

        }  // END THE STARTED == FALSE LOGIC

        if (Started == true) {  // STARTED == TRUE IN NORMAL RACE MODE (I.E., FREERUN == FALSE)

          if (nearWP == false) {  // NEARWP == FALSE

            // CALCULATE DISTANCE TO UPCOMING WAYPOINT in thousandths of a mile

            if (L1 == true) {
              colno = 0;  // set the array column number to 0 for Leg 1
            }
            if (L2 == true) {
              colno = 5;  // set the array column number to 5 for Leg 2
            }


            // GET THE DISTANCE TO THE UPCOMING WAYPOINT:
            WPLatDeg = WPArray[2][colno + waypt];
            WPLatDecDeg = WPArray[3][colno + waypt];
            WPLngDeg = WPArray[4][colno + waypt];
            WPLngDecDeg = WPArray[5][colno + waypt];
            convertDDMMToInt(latNow, latDirection, latDeg, latDecDeg);
            latCurrDeg = latDeg;
            latCurrDecDeg = latDecDeg;
            convertDDMMToInt(lngNow, lngDirection, lngDeg, lngDecDeg);
            lngCurrDeg = lngDeg;
            lngCurrDecDeg = lngDecDeg;

            getDistBwt(latCurrDeg, latCurrDecDeg, lngCurrDeg, lngCurrDecDeg, WPLatDeg, WPLatDecDeg, WPLngDeg, WPLngDecDeg);

            distToWP = distBwt;
            DNLAF();
            if (waypt < 4) {
              distToWPadj = distToWP + 13 + dynLAF * (velocityMPH / 360);

              // CHECK TO SEE IF NEAR TO THE WAYPOINT:
              currThous = (Miles * 1000 + (thousandths));  // just get the currThous

              if (distToWPadj <= 200)

              {
                if (snapshotOnce == false) {
                  // SNAPSHOT THE CURRENT MILEAGE READING IN THOUSANDTHS OF A MILE:

                  currThousSnap = currThous;

                  snapshotOnce = true;
                  // PREDICT THE MILEAGE READING AT THE UPCOMING WAYPOINT:
                  predThousAtWP = distToWPadj + currThousSnap;

                  predThousAtWP = distToWP + currThousSnap;
                  nearWP = true;
                }
              }  // END distToWPadj <= 200
            }    // END waypt < 4


            // TIMEOUT THE REDLED

            if (countTenPPS >= 6) {
              digitalWrite(REDLED_PIN, HIGH);  // turn off the red LED
              redLED = false;
            }

          }  // END NEARWP == FALSE
          // THIS IS THE LOGIC FOR NEARWP == TRUE
          if (nearWP == true) {  // NEARWP == TRUE
            if (waypt < 4) {
              if (yellowLED == false) {
                digitalWrite(YELLED_PIN, LOW);  // turn on the yellow LED
                yellowLED = true;
              }

              currThous = Miles * 1000 + thousandths;

              // IF THE DISTANCE REACHES THE PREDICTED VALUE OF THE MILEAGE AT THE WAYPOINT;
              if (predThousAtWP - currThous <= 1) {
                // DECLARE THAT WAYPOINT HAS BEEN REACHED
                nearWP = false;
                if (justWriteOnce == false) {
                  // LOG THE ACTUAL MILEAGE BEFORE ADJUSTMENT:
                  arrayLogM[waypt] = Miles;
                  arrayLogT[waypt] = thousandths;
                  justWriteOnce = true;
                  snapshotOnce = false;
                }

                digitalWrite(YELLED_PIN, HIGH);
                yellowLED = false;
                if (redLED == false) {
                  digitalWrite(REDLED_PIN, LOW);  // turn on the red led
                  redLED = true;
                  countTenPPS = 0;
                }

                // ADJUST THE MILEAGE TO THE OFFICIAL WAYPOINT MILEAGE

                Miles = (WPArray[0][colno + waypt]);
                thousandths = ((WPArray[1][colno + waypt]) - 1);
                currThous = (Miles * 1000 + thousandths);

                // ADD FOR REV 45:
                L2WP3Thous = (WPArray[0][8]) * 1000 + WPArray[1][8];
                finishL2Thous = (WPArray[0][9]) * 1000 + WPArray[1][9];

                nearWP = false;

                arrayLogMileage[waypt] = (arrayLogM[waypt]) * 1000 + (arrayLogT[waypt]);
                arrayLogAB[waypt] = ABTime;         // This logs the Ahead/Behind Time at waypoint
                arrayLogSW[waypt] = swCount;        // This logs the stopwatch count at waypoint
                arrayLogDist[waypt] = distToWPadj;  // log the distance to the waypoint when detected

                arrayLogAT[waypt] = actualTime;

                arrayLogSpeed[waypt] = velocityMPH;  // Speed in mph

                writeOnce = false;

                // INCREMENT TO POINT TO THE NEXT WAYPOINT:
                waypt = waypt + 1;

                // DIAGNOSTIC:
                if (writeOnce == false) {
                  if (L1 == true) {
                    colno = 0;  // set the array column number to 0 for Leg 1
                  }
                  if (L2 == true) {
                    colno = 5;  // set the array column number to 5 for Leg 2
                  }
                  WPThous = (WPArray[0][colno + waypt]) * 1000 + (WPArray[1][colno + waypt]);

                  writeOnce = true;
                }
              }  // END REACHED THE WAYPOINT
            }    // END waypt < 4
          }      // END nearWP == true

          if (waypt >= 4) {
            // WAYPT >= 4

            // CALCULATE DISTANCE TO THE FINISH
            currThous = (Miles * 1000 + thousandths);
            if (L1 == true) {
              colno = 0;  // set the array column number to 0 for Leg 1
              finishThous = finishL1Thous;
            }
            if (L2 == true) {
              colno = 5;  // set the array column number to 5 for Leg 2
              finishThous = finishL2Thous;
            }

            currThous = (Miles * 1000 + thousandths);  // NOTE: This is in thousandths miles
            distToWP = finishThous - currThous;

            if (distToWP <= 200)

            {
              nearWP = true;
              // TURN ON THE YELLOW LED RIGHT AWAY
              if (yellowLED == false) {
                digitalWrite(YELLED_PIN, LOW);  // turn on yellow LED
                yellowLED = true;
              }
            }

            if (distToWP <= 0) {
              nearWP = false;
              if (L1 == true) {
                perfectTime = finishL1Thous * 360 / targetSpeed;
                FFR1();
              }
              if (L2 == true) {
                perfectTime = finishL2Thous * 360 / targetSpeed;
                FFR2();
              }
            }

            // AUTO-DETECTION OF PAST FINISH LINE

            // See if this is at or past the finish line
            if (L1 == true) {  // L1 TRUE
              perfectTime = finishL1Thous * 3600 / targetSpeed;

              if ((L1brg == 0) || L1brg == 2)  // if bearing is north or south
              {
                if (((L1WP4Lat * hLat - latC * hLat) < -0.000010) && (L1brg == 0)) {
                  PFFlag = true;
                  latCP = latC;                              // Snapshot the latitude
                  distPast = 68351 * abs(L1WP4Lat - latCP);  // in thousandths of a mile
                  arrayLogToD[0] = int(distPast);
                  FFR1();
                }
                if (((L1WP4Lat * hLat - latC * hLat) > 0.000010) && (L1brg == 2)) {
                  PFFlag = true;
                  latCP = latC;  // Snapshot the latitude
                  distPast = 68351.0 * abs(L1WP4Lat - latCP);
                  arrayLogToD[0] = int(distPast * 100.0);
                  FFR1();
                }
              }
              if ((L1brg == 1) || (L1brg == 3))  // if bearing is east or west
              {
                if (((L1WP4Lng * hLng - lngC * hLng) < -0.000010) && (L1brg == 3)) {
                  PFFlag = true;
                  lngCP = lngC;  // Snapshot the longitude
                  distPast = 55924.0 * abs(L1WP4Lng - lngCP);
                  arrayLogToD[0] = int(distPast * 100.0);
                  FFR1();
                }
                if (((L1WP4Lng * hLng - lngC * hLng) > 0.000010) && (L1brg == 1)) {
                  PFFlag = true;
                  lngCP = lngC;  // Snapshot the longitude
                  distPast = 55924.0 * abs(L1WP4Lng - lngCP);
                  arrayLogToD[0] = int(distPast * 100.0);
                  FFR1();
                }
              }
            }  // END L1 == TRUE

            if (L2 == true) {  // L2 == TRUE
              perfectTime = finishL2Thous * 360 / targetSpeed;
              if ((L2brg == 0) || (L2brg == 2))  // bearing is north or south
              {
                if (((L2WP4Lat * hLat - latC * hLat) < -0.000010) && (L2brg == 0)) {
                  PFFlag = true;
                  latCP = latC;  // Snapshot the latitude
                  distPast = 68351.0 * abs(L2WP4Lat - latCP);
                  arrayLogToD[0] = int(distPast * 100.0);
                  FFR2();
                }
                if (((L2WP4Lat * hLat - latC * hLat) > 0.000010) && (L2brg == 2)) {
                  PFFlag = true;
                  latCP = latC;  // Snapshot the latitude
                  distPast = 68351.0 * abs(L2WP4Lat - latCP);
                  arrayLogToD[0] = int(distPast * 100.0);
                  FFR2();
                }
              }
              if ((L2brg == 1) || (L2brg == 3))  // bearing is west or east
              {
                if (((L2WP4Lng * hLng - lngC * hLng) < -0.000010) && (L2brg == 3)) {
                  PFFlag = true;
                  lngCP = lngC;  // Snapshot the longitude
                  distPast = 55924.0 * abs(L2WP4Lng - lngCP);
                  arrayLogToD[0] = int(distPast * 100.0);
                  FFR2();
                }
                if (((L2WP4Lng * hLng - lngC * hLng) > 0.000010) && (L2brg == 1)) {
                  PFFlag = true;
                  lngCP = lngC;  // Snapshot the longitude
                  distPast = 55924.0 * abs(L2WP4Lng - lngCP);
                  arrayLogToD[0] = int(distPast * 100.0);
                  FFR2();
                }
              }
            }  // END L2 == TRUE

          }  // END WAYPT >= 4

        }  // END STARTED == TRUE IN NORMAL RACE MODE

      }  // END freeRun == false LOGIC

      // START FREE RUN LOGIC

      if (freeRun == true) {  // START FREERUN TRUE

        if (redLED == false)  // Wait for PB bounce to be over before re-attaching the interrupt
        {
          attachInterrupt(digitalPinToInterrupt(PB_PIN), PB, FALLING);  // ATTACH THE PB INTERRUPT HERE
        }
        if (redLED == true) {
          if (countTwoPPS >= 2) {
            digitalWrite(REDLED_PIN, HIGH);  // turn off the red LED after 2 seconds
            redLED = false;                  // and turn off the flag
            countTwoPPS = 3;                 // set the counter higher to prevent the red LED from coming on
            PPSInt = false;                  // turn off the PPS interrupt flag
          }
        }
        if (PBInt == true) {  // START THE PBINT == TRUE FOR FREE RUN LOGIC

          // Turn on the Red LED for a few seconds here...
          if (redLED == false) {
            digitalWrite(REDLED_PIN, LOW);  // turn on the red LED
            redLED = true;                  // turn on the flag for the red LED
            countTwoPPS = 0;                // set the counter to zero
            PPSInt = false;                 // turn off the PPS interrupt flag
          }

          // START THE STARTED == FALSE LOGIC FOR FREE RUN
          if (Started == false) {  // STARTED IS FALSE
            // ZERO OUT THE MILEAGE AND TIME
            (thousandths = 0);
            (Miles = 0);

            (ABTime = 0);
            (actualTime = 0);
            if (noSD == false) {
              FRLogger();  // call the waypoint logging subroutine to log this initial waypoint in Free Run Mode
              // but only if there is a microSD card in the slot
            }
            Started = true;           // Set the Started flag to indicate this Free Run Mode has started
            detachInterrupt(PB_PIN);  // stop the PB interrupt until redLED timer goes off (2 seconds)
            // TURN OFF THE PBINT FLAG
            PBInt = false;
            // AND DETACH THE PB INTERRUPT if there is no SD card in the slot
            if (noSD == true) {
              detachInterrupt(PB_PIN);  // stop the PB interrupt
              // PRINT OUT LOCATION ONCE:
              if (locFlagFR == false) {
                Serial.print("Latitude: ");
                Serial.println(latC, 6);
                Serial.print("Longitude: ");
                Serial.println(lngC, 6);
                locFlagFR = true;
              }
            }  // END noSD == true
          }    // END STARTED IS FALSE FOR FREE RUN MODE
        }      // END PBInt == true for initial Free Run start
        // ON SUBSEQUENT PUSHES OF THE PB, LOG THE WAYPOINTS
        if (Started == true) {  // IF STARTED IS TRUE IN FREE RUN MODE (i.e., after the initial PB push)
          if (noSD == false) {  // AND IF THERE IS AN SD CARD IN THE SLOT

            if (PBInt == true) {
              // UPON THE NEXT PB Interrupt
              if ((float(Miles) + (float(thousandths / 1000.0)) > (float(oldMiles) + (float(oldThousandths / 1000.0)) + 0.2))) {
                FRLogger();               // Call the FRLogger subroutine to log the waypoint values
                detachInterrupt(PB_PIN);  // detach the PB interrupt to prevent double logging
              }
              PBInt = false;  // turn off the interrupt flag

            }  // END PBInt == TRUE

          }  // END SD CARD IN SLOT

        }  // END FREE RUN STARTED

      }  // END FREE RUN LOGIC
    }    // END newNMEAreceived
  }      // END Finished == false

  // RE-INITIALIZE THE LED DISPLAYS EVERY 10 SECONDS TO RESOLVE ISSUE WITH REMOTE DISPLAY
  if (actualTime % 1000 == 0) {
    LedControl lc1 = LedControl(3, 2, A2, 1);
    LedControl lc2 = LedControl(A0, A5, A1, 1);
    lc1.shutdown(0, false);
    lc1.setIntensity(0, 10);
    lc1.clearDisplay(0);
    lc2.shutdown(0, false);
    lc2.setIntensity(0, 10);
    lc2.clearDisplay(0);
  }


  // DISPLAY THE MILEAGE OR THE SPEED

  if (digitalRead(SPPOS_PIN) == LOW) {
    spSwitch = true;
  }

  else {
    spSwitch = false;
  }
  if (spSwitch == true) {
    milesDisplay = spdMPH;
    thousandthsDisplay = spdThouMPH;
  }
  if (spSwitch == false) {
    (thousandthsDisplay = thousandths);
    (milesDisplay = Miles);
  }
  for (int m = 1; m <= 3; m++) {
    if (m == 3) {
      (ones = thousandthsDisplay % 10);
      (thousandthsDisplay = thousandthsDisplay - ones);
      (tens = (thousandthsDisplay / 10) % 10);
      (thousandthsDisplay = thousandthsDisplay - (10 * tens));
    }

    lc2.setDigit(0, m, GetDigit(thousandthsDisplay, m), Milesdp);  // thousandths of a mile are in 1, 2, and 3
  }

  for (int j = 1; j <= 3; j++) {
    if (j == 1) {
      (Milesdp = true);  // turn on the decimal point on digit # 4
    } else {
      (Milesdp = false);  // turn off the decimal point for other mileage digits
    }
    if (j == 3) {
      (Mones = milesDisplay % 10);
      (milesDisplay = milesDisplay - Mones);
      (Mtens = (milesDisplay / 10) % 10);
      (milesDisplay = milesDisplay - (10 * Mtens));
    }

    lc2.setDigit(0, (j + 3), GetDigit(milesDisplay, j), Milesdp);  // miles get displayed in 4, 5, and 6
  }

  // DISTANCE CALCULATIONS BASED ON CLOCK AND SPEED:
  if (clockInt == true) {     // START THE CLOCK LOGIC DISTANCE CALCULATIONS
    if (Finished == false) {  // FINISHED FALSE
      // ESTABLISH THE OLD DISTANCE TO WAYPOINT BEFORE INCREMENTING THE DISTANCE
      if (L1 == true) {
        colno = 0;
      }
      if (L2 == true) {
        colno = 5;
      }

      if (waypt >= 4) {
        finishThous = (WPArray[0][colno + waypt]) * 1000 + WPArray[1][colno + waypt];

        distToWP = finishThous - currThous;
        prevDistToWP = distToWP;
      }
      // CALCULATE DISTANCE TRAVELED IN LAST 0.01 seconds USING GPS VELOCITY
      if ((velocityMPH) >= 2) {

        incrDist = 1464.4 * velocityMPH;  // to compensate for fast timer

        // Note: incrDist is in 100,000ths feet

      } else {
        incrDist = 0;  // Keep the distance from incrementing at low or no speed
      }
      incrDistSum = incrDistSum + incrDist;
      while (incrDistSum >= 528000) {
        thousandths = thousandths + 1;
        incrDistSum = incrDistSum - 528000;
        if (thousandths >= 1000) {
          thousandths = thousandths - 1000;  // correct the thousandths first 230604 change
          Miles = Miles + 1;
        }

        distToWP = finishThous - currThous;
        diffPrevToNow = previousDistToWP - distToWP;
        if ((distToWP <= 100) && (waypt >= 4)) {
          currThous = finishThous - distToWP;
        }

      }  // END while incrDistSum MORE THAN 5.28 FEET

      if ((waypt >= 4) && (distToWP <= 0)) {
        if (ABSnapshot == false) {
          ABSnap = ABTime;
          ABSnapshot = true;
        }
        if (L1 == true) {
          FFR1();
        }
        if (L2 == true) {
          FFR2();
        }
      }
    }

    // THIS SECTION CALCULATES THE ABTIME IN STANDARD OR FREE RUN MODE
    milesF = Miles;
    thousandthsF = thousandths;

    targetTime = int(((milesF * 1000 + thousandthsF) / targetSpeed) * 360.0);
    if (ABSnapshot == true) {
      ABTime = ABSnap;
    }

    if ((ABSnapshot == false) && (Started == true)) {
      ABTime = (targetTime - actualTime);
    }

    clockInt = false;  // turn off the clock interrupt flag
  }                    // END THE CLOCK LOGIC FOR STANDARD OR FREE RUN

  // DISPLAY AHEAD-BEHIND TIME
  if (digitalRead(SWPOS_PIN) == LOW) {
    swSwitch = true;  // set the stopwatch function true - i.e., display stopwatch count
  } else {
    swSwitch = false;  // set the stopwatch function false - i.e., display ABTime
  }
  if (swSwitch == false) {
    // Display the Ahead-Behind Time
    if (ABTime < 0) {
      lc1.setChar(0, 7, '-', false);  // turn the minus sign on in position 8
    } else {
      lc1.setChar(0, 7, ' ', false);  // leave the position 8 LED blank
    }
    (ABSABTime = abs(ABTime));  // take the absolute value of the Ahead Behind time

    (ABSecs = (ABSABTime / 100));
    (ABCents = (ABSABTime - (ABSecs * 100)));

    for (int i = 1; i <= 3; i++) {
      if (i == 1) {
        (ABdp = true);
      } else {
        (ABdp = false);
      }
      lc1.setDigit(0, i + 3, GetDigit(ABSecs, i), ABdp);  // write the seconds digits into the LED display
    }

    for (int j = 1; j <= 2; j++) {
      lc1.setDigit(0, j + 1, GetDigit(ABCents, j), false);  // write the hundredths sec digits into the LED display
    }
  }
  if (swSwitch == true) {
    //Display the stopwatch count
    if (swCount < 0) {
      lc1.setChar(0, 7, '-', false);  // turn the minus sign on in position 8
    } else {
      lc1.setChar(0, 7, ' ', false);  // leave the position 8 LED blank
    }
    (ABSABTime = abs(swCount));  // take the absolute value of the stopwatch count time

    (ABSecs = (swCount / 100));
    (ABCents = (ABSABTime - (ABSecs * 100)));

    for (int i = 1; i <= 3; i++) {
      if (i == 1) {
        (ABdp = true);
      } else {
        (ABdp = false);
      }
      lc1.setDigit(0, i + 3, GetDigit(ABSecs, i), ABdp);  // write the seconds digits into the LED display
    }

    for (int j = 1; j <= 2; j++) {
      lc1.setDigit(0, j + 1, GetDigit(ABCents, j), false);  // write the hundredths sec digits into the LED display
    }
  }
  // END THE DISPLAY CODE FOR THE STOPWATCH COUNT DISPLAY


}  // END LOOP

// SUBROUTINES

// SUBROUTINE TO CONVERT DDMM.mmmm TO INTEGER DEGREES AND INTEGER MILLIONTHS DEGREES
void convertDDMMToInt(float DDMM, char hemis, volatile int &Deg, volatile int &DecDeg) {
  // Extract the Degrees
  Deg = (int)(DDMM / 100.0);

  // Calculate the millionths of a degree as a 6-digit integer
  float fracPart = (DDMM - (100 * (Deg))) / 60.0;
  DecDeg = (int)(fracPart * 1000000);
  // ADJUST THE SIGN BASED ON THE HEMISPHERE:
  if ((hemis == 'S') || (hemis == 'W')) {
    Deg = -Deg;
    DecDeg = -DecDeg;
  }
}


// SUBROUTINE TO CONVERT GPS COORDINATE INTEGERS TO DEGREES
float convertToFloat(int degrees, int fraction) {
  if (degrees < 0) {
    fraction = -fraction;
  }
  return degrees + (fraction / 1000000.0);
}

// SUBROUTINE TO CALCULATE DISTANCE BETWEEN TWO GPS COORDINATES
int getDistBwt(int lat1_deg, int lat1_frac, int lng1_deg, int lng1_frac, int lat2_deg, int lat2_frac, int lng2_deg, int lng2_frac) {
  float lat1 = convertToFloat(lat1_deg, lat1_frac);
  float lng1 = convertToFloat(lng1_deg, lng1_frac);
  float lat2 = convertToFloat(lat2_deg, lat2_frac);
  float lng2 = convertToFloat(lng2_deg, lng2_frac);
  distBwt = (0.621371212 * (TinyGPSPlus::distanceBetween(lat1, lng1, lat2, lng2)));
  return distBwt;  // thousandths of a mile
}

void FRLogger(void)  // The subroutine that logs waypoint values in Free Run Mode
{
  FRLog = SD.open("FRLog.txt", FILE_WRITE);  // Create or open the FRLog file for writing
  if (Started == false) {
    // Add software rev to Free Run Log header:
    FRLog.print("Software Rev is: ");
    FRLog.println(Rev);

    FRLog.println("Free Run Log of Waypoints: ");  // Write this heading once into the log
  }
  FRLog.print("Miles: ");
  FRLog.print(Miles);
  oldMiles = Miles;
  FRLog.write(' ');
  FRLog.print("Thousandths: ");
  FRLog.print(thousandths);
  oldThousandths = thousandths;
  FRLog.write(' ');
  FRLog.print("ABTime: ");
  FRLog.print(ABTime);
  FRLog.write(' ');
  FRLog.print("Latitude Degrees: ");
  FRLog.print(latDeg);
  FRLog.print("Latitude millionths degrees: ");
  FRLog.print(latDecDeg);
  FRLog.write(' ');
  FRLog.print("Longitude Degrees: ");
  FRLog.print(lngDeg);
  FRLog.print("Longitude millionths degrees: ");
  FRLog.print(lngDecDeg);
  FRLog.println(' ');
  FRLog.close();
}

void FFR1(void)  // This subroutine is called if past the finish on Leg 1
{
  MyTimer5.end();   // stop the 100 Hz timer
  Finished = true;  // set the Finished flag

  detachInterrupt(PB_PIN);  // stop the PB interrupt
  if (PFFlag == true) {
    // latCP = latC;  // capture the latitude past the finish line
    // lngCP = lngC; // capture the longitude past the finish line
    actualTimeAtPF = actualTime;
    //MilesAtPF = Miles;
    thousandthsAtPF = thousandths + Miles * 1000;
    velocityAtPF = velocityMPH;
    dynLAFatPF = dynLAF;
    // REV 23Y: Use estimated distPast instead of this:
    //if ((L1brg == 0) || (L1brg == 2)) // north or south bearing - hold longitude constant
    //{
    //distPast = (TinyGPSPlus::distanceBetween(latCP, lngCP, L1WP4Lat, lngCP));
    //}
    //if ((L1brg == 1) || (L1brg == 3)) // east or west bearing - hold latitude constant
    //{
    //distPast = (TinyGPSPlus::distanceBetween(latCP, lngCP, latCP, L1WP4Lng));
    //}
    digitalWrite(REDLED_PIN, LOW);  // turn on the red LED
    redLED = true;
    digitalWrite(YELLED_PIN, HIGH);  // turn off the yellow LED
    yellowLED = false;

    finishThous = thousandthsAtPF - (distPast - (dynLAF * (velocityAtPF / 100)));
    // actualTime = actualTimeAtPF - (int(distPast / velocityAtPF / 100) - dynLAF);
    actTimeAdj = 100 * distPast / velocityAtPF;
    actualTime = actualTimeAtPF + dynLAF;
    actualTime = actualTime - int(actTimeAdj);

  }  // END PFFlag == true
  else {
    finishThous = Miles * 1000 + thousandths;
    perfectTime = finishL1Thous * 360 / targetSpeed;
  }
  ABTime = perfectTime - actualTime;
  digitalWrite(REDLED_PIN, LOW);  // turn on the red LED
  redLED = true;
  digitalWrite(YELLED_PIN, HIGH);  // turn off the yellow LED
  yellowLED = false;

  arrayLogMileage[4] = finishThous;  // INSERT A LOG OF THE ACTUAL FINISH MILEAGE RATHER THAN THE SLAMMED MILEAGE
  Miles = (finishThous - finishThous % 1000) / 1000;

  thousandths = (finishThous + 0.0001 - Miles * 1000);

  errorOut = (ABTime);  // Save the errorOut from Leg 1 in centiseconds

  // Delete any prior ERR.txt file
  SD.remove("ERR.txt");

  //CREATE A NEW ERR.txt FILE ON THE SD CARD AND WRITE errorOut TO IT

  err = SD.open("ERR.txt", FILE_WRITE);  // This creates the err file for writing
  err.seek(0);

  char errOut[10];
  itoa(errorOut, errOut, 10);  // convert integer to ASCII, base 10

  err.write(errOut);  // write the value of the errorOut in centiseconds to the SD card file

  err.write('\n');  // add a return character at the end (there should already be one)

  err.close();  // Close the file

  // POPULATE THE LOG ARRAY for waypoint 4 in Leg 1:
  arrayLogM[4] = Miles;
  arrayLogT[4] = thousandths;
  // arrayLogMileage[4] = Miles + (float(thousandths / 1000.0));
  arrayLogAB[4] = ABTime;
  // REV 23Y Logging Change:
  arrayLogToD[0] = int(distPast);  // log thousandths of a mile past finish rather than meters
  arrayLogToD[1] = dynLAF;
  arrayLogToD[2] = actualTimeAtPF;
  //arrayLogToD[3] = MilesAtPF;
  arrayLogToD[4] = thousandthsAtPF;
  // END REV 23Y Logging Change
  arrayLogAT[4] = actualTime;
  arrayLogSW[4] = swCount;
  arrayLogSpeed[4] = velocityMPH;  // speed in mph

  // POPULATE THE LOG ARRAY:
  for (int j = 0; j < COLL_DIM; j++) {
    arrayL1[0][j] = arrayLogORRMileage[j];
    arrayL1[1][j] = arrayLogMileage[j];
    arrayL1[2][j] = arrayLogToD[j];

    arrayL1[3][j] = arrayLogDist[j];  // LOGS DISTANCE FROM DETECTION TO WAYPOINT

    arrayL1[4][j] = arrayLogAT[j];
    arrayL1[5][j] = arrayLogAB[j];
    arrayL1[6][j] = arrayLogSpeed[j];
    arrayL1[7][j] = arrayLogSW[j];
  }

  // NOW WRITE DATA TO THE LOG
  L1Log = SD.open("L1Log.txt", FILE_WRITE);  // create a file called L1Log.txt on SD card
  L1Log.seek(0);                             // go to beginning of the file
  // ADD Software Rev to Leg 1 Log:
  L1Log.print("Software Rev is: ");
  L1Log.println(Rev);

  for (int r = 0; r < ROWL_DIM; r++) {
    if (r == 0) {
      L1Log.println("Leg 1 Log:");
      L1Log.print("Official mileage in thousandths at waypoint itself: ");
      for (int i = 0; i < COLL_DIM; i++) {
        L1Log.print(arrayL1[0][i], 0);
        L1Log.write(' ');
      }
      L1Log.write('\n');
    }
    if (r == 1) {
      L1Log.print("Thousandths of a mile at waypoint itself: ");
      for (int i = 0; i < COLL_DIM; i++) {
        L1Log.print(arrayL1[1][i], 0);
        L1Log.write(' ');
      }
      L1Log.write('\n');
    }
    if (r == 2) {
      // L1Log.print("Time of Day in UTC Seconds = ");
      L1Log.print("distPastThous, dynLAF, actualTimeAtPF, thousandthsAtPF: ");  //REV 23Y DIAGNOSTIC
      for (int i = 0; i < COLL_DIM; i++) {
        L1Log.print((arrayL1[2][i]), 0);
        L1Log.write(' ');
      }
      L1Log.write('\n');
    }
    if (r == 3) {
      L1Log.print("Thousandths of a mile from detection to waypoint: ");
      for (int i = 0; i < COLL_DIM; i++) {
        L1Log.print(arrayL1[3][i], 0);
        L1Log.write(' ');
      }
      L1Log.write('\n');
    }

    if (r == 4) {
      L1Log.print("Actual time in seconds at waypoint: ");
      for (int i = 0; i < COLL_DIM; i++) {
        L1Log.print(((arrayL1[4][i]) / 100.0), 2);
        L1Log.write(' ');
      }
      L1Log.write('\n');
    }
    if (r == 5) {
      L1Log.print("Ahead Behind Time in seconds at waypoint: ");
      for (int i = 0; i < COLL_DIM; i++) {
        L1Log.print(((arrayL1[5][i]) / 100.0), 2);
        L1Log.write(' ');
      }
      L1Log.write('\n');
    }
    if (r == 6) {
      L1Log.print("Speed in miles per hour: ");
      for (int i = 0; i < COLL_DIM; i++) {
        L1Log.print(arrayL1[6][i], 3);
        L1Log.write(' ');
      }
      L1Log.write('\n');
    }
    if (r == 7) {
      L1Log.print("Stopwatch Count in centiseconds: ");
      for (int i = 0; i < COLL_DIM; i++) {
        L1Log.print(arrayL1[7][i], 0);
        L1Log.write(' ');
      }
      L1Log.write('\n');
    }
  }  // END r++ loop

  L1Log.write('\n');  // add a line feed
  L1Log.close();      // close the file
}

void FFR2(void)  // The Finish, Freeze, and Recalculate subroutine for Leg 2
{
  MyTimer5.end();   // stop the 100 Hz timer
  Finished = true;  // set the Finished flag
  //detachInterrupt(DD_PIN);  // stop the DD pulses from interrupting
  detachInterrupt(PB_PIN);  // stop the PB interrupt
  if (PFFlag == true) {
    //latCP = latC;  // capture the latitude past the finish line
    //lngCP = lngC; // capture the longitude past the finish line
    actualTimeAtPF = actualTime;
    //MilesAtPF = Miles;
    thousandthsAtPF = thousandths;
    velocityAtPF = velocityMPH;
    dynLAFatPF = dynLAF;
    // REV 23Y Use estimated distPast rather than these calculations:
    // if ((L2brg == 0) || (L2brg == 2)) // north or south bearing - hold longitude constant
    // {
    //  distPast = (TinyGPSPlus::distanceBetween(latCP, lngCP, L2WP4Lat, lngCP));
    //}
    //if ((L2brg == 1) || (L2brg == 3)) // east or west bearing - hold latitude constant
    //{
    // distPast = (TinyGPSPlus::distanceBetween(latCP, lngCP, latCP, L2WP4Lng));
    //}
    digitalWrite(REDLED_PIN, LOW);  // turn on the red LED
    redLED = true;
    digitalWrite(YELLED_PIN, HIGH);  // turn off the yellow LED
    yellowLED = false;

    finishThous = thousandthsAtPF - distPast - (dynLAF * (velocityAtPF / 100));
    //actualTime = actualTimeAtPF - (int(distPast / velocityAtPF / 100) - dynLAF);
    actTimeAdj = 100 * distPast / velocityAtPF;
    actualTime = actualTimeAtPF + dynLAF;
    actualTime = actualTime - int(actTimeAdj);
  } else {
    finishThous = Miles * 1000 + thousandths;
    //finishMileage = Miles + float(thousandths / 1000.0);
    perfectTime = finishL2Thous * 360 / targetSpeed;
  }
  ABTime = perfectTime - actualTime;
  digitalWrite(REDLED_PIN, LOW);  // turn on the red LED
  redLED = true;
  digitalWrite(YELLED_PIN, HIGH);  // turn off the yellow LED
  yellowLED = false;

  arrayLogMileage[4] = finishThous;  // INSERT A LOG OF THE ACTUAL FINISH MILEAGE RATHER THAN THE SLAMMED MILEAGE
  //Miles = int(finishMileage);
  //thousandths = int((finishMileage + 0.0001 - Miles) * 1000);
  // POPULATE THE Log Array for waypoint 4 in Leg 2:
  arrayLogM[4] = Miles;
  arrayLogT[4] = thousandths;
  //arrayLogMileage[4] = Miles + (float(thousandths / 1000.0));
  arrayLogAB[4] = ABTime;
  //REV 23Y Logging
  arrayLogToD[0] = int(distPast);  // log thousandths of a mile past finish rather than meters
  arrayLogToD[1] = dynLAF;
  arrayLogToD[2] = actualTimeAtPF;
  //arrayLogToD[3] = MilesAtPF;
  arrayLogToD[4] = thousandthsAtPF;
  arrayLogAT[4] = actualTime;
  arrayLogSW[4] = swCount;
  arrayLogSpeed[4] = velocityMPH;  // speed in mph

  // POPULATE THE LOG ARRAY:
  for (int j = 0; j < COLL_DIM; j++) {
    arrayL2[0][j] = arrayLogORRMileage[j];
    arrayL2[1][j] = arrayLogMileage[j];
    arrayL2[2][j] = arrayLogToD[j];
    arrayL2[3][j] = arrayLogDist[j];
    arrayL2[4][j] = arrayLogAT[j];
    arrayL2[5][j] = arrayLogAB[j];
    arrayL2[6][j] = arrayLogSpeed[j];
    arrayL2[7][j] = arrayLogSW[j];
  }
  // NOW WRITE DATA TO THE LOG

  L2Log = SD.open("L2Log.txt", FILE_WRITE);  // This creates the Leg 2 Log file for writing
  L2Log.seek(0);
  // ADD Software Rev to Leg 2 Log
  L2Log.print("Software Rev is: ");
  L2Log.println(Rev);

  for (int r = 0; r < ROWL_DIM; r++) {
    if (r == 0) {
      L2Log.println("Leg 2 Log:");
      L2Log.print("Official mileage in thousandths miles at waypoint itself: ");
      for (int i = 0; i < COLL_DIM; i++) {
        L2Log.print(arrayL2[0][i], 0);
        L2Log.write(' ');
      }
      L2Log.write('\n');  // add a line feed after this row
    }
    if (r == 1) {
      L2Log.print("Mileage in thousandths at waypoint itself: ");
      for (int i = 0; i < COLL_DIM; i++) {
        L2Log.print(arrayL2[1][i], 0);
        L2Log.write(' ');
      }
      L2Log.write('\n');  // add a line feed after this row
    }
    if (r == 2) {
      //L2Log.print("UTC Time of Day in Seconds = ");
      L2Log.print("distPastThous, dynLAF, actualTimeAtPF, thousandthsAtPF: ");  //REV 23Y Logging
      for (int i = 0; i < COLL_DIM; i++) {
        L2Log.print((arrayL2[2][i]), 0);
        L2Log.write(' ');
      }
      L2Log.write('\n');  // add a line feed after this row
    }
    if (r == 3) {
      L2Log.print("Thousandths of a mile to waypoint from detection: ");
      for (int i = 0; i < COLL_DIM; i++) {
        L2Log.print(arrayL2[3][i], 0);
        L2Log.write(' ');
      }
      L2Log.write('\n');  // add a line feed after this row
    }
    if (r == 4) {
      L2Log.print("Actual time in seconds at waypt: ");
      for (int i = 0; i < COLL_DIM; i++) {
        L2Log.print(((arrayL2[4][i]) / 100.0), 2);
        L2Log.write(' ');
      }
      L2Log.write('\n');  // add a line feed after this row
    }
    if (r == 5) {
      L2Log.print("Ahead Behind Time in seconds at waypoint: ");
      for (int i = 0; i < COLL_DIM; i++) {
        L2Log.print(((arrayL2[5][i]) / 100.0), 2);
        L2Log.write(' ');
      }
      L2Log.write('\n');  // add a line feed after this row
    }

    if (r == 7) {
      L2Log.print("Stopwatch Count in centiseconds: ");
      for (int i = 0; i < COLL_DIM; i++) {
        L2Log.print(arrayL2[7][i], 0);
        L2Log.write(' ');
      }
      L2Log.write('\n');  // add a line feed after this row
    }
  }                   // END r++ loop
  L2Log.write('\n');  // add a line feed
  L2Log.close();      // close the file
}  // END FFR2(void)

void DNLAF(void) {
  actTimeRem = actualTimeTS % 100;            // get just the centiseconds portion of timestamped actualTime
  dynLAF = -(actTimeRem * 10 - timeMS) / 10;  // the centiseconds difference between current time and
  // last GPS reading timestamp
  if (dynLAF > 0)  // if the dynamic LAF is positive instead of negative,
  {
    dynLAF = -(actTimeRem * 10 + 1000 - timeMS) / 10;  // add a second and then find the delta
  }
  // COMPENSATE FOR ANTENNA DISTANCE FROM FRONT OF CAR
  dynLAF = dynLAF - ((100 * antD) / (1.4666667 * velocityMPH));  // makes dynLAF more negative
}

// INTERRUPTS

void PPS(void)  // The GPS PPS interrupt
{
  PPSInt = true;            // Set the PPSInt flag
  PPSCount = PPSCount + 1;  // Increment the PPSCount
  countTwoPPS = countTwoPPS + 1;
  if (Started == true) {
    ToDSeconds = ((3600 * timeHr) + (60 * timeMin) + timeSecs + 1);
    if (ToDSeconds < ToDStartSeconds) {
      ToDStartSeconds = ToDStartSeconds - 86400;  // To handle midnight UTC crossover
    }
    // if (ToDSeconds > oldTimeSeconds) {
    PPSCount = ToDSeconds - ToDStartSeconds;
    if (PPSCount % 10 == 0)  // Make the adjustment every 10 seconds
    {
      if ((PPSCount > 10) && (actualTime % 100 < 10)) {
        adjTime = actualTime - actualTime % 100;  // take off the extra centiseconds
      } else {
        adjTime = actualTime;
      }
      if (L1 == true) {
        actualTime = adjTime;  // adjust the actual time for clock being too fast
      }
      if (L2 == true) {
        actualTime = adjTime - errorOut;
      }

      if (swEnable == true) {
        swCount = adjTime;
      }
    }


    oldTimeSeconds = ToDSeconds;  // store the last ToDSeconds reading
  }                               // END STARTED == TRUE
  countTenPPS = countTenPPS + 1;

}  // End PPS ISR

void Timer5_IRQ(void)  // This interrupts every 10 msecs if set at 100Hz
{
  clockInt = true;  // set the clock interrupt flag for outside isr processing every centisecond

  if ((PBInt == true) && (swEnable == true) && (Started == true) && (waypt >= 4)) {
    detachInterrupt(PB_PIN);
    PBInt = false;
    arrayLogSW[4] = swCount;
    swEnable = false;
    if (L1 == true) {
      FFR1();
    }
    if (L2 == true) {
      FFR2();
    }
  }
  if (swEnable == true) {
    swCount = swCount + 1;  // increment the stopwatch count
  }
  actualTime = actualTime + 1;
  TenHzCtr = TenHzCtr + 1;
  TenHertzCtr = TenHertzCtr + 1;
  if (TenHzCtr >= 10) {
    TenHzCtr = 0;
    TenHzInt = true;
    // Decrement the latitude NOW
    // distBwtFlag = true; // raise the flag to call the getDistBwt subroutine
  }
  if (TenHertzCtr >= 10) {

    TenHertzCtr = 0;
    TenHertzInt = true;
  }
}  // END Timer5 interrupt service routine


void PB(void)  // The PB interrupt
{
  (PBInt = true);  // set the PBInt flag on
}
