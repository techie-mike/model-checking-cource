------------------------ MODULE DigitalClock ------------------------

EXTENDS Naturals, TLC

CONSTANTS OFF, SETTING_TIME, SHOW_TIME, ALARM, SETTING_ALARM_TIME, PRESSED, PRESSED_HOLD, PRESSED_LONG_HOLD

VARIABLE currentTime, alarmTime, currentState, alarmState, button


(* Initialization: initial state - clock off *)
Init == /\ currentState = OFF
        /\ currentTime \in {0, 100}
        /\ alarmTime = 0
        /\ alarmState = "Off"
        /\ button \in {OFF, PRESSED, PRESSED_HOLD, PRESSED_LONG_HOLD}

(* Actions to set the time - only from settings *)
SetTimeAction(time) ==
    /\ currentState = SETTING_TIME
    /\ currentTime' = time
    /\ currentState' = SHOW_TIME
    /\ UNCHANGED << alarmState, alarmTime, button >>

(* Steps to turn the alarm on/off, for example one of the button*)
ToggleAlarmAction ==
    \/ /\ currentState = SHOW_TIME
       /\ button = PRESSED
       /\ alarmState = "On"
       /\ alarmState' = "Off"  
       /\ UNCHANGED << currentState, alarmTime, button, currentTime >>
    \/ /\ currentState = SHOW_TIME
       /\ button = PRESSED
       /\ alarmState = "Off"
       /\ alarmState' = "On"
       /\ UNCHANGED << currentState, alarmTime, button, currentTime >>
    \/ /\ currentState = ALARM
       /\ button = PRESSED
       /\ alarmState' = "Off"
       /\ currentState' = SHOW_TIME
       /\ UNCHANGED << alarmTime, button, currentTime >>
    \/ /\ currentState = SHOW_TIME
       /\ button = PRESSED_HOLD
       /\ currentState' = SETTING_TIME
       /\ UNCHANGED << alarmState, alarmTime, currentTime, button, currentTime >>
    \/ /\ currentState = SHOW_TIME
       /\ button = PRESSED_LONG_HOLD
       /\ currentState' = SETTING_ALARM_TIME
       /\ UNCHANGED << alarmState, alarmTime, currentTime, button, currentTime >> 

(* Steps to set alarm time - only from alarm settings *)
SetAlarmAction(time) ==
    /\ currentState = SETTING_ALARM_TIME
    /\ alarmTime' = time
    /\ alarmState' = "On"
    /\ currentState' = SHOW_TIME
    /\ UNCHANGED << currentTime, button >>

(* Actions to trigger the alarm, it is assumed that all the settings are set, if we are in the settings, then the alarm does not work *)
AlarmTriggered ==
    /\ currentState = SHOW_TIME
    /\ currentTime = alarmTime
    /\ alarmState = "On"
    /\ alarmState' = "Off"
    /\ currentState' = ALARM
    /\ UNCHANGED << alarmTime, button, currentTime >>
    
UpdateTime ==
    /\ currentTime' = (currentTime + 1) % 86400
    /\ UNCHANGED << alarmState, alarmTime, currentState, button >>

(* Alarm actions *)
Next ==
    \/  /\ currentState = OFF
        /\ currentState' = SHOW_TIME
        /\ currentTime' = 0
        /\ alarmTime' = 0
        /\ alarmState' = "Off"
        /\ UNCHANGED button
    \/ SetTimeAction(120)
    \/ ToggleAlarmAction
    \/ SetAlarmAction(100)
    \/ AlarmTriggered
    \/ UpdateTime
    \/  /\ button' = OFF  (* Disable button *)
        /\ UNCHANGED << alarmState, alarmTime, currentState, currentTime >>

(* Bringing it all together *)
Spec == Init /\ [][Next]_<<currentTime, alarmTime, currentState, alarmState, button>>

=============================================================================
