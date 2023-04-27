-------------------------- MODULE Microwave  --------------------------

EXTENDS TLC, Integers

CONSTANTS 
    OFF, ON, CLOSED, OPEN

VARIABLES 
    door,
    running,
    timeRemaining

vars == << door, running, timeRemaining >>

TypeOK == door \in { CLOSED, OPEN } /\ running \in { OFF, ON } /\ timeRemaining \in Nat

DoorSafety == TRUE

\* DoorSafety == door = OPEN => running = OFF

HeatLiveness == TRUE

\* HeatLiveness == running = ON ~> running = OFF

OnlyTicksAfterStart == TRUE

\* OnlyTicksAfterStart == [][running = ON => ~ (running' = OFF /\ timeRemaining' > 0)]_<<running, timeRemaining>>

MaxTime == 60

Init ==
    /\ door = CLOSED
    /\ running = OFF
    /\ timeRemaining = 0

IncTime ==
    /\ running = OFF
    /\ timeRemaining' = timeRemaining + 1
    /\ timeRemaining' <= MaxTime
    /\ UNCHANGED << door, running >>

Start ==
    /\ timeRemaining > 0
    /\ running' = ON
    /\ UNCHANGED << door, timeRemaining >>

Cancel ==
    /\ running' = OFF
    /\ timeRemaining' = 0
    /\ UNCHANGED << door >>

Tick ==
    /\ running = ON
    /\ timeRemaining' = timeRemaining - 1
    /\ timeRemaining' >= 0
    /\ IF timeRemaining' = 0 THEN running' = OFF ELSE UNCHANGED << running >>
    /\ UNCHANGED << door >>

OpenDoor ==
    /\ door' = OPEN
    /\ UNCHANGED << running, timeRemaining >>

CloseDoor ==
    /\ door' = CLOSED
    /\ UNCHANGED << running, timeRemaining >>

TickProgress == TRUE

\* TickProgress == WF_timeRemaining(Tick)

Next ==
    \/ IncTime
    \/ Start
    \/ Cancel
    \/ OpenDoor
    \/ CloseDoor
    \/ Tick

Spec == Init /\ [][Next]_vars /\ TickProgress

====

(* other possible events
      action := "10min"
      action := "1min"
      action := "10sec"
      action := "1sec"
      action := "power"
      action := "timer"
*)
