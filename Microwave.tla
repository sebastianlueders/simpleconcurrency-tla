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

MaxTime == 60

Init ==
    /\ door = CLOSED
    /\ running = OFF
    /\ timeRemaining = 0

\* increment remaining time by one second
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

DoorSafety == TRUE

\* DoorSafety == door = OPEN => running = OFF

\* DoorSafety == running = ON => door = CLOSED

HeatLiveness == TRUE

\* HeatLiveness == running = ON ~> running = OFF

RunsUntilDoneOrInterrupted == TRUE

\* RunsUntilDoneOrInterrupted == 
\*     [][running = ON => running' = ON \/ timeRemaining' = 0 \/ door' = OPEN]_vars

====

(* other possible events
      action := "10min"
      action := "1min"
      action := "10sec"
      action := "power"
      action := "timer"
*)
