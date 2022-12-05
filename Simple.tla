-------------------------- MODULE Simple  --------------------------

EXTENDS Integers

VARIABLES v

Max == 1000

Init == v = 0

Next == 
  \/  /\ v < Max
      /\ v' = v + 1
  \/  /\ v >= Max
      /\ UNCHANGED <<v>>

Spec == (v = 0) /\  [][IF v < Max THEN v' = v + 1 ELSE UNCHANGED <<v>>]_v

====
