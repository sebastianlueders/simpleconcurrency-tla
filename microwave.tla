---- MODULE microwave ----
EXTENDS TLC, Integers
CONSTANTS CounterMin, CounterMax, N
ASSUME CounterMin < CounterMax

(* --algorithm the_microwave

variables action = "none"

process user = "user"
begin U:
  while TRUE do
    either 
      action := "doorOpen"
    or 
      action := "doorClose"
    or 
      action := "10min"
    or 
      action := "1min"
    or 
      action := "10sec"
    or 
      action := "1sec"
    or 
      action := "power"
    or 
      action := "timer"
    or 
      action := "start"
    or 
      action := "stop"
    or 
      action := "none"
    end either
  end while
end process
  
process counter = "microwave"
variables value = 0
begin C:
  while TRUE do
    either
      await action = "inc"
    ; if value < CounterMax then value := value + 1 end if
    or
      await action = "dec"
    ; if value > CounterMin then value := value - 1 end if
    or
      await action = "reset"
    ; value := CounterMin
    end either
  ; assert CounterMin <= value /\ value <= CounterMax
  end while
end process

end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "4488d2f4" /\ chksum(tla) = "79b7ec1f")
VARIABLES action, value

vars == << action, value >>

ProcSet == {"user"} \cup {"microwave"}

Init == (* Global variables *)
        /\ action = "none"
        (* Process counter *)
        /\ value = 0

user == /\ \/ /\ action' = "doorOpen"
           \/ /\ action' = "doorClose"
           \/ /\ action' = "10min"
           \/ /\ action' = "1min"
           \/ /\ action' = "10sec"
           \/ /\ action' = "1sec"
           \/ /\ action' = "power"
           \/ /\ action' = "timer"
           \/ /\ action' = "start"
           \/ /\ action' = "stop"
           \/ /\ action' = "none"
        /\ value' = value

counter == /\ \/ /\ action = "inc"
                 /\ IF value < CounterMax
                       THEN /\ value' = value + 1
                       ELSE /\ TRUE
                            /\ value' = value
              \/ /\ action = "dec"
                 /\ IF value > CounterMin
                       THEN /\ value' = value - 1
                       ELSE /\ TRUE
                            /\ value' = value
              \/ /\ action = "reset"
                 /\ value' = CounterMin
           /\ Assert(CounterMin <= value' /\ value' <= CounterMax, 
                     "Failure of assertion at line 53, column 5.")
           /\ UNCHANGED action

Next == user \/ counter

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
