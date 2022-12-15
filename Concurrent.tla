-------------------------- MODULE Concurrent  --------------------------

EXTENDS Naturals

VARIABLES shared, pc, local

vars == << shared, pc, local >>

N == 5

Threads == 0..(N - 1)

Init ==
  /\ shared = 0
  /\ pc = [t \in Threads |-> "fetch"]
  /\ local = [t \in Threads |-> 0]

Fetch(t) == 
  /\ pc[t] = "fetch"
  /\ pc' = [pc EXCEPT ![t] = "store"]
  /\ local' = [local EXCEPT ![t] = @ + 1]
  /\ UNCHANGED << shared >>

Store(t) == 
  /\ pc[t] = "store"
  /\ pc' = [pc EXCEPT ![t] = "done"]
  /\ shared' = local[t]
  /\ UNCHANGED << local >>

Inc(t) ==
  /\ pc[t] = "fetch"
  /\ pc' = [pc EXCEPT ![t] = "done"]
  /\ shared' = shared + 1
  /\ UNCHANGED << local >>

Terminating ==
  /\ \A t \in Threads : pc[t] = "done"
  /\ UNCHANGED vars

Next == 
  \* \/ \E t \in Threads : Fetch(t)
  \* \/ \E t \in Threads : Store(t)
  \/ \E t \in Threads : Inc(t)
  \/ Terminating

\* Progress == TRUE

Progress == \A t \in Threads : WF_shared(Inc(t))

Spec == Init /\ [][Next]_vars /\ Progress

Correctness == <>(shared = N)

====
