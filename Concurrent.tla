-------------------------- MODULE Concurrent  --------------------------

EXTENDS Naturals

VARIABLES shared, state, local, lock

vars == << shared, state, local, lock >>

N == 5

Threads == 0..(N - 1)

TypeOK == 
  /\ shared \in Nat
  /\ DOMAIN local = Threads
  /\ \A t \in Threads: local[t] \in 0..N
  /\ DOMAIN state = Threads
  /\ \A v \in Threads: state[v] \in { "fetch", "store", "done" }
  /\ lock \in 0..N

WithLocking == FALSE

IsUnlocked == lock = N
Lock(t) == IF WithLocking THEN t \in Threads /\ lock' = t ELSE UNCHANGED << lock >>
IsLockedBy(t) == WithLocking => t \in Threads /\ lock = t
Unlock == IF WithLocking THEN lock' = N ELSE UNCHANGED << lock >>

Init ==
  /\ shared = 0
  /\ state = [t \in Threads |-> "fetch"]
  /\ local = [t \in Threads |-> 0]
  /\ IsUnlocked

Fetch(t) == \* local = local + 1
  \* preconditions
  /\ state[t] = "fetch"
  /\ IsUnlocked
  \* effect
  /\ local' = [local EXCEPT ![t] = shared]
  \* state change
  /\ state' = [state EXCEPT ![t] = "store"]
  /\ Lock(t)
  /\ UNCHANGED << shared >>

Store(t) == \* shared = local
  \* preconditions
  /\ state[t] = "store"
  /\ IsLockedBy(t)
  \* effect
  /\ shared' = local[t] + 1
  \* state change
  /\ state' = [state EXCEPT ![t] = "done"]
  /\ Unlock
  /\ UNCHANGED << local >>

WithTermination == FALSE

Terminating ==
  /\ WithTermination
  /\ \A t \in Threads : state[t] = "done"
  /\ UNCHANGED vars

Next == 
  \/ \E t \in Threads : Fetch(t)
  \/ \E t \in Threads : Store(t)
  \/ Terminating \* OK to stay in final state[t] = "done"

WithProgress == FALSE

Progress == WithProgress => \A t \in Threads : WF_state(Next)

Spec == Init /\ [][Next]_vars /\ Progress

WithCorrectness == FALSE

Correctness == <>(WithCorrectness => shared = N /\ IsUnlocked)

====
