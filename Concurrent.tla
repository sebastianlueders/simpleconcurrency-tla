\*34567890123456789012345678901234567890123456789012

-------------------------- MODULE Concurrent  --------------------------

EXTENDS Naturals

CONSTANTS
    K, \* number of concurrent threads
    RequireCorrectness,
    ImplementTermination,
    ImplementProgress,
    ImplementLocking

VARIABLES shared, state, local, lock

vars == << shared, state, local, lock >>

Threads == 0..(K - 1)

TypeOK ==
  /\ shared \in Nat
  /\ DOMAIN local = Threads
  /\ \A t \in Threads: local[t] \in 0..K
  /\ DOMAIN state = Threads
  /\ \A v \in Threads: state[v] \in
    { "fetch", "store", "done" }
  /\ lock \in 0..K

IsUnlocked == lock = K
Lock(t) == IF ImplementLocking
  THEN t \in Threads /\ lock' = t
  ELSE UNCHANGED << lock >>
IsLockedBy(t) == ImplementLocking =>
  t \in Threads /\ lock = t
Unlock == IF ImplementLocking
  THEN lock' = K
  ELSE UNCHANGED << lock >>

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

Terminating ==
  /\ ImplementTermination
  /\ \A t \in Threads : state[t] = "done"
  /\ UNCHANGED vars

Next ==
  \/ \E t \in Threads : Fetch(t)
  \/ \E t \in Threads : Store(t)
  \/ Terminating \* OK to stay in state[t] = "done"

Progress == ImplementProgress =>
  \A t \in Threads : WF_state(Next)

Spec == Init /\ [][Next]_vars /\ Progress

Correctness == <>(RequireCorrectness =>
  [](shared = K /\ IsUnlocked))

====
