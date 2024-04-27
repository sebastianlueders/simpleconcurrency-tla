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
  /\ DOMAIN lock = Threads
  /\ \A v \in Threads: lock[v] \in BOOLEAN 

Init ==
  /\ shared = 0
  /\ state = [t \in Threads |-> "fetch"]
  /\ local = [t \in Threads |-> 0]
  /\ lock = [t \in Threads |-> FALSE]

Fetch(t) == \* local = local + 1
  /\ state[t] = "fetch"
  /\ \A k \in Threads : ~ lock[k]
  /\ local' = [local EXCEPT ![t] = shared]
  /\ state' = [state EXCEPT ![t] = "store"]
  /\ lock' = [lock EXCEPT ![t] = TRUE]
  /\ UNCHANGED << shared >>

Store(t) == \* shared = local
  /\ state[t] = "store"
  /\ lock[t]
  /\ shared' = local[t] + 1
  /\ state' = [state EXCEPT ![t] = "done"]
  /\ lock' = [lock EXCEPT ![t] = FALSE]
  /\ UNCHANGED << local >>

Terminating ==
  /\ \A t \in Threads : state[t] = "done"
  /\ UNCHANGED vars

\* WithTermination == FALSE

Next == 
  \/ \E t \in Threads : Fetch(t)
  \/ \E t \in Threads : Store(t)
  \/ Terminating \* OK to stay in final state state[t] = "done"

\* Progress == TRUE

Progress == \A t \in Threads : WF_state(Next)

Spec == Init /\ [][Next]_vars /\ Progress

\* Correctness == TRUE

Correctness == <>(shared = N)

====
