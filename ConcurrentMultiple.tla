\*34567890123456789012345678901234567890123456789012

-------------------------- MODULE ConcurrentMultiple  --------------------------

EXTENDS Naturals

VARIABLES shared, state, count, local, lock

vars == << shared, state, count, local, lock >>

RequireCorrectness == FALSE

ImplementTermination == FALSE
ImplementProgress == TRUE
ImplementLocking == FALSE

N == 2 \* number of threads

K == 4 \* number of increments per thread

Threads == 0..(N - 1)

TypeOK ==
  /\ shared \in Nat
  /\ DOMAIN local = Threads
  /\ DOMAIN count = Threads
  /\ DOMAIN state = Threads
  /\ \A t \in Threads: 
    /\ count[t] \in 0..K
    /\ state[t] \in { "fetch", "store", "done" }
    /\ local[t] \in 0..(N * K)
  /\ lock \in 0..N

IsUnlocked == lock = N
Lock(t) == IF ImplementLocking
  THEN t \in Threads /\ lock' = t
  ELSE UNCHANGED << lock >>
IsLockedBy(t) == ImplementLocking =>
  t \in Threads /\ lock = t
Unlock == IF ImplementLocking
  THEN lock' = N
  ELSE UNCHANGED << lock >>

Init ==
  /\ shared = 0
  /\ state = [t \in Threads |-> "fetch"]
  /\ count = [t \in Threads |-> K]
  /\ local = [t \in Threads |-> 0]
  /\ IsUnlocked

Fetch(t) == \* local = local + 1
  \* preconditions
  /\ state[t] = "fetch"
  /\ count[t] > 0
  /\ IsUnlocked
  \* effect
  /\ local' = [local EXCEPT ![t] = shared]
  \* state change
  /\ state' = [state EXCEPT ![t] = "store"]
  /\ Lock(t)
  /\ UNCHANGED << count, shared >>

Store(t) == \* shared = local
  \* preconditions
  /\ state[t] = "store"
  /\ IsLockedBy(t)
  \* effect
  /\ shared' = local[t] + 1
  \* state change
  /\ count' = [count EXCEPT ![t] = @ - 1]
  /\ IF count[t] > 1
    THEN state' = [state EXCEPT ![t] = "fetch"]
    ELSE state' = [state EXCEPT ![t] = "done"]
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

Max(X, Y) == IF X > Y THEN X ELSE Y

MinShared == 
  IF K <= 3
  THEN K
  ELSE Max(K + 1 - N, 3)

Correctness == <>(
  IF RequireCorrectness
  THEN shared = N * K /\ IsUnlocked \* correctness when each increment is atomic
  ELSE shared > MinShared \* minimum result when increments can overlap
)

====
