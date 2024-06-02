---- MODULE ConcurrentMultiplePluscal ----

EXTENDS Naturals

\* 5..7 -> 4
\* 8..10 -> 5
\* 11..13 -> 6

K == 4
N == 4
MinShared == (N + 1) \div 3 + 2

Threads == 0..(K - 1)

(* --algorithm concurrent_increment

variables shared = 0

define
    Correctness == <>(shared > MinShared)
end define;

fair process inc \in Threads
variables local = 0, count = N;
begin F:
    while count > 0 do
            local := shared;
        S:
            shared := local + 1;
            count := count - 1;
    end while;
end process;

end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "4c07df00" /\ chksum(tla) = "45044520")
VARIABLES shared, pc

(* define statement *)
Correctness == <>(shared > MinShared)

VARIABLES local, count

vars == << shared, pc, local, count >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ shared = 0
        (* Process inc *)
        /\ local = [self \in Threads |-> 0]
        /\ count = [self \in Threads |-> N]
        /\ pc = [self \in ProcSet |-> "F"]

F(self) == /\ pc[self] = "F"
           /\ IF count[self] > 0
                 THEN /\ local' = [local EXCEPT ![self] = shared]
                      /\ pc' = [pc EXCEPT ![self] = "S"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ local' = local
           /\ UNCHANGED << shared, count >>

S(self) == /\ pc[self] = "S"
           /\ shared' = local[self] + 1
           /\ count' = [count EXCEPT ![self] = count[self] - 1]
           /\ pc' = [pc EXCEPT ![self] = "F"]
           /\ local' = local

inc(self) == F(self) \/ S(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: inc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(inc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
