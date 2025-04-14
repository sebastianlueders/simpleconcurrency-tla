---- MODULE ConcurrentMultiplePluscal ----

EXTENDS Naturals

CONSTANTS
    K, \* number of concurrent threads
    N \* number of repetitions per thread

Min(X, Y) == IF X < Y THEN X ELSE Y

MinShared == IF K = 1
  THEN N
  ELSE Min(2, N)

Threads == 0..(K - 1)

(* --algorithm concurrent_increment

variables shared = 0

define
    Correctness == <>[](shared > MinShared)
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

====
