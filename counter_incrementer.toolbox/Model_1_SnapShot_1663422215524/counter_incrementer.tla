------------------------ MODULE counter_incrementer ------------------------
EXTENDS Integers, Sequences, TLC

(*--algorithm counter_incrementer
variables
    counter = 0,
    goal = 3;
define
    Success == <>[](counter = goal)
end define;

fair process incrementer \in 1..3
variable local = 0
begin
    Get:
        local := counter;
    Increment:
        counter := local + 1;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "81703eed" /\ chksum(tla) = "78ebc73d")
VARIABLES counter, goal, pc

(* define statement *)
Success == <>[](counter = goal)

VARIABLE local

vars == << counter, goal, pc, local >>

ProcSet == (1..3)

Init == (* Global variables *)
        /\ counter = 0
        /\ goal = 3
        (* Process incrementer *)
        /\ local = [self \in 1..3 |-> 0]
        /\ pc = [self \in ProcSet |-> "Get"]

Get(self) == /\ pc[self] = "Get"
             /\ local' = [local EXCEPT ![self] = counter]
             /\ pc' = [pc EXCEPT ![self] = "Increment"]
             /\ UNCHANGED << counter, goal >>

Increment(self) == /\ pc[self] = "Increment"
                   /\ counter' = local[self] + 1
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << goal, local >>

incrementer(self) == Get(self) \/ Increment(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..3: incrementer(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..3 : WF_vars(incrementer(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Sat Sep 17 21:41:43 CST 2022 by wengjialin
\* Created Sat Sep 17 21:39:26 CST 2022 by wengjialin
