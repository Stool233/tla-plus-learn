----------------------------- MODULE MapReduce -----------------------------

EXTENDS Integers, TLC, Sequences

PT == INSTANCE PT

CONSTANTS Workers, Reducer, NULL

PossibleInputs == PT!TupleOf(0..2, 4)

SumSeq(seq) == PT!ReduceSeq(LAMBDA x, y: x + y, seq, 0)

(*--algorithm mapreduce
variables input \in PossibleInputs;

process reducer = Reducer
variables final = 0;
begin
    Schedule:
        skip;
    ReduceResult:
        skip;
    Finish:
        assert final = SumSeq(input);
end process;

process worker \in Workers
begin
    Worker:
        skip;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "6f344a4a" /\ chksum(tla) = "508de158")
VARIABLES input, pc, final

vars == << input, pc, final >>

ProcSet == {Reducer} \cup (Workers)

Init == (* Global variables *)
        /\ input \in PossibleInputs
        (* Process reducer *)
        /\ final = 0
        /\ pc = [self \in ProcSet |-> CASE self = Reducer -> "Schedule"
                                        [] self \in Workers -> "Worker"]

Schedule == /\ pc[Reducer] = "Schedule"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![Reducer] = "ReduceResult"]
            /\ UNCHANGED << input, final >>

ReduceResult == /\ pc[Reducer] = "ReduceResult"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![Reducer] = "Finish"]
                /\ UNCHANGED << input, final >>

Finish == /\ pc[Reducer] = "Finish"
          /\ Assert(final = SumSeq(input), 
                    "Failure of assertion at line 24, column 9.")
          /\ pc' = [pc EXCEPT ![Reducer] = "Done"]
          /\ UNCHANGED << input, final >>

reducer == Schedule \/ ReduceResult \/ Finish

Worker(self) == /\ pc[self] = "Worker"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << input, final >>

worker(self) == Worker(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == reducer
           \/ (\E self \in Workers: worker(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat Nov 19 16:07:27 CST 2022 by wengjialin
\* Created Sat Nov 19 15:22:03 CST 2022 by wengjialin
