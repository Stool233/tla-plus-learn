----------------------------- MODULE MapReduce -----------------------------

EXTENDS Integers, TLC, Sequences

PT == INSTANCE PT

CONSTANTS Workers, Reducer, NULL

PossibleInputs == PT!TupleOf(0..2, 4)

SumSeq(seq) == PT!ReduceSeq(LAMBDA x, y: x + y, seq, 0)

(*--algorithm mapreduce
variables 
    input \in PossibleInputs;
    result = [w \in Workers |-> NULL];

process reducer = Reducer
variables final = 0, consumed = [w \in Workers |-> FALSE];
begin
    Schedule:
        skip;
    ReduceResult:
        while \E w \in Workers: ~consumed[w] do
            with w \in {w \in Workers: ~consumed[w] /\ result[w] /= NULL} do
                final := final + result[w];
                consumed[w] := TRUE;
            end with;
        end while;
        skip;
    Finish:
        assert final = SumSeq(input);
end process;

process worker \in Workers
begin
    Worker:
        result[self] := 5
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "1eda0518" /\ chksum(tla) = "94205f66")
VARIABLES input, result, pc, final, consumed

vars == << input, result, pc, final, consumed >>

ProcSet == {Reducer} \cup (Workers)

Init == (* Global variables *)
        /\ input \in PossibleInputs
        /\ result = [w \in Workers |-> NULL]
        (* Process reducer *)
        /\ final = 0
        /\ consumed = [w \in Workers |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self = Reducer -> "Schedule"
                                        [] self \in Workers -> "Worker"]

Schedule == /\ pc[Reducer] = "Schedule"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![Reducer] = "ReduceResult"]
            /\ UNCHANGED << input, result, final, consumed >>

ReduceResult == /\ pc[Reducer] = "ReduceResult"
                /\ IF \E w \in Workers: ~consumed[w]
                      THEN /\ \E w \in {w \in Workers: ~consumed[w] /\ result[w] /= NULL}:
                                /\ final' = final + result[w]
                                /\ consumed' = [consumed EXCEPT ![w] = TRUE]
                           /\ pc' = [pc EXCEPT ![Reducer] = "ReduceResult"]
                      ELSE /\ TRUE
                           /\ pc' = [pc EXCEPT ![Reducer] = "Finish"]
                           /\ UNCHANGED << final, consumed >>
                /\ UNCHANGED << input, result >>

Finish == /\ pc[Reducer] = "Finish"
          /\ Assert(final = SumSeq(input), 
                    "Failure of assertion at line 32, column 9.")
          /\ pc' = [pc EXCEPT ![Reducer] = "Done"]
          /\ UNCHANGED << input, result, final, consumed >>

reducer == Schedule \/ ReduceResult \/ Finish

Worker(self) == /\ pc[self] = "Worker"
                /\ result' = [result EXCEPT ![self] = 5]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << input, final, consumed >>

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
\* Last modified Sat Nov 19 16:36:01 CST 2022 by wengjialin
\* Created Sat Nov 19 15:22:03 CST 2022 by wengjialin
