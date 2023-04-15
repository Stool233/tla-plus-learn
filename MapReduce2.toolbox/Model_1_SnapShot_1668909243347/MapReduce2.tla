----------------------------- MODULE MapReduce2 -----------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets

PT == INSTANCE PT

CONSTANTS Workers, Reducer, NULL

PossibleInputs == PT!TupleOf(0..2, 4)

SumSeq(seq) == PT!ReduceSeq(LAMBDA x, y: x + y, seq, 0)
FairWorkers == CHOOSE set_w \in SUBSET Workers: Cardinality(set_w) = 1
UnfairWorkers == Workers \ FairWorkers

(*--algorithm mapreduce
variables 
    input \in PossibleInputs;
    result = [w \in Workers |-> NULL];
    queue = [w \in Workers |-> <<>>]; 



procedure work()
    variables total = 0;
begin
    WaitForQueue:
        await queue[self] /= <<>>;
    Process:
        while queue[self] /= <<>> do
            total := total + Head(queue[self]);
            queue[self] := Tail(queue[self]);
        end while;
    Result:
        result[self] := total;
        return;
end procedure;



fair process reducer = Reducer
variables final = 0, consumed = [w \in Workers |-> FALSE];
begin
    Schedule:
        with worker_order = PT!OrderSet(Workers) do
            queue := [ w \in Workers |-> 
                LET offset == PT!Index(worker_order, w) - 1 \* sequences start at 1
                IN PT!SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) = 
                offset)
            ];
        end with;
    ReduceResult:
        while \E w \in Workers: ~consumed[w] do
            with w \in {w \in Workers: ~consumed[w] /\ result[w] /= NULL} do
                final := final + result[w];
                consumed[w] := TRUE;
            end with;
        end while;
    Finish:
        assert final = SumSeq(input);
end process;

fair process fair_workers \in FairWorkers
begin FairWorker:
    call work();
end process;

process worker \in UnfairWorkers
begin RegularWorker:
    call work();
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7f53de9" /\ chksum(tla) = "e6392a9d")
VARIABLES input, result, queue, pc, stack, total, final, consumed

vars == << input, result, queue, pc, stack, total, final, consumed >>

ProcSet == {Reducer} \cup (FairWorkers) \cup (UnfairWorkers)

Init == (* Global variables *)
        /\ input \in PossibleInputs
        /\ result = [w \in Workers |-> NULL]
        /\ queue = [w \in Workers |-> <<>>]
        (* Procedure work *)
        /\ total = [ self \in ProcSet |-> 0]
        (* Process reducer *)
        /\ final = 0
        /\ consumed = [w \in Workers |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = Reducer -> "Schedule"
                                        [] self \in FairWorkers -> "FairWorker"
                                        [] self \in UnfairWorkers -> "RegularWorker"]

WaitForQueue(self) == /\ pc[self] = "WaitForQueue"
                      /\ queue[self] /= <<>>
                      /\ pc' = [pc EXCEPT ![self] = "Process"]
                      /\ UNCHANGED << input, result, queue, stack, total, 
                                      final, consumed >>

Process(self) == /\ pc[self] = "Process"
                 /\ IF queue[self] /= <<>>
                       THEN /\ total' = [total EXCEPT ![self] = total[self] + Head(queue[self])]
                            /\ queue' = [queue EXCEPT ![self] = Tail(queue[self])]
                            /\ pc' = [pc EXCEPT ![self] = "Process"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Result"]
                            /\ UNCHANGED << queue, total >>
                 /\ UNCHANGED << input, result, stack, final, consumed >>

Result(self) == /\ pc[self] = "Result"
                /\ result' = [result EXCEPT ![self] = total[self]]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ total' = [total EXCEPT ![self] = Head(stack[self]).total]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << input, queue, final, consumed >>

work(self) == WaitForQueue(self) \/ Process(self) \/ Result(self)

Schedule == /\ pc[Reducer] = "Schedule"
            /\ LET worker_order == PT!OrderSet(Workers) IN
                 queue' =          [ w \in Workers |->
                              LET offset == PT!Index(worker_order, w) - 1
                              IN PT!SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) =
                              offset)
                          ]
            /\ pc' = [pc EXCEPT ![Reducer] = "ReduceResult"]
            /\ UNCHANGED << input, result, stack, total, final, consumed >>

ReduceResult == /\ pc[Reducer] = "ReduceResult"
                /\ IF \E w \in Workers: ~consumed[w]
                      THEN /\ \E w \in {w \in Workers: ~consumed[w] /\ result[w] /= NULL}:
                                /\ final' = final + result[w]
                                /\ consumed' = [consumed EXCEPT ![w] = TRUE]
                           /\ pc' = [pc EXCEPT ![Reducer] = "ReduceResult"]
                      ELSE /\ pc' = [pc EXCEPT ![Reducer] = "Finish"]
                           /\ UNCHANGED << final, consumed >>
                /\ UNCHANGED << input, result, queue, stack, total >>

Finish == /\ pc[Reducer] = "Finish"
          /\ Assert(final = SumSeq(input), 
                    "Failure of assertion at line 58, column 9.")
          /\ pc' = [pc EXCEPT ![Reducer] = "Done"]
          /\ UNCHANGED << input, result, queue, stack, total, final, consumed >>

reducer == Schedule \/ ReduceResult \/ Finish

FairWorker(self) == /\ pc[self] = "FairWorker"
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "work",
                                                             pc        |->  "Done",
                                                             total     |->  total[self] ] >>
                                                         \o stack[self]]
                    /\ total' = [total EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "WaitForQueue"]
                    /\ UNCHANGED << input, result, queue, final, consumed >>

fair_workers(self) == FairWorker(self)

RegularWorker(self) == /\ pc[self] = "RegularWorker"
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "work",
                                                                pc        |->  "Done",
                                                                total     |->  total[self] ] >>
                                                            \o stack[self]]
                       /\ total' = [total EXCEPT ![self] = 0]
                       /\ pc' = [pc EXCEPT ![self] = "WaitForQueue"]
                       /\ UNCHANGED << input, result, queue, final, consumed >>

worker(self) == RegularWorker(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == reducer
           \/ (\E self \in ProcSet: work(self))
           \/ (\E self \in FairWorkers: fair_workers(self))
           \/ (\E self \in UnfairWorkers: worker(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(reducer)
        /\ \A self \in FairWorkers : WF_vars(fair_workers(self)) /\ WF_vars(work(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


Liveness == <>[](final = SumSeq(input))

=============================================================================
\* Modification History
\* Last modified Sun Nov 20 01:19:57 CST 2022 by wengjialin
\* Created Sat Nov 19 22:46:34 CST 2022 by wengjialin
