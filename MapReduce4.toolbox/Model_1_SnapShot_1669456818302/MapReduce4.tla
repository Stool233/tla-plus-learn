----------------------------- MODULE MapReduce4 -----------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets

PT == INSTANCE PT

CONSTANTS Workers, Reducer, NULL

CONSTANTS ItemRange, ItemCount
ASSUME ItemRange \subseteq Nat
ASSUME ItemCount \in Nat

PossibleInputs == PT!TupleOf(ItemRange, ItemCount)

SumSeq(seq) == PT!ReduceSeq(LAMBDA x, y: x + y, seq, 0)
FairWorkers == CHOOSE set_w \in SUBSET Workers: Cardinality(set_w) = 1
UnfairWorkers == Workers \ FairWorkers

(*--algorithm mapreduce
variables 
    input \in PossibleInputs;
    result = [w \in Workers |-> [total |-> NULL, count |-> NULL]];
    queue = [w \in Workers |-> <<>>],
    status = [w \in Workers |-> "active"];  \* Only reducer should touch this 


define
    ActiveWorkers == {w \in Workers: status[w] = "active"}
    HealthyWorkers == {w \in Workers: status[w] /= "broken"}
    TypeInvariant ==
        /\ status \in [Workers -> {"active", "inactive", "broken"}]
        /\ \A w \in Workers:
            /\ Len(queue[w]) <= ItemCount
            
            /\ \A item \in 1..Len(queue[w]):
                queue[w][item] \in ItemRange
            
            /\ \/ result[w].total = NULL
               \/ result[w].total <= SumSeq(input)
            /\ \/ result[w].count = NULL
               \/ result[w].count <= ItemCount
end define;


macro reduce() begin
    with w \in {w \in ActiveWorkers: 
           result[w].count = Len(assignments[w])} 
    do
        final[w] := result[w].total;
        status[w] := "inactive";
    end with;
end macro;


procedure work()
    variables total = 0, count = 0;
begin
    WaitForQueue:
        await queue[self] /= <<>>;
    Process:
        while queue[self] /= <<>> do
            total := total + Head(queue[self]);
            queue[self] := Tail(queue[self]);
            count := count + 1;
        end while;
    Result:
        result[self] := [total |-> total, count |-> count];
        goto WaitForQueue;
end procedure;




fair process reducer = Reducer
variables 
    final = [w \in Workers |-> 0], 
    consumed = [w \in Workers |-> FALSE];
    assignments = [w \in Workers |-> <<>>];
begin
    Schedule:
        with worker_order = PT!OrderSet(Workers) do
            queue := [ w \in Workers |-> 
                LET offset == PT!Index(worker_order, w) - 1 \* sequences start at 1
                IN PT!SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) = 
                offset)
            ];
            assignments := queue;
        end with;
        with w \in {w \in ActiveWorkers: Cardinality(queue[w]) = 0} do
            status[w] := "inactive";
           
        end with;
        
    ReduceResult:
        while ActiveWorkers /= {} do
            either
                \* Reduce
                reduce();
            or
                \* Reassign
                with 
                    from_worker \in ActiveWorkers \ FairWorkers,
                    to_worker \in HealthyWorkers \ {from_worker} 
                    
                do
                    assignments[to_worker] :=
                        assignments[to_worker] \o
                        assignments[from_worker];
                    queue[to_worker] := 
                        queue[to_worker] \o
                        assignments[from_worker];
                    status[from_worker] := "broken" ||
                    status[to_worker] := "active";
                    final[to_worker] := 0;
                    
                    
                end with; 
            end either;
        end while;
    Finish:
        assert SumSeq(final) = SumSeq(input);
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
\* BEGIN TRANSLATION (chksum(pcal) = "9aad426e" /\ chksum(tla) = "76e250bf")
VARIABLES input, result, queue, status, pc, stack

(* define statement *)
ActiveWorkers == {w \in Workers: status[w] = "active"}
HealthyWorkers == {w \in Workers: status[w] /= "broken"}
TypeInvariant ==
    /\ status \in [Workers -> {"active", "inactive", "broken"}]
    /\ \A w \in Workers:
        /\ Len(queue[w]) <= ItemCount

        /\ \A item \in 1..Len(queue[w]):
            queue[w][item] \in ItemRange

        /\ \/ result[w].total = NULL
           \/ result[w].total <= SumSeq(input)
        /\ \/ result[w].count = NULL
           \/ result[w].count <= ItemCount

VARIABLES total, count, final, consumed, assignments

vars == << input, result, queue, status, pc, stack, total, count, final, 
           consumed, assignments >>

ProcSet == {Reducer} \cup (FairWorkers) \cup (UnfairWorkers)

Init == (* Global variables *)
        /\ input \in PossibleInputs
        /\ result = [w \in Workers |-> [total |-> NULL, count |-> NULL]]
        /\ queue = [w \in Workers |-> <<>>]
        /\ status = [w \in Workers |-> "active"]
        (* Procedure work *)
        /\ total = [ self \in ProcSet |-> 0]
        /\ count = [ self \in ProcSet |-> 0]
        (* Process reducer *)
        /\ final = [w \in Workers |-> 0]
        /\ consumed = [w \in Workers |-> FALSE]
        /\ assignments = [w \in Workers |-> <<>>]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = Reducer -> "Schedule"
                                        [] self \in FairWorkers -> "FairWorker"
                                        [] self \in UnfairWorkers -> "RegularWorker"]

WaitForQueue(self) == /\ pc[self] = "WaitForQueue"
                      /\ queue[self] /= <<>>
                      /\ pc' = [pc EXCEPT ![self] = "Process"]
                      /\ UNCHANGED << input, result, queue, status, stack, 
                                      total, count, final, consumed, 
                                      assignments >>

Process(self) == /\ pc[self] = "Process"
                 /\ IF queue[self] /= <<>>
                       THEN /\ total' = [total EXCEPT ![self] = total[self] + Head(queue[self])]
                            /\ queue' = [queue EXCEPT ![self] = Tail(queue[self])]
                            /\ count' = [count EXCEPT ![self] = count[self] + 1]
                            /\ pc' = [pc EXCEPT ![self] = "Process"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Result"]
                            /\ UNCHANGED << queue, total, count >>
                 /\ UNCHANGED << input, result, status, stack, final, consumed, 
                                 assignments >>

Result(self) == /\ pc[self] = "Result"
                /\ result' = [result EXCEPT ![self] = [total |-> total[self], count |-> count[self]]]
                /\ pc' = [pc EXCEPT ![self] = "WaitForQueue"]
                /\ UNCHANGED << input, queue, status, stack, total, count, 
                                final, consumed, assignments >>

work(self) == WaitForQueue(self) \/ Process(self) \/ Result(self)

Schedule == /\ pc[Reducer] = "Schedule"
            /\ LET worker_order == PT!OrderSet(Workers) IN
                 /\ queue' =          [ w \in Workers |->
                                 LET offset == PT!Index(worker_order, w) - 1
                                 IN PT!SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) =
                                 offset)
                             ]
                 /\ assignments' = queue'
            /\ \E w \in {w \in ActiveWorkers: Cardinality(queue'[w]) = 0}:
                 status' = [status EXCEPT ![w] = "inactive"]
            /\ pc' = [pc EXCEPT ![Reducer] = "ReduceResult"]
            /\ UNCHANGED << input, result, stack, total, count, final, 
                            consumed >>

ReduceResult == /\ pc[Reducer] = "ReduceResult"
                /\ IF ActiveWorkers /= {}
                      THEN /\ \/ /\ \E w \in     {w \in ActiveWorkers:
                                             result[w].count = Len(assignments[w])}:
                                      /\ final' = [final EXCEPT ![w] = result[w].total]
                                      /\ status' = [status EXCEPT ![w] = "inactive"]
                                 /\ UNCHANGED <<queue, assignments>>
                              \/ /\ \E from_worker \in ActiveWorkers \ FairWorkers:
                                      \E to_worker \in HealthyWorkers \ {from_worker}:
                                        /\ assignments' = [assignments EXCEPT ![to_worker] = assignments[to_worker] \o
                                                                                             assignments[from_worker]]
                                        /\ queue' = [queue EXCEPT ![to_worker] = queue[to_worker] \o
                                                                                 assignments'[from_worker]]
                                        /\ status' = [status EXCEPT ![from_worker] = "broken",
                                                                    ![to_worker] = "active"]
                                        /\ final' = [final EXCEPT ![to_worker] = 0]
                           /\ pc' = [pc EXCEPT ![Reducer] = "ReduceResult"]
                      ELSE /\ pc' = [pc EXCEPT ![Reducer] = "Finish"]
                           /\ UNCHANGED << queue, status, final, assignments >>
                /\ UNCHANGED << input, result, stack, total, count, consumed >>

Finish == /\ pc[Reducer] = "Finish"
          /\ Assert(SumSeq(final) = SumSeq(input), 
                    "Failure of assertion at line 120, column 9.")
          /\ pc' = [pc EXCEPT ![Reducer] = "Done"]
          /\ UNCHANGED << input, result, queue, status, stack, total, count, 
                          final, consumed, assignments >>

reducer == Schedule \/ ReduceResult \/ Finish

FairWorker(self) == /\ pc[self] = "FairWorker"
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "work",
                                                             pc        |->  "Done",
                                                             total     |->  total[self],
                                                             count     |->  count[self] ] >>
                                                         \o stack[self]]
                    /\ total' = [total EXCEPT ![self] = 0]
                    /\ count' = [count EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "WaitForQueue"]
                    /\ UNCHANGED << input, result, queue, status, final, 
                                    consumed, assignments >>

fair_workers(self) == FairWorker(self)

RegularWorker(self) == /\ pc[self] = "RegularWorker"
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "work",
                                                                pc        |->  "Done",
                                                                total     |->  total[self],
                                                                count     |->  count[self] ] >>
                                                            \o stack[self]]
                       /\ total' = [total EXCEPT ![self] = 0]
                       /\ count' = [count EXCEPT ![self] = 0]
                       /\ pc' = [pc EXCEPT ![self] = "WaitForQueue"]
                       /\ UNCHANGED << input, result, queue, status, final, 
                                       consumed, assignments >>

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


Liveness == <>[](SumSeq(final) = SumSeq(input))

ReducerTerminates == <>(pc[Reducer] = "Finish")

=============================================================================
\* Modification History
\* Last modified Sat Nov 26 17:59:11 CST 2022 by wengjialin
\* Created Tue Nov 22 22:17:01 CST 2022 by wengjialin
