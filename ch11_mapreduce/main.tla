-------------------------------- MODULE main --------------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets
PT == INSTANCE PT
CONSTANTS Workers, Reducer, NULL

PossibleInputs == PT!TupleOf(0..2, 4)
SumSeq(seq) == PT!ReduceSeq(LAMBDA x, y: x + y, seq, 0)
FairWorkers == CHOOSE set_w \in SUBSET Workers: Cardinality(set_w) = 1
UnFairWorkers == Workers \ FairWorkers

(*--algorithm mapreduce

variables
  input \in PossibleInputs,
  result = [w \in Workers |-> NULL],
  queue = [w \in Workers |-> <<>>]; \* remove hardcoding

macro reduce() begin
  with w \in {w \in Workers: result[w].count = Len(assignments[w]) /\ ~consumed[w]} do
    final[w]    := result[w].total;
    consumed[w] := TRUE;
  end with;
end macro;

\*
procedure work()
  variables total = 0, count = 0;
begin
  WaitForQueue:
    await queue[self] /= <<>>;
  Process:
    while queue[self] /= <<>> do
      total       := total + Head(queue[self]);
      queue[self] := Tail(queue[self]);
      count       := count + 1;
    end while;
  Result:
    result[self] := [ total |-> total, count |-> count ];
    goto WaitForQueue;
end procedure;

fair process reducer = Reducer
variables
  final       = [w \in Workers |-> 0],
  consumed    = [w \in Workers |-> FALSE],
  assignments = [w \in Workers |-> <<>>];
begin
  Schedule:
    with worker_order = PT!OrderSet(Workers) do
      queue := [ w \in Workers |->
        LET offset == PT!Index(worker_order, w) - 1 \* sequences start at 1
        IN PT!SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) = offset)
        ];
    end with;
  ReduceResult:
    while \E w \in Workers: ~consumed[w] do
      either
        \* Reduce
        reduce();
      or
        \* Reassign
        with from_worker \in {w \in UnFairWorkers:
            result[w].count /= Len(assignments[w]) /\ ~consumed[w] },
          to_worker \in FairWorkers do
            assignments[to_worker] := assignments[to_worker] \o assignments[from_worker];
            queue[to_worker]       := queue[to_worker]       \o assignments[from_worker];
            consumed[from_worker]  := TRUE ||
            consumed[to_worker]    := FALSE;
            final[to_worker]        := 0;
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

process worker \in UnFairWorkers
begin RegularWorker:
  call work();
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ae072ce8" /\ chksum(tla) = "796bc7ca")
VARIABLES input, result, queue, pc, stack, total, count, final, consumed, 
          assignments

vars == << input, result, queue, pc, stack, total, count, final, consumed, 
           assignments >>

ProcSet == {Reducer} \cup (FairWorkers) \cup (UnFairWorkers)

Init == (* Global variables *)
        /\ input \in PossibleInputs
        /\ result = [w \in Workers |-> NULL]
        /\ queue = [w \in Workers |-> <<>>]
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
                                        [] self \in UnFairWorkers -> "RegularWorker"]

WaitForQueue(self) == /\ pc[self] = "WaitForQueue"
                      /\ queue[self] /= <<>>
                      /\ pc' = [pc EXCEPT ![self] = "Process"]
                      /\ UNCHANGED << input, result, queue, stack, total, 
                                      count, final, consumed, assignments >>

Process(self) == /\ pc[self] = "Process"
                 /\ IF queue[self] /= <<>>
                       THEN /\ total' = [total EXCEPT ![self] = total[self] + Head(queue[self])]
                            /\ queue' = [queue EXCEPT ![self] = Tail(queue[self])]
                            /\ count' = [count EXCEPT ![self] = count[self] + 1]
                            /\ pc' = [pc EXCEPT ![self] = "Process"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Result"]
                            /\ UNCHANGED << queue, total, count >>
                 /\ UNCHANGED << input, result, stack, final, consumed, 
                                 assignments >>

Result(self) == /\ pc[self] = "Result"
                /\ result' = [result EXCEPT ![self] = [ total |-> total[self], count |-> count[self] ]]
                /\ pc' = [pc EXCEPT ![self] = "WaitForQueue"]
                /\ UNCHANGED << input, queue, stack, total, count, final, 
                                consumed, assignments >>

work(self) == WaitForQueue(self) \/ Process(self) \/ Result(self)

Schedule == /\ pc[Reducer] = "Schedule"
            /\ LET worker_order == PT!OrderSet(Workers) IN
                 queue' =        [ w \in Workers |->
                          LET offset == PT!Index(worker_order, w) - 1
                          IN PT!SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) = offset)
                          ]
            /\ pc' = [pc EXCEPT ![Reducer] = "ReduceResult"]
            /\ UNCHANGED << input, result, stack, total, count, final, 
                            consumed, assignments >>

ReduceResult == /\ pc[Reducer] = "ReduceResult"
                /\ IF \E w \in Workers: ~consumed[w]
                      THEN /\ \/ /\ \E w \in {w \in Workers: result[w].count = Len(assignments[w]) /\ ~consumed[w]}:
                                      /\ final' = [final EXCEPT ![w] = result[w].total]
                                      /\ consumed' = [consumed EXCEPT ![w] = TRUE]
                                 /\ UNCHANGED <<queue, assignments>>
                              \/ /\ \E from_worker \in                  {w \in UnFairWorkers:
                                                       result[w].count /= Len(assignments[w]) /\ ~consumed[w] }:
                                      \E to_worker \in FairWorkers:
                                        /\ assignments' = [assignments EXCEPT ![to_worker] = assignments[to_worker] \o assignments[from_worker]]
                                        /\ queue' = [queue EXCEPT ![to_worker] = queue[to_worker]       \o assignments'[from_worker]]
                                        /\ consumed' = [consumed EXCEPT ![from_worker] = TRUE,
                                                                        ![to_worker] = FALSE]
                                        /\ final' = [final EXCEPT ![to_worker] = 0]
                           /\ pc' = [pc EXCEPT ![Reducer] = "ReduceResult"]
                      ELSE /\ pc' = [pc EXCEPT ![Reducer] = "Finish"]
                           /\ UNCHANGED << queue, final, consumed, assignments >>
                /\ UNCHANGED << input, result, stack, total, count >>

Finish == /\ pc[Reducer] = "Finish"
          /\ Assert(SumSeq(final) = SumSeq(input), 
                    "Failure of assertion at line 75, column 5.")
          /\ pc' = [pc EXCEPT ![Reducer] = "Done"]
          /\ UNCHANGED << input, result, queue, stack, total, count, final, 
                          consumed, assignments >>

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
                    /\ UNCHANGED << input, result, queue, final, consumed, 
                                    assignments >>

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
                       /\ UNCHANGED << input, result, queue, final, consumed, 
                                       assignments >>

worker(self) == RegularWorker(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == reducer
           \/ (\E self \in ProcSet: work(self))
           \/ (\E self \in FairWorkers: fair_workers(self))
           \/ (\E self \in UnFairWorkers: worker(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(reducer)
        /\ \A self \in FairWorkers : WF_vars(fair_workers(self)) /\ WF_vars(work(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
liveness == <>[](SumSeq(final) = SumSeq(input))
=============================================================================
\* Modification History
\* Last modified Sat Dec 18 20:15:04 AEDT 2021 by douglas
\* Created Wed Dec 08 22:44:35 AEDT 2021 by douglas
