--------------------------- MODULE binary_search ---------------------------
EXTENDS Integers, Sequences, TLC

PT == INSTANCE PT

OrderedSeqOf(set, n) ==
  { seq \in PT!SeqOf(set, n):
    \A x \in 2..Len(seq):
      seq[x] >= seq[x-1] }
      
MaxInt == 4

Range(f) == {f[x]: x \in DOMAIN f}

Pow2(n) ==
  LET f[x \in 0..n] ==
    IF x = 0
    THEN 1
    ELSE 2*f[x-1]
  IN f[n]

(*--algorithm binary_search

variables
  low         =   1,
  seq         \in OrderedSeqOf(1..MaxInt, MaxInt),
  high        = Len(seq),
  target      \in 1..MaxInt,
  found_index =   0,
  counter     =   0;

begin
Search:
  while low <= high do
    counter := counter + 1;
    with
      m = (high + low) \div 2
      do
        if seq[m] = target then
          found_index := m;
          goto Result;
        elsif seq[m] < target then
          low  := m + 1;
        else
          high := m - 1;
        end if;
    end with;
  end while;
  
Result:
  if Len(seq) > 0 then
    assert Pow2(counter-1) <= Len(seq);
  end if;
  if target \in Range(seq) then
    assert seq[found_index] = target;
  else
    assert found_index      = 0;
  end if;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-c6d83c6df2806de3b947a6054a524c1f
VARIABLES low, seq, high, target, found_index, counter, pc

vars == << low, seq, high, target, found_index, counter, pc >>

Init == (* Global variables *)
        /\ low = 1
        /\ seq \in OrderedSeqOf(1..MaxInt, MaxInt)
        /\ high = Len(seq)
        /\ target \in 1..MaxInt
        /\ found_index = 0
        /\ counter = 0
        /\ pc = "Search"

Search == /\ pc = "Search"
          /\ IF low <= high
                THEN /\ counter' = counter + 1
                     /\ LET m == (high + low) \div 2 IN
                          IF seq[m] = target
                             THEN /\ found_index' = m
                                  /\ pc' = "Result"
                                  /\ UNCHANGED << low, high >>
                             ELSE /\ IF seq[m] < target
                                        THEN /\ low' = m + 1
                                             /\ high' = high
                                        ELSE /\ high' = m - 1
                                             /\ low' = low
                                  /\ pc' = "Search"
                                  /\ UNCHANGED found_index
                ELSE /\ pc' = "Result"
                     /\ UNCHANGED << low, high, found_index, counter >>
          /\ UNCHANGED << seq, target >>

Result == /\ pc = "Result"
          /\ IF Len(seq) > 0
                THEN /\ Assert(Pow2(counter-1) <= Len(seq), 
                               "Failure of assertion at line 52, column 5.")
                ELSE /\ TRUE
          /\ IF target \in Range(seq)
                THEN /\ Assert(seq[found_index] = target, 
                               "Failure of assertion at line 55, column 5.")
                ELSE /\ Assert(found_index      = 0, 
                               "Failure of assertion at line 57, column 5.")
          /\ pc' = "Done"
          /\ UNCHANGED << low, seq, high, target, found_index, counter >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Search \/ Result
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-b23f904d02ba1340635eae0c4c31dee1


=============================================================================
\* Modification History
\* Last modified Fri Jul 03 21:33:23 AEST 2020 by douglas
\* Created Fri Jul 03 21:25:43 AEST 2020 by douglas
