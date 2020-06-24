---------------------- MODULE definitely_binary_search ----------------------
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

(*--algorithm definitely_binary_search

variables
  i           =   1,
  seq         \in OrderedSeqOf(1..MaxInt, MaxInt),
  target      \in 1..MaxInt,
  found_index =   0,
  counter     =   0;

begin
  Search:
    while i <= Len(seq) do
    counter := counter + 1;
      if seq[i] = target then
        found_index := i;
        goto Result;
      else
        i := i + 1;
      end if;
    end while;
  Result:
    if Len(seq) > 0 then
      assert Pow2(counter-1) <= Len(seq);
    end if;
    if target \in Range(seq) then
      assert seq[found_index] = target;
    else
      \* 0 is out of DOMAIN seq, so can represent "not found"
      assert found_index = 0;
    end if;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-decfeee98c4c72410b0bd782048ade91
VARIABLES i, seq, target, found_index, counter, pc

vars == << i, seq, target, found_index, counter, pc >>

Init == (* Global variables *)
        /\ i = 1
        /\ seq \in OrderedSeqOf(1..MaxInt, MaxInt)
        /\ target \in 1..MaxInt
        /\ found_index = 0
        /\ counter = 0
        /\ pc = "Search"

Search == /\ pc = "Search"
          /\ IF i <= Len(seq)
                THEN /\ counter' = counter + 1
                     /\ IF seq[i] = target
                           THEN /\ found_index' = i
                                /\ pc' = "Result"
                                /\ i' = i
                           ELSE /\ i' = i + 1
                                /\ pc' = "Search"
                                /\ UNCHANGED found_index
                ELSE /\ pc' = "Result"
                     /\ UNCHANGED << i, found_index, counter >>
          /\ UNCHANGED << seq, target >>

Result == /\ pc = "Result"
          /\ IF Len(seq) > 0
                THEN /\ Assert(Pow2(counter-1) <= Len(seq), 
                               "Failure of assertion at line 44, column 7.")
                ELSE /\ TRUE
          /\ IF target \in Range(seq)
                THEN /\ Assert(seq[found_index] = target, 
                               "Failure of assertion at line 47, column 7.")
                ELSE /\ Assert(found_index = 0, 
                               "Failure of assertion at line 50, column 7.")
          /\ pc' = "Done"
          /\ UNCHANGED << i, seq, target, found_index, counter >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Search \/ Result
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-b8276ad2f3df65112d0046ef58543fdf

=============================================================================
\* Modification History
\* Last modified Wed Jun 24 21:18:12 AEST 2020 by douglas
\* Created Wed Jun 24 20:57:35 AEST 2020 by douglas
