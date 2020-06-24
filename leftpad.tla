------------------------------ MODULE leftpad ------------------------------

EXTENDS Integers, Sequences, TLC

PT == INSTANCE PT

Leftpad(c, n, str) ==
  IF n < 0 THEN str ELSE
  LET
    outlength == PT!Max(Len(str), n)
    padlength ==
      CHOOSE padlength \in 0..n:
        padlength + Len(str) = outlength
  IN
    [x \in 1..padlength |-> c] \o str

Characters == {"a", "b", "c"}

(*--algorithm leftpad

variables
  in_c   \in Characters \union {" "},
  in_n   \in 0..6,
  in_str \in PT!SeqOf(Characters, 6),
  output;
begin
  Pre_Condition:
    assert in_n >= 0;
    output := in_str;
  Main_Process:
    while Len(output) < in_n do
      output := <<in_c>> \o output;
    end while;
  Post_Condition:
    assert output = Leftpad(in_c, in_n, in_str);
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e4c99850a9fbefa9c8f5cfab4bc70b48
CONSTANT defaultInitValue
VARIABLES in_c, in_n, in_str, output, pc

vars == << in_c, in_n, in_str, output, pc >>

Init == (* Global variables *)
        /\ in_c \in (Characters \union {" "})
        /\ in_n \in 0..6
        /\ in_str \in PT!SeqOf(Characters, 6)
        /\ output = defaultInitValue
        /\ pc = "Pre_Condition"

Pre_Condition == /\ pc = "Pre_Condition"
                 /\ Assert(in_n >= 0, 
                           "Failure of assertion at line 28, column 5.")
                 /\ output' = in_str
                 /\ pc' = "Main_Process"
                 /\ UNCHANGED << in_c, in_n, in_str >>

Main_Process == /\ pc = "Main_Process"
                /\ IF Len(output) < in_n
                      THEN /\ output' = <<in_c>> \o output
                           /\ pc' = "Main_Process"
                      ELSE /\ pc' = "Post_Condition"
                           /\ UNCHANGED output
                /\ UNCHANGED << in_c, in_n, in_str >>

Post_Condition == /\ pc = "Post_Condition"
                  /\ Assert(output = Leftpad(in_c, in_n, in_str), 
                            "Failure of assertion at line 35, column 5.")
                  /\ pc' = "Done"
                  /\ UNCHANGED << in_c, in_n, in_str, output >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Pre_Condition \/ Main_Process \/ Post_Condition
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-6ac2e3a7c34f35ff003cb77172f7be46
   

=============================================================================
\* Modification History
\* Last modified Wed Jun 24 20:32:21 AEST 2020 by douglas
\* Created Tue Jun 23 20:02:09 AEST 2020 by douglas
