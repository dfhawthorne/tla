---------------------------- MODULE TortoiseHare ----------------------------
EXTENDS TLC

CONSTANTS Nodes, NULL
INSTANCE LinkedLists
(*--fair algorithm tortoise_and_hare
variables
  ll \in LinkedLists(Nodes),
  tortoise = First(ll),
  hare = tortoise;
macro advance(pointer) begin
  pointer := ll[pointer];
  if pointer = NULL then
    assert ~Cyclic(ll);
    goto Done;
  end if;
end macro;
begin
  while TRUE do
    advance(tortoise);
    advance(hare);
    advance(hare);
    if tortoise = hare then
      assert Cyclic(ll);
      goto Done;
    end if;
  end while;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-eb640a31be0af5cb418608119cbb21ab
VARIABLES ll, tortoise, hare, pc

vars == << ll, tortoise, hare, pc >>

Init == (* Global variables *)
        /\ ll \in LinkedLists(Nodes)
        /\ tortoise = First(ll)
        /\ hare = tortoise
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ tortoise' = ll[tortoise]
         /\ IF tortoise' = NULL
               THEN /\ Assert(~Cyclic(ll), 
                              "Failure of assertion at line 14, column 5 of macro called at line 20, column 5.")
                    /\ pc' = "Done"
               ELSE /\ pc' = "Lbl_2"
         /\ UNCHANGED << ll, hare >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ hare' = ll[hare]
         /\ IF hare' = NULL
               THEN /\ Assert(~Cyclic(ll), 
                              "Failure of assertion at line 14, column 5 of macro called at line 21, column 5.")
                    /\ pc' = "Done"
               ELSE /\ pc' = "Lbl_3"
         /\ UNCHANGED << ll, tortoise >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ hare' = ll[hare]
         /\ IF hare' = NULL
               THEN /\ Assert(~Cyclic(ll), 
                              "Failure of assertion at line 14, column 5 of macro called at line 22, column 5.")
                    /\ pc' = "Done"
               ELSE /\ pc' = "Lbl_4"
         /\ UNCHANGED << ll, tortoise >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ IF tortoise = hare
               THEN /\ Assert(Cyclic(ll), 
                              "Failure of assertion at line 24, column 7.")
                    /\ pc' = "Done"
               ELSE /\ pc' = "Lbl_1"
         /\ UNCHANGED << ll, tortoise, hare >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3d56ee45c57e8c2c841b7091bd424711

=============================================================================
\* Modification History
\* Last modified Wed Sep 16 16:07:10 AEST 2020 by douglas
\* Created Wed Sep 16 15:59:44 AEST 2020 by douglas
