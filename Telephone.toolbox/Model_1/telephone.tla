----------------------------- MODULE telephone -----------------------------

EXTENDS Sequences, TLC

=============================================================================
\* Modification History
\* Last modified Sat Mar 16 18:09:26 AEDT 2019 by douglas
\* Created Sat Mar 16 17:55:47 AEDT 2019 by douglas

(*--algorithm telephone
variables
  to_send = <<1, 2, 3>>,
  received = <<>>,
  in_transit = {};
begin
  while Len(received) /= 3 do
    \* send
    if in_send /= <<>> then
      in_transit := in_transit \union {Head(to_send)};
      to_send    := Tail(to_send);
    end if;
    \* receive
    either
      with msg \in in_transit do
        received   := Append(received, msg);
        in_transit := in_transit \ {msg};
      end with;
    or
      skip;
    end either;
  end while;
  assert recieved = <<1, 2, 3>>;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES to_send, received, in_transit, pc

vars == << to_send, received, in_transit, pc >>

Init == (* Global variables *)
        /\ to_send = <<1, 2, 3>>
        /\ received = <<>>
        /\ in_transit = {}
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(received) /= 3
               THEN /\ IF in_send /= <<>>
                          THEN /\ in_transit' = (in_transit \union {Head(to_send)})
                               /\ to_send' = Tail(to_send)
                          ELSE /\ TRUE
                               /\ UNCHANGED << to_send, in_transit >>
                    /\ \/ /\ pc' = "Lbl_2"
                       \/ /\ TRUE
                          /\ pc' = "Lbl_1"
               ELSE /\ Assert(recieved = <<1, 2, 3>>, 
                              "Failure of assertion at line 32, column 3.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << to_send, in_transit >>
         /\ UNCHANGED received

Lbl_2 == /\ pc = "Lbl_2"
         /\ \E msg \in in_transit:
              /\ received' = Append(received, msg)
              /\ in_transit' = in_transit \ {msg}
         /\ pc' = "Lbl_1"
         /\ UNCHANGED to_send

Next == Lbl_1 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
