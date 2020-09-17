-------------------------------- MODULE main --------------------------------
EXTENDS Integers, TLC, Sequences
CONSTANTS Books, People, NumCopies
ASSUME NumCopies \subseteq Nat
PT == INSTANCE PT

(*--algorithm library
variables
  library \in [Books -> NumCopies],
  reserves = [b \in Books |-> <<>>];
  
define
  AvailableBooks == {b \in Books: library[b] > 0}
  BorrowableBooks(p) == {b \in AvailableBooks: reserves[b] = <<>> \/ p = Head(reserves[b])}
  set ++ x == set \union {x}
  set -- x == set \ {x}
end define;
  
fair process person \in People
variables
  books = {},
  wants \in SUBSET Books;
begin
  Person:
    either
      \* Checkout
      with b \in BorrowableBooks(self) \ books do
        library[b] := library[b] - 1;
        books := books ++ b;
        wants := wants -- b;
        if reserves[b] /= <<>> /\ self = Head(reserves[b]) then
          reserves[b] := Tail(reserves[b]);
        end if;
      end with;
    or
      \* Return
      with b \in AvailableBooks \ books do
        library[b] := library[b] + 1;
        books := books -- b;
      end with;
    or
      \* Reserve
      with b \in {b \in Books: self \notin PT!Range(reserves[b])} do
        reserves[b] := Append(reserves[b], self);
      end with;
    end either;
  goto Person;
end process;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ccdba9e162674fe85c1a1531d2666196
VARIABLES library, reserves, pc

(* define statement *)
AvailableBooks == {b \in Books: library[b] > 0}
BorrowableBooks(p) == {b \in AvailableBooks: reserves[b] = <<>> \/ p = Head(reserves[b])}
set ++ x == set \union {x}
set -- x == set \ {x}

VARIABLES books, wants

vars == << library, reserves, pc, books, wants >>

ProcSet == (People)

Init == (* Global variables *)
        /\ library \in [Books -> NumCopies]
        /\ reserves = [b \in Books |-> <<>>]
        (* Process person *)
        /\ books = [self \in People |-> {}]
        /\ wants \in [People -> SUBSET Books]
        /\ pc = [self \in ProcSet |-> "Person"]

Person(self) == /\ pc[self] = "Person"
                /\ \/ /\ \E b \in BorrowableBooks(self) \ books[self]:
                           /\ library' = [library EXCEPT ![b] = library[b] - 1]
                           /\ books' = [books EXCEPT ![self] = books[self] ++ b]
                           /\ wants' = [wants EXCEPT ![self] = wants[self] -- b]
                           /\ IF reserves[b] /= <<>> /\ self = Head(reserves[b])
                                 THEN /\ reserves' = [reserves EXCEPT ![b] = Tail(reserves[b])]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED reserves
                   \/ /\ \E b \in AvailableBooks \ books[self]:
                           /\ library' = [library EXCEPT ![b] = library[b] + 1]
                           /\ books' = [books EXCEPT ![self] = books[self] -- b]
                      /\ UNCHANGED <<reserves, wants>>
                   \/ /\ \E b \in {b \in Books: self \notin PT!Range(reserves[b])}:
                           reserves' = [reserves EXCEPT ![b] = Append(reserves[b], self)]
                      /\ UNCHANGED <<library, books, wants>>
                /\ pc' = [pc EXCEPT ![self] = "Person"]

person(self) == Person(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in People: person(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in People : WF_vars(person(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a023856be9bc41bef712d1599df1089f

NoDuplicateReservations ==
  \A b \in Books:
    \A i, j \in 1..Len(reserves[b]):
      i /= j => reserves[b][i] /= reserves[b][j]

TypeInvariant ==
  /\ library \in [Books -> NumCopies ++ 0]
  /\ books \in [People -> SUBSET Books]
  /\ wants \in [People -> SUBSET Books]
  /\ reserves \in [Books -> Seq(People)]
  /\ NoDuplicateReservations
  
Liveness ==
  /\ <>(\A p \in People: wants[p] = {})

=============================================================================
\* Modification History
\* Last modified Thu Sep 17 18:56:01 AEST 2020 by douglas
\* Created Thu Sep 17 17:56:38 AEST 2020 by douglas
