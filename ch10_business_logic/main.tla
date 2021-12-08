-------------------------------- MODULE main --------------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANTS Books, People, NumCopies
ASSUME NumCopies \subseteq Nat
PT == INSTANCE PT

set ++ x == set \union {x}
set -- x == set \ {x}

(*--algorithm library
variables
  library \in [Books -> NumCopies],
  reserves = [b \in Books |-> <<>>];
  
define
  AvailableBooks == {b \in Books: library[b] > 0}
  BorrowableBooks(p) == 
    {b \in AvailableBooks: 
      \/ reserves[b] = <<>>
      \/ p = Head(reserves[b])}
end define;
  
fair process person \in People
variables
  books = {},
  wants \in SUBSET Books;
begin
  Person:
    while TRUE do
      either
        \* Checkout
        with b \in (BorrowableBooks(self) \intersect wants) \ books do
          library[b] := library[b] - 1;
          books := books ++ b;
          wants := wants -- b;
          if reserves[b] /= <<>> /\ self = Head(reserves[b]) then
            reserves[b] := Tail(reserves[b]);
          end if;
        end with;
      or
        \* Return
        with b \in books do
          library[b] := library[b] + 1;
          books := books -- b;
        end with;
      or
        \* Reserve
        with b \in {b \in Books: self \notin PT!Range(reserves[b])} do
          reserves[b] := Append(reserves[b], self);
        end with;
      or
        \* Want
        await wants = {};
        with b \in SUBSET books do
          wants := b;
        end with;
      end either;
    end while;
end process;

fair process book_reservation \in Books
begin
  Expire:
    await reserves[self] /= <<>>;
    reserves[self] := Tail(reserves[self]);
    goto Expire;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b22fe422" /\ chksum(tla) = "e45fdb73")
VARIABLES library, reserves, pc

(* define statement *)
AvailableBooks == {b \in Books: library[b] > 0}
BorrowableBooks(p) ==
  {b \in AvailableBooks:
    \/ reserves[b] = <<>>
    \/ p = Head(reserves[b])}

VARIABLES books, wants

vars == << library, reserves, pc, books, wants >>

ProcSet == (People) \cup (Books)

Init == (* Global variables *)
        /\ library \in [Books -> NumCopies]
        /\ reserves = [b \in Books |-> <<>>]
        (* Process person *)
        /\ books = [self \in People |-> {}]
        /\ wants \in [People -> SUBSET Books]
        /\ pc = [self \in ProcSet |-> CASE self \in People -> "Person"
                                        [] self \in Books -> "Expire"]

Person(self) == /\ pc[self] = "Person"
                /\ \/ /\ \E b \in (BorrowableBooks(self) \intersect wants[self]) \ books[self]:
                           /\ library' = [library EXCEPT ![b] = library[b] - 1]
                           /\ books' = [books EXCEPT ![self] = books[self] ++ b]
                           /\ wants' = [wants EXCEPT ![self] = wants[self] -- b]
                           /\ IF reserves[b] /= <<>> /\ self = Head(reserves[b])
                                 THEN /\ reserves' = [reserves EXCEPT ![b] = Tail(reserves[b])]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED reserves
                   \/ /\ \E b \in books[self]:
                           /\ library' = [library EXCEPT ![b] = library[b] + 1]
                           /\ books' = [books EXCEPT ![self] = books[self] -- b]
                      /\ UNCHANGED <<reserves, wants>>
                   \/ /\ \E b \in {b \in Books: self \notin PT!Range(reserves[b])}:
                           reserves' = [reserves EXCEPT ![b] = Append(reserves[b], self)]
                      /\ UNCHANGED <<library, books, wants>>
                   \/ /\ wants[self] = {}
                      /\ \E b \in SUBSET books[self]:
                           wants' = [wants EXCEPT ![self] = b]
                      /\ UNCHANGED <<library, reserves, books>>
                /\ pc' = [pc EXCEPT ![self] = "Person"]

person(self) == Person(self)

Expire(self) == /\ pc[self] = "Expire"
                /\ reserves[self] /= <<>>
                /\ reserves' = [reserves EXCEPT ![self] = Tail(reserves[self])]
                /\ pc' = [pc EXCEPT ![self] = "Expire"]
                /\ UNCHANGED << library, books, wants >>

book_reservation(self) == Expire(self)

Next == (\E self \in People: person(self))
           \/ (\E self \in Books: book_reservation(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in People : WF_vars(person(self))
        /\ \A self \in Books : WF_vars(book_reservation(self))

\* END TRANSLATION 

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
  
NextInLineFor(p, b) ==
  /\ reserves[b] /= <<>>
  /\ p = Head(reserves[b])
  
Liveness ==
  \A p \in People:
    \A b \in Books:
      b \in wants[p] ~>
        \/ b \notin wants[p]
        \/ NextInLineFor(p, b)
  
=============================================================================
\* Modification History
\* Last modified Wed Dec 08 22:06:12 AEDT 2021 by douglas
\* Created Thu Sep 17 17:56:38 AEST 2020 by douglas
