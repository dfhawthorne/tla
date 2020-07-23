------------------------------- MODULE mainll -------------------------------
EXTENDS TLC, Integers, FiniteSets, Sequences
CONSTANTS Nodes, NULL
INSTANCE LinkedLists WITH NULL <- NULL
AllLinkedLists == LinkedLists(Nodes)
CycleImpliesRingOrTwoParents(ll) ==
  Cyclic(ll) <=>
    \/ Ring(ll)
    \/ \E n \in DOMAIN ll:
      Cardinality({p \in DOMAIN ll: ll[p] = n}) = 2
Valid ==
  /\ \A ll \in AllLinkedLists:
    /\ Assert(CycleImpliesRingOrTwoParents(ll), <<"Counterexample:", ll>>)

=============================================================================
\* Modification History
\* Last modified Thu Jul 23 20:16:35 AEST 2020 by douglas
\* Created Thu Jul 23 19:51:52 AEST 2020 by douglas
