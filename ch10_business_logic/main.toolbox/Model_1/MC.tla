---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
b1, b2
----

\* MV CONSTANT definitions People
const_16389616415942000 == 
{p1}
----

\* MV CONSTANT definitions Books
const_16389616415943000 == 
{b1, b2}
----

\* CONSTANT definitions @modelParameterConstants:0NumCopies
const_16389616415944000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Wed Dec 08 22:07:21 AEDT 2021 by douglas
