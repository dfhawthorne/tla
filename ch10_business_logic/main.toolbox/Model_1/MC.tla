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
const_160033300805944000 == 
{p1}
----

\* MV CONSTANT definitions Books
const_160033300805945000 == 
{b1, b2}
----

\* CONSTANT definitions @modelParameterConstants:0NumCopies
const_160033300805946000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Thu Sep 17 18:56:48 AEST 2020 by douglas
