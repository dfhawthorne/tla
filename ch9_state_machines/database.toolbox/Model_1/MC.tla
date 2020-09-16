---- MODULE MC ----
EXTENDS database, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2
----

\* MV CONSTANT definitions Clients
const_160024912729524000 == 
{c1, c2}
----

\* MV CONSTANT definitions Data
const_160024912729525000 == 
{d1, d2}
----

=============================================================================
\* Modification History
\* Created Wed Sep 16 19:38:47 AEST 2020 by douglas
