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
const_160032908295212000 == 
{c1, c2}
----

\* MV CONSTANT definitions Data
const_160032908295213000 == 
{d1, d2}
----

=============================================================================
\* Modification History
\* Created Thu Sep 17 17:51:22 AEST 2020 by douglas
