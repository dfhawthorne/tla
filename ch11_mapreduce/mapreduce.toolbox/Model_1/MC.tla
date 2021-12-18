---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2
----

\* MV CONSTANT definitions Workers
const_16398189441122000 == 
{w1, w2}
----

\* INIT definition @modelBehaviorNoSpec:0
init_16398189441123000 ==
FALSE/\final = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_16398189441124000 ==
FALSE/\final' = final
----
=============================================================================
\* Modification History
\* Created Sat Dec 18 20:15:44 AEDT 2021 by douglas
