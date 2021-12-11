---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2
----

\* MV CONSTANT definitions Workers
const_163921096675537000 == 
{w1, w2}
----

\* INIT definition @modelBehaviorNoSpec:0
init_163921096675538000 ==
FALSE/\final = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_163921096675539000 ==
FALSE/\final' = final
----
=============================================================================
\* Modification History
\* Created Sat Dec 11 19:22:46 AEDT 2021 by douglas
