---- MODULE MC ----
EXTENDS main, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2
----

\* MV CONSTANT definitions Workers
const_163982803537532000 == 
{w1, w2}
----

\* CONSTANT definitions @modelParameterConstants:3ItemCount
const_163982803537533000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:4ItemRange
const_163982803537534000 == 
0..2
----

\* INIT definition @modelBehaviorNoSpec:0
init_163982803537635000 ==
FALSE/\final = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_163982803537636000 ==
FALSE/\final' = final
----
=============================================================================
\* Modification History
\* Created Sat Dec 18 22:47:15 AEDT 2021 by douglas
