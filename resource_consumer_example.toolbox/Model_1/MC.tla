---- MODULE MC ----
EXTENDS resource_consumer_example, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT definitions Actors
const_159273958772514000 == 
{a1, a2}
----

\* SYMMETRY definition
symm_159273958772515000 == 
Permutations(const_159273958772514000)
----

\* CONSTANT definitions @modelParameterConstants:0ResourceCap
const_159273958772516000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:1MaxConsumerReq
const_159273958772517000 == 
2
----

=============================================================================
\* Modification History
\* Created Sun Jun 21 21:39:47 AEST 2020 by douglas
