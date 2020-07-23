---- MODULE MC ----
EXTENDS mainll, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Nodes
const_15954994142888000 == 
{a, b, c}
----

\* Constant expression definition @modelExpressionEval
const_expr_15954994142889000 == 
Valid
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_15954994142889000>>)
----

=============================================================================
\* Modification History
\* Created Thu Jul 23 20:16:54 AEST 2020 by douglas
