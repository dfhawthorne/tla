---- MODULE MC ----
EXTENDS wire, TLC

\* Constant expression definition @modelExpressionEval
const_expr_15463291564706000 == 
1 + 2
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_15463291564706000>>)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15463291564707000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15463291564708000 ==
NoOverdrafts
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_15463291564709000 ==
EventuallyConsistent
----
=============================================================================
\* Modification History
\* Created Tue Jan 01 18:52:36 AEDT 2019 by douglas
