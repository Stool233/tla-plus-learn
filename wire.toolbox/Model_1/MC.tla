---- MODULE MC ----
EXTENDS wire, TLC

\* Constant expression definition @modelExpressionEval
const_expr_165984023214515000 == 
1 + 2
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_165984023214515000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_165984023214516000 ==
FALSE/\people = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_165984023214517000 ==
FALSE/\people' = people
----
=============================================================================
\* Modification History
\* Created Sun Aug 07 10:43:52 CST 2022 by wengjialin
