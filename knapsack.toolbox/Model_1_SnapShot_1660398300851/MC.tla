---- MODULE MC ----
EXTENDS knapsack, TLC

\* Constant expression definition @modelExpressionEval
const_expr_166039829882312000 == 
BestKnapsack(HardcodedItemSet)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_166039829882312000>>)
----

=============================================================================
\* Modification History
\* Created Sat Aug 13 21:44:58 CST 2022 by wengjialin
