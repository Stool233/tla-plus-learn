---- MODULE MC ----
EXTENDS knapsack, TLC

\* Constant expression definition @modelExpressionEval
const_expr_166039833767714000 == 
KnapsackValue([a |-> 1, b |-> 3, c |-> 0], HardcodedItemSet)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_166039833767714000>>)
----

=============================================================================
\* Modification History
\* Created Sat Aug 13 21:45:37 CST 2022 by wengjialin
