---- MODULE MC ----
EXTENDS knapsack, TLC

\* Constant expression definition @modelExpressionEval
const_expr_166039839034616000 == 
{BestKnapsack(itemset) : itemset \in ItemSets}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_166039839034616000>>)
----

=============================================================================
\* Modification History
\* Created Sat Aug 13 21:46:30 CST 2022 by wengjialin
