---- MODULE MC ----
EXTENDS knapsack, TLC

\* Constant expression definition @modelExpressionEval
const_expr_166040009940032000 == 
{BestKnapsacks(itemse) : itemse \in ItemSets}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_166040009940032000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_166040009940033000 ==
FALSE/\itemset = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_166040009940034000 ==
FALSE/\itemset' = itemset
----
=============================================================================
\* Modification History
\* Created Sat Aug 13 22:14:59 CST 2022 by wengjialin
