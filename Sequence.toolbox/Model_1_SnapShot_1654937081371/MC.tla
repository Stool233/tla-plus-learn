---- MODULE MC ----
EXTENDS Sequence, TLC

\* Constant expression definition @modelExpressionEval
const_expr_165493707922180000 == 
Remove(3, <<1, 2, 3, 4>>)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_165493707922180000>>)
----

=============================================================================
\* Modification History
\* Created Sat Jun 11 16:44:39 CST 2022 by wengjialin
