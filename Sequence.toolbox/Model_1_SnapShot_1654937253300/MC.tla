---- MODULE MC ----
EXTENDS Sequence, TLC

\* Constant expression definition @modelExpressionEval
const_expr_165493725228184000 == 
1..3 \X {"a", "b"}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_165493725228184000>>)
----

=============================================================================
\* Modification History
\* Created Sat Jun 11 16:47:32 CST 2022 by wengjialin
