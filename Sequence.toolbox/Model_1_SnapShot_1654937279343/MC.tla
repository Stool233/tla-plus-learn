---- MODULE MC ----
EXTENDS Sequence, TLC

\* Constant expression definition @modelExpressionEval
const_expr_165493727832586000 == 
(1..3) \X {"a", "b"}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_165493727832586000>>)
----

=============================================================================
\* Modification History
\* Created Sat Jun 11 16:47:58 CST 2022 by wengjialin
