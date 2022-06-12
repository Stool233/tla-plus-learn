---- MODULE MC ----
EXTENDS ABSpec, TLC

\* CONSTANT definitions @modelParameterConstants:0Data
const_1654940951112100000 == 
{"a", "b", "c"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1654940951112103000 ==
\A v \in Data \X {0, 1} : (AVar = v) ~> (BVar = v)
----
=============================================================================
\* Modification History
\* Created Sat Jun 11 17:49:11 CST 2022 by wengjialin
