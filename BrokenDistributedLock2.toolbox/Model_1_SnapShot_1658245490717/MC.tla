---- MODULE MC ----
EXTENDS BrokenDistributedLock2, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_165824548769634000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_165824548769635000 ==
[](TypeOK /\ Consistent)
----
=============================================================================
\* Modification History
\* Created Tue Jul 19 23:44:47 CST 2022 by wengjialin
