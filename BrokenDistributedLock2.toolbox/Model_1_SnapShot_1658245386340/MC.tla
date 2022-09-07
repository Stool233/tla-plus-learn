---- MODULE MC ----
EXTENDS BrokenDistributedLock2, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_165824538231430000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_165824538231431000 ==
[](TypeOK /\ Consistent3)
----
=============================================================================
\* Modification History
\* Created Tue Jul 19 23:43:02 CST 2022 by wengjialin
