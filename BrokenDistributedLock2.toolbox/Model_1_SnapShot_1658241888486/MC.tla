---- MODULE MC ----
EXTENDS BrokenDistributedLock2, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_165824188546026000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_165824188546127000 ==
[](TypeOK /\ Consistent3)
----
=============================================================================
\* Modification History
\* Created Tue Jul 19 22:44:45 CST 2022 by wengjialin
