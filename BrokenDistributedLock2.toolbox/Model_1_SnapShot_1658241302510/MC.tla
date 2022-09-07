---- MODULE MC ----
EXTENDS BrokenDistributedLock2, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_165824130048216000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_165824130048217000 ==
[](TypeOK)
----
=============================================================================
\* Modification History
\* Created Tue Jul 19 22:35:00 CST 2022 by wengjialin
