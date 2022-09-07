---- MODULE MC ----
EXTENDS BrokenDistributedLock2, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_165824134611718000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_165824134611719000 ==
[](TypeOK)
----
=============================================================================
\* Modification History
\* Created Tue Jul 19 22:35:46 CST 2022 by wengjialin
