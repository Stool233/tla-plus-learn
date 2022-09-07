---- MODULE MC ----
EXTENDS BrokenDistributedLock2, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_165824167524424000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_165824167524425000 ==
[](TypeOK /\ Consistent3)
----
=============================================================================
\* Modification History
\* Created Tue Jul 19 22:41:15 CST 2022 by wengjialin
