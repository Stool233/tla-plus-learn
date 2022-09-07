---- MODULE MC ----
EXTENDS BrokenDistributedLock2, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_165824551230938000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_165824551230939000 ==
[](TypeOK /\ Consistent2)
----
=============================================================================
\* Modification History
\* Created Tue Jul 19 23:45:12 CST 2022 by wengjialin
