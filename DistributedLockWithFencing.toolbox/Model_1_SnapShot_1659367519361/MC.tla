---- MODULE MC ----
EXTENDS DistributedLockWithFencing, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_165936751733810000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_165936751733811000 ==
[](TypeOK)
----
=============================================================================
\* Modification History
\* Created Mon Aug 01 23:25:17 CST 2022 by wengjialin
