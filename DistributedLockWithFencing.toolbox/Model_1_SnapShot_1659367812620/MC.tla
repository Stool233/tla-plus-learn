---- MODULE MC ----
EXTENDS DistributedLockWithFencing, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_165936780959714000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_165936780959715000 ==
[](TypeOK)
----
=============================================================================
\* Modification History
\* Created Mon Aug 01 23:30:09 CST 2022 by wengjialin
