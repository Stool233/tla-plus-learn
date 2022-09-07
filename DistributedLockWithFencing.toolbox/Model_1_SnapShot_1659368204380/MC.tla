---- MODULE MC ----
EXTENDS DistributedLockWithFencing, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_165936820235618000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_165936820235619000 ==
[](TypeOK)
----
=============================================================================
\* Modification History
\* Created Mon Aug 01 23:36:42 CST 2022 by wengjialin
