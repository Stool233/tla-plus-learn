---- MODULE MC ----
EXTENDS DistributedLockWithFencing, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_16593673273446000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_16593673273447000 ==
[](TypeOK)
----
=============================================================================
\* Modification History
\* Created Mon Aug 01 23:22:07 CST 2022 by wengjialin
