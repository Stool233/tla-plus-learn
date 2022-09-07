---- MODULE MC ----
EXTENDS DistributedLockWithFencing, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_165927732175216000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_165927732175217000 ==
[](TypeOK /\ Consistent2)
----
=============================================================================
\* Modification History
\* Created Sun Jul 31 22:22:01 CST 2022 by wengjialin
