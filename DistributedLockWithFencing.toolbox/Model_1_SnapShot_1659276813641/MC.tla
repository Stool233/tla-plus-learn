---- MODULE MC ----
EXTENDS DistributedLockWithFencing, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_165927681162014000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_165927681162115000 ==
[](TypeOK /\ Consistent2)
----
=============================================================================
\* Modification History
\* Created Sun Jul 31 22:13:31 CST 2022 by wengjialin
