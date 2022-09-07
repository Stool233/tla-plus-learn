---- MODULE MC ----
EXTENDS BrokenDistributedLock, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_16580696261366000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_16580696261367000 ==
[](TypeOK)
----
=============================================================================
\* Modification History
\* Created Sun Jul 17 22:53:46 CST 2022 by wengjialin
