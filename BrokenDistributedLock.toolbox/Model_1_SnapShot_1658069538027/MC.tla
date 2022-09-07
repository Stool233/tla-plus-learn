---- MODULE MC ----
EXTENDS BrokenDistributedLock, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_16580695336054000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_16580695336055000 ==
[](TypeOK)
----
=============================================================================
\* Modification History
\* Created Sun Jul 17 22:52:13 CST 2022 by wengjialin
