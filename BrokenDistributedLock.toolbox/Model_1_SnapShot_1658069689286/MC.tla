---- MODULE MC ----
EXTENDS BrokenDistributedLock, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_165806968726210000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_165806968726211000 ==
[](TypeOK)
----
=============================================================================
\* Modification History
\* Created Sun Jul 17 22:54:47 CST 2022 by wengjialin
