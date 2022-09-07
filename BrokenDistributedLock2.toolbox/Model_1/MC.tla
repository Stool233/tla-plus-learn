---- MODULE MC ----
EXTENDS BrokenDistributedLock2, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_165824553188942000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_165824553188943000 ==
[](TypeOK /\ Consistent3)
----
=============================================================================
\* Modification History
\* Created Tue Jul 19 23:45:31 CST 2022 by wengjialin
