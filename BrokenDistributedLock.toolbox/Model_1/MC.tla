---- MODULE MC ----
EXTENDS BrokenDistributedLock, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_165806971139614000 == 
{"c1", "c2"}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_165806971139615000 ==
[](TypeOK /\ Consistent)
----
=============================================================================
\* Modification History
\* Created Sun Jul 17 22:55:11 CST 2022 by wengjialin
