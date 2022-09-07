---- MODULE MC ----
EXTENDS time_periods, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT definitions Actors
const_166161129684732000 == 
{a1, a2}
----

\* CONSTANT definitions @modelParameterConstants:0ResourceCap
const_166161129684733000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:1MaxConsumerReq
const_166161129684734000 == 
2
----

=============================================================================
\* Modification History
\* Created Sat Aug 27 22:41:36 CST 2022 by wengjialin
