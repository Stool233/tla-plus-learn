---- MODULE MC ----
EXTENDS time_periods, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT definitions Actors
const_166161919528460000 == 
{a1, a2}
----

\* CONSTANT definitions @modelParameterConstants:0ResourceCap
const_166161919528461000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:1MaxConsumerReq
const_166161919528462000 == 
2
----

=============================================================================
\* Modification History
\* Created Sun Aug 28 00:53:15 CST 2022 by wengjialin
