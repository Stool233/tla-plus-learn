---- MODULE MC ----
EXTENDS time_periods, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT definitions Actors
const_166161854761440000 == 
{a1, a2}
----

\* CONSTANT definitions @modelParameterConstants:0ResourceCap
const_166161854761441000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:1MaxConsumerReq
const_166161854761442000 == 
2
----

=============================================================================
\* Modification History
\* Created Sun Aug 28 00:42:27 CST 2022 by wengjialin
