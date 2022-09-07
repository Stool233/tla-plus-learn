---- MODULE MC ----
EXTENDS time_periods, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT definitions Actors
const_166161912246752000 == 
{a1, a2}
----

\* CONSTANT definitions @modelParameterConstants:0ResourceCap
const_166161912246753000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:1MaxConsumerReq
const_166161912246754000 == 
2
----

=============================================================================
\* Modification History
\* Created Sun Aug 28 00:52:02 CST 2022 by wengjialin
