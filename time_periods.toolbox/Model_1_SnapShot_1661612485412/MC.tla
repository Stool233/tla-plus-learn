---- MODULE MC ----
EXTENDS time_periods, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT definitions Actors
const_166161248137736000 == 
{a1, a2}
----

\* CONSTANT definitions @modelParameterConstants:0ResourceCap
const_166161248137837000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:1MaxConsumerReq
const_166161248137838000 == 
2
----

=============================================================================
\* Modification History
\* Created Sat Aug 27 23:01:21 CST 2022 by wengjialin
