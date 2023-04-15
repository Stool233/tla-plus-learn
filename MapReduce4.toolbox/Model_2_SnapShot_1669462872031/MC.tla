---- MODULE MC ----
EXTENDS MapReduce4, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2, w3
----

\* MV CONSTANT definitions Workers
const_1669462867980149000 == 
{w1, w2, w3}
----

\* CONSTANT definitions @modelParameterConstants:0ItemCount
const_1669462867980150000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1ItemRange
const_1669462867980151000 == 
0..2
----

=============================================================================
\* Modification History
\* Created Sat Nov 26 19:41:07 CST 2022 by wengjialin
