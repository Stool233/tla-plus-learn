---- MODULE MC ----
EXTENDS MapReduce4, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2, w3
----

\* MV CONSTANT definitions Workers
const_1669462855610143000 == 
{w1, w2, w3}
----

\* CONSTANT definitions @modelParameterConstants:0ItemCount
const_1669462855610144000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1ItemRange
const_1669462855610145000 == 
0..2
----

=============================================================================
\* Modification History
\* Created Sat Nov 26 19:40:55 CST 2022 by wengjialin
