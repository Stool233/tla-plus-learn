---- MODULE MC ----
EXTENDS MapReduce4, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2, w3
----

\* MV CONSTANT definitions Workers
const_1669456812821101000 == 
{w1, w2, w3}
----

\* CONSTANT definitions @modelParameterConstants:0ItemCount
const_1669456812823102000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1ItemRange
const_1669456812823103000 == 
0..2
----

=============================================================================
\* Modification History
\* Created Sat Nov 26 18:00:12 CST 2022 by wengjialin
