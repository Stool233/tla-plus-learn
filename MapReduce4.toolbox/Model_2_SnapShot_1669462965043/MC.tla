---- MODULE MC ----
EXTENDS MapReduce4, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2, w3
----

\* MV CONSTANT definitions Workers
const_1669462909844155000 == 
{w1, w2, w3}
----

\* CONSTANT definitions @modelParameterConstants:0ItemCount
const_1669462909844156000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1ItemRange
const_1669462909844157000 == 
0..2
----

=============================================================================
\* Modification History
\* Created Sat Nov 26 19:41:49 CST 2022 by wengjialin
