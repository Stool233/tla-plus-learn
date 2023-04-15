---- MODULE MC ----
EXTENDS MapReduce4, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2, w3
----

\* MV CONSTANT definitions Workers
const_166912722021183000 == 
{w1, w2, w3}
----

\* CONSTANT definitions @modelParameterConstants:0ItemCount
const_166912722021184000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1ItemRange
const_166912722021185000 == 
0..2
----

=============================================================================
\* Modification History
\* Created Tue Nov 22 22:27:00 CST 2022 by wengjialin
