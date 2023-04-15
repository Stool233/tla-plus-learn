---- MODULE MC ----
EXTENDS MapReduce3, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2
----

\* MV CONSTANT definitions Workers
const_166912610343822000 == 
{w1, w2}
----

\* CONSTANT definitions @modelParameterConstants:3ItemCount
const_166912610343823000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:4ItemRange
const_166912610343824000 == 
0..2
----

=============================================================================
\* Modification History
\* Created Tue Nov 22 22:08:23 CST 2022 by wengjialin
