---- MODULE MC ----
EXTENDS MapReduce3, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2
----

\* MV CONSTANT definitions Workers
const_166912609482312000 == 
{w1, w2}
----

\* CONSTANT definitions @modelParameterConstants:3ItemCount
const_166912609482313000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:4ItemRange
const_166912609482314000 == 
0..2
----

=============================================================================
\* Modification History
\* Created Tue Nov 22 22:08:14 CST 2022 by wengjialin
