---- MODULE MC ----
EXTENDS MapReduce3, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2
----

\* MV CONSTANT definitions Workers
const_166912619823627000 == 
{w1, w2}
----

\* CONSTANT definitions @modelParameterConstants:3ItemCount
const_166912619823628000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:4ItemRange
const_166912619823629000 == 
0..2
----

=============================================================================
\* Modification History
\* Created Tue Nov 22 22:09:58 CST 2022 by wengjialin
