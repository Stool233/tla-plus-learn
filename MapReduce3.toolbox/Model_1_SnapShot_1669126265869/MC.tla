---- MODULE MC ----
EXTENDS MapReduce3, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2, w3
----

\* MV CONSTANT definitions Workers
const_166912621872337000 == 
{w1, w2, w3}
----

\* CONSTANT definitions @modelParameterConstants:3ItemCount
const_166912621872338000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:4ItemRange
const_166912621872339000 == 
0..2
----

=============================================================================
\* Modification History
\* Created Tue Nov 22 22:10:18 CST 2022 by wengjialin
