---- MODULE MC ----
EXTENDS MapReduce4, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2, w3
----

\* MV CONSTANT definitions Workers
const_166912695346867000 == 
{w1, w2, w3}
----

\* CONSTANT definitions @modelParameterConstants:0ItemCount
const_166912695346868000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1ItemRange
const_166912695346869000 == 
0..2
----

=============================================================================
\* Modification History
\* Created Tue Nov 22 22:22:33 CST 2022 by wengjialin
