---- MODULE MC ----
EXTENDS MapReduce3, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2, w3
----

\* MV CONSTANT definitions Workers
const_16691260255102000 == 
{w1, w2, w3}
----

\* CONSTANT definitions @modelParameterConstants:3ItemCount
const_16691260255103000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:4ItemRange
const_16691260255104000 == 
0..2
----

=============================================================================
\* Modification History
\* Created Tue Nov 22 22:07:05 CST 2022 by wengjialin
