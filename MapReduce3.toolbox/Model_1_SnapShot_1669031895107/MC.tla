---- MODULE MC ----
EXTENDS MapReduce3, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2, w3
----

\* MV CONSTANT definitions Workers
const_16690318876857000 == 
{w1, w2, w3}
----

\* CONSTANT definitions @modelParameterConstants:3ItemCount
const_16690318876858000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:4ItemRange
const_16690318876859000 == 
0..2
----

=============================================================================
\* Modification History
\* Created Mon Nov 21 19:58:07 CST 2022 by wengjialin
