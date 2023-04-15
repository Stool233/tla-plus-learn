---- MODULE MC ----
EXTENDS MapReduce, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2
----

\* MV CONSTANT definitions Workers
const_16688453176415000 == 
{w1, w2}
----

\* INIT definition @modelBehaviorNoSpec:0
init_16688453176426000 ==
FALSE/\input = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_16688453176427000 ==
FALSE/\input' = input
----
=============================================================================
\* Modification History
\* Created Sat Nov 19 16:08:37 CST 2022 by wengjialin
