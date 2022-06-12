---- MODULE MC ----
EXTENDS AB, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2, d3
----

\* MV CONSTANT definitions Data
const_1654954380453128000 == 
{d1, d2, d3}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1654954380453129000 ==
/\ Len(AtoB) =< 3
/\ Len(BtoA) =< 3
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1654954380453131000 ==
ABS!Spec
----
=============================================================================
\* Modification History
\* Created Sat Jun 11 21:33:00 CST 2022 by wengjialin
