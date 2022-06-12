---- MODULE MC ----
EXTENDS AB, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2, d3
----

\* MV CONSTANT definitions Data
const_1654947675510125000 == 
{d1, d2, d3}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1654947675510126000 ==
/\ Len(AtoB) =< 3
/\ Len(BtoA) =< 3
----
=============================================================================
\* Modification History
\* Created Sat Jun 11 19:41:15 CST 2022 by wengjialin
