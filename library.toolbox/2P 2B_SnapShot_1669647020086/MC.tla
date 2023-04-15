---- MODULE MC ----
EXTENDS library, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
b1, b2
----

\* MV CONSTANT definitions People
const_1669647017038443000 == 
{p1, p2}
----

\* MV CONSTANT definitions Books
const_1669647017038444000 == 
{b1, b2}
----

\* CONSTANT definitions @modelParameterConstants:0NumCopies
const_1669647017038445000 == 
1..1
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1669647017038446000 ==
\A p \in People: Cardinality(wants[p]) <= 1
----
=============================================================================
\* Modification History
\* Created Mon Nov 28 22:50:17 CST 2022 by wengjialin
