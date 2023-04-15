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
const_1669646636724382000 == 
{p1, p2}
----

\* MV CONSTANT definitions Books
const_1669646636724383000 == 
{b1, b2}
----

\* CONSTANT definitions @modelParameterConstants:0NumCopies
const_1669646636724384000 == 
1..1
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1669646636724385000 ==
\A p \in People: Cardinality(wants[p]) <= 1
----
=============================================================================
\* Modification History
\* Created Mon Nov 28 22:43:56 CST 2022 by wengjialin
