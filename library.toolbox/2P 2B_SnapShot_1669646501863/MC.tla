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
const_1669646494887376000 == 
{p1, p2}
----

\* MV CONSTANT definitions Books
const_1669646494887377000 == 
{b1, b2}
----

\* CONSTANT definitions @modelParameterConstants:0NumCopies
const_1669646494887378000 == 
1..1
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1669646494887379000 ==
\A p \in People: Cardinality(wants[p]) <= 1
----
=============================================================================
\* Modification History
\* Created Mon Nov 28 22:41:34 CST 2022 by wengjialin
