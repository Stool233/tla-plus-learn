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
const_1669644372594360000 == 
{p1, p2}
----

\* MV CONSTANT definitions Books
const_1669644372594361000 == 
{b1, b2}
----

\* CONSTANT definitions @modelParameterConstants:0NumCopies
const_1669644372594362000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Mon Nov 28 22:06:12 CST 2022 by wengjialin
