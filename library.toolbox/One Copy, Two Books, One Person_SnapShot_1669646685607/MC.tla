---- MODULE MC ----
EXTENDS library, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
b1, b2
----

\* MV CONSTANT definitions People
const_1669646683579393000 == 
{p1}
----

\* MV CONSTANT definitions Books
const_1669646683579394000 == 
{b1, b2}
----

\* CONSTANT definitions @modelParameterConstants:0NumCopies
const_1669646683579395000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Mon Nov 28 22:44:43 CST 2022 by wengjialin
