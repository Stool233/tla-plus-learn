---- MODULE MC ----
EXTENDS library, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
b1
----

\* MV CONSTANT definitions People
const_1669646833611418000 == 
{p1, p2}
----

\* MV CONSTANT definitions Books
const_1669646833611419000 == 
{b1}
----

\* CONSTANT definitions @modelParameterConstants:0NumCopies
const_1669646833611420000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Mon Nov 28 22:47:13 CST 2022 by wengjialin
