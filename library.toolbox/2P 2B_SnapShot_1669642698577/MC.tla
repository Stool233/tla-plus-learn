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
const_1669642694518355000 == 
{p1, p2}
----

\* MV CONSTANT definitions Books
const_1669642694518356000 == 
{b1, b2}
----

\* CONSTANT definitions @modelParameterConstants:0NumCopies
const_1669642694518357000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Mon Nov 28 21:38:14 CST 2022 by wengjialin
