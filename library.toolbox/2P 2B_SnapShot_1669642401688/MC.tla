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
const_1669642396654350000 == 
{p1, p2}
----

\* MV CONSTANT definitions Books
const_1669642396654351000 == 
{b1, b2}
----

\* CONSTANT definitions @modelParameterConstants:0NumCopies
const_1669642396654352000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Mon Nov 28 21:33:16 CST 2022 by wengjialin
