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
const_1669646797754413000 == 
{p1, p2}
----

\* MV CONSTANT definitions Books
const_1669646797754414000 == 
{b1}
----

\* CONSTANT definitions @modelParameterConstants:0NumCopies
const_1669646797754415000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Mon Nov 28 22:46:37 CST 2022 by wengjialin
