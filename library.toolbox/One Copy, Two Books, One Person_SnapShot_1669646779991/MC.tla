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
const_1669646777955408000 == 
{p1}
----

\* MV CONSTANT definitions Books
const_1669646777955409000 == 
{b1, b2}
----

\* CONSTANT definitions @modelParameterConstants:0NumCopies
const_1669646777955410000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Mon Nov 28 22:46:17 CST 2022 by wengjialin
