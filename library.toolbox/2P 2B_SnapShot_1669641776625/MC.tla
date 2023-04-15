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
const_1669641773598345000 == 
{p1, p2}
----

\* MV CONSTANT definitions Books
const_1669641773598346000 == 
{b1, b2}
----

\* CONSTANT definitions @modelParameterConstants:0NumCopies
const_1669641773598347000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Mon Nov 28 21:22:53 CST 2022 by wengjialin
