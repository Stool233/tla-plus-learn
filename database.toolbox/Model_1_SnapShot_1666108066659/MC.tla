---- MODULE MC ----
EXTENDS database, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2
----

\* MV CONSTANT definitions Clients
const_166610806464010000 == 
{c1, c2}
----

\* MV CONSTANT definitions Data
const_166610806464011000 == 
{d1, d2}
----

=============================================================================
\* Modification History
\* Created Tue Oct 18 23:47:44 CST 2022 by wengjialin
