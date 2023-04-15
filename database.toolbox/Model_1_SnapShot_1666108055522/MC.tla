---- MODULE MC ----
EXTENDS database, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2
----

\* MV CONSTANT definitions Clients
const_16661080524816000 == 
{c1}
----

\* MV CONSTANT definitions Data
const_16661080524817000 == 
{d1, d2}
----

=============================================================================
\* Modification History
\* Created Tue Oct 18 23:47:32 CST 2022 by wengjialin
