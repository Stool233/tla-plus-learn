---- MODULE MC ----
EXTENDS PaxosCommit, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2
----

\* MV CONSTANT definitions Acceptor
const_16548744792817000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions RM
const_16548744792818000 == 
{r1, r2}
----

\* SYMMETRY definition
symm_16548744792819000 == 
Permutations(const_16548744792818000)
----

\* CONSTANT definitions @modelParameterConstants:0Ballot
const_165487447928110000 == 
{0, 1}
----

\* CONSTANT definitions @modelParameterConstants:2Majority
const_165487447928111000 == 
{{a1, a2}, {a1, a3}, {a2, a3}}
----

=============================================================================
\* Modification History
\* Created Fri Jun 10 23:21:19 CST 2022 by wengjialin
