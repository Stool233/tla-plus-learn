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
const_165487491536117000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions RM
const_165487491536118000 == 
{r1, r2}
----

\* SYMMETRY definition
symm_165487491536119000 == 
Permutations(const_165487491536117000) \union Permutations(const_165487491536118000)
----

\* CONSTANT definitions @modelParameterConstants:0Ballot
const_165487491536120000 == 
{0, 1}
----

\* CONSTANT definitions @modelParameterConstants:2Majority
const_165487491536121000 == 
{{a1, a2}, {a1, a3}, {a2, a3}}
----

=============================================================================
\* Modification History
\* Created Fri Jun 10 23:28:35 CST 2022 by wengjialin
