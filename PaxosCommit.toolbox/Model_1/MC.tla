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
const_165487545762364000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions RM
const_165487545762365000 == 
{r1, r2}
----

\* SYMMETRY definition
symm_165487545762366000 == 
Permutations(const_165487545762364000) \union Permutations(const_165487545762365000)
----

\* CONSTANT definitions @modelParameterConstants:0Ballot
const_165487545762367000 == 
{0, 1}
----

\* CONSTANT definitions @modelParameterConstants:2Majority
const_165487545762368000 == 
{{a1, a2}, {a1, a3}, {a2, a3}}
----

=============================================================================
\* Modification History
\* Created Fri Jun 10 23:37:37 CST 2022 by wengjialin
