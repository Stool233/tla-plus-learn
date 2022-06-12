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
const_165487536313843000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions RM
const_165487536313844000 == 
{r1, r2}
----

\* SYMMETRY definition
symm_165487536313845000 == 
Permutations(const_165487536313844000)
----

\* CONSTANT definitions @modelParameterConstants:0Ballot
const_165487536313846000 == 
{0, 1}
----

\* CONSTANT definitions @modelParameterConstants:2Majority
const_165487536313847000 == 
{{a1, a2}, {a1, a3}, {a3}}
----

=============================================================================
\* Modification History
\* Created Fri Jun 10 23:36:03 CST 2022 by wengjialin
