--------------------------- MODULE SimpleProgram ---------------------------
EXTENDS Integers
VARIABLES i, pc

Init == (pc = "start") /\ (i = 0)

Pick == \/  /\ pc = "start"
            /\ i' \in 0..1000
            /\ pc' = "middle"

Add1 == \/  /\ pc = "middle"
            /\ i' = i + 1
            /\ pc' = "done"
            
Next == Pick \/ Add1

=============================================================================
\* Modification History
\* Last modified Tue Jun 07 13:11:06 CST 2022 by wengjialin
\* Created Tue Jun 07 13:00:52 CST 2022 by wengjialin
