------------------------------ MODULE Sequence ------------------------------
EXTENDS Integers, Sequences

Remove(i, seq) == 
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] 
                                      ELSE seq[j+1]]


=============================================================================
\* Modification History
\* Last modified Sat Jun 11 16:42:18 CST 2022 by wengjialin
\* Created Sat Jun 11 16:40:24 CST 2022 by wengjialin
