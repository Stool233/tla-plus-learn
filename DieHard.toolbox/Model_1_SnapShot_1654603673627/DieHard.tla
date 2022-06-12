------------------------------ MODULE DieHard ------------------------------
EXTENDS Integers
VARIABLES small, big

TypeOK ==       /\ small \in 0..3
                /\ big \in 0..5

Init ==         /\ big = 0 
                /\ small = 0


FillSmall ==    /\ small' = 3
                /\ big' = big
              

FillBig ==      /\ small' = small
                /\ big' = 5


EmptySmall ==   /\ small' = 0
                /\ big' = big

EmptyBig ==     /\ big' = 0
                /\ small' = small             

SmallToBig ==   IF  big + small =< 5
                    THEN    /\ big' = big + small
                            /\ small' = 0
                    ELSE    /\ big' = 5
                            /\ small' = small - (5 - big)

BigToSmall ==   IF big + small =< 3
                    THEN    /\ small' = big + small
                            /\ big' = 0
                    ELSE    /\ small' = 3
                            /\ big' = big - (3 - small)


Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall


=============================================================================
\* Modification History
\* Last modified Tue Jun 07 20:07:43 CST 2022 by wengjialin
\* Created Tue Jun 07 19:37:04 CST 2022 by wengjialin
