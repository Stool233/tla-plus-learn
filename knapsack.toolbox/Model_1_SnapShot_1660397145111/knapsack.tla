------------------------------ MODULE knapsack ------------------------------
EXTENDS TLC, Integers, Sequences
PT == INSTANCE PT

Capacity == 7

Items == {"a", "b", "c"}

HardcodedItemSet == [
    a |-> [size |-> 1, value |-> 1],
    b |-> [size |-> 2, value |-> 3],
    c |-> [size |-> 3, value |-> 1]
] 

ItemParams == [size: 2..4, value: 0..5]
ItemSets == [Items -> ItemParams]




=============================================================================
\* Modification History
\* Last modified Sat Aug 13 21:25:04 CST 2022 by wengjialin
\* Created Sat Aug 13 21:13:15 CST 2022 by wengjialin
