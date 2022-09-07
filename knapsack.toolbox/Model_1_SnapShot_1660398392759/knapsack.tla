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

KnapsackSize(sack, itemset) ==
    LET size_for(item) == itemset[item].size * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: size_for(item) + acc, Items, 0)

ValidKnapsacks(itemset) ==
    {sack \in [Items -> 0..4]: KnapsackSize(sack, itemset) <= Capacity}
    
\* minor amount of duplicate code
KnapsackValue(sack, itemset) ==
    LET value_for(item) == itemset[item].value * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)
    
BestKnapsack(itemset) ==
    LET all == ValidKnapsacks(itemset)
    IN CHOOSE best \in all:
        \A worse \in all \ {best}:
        KnapsackValue(best, itemset) > KnapsackValue(worse, itemset)




=============================================================================
\* Modification History
\* Last modified Sat Aug 13 21:44:39 CST 2022 by wengjialin
\* Created Sat Aug 13 21:13:15 CST 2022 by wengjialin
