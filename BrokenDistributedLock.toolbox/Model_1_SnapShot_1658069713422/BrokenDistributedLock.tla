----------------------- MODULE BrokenDistributedLock -----------------------

CONSTANT Client \* The set of client

VARIABLES
    clientState, \* clientState[c] is the state of client c.
    lockLeaseState 
    

TypeOK == 
    /\ clientState \in [Client -> {"init", "gotLockLease", "WritingData", "WroteData"}]
    /\ lockLeaseState \in {"unlock", "locked"}

Init == 
    (*************************************************************************)
    (* 每个客户端的状态为 “初始化”                                                *)
    (* 共享资源对应的锁的状态为 “未被占有”                                       *)
    (*************************************************************************)
    /\ clientState = [c \in Client |-> "init"]
    /\ lockLeaseState = "unlock"
    
ClientLocking(c) == 
    (*************************************************************************)
    (* 客户端c占有共享资源对应的锁                                       *)
    (*************************************************************************)
    /\ lockLeaseState = "unlock"
    /\ clientState[c] = "init"
    /\ lockLeaseState' = "locked"
    /\ clientState' = [clientState EXCEPT ![c] = "gotLockLease"]
    
ClientWritingData(c) == 
    (*************************************************************************)
    (* 客户端c访问共享资源                                       *)
    (*************************************************************************)
    /\ clientState[c] = "gotLockLease"
    /\ clientState' = [clientState EXCEPT ![c] = "WritingData"]
    /\ UNCHANGED <<lockLeaseState>>

ClientWroteData(c) == 
    (*************************************************************************)
    (* 客户端c访问共享资源完成并释放锁                                       *)
    (*************************************************************************)
    /\ clientState[c] = "WritingData"
    /\ clientState' = [clientState EXCEPT ![c] = "WroteData"]
    /\ lockLeaseState' = "unlock"
    /\ UNCHANGED <<lockLeaseState>>
    

LockExpire == 
    (*************************************************************************)
    (* 锁租约过期                                       *)
    (*************************************************************************)  
    /\ lockLeaseState = "locked"
    /\ lockLeaseState' = "unlock"
    /\ UNCHANGED <<clientState>>
    
    
Next ==
    \/ LockExpire
    \/ \E c \in Client:
        ClientLocking(c) \/ ClientWritingData(c) \/ ClientWroteData(c)

Spec == Init /\ [] [Next]_<<clientState, lockLeaseState>>


Consistent ==
    \A c \in Client: ~(/\ clientState[c] = "WritingData" 
                       /\ ~lockLeaseState = "locked")

THEOREM Spec => [](TypeOK /\ Consistent)



=============================================================================
\* Modification History
\* Last modified Sun Jul 17 22:53:37 CST 2022 by wengjialin
\* Created Sun Jul 17 20:46:46 CST 2022 by wengjialin
