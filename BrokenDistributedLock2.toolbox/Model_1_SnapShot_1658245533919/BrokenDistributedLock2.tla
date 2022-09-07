----------------------- MODULE BrokenDistributedLock2 -----------------------
EXTENDS FiniteSets

CONSTANT Client \* The set of client

VARIABLES
    clientState, \* clientState[c] is the state of client c.
    lockLeaseState, \* 锁实际的状态
    clientHeldLockState, \* 客户端认为自己是否占有了锁 
    lockClientRef \* 锁实际被哪个客户端c占有（可以理解为Lock Server有一个记录来源IP的能力）
    

TypeOK == 
    /\ clientState \in [Client -> {"init", "successAcquireLock", "failAcquireLock", "WritingData", "ReleasingLock", "ReleasedLock"}]
    /\ clientHeldLockState \in [Client -> { "notHeldLock", "heldLock"}]
    /\ lockLeaseState \in {"unlock", "locked"}
    /\ lockClientRef \in (Client \union {"noClient"})

Init == 
    (*************************************************************************)
    (* 每个客户端的状态为 “初始化”                                                *)
    (* 共享资源对应的锁的状态为 “未被占有”                                       *)
    (*************************************************************************)
    /\ clientState = [c \in Client |-> "init"]
    /\ clientHeldLockState = [c \in Client |-> "notHeldLock"]
    /\ lockLeaseState = "unlock"
    /\ lockClientRef = "noClient"
    

    
ClientLocking(c) == 
    (*************************************************************************)
    (* 客户端c尝试获取锁                                      *)
    (*************************************************************************)
    /\ clientState[c] = "init"
    /\ IF lockLeaseState = "unlock" 
            THEN 
                 /\ lockLeaseState' = "locked"
                 /\ clientState' = [clientState EXCEPT ![c] = "successAcquireLock" ]
                 /\ clientHeldLockState' = [clientHeldLockState EXCEPT ![c] = "heldLock" ]
                 /\ lockClientRef' = c
                 
            ELSE 
                /\ clientState' = [clientState EXCEPT ![c] = "failAcquireLock" ]
                /\ UNCHANGED <<lockLeaseState, clientHeldLockState, lockClientRef>>
                            
                            
ClientWritingData(c) == 
    (*************************************************************************)
    (* 客户端c访问共享资源                                       *)
    (*************************************************************************)
    /\ clientState[c] = "successAcquireLock"
    /\ clientState' = [clientState EXCEPT ![c] = "WritingData"]
    /\ UNCHANGED <<lockLeaseState, clientHeldLockState, lockClientRef>>


ClientWroteData(c) == 
    (*************************************************************************)
    (* 客户端c访问共享资源完成并释放锁                                       *)
    (*************************************************************************)
    /\ clientState[c] = "WritingData"
    /\ clientState' = [clientState EXCEPT ![c] = "ReleasingLock"]
    /\ UNCHANGED <<lockLeaseState, clientHeldLockState, lockClientRef>>
    
    
ClientReleaseLock(c) ==
    /\ clientState[c] = "ReleasingLock"
    /\ clientState' = [clientState EXCEPT ![c] = "ReleasedLock"]
    /\ clientHeldLockState' = [clientHeldLockState EXCEPT ![c] = "notHeldLock" ]
    /\ lockLeaseState' = "unlock"
    /\ lockClientRef' = "noClient"


LockExpire == 
    (*************************************************************************)
    (* 锁租约过期                                       *)
    (*************************************************************************)  
    /\ lockLeaseState = "locked"
    /\ lockLeaseState' = "unlock"
    /\ lockClientRef' = "noClient"
    /\ UNCHANGED <<clientState, clientHeldLockState>>
    
    
Next ==
    \/ LockExpire
    \/ \E c \in Client:
        ClientLocking(c) \/ ClientWritingData(c) \/ ClientWroteData(c) \/ ClientReleaseLock(c)

Spec == Init /\ [] [Next]_<<clientState, lockLeaseState, clientHeldLockState, lockClientRef>>


Consistent ==
    (*************************************************************************)
    (* 客户端c只能在锁实际被它占有的情况下，才能访问共享资源      *)
    (*************************************************************************)
    \A c \in Client: ~(/\ clientState[c] = "WritingData" 
                       /\ ~lockLeaseState = "locked")

CurrentHeldLock ==  {c \in Client: clientHeldLockState[c] = "heldLock"}

Consistent2 == 
    (*************************************************************************)
    (* 同一时刻最多只能有一个客户端认为它自己占有了锁（否则，它会去释放不属于它的锁等等）     *)
    (*************************************************************************) 
    Cardinality(CurrentHeldLock) \in {0, 1}


Consistent3 == 
   (*************************************************************************)
    (* 不允许客户端释放了不属于它的锁     *)
    (*************************************************************************) 
    \A c \in Client: 
             ~(/\ clientState[c] = "ReleasingLock" 
                        /\ ( (~ lockClientRef = c) /\  (~ lockClientRef = "noClient") ) )
    

THEOREM Spec => [](TypeOK /\ Consistent /\ Consistent2 /\ Consistent3)

=============================================================================
\* Modification History
\* Last modified Tue Jul 19 23:44:24 CST 2022 by wengjialin
\* Created Mon Jul 18 22:39:17 CST 2022 by wengjialin
