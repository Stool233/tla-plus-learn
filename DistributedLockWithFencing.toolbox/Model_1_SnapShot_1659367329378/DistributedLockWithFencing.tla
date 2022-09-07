--------------------- MODULE DistributedLockWithFencing ---------------------
EXTENDS FiniteSets, Integers

CONSTANT Client \* The set of client

VARIABLES
    clientState, \* clientState[c] is the state of client c.
    lockLeaseState, \* 锁实际的状态
    clientHeldLockState, \* 客户端认为自己是否占有了锁 
    lockClientRef, \* 锁实际被哪个客户端占有（可以理解为Lock Server有一个记录来源IP的能力）
    storageState, \* 共享资源目前是否在写入（不包含其是否在读取，这里类似于保证数据表的一行的写操作是原子的）
    lockLastToken, \* 锁服务的最近生成的令牌
    storageLastToken,  \* 存储服务最近用过的令牌
    clientFencingToken, \* 客户端从锁服务获取的递增令牌
    usedTokens  \* 用过的tokens

TypeOK == 
    /\ clientState \in [Client -> {"init", "successAcquireLock", "failAcquireLock", "PrepareWritingData", "WritingData", "RejectWriting", "ReleasingLock", "ReleasedLock"}]
    /\ clientHeldLockState \in [Client -> { "notHeldLock", "heldLock"}]
    /\ lockLeaseState \in {"unlock", "locked"}
    /\ storageState \in { "notwrite", "writing" }
    /\ lockClientRef \in (Client \union {"noClient"})
    /\ lockLastToken \in Nat
    /\ storageLastToken \in Nat
    /\ clientFencingToken \in [Client -> Nat]
    /\ usedTokens \subseteq {n \in Nat : n}

Init == 
    (*************************************************************************)
    (* 每个客户端的状态为 “初始化”                                                *)
    (* 共享资源对应的锁的状态为 “未被占有”                                       *)
    (*************************************************************************)
    /\ clientState = [c \in Client |-> "init"]
    /\ clientHeldLockState = [c \in Client |-> "notHeldLock"]
    /\ lockLeaseState = "unlock"
    /\ lockClientRef = "noClient"
    /\ storageState = "notwrite"
    /\ lockLastToken = 0
    /\ storageLastToken = 0
    /\ clientFencingToken = [c \in Client |-> 0]
    /\ usedTokens = {}
    

    
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
                 /\ lockLastToken' = lockLastToken + 1
                 /\ clientFencingToken' = [clientFencingToken EXCEPT ![c] = lockLastToken + 1 ]
                 /\ lockClientRef' = c
                 /\ UNCHANGED <<storageLastToken, storageState, usedTokens>>
                 
            ELSE 
                /\ clientState' = [clientState EXCEPT ![c] = "failAcquireLock" ]
                /\ UNCHANGED <<lockLeaseState, clientHeldLockState, lockClientRef, lockLastToken, clientFencingToken, storageLastToken, storageState, usedTokens>>
                            
                            
ClientPrepareWritingData(c) == 
    (*************************************************************************)
    (* 客户端c访问共享资源                                       *)
    (*************************************************************************)
    /\ clientState[c] = "successAcquireLock"
    /\ clientState' = [clientState EXCEPT ![c] = "PrepareWritingData"]
    /\ UNCHANGED <<lockLeaseState, clientHeldLockState, lockClientRef, lockLastToken, clientFencingToken, storageLastToken, storageState, usedTokens>>


ClientWritingData(c) == 
    (*************************************************************************)
    (* 客户端c访问共享资源完成并释放锁                                       *)
    (*************************************************************************)
    /\ clientState[c] = "PrepareWritingData"
    /\ storageState = "notwrite"
    /\ IF clientFencingToken[c] > storageLastToken
            THEN
                /\ storageLastToken' = clientFencingToken[c]
                /\ clientState' = [clientState EXCEPT ![c] = "WritingData"]
                /\ storageState' = "writing"
                /\ usedTokens' = usedTokens \union { clientFencingToken[c] }
                /\ UNCHANGED <<lockLeaseState, clientHeldLockState, lockClientRef, lockLastToken, clientFencingToken>>
            ELSE
                /\ clientState' = [clientState EXCEPT ![c] = "RejectWriting"]
                /\ UNCHANGED <<lockLeaseState, clientHeldLockState, lockClientRef, lockLastToken, clientFencingToken, storageLastToken, storageState, usedTokens>>
    
    
ClientWroteData(c) == 
    /\ clientState[c] = "WritingData"
    /\ clientState' = [clientState EXCEPT ![c] = "ReleasingLock"]
    /\ storageState' = "notwrite"
    /\ UNCHANGED <<lockLeaseState, clientHeldLockState, lockClientRef, lockLastToken, clientFencingToken, storageLastToken, usedTokens>>
    
    
ClientReleaseLock(c) ==
    /\ clientState[c] = "ReleasingLock"
    /\ clientState' = [clientState EXCEPT ![c] = "ReleasedLock"]
    /\ clientHeldLockState' = [clientHeldLockState EXCEPT ![c] = "notHeldLock" ]
    /\ lockLeaseState' = "unlock"
    /\ lockClientRef' = "noClient"
    /\ UNCHANGED <<lockLastToken, clientFencingToken, storageLastToken, storageState, usedTokens>>


LockExpire == 
    (*************************************************************************)
    (* 锁租约过期                                       *)
    (*************************************************************************)  
    /\ lockLeaseState = "locked"
    /\ lockLeaseState' = "unlock"
    /\ lockClientRef' = "noClient"
    /\ UNCHANGED <<clientState, clientHeldLockState, lockLastToken, storageLastToken, clientFencingToken, storageState, usedTokens>>
    
    
Next ==
    \/ LockExpire
    \/ \E c \in Client:
        ClientLocking(c) \/ ClientPrepareWritingData(c) \/ ClientWritingData(c) \/ ClientWroteData(c) \/ ClientReleaseLock(c)

Spec == Init /\ [] [Next]_<<clientState, lockLeaseState, clientHeldLockState, lockClientRef, lockLastToken, storageLastToken, clientFencingToken, storageState, usedTokens>>


\*Consistent ==
\*    (*************************************************************************)
\*    (* 客户端c只能在锁实际被它占有的情况下，才能成功访问共享资源      *)
\*    (*************************************************************************)
\*    \A c \in Client: ~(/\ clientState[c] = "WritingData" 
\*                       /\ ~lockLeaseState = "locked")




CurrentWritingClients ==  {c \in Client: clientState[c] = "WritingData"}

Consistent2 == 
    (*************************************************************************)
    (* 同一时刻最多只能有一个客户端在访问共享资源（这个规约还不够）      *)
    (*************************************************************************)
    Cardinality(CurrentWritingClients) \in {0, 1}
    
 
Consistent3 == 
    (*************************************************************************)
    (* 保证token的顺序生效性      *)
    (*************************************************************************)
    Cardinality(CurrentWritingClients) \in {0, 1}

\*CurrentHeldLock ==  {c \in Client: clientHeldLockState[c] = "heldLock"}
\*
\*Consistent2 == 
\*    (*************************************************************************)
\*    (* 同一时刻最多只能有一个客户端认为它自己占有了锁（否则，它会去访问不属于它的资源、释放不属于它的锁等等）     *)
\*    (*************************************************************************) 
\*    Cardinality(CurrentHeldLock) \in {0, 1}


\*Consistent3 == 
\*   (*************************************************************************)
\*    (* 不允许客户端释放了不属于它的锁     *)
\*    (*************************************************************************) 
\*    \A c \in Client: 
\*             ~(/\ clientState[c] = "ReleasingLock" 
\*                        /\ ( (~ lockClientRef = c) /\  (~ lockClientRef = "noClient") ) )
    

THEOREM Spec => [](TypeOK)

=============================================================================
\* Modification History
\* Last modified Mon Aug 01 23:22:02 CST 2022 by wengjialin
\* Created Mon Jul 18 22:39:17 CST 2022 by wengjialin

=============================================================================
\* Modification History
\* Created Wed Jul 20 00:04:51 CST 2022 by wengjialin
