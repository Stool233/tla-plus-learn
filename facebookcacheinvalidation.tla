----------------------------- MODULE facebookcacheinvalidation -----------------------------

EXTENDS Naturals

CONSTANTS
    KEYS


VARIABLES 
    database,
    \* Represents metadata version stored in the cache
    cache,
    \* Represents the version stored in the cache, This is what is used for comparsions.
    \* to allow our model to decouple ACTUAL metadata version with STORED version
    cacheVersions,
    cacheFillStates,
    invalidationQueue,
    counter \* Used to prevent repeated states for liveness conditions

\* We can still test with the same cache requirements we've been using this whole time
INSTANCE cacherequirements

vars == <<database, cache, cacheFillStates,
    invalidationQueue, counter, cacheVersions>>

InvalidationMessage == [key: KEYS, version: DataVersion]

CacheFillState == [
    state: {
        "inactive",
        "startfillmetadata",
        "respondedtometadata", \* Next: CacheFillMetadata
        "startfillversion",
        "responedtoversion" \* Next: CacheFillVersion
    },
    version: DataVersion
]

CacheValue == CacheMiss \union CacheHit

TypeOk == 
    /\ database \in [KEYS -> DataVersion]
    /\ cache \in [KEYS -> CacheValue]
    \* Cache versions are typed identically to cache
    /\ cacheVersions \in [KEYS -> CacheValue]
    /\ cacheFillStates \in [KEYS -> CacheFillState]
    /\ invalidationQueue \in SUBSET InvalidationMessage
    /\ counter \in Nat


Init == 
    /\ database = [k \in KEYS |-> 0]
    \* cache (metadata) and cacheVersions start empty together
    /\ cache = [k \in KEYS |-> [type |-> "miss"]]
    /\ cacheVersions = [k \in KEYS |-> [type |-> "miss"]]

    /\ cacheFillStates = [k \in KEYS |-> [
                                state |-> "inactive",
                                version |-> 0
                                ]
                         ]
    /\ invalidationQueue = {}
    /\ counter = 0


DatabaseUpdate(k) == 
    LET updatedVersion == database[k] + 1 IN 
    /\ database' = [database EXCEPT 
                    ![k] = updatedVersion]
    /\ invalidationQueue' = invalidationQueue \union 
                                {[key |-> k, version |-> updatedVersion]}
    /\ UNCHANGED <<cache, cacheVersions, cacheFillStates, counter>>
                                    

CacheStartFillMetadata(k) == 
    /\ cache[k] \in CacheMiss
    /\ cacheFillStates[k].state = "inactive"
    /\ cacheFillStates' = [cacheFillStates EXCEPT ![k].state = "startfillmetadata"]
    /\ UNCHANGED <<database, cache, cacheVersions, invalidationQueue, counter>>


DatabaseRespondWithMetadata(k) == 
    /\ cacheFillStates[k].state = "startfillmetadata"
    /\ cacheFillStates' = [cacheFillStates EXCEPT 
                                ![k].state = "respondedtometadata",
                                ![k].version = database[k]]
    /\ UNCHANGED <<database, cache, cacheVersions, invalidationQueue, counter>>


CacheFillMetadata(k) == 
    \* 这里要处理版本？不需要，facebook的场景中不会处理metdata本身的version
    /\ cacheFillStates[k].state = "respondedtometadata"
    /\ cache' = [cache EXCEPT 
                            ![k] = [
                                type |-> "hit", 
                                version |-> cacheFillStates[k].version
                            ]
                ]
    /\ cacheFillStates' = [cacheFillStates EXCEPT
                                ![k].state = "inactive",
                                ![k].version = 0]
    /\ UNCHANGED <<database, cacheVersions, invalidationQueue, counter>>


CacheStartFillVersion(k) == 
    /\ cacheVersions[k] \in CacheMiss
    /\ cacheFillStates[k].state = "inactive"
    /\ cacheFillStates' = [cacheFillStates EXCEPT ![k].state = "startfillversion"]
    /\ UNCHANGED <<database, cache, cacheVersions, invalidationQueue, counter>>


DatabaseRespondWithVersion(k) == 
    /\ cacheFillStates[k].state = "startfillversion"
    /\ cacheFillStates' = [cacheFillStates EXCEPT 
                                ![k].state = "responedtoversion",
                                ![k].version = database[k]]
    /\ UNCHANGED <<database, cache, cacheVersions, invalidationQueue, counter>>


CacheFillVersion(k) == 
    \* 这里需要处理版本，facebook的场景主要靠这个管理version
    /\ cacheFillStates[k].state = "responedtoversion"
    /\ \/ cacheVersions[k] \in CacheMiss
       \/ /\ cacheVersions[k] \notin CacheMiss
          /\ cacheVersions[k].version < cacheFillStates[k].version
    /\ cacheVersions' = [cacheVersions EXCEPT 
                            ![k] = [
                                type |-> "hit", 
                                version |-> cacheFillStates[k].version
                            ]
                ]
    /\ cacheFillStates' = [cacheFillStates EXCEPT
                                ![k].state = "inactive",
                                ![k].version = 0]
    /\ UNCHANGED <<database, cache, invalidationQueue, counter>>


CacheIgnoreFillVersion(k) == 
    /\ cacheFillStates[k].state = "responedtoversion"
    /\ /\ cacheVersions[k] \in CacheHit
       /\ cacheVersions[k].version >= cacheFillStates[k].version
    /\ cacheFillStates' = [cacheFillStates EXCEPT
                                ![k].state = "inactive",
                                ![k].version = 0]
    \* 防止活性重复状态
    /\ counter' = counter + 1 
    /\ UNCHANGED <<database, cache, cacheVersions, invalidationQueue>>                   


CacheFailFill(k) == 
    /\ cacheFillStates[k].state \in  {"respondedtometadata", "responedtoversion"}
    /\ cacheFillStates' = [cacheFillStates EXCEPT
                                ![k].state = "inactive",
                                ![k].version = 0]
    \* 防止活性重复状态
    /\ counter' = counter + 1 
    /\ UNCHANGED <<database, cache, cacheVersions, invalidationQueue>>  


\* 缓存主动驱逐
CacheEvict(k) ==
    /\ cache[k] \in CacheHit
    /\ cacheFillStates[k].state = "inactive"
    /\ cache' = [cache EXCEPT ![k] = [type |-> "miss"]]
    /\ cacheVersions' = [cache EXCEPT  ![k] = [type |-> "miss"]]
    \* 防止活性重复状态
    /\ counter' = counter + 1 
    /\ UNCHANGED <<database, cacheFillStates, invalidationQueue>>


UpdateFromInvalidationMessage == 
    \E message \in invalidationQueue:
           \* metadata命中，但缓存中没有版本数据 
        /\ \/ /\ cache[message.key] \in CacheHit
              /\ cacheVersions[message.key] \in CacheMiss 
           \* 版本处理
           \/ /\ cacheVersions[message.key] \in CacheHit
              /\ cacheVersions[message.key].version <= message.version
        
        \* 关注当前的缓存填充过程，不引起冲突
        /\ cacheFillStates[message.key].state = "inactive"

        \* 这里会同时更新metadata和version
        /\ cache' = [cache EXCEPT 
                            ![message.key] = [
                                    type |-> "hit", 
                                    version |-> message.version       
                            ]
                    ]
        /\ cacheVersions' = [cacheVersions EXCEPT 
                                    ![message.key] = [
                                            type |-> "hit", 
                                            version |-> message.version  
                                    ]
                            ]
        /\ invalidationQueue' = invalidationQueue \ {message}
        
        /\ UNCHANGED <<database, cacheFillStates,  counter>>

\* 下面这样会无序获取队列中的值？不，都是无序的，所以可能有问题
\* IgnoreInvalidationMessage == 
\*     /\ \E message \in invalidationQueue:
\*            \* 没有这个key的缓存，且没有正在进行的相关的缓存填充过程
\*         /\ \/ /\ cache[message.key] \in CacheMiss
\*               /\ cacheFillStates[message.key].state = "inactive"
\*            \* 缓存已经有了更大的版本
\*            \/ /\ cacheVersions[message.key] \in CacheHit
\*               /\ cacheVersions[message.key].version > message.version            
\*         /\ invalidationQueue' = invalidationQueue \ {message}
\*         \* 防止活性重复状态
\*         /\ counter' = counter + 1 
\*     /\ UNCHANGED <<database, cache, cacheVersions, cacheFillStates>>

IgnoreInvalidationMessage == 
    \E message \in invalidationQueue:
           \* 没有这个key的缓存，且没有正在进行的相关的缓存填充过程
        /\ \/ /\ cache[message.key] \in CacheMiss
              /\ cacheFillStates[message.key].state = "inactive"
           \* 缓存已经有了更大的版本
           \/ /\ cacheVersions[message.key] \in CacheHit
              /\ cacheVersions[message.key].version > message.version            
        /\ invalidationQueue' = invalidationQueue \ {message}
        \* 防止活性重复状态
        /\ counter' = counter + 1 
        /\ UNCHANGED <<database, cache, cacheVersions, cacheFillStates>>



\* FailUpdateInvalidationMessageIgnore ==
\*     \E message \in invalidationQueue:
\*         \*  在缓存中的version 大于等于 事件中的version时会忽略异常处理程序的处理
\*         /\ cacheVersions[message.key] \in CacheHit
\*         /\ cacheVersions[message.key].version >= message.version 
\*         /\ invalidationQueue' = invalidationQueue \ {message}
\*         \* 防止活性重复状态
\*         /\ counter' = counter + 1 
\*         /\ UNCHANGED <<database, cache, cacheVersions, cacheFillStates>>

\* 修复问题，等于的不能忽略
FailUpdateInvalidationMessageIgnore ==
    \E message \in invalidationQueue:
        \*  在缓存中的version 大于 事件中的version时会忽略异常处理程序的处理
        /\ cacheVersions[message.key] \in CacheHit
        /\ cacheVersions[message.key].version > message.version 
        /\ invalidationQueue' = invalidationQueue \ {message}
        \* 防止活性重复状态
        /\ counter' = counter + 1 
        /\ UNCHANGED <<database, cache, cacheVersions, cacheFillStates>>


FailUpdateInvalidationMessageEvictkey == 
    \E message \in invalidationQueue:
           \* metadata命中，但缓存中没有版本数据 
        /\ \/ /\ cache[message.key] \in CacheHit
              /\ cacheVersions[message.key] \in CacheMiss 
           \* 版本处理
           \/ /\ cacheVersions[message.key] \in CacheHit
              \* 这里与普通的update少了等于的条件，即版本相同的不驱逐
              /\ cacheVersions[message.key].version < message.version
        
        \* 关注当前的缓存填充过程，不引起冲突
        /\ cacheFillStates[message.key].state = "inactive"

        /\ invalidationQueue' = invalidationQueue \ {message}
        /\ cache' = [cache EXCEPT ![message.key] = [type |-> "miss"]]
        /\ cacheVersions' = [cacheVersions EXCEPT ![message.key] = [type |-> "miss"]]
        /\ UNCHANGED <<database, cacheFillStates, counter>>



CacheFairness ==
    \/ \E k \in KEYS:
        \/ CacheStartFillMetadata(k)
        \/ DatabaseRespondWithMetadata(k)
        \/ CacheFillMetadata(k)
        \/ CacheStartFillVersion(k)
        \/ DatabaseRespondWithVersion(k)
        \/ CacheFillVersion(k)
        \/ CacheIgnoreFillVersion(k)
    \/ UpdateFromInvalidationMessage
    \/ IgnoreInvalidationMessage
    \/ FailUpdateInvalidationMessageIgnore
    \/ FailUpdateInvalidationMessageEvictkey      


Next == 
    \/ \E k \in KEYS:
        \* Database state
        \/ DatabaseUpdate(k)
        \* Cache state
        \/ CacheStartFillMetadata(k)
        \/ DatabaseRespondWithMetadata(k)
        \/ CacheFillMetadata(k)
        \/ CacheStartFillVersion(k)
        \/ DatabaseRespondWithVersion(k)
        \/ CacheFillVersion(k)
        \/ CacheIgnoreFillVersion(k)
        \/ CacheFailFill(k)
        \/ CacheEvict(k)
    \/ UpdateFromInvalidationMessage
    \/ IgnoreInvalidationMessage
    \/ FailUpdateInvalidationMessageIgnore
    \/ FailUpdateInvalidationMessageEvictkey
        





Spec == Init /\ [][Next]_vars /\ WF_vars(CacheFairness)


\* 防止出现重复状态
CounterBound == counter =< 2

=============================================================================
