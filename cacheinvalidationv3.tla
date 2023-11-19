-------------------- MODULE cacheinvalidationv3 --------------------

EXTENDS Naturals

CONSTANT 
    KEYS

VARIABLES 
    database,
    cache,
    cacheFillStates, \* cacheFillStatus[key] = Fill state
    invalidationQueue,
    counter \* Used to prevent repeated states for liveness conditions

INSTANCE cacherequirements

vars == <<database, cache, cacheFillStates, invalidationQueue, counter>>

InvalidationMessage == [key: KEYS, version: DataVersion]

CacheFillState == [state: {"inactive", "started", "respondedto"}, version: DataVersion]

CacheValue == CacheMiss \union CacheHit

TypeOk ==
    /\ database \in [KEYS -> DataVersion]
    /\ cache \in [KEYS -> CacheValue]
    \* We track the cache fill state for each key. It is a multipart process
    /\ cacheFillStates \in [KEYS -> CacheFillState]
    \* We model invalidationQueue as a set, because we cannot guarantee in-order delivery
    /\ invalidationQueue \in SUBSET InvalidationMessage
    /\ counter \in Nat

Init ==
    /\ database = [k \in KEYS |-> 0]
    /\ cache = [k \in KEYS |-> [type |-> "miss"]]
    \* Cache fill states start inactive
    /\ cacheFillStates = [k \in KEYS |-> [
                                state |-> "inactive",
                                \* Version set to earliest possible version
                                version |-> 0]
                         ]
    \* The invalidation queue starts empty
    /\ invalidationQueue = {}
    /\ counter = 0


DatabaseUpdate(k) ==
    LET updatedVersion == database[k] + 1 IN
    \* The version of that key is incremented, representing a write
    /\ database' = [database EXCEPT 
                        ![k] = updatedVersion]
    \* Adds invalidation message to queue.
    \* We don't need to model a delay in adding message as the cache can
    \* always delay handling message to similar effect.
    /\ invalidationQueue' = invalidationQueue \union 
                                \* Add updated data to invalidation message
                                {[key |-> k, version |-> updatedVersion]}
    /\ UNCHANGED <<cache, cacheFillStates, counter>>


\* Cache Fill behavior
CacheStartReadThroughFill(k) ==
    \* Read-through only occurs when the cache is unset for that value
    /\ cache[k] \in CacheMiss
    \* One cache fill request at a time
    /\ cacheFillStates[k].state = "inactive"
    /\ cacheFillStates' = [cacheFillStates EXCEPT ![k].state = "started"]
    /\ UNCHANGED <<database, cache, invalidationQueue, counter>>


\* This is the moment the database provides a value for cache fill
DatabaseRespondToCacheFill(k) ==
    /\ cacheFillStates[k].state = "started"
    /\ cacheFillStates' = [cacheFillStates EXCEPT 
                            ![k].state = "respondedto",
                            ![k].version = database[k]  
                          ]
    /\ UNCHANGED <<database, cache, invalidationQueue, counter>>


\* Cache incorporates the data
CacheCompleteFill(k) ==
    /\ cacheFillStates[k].state = "respondedto"
       \* Either the cache is empty for that key
    /\ \/ cache[k] \in CacheMiss
       \* or we are filling a newer version
       \/ /\ cache[k] \notin CacheMiss
          /\ cache[k].version < cacheFillStates[k].version
    /\ cacheFillStates' = [cacheFillStates EXCEPT \* Reset to 0
                            ![k].state = "inactive",
                            ![k].version = 0
                          ]
    /\ cache' = [cache EXCEPT 
                        ![k] = [
                            \* Cache value is now a hit
                            type |-> "hit",
                            \* Set to whatever came back in response
                            version |-> cacheFillStates[k].version
                        ]
                ]
    /\ UNCHANGED <<database, invalidationQueue, counter>>


CacheIgnoreFill(k) ==
    /\ cacheFillStates[k].state = "respondedto"
    \* If we have a newer version in cache, ignore fill
    /\ /\ cache[k] \in CacheHit
       /\ cache[k].version >= cacheFillStates[k].version
    /\ cacheFillStates' = [cacheFillStates EXCEPT \* Reset to 0
                            ![k].state = "inactive",
                            ![k].version = 0
                        ]
    /\ counter' = counter + 1
    \* Don't update cache
    /\ UNCHANGED <<cache, database, invalidationQueue>>


\* Cache fails to fill
CacheFailFill(k) ==
    /\ cacheFillStates[k].state = "respondedto"
    \* Cache fill state is reset, having not filled cache
    /\ cacheFillStates' = [cacheFillStates EXCEPT 
                            ![k].state = "inactive",
                            ![k].version = 0
                          ]
    /\ UNCHANGED <<database, cache, invalidationQueue, counter>>


\* Handle invalidation message. Assume it is not taken off queue in case of
\* failure. Therefore failure modeled as CacheHandleInvalidationMessage not
\* occurring.
CacheHandleInvalidationMessage ==
    /\ \E message \in invalidationQueue: \* Dequeue invalidation queue in any order
        /\ \/ /\ cache[message.key] \in CacheHit
              \* Message needs to be newer than the cache
              /\ cache[message.key].version < message.version      
           \* Or not in the cache, but with a pending fill request
           \/ /\ cache[message.key] \in CacheMiss
              /\ cacheFillStates[message.key].state # "inactive"
        \* Update item in cache
        /\ cache' = [cache EXCEPT 
                        ![message.key] = [
                            type |-> "hit",
                            \* Update to version in invalidation message
                            version |-> message.version    
                        ]
                    ]
        \* Remove message from queue
        /\ invalidationQueue' = invalidationQueue \ {message}
  
    /\ UNCHANGED <<cacheFillStates, database, counter>>


CacheIgnoreInvalidationMessage == 
    /\ \E message \in invalidationQueue: \* Dequeue invalidation queue in any order
           \* Ignore invalidation messages for messages not in cache
        /\ \/ /\ cache[message.key] \in CacheMiss
              \* and a fill is not occurring
              /\ cacheFillStates[message.key].state = "inactive"
           \* Or when the cache already has the same or larger version
           \/ /\ cache[message.key] \notin CacheMiss
              /\ cache[message.key].version >= message.version
        \* Remove message from queue to ignore
        /\ invalidationQueue' = invalidationQueue \ {message}
    \* Don't update cache
    /\ counter' = counter + 1
    /\ UNCHANGED <<cacheFillStates, database, cache>>


CacheEvict(k) ==
    /\ cache[k] \in CacheHit
    \* A key with pending request will not be evicted
    /\ cacheFillStates[k].state = "inactive"
    /\ cache' = [cache EXCEPT ![k] = [type |-> "miss"]]
    /\ counter' = counter + 1
    /\ UNCHANGED <<database, cacheFillStates, invalidationQueue>>


\* The cache will always be able to...
CacheFairness ==
    \E k \in KEYS:
        \* Complete the cache fill process
        \/ CacheStartReadThroughFill(k)
        \/ DatabaseRespondToCacheFill(k) \* Write
        \/ CacheCompleteFill(k)
        \/ CacheIgnoreFill(k)
        \* Process invalidation messages
        \/ CacheHandleInvalidationMessage
        \/ CacheIgnoreInvalidationMessage



(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)


Next == 
    \E k \in KEYS:
        \* Database states
        \/ DatabaseUpdate(k)
        \* Cache states
        \/ CacheStartReadThroughFill(k)
        \/ DatabaseRespondToCacheFill(k)
        \/ CacheCompleteFill(k)
        \/ CacheIgnoreFill(k)
        \/ CacheHandleInvalidationMessage
        \/ CacheIgnoreInvalidationMessage
        \/ CacheEvict(k)


\* Cache fairness is included as part of the specification of system behavior.
\* This is just how the system works.
Spec == Init /\ [][Next]_vars /\ WF_vars(CacheFairness)

=============================================================================

