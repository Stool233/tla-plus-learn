---------------------------- MODULE time_periods ----------------------------
EXTENDS Integers
CONSTANT ResourceCap, MaxConsumerReq, Actors

ASSUME ResourceCap > 0
ASSUME Actors /= {}
ASSUME MaxConsumerReq \in 1..ResourceCap

(*--algorithm cache
variables resources_left = ResourceCap;

define
    ResourceInvariant == resources_left >= 0
end define;

process actor \in Actors
variables
    resources_needed \in 1..MaxConsumerReq
begin
    WaitForResources:
        while TRUE do
            await resources_left >= resources_needed;
            UseResources:
                while resources_needed > 0 do
                    resources_left := resources_left - 1;
                    resources_needed := resources_needed - 1;
                end while;
                with x \in 1..MaxConsumerReq do
                    resources_needed := x;
                end with;
           
        end while;
end process;

process time = "time"
begin
    Tick:
        resources_left := ResourceCap;
        goto Tick;
    end process;

end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "96b70b36" /\ chksum(tla) = "a177165d")
VARIABLES resources_left, pc

(* define statement *)
ResourceInvariant == resources_left >= 0

VARIABLE resources_needed

vars == << resources_left, pc, resources_needed >>

ProcSet == (Actors) \cup {"time"}

Init == (* Global variables *)
        /\ resources_left = ResourceCap
        (* Process actor *)
        /\ resources_needed \in [Actors -> 1..MaxConsumerReq]
        /\ pc = [self \in ProcSet |-> CASE self \in Actors -> "WaitForResources"
                                        [] self = "time" -> "Tick"]

WaitForResources(self) == /\ pc[self] = "WaitForResources"
                          /\ resources_left >= resources_needed[self]
                          /\ pc' = [pc EXCEPT ![self] = "UseResources"]
                          /\ UNCHANGED << resources_left, resources_needed >>

UseResources(self) == /\ pc[self] = "UseResources"
                      /\ IF resources_needed[self] > 0
                            THEN /\ resources_left' = resources_left - 1
                                 /\ resources_needed' = [resources_needed EXCEPT ![self] = resources_needed[self] - 1]
                                 /\ pc' = [pc EXCEPT ![self] = "UseResources"]
                            ELSE /\ \E x \in 1..MaxConsumerReq:
                                      resources_needed' = [resources_needed EXCEPT ![self] = x]
                                 /\ pc' = [pc EXCEPT ![self] = "WaitForResources"]
                                 /\ UNCHANGED resources_left

actor(self) == WaitForResources(self) \/ UseResources(self)

Tick == /\ pc["time"] = "Tick"
        /\ resources_left' = ResourceCap
        /\ pc' = [pc EXCEPT !["time"] = "Tick"]
        /\ UNCHANGED resources_needed

time == Tick

Next == time
           \/ (\E self \in Actors: actor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat Aug 27 22:48:46 CST 2022 by wengjialin
\* Created Sat Aug 27 22:04:51 CST 2022 by wengjialin
