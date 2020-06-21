--------------------- MODULE resource_consumer_example ---------------------
EXTENDS Integers

CONSTANT ResourceCap, MaxConsumerReq, Actors

ASSUME ResourceCap > 0
ASSUME Actors /= {}
ASSUME MaxConsumerReq \in 1..ResourceCap

(*--algorithm cache

variables
  resource_cap \in 1..ResourceCap;
  resources_left = resource_cap;
  reserved       = 0; \* our semaphore

define
  ResourceInvariant == resources_left >= 0
end define;

\* Actor process

process actor \in Actors

variables
  resources_needed \in 1..MaxConsumerReq
begin
  WaitForResources:
    while TRUE do
      await reserved + resources_needed <= resources_left;
      reserved := reserved + resources_needed;
      UseResources:
        while resources_needed > 0 do
          resources_left   := resources_left   - 1;
          resources_needed := resources_needed - 1;
          reserved         := reserved         - 1;
        end while;
        with x \in 1..MaxConsumerReq do
          resources_needed := x;
        end with;
    end while;
end process;

\* Time process

process time = "time"

begin
  Tick:
    resources_left := ResourceCap;
    goto Tick;
end process;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ea8a07dd3dbd026abf84075356be3f80
VARIABLES resource_cap, resources_left, reserved, pc

(* define statement *)
ResourceInvariant == resources_left >= 0

VARIABLE resources_needed

vars == << resource_cap, resources_left, reserved, pc, resources_needed >>

ProcSet == (Actors) \cup {"time"}

Init == (* Global variables *)
        /\ resource_cap \in 1..ResourceCap
        /\ resources_left = resource_cap
        /\ reserved = 0
        (* Process actor *)
        /\ resources_needed \in [Actors -> 1..MaxConsumerReq]
        /\ pc = [self \in ProcSet |-> CASE self \in Actors -> "WaitForResources"
                                        [] self = "time" -> "Tick"]

WaitForResources(self) == /\ pc[self] = "WaitForResources"
                          /\ reserved + resources_needed[self] <= resources_left
                          /\ reserved' = reserved + resources_needed[self]
                          /\ pc' = [pc EXCEPT ![self] = "UseResources"]
                          /\ UNCHANGED << resource_cap, resources_left, 
                                          resources_needed >>

UseResources(self) == /\ pc[self] = "UseResources"
                      /\ IF resources_needed[self] > 0
                            THEN /\ resources_left' = resources_left   - 1
                                 /\ resources_needed' = [resources_needed EXCEPT ![self] = resources_needed[self] - 1]
                                 /\ reserved' = reserved         - 1
                                 /\ pc' = [pc EXCEPT ![self] = "UseResources"]
                            ELSE /\ \E x \in 1..MaxConsumerReq:
                                      resources_needed' = [resources_needed EXCEPT ![self] = x]
                                 /\ pc' = [pc EXCEPT ![self] = "WaitForResources"]
                                 /\ UNCHANGED << resources_left, reserved >>
                      /\ UNCHANGED resource_cap

actor(self) == WaitForResources(self) \/ UseResources(self)

Tick == /\ pc["time"] = "Tick"
        /\ resources_left' = ResourceCap
        /\ pc' = [pc EXCEPT !["time"] = "Tick"]
        /\ UNCHANGED << resource_cap, reserved, resources_needed >>

time == Tick

Next == time
           \/ (\E self \in Actors: actor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-5a10bffee2a149cf62f4ef7559a4237b

=============================================================================
\* Modification History
\* Last modified Sun Jun 21 21:38:15 AEST 2020 by douglas
\* Created Sun Jun 21 20:17:31 AEST 2020 by douglas
