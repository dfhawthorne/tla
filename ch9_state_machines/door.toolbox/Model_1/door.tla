-------------------------------- MODULE door --------------------------------

(*--algorithm door

variables
  open = FALSE,
  locked = FALSE,
  key \in BOOLEAN;
process open_door = "Open Door"
begin
  OpenDoor:
    await open;
    either \* lock/unlock
      locked := ~locked;
    or \* close
      await ~locked;
      locked := FALSE;
    end either;
    goto OpenDoor;
end process;
process closed_door = "Closed Door"
begin
  ClosedDoor:
    await ~open;
    either \* lock/unlock
      await key;
      locked := ~locked;
    or \* close
      await ~locked;
      open := TRUE;
    end either;
    goto ClosedDoor;
end process;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9e0d557cc570e0ef2d6e9438ce29d076
VARIABLES open, locked, key, pc

vars == << open, locked, key, pc >>

ProcSet == {"Open Door"} \cup {"Closed Door"}

Init == (* Global variables *)
        /\ open = FALSE
        /\ locked = FALSE
        /\ key \in BOOLEAN
        /\ pc = [self \in ProcSet |-> CASE self = "Open Door" -> "OpenDoor"
                                        [] self = "Closed Door" -> "ClosedDoor"]

OpenDoor == /\ pc["Open Door"] = "OpenDoor"
            /\ open
            /\ \/ /\ locked' = ~locked
               \/ /\ ~locked
                  /\ locked' = FALSE
            /\ pc' = [pc EXCEPT !["Open Door"] = "OpenDoor"]
            /\ UNCHANGED << open, key >>

open_door == OpenDoor

ClosedDoor == /\ pc["Closed Door"] = "ClosedDoor"
              /\ ~open
              /\ \/ /\ key
                    /\ locked' = ~locked
                    /\ open' = open
                 \/ /\ ~locked
                    /\ open' = TRUE
                    /\ UNCHANGED locked
              /\ pc' = [pc EXCEPT !["Closed Door"] = "ClosedDoor"]
              /\ key' = key

closed_door == ClosedDoor

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == open_door \/ closed_door
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-2149a5f02208bf76ce5d070ce7c5f667
      
=============================================================================
\* Modification History
\* Last modified Wed Sep 16 17:00:15 AEST 2020 by douglas
\* Created Wed Sep 16 16:17:15 AEST 2020 by douglas
