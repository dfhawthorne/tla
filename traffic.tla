------------------------------ MODULE traffic ------------------------------

NextColour(c) == CASE c = "red"   -> "green"
                   [] c = "green" -> "red"

(*--algorithm traffic

variables
  at_light = TRUE,
  light    = "red";
  
\* Light process

fair process light = "light"
begin
  Cycle:
    while at_light do
      light := NextColour(light);
    end while;
end process;

\* Car process

fair+ process car = "car"
begin
  Drive:
    when light = "green";
    at_light := FALSE;
end process;

end algorithm; *) 
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-35e0c0f830b5934ec44c55d3d29bd389
\* Process light at line 14 col 6 changed to light_
VARIABLES at_light, light, pc

vars == << at_light, light, pc >>

ProcSet == {"light"} \cup {"car"}

Init == (* Global variables *)
        /\ at_light = TRUE
        /\ light = "red"
        /\ pc = [self \in ProcSet |-> CASE self = "light" -> "Cycle"
                                        [] self = "car" -> "Drive"]

Cycle == /\ pc["light"] = "Cycle"
         /\ IF at_light
               THEN /\ light' = NextColour(light)
                    /\ pc' = [pc EXCEPT !["light"] = "Cycle"]
               ELSE /\ pc' = [pc EXCEPT !["light"] = "Done"]
                    /\ light' = light
         /\ UNCHANGED at_light

light_ == Cycle

Drive == /\ pc["car"] = "Drive"
         /\ light = "green"
         /\ at_light' = FALSE
         /\ pc' = [pc EXCEPT !["car"] = "Done"]
         /\ light' = light

car == Drive

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == light_ \/ car
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(light_)
        /\ SF_vars(car)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-074e5872c39ac24dfb6b988bdbd0e1d2

=============================================================================
\* Modification History
\* Last modified Mon Jun 22 19:43:10 AEST 2020 by douglas
\* Created Mon Jun 22 19:24:41 AEST 2020 by douglas
