EXTENDS TLC, Integer

------------------------------- MODULE point -------------------------------

LOCAL INSTANCE Integers
CONSTANTS X, Y
ASSUME X \in Int
ASSUME Y \in Int
Point == <<X, Y>>
Add(x, y) == <<X + x, Y + y>>

=============================================================================
\* Modification History
\* Last modified Wed May 27 22:42:11 AEST 2020 by douglas
\* Created Wed May 27 22:38:05 AEST 2020 by douglas

INSTANCE Point WITH X <- 1, Y <- 2
