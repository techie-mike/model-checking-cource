----------------------------- MODULE electronic_lock -----------------------------

EXTENDS Naturals, TLC

CONSTANTS
    AdminCard,
    RFIDCards,
    OutsideCard,
    AnswerRequest

VARIABLES
    lockState,
    serverConnected,
    lastCard, 
    doorTimer

Init == 
    /\ lockState = "open"
    /\ serverConnected = FALSE
    /\ lastCard = 0
    /\ doorTimer = 0

ConnectToServer == 
    /\ serverConnected = FALSE
    /\ serverConnected' = TRUE
    /\ lockState' = "closed"
    /\ UNCHANGED <<lastCard, doorTimer>>


DisconnectFromServer ==
    /\ serverConnected = TRUE
    /\ serverConnected' = FALSE
    /\ lockState' = "open"
    /\ UNCHANGED <<lastCard, doorTimer>>


ReadCard(card) == 
    /\ lastCard' = card
    /\ UNCHANGED <<lockState, serverConnected, doorTimer>>

ProcessCard == 
    /\ IF (lastCard = AdminCard) \/ (serverConnected = TRUE /\ AnswerRequest = TRUE)
       THEN /\ lockState' = "open"
            /\ doorTimer' = 10
       ELSE /\ UNCHANGED <<lockState>>
            /\ doorTimer' = 0
    /\ UNCHANGED <<lastCard, serverConnected>>

DecrementTimer == 
    /\ lockState = "open"
    /\ doorTimer > 1
    /\ doorTimer' = doorTimer - 1
    /\ IF doorTimer = 0 THEN lockState' = "closed" ELSE UNCHANGED lockState
    /\ UNCHANGED <<serverConnected, lastCard>>


Next == 
    \/ ConnectToServer
    \/ ReadCard(OutsideCard)
    \/ ProcessCard
    \/ DecrementTimer


Spec == Init /\ [][Next]_<<lockState, serverConnected, lastCard, doorTimer>>


=============================================================================

\* Modification History
\* Last modified Wed May 22 02:36:11 MSK 2024 by kasko
\* Created Tue May 20 20:18:07 MSK 2024 by kasko

