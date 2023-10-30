---- MODULE team_build ----
EXTENDS TLC, FiniteSets, Integers

CONSTANTS PLAYERS, LOBBY_SIZE
ASSUME Cardinality(PLAYERS) >= LOBBY_SIZE

VARIABLES lobby

TypeOK == lobby \subseteq PLAYERS

isLobbyFull == Cardinality(lobby) = LOBBY_SIZE

canEnterGame == /\ isLobbyFull
                /\ lobby' = lobby

exitLobby(x) == /\ ~isLobbyFull
                /\ x \in lobby
                /\ lobby' = lobby \ {x}

enterLobby(x) == /\ ~isLobbyFull
                 /\ x \notin lobby
                 /\ lobby' = lobby \union {x}

Init == lobby = {}

Next == \/ canEnterGame
        \/ \E p \in PLAYERS: exitLobby(p) \/ enterLobby(p)

Spec == Init /\ [][Next]_lobby

ModelInvariant == isLobbyFull

THEOREM Spec => [](TypeOK) /\ <>[](ModelInvariant)
====