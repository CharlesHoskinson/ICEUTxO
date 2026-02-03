--------------------------- MODULE StarstreamUTXO ---------------------------
(***************************************************************************
 * UTXO State Machine for Starstream
 ***************************************************************************)

EXTENDS StarstreamTypes, StarstreamFrame

(***************************************************************************
 * UTXO RECORD TYPE
 ***************************************************************************)

UTXORecordSet ==
    [id: UTXOIdRange,
     state: UTXOStates,
     frame: FrameSet,
     datum: DatumValues,
     tokens: TokenBagType,
     contractId: ContractIds,
     owner: OwnerAddrs,
     lockedBy: TxIdRange \cup {NO_TX}]

(***************************************************************************
 * UTXO CONSTRUCTORS
 ***************************************************************************)

NewUTXO(utxoId, contract, ownerAddr, initialDatum, initialTokens) ==
    [id |-> utxoId,
     state |-> "Created",
     frame |-> InitFrame(0),
     datum |-> initialDatum,
     tokens |-> initialTokens,
     contractId |-> contract,
     owner |-> ownerAddr,
     lockedBy |-> NO_TX]

SuspendedUTXO(utxoId, contract, ownerAddr, datum, tokens, frame) ==
    [id |-> utxoId,
     state |-> "Suspended_at_Yield",
     frame |-> frame,
     datum |-> datum,
     tokens |-> tokens,
     contractId |-> contract,
     owner |-> ownerAddr,
     lockedBy |-> NO_TX]

(***************************************************************************
 * UTXO PREDICATES
 ***************************************************************************)

IsUTXORecord(u) ==
    /\ IsValidUTXOId(u.id)
    /\ IsValidUTXOState(u.state)
    /\ IsFrame(u.frame)
    /\ u.datum \in DatumValues
    /\ IsValidTokenBag(u.tokens)
    /\ u.contractId \in ContractIds
    /\ u.owner \in OwnerAddrs
    /\ (u.lockedBy = NO_TX \/ u.lockedBy \in TxIdRange)

IsLive(u) ==
    /\ IsUTXORecord(u)
    /\ u.state # "Consumed"

IsConsumed(u) == /\ IsUTXORecord(u) /\ u.state = "Consumed"

IsReserved(u) == /\ IsUTXORecord(u) /\ u.state = "Reserved"
IsExecuting(u) == /\ IsUTXORecord(u) /\ u.state = "Executing"

CanQuery(u) == /\ IsLive(u) /\ u.state \in {"Suspended_at_Yield", "Reserved", "Executing"}
CanMutate(u) == /\ IsLive(u) /\ u.state \in {"Suspended_at_Yield", "Reserved", "Executing"}
CanConsume(u) == /\ IsLive(u) /\ u.state \in {"Suspended_at_Yield", "Reserved", "Executing"}
CanRaiseEffect(u) == /\ IsLive(u) /\ u.state \in {"Created", "Suspended_at_Yield", "Executing"}

IsWaitingForHandler(u) == /\ IsUTXORecord(u) /\ u.state = "Suspended_at_Effect"

CanReserve(u) == /\ IsUTXORecord(u) /\ u.state = "Suspended_at_Yield" /\ u.lockedBy = NO_TX

(***************************************************************************
 * STATE TRANSITION OPERATORS (pure record updates)
 ***************************************************************************)

CreateToYield(u, yieldPC, newDatum) ==
    [u EXCEPT
        !.state = "Suspended_at_Yield",
        !.frame = AdvancePC(u.frame, yieldPC),
        !.datum = newDatum]

ExecuteQuery(u) == u

ExecuteMutation(u, newDatum, newPC) ==
    [u EXCEPT
        !.frame = AdvancePC(u.frame, newPC),
        !.datum = newDatum]

RaiseEffect(u, effectPC) ==
    [u EXCEPT
        !.state = "Suspended_at_Effect",
        !.frame = SuspendForEffect(u.frame, effectPC)]

HandleEffect(u, resumePC, handlerResult) ==
    [u EXCEPT
        !.state = "Suspended_at_Yield",
        !.frame = ResumeFromEffect(u.frame, resumePC, handlerResult)]

RaiseEffectUTXO(u, effectPC) ==
    [u EXCEPT
        !.state = "Suspended_at_Effect",
        !.frame = SuspendForEffect(u.frame, effectPC)]

ResumeEffectUTXO(u, resumePC, handlerResult) ==
    [u EXCEPT
        !.state = "Executing",
        !.frame = ResumeFromEffect(u.frame, resumePC, handlerResult)]

ConsumeUTXO(u) ==
    [u EXCEPT
        !.state = "Consumed",
        !.frame = Terminate(u.frame)]

ReserveUTXO(u, txId) ==
    [u EXCEPT
        !.state = "Reserved",
        !.lockedBy = txId]

ReleaseReservation(u) ==
    [u EXCEPT
        !.state = "Suspended_at_Yield",
        !.lockedBy = NO_TX]

BeginExecuteUTXO(u) ==
    [u EXCEPT !.state = "Executing"]

EndExecuteUTXO(u) ==
    [u EXCEPT !.state = "Reserved"]

(***************************************************************************
 * UTXO SET OPERATIONS
 ***************************************************************************)

FindUTXO(utxoSet, utxoId) == CHOOSE u \in utxoSet : u.id = utxoId

UTXOExists(utxoSet, utxoId) == \E u \in utxoSet : u.id = utxoId

LiveUTXOs(utxoSet) == {u \in utxoSet : IsLive(u)}

ConsumedUTXOs(utxoSet) == {u \in utxoSet : IsConsumed(u)}

UTXOsOwnedBy(utxoSet, owner) == {u \in utxoSet : u.owner = owner}

UTXOsForContract(utxoSet, contract) == {u \in utxoSet : u.contractId = contract}

UpdateUTXOInSet(utxoSet, newUTXO) ==
    {IF u.id = newUTXO.id THEN newUTXO ELSE u : u \in utxoSet}

RemoveUTXOFromSet(utxoSet, utxoId) == {u \in utxoSet : u.id # utxoId}

AddUTXOToSet(utxoSet, newUTXO) == utxoSet \cup {newUTXO}

(***************************************************************************
 * UTXO INVARIANTS
 ***************************************************************************)

UniqueUTXOIds(utxoSet) ==
    \A u1, u2 \in utxoSet : u1 # u2 => u1.id # u2.id

NoZombieUTXOs(utxoSet) ==
    \A u \in utxoSet : ~(IsLive(u) /\ IsConsumed(u))

ConsumedIsFinal(u, uNext) == IsConsumed(u) => IsConsumed(uNext)

=============================================================================
