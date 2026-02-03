------------------------ MODULE StarstreamTransaction ------------------------
(***************************************************************************
 * Transaction Model for Starstream
 ***************************************************************************)

EXTENDS StarstreamTypes, StarstreamFrame, StarstreamUTXO, StarstreamEffects,
        StarstreamCoordination, StarstreamAuth, StarstreamProof

(***************************************************************************
 * TRANSACTION RECORD TYPE
 ***************************************************************************)

TransactionRecordSet ==
    [id: TxIdRange,
     signer: OwnerAddrs,
     signature: SignatureType,
     inputs: SUBSET UTXORecordSet,
     coordination: CoordinationStateSet,
     outputs: SUBSET UTXORecordSet,
     readSet: SUBSET UTXOIdRange,
     readSnapshot: SUBSET UTXORecordSet,
     writeSet: SUBSET UTXOIdRange,
     phase: TxStates,
     result: DatumValues \cup {NULL},
     proofCommitments: SUBSET ProofCommitmentType,  \* IVC proof commitments
     proofPhase: ProofPhases]                        \* Overall proof phase for tx

(***************************************************************************
 * TRANSACTION CONSTRUCTORS
 ***************************************************************************)

SignTx(tx) ==
    [tx EXCEPT !.signature = MakeSignature(tx.signer, tx.id, TxContentsHash(tx))]

NewTransaction(txId, signer) ==
    SignTx([id |-> txId,
            signer |-> signer,
            signature |-> MakeSignature(signer, txId, <<>>),
            inputs |-> {},
            coordination |-> InitCoordination,
            outputs |-> {},
            readSet |-> {},
            readSnapshot |-> {},
            writeSet |-> {},
            phase |-> "Idle",
            result |-> NULL,
            proofCommitments |-> {},
            proofPhase |-> "NotStarted"])

TransactionWithInputs(txId, signer, inputUtxos) ==
    LET inputIds == {u.id : u \in inputUtxos}
    IN SignTx([id |-> txId,
               signer |-> signer,
               signature |-> MakeSignature(signer, txId, <<>>),
               inputs |-> inputUtxos,
               coordination |-> GatheringCoordination(inputIds),
               outputs |-> {},
               readSet |-> inputIds,
               readSnapshot |-> inputUtxos,
               writeSet |-> inputIds,
               phase |-> "Reserve",
               result |-> NULL,
               proofCommitments |-> {},
               proofPhase |-> "NotStarted"])

(***************************************************************************
 * TRANSACTION PREDICATES
 ***************************************************************************)

IsTransactionRecord(tx) ==
    /\ tx.id \in TxIdRange
    /\ tx.signer \in OwnerAddrs
    /\ IsSignature(tx.signature)
    /\ \A u \in tx.inputs : IsUTXORecord(u)
    /\ IsCoordinationState(tx.coordination)
    /\ \A u \in tx.outputs : IsUTXORecord(u)
    /\ \A id \in tx.readSet : id \in UTXOIdRange
    /\ \A u \in tx.readSnapshot : IsUTXORecord(u)
    /\ \A id \in tx.writeSet : id \in UTXOIdRange
    /\ tx.phase \in TxStates
    /\ tx.result \in DatumValues \cup {NULL}
    /\ \A p \in tx.proofCommitments : IsProofCommitment(p)
    /\ tx.proofPhase \in ProofPhases

IsIdleTx(tx) == tx.phase = "Idle"
IsReserveTx(tx) == tx.phase = "Reserve"
IsExecutingTx(tx) == tx.phase = "Executing"
IsCommittedTx(tx) == tx.phase = "Committed"
IsFailedTx(tx) == tx.phase = "Failed"
IsCompleteTx(tx) == tx.phase \in {"Committed", "Failed"}

(***************************************************************************
 * BALANCE CALCULATION
 ***************************************************************************)

SumInputTokens(tx) ==
    FoldSet(LAMBDA acc, u : AddTokenBags(acc, u.tokens), EmptyTokenBag, tx.inputs)

SumOutputTokens(tx) ==
    FoldSet(LAMBDA acc, u : AddTokenBags(acc, u.tokens), EmptyTokenBag, tx.outputs)

BalancePreserved(tx) ==
    TokenBagsEqual(SumInputTokens(tx), SumOutputTokens(tx))

NetTokenFlow(tx) ==
    [t \in TOKEN_TYPES |->
        [id \in TOKEN_IDS |-> SumOutputTokens(tx)[t][id] - SumInputTokens(tx)[t][id]]]

(***************************************************************************
 * TRANSACTION STATE TRANSITIONS (pure updates)
 ***************************************************************************)

ReserveTransaction(tx, inputUtxos) ==
    LET updated ==
        [tx EXCEPT
            !.inputs = inputUtxos,
            !.coordination = GatheringCoordination({u.id : u \in inputUtxos}),
            !.readSet = {u.id : u \in inputUtxos},
            !.readSnapshot = inputUtxos,
            !.writeSet = {u.id : u \in inputUtxos},
            !.phase = "Reserve"]
    IN SignTx(updated)

BeginExecution(tx) ==
    SignTx([tx EXCEPT !.phase = "Executing"])

BeginCommitting(tx) ==
    SignTx([tx EXCEPT !.phase = "Committing"])

BeginRollback(tx, reason) ==
    SignTx([tx EXCEPT !.phase = "Rollback", !.result = reason])

AddOutput(tx, newUtxo) ==
    SignTx([tx EXCEPT
        !.outputs = tx.outputs \cup {newUtxo},
        !.writeSet = tx.writeSet \cup {newUtxo.id}])

CommitTransaction(tx) ==
    SignTx([tx EXCEPT !.phase = "Committed", !.result = "Complete"])

AbortTransaction(tx, reason) ==
    SignTx([tx EXCEPT !.phase = "Failed", !.result = reason])

UpdateCoordination(tx, newCoord) ==
    SignTx([tx EXCEPT !.coordination = newCoord])

ExecuteCallInTx(tx, callResult) ==
    LET newCoord == ExecuteNextCall(tx.coordination, callResult)
        updated == [tx EXCEPT !.coordination = newCoord]
    IN SignTx(updated)

RaiseEffectInTx(tx, effectKind, utxoId, continuationId, tag, payload) ==
    LET newCoord == RaiseInCoordination(tx.coordination, effectKind, utxoId, continuationId, tag, payload)
        updated == [tx EXCEPT !.coordination = newCoord]
    IN SignTx(updated)

HandleEffectInTx(tx, handlerResult) ==
    LET newCoord == HandleEffectInCoord(tx.coordination, handlerResult)
        updated == [tx EXCEPT !.coordination = newCoord]
    IN SignTx(updated)

FinalizeOutputs(tx, outputSpecs, outputUtxos) ==
    LET updated ==
        [tx EXCEPT
            !.outputs = outputUtxos,
            !.coordination = CompleteCoordination(BeginFinalizing(tx.coordination, outputSpecs)),
            !.writeSet = tx.writeSet \cup {u.id : u \in outputUtxos}]
    IN SignTx(updated)

(***************************************************************************
 * PROOF OPERATIONS IN TRANSACTION
 ***************************************************************************)

\* Add a proof commitment to the transaction
AddProofToTx(tx, proof) ==
    SignTx([tx EXCEPT !.proofCommitments = @ \cup {proof}])

\* Remove a proof commitment from the transaction
RemoveProofFromTx(tx, proof) ==
    SignTx([tx EXCEPT !.proofCommitments = @ \ {proof}])

\* Begin proof generation for the transaction
BeginTxProofGen(tx, proof) ==
    LET updatedProof == BeginProofGeneration(proof)
    IN SignTx([tx EXCEPT
        !.proofCommitments = (@ \ {proof}) \cup {updatedProof},
        !.proofPhase = "Generating"])

\* Mark a proof as verified in the transaction
MarkTxProofVerified(tx, proof) ==
    LET updatedProof == MarkProofVerified(proof)
        newCommitments == (tx.proofCommitments \ {proof}) \cup {updatedProof}
        allVerified == \A p \in newCommitments : IsVerifiedProof(p)
    IN SignTx([tx EXCEPT
        !.proofCommitments = newCommitments,
        !.proofPhase = IF allVerified THEN "Verified" ELSE @])

\* Mark a proof as failed in the transaction
MarkTxProofFailed(tx, proof) ==
    LET updatedProof == MarkProofFailed(proof)
    IN SignTx([tx EXCEPT
        !.proofCommitments = (@ \ {proof}) \cup {updatedProof},
        !.proofPhase = "Failed"])

\* Update transaction proof phase
UpdateTxProofPhase(tx, newPhase) ==
    SignTx([tx EXCEPT !.proofPhase = newPhase])

\* Check if all transaction proofs are verified
AllTxProofsVerified(tx) ==
    /\ tx.proofCommitments # {}
    /\ \A p \in tx.proofCommitments : IsVerifiedProof(p)

\* Check if any transaction proof failed
AnyTxProofFailed(tx) ==
    \E p \in tx.proofCommitments : IsFailedProof(p)

\* Check if transaction has pending proofs
HasPendingProofs(tx) ==
    \E p \in tx.proofCommitments : IsPendingProof(p)

(***************************************************************************
 * TRANSACTION INVARIANTS
 ***************************************************************************)

ValidInputs(tx) ==
    IsExecutingTx(tx) => \A u \in tx.inputs : u.state = "Suspended_at_Yield"

ValidOutputs(tx) ==
    \A u \in tx.outputs : u.state \in {"Created", "Suspended_at_Yield"}

InputOutputDisjoint(tx) ==
    {u.id : u \in tx.inputs} \cap {u.id : u \in tx.outputs} = {}

CommittedPreservesBalance(tx) ==
    IsCommittedTx(tx) => BalancePreserved(tx)

UniqueOutputIds(tx) ==
    \A u1, u2 \in tx.outputs : u1 # u2 => u1.id # u2.id

=============================================================================
