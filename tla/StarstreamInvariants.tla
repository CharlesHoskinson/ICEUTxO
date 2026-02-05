------------------------ MODULE StarstreamInvariants ------------------------
(***************************************************************************
 * Invariants and Properties for Starstream UTXO/Transaction Protocol
 ***************************************************************************)

EXTENDS StarstreamTypes, StarstreamFrame, StarstreamUTXO, StarstreamEffects,
        StarstreamCoordination, StarstreamTransaction, StarstreamLedger, StarstreamSpec,
        StarstreamAuth, StarstreamProof, StarstreamCircuitAlignment

(***************************************************************************
 * TYPE INVARIANTS
 ***************************************************************************)

INV_TYPE_LedgerWellTyped ==
    IsValidLedger(ledger)

INV_TYPE_FramesWellTyped ==
    \A u \in ledger.utxoSet : IsFrame(u.frame)

INV_TYPE_TokenBagsWellTyped ==
    \A u \in ledger.utxoSet : IsValidTokenBag(u.tokens)

INV_TYPE_PendingTxWellTyped ==
    \A tx \in ledger.pendingTxs : IsTransactionRecord(tx)

INV_TYPE_All ==
    /\ TypeOK
    /\ INV_TYPE_LedgerWellTyped
    /\ INV_TYPE_FramesWellTyped
    /\ INV_TYPE_TokenBagsWellTyped
    /\ INV_TYPE_PendingTxWellTyped

(***************************************************************************
 * AUTHORIZATION INVARIANTS
 ***************************************************************************)

INV_AUTH_ValidSpend ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsCommittedTx(tx) => ValidSignature(tx.signature, tx)

INV_AUTH_OwnerOnly ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsCommittedTx(tx) => InputsOwnedBySigner(tx)

(***************************************************************************
 * BALANCE INVARIANTS
 ***************************************************************************)

INV_BALANCE_TxPreserved ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsCommittedTx(tx) => BalancePreserved(tx)

INV_BALANCE_PendingTxValid ==
    \A tx \in ledger.pendingTxs :
        IsComplete(tx.coordination) => BalancePreserved(tx)

INV_BALANCE_NFTUnique ==
    \A id \in TOKEN_IDS :
        Cardinality({u \in ledger.utxoSet : u.tokens["NFT"][id] > 0}) <= 1

INV_BALANCE_PendingOutputsNoNFTDuplication ==
    \A tx \in ledger.pendingTxs :
        IsComplete(tx.coordination) =>
            \A id \in TOKEN_IDS :
                LET outputsWithNft ==
                        {u \in tx.outputs : u.tokens["NFT"][id] > 0}
                    otherUtxos ==
                        {u \in ledger.utxoSet :
                            /\ u.id \notin {i.id : i \in tx.inputs}
                            /\ u.tokens["NFT"][id] > 0}
                IN /\ Cardinality(outputsWithNft) <= 1
                   /\ otherUtxos = {}

INV_BALANCE_NoOverflow ==
    /\ \A tx \in ledger.pendingTxs :
        \A t \in TOKEN_TYPES : \A id \in TOKEN_IDS :
            /\ SumInputTokens(tx)[t][id] <= MAX_TOKEN_TOTAL
            /\ SumOutputTokens(tx)[t][id] <= MAX_TOKEN_TOTAL
    /\ \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        \A t \in TOKEN_TYPES : \A id \in TOKEN_IDS :
            /\ SumInputTokens(tx)[t][id] <= MAX_TOKEN_TOTAL
            /\ SumOutputTokens(tx)[t][id] <= MAX_TOKEN_TOTAL

(***************************************************************************
 * LINEAR TYPE INVARIANTS
 ***************************************************************************)

INV_LINEAR_NoDoubleSpend ==
    {u.id : u \in ledger.utxoSet} \cap ledger.consumedSet = {}

INV_LINEAR_ConsumedTracked ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsCommittedTx(tx) => \A u \in tx.inputs : u.id \in ledger.consumedSet

INV_LINEAR_UniqueActiveIds ==
    \A u1, u2 \in ledger.utxoSet : u1 # u2 => u1.id # u2.id

INV_LINEAR_NoDoubleConsume ==
    \A tx1, tx2 \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        (tx1 # tx2 /\ IsCommittedTx(tx1) /\ IsCommittedTx(tx2)) =>
            ({u.id : u \in tx1.inputs} \cap {u.id : u \in tx2.inputs} = {})

INV_LINEAR_NoDuplication ==
    \A tx1, tx2 \in ledger.pendingTxs :
        (tx1 # tx2) =>
            ({u.id : u \in tx1.inputs} \cap {u.id : u \in tx2.inputs} = {})

INV_LINEAR_PendingInputsNotConsumed ==
    \A tx \in ledger.pendingTxs :
        ({u.id : u \in tx.inputs} \cap ledger.consumedSet = {})

(***************************************************************************
 * IEUTXO/CHUNK INVARIANTS
 ***************************************************************************) 

RECURSIVE FilterCommitted(_)
FilterCommitted(txs) ==
    IF txs = <<>> THEN <<>>
    ELSE LET tail == IF Len(txs) <= 1 THEN <<>> ELSE SubSeq(txs, 2, Len(txs))
         IN IF IsCommittedTx(txs[1])
            THEN <<txs[1]>> \o FilterCommitted(tail)
            ELSE FilterCommitted(tail)

CommittedHistory == FilterCommitted(ledger.txHistory)

INV_IEUTXO_PendingShape ==
    \A tx \in ledger.pendingTxs :
        /\ UniqueInputIds(tx)
        /\ UniqueOutputIds(tx)
        /\ InputOutputDisjoint(tx)

INV_IEUTXO_CommittingNonEmpty ==
    \A tx \in ledger.pendingTxs :
        tx.phase = "Committing" => TxNonEmpty(tx)

INV_IEUTXO_PendingOutputsFresh ==
    \A tx \in ledger.pendingTxs :
        OutputIds(tx) \cap (UTXOIds(ledger.utxoSet) \cup ledger.consumedSet) = {}

INV_IEUTXO_PendingOutputsDistinct ==
    \A tx1, tx2 \in ledger.pendingTxs :
        tx1 # tx2 => OutputIds(tx1) \cap OutputIds(tx2) = {}

INV_IEUTXO_CommittingInputsValidate ==
    \A tx \in ledger.pendingTxs :
        tx.phase = "Committing" => TxInputsValidate(ledger, tx)

INV_IEUTXO_CommittingProofsVerified ==
    \A tx \in ledger.pendingTxs :
        tx.phase = "Committing" => AllTxProofsVerified(tx)

INV_IEUTXO_CommittedHistoryChunk ==
    ChunkValid(CommittedHistory)

(***************************************************************************
 * LOCK/RESERVATION INVARIANTS
 ***************************************************************************)

INV_LOCK_Exclusive ==
    \A u \in ledger.utxoSet :
        u.lockedBy = NO_TX \/ (\E tx \in ledger.pendingTxs : tx.id = u.lockedBy)

INV_LOCK_ValidReservation ==
    \A u \in ledger.utxoSet :
        u.lockedBy # NO_TX => u.state \in {"Reserved", "Executing", "Suspended_at_Effect"}

INV_LOCK_ConsistentSet ==
    LockedSetConsistent(ledger)

INV_LOCK_AtomicRelease ==
    \A u \in ledger.utxoSet :
        u.state \in {"Reserved", "Executing", "Suspended_at_Effect"} => u.lockedBy # NO_TX

(***************************************************************************
 * OPTIMISTIC CONCURRENCY INVARIANTS
 ***************************************************************************)

INV_OPT_ReadSetConsistent ==
    \A tx \in ledger.pendingTxs :
        tx.readSet = {u.id : u \in tx.readSnapshot}

INV_OPT_WriteSetConsistent ==
    \A tx \in ledger.pendingTxs :
        tx.writeSet = {u.id : u \in tx.inputs} \cup {u.id : u \in tx.outputs}

(***************************************************************************
 * LIFECYCLE INVARIANTS
 ***************************************************************************)

INV_LIFECYCLE_ConsumedIsFinal ==
    \A u \in ledger.utxoSet : u.state # "Consumed"

INV_LIFECYCLE_ActiveAreLive ==
    \A u \in ledger.utxoSet : IsLive(u)

INV_LIFECYCLE_FrameConsistent ==
    \A u \in ledger.utxoSet :
        /\ (u.state = "Created") => (u.frame.pc = 0)
        /\ (u.state = "Consumed") => (u.frame.pc = -1)
        /\ (u.state = "Suspended_at_Yield") => (u.frame.pc >= 0)
        /\ (u.state = "Suspended_at_Effect") => (u.frame.pc >= 0)

(***************************************************************************
 * EFFECT INVARIANTS
 ***************************************************************************)

INV_EFFECT_MustBeHandled ==
    \A tx \in ledger.pendingTxs :
        IsComplete(tx.coordination) => ~HasPendingEffects(tx.coordination)

INV_EFFECT_NoOrphans ==
    \A tx \in ledger.pendingTxs :
        \A e \in FcnRange(tx.coordination.effectStack) :
            e["sourceUtxoId"] \in {u["id"] : u \in tx.inputs}

INV_EFFECT_SourceSuspended ==
    \A tx \in ledger.pendingTxs :
        \A e \in PendingEffects(tx.coordination.effectStack) :
            /\ UTXOExistsInLedger(ledger, e["sourceUtxoId"])
            /\ LET u == GetUTXO(ledger, e["sourceUtxoId"])
               IN /\ u.state = "Suspended_at_Effect"
                  /\ u.lockedBy = tx.id

INV_EFFECT_ContinuationMatch ==
    \A tx \in ledger.pendingTxs :
        \A e \in PendingEffects(tx.coordination.effectStack) :
            /\ UTXOExistsInLedger(ledger, e["sourceUtxoId"])
            /\ LET u == GetUTXO(ledger, e["sourceUtxoId"])
               IN e["continuationId"] = u.frame.pc

INV_OPT_EFFECT_SourceSuspended ==
    \A tx \in ledger.pendingTxs :
        \A e \in PendingEffects(tx.coordination.effectStack) :
            \E u \in tx.inputs :
                /\ u.id = e["sourceUtxoId"]
                /\ u.state = "Suspended_at_Effect"

INV_OPT_EFFECT_ContinuationMatch ==
    \A tx \in ledger.pendingTxs :
        \A e \in PendingEffects(tx.coordination.effectStack) :
            \E u \in tx.inputs :
                /\ u.id = e["sourceUtxoId"]
                /\ e["continuationId"] = u.frame.pc

INV_EFFECT_StackDepthBounded ==
    \A tx \in ledger.pendingTxs :
        Len(tx.coordination.effectStack) <= MAX_EFFECT_DEPTH

(***************************************************************************
 * HANDLER STACK INVARIANTS (IVC Alignment)
 ***************************************************************************)

\* All effects target valid interfaces
INV_EFFECT_InterfaceConsistent ==
    \A tx \in ledger.pendingTxs :
        \A e \in FcnRange(tx.coordination.effectStack) :
            e.interfaceId \in InterfaceIdRange

\* Handler stacks are within depth bounds per interface
INV_EFFECT_PerInterfaceDepth ==
    \A tx \in ledger.pendingTxs :
        \A iface \in InterfaceIdRange :
            Len(tx.coordination.handlerStacks[iface]) <= MAX_HANDLER_DEPTH

\* Pending effects have handlers installed for their interface
INV_EFFECT_EffectsMatchInstalledHandlers ==
    \A tx \in ledger.pendingTxs :
        \A e \in PendingEffects(tx.coordination.effectStack) :
            HasHandlerFor(tx.coordination.handlerStacks, e.interfaceId)

\* Installed handlers set is consistent with handler stacks
INV_EFFECT_InstalledHandlersConsistent ==
    \A tx \in ledger.pendingTxs :
        InstalledHandlersConsistent(tx.coordination)

\* Handler stacks are well-formed
INV_EFFECT_ValidHandlerStacks ==
    \A tx \in ledger.pendingTxs :
        ValidHandlerStacks(tx.coordination)

(***************************************************************************
 * EFFECT TERMINATION INVARIANTS
 *
 * These invariants support the fuel-based termination proof.
 * The budget discipline ensures Σ(fuel+1) strictly decreases on each handle.
 ***************************************************************************)

\* All effects have fuel within valid range
INV_EFFECT_FuelBounded ==
    \A tx \in ledger.pendingTxs :
        \A e \in FcnRange(tx.coordination.effectStack) :
            e.fuel \in FuelRange

\* Sum of (fuel+1) over all pending effects (potential function)
TotalFuel(effectStack) ==
    LET effects == FcnRange(effectStack)
    IN IF effects = {} THEN 0
       ELSE FcnSum([e \in effects |-> e.fuel + 1])

\* Total potential is bounded by MAX_EFFECT_FUEL * MAX_EFFECT_DEPTH
INV_EFFECT_PotentialBounded ==
    \A tx \in ledger.pendingTxs :
        TotalFuel(tx.coordination.effectStack) <= MAX_EFFECT_FUEL * MAX_EFFECT_DEPTH

(***************************************************************************
 * PROOF INVARIANTS (IVC Alignment)
 ***************************************************************************)

\* All proofs in ledger have valid process IDs
INV_PROOF_IntegrityBound ==
    \A proof \in ledger.proofStore :
        proof.ivcProcessId \in ProcessIdRange /\ IsValidProof(proof)

\* No duplicate pending proofs for the same process ID
INV_PROOF_NoDoubleProof ==
    \A p1, p2 \in ledger.proofStore :
        (p1 # p2 /\ IsPendingProof(p1) /\ IsPendingProof(p2)) =>
            p1.ivcProcessId # p2.ivcProcessId

\* Verified proofs have consistent state
INV_PROOF_VerificationInvariant ==
    \A proof \in ledger.proofStore :
        IsVerifiedProof(proof) => proof.phase = "Verified" /\ proof.verified

\* Transaction proof phase is consistent with proof commitments
INV_PROOF_ConsistentPhase ==
    \A tx \in ledger.pendingTxs :
        (tx.proofPhase = "Verified") => \A p \in tx.proofCommitments : p.verified

\* All committed transactions had verified proofs
INV_PROOF_CommittedVerified ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsCommittedTx(tx) => AllTxProofsVerified(tx)

\* Active proofs set matches proof store
INV_PROOF_ActiveProofsConsistent ==
    ledger.activeProofs = {p.ivcProcessId : p \in ledger.proofStore}

\* Transaction proofs are in ledger proof store
INV_PROOF_TxProofsInLedger ==
    \A tx \in ledger.pendingTxs :
        \A p \in tx.proofCommitments :
            \E lp \in ledger.proofStore :
                lp.ivcProcessId = p.ivcProcessId

\* IVC configuration is valid in all coordinations
INV_PROOF_ValidIVCConfig ==
    \A tx \in ledger.pendingTxs :
        ValidIVCConfig(tx.coordination)

(***************************************************************************
 * CIRCUIT-ALIGNED INVARIANTS
 *
 * These invariants correspond to constraints enforced by the interleaving
 * proof circuit but not previously formalized in the TLA+ specification.
 * They are defined in StarstreamCircuitAlignment.tla and referenced here.
 ***************************************************************************)

INV_CIRCUIT_NoSelfResumeCheck ==
    INV_CIRCUIT_NoSelfResume

INV_CIRCUIT_ActivationConsistentCheck ==
    INV_CIRCUIT_ActivationConsistent

INV_CIRCUIT_RefArenaBoundedCheck ==
    INV_CIRCUIT_RefArenaBounded

INV_CIRCUIT_HandlerNodeLinkedCheck ==
    INV_CIRCUIT_HandlerNodeLinked

INV_CIRCUIT_InitializationConsistentCheck ==
    INV_CIRCUIT_InitializationConsistent

INV_CIRCUIT_EffectOpcodeSingleStepCheck ==
    INV_CIRCUIT_EffectOpcodeSingleStep

INV_CIRCUIT_DualTraceConsistencyCheck ==
    INV_CIRCUIT_DualTraceConsistency

INV_CIRCUIT_ValueCommitmentIntegrityCheck ==
    INV_CIRCUIT_ValueCommitmentIntegrity

(***************************************************************************
 * FRAME INTEGRITY INVARIANTS
 ***************************************************************************)

INV_FRAME_Integrity ==
    \A u \in ledger.utxoSet : u.frame.hash = ComputeFrameHash(u.frame.pc, u.frame.locals, u.frame.methodId)

(***************************************************************************
 * ATTACK PREVENTION INVARIANTS
 ***************************************************************************)

INV_ATK_NoReplay ==
    \A id \in ledger.consumedSet : ~(\E u \in ledger.utxoSet : u.id = id)

INV_ATK_IdMonotonic ==
    /\ \A u \in ledger.utxoSet : u.id < ledger.nextUtxoId
    /\ \A id \in ledger.consumedSet : id < ledger.nextUtxoId

INV_ATK_NoNegativeTokens ==
    \A u \in ledger.utxoSet :
        \A t \in TOKEN_TYPES : \A id \in TOKEN_IDS : u.tokens[t][id] >= 0

(***************************************************************************
 * ROLLBACK INVARIANTS
 ***************************************************************************)

INV_ROLLBACK_NoLeak ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsFailedTx(tx) =>
            /\ {u.id : u \in tx.outputs} \cap {u.id : u \in ledger.utxoSet} = {}
            /\ {u.id : u \in tx.inputs} \cap ledger.consumedSet = {}

(***************************************************************************
 * COMBINED SAFETY INVARIANTS
 ***************************************************************************)

INV_Safety ==
    /\ INV_TYPE_All
    /\ INV_AUTH_ValidSpend
    /\ INV_AUTH_OwnerOnly
    /\ INV_BALANCE_TxPreserved
    /\ INV_BALANCE_NFTUnique
    /\ INV_BALANCE_PendingOutputsNoNFTDuplication
    /\ INV_BALANCE_NoOverflow
    /\ INV_LINEAR_NoDoubleSpend
    /\ INV_LINEAR_ConsumedTracked
    /\ INV_LINEAR_UniqueActiveIds
    /\ INV_LINEAR_PendingInputsNotConsumed
    /\ INV_IEUTXO_PendingShape
    /\ INV_IEUTXO_CommittingNonEmpty
    /\ INV_IEUTXO_PendingOutputsFresh
    /\ INV_IEUTXO_PendingOutputsDistinct
    /\ INV_IEUTXO_CommittingInputsValidate
    /\ INV_IEUTXO_CommittingProofsVerified
    /\ INV_IEUTXO_CommittedHistoryChunk
    /\ INV_LOCK_Exclusive
    /\ INV_LOCK_ValidReservation
    /\ INV_LOCK_ConsistentSet
    /\ INV_LOCK_AtomicRelease
    /\ INV_OPT_ReadSetConsistent
    /\ INV_OPT_WriteSetConsistent
    /\ INV_LIFECYCLE_ConsumedIsFinal
    /\ INV_EFFECT_MustBeHandled
    /\ INV_EFFECT_SourceSuspended
    /\ INV_EFFECT_ContinuationMatch
    /\ INV_EFFECT_StackDepthBounded
    /\ INV_EFFECT_InterfaceConsistent
    /\ INV_EFFECT_PerInterfaceDepth
    /\ INV_EFFECT_ValidHandlerStacks
    /\ INV_PROOF_IntegrityBound
    /\ INV_PROOF_NoDoubleProof
    /\ INV_PROOF_VerificationInvariant
    /\ INV_PROOF_ConsistentPhase
    /\ INV_PROOF_CommittedVerified
    /\ INV_PROOF_ActiveProofsConsistent
    /\ INV_PROOF_ValidIVCConfig
    /\ INV_CIRCUIT_NoSelfResumeCheck
    /\ INV_CIRCUIT_ActivationConsistentCheck
    /\ INV_CIRCUIT_RefArenaBoundedCheck
    /\ INV_CIRCUIT_HandlerNodeLinkedCheck
    /\ INV_CIRCUIT_InitializationConsistentCheck
    /\ INV_CIRCUIT_EffectOpcodeSingleStepCheck
    /\ INV_CIRCUIT_DualTraceConsistencyCheck
    /\ INV_CIRCUIT_ValueCommitmentIntegrityCheck
    /\ INV_ATK_NoReplay
    /\ INV_ATK_IdMonotonic
    /\ INV_ATK_NoNegativeTokens
    /\ INV_ROLLBACK_NoLeak

(***************************************************************************
 * LIVENESS PROPERTIES
 ***************************************************************************) 

PendingTxId(txId) ==
    txId \in {t.id : t \in ledger.pendingTxs}

CommittedTxId(txId) ==
    \E tx \in ledger.txHistory : tx.id = txId /\ IsCommittedTx(tx)

CommitEnabled(txId) ==
    ENABLED CommitTx(txId)

LIVE_TxEventuallyCommits ==
    \A txId \in TxIdRange :
        (<>[]CommitEnabled(txId)) => <>CommittedTxId(txId)

LIVE_TxEventuallyTerminates ==
    \A txId \in TxIdRange :
        []( PendingTxId(txId) => <>~PendingTxId(txId) )

PendingTxHasEffects(txId) ==
    PendingTxId(txId) /\ HasPendingEffects(GetPendingTx(ledger, txId).coordination)

PendingTxEffectsCleared(txId) ==
    ~PendingTxId(txId) \/
        (PendingTxId(txId) /\ ~HasPendingEffects(GetPendingTx(ledger, txId).coordination))

LIVE_EffectsEventuallyHandled ==
    \A txId \in TxIdRange :
        PendingTxHasEffects(txId) ~> PendingTxEffectsCleared(txId)

\* Fuel-based termination: potential eventually reaches 0
\* Under fairness, effect handling steps keep occurring while effects exist
LIVE_EffectTermination ==
    \A txId \in TxIdRange :
        LET tx == GetPendingTx(ledger, txId)
        IN PendingTxId(txId) /\ TotalFuel(tx.coordination.effectStack) > 0 ~>
               TotalFuel(tx.coordination.effectStack) = 0

LIVE_CanReturnToIdle ==
    []<>(ledger.pendingTxs = {})

=============================================================================
