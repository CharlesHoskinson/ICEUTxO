----------------------- MODULE MC_StarstreamOptimistic -----------------------
(***************************************************************************
 * Model Checking Configuration for Starstream Optimistic Spec
 ***************************************************************************)

EXTENDS StarstreamSpecOptimistic, StarstreamInvariants, TLC

(***************************************************************************
 * CONSTANT DEFINITIONS FOR MODEL CHECKING
 ***************************************************************************)

MC_MAX_UTXOS == 3
MC_MAX_TX_INPUTS == 2
MC_MAX_TX_OUTPUTS == 2
MC_MAX_FRAME_VARS == 4
MC_MAX_PENDING_TXS == 2
MC_UTXO_ID_BOUND == 8

MC_TOKEN_TYPES == {"ADA", "NFT"}
MC_TOKEN_IDS == {1, 2, 3}

MC_MAX_TOKEN_TOTAL == 4
MC_CHAIN_ID == 1
MC_BLOCK_HEIGHT == 0

MC_MAX_EFFECT_DEPTH == MC_MAX_TX_INPUTS

(***************************************************************************
 * CONSTANT OVERRIDES
 ***************************************************************************)

TokenTypeSymmetry == Permutations(MC_TOKEN_TYPES)
OwnerSymmetry == Permutations({"Alice", "Bob", "Charlie"})

(***************************************************************************
 * STATE CONSTRAINTS
 ***************************************************************************)

MC_StateConstraint ==
    /\ Cardinality(ledger.utxoSet) <= MC_MAX_UTXOS
    /\ Cardinality(ledger.consumedSet) <= MC_UTXO_ID_BOUND
    /\ Cardinality(ledger.pendingTxs) <= MC_MAX_PENDING_TXS
    /\ ledger.nextUtxoId <= MC_UTXO_ID_BOUND + 1
    /\ \A tx \in ledger.pendingTxs :
        /\ Len(tx.coordination.effectStack) <= MC_MAX_EFFECT_DEPTH
        /\ Len(tx.coordination.pendingCalls) <= MC_MAX_TX_INPUTS
    /\ Len(ledger.txHistory) <= 3

(***************************************************************************
 * ACTION CONSTRAINTS
 ***************************************************************************)

MC_ActionConstraint == TRUE

(***************************************************************************
 * INVARIANTS TO CHECK
 ***************************************************************************)

MC_TypeOK == TypeOK

MC_NoDoubleSpend == INV_LINEAR_NoDoubleSpend
MC_BalancePreserved == INV_BALANCE_TxPreserved
MC_ConsumedTracked == INV_LINEAR_ConsumedTracked
MC_ConsumedIsFinal == INV_LIFECYCLE_ConsumedIsFinal
MC_EffectsMustBeHandled == INV_EFFECT_MustBeHandled
MC_NoReplay == INV_ATK_NoReplay
MC_PendingInputsNotConsumed == INV_LINEAR_PendingInputsNotConsumed
MC_OptEffectSourceSuspended == INV_OPT_EFFECT_SourceSuspended
MC_OptEffectContinuationMatch == INV_OPT_EFFECT_ContinuationMatch
MC_EffectStackDepthBounded == INV_EFFECT_StackDepthBounded
MC_PendingOutputsNoNFTDuplication == INV_BALANCE_PendingOutputsNoNFTDuplication
MC_LockAtomicRelease == INV_LOCK_AtomicRelease
MC_NoOverflow == INV_BALANCE_NoOverflow
MC_OptReadSetConsistent == INV_OPT_ReadSetConsistent
MC_OptWriteSetConsistent == INV_OPT_WriteSetConsistent

MC_OptSafety ==
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
    /\ INV_LOCK_Exclusive
    /\ INV_LOCK_ValidReservation
    /\ INV_LOCK_ConsistentSet
    /\ INV_LOCK_AtomicRelease
    /\ INV_LIFECYCLE_ConsumedIsFinal
    /\ INV_EFFECT_MustBeHandled
    /\ INV_OPT_EFFECT_SourceSuspended
    /\ INV_OPT_EFFECT_ContinuationMatch
    /\ INV_EFFECT_StackDepthBounded
    /\ INV_ATK_NoReplay
    /\ INV_ATK_IdMonotonic
    /\ INV_ATK_NoNegativeTokens
    /\ INV_ROLLBACK_NoLeak
    /\ INV_OPT_ReadSetConsistent
    /\ INV_OPT_WriteSetConsistent
    /\ INV_IEUTXO_PendingShape
    /\ INV_IEUTXO_CommittingNonEmpty
    /\ INV_IEUTXO_PendingOutputsFresh
    /\ INV_IEUTXO_PendingOutputsDistinct
    /\ INV_IEUTXO_CommittingInputsValidate
    /\ INV_IEUTXO_CommittingProofsVerified
    /\ INV_IEUTXO_CommittedHistoryChunk
    /\ INV_PROOF_CommittedVerified

(***************************************************************************
 * LIVENESS PROPERTIES TO CHECK
 ***************************************************************************)

MC_TxTerminates == LIVE_TxEventuallyTerminates
MC_TxCommits == LIVE_TxEventuallyCommits
MC_IdleReachable == LIVE_CanReturnToIdle
MC_EffectsHandled == LIVE_EffectsEventuallyHandled

(***************************************************************************
 * SPECIFICATION VARIANTS
 ***************************************************************************)

MC_Spec == OptSpec
MC_FairSpec == OptFairSpec
MC_StrongFairSpec == OptStrongFairSpec

=============================================================================
