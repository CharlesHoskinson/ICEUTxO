--------------------------- MODULE MC_Starstream ---------------------------
(***************************************************************************
 * Model Checking Configuration for Starstream TLA+ Specification
 ***************************************************************************)

EXTENDS StarstreamSpec, StarstreamInvariants, TLC

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

\* IVC-aligned constants
MC_MAX_COORDINATORS == 2
MC_MAX_INTERFACES == 3
MC_MAX_HANDLER_DEPTH == 2
MC_MAX_EFFECT_FUEL == 5      \* Maximum fuel per effect for termination

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
        /\ \A iface \in InterfaceIdRange :
            Len(tx.coordination.handlerStacks[iface]) <= MC_MAX_HANDLER_DEPTH
        /\ Cardinality(tx.proofCommitments) <= MC_MAX_TX_INPUTS
    /\ Len(ledger.txHistory) <= 3
    /\ Cardinality(ledger.proofStore) <= MC_MAX_PENDING_TXS * MC_MAX_TX_INPUTS

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
MC_EffectSourceSuspended == INV_EFFECT_SourceSuspended
MC_EffectContinuationMatch == INV_EFFECT_ContinuationMatch
MC_EffectStackDepthBounded == INV_EFFECT_StackDepthBounded
MC_PendingOutputsNoNFTDuplication == INV_BALANCE_PendingOutputsNoNFTDuplication
MC_LockAtomicRelease == INV_LOCK_AtomicRelease
MC_NoOverflow == INV_BALANCE_NoOverflow

\* Handler stack invariants (IVC alignment)
MC_EffectInterfaceConsistent == INV_EFFECT_InterfaceConsistent
MC_EffectPerInterfaceDepth == INV_EFFECT_PerInterfaceDepth
MC_EffectMatchInstalledHandlers == INV_EFFECT_EffectsMatchInstalledHandlers
MC_EffectInstalledHandlersConsistent == INV_EFFECT_InstalledHandlersConsistent
MC_EffectValidHandlerStacks == INV_EFFECT_ValidHandlerStacks

\* Effect termination invariants
MC_EffectFuelBounded == INV_EFFECT_FuelBounded
MC_EffectPotentialBounded == INV_EFFECT_PotentialBounded

\* Proof invariants (IVC alignment)
MC_ProofIntegrityBound == INV_PROOF_IntegrityBound
MC_ProofNoDoubleProof == INV_PROOF_NoDoubleProof
MC_ProofVerificationInvariant == INV_PROOF_VerificationInvariant
MC_ProofConsistentPhase == INV_PROOF_ConsistentPhase
MC_ProofActiveProofsConsistent == INV_PROOF_ActiveProofsConsistent
MC_ProofTxProofsInLedger == INV_PROOF_TxProofsInLedger
MC_ProofValidIVCConfig == INV_PROOF_ValidIVCConfig

MC_Safety == INV_Safety

(***************************************************************************
 * LIVENESS PROPERTIES TO CHECK
 ***************************************************************************)

MC_TxTerminates == LIVE_TxEventuallyTerminates
MC_TxCommits == LIVE_TxEventuallyCommits
MC_IdleReachable == LIVE_CanReturnToIdle
MC_EffectsHandled == LIVE_EffectsEventuallyHandled
MC_EffectTermination == LIVE_EffectTermination

(***************************************************************************
 * SPECIFICATION VARIANTS
 ***************************************************************************)

MC_Spec == Spec
MC_FairSpec == FairSpec
MC_StrongFairSpec == StrongFairSpec

(***************************************************************************
 * TRACE EXPLORATION HELPERS
 ***************************************************************************)

MC_FindDoubleSpend == ~INV_LINEAR_NoDoubleSpend
MC_FindBalanceViolation == ~INV_BALANCE_TxPreserved
MC_FindCompletedTx ==
    Len(ledger.txHistory) > 0 /\
    \E i \in 1..Len(ledger.txHistory) : IsCommittedTx(ledger.txHistory[i])

MC_FindFailedTx ==
    Len(ledger.txHistory) > 0 /\
    \E i \in 1..Len(ledger.txHistory) : IsFailedTx(ledger.txHistory[i])

=============================================================================
