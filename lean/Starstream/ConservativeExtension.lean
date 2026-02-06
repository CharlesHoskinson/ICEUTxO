import Mathlib
import StarstreamPilot

/-!
# Conservative Extension: eUTxO embeds into ICE-UTxO

Proposition 4.17: there exists a structure-preserving embedding from
plain eUTxO ledger states to ICE-UTxO states such that:

1. Every simple eUTxO commit lifts to a valid ICE-UTxO `Step.commit`.
2. Safety properties (no double-spend, input liveness, output freshness)
   coincide on the image of the embedding.
3. The ICE-UTxO machinery (effects, handlers, coordination) is inert on
   embedded states.

The key idea: a "simple" eUTxO transaction has no effects, no handlers,
no coordination, and a trivially-verified proof commitment. The embedding
maps such transactions into ICE-UTxO with empty handler stacks, empty
effect queues, and a singleton proof commitment in the Verified phase.
-/

namespace Starstream.ConservativeExtension

open Starstream

/-! ## Simple eUTxO types -/

/-- A simple eUTxO transaction: just inputs, outputs, and an id.
    No effects, no handlers, no coordination. -/
structure SimpleTx where
  id      : TxId
  inputs  : Finset UTXOId
  outputs : Finset UTXOId

/-- A simple eUTxO ledger: just utxos and consumed sets. -/
structure SimpleLedger where
  utxos    : Finset UTXOId
  consumed : Finset UTXOId

/-- Simple validity for an eUTxO transaction. -/
def simpleValidTx (sl : SimpleLedger) (stx : SimpleTx) : Prop :=
  stx.inputs.Nonempty ∧
  stx.outputs.Nonempty ∧
  Disjoint stx.inputs stx.outputs ∧
  stx.inputs ⊆ sl.utxos ∧
  Disjoint stx.outputs (sl.utxos ∪ sl.consumed)

/-- Apply a simple commit: consume inputs, produce outputs. -/
def simpleApplyCommit (sl : SimpleLedger) (stx : SimpleTx) : SimpleLedger :=
  { utxos    := (sl.utxos \ stx.inputs) ∪ stx.outputs
    consumed := sl.consumed ∪ stx.inputs }

/-- No double-spend for simple ledger. -/
def simpleNoDoubleSpend (sl : SimpleLedger) : Prop :=
  Disjoint sl.utxos sl.consumed

/-! ## Trivial proof commitment -/

/-- A trivially verified proof commitment for embedding purposes. -/
def trivialProof : ProofCommitment :=
  { proofKind  := 0
    processId  := 0
    commitHash := 0
    verifyKey  := 0
    phase      := ProofPhase.verified
    stepNumber := 0 }

theorem trivialProof_verified : trivialProof.phase = ProofPhase.verified := rfl

/-! ## Embedding -/

/-- Embed a simple transaction into an ICE-UTxO transaction.
    The embedded tx is in committing phase, has empty read/write sets,
    and a single trivially-verified proof commitment. -/
def embedTx (stx : SimpleTx) : Tx :=
  { id               := stx.id
    inputs           := stx.inputs
    outputs          := stx.outputs
    readSet          := ∅
    writeSet         := ∅
    proofCommitments := [trivialProof]
    phase            := TxPhase.committing }

/-- Embed a simple ledger into an ICE-UTxO ledger.
    Handler stacks, effect queues, pending, locked, history are all empty. -/
def embedLedger (sl : SimpleLedger) : Ledger :=
  { utxos         := sl.utxos
    consumed      := sl.consumed
    locked        := sl.utxos  -- all utxos locked (for locking mode)
    pending       := {embedTx ⟨0, ∅, ∅⟩}  -- placeholder, overridden per-use
    history       := []
    effects       := fun _ => []
    handlerStacks := fun _ => [] }

/-- Embed a simple ledger with a specific transaction in the pending set. -/
def embedLedgerWith (sl : SimpleLedger) (stx : SimpleTx) : Ledger :=
  { utxos         := sl.utxos
    consumed      := sl.consumed
    locked        := sl.utxos
    pending       := {embedTx stx}
    history       := []
    effects       := fun _ => []
    handlerStacks := fun _ => [] }

/-! ## Embedding preserves structure -/

theorem embedTx_inputs (stx : SimpleTx) :
    (embedTx stx).inputs = stx.inputs := rfl

theorem embedTx_outputs (stx : SimpleTx) :
    (embedTx stx).outputs = stx.outputs := rfl

theorem embedTx_phase (stx : SimpleTx) :
    (embedTx stx).phase = TxPhase.committing := rfl

theorem embedTx_readSet (stx : SimpleTx) :
    (embedTx stx).readSet = ∅ := rfl

theorem embedTx_writeSet (stx : SimpleTx) :
    (embedTx stx).writeSet = ∅ := rfl

/-! ## The embedded transaction has verified proofs -/

theorem embed_allProofsVerified (stx : SimpleTx) :
    allProofsVerified (embedTx stx) := by
  constructor
  · simp [embedTx]
  · intro p hp
    simp [embedTx] at hp
    subst hp
    exact trivialProof_verified

/-! ## Validity transfers -/

theorem embed_validTx (sl : SimpleLedger) (stx : SimpleTx)
    (hvalid : simpleValidTx sl stx) :
    validTx (embedLedgerWith sl stx) (embedTx stx) := by
  obtain ⟨hne_in, hne_out, hdisj, hlive, hfresh⟩ := hvalid
  exact ⟨hne_in, hne_out, hdisj, hlive, hfresh⟩

/-- Read set is trivially valid since it's empty. -/
theorem embed_readSetValid (sl : SimpleLedger) (stx : SimpleTx) :
    readSetValid (embedLedgerWith sl stx) (embedTx stx) := by
  simp [readSetValid, embedTx]

/-! ## CommitEnabledStrong holds for embedded transactions -/

theorem embed_commitEnabledStrong_locking (sl : SimpleLedger) (stx : SimpleTx)
    (hvalid : simpleValidTx sl stx) :
    commitEnabledStrong Mode.locking (embedLedgerWith sl stx) (embedTx stx) := by
  refine ⟨embed_allProofsVerified stx, embed_validTx sl stx hvalid,
          embedTx_phase stx, ?_, ?_⟩
  · -- tx ∉ history (history is [])
    simp [embedLedgerWith]
  · -- locking: inputs ⊆ locked ∧ readSetValid
    constructor
    · -- inputs ⊆ locked = sl.utxos
      exact hvalid.2.2.2.1
    · exact embed_readSetValid sl stx

theorem embed_commitEnabledStrong_optimistic (sl : SimpleLedger) (stx : SimpleTx)
    (hvalid : simpleValidTx sl stx) :
    commitEnabledStrong Mode.optimistic (embedLedgerWith sl stx) (embedTx stx) := by
  refine ⟨embed_allProofsVerified stx, embed_validTx sl stx hvalid,
          embedTx_phase stx, ?_, ?_⟩
  · simp [embedLedgerWith]
  · constructor
    · exact embed_readSetValid sl stx
    · exact hvalid.2.2.2.2

/-! ## Step lifting: simple eUTxO commit lifts to ICE-UTxO commit -/

/-- Every valid simple eUTxO commit lifts to a valid ICE-UTxO Step.commit
    in locking mode. -/
theorem embed_step_lifts_locking (sl : SimpleLedger) (stx : SimpleTx)
    (hvalid : simpleValidTx sl stx) :
    Step Mode.locking
      (embedLedgerWith sl stx)
      (applyCommit (embedLedgerWith sl stx) (embedTx stx)) := by
  apply Step.commit
  · -- tx ∈ pending
    simp [embedLedgerWith]
  · exact embed_commitEnabledStrong_locking sl stx hvalid
  · exact precGraphAcyclicExt_of_history _
  · exact fullPrecGraphAcyclic_of_history _

/-- Every valid simple eUTxO commit lifts to a valid ICE-UTxO Step.commit
    in optimistic mode. -/
theorem embed_step_lifts_optimistic (sl : SimpleLedger) (stx : SimpleTx)
    (hvalid : simpleValidTx sl stx) :
    Step Mode.optimistic
      (embedLedgerWith sl stx)
      (applyCommit (embedLedgerWith sl stx) (embedTx stx)) := by
  apply Step.commit
  · simp [embedLedgerWith]
  · exact embed_commitEnabledStrong_optimistic sl stx hvalid
  · exact precGraphAcyclicExt_of_history _
  · exact fullPrecGraphAcyclic_of_history _

/-! ## Safety properties coincide on the image of the embedding -/

/-- No double-spend coincides: the ICE-UTxO property on the embedded ledger
    is equivalent to the simple eUTxO property. -/
theorem embed_noDoubleSpend_iff (sl : SimpleLedger) :
    noDoubleSpend (embedLedgerWith sl ⟨0, ∅, ∅⟩) ↔ simpleNoDoubleSpend sl := by
  simp [noDoubleSpend, simpleNoDoubleSpend, embedLedgerWith]

/-- Input liveness coincides. -/
theorem embed_inputsLive_iff (sl : SimpleLedger) (stx : SimpleTx) :
    inputsLive (embedLedgerWith sl stx) (embedTx stx) ↔
    stx.inputs ⊆ sl.utxos := by
  simp [inputsLive, embedLedgerWith, embedTx]

/-- Output freshness coincides. -/
theorem embed_outputsFresh_iff (sl : SimpleLedger) (stx : SimpleTx) :
    outputsFresh (embedLedgerWith sl stx) (embedTx stx) ↔
    Disjoint stx.outputs (sl.utxos ∪ sl.consumed) := by
  simp [outputsFresh, embedLedgerWith, embedTx]

/-! ## ICE machinery is inert on embedded states -/

/-- No effects are pending on any interface in the embedded ledger. -/
theorem embed_noPendingEffects (sl : SimpleLedger) (stx : SimpleTx) :
    noPendingEffects (embedLedgerWith sl stx) := by
  intro i
  simp [embedLedgerWith]

/-- No handlers are installed on any interface in the embedded ledger. -/
theorem embed_noHandlers (sl : SimpleLedger) (stx : SimpleTx) :
    ∀ i, (embedLedgerWith sl stx).handlerStacks i = [] := by
  intro i
  simp [embedLedgerWith]

/-- The embedded ledger has empty history. -/
theorem embed_emptyHistory (sl : SimpleLedger) (stx : SimpleTx) :
    (embedLedgerWith sl stx).history = [] := by
  simp [embedLedgerWith]

/-! ## Core state projection commutes with embedding -/

/-- The core state of the embedded ledger matches the simple ledger. -/
theorem embed_coreOf (sl : SimpleLedger) (stx : SimpleTx) :
    coreOf (embedLedgerWith sl stx) = ⟨sl.utxos, sl.consumed⟩ := by
  simp [coreOf, embedLedgerWith]

/-- Applying commit on embedded state projects to simple commit. -/
theorem embed_commit_core (sl : SimpleLedger) (stx : SimpleTx) :
    coreOf (applyCommit (embedLedgerWith sl stx) (embedTx stx)) =
    ⟨(sl.utxos \ stx.inputs) ∪ stx.outputs, sl.consumed ∪ stx.inputs⟩ := by
  simp [coreOf, applyCommit, embedLedgerWith, embedTx]

/-- Core state after ICE-UTxO commit equals core state after simple commit.
    This is the key coherence property: the embedding commutes with commits
    at the core state level. -/
theorem embed_commit_coherent (sl : SimpleLedger) (stx : SimpleTx) :
    coreOf (applyCommit (embedLedgerWith sl stx) (embedTx stx)) =
    applyCoreCommit (coreOf (embedLedgerWith sl stx)) (embedTx stx) := by
  rw [coreOf_applyCommit]

/-! ## CommitEnabledStrong degenerates to simple validation -/

/-- On embedded transactions, commitEnabledStrong reduces to simple eUTxO
    validation: inputs live, outputs fresh, inputs disjoint from outputs.
    The proof, phase, and mode machinery all collapse. -/
theorem embed_commitEnabledStrong_reduces_locking (sl : SimpleLedger) (stx : SimpleTx) :
    commitEnabledStrong Mode.locking (embedLedgerWith sl stx) (embedTx stx) ↔
    simpleValidTx sl stx := by
  constructor
  · intro ⟨_, hvalid, _, _, _⟩
    exact hvalid
  · exact embed_commitEnabledStrong_locking sl stx

theorem embed_commitEnabledStrong_reduces_optimistic (sl : SimpleLedger) (stx : SimpleTx) :
    commitEnabledStrong Mode.optimistic (embedLedgerWith sl stx) (embedTx stx) ↔
    simpleValidTx sl stx := by
  constructor
  · intro ⟨_, hvalid, _, _, _⟩
    exact hvalid
  · exact embed_commitEnabledStrong_optimistic sl stx

/-! ## Ledger invariant holds on embedded initial states -/

/-- An embedded simple ledger with no-double-spend satisfies the full
    ICE-UTxO ledger invariant. -/
theorem embed_ledgerInvariant (sl : SimpleLedger)
    (hds : simpleNoDoubleSpend sl) :
    ledgerInvariant (embedLedgerWith sl ⟨0, ∅, ∅⟩) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- noDoubleSpend
    exact (embed_noDoubleSpend_iff sl).mpr hds
  · -- lockedSubsetActive
    simp [lockedSubsetActive, embedLedgerWith]
  · -- historyNodup
    simp [historyNodup, embedLedgerWith]
  · -- committedImpliesVerified
    simp [committedImpliesVerified, embedLedgerWith]
  · -- precGraphAcyclicExt
    simp [embedLedgerWith]
    exact precGraphAcyclicExt_of_history []
  · -- fullPrecGraphAcyclic
    simp [embedLedgerWith]
    exact fullPrecGraphAcyclic_of_history []

end Starstream.ConservativeExtension
