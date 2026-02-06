import Mathlib
import StarstreamPilot

/-!
# Optimistic Mode Specializations

The safety theorems in StarstreamPilot.lean are parametric in `m : Mode`.
This file provides explicit specializations to `Mode.optimistic`, making
the optimistic-mode guarantees first-class and removing the "pessimistic
mode only" caveat from the paper.

Results:
- `optimistic_step_preserves_invariant`: invariant preservation under optimistic steps
- `optimistic_concurrent_refines_serial`: concurrent-to-serial refinement
- `optimistic_reachable_ledgerInvariant`: reachable states satisfy the invariant
- `optimistic_snapshot_valid`: commit guard implies read set ⊆ utxos
- `optimistic_must_abort_if_snapshot_invalid`: negation of commit guard
- `optimistic_serializable`: serializability of optimistic histories
- `optimistic_strong_serializable`: strong serializability from invariant
-/

namespace Starstream.OptimisticMode

open Starstream

/-! ## Invariant preservation -/

/-- Every optimistic-mode step preserves the ledger invariant. -/
theorem optimistic_step_preserves_invariant {l l' : Ledger}
    (hstep : Step Mode.optimistic l l')
    (hinv : ledgerInvariant l) :
    ledgerInvariant l' :=
  step_preserves_invariant hstep hinv

/-- Multi-step invariant preservation in optimistic mode. -/
theorem optimistic_steps_preserve_invariant {l l' : Ledger}
    (hsteps : Steps Mode.optimistic l l')
    (hinv : ledgerInvariant l) :
    ledgerInvariant l' :=
  ledgerInvariant_steps hsteps hinv

/-- Reachable states from Init satisfy the invariant in optimistic mode. -/
theorem optimistic_reachable_ledgerInvariant {l₀ l : Ledger}
    (hinit : Init l₀) (hsteps : Steps Mode.optimistic l₀ l) :
    ledgerInvariant l :=
  reachable_ledgerInvariant hinit hsteps

/-! ## Refinement -/

/-- Every concurrent optimistic execution refines the serial spec. -/
theorem optimistic_concurrent_refines_serial {l₀ lₙ : Ledger}
    (hexec : Steps Mode.optimistic l₀ lₙ)
    (hinv : ledgerInvariant l₀) :
    SerialSteps Mode.optimistic (absLedger l₀) (absLedger lₙ) :=
  concurrent_refines_serial hexec hinv

/-! ## Snapshot validation -/

/-- In optimistic mode, commitEnabledStrong implies the read set is a
    subset of the live UTXO set (snapshot validity). -/
theorem optimistic_snapshot_valid {l : Ledger} {tx : Tx}
    (hen : commitEnabledStrong Mode.optimistic l tx) :
    tx.readSet ⊆ l.utxos := by
  obtain ⟨_, _, _, _, hrsv, _⟩ := hen
  exact hrsv

/-- In optimistic mode, commitEnabledStrong implies outputs are fresh. -/
theorem optimistic_outputs_fresh {l : Ledger} {tx : Tx}
    (hen : commitEnabledStrong Mode.optimistic l tx) :
    outputsFresh l tx := by
  obtain ⟨_, _, _, _, _, hfresh⟩ := hen
  exact hfresh

/-- If the snapshot is invalid (some read-set UTXO consumed), the
    transaction cannot commit in optimistic mode. -/
theorem optimistic_must_abort_if_snapshot_invalid {l : Ledger} {tx : Tx}
    (hinvalid : ¬ (tx.readSet ⊆ l.utxos)) :
    ¬ commitEnabledStrong Mode.optimistic l tx := by
  intro hen
  exact hinvalid (optimistic_snapshot_valid hen)

/-- If outputs collide with existing state, commit is blocked. -/
theorem optimistic_must_abort_if_outputs_stale {l : Ledger} {tx : Tx}
    (hstale : ¬ outputsFresh l tx) :
    ¬ commitEnabledStrong Mode.optimistic l tx := by
  intro hen
  exact hstale (optimistic_outputs_fresh hen)

/-! ## Serializability -/

/-- Optimistic mode produces core-serializable histories. -/
theorem optimistic_serializable {l0 l : Ledger}
    (hnodup : l.history.Nodup) :
    coreSerializable l0 l :=
  opt_mode_serializable hnodup

/-- Optimistic mode produces strongly-serializable histories from invariant. -/
theorem optimistic_strong_serializable {l0 l : Ledger}
    (hinv : ledgerInvariant l) :
    strongCoreSerializable (coreOf l0) l.history :=
  opt_mode_serializable_strong_inv hinv

/-! ## No double-spend -/

/-- Reachable optimistic states have no double-spend. -/
theorem optimistic_reachable_noDoubleSpend {l₀ l : Ledger}
    (hinit : Init l₀) (hsteps : Steps Mode.optimistic l₀ l) :
    noDoubleSpend l :=
  reachable_noDoubleSpend hinit hsteps

/-! ## Consumed monotonicity -/

/-- Consumed set grows monotonically under optimistic execution. -/
theorem optimistic_consumed_monotone {l₀ lₙ : Ledger}
    (hsteps : Steps Mode.optimistic l₀ lₙ) :
    l₀.consumed ⊆ lₙ.consumed :=
  consumed_monotone_steps hsteps

/-! ## History properties -/

/-- Committed transactions in optimistic mode all have verified proofs. -/
theorem optimistic_committed_verified {l₀ l : Ledger}
    (hinit : Init l₀) (hsteps : Steps Mode.optimistic l₀ l) :
    committedImpliesVerified l :=
  reachable_committedImpliesVerified hinit hsteps

/-- History remains duplicate-free under optimistic execution. -/
theorem optimistic_historyNodup {l₀ l : Ledger}
    (hinit : Init l₀) (hsteps : Steps Mode.optimistic l₀ l) :
    historyNodup l :=
  reachable_historyNodup hinit hsteps

end Starstream.OptimisticMode
