import StarstreamPilot

set_option autoImplicit false

namespace Starstream.Oracle

/-!
Phase D: lift key oracle properties to the Starstream protocol layer
defined in `StarstreamPilot.lean` (phases/effects/proofs modeled).
-/

theorem starstream_commit_preserves_no_double_spend
    {l : Starstream.Ledger} {tx : Starstream.Tx}
    (hinv : Starstream.noDoubleSpend l)
    (hfresh : Starstream.outputsFresh l tx)
    (hlive : Starstream.inputsLive l tx) :
    Starstream.noDoubleSpend (Starstream.applyCommit l tx) := by
  simpa using (Starstream.commit_preserves_no_double_spend hinv hfresh hlive)

theorem starstream_consumed_monotone_step
    {m : Starstream.Mode} {l l' : Starstream.Ledger}
    (hstep : Starstream.Step m l l') :
    l.consumed ⊆ l'.consumed := by
  simpa using (Starstream.consumed_monotone_step hstep)

theorem starstream_consumed_monotone_steps
    {m : Starstream.Mode} {l₀ lₙ : Starstream.Ledger}
    (hsteps : Starstream.Steps m l₀ lₙ) :
    l₀.consumed ⊆ lₙ.consumed := by
  simpa using (Starstream.consumed_monotone_steps hsteps)

theorem starstream_commit_consumes_inputs
    {l : Starstream.Ledger} {tx : Starstream.Tx} :
    tx.inputs ⊆ (Starstream.applyCommit l tx).consumed := by
  simpa using (Starstream.commit_consumes_inputs (l := l) (tx := tx))

theorem starstream_commit_requires_proof
    {m : Starstream.Mode} {l l' : Starstream.Ledger} {tx : Starstream.Tx} :
    Starstream.Step m l l' →
    l'.history = l.history ++ [tx] →
    Starstream.proofOk tx := by
  intro hstep hhist
  simpa using (Starstream.commit_requires_proof hstep hhist)

theorem starstream_step_preserves_invariant
    {m : Starstream.Mode} {l l' : Starstream.Ledger}
    (hstep : Starstream.Step m l l')
    (hinv : Starstream.ledgerInvariant l) :
    Starstream.ledgerInvariant l' := by
  simpa using (Starstream.step_preserves_invariant hstep hinv)

theorem starstream_concurrent_refines_serial
    {m : Starstream.Mode} {l₀ lₙ : Starstream.Ledger}
    (hexec : Starstream.Steps m l₀ lₙ)
    (hinv : Starstream.ledgerInvariant l₀) :
    Starstream.SerialSteps m (Starstream.absLedger l₀) (Starstream.absLedger lₙ) := by
  simpa using (Starstream.concurrent_refines_serial hexec hinv)

end Starstream.Oracle
