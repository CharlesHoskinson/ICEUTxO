# Lean pilot status (Starstream)

This document records what is proved in the Lean pilot, what is trivial by definition, and what still needs real work.

The pilot is minimal. It tests whether Lean is workable and exposes the hard proofs. It is not a full formalization.

The Lean model should mirror the TLA+ boundaries: ledger state, interleavings, and commit gating.

We use `Finset` and `List` to keep proofs manageable. We can replace them once the semantics are stable.

`Step.commit` now requires `commitEnabledStrong` which enforces structured proof commitments, transaction phase gating (`TxPhase.committing`), history freshness (tx not in `history`), and read-set validation in both locking and optimistic modes.

Effects and handlers are global queues and stacks keyed by interface. The model does not track effect ownership or when stacks may change.

`proofVerified` is retained for backward compatibility but is supplemented by `ProofCommitment` and `ProofPhase` for structured proof lifecycle tracking.

Serializability has both a permissive definition (`serializable`) and a strengthened version (`serializableStrong`) that requires validity under the serial step relation.

The precedence graph uses both standard read/write sets (`conflicts`) and extended edges for UTXO creation/consumption (`conflictsExt`).

`applyHistory` folds commits and assumes commits are the only observable change. Once effects and phases exist, recheck soundness.

Commits are treated as atomic. The refinement argument from interleavings to atomic commits is now scaffolded via `concurrent_refines_serial`.

Locking vs optimistic mode are just a parameter. Both modes now enforce `readSetValid` to prevent phantom reads. The difference is that locking also requires `tx.inputs ⊆ l.locked`.

Workflow: strengthen definitions first, then re-prove.

Use this pilot as a cross-check against TLA+. Tighten a Lean definition only if the TLA+ spec supports it.

This document is also a go/no-go record. If Lean gets too expensive, we should know why.

## Current file
- `StarstreamPilot.lean`

## What is proved (non-trivially)

1) `commit_requires_proof` — COMPLETE
   - Any step that appends to history must have `proofOk`.
   - Cases on `Step`; only `Step.commit` can append; `commitEnabledStrong` implies `commitEnabled` via bridge theorem, which includes `proofOk`.
   - Uses `list_eq_self_append_singleton`, `append_right_cancel`, and `commitEnabledStrong_implies_commitEnabled`.

2) `circuit_witness_implies_serial_step` — COMPLETE
   - A valid `refinementWitness` directly satisfies the `SerialStep` existential.
   - Proof: destructure `refinementWitness` into `allProofsVerified`, `validTx`, phase, and mode conditions; these are exactly `commitEnabledStrong`.

3) `acyclicExt_implies_acyclic` — COMPLETE
   - Extended precedence graph acyclicity implies standard acyclicity.
   - Proof: `precEdge` edges are a subset of `precEdgeExt` edges; use `TransGen.mono`.

4) `acyclic_precgraph_serializable` — COMPLETE
   - Uses a topological-sort witness via `acyclic_strong_serializable`.
   - Requires `history.Nodup`; acyclicity is now derived structurally from `before`.

5) `effectStep_decreases_queue` — COMPLETE
   - Single effect-handling step strictly decreases queue potential for handled interface.
   - Proof: `handleEffect_removes_head` shows one effect removed; `effectPotential e > 0`.

6) `fuelBudget_implies_pointwise` — COMPLETE
   - Budget discipline `Σ(r.fuel + 1) ≤ f` implies pointwise `r.fuel < f` for all raised effects.
   - Proof: each `r.fuel + 1` ≤ sum ≤ f, so `r.fuel < f`.

7) `effectStep_decreases_potential` — COMPLETE
   - Single effect-handling step strictly decreases total potential across all interfaces.
   - Proof: uses `list_sum_lt_of_one_lt` with `effectStep_decreases_queue` for the handled interface
     and `handleEffect_preserves_others` for unchanged interfaces.

8) `effect_handling_terminates` — COMPLETE
   - Effect handling terminates in at most `potential(initial)` steps.
   - Proof: strong induction on potential; each step decreases potential by ≥1.

## Effect termination

Effect-chain termination is proved under the **fuel discipline**:

- **Fuel field**: Each `Effect` carries `fuel : Nat` (remaining budget for subtree).
- **Budget discipline** (`fuelBudget`): When handling effect with fuel `f` and raising `raised`,
  the sum `Σ(r.fuel + 1)` for `r ∈ raised` must be ≤ `f`.
- **Potential measure**: `μ(ledger) = Σ(e.fuel + 1)` over all pending effects.
- **Strict decrease**: Each handle step removes `(f + 1)`, adds at most `f`, so μ decreases by ≥ 1.
- **Termination bound**: At most `potential(initial)` steps to reach empty queues.

### Proved termination theorems

- `effectStep_decreases_potential` — total potential strictly decreases per handle step (COMPLETE)
- `effect_handling_terminates` — existence of terminal state with bound ≤ initial potential (COMPLETE)

### Supporting lemmas (all COMPLETE)

- `potential_zero_no_effects` — zero potential implies no pending effects in range
- `exists_handleable_effect` — if effects exist and handlers installed, can take a step
- `handleEffect_preserves_handlers` — handlers remain installed after handling

**Note:** Handler computation itself is assumed atomic/total. This proof rules out infinite
*effect chains*, not diverging handlers.

## What is proved (but still assumption-heavy)
These proofs are thin wrappers around acyclicity; they do not derive it from validation.

1) `lock_mode_serializable` / `opt_mode_serializable`
- Now take `history.Nodup`.
- Current proof: direct application of `acyclic_precgraph_serializable`.
- Status: assumption removed for reachable states given `Init`; still needed when reasoning about
  arbitrary `l` without reachability hypotheses.

## Proof obligations (sorry)
These are skeleton theorems with proof strategies documented but incomplete proofs:

1) `swap_nonconflicting_preserves` — Key swap/commutativity lemma
   - Strategy: unfold `applyHistory` as `foldl`, factor prefix, use `txCommute`.

2) `commit_preserves_no_double_spend` — Invariant preservation
   - Strategy: show `(utxos \ inputs) ∪ outputs` disjoint from `consumed ∪ inputs`.

3) `noncommit_preserves_no_double_spend` — Invariant preservation for non-commit steps
   - Strategy: non-commit steps don't modify `utxos` or `consumed`.

4) `pending_only_steps_stutter` — Stuttering lemma for refinement
   - Strategy: `absLedger` erases `pending` and `locked`, so steps only changing those are stuttering.

5) `concurrent_refines_serial` — MAIN REFINEMENT THEOREM
   - Strategy: induction on `Steps`, map commit steps to `SerialStep`, other steps stutter.

6) `step_preserves_invariant` — Invariant preservation across all steps
   - Strategy: case split on `Step`; commit uses `commit_preserves_no_double_spend`, others preserve `utxos`/`consumed`.

## New additions (interleaving proof alignment)

### Structured proof commitments
- `ProofPhase` inductive: `notStarted | generating | verifying | verified | failed`
- `ProofCommitment` structure: kind, processId, commitHash, verifyKey, phase, stepNumber
- `allProofsVerified`: all commitments in Verified phase
- `commitEnabledStrong`: requires structured proofs + correct tx phase; now used by `Step.commit` and `SerialStep`
- `commitEnabledStrong_implies_commitEnabled`: bridge theorem (strong → weak)
- `allProofsVerified_implies_proofOk`: bridge axiom linking structured and boolean proof models

### Transaction lifecycle
- `TxPhase` inductive: `idle | reserve | executing | committing | committed | rollback | failed`
- Tx now carries `proofCommitments : List ProofCommitment` and `phase : TxPhase`

### Multi-step semantics
- `Steps`: reflexive transitive closure of `Step`
- `SerialSteps`: reflexive transitive closure of `SerialStep`

### Extended precedence graph
- `conflictsExt`: standard conflicts + UTXO creation/consumption edges
- `precEdgeExt` / `precGraphAcyclicExt`: extended versions; all serializability theorems now use `precGraphAcyclicExt`
- `acyclicExt_implies_acyclic`: bridge lemma (extended acyclicity → standard acyclicity)
- `serializableStrong`: requires validity under serial step relation

### Swap commutativity
- `txCommute`: two non-conflicting transactions commute
- `swap_nonconflicting_preserves`: swapping adjacent non-conflicting txs preserves `applyHistory` (skeleton)

### Interleaving proof circuit connection
- `InterleavingWitness`: structured witness from the ZK circuit
- `circuitVerifiable`: all proofs verified and correct phase
- `refinementWitness`: circuit proof + ledger validation

### Ledger invariants
- `noDoubleSpend`, `lockedSubsetActive`, `historyNodup`, `committedImpliesVerified`
- `precGraphAcyclicExt` / `fullPrecGraphAcyclic`: precedence graph acyclicity (structural from `before`)
- `noDuplicatePendingProofs`: per-tx proof uniqueness
- `ledgerInvariant`: combined invariant
- `historyNodup_step` / `historyNodup_steps`: uniqueness preserved by Step/Steps (freshness from `commitEnabledStrong`)
- `Init`: history/pending/locked/consumed/effects/handlers empty at genesis
- `reachable_historyNodup` / `reachable_ledgerInvariant`: reachability corollaries from `Init`
- `reachable_noDoubleSpend`, `reachable_lockedSubsetActive`, `reachable_committedImpliesVerified`
- `reachable_precGraphAcyclicExt`, `reachable_fullPrecGraphAcyclic`, `reachable_noDuplicatePendingProofs`

### Refinement mapping
- `absLedger`: abstraction map (erases pending/locked)
- `isStuttering`: concrete step doesn't change abstract state
- `concurrent_refines_serial`: main refinement theorem (skeleton)
- `circuit_witness_implies_serial_step`: circuit witness → serial step (proved)

## Missing definitions / invariants that must be added

### A. Concurrency semantics
- Introduce transaction phases (Reserve, Execute, Commit) to capture interleavings more precisely.
- Model effects/handlers at the transaction level (not just global queues), with constraints like:
  - pending effects must be handled before commit,
  - handler stacks must be consistent with installed handlers.

### B. Serializability machinery
- Fill in `swap_nonconflicting_preserves` proof.
- Prove a topological sort lemma: acyclicity implies existence of a topo order.
- Show topo order yields the same final state as the concurrent history.
- Upgrade `lock_mode_serializable` and `opt_mode_serializable` to use `serializableStrong`.

### C. Proof model
- Add invariants linking `ProofCommitment` to IVC circuit state.
- Prove `committedImpliesVerified` is preserved by all steps.
- Add invariant: no duplicate pending proofs for same process ID across ledger.

### D. Ledger & tx validity
- Strengthen `validTx` to incorporate:
  - input uniqueness,
  - output uniqueness,
  - input/output disjointness,
  - input ownership and signature validity,
  - output freshness relative to the ledger.

### E. Optimistic concurrency
- Define a read snapshot and ensure `readSet` matches it.
- Add `ReadSetValid` and `WriteSetValid` invariants.
- Prove commit-time validation implies serializable history (or no cycles).

### F. Fill in sorry proofs
Priority order for filling in `sorry` proofs:
1. `commit_preserves_no_double_spend` — foundational invariant
2. `swap_nonconflicting_preserves` — key for serializability
3. `pending_only_steps_stutter` — needed for refinement
4. `step_preserves_invariant` — invariant preservation (depends on 1)
5. `concurrent_refines_serial` — main refinement theorem (depends on 3, 4)
6. `noncommit_preserves_no_double_spend` — invariant completeness

## Notes on correctness vs. placeholders
- `sorry` is used for proof obligations that have documented strategies but incomplete proofs.
- Fully proved: `commit_requires_proof`, `circuit_witness_implies_serial_step`, `acyclicExt_implies_acyclic`, `list_eq_self_append_singleton`, `append_right_cancel`.
- Bridge axiom: `allProofsVerified_implies_proofOk` (asserted; links structured proofs to Bool field).
- Assumption-heavy: `lock_mode_serializable`, `opt_mode_serializable` (need `history.Nodup` or a derivation of it).
- The next step is to fill in `sorry` proofs following the documented strategies.

## System diagrams (ASCII)

These diagrams capture the intended semantics. If a diagram asserts a guard or ordering, the model should encode it.

Transaction lifecycle should be explicit in the step relation, not implicit in a single commit action. The current pilot flattens this, which is why interleavings are too permissive.

```
Idle -> Reserve -> Executing -> Committing -> Committed
          |           |             |
          v           v             v
        Failed <------+-------------+
```

Interleavings should be understood as interleavings of phase-level steps rather than one-step atomic commits. The serial spec should collapse a whole transaction path into a single atomic step, and the refinement should relate the two.

```
Concurrent trace:
  T1.reserve; T2.reserve; T1.execute; T2.execute; T1.commit; T2.commit

Serial trace:
  T1.commit; T2.commit
```

Proof gating is part of the commit precondition, not a post-hoc invariant. The proof artifact must be present and verified before the commit step can fire.

```
VerifyProof(tx) -> proofVerified(tx) = true -> Commit(tx)
```

Effects are interface-scoped; handlers are stacks per interface. A pending effect should not be handled unless a handler is present for its interface, and commit should be blocked if pending effects exist.

```
effects[iface] = [E2, E1]
handlerStacks[iface] = [H2, H1]
HandleEffect requires handlerStacks[iface].length > 0
Commit requires effects[iface] = []
```

## Mapping table (TLA+ -> Lean pilot)

| TLA+ concept | Lean pilot artifact | Gap / needed work |
|---|---|---|
| LedgerStateSet | `Ledger` | Missing proofStore/activeProofs; no readSnapshot |
| TransactionRecordSet | `Tx` | Has phase + proofCommitments; missing signer/signature |
| ProofCommitmentType | `ProofCommitment` | Aligned with TLA+ ProofPhases |
| ProofPhases | `ProofPhase` | Direct mapping |
| TxStates | `TxPhase` | Direct mapping |
| BeginCommit/CommitTx | `Step.commit` | Phase + freshness gating enforced via `commitEnabledStrong` |
| AllTxProofsVerified | `allProofsVerified` | Structured, non-boolean |
| Optimistic read/write validation | `commitEnabled` / `commitEnabledStrong` | Both modes check `readSetValid`; no snapshot/version checking |
| Effects + handler stacks | `effects`, `handlerStacks` | No per-tx ownership or commit blocking |
| IEUTxO chunk validity | `serializable` / `serializableStrong` | Strengthened definition added |
| Proof commitments | `ProofCommitment` + `allProofsVerified` | Needs IVC circuit state link |
| SerialRefinement | `concurrent_refines_serial` | Skeleton with proof strategy |
| CircuitVerifiable | `circuitVerifiable` | Aligned with TLA+ CircuitAlignment module |
| NoDuplicatePendingEffects | `noDuplicatePendingProofs` | Per-tx only; need ledger-wide |
| Precedence graph | `precEdge` / `precEdgeExt` | Serializability theorems now use `precGraphAcyclicExt` |
| Swap commutativity | `txCommute` + `swap_nonconflicting_preserves` | Skeleton |
| Effect fuel | `Effect.fuel` | Budget for effect subtree (termination) |
| FuelBudget | `fuelBudget` | Sum of raised (fuel+1) ≤ handled.fuel |
| TotalFuel/Potential | `potential` | Termination measure Σ(fuel+1) |
| INV_EFFECT_FuelBounded | `effectsBounded` (implicit) | Fuel within range |
| LIVE_EffectTermination | `effect_handling_terminates` | Bounded termination theorem |
