# Liveness Plan — Status: Implemented

## 0. Purpose
Define the liveness claims ICE-UTxO can support, the assumptions they require,
and the minimal model extensions needed to prove them.

## 1. Approach: Three-Tier Evidence Strategy

Rather than full temporal-logic mechanization in Lean 4 (estimated 1,000–2,000 lines
for uncertain return), we adopted a three-tier strategy:

1. **Lean 4**: Mechanized finite-state supporting lemmas (enabledness, step effects,
   monotonicity). These are the "safety backbone" that any liveness proof requires.
   Universal, machine-checked, zero sorry.

2. **TLA+ model checking**: Enabled the liveness properties in `MC_Starstream.tla`,
   switched to `MC_FairSpec`/`MC_StrongFairSpec`, and run TLC. Validates L1–L3 on
   small finite instances with explicit fairness.

3. **Paper-level theorems**: L1–L5 stated formally with explicit assumptions in
   Section 4.6. Cite Lean lemmas as mechanized foundation and TLA+ as validation.

## 2. Target Liveness Properties

| Property | Statement | Assumptions | Evidence | Paper |
|----------|-----------|-------------|----------|-------|
| **L1** | Commit-enabled tx eventually commits | WF(commit), stability | Lean + TLC + paper | Thm 4.6 |
| **L2** | Pending tx eventually commits or aborts | WF(abort) | Lean + TLC + paper | Thm 4.7 |
| **L3** | Effect queue eventually empties | SF(handleE), handler stability | Lean + TLC + paper | Thm 4.8 |
| **L4** | Conflict-free PTB completes | Fair role participation | Existing Lean + MPST lit | Prop 4.9 |
| **L5** | S-BAC eventually decides | Partial synchrony, honest shards | Literature citation | Remark 4.10 |

## 3. Lean Lemmas Added (StarstreamPilot.lean)

- `commitEnabled'`: enabledness predicate for commit
- `abortEnabled`: enabledness predicate for abort
- `commit_step_specific`: commit produces a specific successor state
- `commit_adds_to_history`: tx enters history after commit
- `commit_removes_from_pending`: tx leaves pending after commit
- `abort_removes_from_pending`: tx leaves pending after abort
- `abort_enabled_of_pending`: abort always enabled for pending tx
- `handleEffect_succeeds`: handleEffect succeeds with effect + handler present
- `handleEffect_decreases_effects`: handleEffect strictly decreases queue length

All lemmas compile with zero sorry, zero custom axioms.

## 4. TLA+ Changes

- `Starstream.cfg`: SPECIFICATION changed to MC_FairSpec, PROPERTIES uncommented
- `StarstreamOptimistic.cfg`: Same changes for optimistic variant
- `MC_Starstream.tla`: No changes needed (MC_TxTerminates, MC_EffectsHandled,
  MC_IdleReachable already correctly defined)

Properties to check:
- `LIVE_TxEventuallyCommits` under `FairSpec` (WF on commit)
- `LIVE_TxEventuallyTerminates` under `FairSpec` (WF on commit/rollback)
- `LIVE_EffectsEventuallyHandled` under `StrongFairSpec` (SF on HandleTxEffect)
- `LIVE_CanReturnToIdle` under `FairSpec`

## 5. TLA+ ↔ Lean Cross-Reference

| TLA+ Property | TLA+ Fairness | Lean Support Lemma | Paper Theorem |
|---------------|---------------|-------------------|---------------|
| `LIVE_TxEventuallyCommits` | `WeakFairness` | `commit_enabled_can_step` | L1 |
| `LIVE_TxEventuallyTerminates` | `WeakFairness` | `pending_can_step` | L2 |
| `LIVE_EffectsEventuallyHandled` | `StrongFairness` | `handleEffect_succeeds`, `handleEffect_decreases_effects` | L3 |
| `LIVE_CanReturnToIdle` | `WeakFairness` | `abort_removes_from_pending`, `commit_removes_from_pending` | L2 |
 
PTB note: `HandleTxEffect` corresponds to the PTB Resume event in the main spec
(and `OptHandleTxEffect` in the optimistic variant).

## 6. Paper Changes

- **Section 4.6** (new): Conditional Liveness — fairness assumptions, L1–L5
- **Section 7**: Table 1 updated with liveness support lemmas, TLA+ paragraph added,
  Table 2 line counts updated, limitation 3 updated
- **Section 9**: Liveness paragraph replaced with redirect to Section 4.6

## 7. Literature Grounding

- Lamport (1994): WF/SF definitions
- Kung-Robinson (1979): starvation in optimistic CC
- Bernstein-Hadzilacos-Goodman (1987): deadlock/livelock taxonomy
- Gray-Reuter (1993): timeout-based abort
- Coppo et al. (2016): global progress for interleaved sessions
- Castellani-Dezani-Giannini (2024): event-structure progress
- Dwork-Lynch-Stockmeyer (1988): consensus under partial synchrony
- Al-Bassam et al. (2018): S-BAC liveness under honest-shard assumption

## 8. What Remains Future Work

- Full temporal-logic mechanization in Lean 4 (coinductive traces, temporal operators)
- Cross-shard liveness (L5) mechanization (depends on BFT consensus formalization)
- Strong fairness variants and their practical justification
- Contention analysis and backoff policy formalization
