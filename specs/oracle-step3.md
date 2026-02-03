# Step 3 Deliverable: Oracle API + Property Alignment

This document defines the executable checker APIs (single-tx, chunk, ledger-step) and outlines the property theorems, test strategy, and proof roadmap that align the Lean oracle with the TLA+ invariants.

## 1) Executable API Surface (Lean)

The executable APIs are defined in:
- `formal/lean/Starstream/Oracle/Idealized.lean`
- `formal/lean/Starstream/Oracle/API.lean`

### Single-transaction API
- `checkTx` validates a single transaction against a ledger under a gas budget.
- `applyTx` applies a single transaction and returns the next ledger state.
- `checkTxInput` / `applyTxInput` are input-record wrappers for stable API usage.

### Chunk API (batch)
- `applyChunk` folds `applyTx` over a list of transactions and returns the first error index if any.
- `checkChunkInput` is a thin wrapper returning only `Unit` on success.

### Ledger-step API
- `ledgerStep` is the canonical single-step transition, defined as an alias to `applyTxInput`.
- Nondeterministic stepping is explicitly deferred to the future `Choice`-driven API.

## 2) Proposed Property Theorems (Alignment with TLA+)

These are the intended Lean lemmas to connect executable behavior to TLA+ invariants. They are listed as a roadmap; no sorries are introduced.

### Input validity and well-formedness
- `checkTx_ok_implies_nonempty`: if `checkTx` succeeds, inputs and outputs are non-empty.
- `checkTx_ok_implies_unique`: if `checkTx` succeeds, inputs and outputs are id-unique.
- `checkTx_ok_implies_no_overlap`: if `checkTx` succeeds, inputs and outputs are disjoint.
- `checkTx_ok_implies_live`: if `checkTx` succeeds, all inputs exist in the ledger.
- `checkTx_ok_implies_fresh_outputs`: if `checkTx` succeeds, outputs are fresh vs live+consumed.

### Safety invariants (Idealized UTXO)
- `applyTx_preserves_balance`: if `applyTx` succeeds, `balancePreserved` holds.
- `applyTx_updates_consumed`: inputs are added to `consumed` after commit.
- `applyTx_removes_inputs`: inputs are removed from the live UTXO set.
- `applyTx_no_double_spend`: once consumed, an input cannot appear in live set.

### Chunk and serial consistency
- `applyChunk_fold`: `applyChunk` is equivalent to repeated `applyTx` application.
- `applyChunk_first_error`: if a chunk fails, the reported index is the earliest failure.

### Determinism
- `applyTx_deterministic`: identical inputs produce identical outputs.

These correspond directly to TLA+ invariants in `StarstreamInvariants.tla`:
- `INV_LINEAR_NoDoubleSpend` / `INV_LINEAR_ConsumedTracked`
- `INV_BALANCE_TxPreserved`
- `INV_IEUTXO_PendingShape` (idealized shape constraints)

## 3) Test Strategy (Executable Oracle)

**Unit tests**
- Each error code has a minimal failing vector.
- Each success case validates balance, consumed set updates, and output freshness.

**Property tests**
- Random small ledgers and txs within bounds.
- If `checkTx` succeeds, then `applyTx` preserves invariants.

**Golden vectors**
- Stable JSON encoding of inputs and outputs.
- `ledgerStep` and `applyChunk` are the canonical entrypoints for CI.

## 4) Proof Roadmap (Lean)

Phase A: Prove `checkTx` implications
- Show each check in `checkTx` corresponds to a boolean predicate or set relation.
- Prove lemmas in the order of checks (nonempty, unique, disjoint, live, fresh, signature, balance).

Phase B: Prove `applyTx` preserves invariants
- Unfold `applyTx` and show each ledger field update preserves core invariants.
- Establish that new ledger state reflects consumed inputs and added outputs.

Phase C: Chunk correctness
- Prove `applyChunk` equivalence to fold of `applyTx`.
- Prove earliest-failure semantics for `ChunkErr`.

Phase D: Starstream extensions
- Lift theorems to Starstream types once phases/effects/proofs are modeled.
- Map the same property names to the TLA+ invariant set used in `MC_Starstream.tla`.

## 5) Status

- API wrappers implemented and compiled.
- Theorems are listed as a roadmap with no sorries or axioms.
- Next: Start Phase A lemma proofs once the idealized invariants list is finalized.
