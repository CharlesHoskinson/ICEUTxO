# Oracle Scope and Interface (Step 1)

This document captures the clarified scope and interface for the executable oracle, plus a mapping to the existing TLA+ specification. It is intended to lock the boundary of the oracle so golden vectors and CI remain stable.

## Scope

The oracle covers two layers:

1) Idealized UTXO core
- Pure ledger semantics: inputs, outputs, consumed IDs, balance preservation, uniqueness, and chunk validity.
- No execution model, no network/consensus, no bytecode semantics.
- Deterministic transitions only.

2) Starstream protocol layer
- Extends the idealized layer with UTXO lifecycle, transaction phases, coordination scripts, effects, proofs, and locks.
- Deterministic atomic application of a fully-specified Starstream transaction.
- Nondeterminism is modeled explicitly via a separate Choice-driven API (not in the deterministic core).

Out of scope (explicitly): consensus/forks, network delivery, gas economics beyond the deterministic gas model, cryptographic soundness proofs, zk-circuit execution details, and adversarial scheduling outside explicit choices.

## Deterministic Oracle Interface

Deterministic APIs are total and return either a new state or a structured error. No randomness or implicit choices are allowed.

Idealized UTXO:
- checkTx(ledger, tx, gas?) -> Ok | Err
- applyTx(ledger, tx, gas?) -> Ok(ledger') | Err
- applyChunk(ledger, txs, gas?) -> Ok(ledger') | Err(index, Err)

Starstream:
- checkTx(ledger, tx, gas?, trace?) -> Ok | Err
- applyTx(ledger, tx, gas?, trace?) -> Ok(ledger', trace?) | Err

Determinism rules:
- Canonical ordering for IDs and serialized maps.
- Stable error precedence rules (same input, same error).
- Optional trace output must not affect state or error identity.

## Nondeterministic Extension (Explicit Choices)

Nondeterminism is modeled explicitly and separately from the deterministic oracle.

- stepWithChoice(ledger, choice, gas?, trace?) -> Ok(ledger', trace?) | Err
- step(ledger, bounds) -> Finset ledger'

All nondeterminism must be fully encoded in Choice (e.g., which tx, which effect, which handler). The deterministic core remains the single source of truth for golden vectors.

## Error Model

Errors are part of the oracle contract. Each error has a stable code and minimal message. The error schema is versioned. The first failing condition is reported deterministically.

## Mapping to TLA+ Concepts

The table below maps the oracle types to existing TLA+ modules and records.

- LedgerState (Starstream) maps to StarstreamLedger.tla LedgerStateSet
  - utxos -> ledger.utxoSet
  - consumed -> ledger.consumedSet
  - locked -> ledger.lockedSet
  - nextUtxoId -> ledger.nextUtxoId
  - nextTxId -> ledger.nextTxId
  - pendingTxs -> ledger.pendingTxs
  - txHistory -> ledger.txHistory
  - proofStore -> ledger.proofStore
  - activeProofs -> ledger.activeProofs

- Utxo (idealized) maps to StarstreamUTXO.tla UTXORecord
- StarUtxo (extended) adds:
  - state -> u.state
  - frame -> u.frame
  - lockedBy -> u.lockedBy

- Tx (idealized) maps to StarstreamTransaction.tla TransactionRecord (subset)
- StarTx (extended) adds:
  - phase -> tx.phase
  - coordination -> tx.coordination
  - proofCommitments -> tx.proofCommitments
  - readSet/writeSet -> tx.readSet/tx.writeSet (optimistic spec)

- Effects/Coordination map to StarstreamEffects.tla and StarstreamCoordination.tla
- Proofs map to StarstreamProof.tla
- Authorization maps to StarstreamAuth.tla

The deterministic oracle enforces the invariants currently checked in MC_Starstream.tla, with explicit documentation for any invariant that is excluded.

## Versioning

The oracle interface, hashing spec, and error taxonomy are versioned. Any change to these requires a schema bump and regeneration of golden vectors.
