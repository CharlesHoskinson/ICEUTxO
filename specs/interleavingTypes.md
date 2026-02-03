# Interleaving Concurrency Model + Session Types for Starstream

This document defines a concurrency model suitable for Starstream’s UTXO/transaction protocol and shows how session types fit into (and complement) that model. The goal is a formalizable model that is both faithful to blockchain semantics and able to capture the concurrency and protocol-safety concerns unique to Starstream (coroutines, effects, and linear resources).

## 1) Executive summary

**Recommended model:**
- **Serializable transactions with optimistic parallel execution** (validate‑on‑commit).
- **Formal foundation:** an **interleaving transition system** (state machine) over shared ledger state.
- **Session types:** used to **constrain intra‑transaction protocols** (effects/handlers/resume, linear consumption), not to define ledger‑level concurrency.

This yields: high parallelism (UTXO disjointness), deterministic commit boundaries (proof‑friendly), and crisp safety properties (no double‑spend, linear consumption, effect‑protocol safety).

## 2) What “interleaving model” means

TLA+ (and PlusCal) model concurrency via **interleavings of atomic actions**. There are no simultaneous steps; instead, the next state is chosen by any enabled action in any order. A concurrency model is thus defined by:

- The **state variables**
- The **actions** that update them
- The **guards** on those actions
- The **invariants** and **liveness** properties that must always hold

This is **not** a process calculus (e.g., π‑calculus, CSP). Those are communication‑centric. In TLA+, you encode concurrency as a shared‑state transition system.

## 3) Why serializable‑with‑optimistic‑execution fits Starstream

1. **Ledger semantics are serial:** blocks define a total order. The observable state should be equivalent to some serial order of transaction commits.
2. **UTXOs make conflicts explicit:** inputs are explicit, so conflicts are easily detected at commit.
3. **High parallelism:** disjoint UTXOs can execute independently.
4. **Proof‑friendly:** clear commit boundaries are ideal for proof validity checks (IVC/PCD/MCC).
5. **Avoids deadlocks:** optimistic execution avoids lock contention across long transactions.

## 4) Formal model class

A **transactional interleaving state machine** with a **single atomic commit step** and explicit abort semantics.

### 4.1 Core state (conceptual)

- `utxoStatus[u] ∈ {Unspent, Locked(tx), Consumed}`
- `txState[tx] ∈ {Init, Running, WaitingEffect, ReadyToCommit, Aborted}`
- `txInputs[tx] ⊆ UTXO`
- `txOutputs[tx] ⊆ UTXO`
- `txReadSet[tx]` and `txWriteSet[tx]` (optional, if using read‑validation)
- `txEffects[tx]` (pending effect instances)
- `ledgerUTXOs` (committed, i.e., `utxoStatus = Unspent`)

### 4.2 Key actions (conceptual)

- `Begin(tx)`
  - Initializes `txState`, collects intended inputs, (optionally) locks inputs.

- `ExecStep(tx)`
  - Advances coordination/UTXO execution in small steps.
  - May `raise` effects and move to `WaitingEffect`.

- `HandleEffect(tx)`
  - Resolves one pending effect, producing a resume value.
  - Must resume the exact continuation that raised the effect.

- `Commit(tx)`
  - **Atomic**: validate input UTXOs still `Unspent` (or locked to tx), and read‑set stable.
  - If valid: consume inputs, publish outputs, clear `txState`.
  - If invalid: `Abort(tx)`.

- `Abort(tx)`
  - Releases locks, clears staged outputs/effects.

### 4.3 Safety invariants

- **No double‑spend (global):**
  - No UTXO is `Locked` by two txs.
  - No UTXO is both `Unspent` and `Consumed`.

- **Atomicity:**
  - Outputs are visible only after commit.
  - Inputs are consumed only at commit.

- **Balance preservation (per asset):**
  - For each asset type or token ID: `inputs - burns + mints = outputs`.

- **Effect correctness:**
  - Every raised effect is either handled or aborts the transaction.
  - A handle must resume the exact continuation that raised it.

- **Frame integrity:**
  - Resumes must use stored frames; frames may change only by execution steps.

### 4.4 Liveness (under weak fairness)

- Any `Running` tx eventually either commits or aborts.
- Any pending effect eventually either gets handled or causes abort.

## 5) Where session types belong

Session types **do not replace** the interleaving model. They **complement** it by constraining **protocol structure inside a transaction**:

- **Effect/handler protocol:** a `raise` must be matched by a `handle`, which must resume the same continuation.
- **Linearity:** UTXOs and linear resources are consumed exactly once.
- **Ordering:** certain effects can only happen in certain phases (e.g., `yield` before `consume`).

### 5.1 Session‑type‑like view of a UTXO lifecycle

```
UTXO = Created · (Yield · HandleEffect · Resume)* · Consume
```

This is a protocol specification, not a concurrency semantics. It enforces valid sequences **within a single transaction**.

### 5.2 Example of effect protocol as session type

```
EffectProtocol = Raise(effectTag, payload) · Handle(effectTag) · Resume(value)
```

The session type encodes that the handler must match the effect’s tag and that the resume value is returned to the correct continuation.

## 6) Why process calculus is not the right primary model

Process calculi are designed for **communication topology** and **message passing**. Starstream’s core safety properties depend on shared ledger state and atomic commit semantics, which are more naturally modeled as a **transactional state machine**. You can still use process‑calculus intuition for coordination scripts, but the ledger model should be a shared‑state interleaving system.

## 7) Practical TLA+ modeling guidance

1. **Choose the concurrency model explicitly.**
   - If your focus is ledger safety, model transactions as atomic.
   - If your focus is execution engine safety, model interleavings with `Begin/Exec/Commit/Abort`.

2. **Encode optimistic concurrency.**
   - Record `txInputs` and validate they remain `Unspent` at commit.
   - Optionally validate `readSet` for non‑UTXO reads.

3. **Make effect handling explicit.**
   - An effect instance should carry `(tag, payload, continuationId)`.
   - Handling must resume the exact continuation.

4. **Use session‑type invariants as action guards.**
   - For example: a `Consume` action is only enabled if the UTXO protocol state allows it.

## 8) Quick mapping to Starstream design constraints

- **UTXO cannot call UTXO:** model as a forbidden action or a protocol violation.
- **Tokens cannot own tokens:** ensure token ownership is a primitive relation with no nesting.
- **Linear types:** map to session‑type linearity and global invariants.
- **Proof validity:** gate commit on `ValidProof(tx)`.

## 9) Optional extensions

- **Serializable‑trace invariant:** every interleaving trace is equivalent to some serial commit order.
- **Conflict‑graph validation:** commit only if no edges in a read/write conflict graph.
- **Effect cancellation semantics:** model explicit cancellation if effects are unhandled.

## 10) Summary

The best formal model for Starstream concurrency is a **transactional interleaving state machine** with **optimistic validation and atomic commit**. Session types strengthen the model by enforcing correct protocols **inside** a transaction, but they are not themselves a concurrency model. Together, they provide a rigorous foundation for both ledger safety and Starstream‑specific protocol correctness.
