# ICE-UTxO: Interleaving Coroutine Effects UTxO

Status: working note for PL researchers and formal methods practitioners.

## Summary (MPST-first)
ICE-UTxO is a conservative extension of eUTxO in which:
- A coordination script is a multiparty protocol (MPST/global type) with event-structure semantics.
- A transaction carries a compiled PTB-style program plus an IVC witness that the program's trace conforms to the protocol.
- Ledger commit remains atomic and UTxO-style safety properties are preserved.

## Core idea (one sentence)
A transaction is a proof-carrying implementation of a multiparty protocol; the PTB program is the concrete schedule, and the IVC witness certifies its validity.

---

## 1) Formal core: MPST and event-structure semantics

### Roles
Roles are the participants in a coordination script:
- UTXO coroutines (frame-carrying UTXOs)
- Effect handlers (interface-specific services)
- Coordinator/transaction driver

### Global type and event structure
A coordination script is a global type that specifies allowed interactions among roles.
We interpret the global type as an event structure:
- events are labeled by actions (resume, raise, install, read, consume, etc.)
- order is a partial order capturing causal dependencies
- conflict captures mutually exclusive steps

This makes the partial order the primary semantic object. A concrete execution is a linearization (trace) of this structure.

### Projection and local conformance
Each role projects the global type to a local type/automaton.
A trace is valid only if every role's projection accepts its local view.
This matches the local conformance checks already used in the Lean model.

### IVC witness obligations
The IVC witness proves that a proposed trace is:
- a linearization of the event structure
- accepted by the global type
- consistent with protocol constraints such as continuation matching and no self-resume
- consistent with handler availability and activation state

We treat the witness as the single source of truth for interleaving correctness.

---

## 2) PTB as compilation target

### PTB command model
The coordination script is compiled to a PTB-style bytecode:
- a list of commands with explicit inputs and outputs
- results are stored in temporary registers (Result(i))
- later commands can consume earlier results

Example (informal):
1) Call(Coroutine.resume, FrameObj) -> Result(0) = EffectVariant
2) Call(Handler.dispatch, Result(0)) -> Result(1) = Value
3) Call(Coroutine.resume, FrameObj, Result(1)) -> Result(2) = NewFrame

### Translation to the formal core
The PTB program induces the event-structure order:
- dataflow dependencies (Result edges) become order edges
- object access (owned/shared objects) introduces additional ordering constraints
- conflict arises from mutually exclusive resource use

### PTB to event-structure translation (concrete rules)
Given a PTB program with commands c0..cn-1, define one event ei per command ci.
Labels are the command kinds (resume, raise, install, read, consume, produce, lock, snapshot).

Order edges (ei < ej) are added when:
- Dataflow: cj consumes Result(i).
- Object access: ci and cj access the same object and at least one is a write/consume/lock/produce;
  order follows program order.
- Handler lifetime: install(h) < use(h) < uninstall(h) for each interface handler h.
- Explicit protocol constraints: any additional order edges required by the global type.

Conflict edges (ei # ej) are added when:
- Both commands consume the same UTXO.
- Both commands install different handlers for the same interface without ordering.
- A PTB command is part of an explicit choice/guarded branch (choice is encoded as conflict).

The PTB program order is the proposed trace; the IVC witness must show it is a linearization
of the event structure.

The validator executes the PTB deterministically and checks the IVC witness against the induced trace.
PTB is a compilation target, not the semantic core.

---

## 3) Object model and consensus

We separate objects into two categories:
- Owned objects: coroutine frames and purely local state
- Shared objects: effect handlers and shared resources

If a PTB touches only owned objects, it can take a fast path.
If it touches shared objects, it must go through consensus for total ordering.
We adopt S-BAC for atomic cross-shard commit of shared objects.

---

## 4) Model overview

ICE-UTxO adds three layers to eUTxO:
1) Coroutine state on UTXOs (frame with pc, locals, method id, hash).
2) Transaction-level coordination state (now materialized as a PTB program).
3) IVC proof artifacts that certify the interleaving within a transaction.

### State components (informal tuple)
Ledger state L:
- utxos: set of live UTXOs
- consumed: set of spent UTXO ids
- locked: set of reserved UTXO ids (locking mode)
- pendingTxs: set of in-flight transactions
- history: sequence of committed or failed transactions
- proofStore: set of active proof commitments
- nextUtxoId, nextTxId

UTXO u:
- id, owner, contractId, datum, tokens
- state in {Created, Suspended_at_Yield, Suspended_at_Effect, Reserved, Executing, Consumed}
- frame = (pc, locals, methodId, hash)
- lockedBy (tx id or NO_TX)

Transaction tx:
- inputs, outputs
- readSet, readSnapshot, writeSet (optimistic mode)
- ptbProgram (compiled coordination script)
- proofCommitments, proofPhase
- phase in {Idle, Reserve, Executing, Committing, Rollback, Committed, Failed}
- signer, signature

Effect e:
- kind in {Pure, Effectful, Runtime}
- sourceUtxoId
- continuationId
- interfaceId
- tag, payload
- handled flag
- witLedgerKind in {Resume, Yield_Intermediate, Yield_Final, Burn, Bind, Unbind, NewUtxo}

Proof commitment p:
- proofKind in {IVC_Step, IVC_Accumulator, Witness}
- ivcProcessId
- commitmentHash
- verificationKey
- phase in {NotStarted, Generating, Verifying, Verified, Failed}
- stepNumber

---

## 5) Operational semantics (high level)

### Phases
1) ReserveTx: select inputs, reserve (locking) or snapshot (optimistic).
2) Execute: run the PTB program, producing effects and intermediate frames.
3) FinalizeTx: construct outputs once all effects are handled.
4) CommitTx: verify proofs, then atomically update the ledger.
5) Rollback: abort and release locks or discard optimistic effects.

### Effect handling
- Effects are routed by interface id.
- Handlers are dynamically installed/uninstalled by commands.
- Commit is blocked if any pending effects remain.

---

## 6) IVC witness and interleaving correctness

The witness enforces constraints such as:
- continuation matching: resume targets the correct yielded pc
- no self-resume: a process cannot resume itself
- handler availability for interface-targeted effects
- activation state consistency in the IVC accumulator
- trace accepted by the global type and event structure

Proof commitments are stored in the ledger and must verify before commit.

---

## 7) Commit rule (schematic)
A transaction can commit iff:
- tx.phase = Committing
- all proofs verified (proof commitments in Verified phase)
- no pending effects
- balance preserved between inputs and outputs
- valid signature and ownership checks
- inputs are live, outputs are fresh
- optimistic mode: read snapshot still matches ledger

Then:
L' = CommitTx(L, tx) (atomic: consume inputs, add outputs, append history)

---

## 8) Concurrency modes
- Locking mode: reserves inputs before execution; requires inputs subset of locked.
- Optimistic mode: no locks; uses readSnapshot and validates at commit time.
Both modes are proof-gated for interleaving correctness.

---

## 9) Reduction to eUTxO
If coroutines never yield and no effects are raised, ICE-UTxO reduces to eUTxO:
- each input is validated once
- transaction applies atomically
- standard UTXO safety properties hold

---

## 10) Clarifications and design choices (Q and A)

### 1) Circuit-ledger bridge (trust boundary F3)
Is circuit soundness assumed or proved?
Current status: assumed. In Lean, allProofsVerified is treated as an oracle,
and the TLA+ invariants assume the circuit constraints hold. A full end-to-end
proof would require a mechanized proof of the ZK circuit arithmetization
(e.g., PLONK/Halo2) plus a linkage theorem showing those constraints imply the
TLA+ predicates. This is planned work, not implemented.

How does INV_CIRCUIT_ValueCommitmentIntegrityCheck avoid re-running?
The integrity check binds the proof to a frame hash (pc, locals, methodId).
Runtime validation recomputes this hash from stored frame data and compares it
to the commitment; it does not re-run the coroutine.

### 2) Scheduling and determinism
Is the schedule explicit or derived?
Explicit. The PTB program is the schedule. The validator executes it
deterministically and checks the witness against the induced trace.

How to prevent manipulated scheduler attacks?
The witness must verify and all effects must be handled. A pathological
schedule cannot commit and simply fails (the submitter pays the cost).
We expect practical guards: step bounds, gas limits, and protocol invariants.

### 3) Effect handler semantics
Are handlers lexical or dynamic?
Handlers are dynamically scoped to the transaction timeline. They are installed
and uninstalled explicitly via PTB commands.

What if an effect is raised with no handler installed?
If the program raises an effect with no handler installed, it remains pending
and commit is blocked. The intended design is to guard raises with handler
availability (protocol typing rules enforced via MPST).

### 4) Concurrency modes
Can locking and optimistic be mixed within a transaction?
Not in the current formalization. The mode is per-transaction.
Mixing modes per-input would require new state and validation rules.

When is the read snapshot taken?
In the optimistic spec, the snapshot is taken when the transaction is begun
on-ledger (BeginOptTxInLedger), not by the client.

### 5) IVC configuration details
What are id_curr and id_prev?
They are process identifiers in the interleaving trace (UTXO processes and
coordinators) and correspond to circuit wires. They are not step counters.

Is "no self-resume" fundamental or a design choice?
It is a protocol constraint aligned with the circuit model, not a fundamental
limit of IVC schemes. A different circuit could relax it.

### 6) Formal verification roadmap
Is the goal a constructive serializability proof?
Yes. The current Lean proof uses the identity permutation as a placeholder.
The target is a constructive proof deriving a valid serial order from the
dependency graph (e.g., via topological sort and swap lemmas).

Will TLA+ be fully mechanized, or replaced by Lean?
TLA+ remains the executable specification and model-checking layer. Lean is
the mechanized proof layer for key theorems.

---

## 11) Example trace (informal)
Inputs: U1 and U2
1) ReserveTx(U1, U2)
2) Execute PTB:
   a) Resume U1 -> yields effect on interface I
   b) Handle effect on I -> resume U1
   c) Resume U2
3) FinalizeTx -> outputs
4) Proofs verified -> CommitTx

---

## 12) Mapping to repository artifacts
- TLA+ spec: tla/StarstreamSpec.tla and related modules
- Invariants: tla/StarstreamInvariants.tla
- Circuit alignment: tla/StarstreamCircuitAlignment.tla
- Lean pilot: lean/StarstreamPilot.lean
- MPST/event-structure core: lean/Starstream/Coordination/Script.lean

---

## 13) Chainspace integration layer
Chainspace is a good deployment and atomic-commit substrate, not a replacement
for ICE-UTxO semantics. We adopt its sharded commit model while keeping the
protocol semantics and IVC witness as the core transaction meaning.

Mapping (conceptual):
- Chainspace object -> ICE-UTxO extended UTXO (frame-carrying)
- Chainspace procedure bundle -> ICE-UTxO PTB program + witness
- Chainspace checker -> ICE-UTxO witness verifier + ledger checks
- Chainspace S-BAC -> ICE-UTxO atomic cross-shard commit

Why this makes sense:
Chainspace already models atomic bundles of procedures across shards using
S-BAC and distinguishes execution from verification. ICE-UTxO adds coroutine
frames, algebraic effects, and IVC correctness of the schedule inside that
bundle.

---

## 14) Design implications for coordination scripts
- The formal semantics is MPST + event structures.
- The PTB program is a compilation target that must typecheck against the
  global protocol.
- Validators check the witness and ledger invariants, not by re-executing
  coroutine logic.
- Cross-shard atomicity is provided by S-BAC when shared objects are involved.

---

## 15) Open problems
- Strengthen the serializability proof (non-trivial permutation witness).
- Prove soundness of the IVC circuit relative to the TLA+ model.
- Formalize a full language semantics for coroutines and effect handlers.
- Relate ICE-UTxO to existing eUTxO ledger implementations.
