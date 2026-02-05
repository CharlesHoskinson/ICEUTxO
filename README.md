# ICE-UTxO

ICE-UTxO extends the eUTXO model with coroutines, algebraic effects, and proof-carrying transactions. This repo contains the TLA+ spec (model-checked), Lean 4 proofs, and the paper.

## The problem

eUTXO validators are single-shot functions. A validator runs, returns true/false, and that's it. It can't pause, can't resume, can't request a service from another contract, can't wait for a callback. If you want multi-step protocols — escrow, auctions, atomic swaps — you split them across multiple transactions and hope nothing goes wrong in between.

## The solution

Three layers:

1. **Coroutine frames on UTXOs.** A UTXO carries `{pc, locals, methodId, hash}`. It can yield mid-execution and resume later.
2. **Algebraic effect handlers.** Dynamically-scoped, interface-keyed stacks. A coroutine raises an effect; the nearest handler for that interface catches it and resumes the coroutine with a result.
3. **Coordination scripts.** MPST global types compile to PTB bytecode. An IVC witness proves the trace conforms to the protocol.

When nothing yields and nothing raises effects, it degenerates to standard eUTXO.

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Coordination Script                       │
│              (MPST global type → PTB bytecode)               │
└─────────────────────────────────────────────────────────────┘
                              │
                              │ IVC witness
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                      Transaction                             │
│   ┌──────────┐  ┌──────────┐  ┌──────────┐                  │
│   │  Input   │  │  Input   │  │  Output  │  ...             │
│   │  UTXO    │  │  UTXO    │  │  UTXO    │                  │
│   └────┬─────┘  └────┬─────┘  └──────────┘                  │
│        │             │                                       │
│        ▼             ▼                                       │
│   ┌──────────────────────────────────────┐                  │
│   │         Coroutine Frames             │                  │
│   │  {pc, locals, methodId, hash}        │                  │
│   └──────────────────────────────────────┘                  │
│        │                                                     │
│        │ raise                                               │
│        ▼                                                     │
│   ┌──────────────────────────────────────┐                  │
│   │     Effect Handler Stacks            │                  │
│   │  interface₁ → [H₃, H₂, H₁]           │                  │
│   │  interface₂ → [H₁]                   │                  │
│   └──────────────────────────────────────┘                  │
└─────────────────────────────────────────────────────────────┘
                              │
                              │ commit
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                        Ledger                                │
│   utxoSet ∪ consumed = ∅    (no double spend)               │
│   Σ inputs = Σ outputs      (token conservation)            │
└─────────────────────────────────────────────────────────────┘
```

```
tla/   TLA+ spec and TLC model checker configs
lean/  Lean 4 mechanization
paper/ Academic paper
specs/ Design notes
```

## Implementation

This is the spec. The implementation is [Starstream](https://github.com/LFDT-Nightstream/Starstream).

Done in Starstream: parser, typechecker, effect kinds, WASM codegen, UTXO storage.

Not yet: coroutines, effect handlers, tx lifecycle, proofs, coordination scripts.

See [IMPLEMENTATION-STATUS.md](./IMPLEMENTATION-STATUS.md) for details.

## What's verified

### TLA+ invariants (checked by TLC)

A sample — see `tla/StarstreamInvariants.tla` for all 50+:

| Invariant | What it says |
|-----------|--------------|
| `INV_LINEAR_NoDoubleSpend` | Active UTXOs and consumed set are disjoint |
| `INV_BALANCE_TxPreserved` | Input tokens = output tokens per committed tx |
| `INV_EFFECT_SourceSuspended` | Pending effect sources are suspended and locked |
| `INV_PROOF_CommittedVerified` | Committed txs had verified proofs |
| `INV_CIRCUIT_NoSelfResume` | A coroutine can't resume itself |
| `INV_ATK_NoReplay` | Consumed UTXOs can't reappear |

### Lean 4 theorems

The pilot proves core properties without `sorry` or custom axioms:

| Theorem | What it says |
|---------|--------------|
| `verified_reachable` | Proof phase can reach Verified from NotStarted |
| `committing_reachable` | Tx phase can reach Committing from Idle |
| `commit_requires_proof` | Any commit step requires verified proofs |
| `circuit_witness_implies_serial_step` | Valid ZK witness satisfies serial semantics |
| `acyclic_precgraph_serializable` | Acyclic precedence graphs are serializable |
| `list_eq_self_append_singleton` | A list can't equal itself plus an element |
| `append_right_cancel` | Right-cancellation for list append |

See `lean/README.md` for the full inventory including proof obligations still marked `sorry`.

### What's NOT proved

- Liveness (TLC can check it but it's slow; disabled by default)
- Full refinement theorem (`concurrent_refines_serial` has a skeleton)
- Effect handler termination

## Build

### TLA+ (TLC)

```bash
cd tla
java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg
```

If TLC runs out of memory, reduce bounds in `Starstream.cfg` or disable liveness.

### Lean

```bash
cd lean
lake build
```

Requires Lean 4 v4.27.0 (pinned in `lean-toolchain`).

## Reading order

For the model:
1. `specs/iceUTXO.md` — the core technical idea
2. `tla/StarstreamSpec.tla` — Init, Next, and the 30+ actions
3. `tla/StarstreamInvariants.tla` — all the safety properties

For the proofs:
1. `lean/StarstreamPilot.lean` — core types and phase transitions
2. `lean/README.md` — proof inventory and what's still TODO

## Credits

Code documentation by Claude.

## License

Apache 2.0
