# TLA+ Specification for Starstream UTXO/Transaction Protocol

## Overview

Create a modular TLA+ specification that models Starstream's UTXO/transaction protocol layer, enabling model checking of critical safety properties (no double-spend, balance preservation, linear consumption, authorization).

---

## Concurrency Model Decision

**Choice: Pessimistic Locking (Conservative Baseline)**

We model pessimistic locking as the conservative baseline. An optimistic variant (read-set/write-set validation) exists but is out of scope for TLC until the locking model stabilizes.

Transactions are NOT modeled as atomic. Instead, we model explicit phases:
1. **Reserve** - Lock input UTXOs atomically or in deterministic order (by UTXO id); partial locks trigger immediate rollback
2. **Execute** - Run coordination script, handle effects
3. **Commit** - Apply changes to ledger (on success); only step that mutates `utxoSet`/`consumedSet`
4. **Rollback** - Release locks, restore state (on failure)

**Lock Acquisition Semantics**: Reserve locks all inputs atomically OR in ascending UTXO id order. If any lock fails, all acquired locks are released immediately (no partial lock holding). This prevents deadlocks.

This exposes race conditions and rollback semantics for model checking.

---

## Module Structure

```
tla/
├── StarstreamTypes.tla          # Foundation types, constants, enums
├── StarstreamFrame.tla          # Stackless coroutine Frame (PC + locals)
├── StarstreamEffects.tla        # Effect system with continuation IDs
├── StarstreamUTXO.tla           # UTXO state machine with Executing state
├── StarstreamAuth.tla           # Authorization and signature verification
├── StarstreamCoordination.tla   # Coordination script execution
├── StarstreamTransaction.tla    # Transaction phases (reserve/execute/commit/rollback)
├── StarstreamLedger.tla         # Global ledger state with locks
├── StarstreamSpec.tla           # Top-level composition
├── StarstreamInvariants.tla     # All safety and liveness properties
├── MC_Starstream.tla            # TLC model checking config
└── Starstream.cfg               # TLC configuration file
```

---

## Key Types to Model

| Type | Fields |
|------|--------|
| `UTXORecord` | id, state, frame, datum, tokens, contractId, owner, **lockedBy**, **protocolState** |
| `Frame` | pc, locals, methodId, **frameHash** (integrity check) |
| `EffectRecord` | kind, sourceUtxoId, value, handled, **continuationId**, **tag**, **payload**, **handlerId**, **scopeId** |
| `TransactionRecord` | id, phase, inputs, coordination, outputs, result, **signature**, **txContentsHash** |
| `LedgerState` | utxoSet, consumedSet, **lockedSet**, nextUtxoId, pendingTxs (plural), txHistory |
| `TokenBalance` | **[TokenType -> [TokenId -> Amount]]** (per-asset, per-id accounting) |

### Protocol State (Session Types)

`protocolState` tracks UTXO session state for valid action sequencing:
```
Created → Yielded → (Effect ↔ Resumed)* → Consumed
```

Actions are guarded by protocol state:
- `Reserve`: only when `protocolState = Yielded`
- `RaiseEffect`: only when `protocolState ∈ {Yielded, Resumed}`
- `HandleEffect`: only when `protocolState = Effect`
- `Consume`: only when `protocolState = Yielded`

---

## UTXO State Machine (Revised)

```
                              ┌──────────────┐
                              │   Created    │
                              └──────┬───────┘
                                     │ (initial yield)
                                     ▼
┌─────────────────────────────────────────────────────────────────┐
│                      Suspended_at_Yield                         │
│  (can be: queried, reserved for tx, resumed)                    │
└──────┬──────────────────┬───────────────────────┬───────────────┘
       │ (reserve)        │ (resume/mutate)       │ (raise)
       ▼                  ▼                       ▼
┌──────────────┐   ┌──────────────┐       ┌──────────────────────┐
│   Reserved   │   │  Executing   │       │ Suspended_at_Effect  │
│ (locked by   │   │ (running in  │       │ (waiting for handler │
│  pending tx) │   │  tx context) │       │  to resume)          │
└──────┬───────┘   └──────┬───────┘       └──────────┬────────────┘
       │                  │ (yield/raise/complete)   │ (handle+resume)
       │                  ▼                          │
       └─────────> Suspended_at_Yield <──────────────┘
                          │
                          │ (consume in committed tx)
                          ▼
                   ┌──────────────┐
                   │   Consumed   │
                   └──────────────┘
```

**Key addition**: `Reserved` and `Executing` states to model in-flight transactions.

---

## Transaction Phases

```
┌─────────┐     ┌───────────┐     ┌───────────┐     ┌──────────┐
│  Idle   │────>│  Reserve  │────>│  Execute  │────>│  Commit  │
└─────────┘     └─────┬─────┘     └─────┬─────┘     └──────────┘
                      │                 │
                      │ (lock fail)     │ (exec fail)
                      ▼                 ▼
               ┌────────────────────────────┐
               │         Rollback           │
               │ (release locks, no change) │
               └────────────────────────────┘
```

---

## Critical Invariants (Hardened)

### Type Invariants
1. **INV_TYPE_All**: All records conform to type predicates

### Authorization Invariants (Strengthened)
2. **INV_AUTH_ValidSpend**: `Consume(utxo) => ValidSignature(tx.signature, utxo.owner, tx.txContentsHash)`
3. **INV_AUTH_OwnerOnly**: Only owner can initiate spend of their UTXO
4. **INV_AUTH_ContentBinding**: `tx.txContentsHash = Hash(tx.inputs, tx.outputs, tx.coordination.id, tx.effectCommitments)`
5. **INV_AUTH_NoReplay**: Each `tx.id` is globally unique (prevents signature replay)

### Balance Invariants (Strengthened)
4. **INV_BALANCE_PerAsset**: For each `(tokenType, tokenId)`: `sum(inputs) = sum(outputs) + burned - minted`
5. **INV_BALANCE_NFTUnique**: Each NFT tokenId appears in at most one UTXO

### Linear Consumption Invariants (Explicit)
6. **INV_LINEAR_ExactlyOnce**: Each UTXO consumed by exactly one transaction
7. **INV_LINEAR_NoDoubleSpend**: `lockedSet ∩ consumedSet = {}`
8. **INV_LINEAR_NoDuplication**: No UTXO ID appears in multiple pending transactions
9. **INV_LINEAR_ConsumedTracked**: `∀ consumed UTXO: id ∈ consumedSet`

### Lock/Reservation Invariants (Strengthened)
10. **INV_LOCK_Exclusive**: Each UTXO locked by at most one transaction
11. **INV_LOCK_ValidReservation**: `Reserved(utxo) => utxo.lockedBy ∈ pendingTxs`
12. **INV_LOCK_ReleasedOnRollback**: Rollback releases all locks held by that tx
13. **INV_LOCK_NoPartialHold**: No tx holds a strict subset of its input locks indefinitely (deadlock prevention)
14. **INV_LOCK_OrderedAcquisition**: Locks acquired in ascending UTXO id order (or atomically)

### Effect Handling Invariants (Strengthened)
15. **INV_EFFECT_ContinuationMatch**: `Handle(effect) => effect.continuationId = resumed_utxo.frame.id`
16. **INV_EFFECT_NoSpoofing**: Cannot mark effect handled without valid resumption
17. **INV_EFFECT_MustBeHandled**: Complete transaction has no pending effects
18. **INV_EFFECT_HandlerIdentity**: `Handle(effect) => effect.handlerId = currentHandler.id` (correct handler resumes)
19. **INV_EFFECT_StackOrder**: Effects handled in LIFO order within a scope (stack semantics for nested effects)

### Frame Integrity Invariants (NEW)
16. **INV_FRAME_Integrity**: `Resume(utxo, frame) => frame.frameHash = hash(stored_frame)`
17. **INV_FRAME_NoSwap**: Resumed frame must match the UTXO's stored continuation
18. **INV_FRAME_PCMonotonic**: PC only changes via valid execution steps

### Structural Invariants (Design Constraints)
19. **INV_STRUCT_NoUTXOCallsUTXO**: UTXOs cannot directly invoke other UTXOs
20. **INV_STRUCT_NoNestedTokens**: Tokens cannot own tokens
21. **INV_STRUCT_UniqueIds**: All UTXO IDs are unique and monotonically increasing

### Protocol/Session Invariants (NEW)
22. **INV_PROTO_ValidState**: `utxo.protocolState ∈ {Created, Yielded, Effect, Resumed, Consumed}`
23. **INV_PROTO_ActionGuard**: Actions enabled only in correct protocol state (see Protocol State section)
24. **INV_PROTO_Consume**: `Consume(utxo) => utxo.protocolState = Yielded`

### Rollback Invariants
25. **INV_ROLLBACK_NoLeak**: Failed tx does not modify ledger state (no partial updates)
26. **INV_ROLLBACK_ResourceConservation**: `Failed(tx) => ledger' = ledger` (except locks released)

### Serializability Invariant (NEW)
29. **INV_SERIAL_Equivalent**: Every interleaving trace is equivalent to some serial commit order (refinement mapping)

### Proof/Verification Invariants (Clarified)

**Proof validity is modeled as a predicate on state transitions.** TLC treats invalid proofs as disabling actions. Correctness depends on proof system soundness (assumed).

26. **INV_PROOF_GatedTransition**: `Commit(tx) => ValidProof(tx, ledger_before, ledger_after)`
27. **INV_PROOF_MCCIntegrity**: `StorageUpdate(utxo, old, new) => ValidMCC(utxo.id, old, new)`
28. **INV_PROOF_TransitionSemantics**: `ValidProof` binds to transition semantics (inputs, outputs, effects)

---

## Liveness Properties

**Fairness Requirements**: Liveness properties require weak fairness (WF) on `Commit` and `Rollback` actions. Without fairness, TLC can stall in lock-held loops.

1. **LIVE_TxEventuallyTerminates**: `Executing(tx) ~> (Committed(tx) ∨ RolledBack(tx))` [WF on Commit, Rollback]
2. **LIVE_EffectsEventuallyHandled**: `PendingEffect(e) ~> (Handled(e) ∨ TxFailed)` [WF on HandleEffect]
3. **LIVE_LocksEventuallyReleased**: `Locked(utxo) ~> (Consumed(utxo) ∨ Unlocked(utxo))` [WF on Commit, Rollback]
4. **LIVE_CanReturnToIdle**: `□◇(phase = IDLE)`
5. **LIVE_NoDeadlock**: `□(∃ enabled action)` (system never deadlocks)

---

## Counterexample Scenarios to Defend

| Attack | Defense (Invariant) |
|--------|---------------------|
| Concurrent spend race | INV_LOCK_Exclusive, INV_LINEAR_NoDuplication |
| Unauthorized spend | INV_AUTH_ValidSpend, INV_AUTH_OwnerOnly |
| Signature replay | INV_AUTH_NoReplay, INV_AUTH_ContentBinding |
| Effect spoofing | INV_EFFECT_ContinuationMatch, INV_EFFECT_NoSpoofing, INV_EFFECT_HandlerIdentity |
| Nested effect ordering | INV_EFFECT_StackOrder |
| Frame swap attack | INV_FRAME_Integrity, INV_FRAME_NoSwap |
| Type-mixing balance bypass | INV_BALANCE_PerAsset (per tokenType+tokenId) |
| Partial failure leak | INV_ROLLBACK_NoLeak, INV_ROLLBACK_ResourceConservation |
| UTXO calling UTXO | INV_STRUCT_NoUTXOCallsUTXO |
| Deadlock via lock contention | INV_LOCK_OrderedAcquisition, INV_LOCK_NoPartialHold, LIVE_NoDeadlock |
| Protocol state violation | INV_PROTO_ActionGuard, INV_PROTO_Consume |
| Non-serializable interleaving | INV_SERIAL_Equivalent |

---

## Model Checking Bounds

```tla
MAX_UTXOS = 4           \* Max UTXOs in ledger
MAX_PENDING_TXS = 2     \* Max concurrent pending transactions (for race detection)
MAX_TX_INPUTS = 2       \* Max inputs per transaction
MAX_TX_OUTPUTS = 2      \* Max outputs per transaction
MAX_FRAME_VARS = 4      \* Max local variables in Frame
MAX_EFFECTS = 3         \* Max pending effects
TOKEN_TYPES = {"ADA", "NFT"}
TOKEN_IDS = {1, 2, 3}   \* For NFT uniqueness checking
UTXO_ID_BOUND = 10      \* Max UTXO identifier value
OWNERS = {"Alice", "Bob", "Eve"}  \* For authorization testing
```

---

## Implementation Order

### Phase 1: Foundation + Auth
- `StarstreamTypes.tla` - Types with per-asset token balances
- `StarstreamFrame.tla` - Frame with frameHash for integrity
- `StarstreamAuth.tla` - Signature verification predicates

### Phase 2: Core + Locking
- `StarstreamUTXO.tla` - State machine with Reserved/Executing states, lockedBy field
- `StarstreamEffects.tla` - Effects with continuationId, tag, payload

### Phase 3: Transactions + Rollback
- `StarstreamCoordination.tla` - Script execution with effect handling
- `StarstreamTransaction.tla` - Phase-based model (reserve/execute/commit/rollback)

### Phase 4: Ledger + Concurrency
- `StarstreamLedger.tla` - Multiple pending transactions, lock management
- `StarstreamSpec.tla` - Top-level with concurrent transaction interleaving

### Phase 5: Invariants + Model Checking
- `StarstreamInvariants.tla` - All 29 invariants + 5 liveness properties
- `MC_Starstream.tla` - Configuration for race condition detection

---

## Verification Strategy

1. **Syntax check**: `java -jar tla2tools.jar -parse StarstreamSpec.tla`
2. **Single-tx invariants**: Model check with `MAX_PENDING_TXS = 1`
3. **Concurrency invariants**: Model check with `MAX_PENDING_TXS = 2` (exposes races)
4. **Attack scenarios**: Manually inject attack states, verify invariants catch them
5. **Liveness**: Enable `FairSpec`, check temporal properties
6. **Coverage**: Ensure all actions are reachable in traces

---

## Files to Create

| File | Lines (est.) | Priority | Key Content |
|------|--------------|----------|-------------|
| `StarstreamTypes.tla` | ~120 | P1 | Per-asset token types, owner types |
| `StarstreamFrame.tla` | ~60 | P1 | Frame with hash, integrity predicates |
| `StarstreamAuth.tla` | ~40 | P1 | ValidSignature, ownership checks |
| `StarstreamUTXO.tla` | ~150 | P1 | 6-state machine, lock predicates |
| `StarstreamEffects.tla` | ~100 | P2 | Continuation-aware effect handling |
| `StarstreamCoordination.tla` | ~120 | P2 | Script execution, method dispatch |
| `StarstreamTransaction.tla` | ~140 | P2 | 4-phase tx model, rollback |
| `StarstreamLedger.tla` | ~100 | P3 | Multi-tx ledger, lock management |
| `StarstreamSpec.tla` | ~180 | P3 | Concurrent actions, interleaving |
| `StarstreamInvariants.tla` | ~250 | P3 | All 29 invariants, 5 liveness |
| `MC_Starstream.tla` | ~60 | P3 | Attack scenario configs |
| `Starstream.cfg` | ~30 | P3 | TLC configuration |

---

## Rebuttal Traceability

### Round 1 (Original Critique)

| Rebuttal Critique | Resolution |
|-------------------|------------|
| **Atomicity vs interleaving not defined** | Added explicit 4-phase tx model: Reserve→Execute→Commit/Rollback |
| **Authorization absent** | Added `StarstreamAuth.tla`, INV_AUTH_ValidSpend, INV_AUTH_OwnerOnly |
| **Effect handling too abstract** | Added continuationId to EffectRecord, INV_EFFECT_ContinuationMatch |
| **No proof/verification gating** | Added INV_PROOF_GatedTransition, INV_PROOF_MCCIntegrity |
| **Balance invariant too coarse** | Changed to `[TokenType -> [TokenId -> Amount]]` per-asset accounting |
| **Missing Executing state** | Added `Reserved` and `Executing` to UTXO state machine |
| **No in-flight lock/reservation** | Added `lockedBy` field, `lockedSet`, INV_LOCK_* invariants |
| **Failure/rollback undefined** | Added Rollback phase, INV_ROLLBACK_NoLeak, INV_ROLLBACK_ResourceConservation |
| **Coordination under-specified** | Added phase-based execution with explicit method dispatch |
| **Linearity not modeled** | Added INV_LINEAR_ExactlyOnce explicitly |
| **UTXO cannot call UTXO missing** | Added INV_STRUCT_NoUTXOCallsUTXO |
| **Tokens cannot own tokens missing** | Added INV_STRUCT_NoNestedTokens |
| **Effects vs runtime conflated** | Kept separate EffectKind values; handler dispatch checks kind |
| **Frame integrity not enforced** | Added frameHash, INV_FRAME_Integrity, INV_FRAME_NoSwap |
| **Single pendingTx hides concurrency** | Changed to `pendingTxs` (plural), MAX_PENDING_TXS = 2 |
| **consumedSet not sufficient** | Added INV_LINEAR_ExactlyOnce: "consumed by exactly one tx" |
| **No ID monotonicity** | Added INV_STRUCT_UniqueIds with monotonicity requirement |
| **No mint/burn modeling** | Added to INV_BALANCE_PerAsset formula: `+ burned - minted` |

### Round 2 (Revised Critique)

| Rebuttal Critique | Resolution |
|-------------------|------------|
| **Lock acquisition semantics undefined** | Added atomic/ordered lock acquisition, INV_LOCK_OrderedAcquisition, INV_LOCK_NoPartialHold |
| **Liveness needs fairness** | Added WF requirements on Commit/Rollback actions, LIVE_NoDeadlock |
| **Authorization doesn't bind contents** | Strengthened to `ValidSignature(sig, owner, txContentsHash)`, added INV_AUTH_ContentBinding |
| **Proof gating is vacuous** | Clarified: ValidProof binds to transition semantics, added INV_PROOF_TransitionSemantics |
| **Effect handler identity missing** | Added `handlerId`, `scopeId` to EffectRecord, INV_EFFECT_HandlerIdentity, INV_EFFECT_StackOrder |
| **No session-typed protocol state** | Added `protocolState` field, Protocol State section, INV_PROTO_* invariants |
| **Serializable-trace property implicit** | Added INV_SERIAL_Equivalent refinement mapping |
| **Alignment with interleavingTypes.md** | Added note: "pessimistic locking as conservative baseline" |

---

## Reference Files

- `/c/starstream/docs/language-spec.md` - Authoritative language semantics
- `/c/starstream/docs/design.md` - UTXO/coroutine/effect architecture
- `/c/starstream/rebuttal.md` - Red-team critique (addressed in this plan)
- `/c/starstream/starstream-types/src/ast.rs` - UTXO/Effect AST definitions
