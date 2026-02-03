# Verification strategy

This document explains why we use formal verification for Starstream, what we model, and how we run checks.

## Why formal verification?

### The problem with testing

Traditional testing has limitations for blockchain protocols:

1. **Combinatorial explosion** - A protocol with N UTXOs and M transactions has exponentially many possible interleavings
2. **Edge cases** - Rare but high-impact scenarios (concurrent double-spend attempts) are hard to trigger
3. **Specification gaps** - Tests verify implementation matches test cases, not that the design is correct

### Why TLA+?

TLA+ is a specification language that enables:

- **Exhaustive state exploration** - Model checker explores all reachable states
- **Precise specification** - Mathematical definition of correct behavior
- **Widely used** - Used by AWS, Azure, MongoDB, and other production systems
- **Readable specifications** - Closer to design documents than code

### What model checking provides

```
Traditional Testing:    Formal Verification:

  Test Case 1 ----+     +---- All States ----+
  Test Case 2 ----+--> |                     |--> Invariant Holds
  Test Case 3 ----+     +---- (exhaustive) --+    OR Counterexample
  ...
  (incomplete)          (complete within bounds)
```

## What we model

### UTXO lifecycle

The specification models the UTXO lifecycle:

```
Created --> Suspended_at_Yield <--> Reserved <--> Executing
    |              |                    |             |
    v              v                    v             v
    +------------->+<-------------------+             |
                   |                                  |
                   +------ Consumed <-----------------+
```

**States modeled:**
- `Created` - Just created, not yet yielded
- `Suspended_at_Yield` - Yielded, waiting for next action
- `Suspended_at_Effect` - Raised an effect, waiting for handler
- `Reserved` - Locked by a pending transaction
- `Executing` - Running in transaction context
- `Consumed` - Spent (final state)

**Note:** `BeginExecuteUTXO` / `EndExecuteUTXO` are wired into `StarstreamSpec`. Inputs move to `Executing` during execution and return to `Reserved` before commit.

### Transaction phases

Transaction lifecycle with coordination:

```
Idle --> Reserve --> Executing --> Committing --> Committed
            |            |              |
            v            v              v
         Failed <--------+<-------------+
```

**Phases modeled:**
- `Idle` - Transaction not started
- `Reserve` - Inputs locked, gathering resources
- `Executing` - Running coordination script
- `Committing` - Validating and committing
- `Rollback` - Aborting and releasing locks
- `Committed` - Successfully completed
- `Failed` - Aborted with reason

**Note:** `Committing` and `Rollback` are transitioned by `StarstreamSpec` as explicit intermediate phases.

The repository also includes an **optimistic-concurrency variant** (`StarstreamSpecOptimistic.tla`) that executes without locking and validates read/write sets at commit time.

### Algebraic effect system

Effects that can be raised and handled during execution:

- **Effect kinds**: `Pure`, `Effectful`, `Runtime`
- **Effect stack**: LIFO ordering of pending effects
- **Interfaces + handlers**: effects are scoped to interfaces and routed via per-interface handler stacks
- **Handler results**: Success/failure with payload
- **Effect depth bound**: bounded by `MAX_EFFECT_DEPTH` in the model

In the PTB-driven spec, `ProcessPTBEvent` executes `Raise`/`Resume` events: the Raise event transitions the source input UTXO to `Suspended_at_Effect`, and the Resume event moves it back to `Executing`. The `HandleTxEffect` action corresponds to the Resume case and is used for liveness fairness.

**Implementation note:** In production, `continuationId` must be a cryptographic commitment to the suspended frame
(for example, `hash(frame || nonce)`), not a predictable sequence.

### Coordination script authorization model

Coordination scripts are part of the signed transaction contents. The signature digest
(`TxContentsHash`) commits to inputs, outputs, read/write sets, proof commitments, and the
coordination state (calls, outputs, effects), so a signer explicitly authorizes the script and
execution footprint that will be executed. The spec also includes adversarial transactions with
invalid signatures or wrong owners and requires they be rejected before commit.

### Multi-transaction concurrency

- Multiple pending transactions can exist simultaneously
- Each transaction locks its input UTXOs exclusively
- Concurrent transactions cannot share inputs

### Token conservation

- Token bags map `(type, id) -> quantity`
- Sum of inputs must equal sum of outputs
- NFTs are unique (at most one per ID across all UTXOs)

## What we don't model

### Cryptographic primitives

Signatures are modeled abstractly:

```tla
ValidSignature(sig, tx) ==
    /\ sig.owner = tx.signer
    /\ sig.txId = tx.id
    /\ sig.contentsHash = TxContentsHash(tx)
```

We assume cryptographic operations work correctly. The specification focuses on protocol logic, not crypto implementation details.

Transactions are constructed and re-signed via `SignTx`, so malformed signatures or wrong-owner inputs are
not explored unless adversarial actions are added.

The signature digest commits to **ordered** coordination data (call sequence, output specs, and effect stack), so reordering is modeled as a different transaction. It also commits to read/write sets and proof commitments, binding optimistic execution and interleaving proofs to the signature.

The digest also commits to `CHAIN_ID` and `BLOCK_HEIGHT` to bind signatures to chain context and prevent cross-chain/height replay.

Commits are proof-gated: transactions must have verified proof commitments (`AllTxProofsVerified`) before `BeginCommit`/`CommitTx` will succeed.
Frame integrity requires collision-resistant hashing (SHA-256 or stronger) to prevent forged frames from passing `INV_FRAME_Integrity`.

### Network and consensus

The model is **asynchronous single-node**:
- No network partitions or message loss
- No Byzantine faults
- No consensus protocol details

This is a good fit because:
- UTXO protocol correctness is independent of consensus
- Network layer provides eventual delivery
- Consensus provides total ordering

### Smart contract bytecode

Contract execution is abstracted:
- Method calls are atomic operations
- State changes are direct record updates
- No gas metering or execution limits

### Adversarial ordering

The model explores all **interleavings** within the configured bounds, but it does not model
external scheduling or network-level ordering beyond those interleavings.

### Fees and economics

No modeling of:
- Transaction fees
- Gas costs
- Economic incentives

## Verification strategy

### Phase 1: type invariants

Ensure data structures are well-formed:

```tla
INV_TYPE_All ==
    /\ TypeOK
    /\ INV_TYPE_LedgerWellTyped
    /\ INV_TYPE_FramesWellTyped
    /\ INV_TYPE_TokenBagsWellTyped
    /\ INV_TYPE_PendingTxWellTyped
```

**Run first** - Type errors cause confusing failures in other invariants.

### Phase 2: safety invariants

Key protocol properties:

| Category | Key Invariants |
|----------|---------------|
| Linear types | `INV_LINEAR_NoDoubleSpend`, `INV_LINEAR_NoDoubleConsume` |
| Balance | `INV_BALANCE_TxPreserved`, `INV_BALANCE_NFTUnique` |
| Authorization | `INV_AUTH_ValidSpend`, `INV_AUTH_OwnerOnly` |
| Lifecycle | `INV_LIFECYCLE_ConsumedIsFinal` |
| Locking | `INV_LOCK_Exclusive`, `INV_LOCK_ValidReservation` |

### Phase 3: liveness properties

Progress checks (require fairness):

```tla
LIVE_TxEventuallyCommits ==
    \A txId \in TxIdRange :
        (<>[]CommitEnabled(txId)) => <>CommittedTxId(txId)
```

```tla
LIVE_TxEventuallyTerminates ==
    \A txId \in TxIdRange :
        []( PendingTxId(txId) => <>~PendingTxId(txId) )
```

Use `FairSpec` or `StrongFairSpec` for liveness checking.

### Fairness requirements (which spec to use)

| Property | Spec to use | Fairness assumption |
|----------|-------------|---------------------|
| `LIVE_TxEventuallyCommits` | `MC_FairSpec` | Weak fairness (commit eventually if continuously enabled) |
| `LIVE_TxEventuallyTerminates` | `MC_FairSpec` | Weak fairness (commit/abort eventually if enabled) |
| `LIVE_CanReturnToIdle` | `MC_FairSpec` | Weak fairness (transactions eventually complete) |
| `LIVE_EffectsEventuallyHandled` | `MC_StrongFairSpec` | Strong fairness on `HandleTxEffect` (PTB Resume) |

**Note:** Safety invariants (all `INV_*`) do **not** require fairness.

### Incremental approach

1. Start with type invariants only
2. Add one safety invariant at a time
3. If violation found, fix spec or invariant
4. Once safety passes, add liveness

## Threat model

| Attack | Preventing Invariant | Description |
|--------|---------------------|-------------|
| Double-spend | `INV_LINEAR_NoDoubleSpend` | Spending same UTXO twice |
| Replay attack | `INV_ATK_NoReplay` | Reusing consumed UTXO ID |
| Unauthorized spend | `INV_AUTH_ValidSpend` | Committed spend without valid signature/owner |
| Token inflation | `INV_BALANCE_TxPreserved` | Creating tokens from nothing |
| NFT duplication | `INV_BALANCE_NFTUnique` | Copying unique tokens |
| Input conflict | `INV_LINEAR_NoDuplication` | Two txs using same input |
| Lock escape | `INV_LOCK_Exclusive` | UTXO unlocked while tx pending |
| Output leak | `INV_ROLLBACK_NoLeak` | Failed tx outputs remain |
| Negative balance | `INV_ATK_NoNegativeTokens` | Token quantity < 0 |
| ID reuse | `INV_ATK_IdMonotonic` | UTXO ID used before allocated |

## Confidence level

### Bounded model checking

TLA+ model checking is **bounded**:
- Explores all states within configured bounds
- Does not prove properties for unbounded systems
- Sufficient for finding bugs, not absolute proof

### Chosen bounds

```tla
MAX_UTXOS = 3          -- Covers 1, 2, 3 UTXO interactions
MAX_TX_INPUTS = 2      -- Covers single and multi-input txs
MAX_PENDING_TXS = 2    -- Covers concurrent transaction conflicts
MAX_FRAME_VARS = 4     -- Bounds local variable space
MAX_TOKEN_TOTAL = 4    -- Bounds per-asset totals for overflow checks
UTXO_ID_BOUND = 8      -- Allows multiple tx cycles
CHAIN_ID = 1           -- Chain context for replay protection
BLOCK_HEIGHT = 0       -- Block height for replay protection
```

These bounds aim to:
1. Cover common interaction patterns
2. Keep state space manageable (< 10^9 states)
3. Exercise the main code paths in the specification

### Symmetry reduction

The specification supports symmetry sets:

```tla
TokenTypeSymmetry == Permutations(MC_TOKEN_TYPES)
OwnerSymmetry == Permutations({"Alice", "Bob", "Charlie"})
```

Symmetry reduction can reduce state space when enabled.
It is **optional** and disabled by default in `Starstream.cfg` (the SYMMETRY line is commented out).

### What we can claim

**Within bounds, we can say:**
- Protocol logic is correct for modeled behaviors
- No double-spend or inflation within bounds
- Committed transactions are authorized (signature + owner) within bounds
- Transaction lifecycle maintains consistency

**Cannot claim:**
- Correctness for unbounded systems
- Implementation matches specification
- Cryptographic security
- Network-level attack resistance

## Relationship to implementation

```
Specification          Implementation
     |                      |
     v                      v
  TLA+ Model    <----->   Code
     |          refines     |
     v                      v
  Invariants   <----->   Tests
     |          cover       |
     v                      v
  Verified     <----->   Tested
```

The specification serves as:
1. **Design document** - Protocol description
2. **Test oracle** - Expected behavior reference
3. **Review artifact** - Lets auditors check protocol logic

