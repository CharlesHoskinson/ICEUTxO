# State machines

This document describes all state machines in the Starstream TLA+ specification with diagrams and transition tables.

## UTXO lifecycle

UTXOs progress through a defined lifecycle from creation to consumption.

### State diagram

**Note:** `pc` means *program counter* (the resume point for a UTXO’s coroutine).

```
                                +------------------+
                                |     Created      |
                                |    (pc = 0)      |
                                +--------+---------+
                                         |
                                         | YieldUTXO
                                         v
    +------------------+          +----------------+          +----------------+
    | Suspended_at     |<-------->|    Reserved    |<-------->|    Executing   |
    |     Yield        |  Release |   (locked)     | BeginEx  |   (locked)     |
    |    (pc >= 0)     |          +-------+--------+          +-------+--------+
    +------------------+                  |                           |
            ^                              \                         |
            |                               \ RaiseEffect            |
            |                                v                       |
            |                          +------+--------+             |
            +--------------------------| Suspended_at  |-------------+
              HandleEffect             |    Effect     |   Resume
                                       |   (pc >= 0)   |
                                       +------+--------+
                                              |
                                       Consume (commit)
                                              |
                                              v
                                      +-------+--------+
                                      |    Consumed    |
                                      |   (pc = -1)    |
                                      |    [FINAL]     |
                                      +----------------+
```

**Note:** Consumption happens from `Executing`/`Reserved` during commit; the diagram focuses on the effect path around execution.

### State descriptions

| State | Description | PC | LockedBy |
|-------|-------------|-----|----------|
| `Created` | Just created, initial frame | 0 | NO_TX |
| `Suspended_at_Yield` | Yielded, waiting for action | >= 0 | NO_TX |
| `Suspended_at_Effect` | Raised effect, waiting for handler | >= 0 | txId |
| `Reserved` | Locked by pending transaction | >= 0 | txId |
| `Executing` | Running in transaction context | >= 0 | txId |
| `Consumed` | Spent, final state | -1 | N/A |

### Transition table

| From | Action | To | Preconditions |
|------|--------|----|---------------|
| Created | `YieldUTXO` | Suspended_at_Yield | - |
| Suspended_at_Yield | `ReserveTx` | Reserved | `lockedBy = NO_TX` |
| Reserved | `BeginExecute` | Executing | Tx in Reserve phase |
| Reserved | `ReleaseReservation` | Suspended_at_Yield | Tx aborted |
| Executing | `EndExecute` | Reserved | - |
| Executing | `RaiseEffect` | Suspended_at_Effect | Effect raised by input UTXO |
| Suspended_at_Effect | `HandleEffect` | Executing | Handler result available |
| Executing | `ConsumeUTXO` | Consumed | Tx commits |
| * | `FinishRollback` | Suspended_at_Yield | (releases lock) |

**Note:** In the current spec, `BeginExecuteUTXO`/`EndExecuteUTXO` are wired into `BeginExecute`/`FinalizeTx`, and effect handling transitions inputs into `Suspended_at_Effect` and back to `Executing`.

### TLA+ operators

```tla
\* State predicates
IsLive(u) == u.state # "Consumed"
CanReserve(u) == u.state = "Suspended_at_Yield" /\ u.lockedBy = NO_TX
CanQuery(u) == u.state \in {"Suspended_at_Yield", "Reserved", "Executing"}

\* Transitions
ReserveUTXO(u, txId) == [u EXCEPT !.state = "Reserved", !.lockedBy = txId]
ConsumeUTXO(u) == [u EXCEPT !.state = "Consumed", !.frame = Terminate(u.frame)]
```

---

## Transaction phases

Transactions follow a multi-phase lifecycle.

### State diagram

```
+--------+     ReserveTx     +-----------+    BeginExecute    +------------+
|  Idle  |------------------>|  Reserve  |------------------->| Executing  |
+--------+                   +-----+-----+                    +-----+------+
                                   |                                |
                                   | StartRollback                   | BeginCommit
                                   |                                v
                                   v                         +------+------+
                            +------+------+                  | Committing  |
                            |  Rollback  |<------------------+------+------+
                            +------+------+                         |
                                   |                                | CommitTx
                                   | FinishRollback                 v
                                   v                         +------+------+
                            +-------------+                   |  Committed  |
                            |   Failed    |<------------------+   [FINAL]   |
                            |   [FINAL]   |                   +-------------+
                            +-------------+
```

**Note:** `Committing` and `Rollback` are wired into `StarstreamSpec` to model a two-step commit/abort path.

### Phase descriptions

| Phase | Description | Inputs Locked | Outputs Created |
|-------|-------------|---------------|-----------------|
| `Idle` | Transaction not started | No | No |
| `Reserve` | Inputs locked, gathering | Yes | No |
| `Executing` | Running coordination script | Yes | In progress |
| `Committing` | Validating balance | Yes | Yes |
| `Rollback` | Releasing locks | Being released | Discarded |
| `Committed` | Completed successfully | Consumed | Active |
| `Failed` | Aborted with reason | Released | Discarded |

### Transition table

| From | Action | To | Preconditions |
|------|--------|----|---------------|
| Idle | `ReserveTx` | Reserve | Inputs available and reservable |
| Reserve | `BeginExecute` | Executing | - |
| Reserve | `StartRollback` | Rollback | - |
| Executing | `StartPTB` | Executing | IsGathering, trace provided |
| Executing | `ProcessPTBEvent` | Executing | IsProcessing, PTB has next event |
| Executing | `FinalizeTx` | Executing | IsProcessing, all calls executed, no pending effects |
| Executing | `BeginCommit` | Committing | Balance preserved, all signed |
| Executing | `StartRollback` | Rollback | - |
| Committing | `CommitTx` | Committed | Inputs locked, outputs finalized |
| Rollback | `FinishRollback` | Failed | Locks released |

**Note:** `Committing` and `Rollback` are first-class phases in `StarstreamSpec` to model two-step commit/abort behavior.

### TLA+ operators

```tla
\* Phase predicates
IsCommittedTx(tx) == tx.phase = "Committed"
IsFailedTx(tx) == tx.phase = "Failed"
IsCompleteTx(tx) == tx.phase \in {"Committed", "Failed"}

\* Transitions
CommitTransaction(tx) == [tx EXCEPT !.phase = "Committed", !.result = "Complete"]
AbortTransaction(tx, reason) == [tx EXCEPT !.phase = "Failed", !.result = reason]
```

---

## Coordination phases

Coordination scripts manage method calls within a transaction.

**PTB note:** Coordination is now validated against PTB traces. The call-sequence transitions below describe the legacy `pendingCalls`/`callIndex` path retained for compatibility.

### State diagram

```
+--------------+    BeginGathering    +------------+    BeginProcessing    +--------------+
|  NotStarted  |--------------------->|  Gathering |--------------------->|  Processing  |
+--------------+                      +------------+                      +------+-------+
                                                                                 |
                                                                                 | (calls complete)
                                                                                 v
                                                                          +------+-------+
                                                                          |  Finalizing  |
                                                                          +------+-------+
                                                                                 |
                                                                                 | CompleteCoordination
                                                                                 v
                                                                          +------+-------+
                                                                          |   Complete   |
                                                                          +--------------+
```

### Phase descriptions

| Phase | Description | Calls | Effects |
|-------|-------------|-------|---------|
| `NotStarted` | Coordination not begun | None | Empty |
| `Gathering` | Collecting input UTXOs | None | Empty |
| `Processing` | Executing method calls | In progress | May exist |
| `Finalizing` | Creating output specs | Complete | Must be empty |
| `Complete` | All done | Complete | Empty |

### Transition table

| From | Action | To | Preconditions |
|------|--------|----|---------------|
| NotStarted | `BeginGathering` | Gathering | Input IDs provided |
| Gathering | `BeginProcessing` | Processing | Calls sequence provided |
| Processing | `ExecuteNextCall` | Processing | More calls to execute |
| Processing | `HandleEffectInCoord` | Processing | Effects pending |
| Processing | `BeginFinalizing` | Finalizing | All calls done, no effects |
| Finalizing | `CompleteCoordination` | Complete | - |

### TLA+ operators

```tla
\* Phase predicates
IsProcessing(coord) == coord.phase = "Processing"
IsComplete(coord) == coord.phase = "Complete"
AllCallsExecuted(coord) == coord.callIndex >= Len(coord.pendingCalls)
HasPendingEffects(coord) == PendingEffects(coord.effectStack) # {}

\* Transitions
BeginProcessing(coord, calls) ==
    [coord EXCEPT !.phase = "Processing", !.pendingCalls = calls, !.callIndex = 0]
```

---

## Effect stack

Effects are managed using a stack (LIFO) structure.

### Operations

```
Push Effect:                    Handle (Pop Top Effect):

    +---+                           +---+
    | E3| <- top                    | E2| <- new top
    +---+                           +---+
    | E2|                           | E1|
    +---+                           +---+
    | E1|
    +---+

PushEffect(stack, E4):          HandleTopEffect(stack, result):

    +---+                           +---+
    | E4| <- new top                | E2| <- new top
    +---+                           +---+
    | E3|                           | E1|
    +---+                           +---+
    | E2|
    +---+
    | E1|
    +---+
```

`HandleTopEffect` returns a handler result and pops the handled effect from the stack; the stack tracks only pending effects.

### Effect record

```tla
[kind: EffectKinds,           \* Pure, Effectful, Runtime
 sourceUtxoId: UTXOIdRange,   \* UTXO that raised effect
 continuationId: ...,         \* For resumption
 tag: EffectTags,             \* Effect type tag
 payload: DatumValues,        \* Effect data
 handled: BOOLEAN,            \* Has it been handled?
 interfaceId: InterfaceIdRange,
 handlerStackId: 1..MAX_HANDLER_DEPTH,
 witLedgerKind: WitLedgerEffectKinds]
```

**Interface routing:** Effects are scoped to interfaces; coordination maintains per-interface handler stacks and routes effects to the top handler for that interface.

**Handler stacks:** Handlers are installed/uninstalled during execution (`InstallTxHandler` / `UninstallTxHandler`). Pending effects must have a handler present for their `interfaceId` before they can be processed.

### Stack invariants

1. **ValidEffectStack**: All elements are valid effect records
2. **AllEffectsHandled**: Coordination completion requires no pending effects (handled effects are popped)
3. **NoOrphans**: All effects from known input UTXOs

---

## Frame lifecycle

Frames track coroutine execution state.

### PC values

| PC Value | Meaning |
|----------|---------|
| `0` | Initial state (Created UTXO) |
| `1..10` | Valid execution/yield points |
| `-1` | Terminated (Consumed UTXO) |

### Frame transitions

```
    pc = 0                pc > 0              pc = -1
  +--------+           +--------+           +--------+
  | Initial|---------->|Suspended|--------->|Terminal|
  +--------+  Yield    +--------+  Consume  +--------+
                           ^
                           |
                     Resume/Advance
                           |
                           v
                       +--------+
                       |Execute |
                       +--------+
```

### TLA+ operators

```tla
\* Frame predicates
IsInitialFrame(f) == f.pc = 0
IsTerminatedFrame(f) == f.pc = -1
IsSuspendedFrame(f) == f.pc > 0 /\ f.pc # -1
IsResumableFrame(f) == f.pc >= 0 /\ f.pc # -1

\* Frame operations
AdvancePC(frame, newPC) == Rehash([frame EXCEPT !.pc = newPC])
Terminate(frame) == Rehash([frame EXCEPT !.pc = -1])
```

---

## Sample execution trace

An example transaction end-to-end:

### Initial state

```
ledger:
  utxoSet: {UTXO(1, Alice, 2 ADA), UTXO(2, Bob, 2 ADA)}
  consumedSet: {}
  pendingTxs: {}
  nextUtxoId: 3
  nextTxId: 1
```

### Step 1: ReserveTx({1}, "Alice")

```
Action: Alice reserves UTXO 1
UTXO 1: Suspended_at_Yield -> Reserved, lockedBy = 1
pendingTxs: {Tx(1, Alice, inputs={UTXO 1}, phase=Reserve)}
nextTxId: 2
```

### Step 2: BeginExecute(1)

```
Action: Begin executing transaction 1
Tx 1: phase = Reserve -> Executing
```

### Step 3: StartProcessing(1, <<ConsumeCall(1, 0, "Empty")>>)

```
Action: Start processing with consume call
Tx 1: coordination.phase = Gathering -> Processing
      coordination.pendingCalls = <<ConsumeCall(1, ...)>>
```

### Step 4: ProcessTxCall(1, "Complete")

```
Action: Execute the consume call
Tx 1: coordination.callIndex = 0 -> 1
      coordination.pendingCalls[1].executed = TRUE
```

### Step 5: FinalizeTx(1, <<[datum |-> "Empty", tokens |-> AdaBag(2), contract |-> "Token", owner |-> "Alice"]>>)

```
Action: Create output specification
Tx 1: outputs = {
          SuspendedUTXO(3, "Token", "Alice", "Empty", AdaBag(2),
              FrameAtYield(1, [v \in VarNames |-> NULL], 0))
      }
      coordination.outputSpecs = <<[datum |-> "Empty", tokens |-> AdaBag(2), contract |-> "Token", owner |-> "Alice"]>>
      coordination.phase = Processing -> Complete
nextUtxoId: 4
```

### Step 6: BeginCommit(1)

```
Action: Enter Committing phase
Preconditions checked:
  - BalancePreserved: inputs(2 ADA) = outputs(2 ADA) ✓
  - ValidSignature: sig matches contents ✓
  - InputsOwnedBySigner: UTXO 1 owned by Alice ✓
```

### Step 7: CommitTx(1)

```
Action: Commit the transaction

Result:
  utxoSet: {UTXO(2, Bob, 2 ADA), UTXO(3, Alice, 2 ADA)}
  consumedSet: {1}
  pendingTxs: {}
  txHistory: <<Tx(1, Committed)>>
```

### Final state

```
ledger:
  utxoSet: {UTXO(2, Bob, 2 ADA), UTXO(3, Alice, 2 ADA)}
  consumedSet: {1}
  pendingTxs: {}
  txHistory: <<Tx(1, phase=Committed)>>
  nextUtxoId: 4
  nextTxId: 2
```

### Invariants verified

At each step, all invariants hold:
- `INV_LINEAR_NoDoubleSpend`: {2,3} ∩ {1} = {} ✓
- `INV_BALANCE_TxPreserved`: 2 ADA in = 2 ADA out ✓
- `INV_LINEAR_ConsumedTracked`: UTXO 1 in consumedSet ✓
- `INV_AUTH_OwnerOnly`: Alice owns UTXO 1 ✓

