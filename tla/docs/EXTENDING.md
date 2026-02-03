# Extending the specification

This guide shows how to add invariants, actions, states, and behaviors to the Starstream TLA+ specification.

## Adding a new invariant

### Step 1: Define in StarstreamInvariants.tla

Add your invariant definition:

```tla
(***************************************************************************
 * MY NEW INVARIANTS
 ***************************************************************************)

INV_NEW_MyProperty ==
    \* Your invariant expression
    \A tx \in ledger.pendingTxs :
        SomeCondition(tx)
```

### Step 2: Add to combined safety (if applicable)

If it's a safety property that should always be checked:

```tla
INV_Safety ==
    /\ INV_TYPE_All
    /\ INV_AUTH_ValidSpend
    ...
    /\ INV_NEW_MyProperty   \* Add here
```

### Step 3: Add to MC_Starstream.tla

Create a model-checking wrapper:

```tla
MC_MyProperty == INV_NEW_MyProperty
```

### Step 4: Add to Starstream.cfg

```
INVARIANTS
    MC_TypeOK
    ...
    MC_MyProperty
```

### Step 5: Test incrementally

1. First, check only type invariants pass
2. Then add your new invariant
3. If it fails, examine the counterexample

---

## Tutorial: Your First Invariant (baby steps)

This walkthrough adds a tiny invariant that checks all UTXO IDs are positive.

### 1) Add the invariant

In `StarstreamInvariants.tla`:

```tla
INV_TUTORIAL_PositiveIds ==
    \A u \in ledger.utxoSet : u.id > 0
```

### 2) Add a model-check wrapper

In `MC_Starstream.tla`:

```tla
MC_Tutorial_PositiveIds == INV_TUTORIAL_PositiveIds
```

### 3) Enable it in the config

In `Starstream.cfg`:

```
INVARIANTS
    MC_TypeOK
    MC_Tutorial_PositiveIds
```

### 4) Run TLC

```bash
java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg
```

**Expected output:**
```
Model checking completed. No error has been found.
```

If you want to see a failure, temporarily change the invariant to `u.id >= 0` and set `UTXO_ID_BOUND = 0` in the config.

### Invariant categories

Follow naming conventions:

| Prefix | Category | Example |
|--------|----------|---------|
| `INV_TYPE_` | Data structure well-formedness | `INV_TYPE_FramesWellTyped` |
| `INV_AUTH_` | Authorization/ownership | `INV_AUTH_ValidSpend` |
| `INV_BALANCE_` | Token conservation | `INV_BALANCE_TxPreserved` |
| `INV_LINEAR_` | Linear type properties | `INV_LINEAR_NoDoubleSpend` |
| `INV_LOCK_` | Reservation/locking | `INV_LOCK_Exclusive` |
| `INV_LIFECYCLE_` | State machine correctness | `INV_LIFECYCLE_ConsumedIsFinal` |
| `INV_EFFECT_` | Effect handling | `INV_EFFECT_MustBeHandled` |
| `INV_ATK_` | Attack prevention | `INV_ATK_NoReplay` |
| `LIVE_` | Liveness property | `LIVE_TxEventuallyCommits` |

---

## Adding a new action

### Step 1: Define preconditions and update

Add to `StarstreamSpec.tla`:

```tla
(***************************************************************************
 * NEW ACTION: Description
 ***************************************************************************)

MyNewAction(param1, param2) ==
    \* Preconditions
    /\ SomePrecondition(param1)
    /\ AnotherPrecondition(param2)
    \* State update
    /\ ledger' = SomeUpdate(ledger, param1, param2)
```

### Step 2: Add to Next

Include in the `Next` disjunction:

```tla
Next ==
    \/ \E c \in SampleContracts, ... : CreateUTXO(c, ...)
    \/ \E ids \in SUBSET ..., ... : ReserveTx(ids, ...)
    ...
    \* Add your action
    \/ \E p1 \in SomeSet, p2 \in AnotherSet : MyNewAction(p1, p2)
```

### Step 3: Verify invariants

Run model checker to ensure existing invariants still hold.

### Action guidelines

1. **Preconditions first**: All guards before state update
2. **Atomic update**: Single `ledger'` assignment
3. **Use helpers**: Define complex updates in appropriate module
4. **Bound parameters**: Use finite sets for TLC enumeration

Example with helper:

```tla
\* In StarstreamLedger.tla
MyUpdateInLedger(ledger, param) ==
    [ledger EXCEPT !.someField = NewValue(param)]

\* In StarstreamSpec.tla
MyNewAction(param) ==
    /\ Precondition(param)
    /\ ledger' = MyUpdateInLedger(ledger, param)
```

---

## Adding a new UTXO state

### Step 1: Add to UTXOStates

In `StarstreamTypes.tla`:

```tla
UTXOStates == {
    "Created",
    "Suspended_at_Yield",
    "Suspended_at_Effect",
    "Reserved",
    "Executing",
    "Consumed",
    "MyNewState"           \* Add here
}
```

### Step 2: Update state predicates

In `StarstreamUTXO.tla`, update predicates:

```tla
IsLive(u) ==
    /\ IsUTXORecord(u)
    /\ u.state \notin {"Consumed"}   \* Adjust if MyNewState is final

CanQuery(u) ==
    /\ IsLive(u)
    /\ u.state \in {"Suspended_at_Yield", "Reserved", "Executing", "MyNewState"}

\* Add new predicate if needed
IsMyNewState(u) == /\ IsUTXORecord(u) /\ u.state = "MyNewState"
```

### Step 3: Add transition operators

```tla
\* Transition TO MyNewState
ToMyNewState(u, param) ==
    [u EXCEPT
        !.state = "MyNewState",
        !.someField = param]

\* Transition FROM MyNewState
FromMyNewState(u) ==
    [u EXCEPT
        !.state = "Suspended_at_Yield"]
```

### Step 4: Update lifecycle invariant

In `StarstreamInvariants.tla`:

```tla
INV_LIFECYCLE_FrameConsistent ==
    \A u \in ledger.utxoSet :
        /\ (u.state = "Created") => (u.frame.pc = 0)
        /\ (u.state = "Consumed") => (u.frame.pc = -1)
        /\ (u.state = "Suspended_at_Yield") => (u.frame.pc >= 0)
        /\ (u.state = "Suspended_at_Effect") => (u.frame.pc >= 0)
        /\ (u.state = "MyNewState") => (u.frame.pc >= 0)  \* Add constraint
```

### Step 5: Add actions using the state

```tla
EnterMyNewState(utxoId, param) ==
    /\ UTXOExistsInLedger(ledger, utxoId)
    /\ LET utxo == GetUTXO(ledger, utxoId)
       IN /\ utxo.state = "Suspended_at_Yield"  \* Precondition
          /\ ledger' = UpdateUTXOInLedger(ledger, ToMyNewState(utxo, param))
```

---

## Adding a new token type

### Step 1: Update TOKEN_TYPES constant

In `Starstream.cfg`:

```
TOKEN_TYPES = {"ADA", "NFT", "STABLE"}
```

### Step 2: Verify token bag operations

The `AddTokenBags` operator in `StarstreamTypes.tla` handles arbitrary token types:

```tla
AddTokenBags(bag1, bag2) ==
    [t \in TOKEN_TYPES |->
        [id \in TOKEN_IDS |-> bag1[t][id] + bag2[t][id]]]
```

No changes needed if using standard operations.

### Step 3: Update sample token bags (if needed)

In `StarstreamSpec.tla`:

```tla
StableBag(amount) ==
    [t \in TOKEN_TYPES |->
        [id \in TOKEN_IDS |->
            IF t = "STABLE" /\ id = AdaId THEN amount ELSE 0]]

SampleTokenBags == {EmptyTokenBag, AdaBag(2), StableBag(1)}
```

### Step 4: Consider type-specific invariants

```tla
INV_BALANCE_StableUnique ==
    \* Example: STABLE tokens have additional constraints
    \A id \in TOKEN_IDS :
        LET total == SumTokenBags(ledger.utxoSet)["STABLE"][id]
        IN total <= 100  \* Max supply
```

---

## Adding a new effect kind

### Step 1: Add to EffectKinds

In `StarstreamTypes.tla`:

```tla
EffectKinds == {
    "Pure",
    "Effectful",
    "Runtime",
    "Storage"     \* New kind
}
```

### Step 2: Add constructor

In `StarstreamEffects.tla`:

```tla
StorageEffect(utxoId, continuationId, tag, payload) ==
    NewEffect("Storage", utxoId, continuationId, tag, payload)
```

### Step 3: Update predicates (if needed)

```tla
IsStorageEffect(e) == /\ IsEffectRecord(e) /\ e.kind = "Storage"

\* If storage effects have special handling requirements
RequiresExternalHandler(e) == e.kind \in {"Runtime", "Storage"}
```

### Step 4: Update PTB resume handling

If the new effect kind requires different handling, update the `Resume` branch
inside `ProcessPTBEvent` (via the `PTBResume` helper):

```tla
PTBResume(txId, tx, coord, evt) ==
    /\ evt.kind = "Resume"
    /\ ...
    /\ IF IsStorageEffect(effect)
       THEN \* Special storage handling
            ...
       ELSE \* Normal handling
            ...
```

---

## Changing model bounds

### Impact analysis

| Constant | Increase Effect | State Space Impact |
|----------|-----------------|-------------------|
| `MAX_UTXOS` | More UTXOs in ledger | Exponential |
| `MAX_TX_INPUTS` | More inputs per tx | Polynomial |
| `MAX_PENDING_TXS` | More concurrent txs | Exponential |
| `UTXO_ID_BOUND` | More unique IDs | Linear |
| `TOKEN_IDS` | More token varieties | Polynomial |

### Suggested limits

| Scenario | MAX_UTXOS | MAX_PENDING_TXS | UTXO_ID_BOUND | Est. States |
|----------|-----------|-----------------|---------------|-------------|
| Quick test | 2 | 1 | 4 | ~10^5 |
| Normal | 3 | 2 | 8 | ~10^7 |
| Thorough | 4 | 2 | 10 | ~10^9 |
| Exhaustive | 5 | 3 | 12 | ~10^11+ |

### Editing bounds

In `Starstream.cfg`:

```
CONSTANTS
    MAX_UTXOS = 4           \* Increased
    MAX_TX_INPUTS = 2
    MAX_TX_OUTPUTS = 2
    MAX_FRAME_VARS = 4
    MAX_PENDING_TXS = 2
    UTXO_ID_BOUND = 10      \* Increased
    TOKEN_TYPES = {"ADA", "NFT"}
    TOKEN_IDS = {1, 2, 3}
```

Also update constraint if needed:

```tla
MC_StateConstraint ==
    /\ Cardinality(ledger.utxoSet) <= 4      \* Match MAX_UTXOS
    /\ Cardinality(ledger.consumedSet) <= 10  \* Match UTXO_ID_BOUND
    ...
```

---

## Testing changes

### 1. Syntax check

```bash
java -cp tla2tools.jar tla2sany.SANY StarstreamSpec.tla
```

### 2. Type check

Run with only type invariants:

```bash
# Create minimal config
echo "SPECIFICATION MC_Spec
CONSTANTS MAX_UTXOS = 2 ...
INVARIANTS MC_TypeOK" > type_check.cfg

java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config type_check.cfg -depth 10
```

### 3. Smoke test

Quick run with small bounds:

```bash
java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg \
    -workers 2 -depth 20
```

### 4. Full regression

Verify all existing invariants still hold:

```bash
java -Xmx8g -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg \
    -workers 4
```

### 5. Check new property

Add your new invariant and run:

```bash
java -Xmx8g -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config new_property.cfg \
    -workers 4 -continue
```

The `-continue` flag finds all violations, not just the first.

---

## Common patterns

### Conditional invariant

Invariant that only applies in certain states:

```tla
INV_COND_Example ==
    \A tx \in ledger.pendingTxs :
        IsExecutingTx(tx) =>  \* Only when executing
            SomeProperty(tx)
```

### Relational invariant

Property relating multiple entities:

```tla
INV_REL_Example ==
    \A tx \in ledger.pendingTxs :
        \A u \in tx.inputs :
            GetUTXO(ledger, u.id).lockedBy = tx.id
```

### Historical invariant

Property over transaction history:

```tla
INV_HIST_Example ==
    \A i \in 1..Len(ledger.txHistory) :
        LET tx == ledger.txHistory[i]
        IN IsCommittedTx(tx) => SomeProperty(tx)
```

### Liveness template

```tla
LIVE_MyProgress ==
    \A x \in SomeSet :
        \* "If x is in state A, it eventually reaches state B"
        [](InStateA(x) => <>(InStateB(x)))
```

---

## Checklist for changes

Before submitting changes:

- [ ] Syntax check passes (`tla2sany.SANY`)
- [ ] Type invariants pass
- [ ] All existing invariants pass
- [ ] New invariant/action has meaningful name
- [ ] Added to appropriate module
- [ ] Updated [MODULES.md](MODULES.md) if adding new operators
- [ ] Updated [INVARIANTS.md](INVARIANTS.md) if adding new invariant
- [ ] Updated [STATE_MACHINES.md](STATE_MACHINES.md) if changing state machine
- [ ] Tested with multiple bound configurations

