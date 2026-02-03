# Usage guide

This guide shows how to run the TLC model checker and read the results.

## Prerequisites

### Java runtime

TLC requires Java 11 or later.

```bash
# Check Java version
java -version

# Expected output (version should be 11+):
# openjdk version "17.0.1" 2021-10-19
```

### TLA+ tools

**Option 1: TLA+ Toolbox (GUI)**

Download from: https://github.com/tlaplus/tlaplus/releases

- Windows: `TLAToolbox-X.X.X-win32.win32.x86_64.zip`
- macOS: `TLAToolbox-X.X.X-macosx.cocoa.x86_64.zip`
- Linux: `TLAToolbox-X.X.X-linux.gtk.x86_64.zip`

**Option 2: Command-line tools**

Download `tla2tools.jar` from the same releases page.

**Platform note:** Paths in this doc use Windows format (`C:\...`). On macOS/Linux, use Unix-style paths.

### Suggested system sizes

| State Space | RAM | Workers |
|-------------|-----|---------|
| < 10^6 states | 4 GB | 2-4 |
| 10^6 - 10^8 states | 8 GB | 4-8 |
| > 10^8 states | 16+ GB | 8+ |

---

## Getting started (CLI walkthrough)

This is a minimal end-to-end run that should succeed on a typical laptop.

1. **Install Java 11+** and remember where `java` lives.
2. **Download `tla2tools.jar`** from the TLA+ releases page.
3. **Open a terminal** and go to the spec folder:
   ```bash
   cd tla/
   ```
4. **Run TLC**:
   ```bash
   java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg
   ```

**Expected output (success):**
```
Parsing file MC_Starstream.tla
...
Model checking completed. No error has been found.
```

If you see the "No error has been found" line, the model checked **within the configured bounds**.

---

## Running with TLA+ Toolbox

### 1. Create new specification

1. File > Open Spec > Add New Spec
2. Browse to `tla/MC_Starstream.tla`
3. Click "Finish"

### 2. Create model

1. Right-click on spec > New Model > Name it "default"
2. In Model Overview:
   - **What is the behavior spec?**: Select `MC_Spec`
   - **What to check?**: Add invariants (see below)

### 3. Configure constants

In "What is the model?" section:

| Constant | Value |
|----------|-------|
| `MAX_UTXOS` | 3 |
| `MAX_TX_INPUTS` | 2 |
| `MAX_TX_OUTPUTS` | 2 |
| `MAX_FRAME_VARS` | 4 |
| `MAX_PENDING_TXS` | 2 |
| `MAX_TOKEN_TOTAL` | 4 |
| `UTXO_ID_BOUND` | 8 |
| `CHAIN_ID` | 1 |
| `BLOCK_HEIGHT` | 0 |
| `MAX_COORDINATORS` | 2 |
| `MAX_INTERFACES` | 3 |
| `MAX_HANDLER_DEPTH` | 2 |
| `TOKEN_TYPES` | `{"ADA", "NFT"}` |
| `TOKEN_IDS` | `{1, 2, 3}` |

### 4. Add invariants

In "What to check?" > "Invariants":

```
MC_TypeOK
MC_NoDoubleSpend
MC_BalancePreserved
MC_ConsumedTracked
MC_ConsumedIsFinal
MC_EffectsMustBeHandled
MC_NoReplay
MC_PendingInputsNotConsumed
MC_EffectSourceSuspended
MC_EffectContinuationMatch
MC_EffectStackDepthBounded
MC_PendingOutputsNoNFTDuplication
MC_LockAtomicRelease
MC_Safety
```

**Note:** The default config includes additional IEUTxO, proof, and handler-stack invariants. For a full sweep, just include `MC_Safety` or mirror the `INVARIANTS` list in `Starstream.cfg`.

### 5. Set state constraint

In "What to check?" > "State Constraint":

```
MC_StateConstraint
```

### 6. Run model checker

- Press F11 or TLC Model Checker > Run Model
- Watch progress in Model Checking Results panel

---

## Running with command line

### Basic command

```bash
cd tla/
java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg
```

### Optimistic variant

```bash
cd tla/
java -cp tla2tools.jar tlc2.TLC MC_StarstreamOptimistic.tla -config StarstreamOptimistic.cfg
```

**Bound note:** Proof generation enumerates `SampleFrameHashes` instead of the full `FrameHashRange` to keep TLC tractable.

### Common flags

| Flag | Purpose | Example |
|------|---------|---------|
| `-workers N` | Number of worker threads | `-workers 4` |
| `-depth N` | Maximum state depth | `-depth 100` |
| `-checkpoint M` | Checkpoint every M minutes | `-checkpoint 5` |
| `-dump file` | Dump states to file | `-dump states.dump` |
| `-coverage M` | Print coverage every M minutes | `-coverage 1` |
| `-deadlock` | Check for deadlocks | `-deadlock` |
| `-terse` | Less verbose output | `-terse` |
| `-continue` | Continue after error | `-continue` |

### Suggested command

```bash
java -Xmx8g -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg -workers 4 -checkpoint 5
```

### Running specific invariants

Edit `Starstream.cfg` or create a custom config:

```
\* Custom config for just type checking
SPECIFICATION MC_Spec
CONSTANTS
    MAX_UTXOS = 3
    ...
CONSTRAINT MC_StateConstraint
INVARIANTS
    MC_TypeOK
```

Then:

```bash
java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config custom.cfg
```

---

## Interpreting results

### Successful run

```
TLC2 Version 2.18 of Day Month 20XX (rev: abc123)
Running breadth-first search Model-Checking with fp 93 and target seed -12345...
Parsing file MC_Starstream.tla
...
Finished computing initial states: 1 distinct state generated at 2023-01-15 10:30:15.
Progress(10) at 2023-01-15 10:30:25: 15,432 states generated, 4,521 distinct states found...
...
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  ...
8432521 states generated, 2156432 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 47.
```

**Key indicators:**
- "No error has been found" - All invariants held **within the configured bounds** (`Starstream.cfg`)
- "distinct states found" - Actual state space explored
- "depth of the complete state graph" - Longest path explored

### Invariant violation

```
Error: Invariant MC_NoDoubleSpend is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ ledger = [utxoSet |-> {[id |-> 1, state |-> "Suspended_at_Yield", ...]},
             consumedSet |-> {},
             ...]
State 2: <ReserveTx line 86, col 5 to line 91, col 55 of module StarstreamSpec>
/\ ledger = ...
...
State 7: <CommitTx line 148, col 5 to line 156, col 57 of module StarstreamSpec>
/\ ledger = [utxoSet |-> {[id |-> 1, ...]},
             consumedSet |-> {1},
             ...]
```

**How to read counterexamples:**
1. Each "State N" shows the ledger after an action
2. The action name and line numbers are shown
3. Follow the trace to see how the violation occurred
4. The final state shows the invariant-violating condition

### State count metrics

| Metric | Meaning |
|--------|---------|
| States generated | Total state evaluations |
| Distinct states | Unique states (after duplicate elimination) |
| States on queue | Unexplored states remaining |
| Search depth | Longest path from initial state |

### Coverage report

```
Progress(15) at 2023-01-15 10:31:00: 125,432 states generated...
The coverage stats:
  <CreateUTXO line 70> Cardinality(ledger.utxoSet) < MAX_UTXOS: 45,234
  <ReserveTx line 79> inputIds # {}: 32,156
  ...
```

Coverage shows how many times each action's guard evaluated to TRUE.

---

## Debugging workflow (decision tree)

```
Start
  |
  v
Did TLC exit with an error before exploring states?
  |-- Yes --> Parse/type error → check module names, EXTENDS, typos
  |
  v
Did TLC report "Invariant ... is violated"?
  |-- Yes --> Run only that invariant → inspect last state → identify action
  |           → add Print() or tighten guards → re-run
  |
  v
Did TLC report "OutOfMemoryError" or stall?
  |-- Yes --> Reduce bounds or add constraints → increase -Xmx → retry
  |
  v
No errors, but unsure why?
  |-- Use coverage output → confirm actions are exercised
  |-- Increase bounds gradually → re-run
```

**Minimal debug loop:**
1. Re-run with just the failing invariant in `Starstream.cfg`
2. Read the final state, then walk backward to the first suspicious action
3. Add `Print` statements or temporary invariants to narrow the cause

---

## Common issues

### Out of memory

**Symptom:**
```
java.lang.OutOfMemoryError: Java heap space
```

**Solutions:**

1. Increase heap size:
   ```bash
   java -Xmx16g -cp tla2tools.jar tlc2.TLC ...
   ```

2. Reduce model bounds:
   ```
   MAX_UTXOS = 2        \* Was 3
   UTXO_ID_BOUND = 6    \* Was 8
   ```

3. Enable state compression (slower but uses less memory):
   ```bash
   java -cp tla2tools.jar tlc2.TLC ... -gzip
   ```

### State explosion

**Symptom:** Progress very slow, billions of states

**Solutions:**

1. Add state constraint (already in config):
   ```tla
   CONSTRAINT MC_StateConstraint
   ```

2. Reduce bounds for initial testing:
   ```
   MAX_UTXOS = 2
   MAX_PENDING_TXS = 1
   UTXO_ID_BOUND = 4
   ```

3. Enable symmetry reduction (edit config):
   ```
   SYMMETRY TokenTypeSymmetry
   ```

### Deadlock detection

**Symptom:**
```
Error: Deadlock reached.
```

By default, deadlock checking is disabled (`CHECK_DEADLOCK FALSE`). If you enable it and get deadlock errors, this means no action is enabled - which may be expected in a stuttering specification.

### Type errors

**Symptom:**
```
Error: In evaluation, the identifier 'foo' is either undefined or not an operator.
```

**Solution:** Usually a typo or missing EXTENDS. Check module imports.

---

## Checking specific properties

### Safety only (default)

The default configuration checks safety invariants:

```
SPECIFICATION MC_Spec
INVARIANTS MC_TypeOK MC_NoDoubleSpend ...
```

### Liveness properties

To check liveness, edit `Starstream.cfg`:

```
\* Change specification to use fairness
SPECIFICATION MC_FairSpec

\* Uncomment liveness properties
PROPERTIES
    MC_TxCommits
    MC_TxTerminates
    MC_IdleReachable
```

To check effect-handling liveness, use strong fairness:

```
SPECIFICATION MC_StrongFairSpec
PROPERTIES
    MC_EffectsHandled
```

`MC_StrongFairSpec` applies strong fairness to `HandleTxEffect` (and
`OptHandleTxEffect` in the optimistic variant).

**Note:** Liveness checking needs more resources and explores infinite behaviors.

### Finding specific bugs

Use trace exploration helpers in `MC_Starstream.tla`:

```bash
# Find a double-spend (should fail if invariant holds)
java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg \
    -invariant MC_FindDoubleSpend
```

These helpers negate invariants to find traces that reach specific states.

---

## Performance tuning

### Worker threads

Use number of CPU cores:

```bash
java -cp tla2tools.jar tlc2.TLC ... -workers 8
```

More workers can speed up exploration (diminishing returns around 8-16).

### Symmetry reduction

When constants have interchangeable values, symmetry reduction can cut state space.

Enable in config:

```
SYMMETRY TokenTypeSymmetry
```

**Caution:** Symmetry must be applied correctly or it can mask bugs.

### State constraints

The constraint limits explored states:

```tla
MC_StateConstraint ==
    /\ Cardinality(ledger.utxoSet) <= MC_MAX_UTXOS
    /\ Cardinality(ledger.consumedSet) <= MC_UTXO_ID_BOUND
    /\ Cardinality(ledger.pendingTxs) <= MC_MAX_PENDING_TXS
    /\ ledger.nextUtxoId <= MC_UTXO_ID_BOUND + 1
    /\ Len(ledger.txHistory) <= 3
```

Tightening these reduces state space but may miss bugs in larger scenarios.

### Checkpointing

For long runs, enable checkpointing:

```bash
java -cp tla2tools.jar tlc2.TLC ... -checkpoint 10
```

This saves progress every 10 minutes. Resume with `-recover`.

---

## Quick reference

### Minimal test (fast)

```bash
# Type check only
java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg \
    -workers 2 -depth 20
```

### Full safety check

```bash
# All safety invariants
java -Xmx8g -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg \
    -workers 4 -checkpoint 5
```

### Liveness check

Edit config to use `MC_FairSpec` and uncomment `PROPERTIES`, then:

```bash
java -Xmx16g -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg \
    -workers 4
```

### Debugging invariant violation

1. Run with just the failing invariant
2. Add `-continue` to find multiple violations
3. Examine counterexample trace
4. Add print statements using TLC's `Print` operator

