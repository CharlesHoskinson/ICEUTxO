# Documentation Plan for Starstream TLA+ Specification

## Objective

Create comprehensive end-to-end documentation for the TLA+ formal specification of Starstream's UTXO/Transaction protocol, covering strategy, what is proved, and how to use it.

---

## Documentation Structure

```
tla/docs/
├── README.md                    # Overview and quick start
├── STRATEGY.md                  # Why TLA+, verification strategy
├── MODULES.md                   # Module reference guide
├── INVARIANTS.md                # Complete invariants catalog
├── STATE_MACHINES.md            # UTXO and Transaction lifecycles
├── USAGE.md                     # Running TLC, interpreting results
└── EXTENDING.md                 # Adding new properties/behaviors
```

---

## File 1: README.md (~150 lines)

### Purpose
Entry point for developers; answers "what is this and how do I get started?"

### Contents
1. **What This Is** - TLA+ formal spec for Starstream UTXO protocol
2. **What It Proves** - Quick summary of key guarantees:
   - No double-spend
   - Token balance preservation
   - Linear UTXO consumption
   - Effect handling completeness at coordination completion
   - Authorization correctness
3. **Module Overview** - Dependency diagram (ASCII)
4. **Quick Start** - 5-step guide to run verification
5. **Prerequisites** - TLA+ Toolbox or CLI installation
6. **Links** - Pointers to other docs

---

## File 2: STRATEGY.md (~200 lines)

### Purpose
Explain the "why" and verification approach for stakeholders and auditors.

### Contents
1. **Why Formal Verification?**
   - Blockchain protocol correctness is critical
   - Testing can miss edge cases; model checking exhaustively explores state space
   - TLA+ is battle-tested (AWS, Azure, etc.)

2. **What We Model**
   - UTXO lifecycle (Created → Suspended_at_Yield/Suspended_at_Effect/Reserved/Executing → Consumed)
   - Transaction phases (Idle → Reserve → Executing → Committing/Rollback → Committed/Failed)
   - Algebraic effect system
   - Multi-transaction concurrency
   - Token conservation

3. **What We Don't Model**
   - Cryptographic primitives (signatures modeled as content-bound records, no crypto)
   - Network/consensus layer
   - Smart contract bytecode execution
   - Gas/fees
   - Adversarial ordering beyond the modeled interleavings

4. **Verification Strategy**
   - Phase 1: Type invariants (structural correctness)
   - Phase 2: Safety invariants (no bad states)
   - Phase 3: Liveness properties (progress guaranteed)
   - Incremental approach: add invariants one at a time

5. **Threat Model**
   - Table mapping attacks to preventing invariants
   - Double-spend, replay, unauthorized spend, inflation, etc.

6. **Confidence Level**
   - Bounded model checking (not infinite state)
   - Constants chosen to represent realistic scenarios
   - Symmetry reduction for efficiency

---

## File 3: MODULES.md (~250 lines)

### Purpose
Reference guide for each TLA+ module's responsibility and key operators.

### Contents
For each module (StarstreamTypes through MC_Starstream):

1. **Module Name**
2. **Layer** (Foundation/Core/Orchestration/Composition/Verification)
3. **Extends** (dependencies)
4. **Purpose** (1-2 sentences)
5. **Key Types Defined**
6. **Key Operators** (table with name, signature, purpose)
7. **Invariants Contributed** (if any)

### Module Order
1. StarstreamTypes - Constants, enums, token bag operations
2. StarstreamFrame - Coroutine frame with PC, locals, hash
3. StarstreamAuth - Content-bound signatures and digest structure (ordered commitments)
4. StarstreamEffects - Effect records and stack operations
5. StarstreamUTXO - UTXO record and state transitions
6. StarstreamCoordination - Method calls and coordination state
7. StarstreamTransaction - Transaction record and balance logic
8. StarstreamLedger - Global state and ledger operations
9. StarstreamSpec - Init, Next, Spec definitions
10. StarstreamInvariants - All safety/liveness properties
11. MC_Starstream - Model checking configuration
12. Starstream.cfg - TLC constants and settings

---

## File 4: INVARIANTS.md (~300 lines)

### Purpose
Complete catalog of all invariants with explanations of what each proves.

### Contents
Organized by category:

1. **TYPE Invariants** (data structure well-formedness)
   - INV_TYPE_LedgerWellTyped
   - INV_TYPE_FramesWellTyped
   - INV_TYPE_TokenBagsWellTyped
   - INV_TYPE_PendingTxWellTyped

2. **AUTH Invariants** (authorization)
   - INV_AUTH_ValidSpend
   - INV_AUTH_OwnerOnly

3. **BALANCE Invariants** (token conservation)
   - INV_BALANCE_TxPreserved
   - INV_BALANCE_PendingTxValid
   - INV_BALANCE_NFTUnique

4. **LINEAR Invariants** (no double-spend)
   - INV_LINEAR_NoDoubleSpend
   - INV_LINEAR_ConsumedTracked
   - INV_LINEAR_UniqueActiveIds
   - INV_LINEAR_NoDoubleConsume
   - INV_LINEAR_NoDuplication

5. **LOCK Invariants** (reservation correctness)
   - INV_LOCK_Exclusive
   - INV_LOCK_ValidReservation
   - INV_LOCK_ConsistentSet

6. **LIFECYCLE Invariants** (state machine correctness)
   - INV_LIFECYCLE_ConsumedIsFinal
   - INV_LIFECYCLE_ActiveAreLive
   - INV_LIFECYCLE_FrameConsistent

7. **EFFECT Invariants** (effect handling)
   - INV_EFFECT_MustBeHandled
   - INV_EFFECT_NoOrphans

8. **FRAME Invariants** (integrity)
   - INV_FRAME_Integrity

9. **ATK Invariants** (attack prevention)
   - INV_ATK_NoReplay
   - INV_ATK_IdMonotonic
   - INV_ATK_NoNegativeTokens

10. **ROLLBACK Invariants** (failure cleanup)
    - INV_ROLLBACK_NoLeak

11. **LIVENESS Properties** (progress)
    - LIVE_TxEventuallyCommits
    - LIVE_TxEventuallyTerminates
    - LIVE_EffectsEventuallyHandled
    - LIVE_CanReturnToIdle

For each invariant:
- **Name**
- **Category**
- **TLA+ Definition** (code block)
- **What It Prevents** (attack/bug scenario)
- **Dependencies** (other invariants it relies on)

---

## File 5: STATE_MACHINES.md (~200 lines)

### Purpose
Visual and textual description of all state machines in the specification.

### Contents

1. **UTXO Lifecycle** (6 states)
   - State diagram (ASCII art)
   - Transition table (from, action, to, preconditions)
   - State descriptions
   - Include `Reserved` and `Executing` as explicit states
   - Include `Suspended_at_Effect` and `lockedBy` semantics

2. **Transaction Phases** (7 phases)
   - State diagram
   - Transition table
   - Phase descriptions
   - Call out phases currently unused in Spec (if any)

3. **Coordination Phases** (5 phases)
   - State diagram
   - Transition table
   - Phase descriptions

4. **Effect Stack**
   - Push/pop operations
   - Handled vs pending states

5. **Frame Lifecycle**
   - PC values and their meanings
   - Termination semantics

6. **Sample Execution Trace**
   - Step-by-step walkthrough of a transaction
   - Shows state changes at each action

---

## File 6: USAGE.md (~250 lines)

### Purpose
Practical guide for running TLC and interpreting results.

### Contents

1. **Prerequisites**
   - Install TLA+ Toolbox (GUI) or tla2tools.jar (CLI)
   - Java 11+ required
   - Recommended: 8GB+ RAM for larger state spaces

2. **Running with TLA+ Toolbox**
   - Create new spec, add modules
   - Configure model (constants, invariants)
   - Run model checker
   - Screenshots/descriptions

3. **Running with CLI**
   ```bash
   java -cp tla2tools.jar tlc2.TLC -config Starstream.cfg MC_Starstream.tla
   ```
   - Common flags: -workers, -depth, -checkpoint
   - Example commands

4. **Interpreting Results**
   - "No errors found" - all invariants hold
   - Counterexample traces - how to read them
   - State count and coverage metrics

5. **Common Issues**
   - Out of memory: reduce MAX_UTXOS/UTXO_ID_BOUND
   - State explosion: enable symmetry, tighten constraints
   - Infinite behavior: check liveness with FairSpec

6. **Checking Specific Properties**
   - Safety only (default)
   - Liveness (uncomment PROPERTIES)
   - Finding specific bugs (MC_FindDoubleSpend, etc.)

7. **Performance Tuning**
   - Symmetry sets (only if configured in Starstream.cfg)
   - State constraints
   - Worker threads

---

## File 7: EXTENDING.md (~200 lines)

### Purpose
Guide for adding new invariants, actions, or behaviors.

### Contents

1. **Adding a New Invariant**
   - Define in StarstreamInvariants.tla
   - Add to INV_Safety if it's a safety property
   - Add to Starstream.cfg INVARIANTS section
   - Test incrementally

2. **Adding a New Action**
   - Define preconditions and state update in StarstreamSpec.tla
   - Add to Next disjunction
   - Ensure existing invariants still hold

3. **Adding a New UTXO State**
   - Add to UTXOStates in StarstreamTypes.tla
   - Update predicates (IsLive, CanQuery, etc.)
   - Add transitions in StarstreamUTXO.tla
   - Update INV_LIFECYCLE_FrameConsistent

4. **Adding a New Token Type**
   - Add to TOKEN_TYPES constant
   - Ensure AddTokenBags handles it
   - Update sample bags in StarstreamSpec.tla

5. **Adding a New Effect Kind**
   - Add to EffectKinds in StarstreamTypes.tla
   - Update constructors in StarstreamEffects.tla

6. **Changing Model Bounds**
   - Edit Starstream.cfg
   - Impact on state space size
   - Recommended limits for fast iteration

7. **Testing Changes**
   - Syntax check: `-parse` flag
   - Type check: run with just INV_TYPE_All
   - Full check: all invariants
   - Regression: verify existing properties still hold

---

## Implementation Order

| Priority | File | Est. Lines | Notes |
|----------|------|------------|-------|
| P1 | README.md | 150 | Entry point, write first |
| P1 | USAGE.md | 250 | Practical, high value |
| P2 | STRATEGY.md | 200 | For stakeholders/auditors |
| P2 | INVARIANTS.md | 300 | Core reference |
| P2 | STATE_MACHINES.md | 200 | Visual aids |
| P3 | MODULES.md | 250 | Detailed reference |
| P3 | EXTENDING.md | 200 | For contributors |

**Total: ~1,550 lines across 7 files**

---

## Verification

After writing each document:
1. Ensure code examples are syntactically correct TLA+
2. Verify file paths and module names match actual files
3. Test any CLI commands provided
4. Cross-reference invariant names against StarstreamInvariants.tla
5. Review state machine diagrams against actual transitions

---

## Key Files to Reference

| File | Purpose |
|------|---------|
| `tla/StarstreamTypes.tla` | Constants, enums |
| `tla/StarstreamAuth.tla` | Content-bound signatures and digests |
| `tla/StarstreamTransaction.tla` | Transaction record + signing |
| `tla/StarstreamSpec.tla` | Init, Next, actions |
| `tla/StarstreamInvariants.tla` | All invariants |
| `tla/MC_Starstream.tla` | Model checking setup |
| `tla/Starstream.cfg` | TLC configuration |
