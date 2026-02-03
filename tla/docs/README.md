# Starstream TLA+ formal specification

This repository contains a TLA+ specification for Starstream's UTXO/Transaction protocol. TLA+ is **not** production code; it’s a mathematical description of how the system should behave. TLC is the model checker that explores all reachable states (within bounds) to find violations, similar to exhaustive testing but over the entire state space.

## What this is

A formal model of the Starstream protocol covering:

- **UTXO lifecycle** - Creation, suspension, reservation, execution, and consumption (with `pc` = program counter)
- **Transaction processing** - Multi-phase commit with coordination scripts
- **Algebraic effect system** - Effect raising and handling within transactions
- **Token conservation** - Balance preservation across all operations
- **Authorization** - Content-bound signature verification and ownership enforcement

## What it proves

The specification checks these safety properties within the configured bounds:

| Property | Invariant | Description |
|----------|-----------|-------------|
| No double-spend | `INV_LINEAR_NoDoubleSpend` | A UTXO cannot be spent twice |
| Token conservation | `INV_BALANCE_TxPreserved` | Total tokens preserved in every committed transaction |
| Checked arithmetic | `INV_BALANCE_NoOverflow` | Per-asset totals stay within arithmetic bounds |
| Linear consumption | `INV_LINEAR_ConsumedTracked` | All consumed UTXOs are tracked |
| NFT uniqueness | `INV_BALANCE_NFTUnique` | Each NFT exists in at most one UTXO |
| Effect completeness | `INV_EFFECT_MustBeHandled` | All effects must be handled before coordination completion |
| Effect source suspended | `INV_EFFECT_SourceSuspended` | Pending effects come from suspended inputs |
| Continuation match | `INV_EFFECT_ContinuationMatch` | Effect continuations match suspended frame PC |
| Authorization | `INV_AUTH_ValidSpend` | Committed spends are authorized (signature + owner) |
| No replay attacks | `INV_ATK_NoReplay` | Consumed IDs cannot reappear |
| Rollback safety | `INV_ROLLBACK_NoLeak` | Failed transactions don't leak outputs |

## Module architecture

```
                    +------------------+
                    | MC_Starstream    |  Model Checking
                    +--------+---------+
                             |
                    +--------v---------+
                    | StarstreamSpec   |  Init, Next, Spec
                    +--------+---------+
                             |
              +--------------+---------------+
              |                              |
   +----------v----------+        +----------v----------+
   | StarstreamInvariants|        | StarstreamLedger    |
   +---------------------+        +----------+----------+
                                             |
         +---------------+-------------------+-------------------+
         |               |                   |                   |
+--------v------+ +------v-------+ +--------v--------+ +--------v------+
| Starstream    | | Starstream   | | Starstream      | | Starstream   |
| Transaction   | | Coordination | | Effects         | | Auth         |
+-------+-------+ +------+-------+ +--------+--------+ +-------+------+
        |                |                  |                  |
        +-------+--------+---------+--------+------------------+
                |                  |
        +-------v-------+  +------v-------+
        | StarstreamUTXO|  |StarstreamFrame|
        +-------+-------+  +------+-------+
                |                 |
                +--------+--------+
                         |
                +--------v--------+
                | StarstreamTypes |  Foundation
                +-----------------+
```

## Quick start

### 1. Prerequisites

- Java 11 or later
- TLA+ Toolbox (GUI) or `tla2tools.jar` (CLI)

Download: https://github.com/tlaplus/tlaplus/releases

### 2. Clone and navigate

```bash
cd tla/
```

### 3. Run model checker (CLI)

```bash
java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg
```

### 4. Run model checker (Toolbox)

1. Open TLA+ Toolbox
2. File > Open Spec > Add New Spec
3. Select `MC_Starstream.tla`
4. Create new model, import `Starstream.cfg` settings
5. Run Model Checker (F11)

### 5. Interpret results

- **"No errors found"** - All invariants hold for the explored state space
- **Counterexample shown** - An invariant was violated; trace shows how

## File structure

| File | Purpose |
|------|---------|
| `StarstreamTypes.tla` | Constants, enums, token bag operations |
| `StarstreamFrame.tla` | Coroutine frame with PC, locals, hash |
| `StarstreamAuth.tla` | Content-bound signatures and ownership verification |
| `StarstreamEffects.tla` | Effect records and stack operations |
| `StarstreamUTXO.tla` | UTXO record and state transitions |
| `StarstreamCoordination.tla` | Method calls and coordination state |
| `StarstreamTransaction.tla` | Transaction record and balance logic |
| `StarstreamLedger.tla` | Global state and ledger operations |
| `StarstreamSpec.tla` | Init, Next, Spec definitions |
| `StarstreamInvariants.tla` | All safety and liveness properties |
| `MC_Starstream.tla` | Model checking configuration |
| `Starstream.cfg` | TLC constants and settings |

## Documentation

| Document | Description |
|----------|-------------|
| [QUICK_REFERENCE.md](QUICK_REFERENCE.md) | Quick commands, invariants, and module map |
| [STRATEGY.md](STRATEGY.md) | Verification strategy and threat model |
| [MODULES.md](MODULES.md) | Detailed module reference |
| [INVARIANTS.md](INVARIANTS.md) | Complete invariants catalog |
| [STATE_MACHINES.md](STATE_MACHINES.md) | UTXO and transaction lifecycles |
| [USAGE.md](USAGE.md) | Running TLC and interpreting results |
| [EXTENDING.md](EXTENDING.md) | Adding new properties and behaviors |

## Reading paths

- **New to TLA+**: [STRATEGY.md](STRATEGY.md) → [USAGE.md](USAGE.md) → [STATE_MACHINES.md](STATE_MACHINES.md) → [SPECIFICATION_DEEP_DIVE.md](SPECIFICATION_DEEP_DIVE.md)
- **Need invariants**: [INVARIANTS.md](INVARIANTS.md) → [QUICK_REFERENCE.md](QUICK_REFERENCE.md) → [SPECIFICATION_DEEP_DIVE.md](SPECIFICATION_DEEP_DIVE.md) Part IV
- **Extending the spec**: [EXTENDING.md](EXTENDING.md) → [MODULES.md](MODULES.md) → [SPECIFICATION_DEEP_DIVE.md](SPECIFICATION_DEEP_DIVE.md) Part VI

## Model bounds

Default configuration (`Starstream.cfg`):

| Constant | Value | Purpose |
|----------|-------|---------|
| `MAX_UTXOS` | 3 | Maximum UTXOs in ledger |
| `MAX_TX_INPUTS` | 2 | Maximum inputs per transaction |
| `MAX_TX_OUTPUTS` | 2 | Maximum outputs per transaction |
| `MAX_FRAME_VARS` | 4 | Maximum locals per coroutine frame |
| `MAX_PENDING_TXS` | 2 | Maximum concurrent transactions |
| `MAX_TOKEN_TOTAL` | 4 | Maximum per-asset total for overflow checks |
| `UTXO_ID_BOUND` | 8 | Maximum UTXO identifier value |
| `CHAIN_ID` | 1 | Chain context for replay protection |
| `BLOCK_HEIGHT` | 0 | Block height for replay protection |
| `TOKEN_TYPES` | `{"ADA", "NFT"}` | Token type domain |
| `TOKEN_IDS` | `{1, 2, 3}` | Token ID domain |

These bounds keep the state space manageable while still exercising common scenarios.

## License

See repository root for license information.

