# Starstream TLA+ Quick Reference

## Commands

```bash
# Parse check
java -jar tla2tools.jar -parse StarstreamSpec.tla

# Model check (default config)
java -jar tla2tools.jar MC_Starstream.tla -config Starstream.cfg

# Parallel model check
java -jar tla2tools.jar MC_Starstream.tla -config Starstream.cfg -workers 4
```

## Key invariants

Note: **PC** means *program counter* (the resume point for a coroutine frame).

- `INV_LINEAR_NoDoubleSpend` — live and consumed sets are disjoint
- `INV_BALANCE_TxPreserved` — input tokens equal output tokens
- `INV_BALANCE_NoOverflow` — per-asset totals stay within bounds
- `INV_AUTH_ValidSpend` — committed txs have valid signatures
- `INV_AUTH_OwnerOnly` — signers own their inputs
- `INV_LOCK_Exclusive` — locks reference existing txs
- `INV_EFFECT_MustBeHandled` — no pending effects at completion
- `INV_EFFECT_SourceSuspended` — pending effects come from suspended inputs
- `INV_EFFECT_ContinuationMatch` — continuation matches suspended frame PC
- `INV_EFFECT_StackDepthBounded` — effect stack depth is bounded
- `INV_BALANCE_PendingOutputsNoNFTDuplication` — pending outputs don’t duplicate NFTs
- `INV_LOCK_AtomicRelease` — lock release is atomic with state change
- `INV_ROLLBACK_NoLeak` — failed txs leave no outputs/consumed inputs

## Common errors

- `Invariant ... is violated` — a safety property failed; inspect the counterexample trace
- `Deadlock reached` — no actions enabled (may be expected in a stuttering spec)
- `OutOfMemoryError` — state explosion; reduce bounds or add constraints
- `identifier ... is either undefined` — typo or missing `EXTENDS`

## Invariant lookup

| Concern | Invariant(s) |
|---------|--------------|
| Double-spend / replay | `INV_LINEAR_NoDoubleSpend`, `INV_ATK_NoReplay` |
| Unauthorized spend | `INV_AUTH_ValidSpend`, `INV_AUTH_OwnerOnly` |
| NFT duplication | `INV_BALANCE_NFTUnique`, `INV_BALANCE_PendingOutputsNoNFTDuplication` |
| Effect safety | `INV_EFFECT_MustBeHandled`, `INV_EFFECT_SourceSuspended` |
| Locking bugs | `INV_LOCK_Exclusive`, `INV_LOCK_AtomicRelease` |
| Overflow | `INV_BALANCE_NoOverflow` |

## State transitions (quick)

**UTXO:** `Created → Suspended_at_Yield → Reserved → Executing → (Suspended_at_Effect) → Executing → Consumed`  
**Rollback:** `Reserved/Executing → Suspended_at_Yield`

**Transaction:** `Idle → Reserve → Executing → Committing → Committed`  
**Rollback path:** `Reserve/Executing/Committing → Rollback → Failed`

## Module map

```
StarstreamTypes.tla
    |
    +-- StarstreamFrame.tla
    |       |
    |       +-- StarstreamUTXO.tla
    |       |
    |       +-- StarstreamEffects.tla
    |               |
    |               +-- StarstreamCoordination.tla
    |
    +-- StarstreamAuth.tla
            |
            +-- StarstreamTransaction.tla
                    |
                    +-- StarstreamLedger.tla
                            |
                            +-- StarstreamSpec.tla
                                    |
                                    +-- StarstreamInvariants.tla
                                            |
                                            +-- MC_Starstream.tla
```
