# Implementation Status

ICE-UTxO is the formal specification. Starstream is the implementation.

## Feature Matrix

| Feature | Spec Location | Status |
|---------|---------------|--------|
| Effect kinds | `StarstreamPilot.lean` | ✅ Done |
| Type primitives | `StarstreamPilot.lean` | ✅ Done |
| Structs/enums | `StarstreamPilot.lean` | ✅ Done |
| UTXO storage | `StarstreamUTXO.tla` | ✅ Done |
| Event emission | `StarstreamEffects.tla` | ⚠️ Syntax only |
| Effect raise | `StarstreamEffects.tla` | ⚠️ Syntax only |
| UTXO state machine | `StarstreamUTXO.tla` | ❌ Not started |
| Yield/resume | `StarstreamFrame.tla` | ❌ Not started |
| Handler stacks | `StarstreamEffects.tla` | ❌ Not started |
| Transaction phases | `StarstreamSpec.tla` | ❌ Not started |
| IVC proofs | `StarstreamProof.tla` | ❌ Not started |
| MPST coordination | `Script.lean` | ❌ Not started |
| S-BAC sharding | `SBAC.lean` | ❌ Not started |

## Compilation

Starstream compiles to WASM:
- UTXO storage → WASM globals with get/set exports
- Functions → WASM functions
- Effect keywords → (future) host function calls

## Phases

1. **Language core** — Done (parser, typechecker, WASM codegen)
2. **Coroutines** — Next (yield/resume, frame serialization)
3. **Effects** — Future (handler stacks, dispatch)
4. **Ledger** — Future (mock ledger, token conservation)
5. **Proofs** — Future (IVC/PCD)

## See also

- `specs/iceUTXO.md` — Core idea
- `tla/StarstreamSpec.tla` — Full spec
- `lean/README.md` — Proof inventory
