----------------------- MODULE StarstreamMinimal -----------------------
(***************************************************************************
 * Minimal spec: what Starstream implements today.
 *
 * Done: effect kinds, type primitives, UTXO storage (WASM globals)
 * Not done: tx lifecycle, handlers, coroutines, proofs
 ***************************************************************************)

EXTENDS Naturals, FiniteSets

EffectKinds == {"Pure", "Effectful", "Runtime"}
TypePrimitives == {"i64", "bool", "unit"}

EffectLe(e1, e2) ==
    \/ e1 = "Pure"
    \/ (e1 = "Effectful" /\ e2 \in {"Effectful", "Runtime"})
    \/ (e1 = "Runtime" /\ e2 = "Runtime")

EffectJoin(e1, e2) ==
    IF e1 = "Runtime" \/ e2 = "Runtime" THEN "Runtime"
    ELSE IF e1 = "Effectful" \/ e2 = "Effectful" THEN "Effectful"
    ELSE "Pure"

\* Effect lattice invariants
INV_EffectJoinCommutative ==
    \A e1, e2 \in EffectKinds : EffectJoin(e1, e2) = EffectJoin(e2, e1)

INV_EffectJoinIdempotent ==
    \A e \in EffectKinds : EffectJoin(e, e) = e

=============================================================================
