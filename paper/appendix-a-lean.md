# Appendix A: Lean 4 Theorem Statements

This appendix reproduces the type signatures of thirteen key theorems from the ICE-UTxO Lean 4 mechanization. All theorems are fully proved with zero sorry and zero custom axioms.

**Reading Lean signatures.** Each `theorem` declaration has the form `theorem name (params) (hypotheses) : conclusion`. Parenthesized arguments `(x : Type)` are explicit parameters; hypotheses named `h...` are assumptions. The colon separates hypotheses from the conclusion (the property being proved). `List Tx` is a list of transactions, `Finset UTXOId` is a finite set of UTxO identifiers, and `→` denotes implication. The `¬` symbol is negation. No Lean programming knowledge is needed to read these signatures as mathematical statements.

### Ledger Semantics (Track 1: StarstreamPilot.lean)

Theorems A.1--A.6 concern the concurrent ledger model: conflict serializability, proof-gated commit, invariant preservation, and the concurrent-to-serial refinement. These results establish that the ICE-UTxO ledger satisfies standard safety properties under arbitrary interleaving of the eight `Step` constructors.

## A.1 Core Commutativity

Non-conflicting transactions commute at the core state level. This is the algebraic heart of the serializability argument.

```lean
-- StarstreamPilot.lean:491
theorem core_commute (s : CoreState) (t1 t2 : Tx)
    (hnc : ¬ fullConflicts t1 t2) :
    applyCoreCommit (applyCoreCommit s t1) t2 =
    applyCoreCommit (applyCoreCommit s t2) t1
```

## A.2 Strong Serializability via Bubble-Sort

Acyclic full-conflict precedence graphs imply all conflict-respecting permutations produce the same core state. This is the universal diamond property.

```lean
-- StarstreamPilot.lean:720
theorem acyclic_strong_serializable (s₀ : CoreState) (hist : List Tx)
    (hnodup : hist.Nodup)
    (hacyc : fullPrecGraphAcyclic hist) :
    strongCoreSerializable s₀ hist
```

## A.3 Proof-Gated Commit

Any step that extends the ledger history must have verified proof commitments. Established by exhaustive case analysis on the 8-constructor `Step` inductive.

```lean
-- StarstreamPilot.lean:1074
theorem commit_requires_proof {m l l' tx} :
    Step m l l' →
    l'.history = l.history ++ [tx] →
    proofOk tx
```

## A.4 Invariant Preservation

Every step of the operational semantics preserves the six-part ledger invariant. Floyd-Hoare style case analysis on all step constructors.

```lean
-- StarstreamPilot.lean:1321
theorem step_preserves_invariant {m : Mode} {l l' : Ledger}
    (hstep : Step m l l')
    (hinv : ledgerInvariant l) :
    ledgerInvariant l'
```

## A.5 Concurrent-to-Serial Refinement

Every concurrent execution refines the serial specification via a stuttering simulation. Non-commit steps are stuttering; commit steps produce serial steps.

```lean
-- StarstreamPilot.lean:1480
theorem concurrent_refines_serial {m : Mode} {l₀ lₙ : Ledger}
    (hexec : Steps m l₀ lₙ)
    (hinv : ledgerInvariant l₀) :
    SerialSteps m (absLedger l₀) (absLedger lₙ)
```

## A.6 No Double-Spend Preservation

The no-double-spend invariant is preserved through commit operations, given that outputs are fresh and inputs are live.

```lean
-- StarstreamPilot.lean:1110
theorem commit_preserves_no_double_spend {l : Ledger} {tx : Tx}
    (hinv : noDoubleSpend l)
    (hfresh : outputsFresh l tx)
    (hlive : inputsLive l tx) :
    noDoubleSpend (applyCommit l tx)
```

### Coordination Layer (Track 2: Script.lean)

Theorems A.7--A.8 concern the MPST coordination layer: projection from global to local scripts and reconstruction of global trace consistency from local conformance. These results ensure that the per-role, per-shard view of a protocol is consistent with the global specification.

## A.7 Projection Preserves Local Conformance

Global conformance of a script on a trace implies local conformance for every role on the projected trace.

```lean
-- Script.lean:880
theorem proj_localConform_of_globalConform (s : Script) (r : RoleId)
    (tr : List EventId)
    (h : s.globalConform tr) :
    s.localConform r (s.traceProj r tr)
```

## A.8 Cross-Role Trace Reconstruction

Local conformance for all roles, combined with cross-role consistency, implies global trace consistency. This is the bottom-up direction of the MPST-to-ledger bridge.

```lean
-- Script.lean:615
theorem traceConsistent_of_local_and_cross (s : Script) (tr : List EventId)
    (hwf : s.wellFormed)
    (hnd : tr.Nodup)
    (hevents : ∀ e, e ∈ tr → e ∈ s.events)
    (hlocal : ∀ r ∈ s.roles, Script.localConform s r (s.traceProj r tr))
    (hcross : s.crossRoleConsistent tr) :
    s.traceConsistent tr
```

### PTB Compilation (PTB.lean)

Theorems A.9--A.11 concern the PTB compilation layer: translation from PTB programs to event-structure scripts, validity of program-order traces, and construction of globally valid coordination witnesses from well-formed programs. These results establish that the concrete PTB execution format correctly induces the event-structure semantics required by the coordination layer.

## A.9 PTB-to-Script Well-Formedness

A PTB program with valid role assignments produces a well-formed event-structure script. Acyclicity of the induced order follows from the $i < j$ constraint.

```lean
-- PTB.lean:302
theorem Program.toScript_wellFormed
    (cfg : Config) (p : Program)
    (hroles : p.rolesOK cfg)
    (hkind : p.roleKindOK cfg) :
    (p.toScript cfg).wellFormed
```

## A.10 Program-Order Trace Validity

The full program-order trace is a valid trace of the induced script when no conflicts exist. This is the base case for the PTB-as-proposed-trace argument.

```lean
-- PTB.lean:375
theorem Program.validTrace_trace
    (cfg : Config) (p : Program)
    (hno : p.noConflicts) :
    Script.validTrace (p.toScript cfg) (p.trace)
```

## A.11 Witness Construction

A well-formed, conflict-free PTB program produces a globally valid coordination witness, combining script well-formedness with trace validity.

```lean
-- PTB.lean:595
theorem Program.witnessGlobalOK_of
    (cfg : AccessConfig) (p : Program) (keep : Nat → Bool)
    (hroles : p.rolesOK cfg.toConfig)
    (hkind : p.roleKindOK cfg.toConfig)
    (hconf : p.conflictFree keep)
    (hdown : p.downClosed keep) :
    witnessGlobalOK (Program.toWitness cfg p keep)
```

### S-BAC Bridge (SBAC.lean)

Theorems A.12--A.13 connect Track 1 and Track 2 through the coordination witness. Together they establish a bidirectional bridge: global witness validity decomposes into local validity (top-down), and local validity with consistency reconstructs global validity (bottom-up).

## A.12 Global Witness Implies Local Witness

A globally valid coordination witness projects to valid local witnesses for all roles. This is the top-down direction enabling S-BAC shard-local verification.

```lean
-- SBAC.lean:36
theorem witnessLocalOK_of_global (w : CoordWitness)
    (h : witnessGlobalOK w) :
    witnessLocalOK w
```

## A.13 Consistent Witness Implies Global Conformance

A well-formed script with a consistent witness trace implies global conformance. Combined with Theorem A.8, this closes the bidirectional bridge.

```lean
-- SBAC.lean:41
theorem witnessGlobalOK_of_local_and_consistent (w : CoordWitness)
    (hwf : w.script.wellFormed)
    (hcons : witnessConsistent w) :
    witnessGlobalOK w
```

---

**Summary of mechanization metrics:**

| Metric | Value |
|---|---|
| Total lines of Lean 4 | 4,502 |
| Declarations | ~303 |
| Theorems | ~95 |
| Lemmas | ~49 |
| Definitions | ~159 |
| Instances | 0 |
| Examples | 0 |
| Sorry count | 0 |
| Custom axioms | 0 |
| `Classical.choice` invocations | 0 |
| `classical` tactic uses | 1 (`Script.lean`:622) |
| Standard axioms | `propext`, `Quot.sound`, `funext` |
