# ICE-UTxO coordination scripts: formal syntax + typing rules (draft)

## Goal
Define a small, formal language for ICE-UTxO coordination scripts that:
- Defines global protocols as event structures (partial-order schedules).
- Projects to local specifications for shard-local checking.
- Admits compilation to PTB-style programs whose traces are checked against the global type.
- Aligns with Chainspace-style evidence and S-BAC prepare/accept.

This is intentionally minimal and ASCII-only; it is meant to be precise enough
for PL researchers to debate and to support a Lean/TLA+ mechanization.

## Core sets and notation
- Roles: r in Role. Roles include UTXO coroutines and interface handlers.
- Interfaces: i in Iface. (An interface can be treated as a role or a role family.)
- UTXO ids: u in UtxoId.
- Handlers: h in HandlerId.
- Effect ops: op in Op (op name + payload type).
- Events: e in EventId.

We model a script as an event structure:
  Script = (RoleDecls, Events, Order, Conflict, Label)
where Order is a strict partial order (<) and Conflict is symmetric and
irreflexive (#). A run is a configuration: a finite set of events that is
conflict-free and down-closed under Order.

## Global script syntax (event-structure style)

Script ::= 'script' Name '{' Roles Events Constraints '}'

Roles ::= 'roles:' RoleDecl (',' RoleDecl)* ';'
RoleDecl ::= RoleName ':' RoleKind
RoleKind ::= 'utxo' | 'iface' | 'shard'

Events ::= 'events:' EventDecl+ 
EventDecl ::= EventId ':' Action ';'

Action ::= Raise | Resume | Install | Uninstall | Read | Consume | Produce | Lock | Snapshot

Raise     ::= RoleName '->' RoleName ':' 'raise'  Op '(' Payload ')'
Resume    ::= RoleName '->' RoleName ':' 'resume' Op '(' Payload ')'
Install   ::= RoleName '->' RoleName ':' 'install' HandlerId
Uninstall ::= RoleName '->' RoleName ':' 'uninstall' HandlerId

Read      ::= RoleName ':' 'read' UtxoId
Consume   ::= RoleName ':' 'consume' UtxoId
Produce   ::= RoleName ':' 'produce' UtxoId
Lock      ::= RoleName ':' 'lock' UtxoId
Snapshot  ::= RoleName ':' 'snapshot' UtxoId

Constraints ::= 'constraints:' Constraint+ 
Constraint  ::= EventId '<' EventId ';'
              | EventId '#' EventId ';'

Notes:
- Roles on the left of '->' are senders/raisers; on the right are receivers/handlers.
- Handler install/uninstall events are explicit and can be ordered/guarded like any event.
- UTXO actions (read/consume/produce/lock/snapshot) are explicit events in the script.
- Branching is encoded via Conflict (#) sets; sequencing via Order (<).

### Derived syntactic sugar (optional)
Sequence:   e1; e2; e3  expands to e1 < e2, e2 < e3
Parallel:   parallel {A} {B} encodes no order between events in A and B
Choice:     choice {A} {B} encodes pairwise conflict between events in A and B

## Local types (projections)

Given a script S and role r, projection yields a local event structure:
  Proj(S, r) = (E_r, <_r, #_r, lab_r)
where:
  E_r = { e in E | r participates in lab(e) }
  <_r  = < restricted to E_r
  #_r  = # restricted to E_r
  lab_r(e) = lab(e) with roles erased to local input/output tags

Participation rule:
- r participates in event e if r is the sender or receiver for e, or if lab(e)
  is a UTXO action performed by r.

Local labels (examples):
- raise:  r -> i : raise op becomes   out raise op to i
- resume: i -> r : resume op becomes  in  resume op from i
- read/consume/produce/lock/snapshot remain local actions

## Typing judgments

We use three core judgments:
1) WF(S): the global script is well-formed.
2) Proj(S, r) = L_r: local projection.
3) L_r |- tr_r : local trace conforms to the local type.

## Well-formedness rules (global)

WF(S) holds if all of the following are satisfied.

WF-RoleDecls
- Every role name is unique and its kind is declared.

WF-EventDecls
- Every event id is unique.
- All roles referenced in events are declared.
- All UTXO ids are declared in the transaction scope or produced within it.

WF-Order
- Order (<) is acyclic and irreflexive.

WF-Conflict
- Conflict (#) is symmetric and irreflexive.
- Conflict is downward closed:
    if e # f and e' < e, then e' # f
    if e # f and f' < f, then e # f'
  (prevents a branch from sharing causal prefixes with a conflicting branch).

WF-HandlerScope
- For any interface i and handler h:
  - install(i,h) must precede any resume that depends on h.
  - uninstall(i,h) must follow all resumes that depend on h.
  - no overlapping installs of different handlers for the same interface
    unless ordered by < (no parallel install on same interface).

WF-UTxO-Linearity
- Each consumed UTXO appears in exactly one Consume event.
- A Produce event creates a fresh UTXO id (not previously consumed/produced).
- If a UTXO is consumed, all reads of that UTXO must be ordered before the consume.
- If a UTXO is locked, any other action on that UTXO must be ordered with it.

WF-EffectPairing (optional, if enforced at script level)
- For each raise event, there exists a matching resume event on the same interface/op.
- Matching is encoded via explicit order constraints (raise < resume).

These rules can be expressed as static checks over the event structure.

## Local conformance (trace typing)

A local trace is a finite sequence of events tr_r = e1, e2, ..., ek.
We treat the trace as a linearization of a configuration of L_r.

Conformance judgment: L_r |- tr_r

Rules (sketch):

(TR-EMPTY)
-----------
L_r |- []

(TR-STEP)
L_r |- tr_r
lab_r(e) is enabled in L_r after tr_r
-----------------------------------
L_r |- tr_r ++ [e]

Enablement conditions (informal):
- All predecessors of e (under <_r) are already in tr_r.
- No conflicting event with e is in tr_r.
- Action-specific guards are satisfied (e.g., handler installed if needed).

This is standard event-structure trace conformance.

## Event-structure operational semantics (formal)

We define small-step semantics over configurations of a script S = (E, <, #, lab).

Configuration:
  C subseteq E is a configuration iff
  (1) Conflict-free: for all e,f in C, not (e # f)
  (2) Downward closed: for all e in C, for all e' with e' < e, we have e' in C

Enablement:
  enabled(e, C) holds iff
  (1) e notin C
  (2) for all e' with e' < e, e' in C
  (3) for all f in C, not (e # f)

Step:
  C -> C' iff exists e such that enabled(e,C) and C' = C union {e}

Trace:
  A finite trace tr = [e1, ..., en] is valid iff there exists a sequence of
  configurations C0 -> C1 -> ... -> Cn with C0 = {} and Ci = Ci-1 union {ei}.
  Every valid trace is a linearization of a configuration, and every configuration
  has at least one linearization.

Local semantics:
  The same definitions apply to each local projection L_r.

Notes:
- This is the standard event-structure semantics used for partial-order models.
- It aligns with "scheduler as a partial order": a transaction is a certificate
  that a specific linearization is permitted.

## PTB compilation target (trace language)

The global script is the semantic source; a transaction carries a compiled
PTB-style program whose execution trace must be a valid linearization of the
global event structure.

PTB sketch (informal):
- A program is a list of commands with explicit inputs and outputs.
- Results are stored in temporary registers Result(i).
- Later commands can consume earlier results.

Compilation/translation rules (to events and constraints):
- Events: one event per PTB command; label by the corresponding action kind.
- Order edges are added when:
  - a command consumes Result(i) from a prior command,
  - two commands access the same object and at least one is a write/consume/lock/produce,
  - a handler is installed before use and uninstalled after use,
  - the global type requires additional order constraints.
- Conflict edges are added when:
  - two commands consume the same UTXO,
  - two commands install different handlers for the same interface without ordering,
  - an explicit choice/guarded branch is represented in the PTB (choice => conflict).

The PTB program order is the proposed trace; the witness must show it is
accepted by the global type and respects < and #.

## Projection algorithm (global -> local)

Input: global script S = (E, <, #, lab) and role r
Output: local script L_r = (E_r, <_r, #_r, lab_r)

Algorithm:
1) E_r := { e in E | r participates in lab(e) }
2) <_r := < restricted to E_r x E_r
3) #_r := # restricted to E_r x E_r
4) lab_r := relabel lab(e) into local action tags
   - if lab(e) = r -> s : raise op then lab_r(e) = out raise op to s
   - if lab(e) = s -> r : raise op then lab_r(e) = in raise op from s
   - if lab(e) = r -> s : resume op then lab_r(e) = out resume op to s
   - if lab(e) = s -> r : resume op then lab_r(e) = in resume op from s
   - if lab(e) = r : read/consume/produce/lock/snapshot then local action

Participation:
  r participates in e iff r is sender or receiver in lab(e), or lab(e) is a
  UTXO action performed by r.

Complexity:
  O(|E| + |<| + |#|) with straightforward filtering.

## Projection and semantics: proof sketches

Lemma 1 (Projection preserves configurations):
  If C is a global configuration of S, then C_r = C cap E_r is a configuration
  of L_r.
Sketch:
  Conflict-free and downward-closed are preserved under restriction because
  <_r and #_r are restricted relations. If e in C_r and e' <_r e, then e' < e
  in the global script, so e' in C by downward-closure, hence e' in C_r.

Lemma 2 (Projection preserves traces):
  If tr is a valid global trace, then tr|r (filtering to E_r) is a valid local
  trace for L_r.
Sketch:
  The global trace corresponds to a chain of configs C0 -> ... -> Cn.
  Restrict each Ci to C_i,r, then the same event-adding steps witness the local
  trace, because enablement conditions depend only on < and # restricted to E_r.

Lemma 3 (Local conformance + global witness => global conformance):
  Suppose for each role r we have a local trace tr_r that is a linearization of
  a local configuration C_r, and the union of traces is consistent with global
  < and # (no conflicts, and all < edges are respected). Then the union is a
  valid global trace of S.
Sketch:
  Because all < edges are respected, the union trace is a linearization of a
  down-closed set C. Conflict-freedom follows from global # consistency. Thus
  C is a global configuration and the union trace is valid.

These are standard event-structure arguments and can be mechanized in Lean.

## Global conformance (transaction-level)

A transaction provides a PTB program and a witness W that consists of:
- the PTB trace (program order) and its role projections,
- cross-role ordering evidence required by the global type.
We accept iff:

(TX-CONFORM)
For all roles r: Proj(S, r) = L_r and L_r |- tr_r
And the union of tr_r respects the global < and # constraints
------------------------------------------------------------
S |- W : ok

This is the core condition to be checked during S-BAC prepare, per shard.

## SBAC alignment (where typing is used)

Each shard checks local conformance and UTXO constraints in its prepare step:
- Local type conformance: L_r |- tr_r
- UTXO constraints: WF-UTxO-Linearity (restricted to local objects)
- Handler scope: WF-HandlerScope (restricted to local interface roles)

ALL PREPARED => accept(commit). Any abort => accept(abort).

## Open design knobs (explicitly parameterized)
- Does the script enforce raise-resume pairing (WF-EffectPairing), or can a
  resume be optional and encoded in the witness?
- Are handler install/uninstall events explicit in scripts or inferred?
- Is projection based on global types with explicit choice, or purely on
  event structures (preferred for partial order)?
- Does the PTB allow guarded branching, and if so how are conflicts encoded?
- Do we allow reordering of independent PTB commands, or require strict program order?

## Next iteration goals
- Tighten the PTB compilation rules (explicit access sets and handler lifetimes).
- Specify command-level semantics (failures, gas, and result typing).
- Connect PTB traces to the Lean event-structure model.

## Existing code for the UTXO state machine (where to look)
- TLA+ UTXO lifecycle + state transitions: `tla/StarstreamUTXO.tla`
- TLA+ effects + handlers + coordination phases: `tla/StarstreamEffects.tla`,
  `tla/StarstreamCoordination.tla`
- Lean concurrent ledger + steps (commit/abort/lock/effect/handler): `lean/StarstreamPilot.lean`
