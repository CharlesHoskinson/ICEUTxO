# ICE-UTxO coordination scripts: MPST + Chainspace SBAC fit

## Purpose
This note sketches the coordination-script requirements for ICE-UTxO using MPST
results and explicitly aligns them with Chainspace's Sharded Byzantine Atomic
Commit (S-BAC) model. It is a first-pass synthesis based on the literature review
and the Chainspace paper.

## Chainspace SBAC recap (facts we will align with)
From the Chainspace paper:
- Transactions are a list of traces. Each trace contains a contract id, procedure
  name, inputs, references, outputs, locals, and dependencies (dep) on other
  traces. Validity is defined by a sequencing rule for traces and a check rule
  that runs the contract checker with side conditions on active objects and types.
- The client executes procedures to produce outputs and provides evidence so
  shards can run checkers without re-executing private computation.
- Objects are immutable, active/inactive; inputs are consumed, outputs become
  active; references must be active but remain so.
- S-BAC runs prepare/accept across all concerned shards: each shard decides
  local prepared(commit/abort) after checking local validity and object status.
  All prepared => accept(commit); any abort => accept(abort). Objects are
  locked during the prepare/accept window.

## MPST results relevant to ICE-UTxO coordination scripts
- Global types specify the full multi-role protocol; projection yields local
  types to check each endpoint; this yields communication safety/progress in
  asynchronous multiparty systems. (Honda/Yoshida/Carbone)
- Interleaving multiple sessions can break progress; interaction-type analyses
  infer global progress constraints across interleavings. (Bettini; Coppo)
- Event-structure semantics give a partial-order model of asynchronous sessions
  and preserve progress; this matches a scheduler-as-partial-order view.
  (Castellani/Dezani-Ciancaglini/Giannini)
- Rely/guarantee MPST avoids overly restrictive global duality and supports
  complex inter-role dependencies. (Scalas/Yoshida)
- Toolchains (Scribble, NuScr, StMungo, TypeScript pipelines) show practical
  projections to CFSM/EFSMs and endpoint APIs, with optional runtime monitors.
- Hybrid verification and runtime monitoring show how to combine static
  protocol checks with lightweight runtime enforcement. (Hu/Yoshida; Neykova)

## Mapping ICE-UTxO to MPST + SBAC (sketch)

### A. Coordination script as a global type
- Roles: UTXO coroutines (each UTXO state machine), interface handlers, and
  possibly shard-level roles for cross-shard decisions.
- Actions: effect raises, handler installs/uninstalls, resume/commit/abort
  actions, and explicit resource claims/reads.
- Dependencies: express causal constraints (must-happen-before) and mutual
  exclusion; use event-structure semantics to represent partial orders instead
  of a single total interleaving.

### B. Local projections as shard-local checkers
- Projection yields, for each UTXO/handler, a local automaton (EFSM/CFSM-like)
  that enumerates allowed effect and resume steps.
- This projection is what each shard can check during S-BAC prepare.
- Rely/guarantee typing is a good fit if we do not want to require a single
  global duality check for complex dependency patterns (e.g., multi-UTXO
  callbacks and conditionally installed handlers).

### C. The ICE-UTxO transaction payload (proposal)
A transaction can bundle:
1) The global coordination script (global type).
2) A partial-order trace certificate (IVC witness) that proves the actual
   coroutine interleaving is a valid execution of the global type.
3) Per-role local trace slices (optional) or the data needed to reconstruct
   them from the certificate.
4) Standard UTXO inputs/outputs and any references.

This mirrors Chainspace's trace list with dependencies: the global type gives
allowed causality, the certificate proves one specific allowed run, and the
per-role projection allows each shard to verify its local slice without
re-running computation.

### D. SBAC integration points
- Prepare(T): each concerned shard verifies:
  - its local objects are active and not already locked
  - its local trace slice conforms to the projected type
  - the IVC witness locally validates the claimed effects/resumes
- Local prepared(commit/abort): emitted with signatures
- Accept(T,*): uses ALL PREPARED or SOME PREPARED to commit or abort
- Commit: consume inputs; create outputs; advance coroutine state in outputs
- Abort: release locks; no outputs created

This aligns with the Chainspace model where client computation is verified by
checkers, not re-executed. Here, the checker also validates protocol conformance
from the local projection.

## What ICE-UTxO needs (actionable design requirements)

### 1) Formal language for coordination scripts
- Syntax for roles, effect ops, handlers, resume points, and causal constraints
- Global types with explicit partial-order constructs (not just sequencing)

### 2) Semantics and proof artifacts
- Event-structure or pomset semantics for the global type
- Projection algorithm to local types
- Certificate/IVC format that can be checked shard-locally

### 3) Progress and safety across interleavings
- A global-progress analysis (Bettini/Coppo style) to prevent stuck
  interleavings across multiple coroutines
- Explicit conditions for allowed handler installation/removal and effect
  availability

### 4) SBAC-aligned validation
- Define the local checker predicate that each shard runs in prepare:
  (local projection + IVC witness + local state constraints)
- Define which parts of the global proof are required by each shard
- Define the minimal evidence to include in the transaction (for auditability)

### 5) Implementation path
- Use Scribble-like global syntax as a starting point, then extend for effects
  and resume
- Compile to EFSM/CFSMs (NuScr-style) for local validation
- Provide a runtime monitor or checker that validates local traces against
  EFSMs using the IVC witness

## SBAC fit summary (one paragraph)
S-BAC already provides the atomic commit skeleton we need: each shard locally
checks validity and object activity, then collectively commits iff all shards
prepared-commit. If we treat ICE-UTxO coordination scripts as global types and
verify their projections locally during prepare, then S-BAC becomes the natural
commit protocol for inter-UTXO coroutines. The IVC witness plays the role of
Chainspace-style evidence: it lets shards validate the coroutine interleaving
without re-running computation, while still enforcing protocol conformance and
UTXO constraints.

## Next steps (if you want me to proceed)
1) Draft a formal syntax + typing rules for coordination scripts.
2) Write a concrete SBAC-checker predicate for shards, with data dependencies.
3) Sketch the IVC witness format that supports local projection checks.
