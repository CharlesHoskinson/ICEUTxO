# Oracle Checklist and Explanations

This document expands the oracle checklist into detailed guidance. Each item includes goals and strategy to keep the oracle deterministic, testable, and suitable as a single source of truth for golden vectors.

## 1) Freeze scope and interface: inputs/outputs, error model, deterministic vs nondet API

Goal: lock the boundary of the oracle so every consumer agrees on what it accepts and what it returns. This avoids moving targets that invalidate vectors and tests.

Strategy: define the precise input payload (ledger state + tx + optional choice) and the exact output contract (new state or structured error). Write these as Lean types first, then mirror them in any JSON schema.

Strategy: explicitly separate deterministic APIs from nondeterministic ones so callers can pick the right oracle and never mix semantics accidentally.

## 2) Define canonical IDs + ordering rules (UTXO, tx, token types) for stable vectors

Goal: ensure output stability across platforms and implementations by removing ordering ambiguity. This is critical for golden vectors.

Strategy: define canonical orderings for IDs and for map serialization (for example, sorted arrays by key). Encode this in the oracle and treat non-canonical input as invalid or normalize it before processing.

Strategy: document the ordering rules in the schema so any downstream consumer can reproduce identical byte-for-byte outputs.

## 2a) Resource/Gas Model

Goal: incorporate deterministic resource bounds so the oracle matches real-world execution limits and rejects transactions that exceed those bounds.

Strategy: add a gas or step counter parameter to `checkTx` and `applyTx`, decrement it on each modeled operation, and return a stable `Err::OutOfGas` when it reaches zero.

Strategy: make the cost model explicit and versioned so golden vectors encode both inputs and the resource budget that led to acceptance or rejection.

## 3) Write Lean core types for Idealized UTXO (Utxo, Tx, Ledger, TokenBag)

Goal: capture the minimal ledger semantics in Lean so the oracle is both executable and a basis for proofs. The types should be compact and unambiguous.

Strategy: model the smallest useful data shape with explicit IDs and token bags. Keep the core UTXO layer free of Starstream-specific fields to preserve reuse and clarity.

Strategy: prefer persistent maps or ordered sets so the model is efficient and deterministic, then provide a normalization layer for JSON.

## 3a) Crypto Spec

Goal: make ID generation and hashing fully concrete so golden vectors are byte-for-byte reproducible across implementations.

Strategy: define the exact hash functions, domain separation, and serialization rules in Lean (or a structurally identical stub) and use them for ID derivation.

Strategy: version the hashing spec and include it in the oracle schema so any change forces a deliberate vector regeneration.

## 4) Implement checkTx and applyTx for idealized layer; ensure total + deterministic

Goal: create a single, authoritative transition function that either returns the next ledger state or a precise error. This is the deterministic oracle core.

Strategy: implement checkTx as a pure validator that returns an error without mutating state, then implement applyTx as a thin wrapper that calls checkTx and applies updates.

Strategy: ensure every branch is total (no partial functions or "choose") and deterministic; if a condition is ambiguous, make it explicit in the inputs.

## 5) Add applyChunk (fold of applyTx) as the core oracle entrypoint

Goal: support multi-transaction golden vectors and an idealized notion of "block" or "chunk" application. This also matches IEUTxO-style reasoning.

Strategy: define applyChunk as a fold over applyTx, so its semantics are directly derived from the single-transaction oracle.

Strategy: keep error reporting precise by returning the first failing tx index and error code to aid debugging and regression triage.

## 5a) Execution Tracing

Goal: produce an optional, structured execution trace (witness) alongside the final state to aid debugging and ZK proving.

Strategy: implement a lightweight tracer monad or effect handler that records rule applications and intermediate facts without influencing deterministic results.

Strategy: define a stable trace schema and include it in vectors only when explicitly enabled, so the default oracle stays minimal.

## 6) Add Err taxonomy with stable codes/messages for golden vectors

Goal: make failures reproducible, inspectable, and stable across versions. Error identity is part of the oracle contract.

Strategy: enumerate error variants that match invariant categories (missing input, double spend, invalid signature, etc.). Assign stable codes and keep messages minimal and structured.

Strategy: version the error schema; if codes change, bump the oracle schema version and regenerate vectors.

## 7) Add JSON encode/decode + schema versioning + canonical normalization

Goal: provide a portable interchange format for vectors while preserving determinism. The oracle must be a reliable generator and consumer of vectors.

Strategy: define a strict JSON schema with a version field and validate inputs before processing. Reject or normalize non-canonical inputs to avoid divergent behavior.

Strategy: define a canonicalization pass that sorts maps and lists and normalizes optional fields so serialization is deterministic.

## 7a) FFI/CLI Wrapper

Goal: make the Lean oracle executable in CI and usable by downstream tooling through a stable CLI or FFI boundary.

Strategy: build a wrapper that reads JSON from stdin and writes results to stdout, with a deterministic exit code protocol for success or error.

Strategy: define and document the compilation pipeline (Lean -> C/binary) and ensure CI runs the exact artifact used for vector generation.

## 8) Golden vectors: deterministic input -> exact output/error; diff-based CI

Goal: make the oracle a single source of truth by asserting that known inputs produce exact outputs. This enables safe refactoring.

Strategy: store a curated set of vectors with expected outputs. In CI, run the oracle and perform strict diffs against expected JSON, failing on any delta.

Strategy: version vector sets and keep a changelog for any intentional changes to semantics.

## 9) Round-trip serialization: encode/decode = id on canonicalized states/txs

Goal: guarantee that serialization is lossless and deterministic. This protects against subtle drift in tooling.

Strategy: add tests that decode a vector, normalize it, encode it, then decode again and compare structural equality.

Strategy: also test rejection or normalization of malformed or non-canonical payloads to ensure the rules are enforced.

## 10) Invariant regression tests: one test per invariant predicate

Goal: ensure that each invariant has dedicated coverage and regressions are localized. This keeps the model aligned with formal intent.

Strategy: for each invariant, create at least one passing case and one failing case where possible. Keep the cases small and comprehensible.

Strategy: tie each test to a stable identifier matching the invariant name so failures are easy to interpret.

## 11) Property tests (idealized): valid tx preserves invariants; invalid tx yields expected error; applyChunk = fold

Goal: use property testing to cover many small cases beyond the golden set. This uncovers edge cases that curated vectors miss.

Strategy: generate small random ledgers and txs within bounds, then assert that applyTx preserves invariants when checkTx passes.

Strategy: assert that applyChunk equals the fold of applyTx to guarantee consistency between single-step and batch semantics.

## 12) Negative corpus: curated invalid cases for every error code

Goal: ensure the oracle emits the intended error for each invalid condition, not a generic or misleading failure.

Strategy: build a small suite of minimal failing cases, one per error code. Keep these cases stable and human-readable.

Strategy: use these cases as a lock on error precedence rules so failures are deterministic and consistent across versions.

## 13) Determinism tests: byte-identical output for identical inputs

Goal: guarantee that given the same input, the oracle always produces exactly the same output bytes. This is non-negotiable for golden vectors.

Strategy: run repeated executions in tests and compare serialized outputs byte-for-byte. Use normalization to remove any incidental ordering.

Strategy: include a "no nondeterminism" audit in CI that checks for usage of unordered collections or randomness.

## 14) Extend types to Starstream (Frame, Effects, Coordination, Proofs, Locks)

Goal: bring Starstream-specific state into the oracle while keeping the idealized layer intact. This preserves modularity.

Strategy: define separate Starstream types that extend or embed the idealized types. Keep the extension fields explicit rather than optional.

Strategy: document mapping between Starstream fields and TLA concepts to maintain alignment with the spec.

## 15) Implement Star.checkTx + Star.applyTx (deterministic, atomic commit)

Goal: provide a deterministic Starstream oracle that treats a transaction as an atomic application of protocol rules.

Strategy: mirror the TLA invariants as executable checks before state mutation. Keep the commit path unified so failures are predictable.

Strategy: prefer a single applyTx that integrates reservation, execution outcomes, and commit invariants based on tx contents.

## 16) Validate against Starstream invariants subset (balance/locks/effects/proofs)

Goal: ensure the oracle enforces the most critical safety properties that match the current model checking set.

Strategy: implement executable predicates for key invariants and call them from checkTx or as post-conditions in applyTx.

Strategy: use the invariant regression tests to lock behavior and prevent drift from the TLA spec.

## 17) Add nondet layer: Choice, stepWithChoice, step (set/finset)

Goal: extend the oracle to explore interleavings and nondeterministic decisions without compromising deterministic semantics.

Strategy: define an explicit Choice type and make stepWithChoice deterministic. This makes nondeterminism explicit and reproducible.

Strategy: implement step as an enumerator over all valid choices within bounds, returning a finite set of successor states.

## 18) stepWithChoice deterministic per Choice

Goal: guarantee that nondeterministic behavior is entirely controlled by the Choice input. This keeps testing and debugging sane.

Strategy: include tests that apply the same Choice multiple times and verify identical results, including error identity.

Strategy: ensure Choice includes all information needed to resolve ambiguity (which tx, which effect, which handler, etc.).

## 19) step enumerates all choices and matches stepWithChoice

Goal: ensure the nondet enumerator is complete and consistent with the deterministic per-choice semantics.

Strategy: test that every result in step corresponds to some Choice and that every valid Choice produces a result in step.

Strategy: if bounds are used, explicitly include the bound parameters in the enumerator input for reproducibility.

## 20) Differential checks vs TLA on bounded cases; document invariant mapping

Goal: cross-validate the executable oracle against the TLA model to increase confidence and catch semantic drift.

Strategy: generate small bounded cases and compare oracle results to TLA outcomes or invariant checks. Record any mismatch and resolve it.

Strategy: maintain a mapping table from TLA invariants to Lean predicates and keep it updated as the spec evolves.
