# Changelog

This file tracks notable changes to the Starstream TLA+ specification and docs.

## 2026-01-27

- Added IEUTxO ledger helpers and chunk-validity invariants to scaffold serializable-trace refinement.
- Introduced proof commitments + lifecycle in the ledger/transactions, and gated commit on verified proofs.
- Added the optimistic-concurrency variant with read/write sets and commit-time validation.
- Expanded interface-aware effects and handler-stack modeling (routing + invariants).
- Bounded proof hash enumeration (`SampleFrameHashes`) and documented TLC performance tradeoffs.
