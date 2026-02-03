# 10. Conclusion

We have presented ICE-UTxO, a conservative extension of the extended UTxO model that equips transactions with coroutines, algebraic effects, and proof-carrying semantics. The model treats each transaction as an instance of a multiparty session protocol: coordination scripts specify allowed interactions as MPST global types with event-structure semantics; PTB-style compilation produces concrete, deterministic schedules; and IVC proof artifacts certify that the schedule conforms to the protocol.

The formal architecture comprises three layers on top of eUTxO: (1) coroutine state on UTxOs, enabling pause/resume semantics via frames; (2) transaction-level coordination via compiled PTB programs with explicit dataflow; and (3) IVC proof artifacts that gate commit behind cryptographic verification. When no coroutines yield and no effects are raised, the three layers collapse and ICE-UTxO degenerates to standard eUTxO.

The model has been fully mechanized in Lean 4 across about 4,500 lines of code with zero sorry, zero custom axioms, and no `Classical.choice` (one localized `classical` split). Key mechanized results include:

- **Strong conflict serializability**: a constructive bubble-sort proof showing that acyclic full-conflict precedence graphs imply all conflict-respecting permutations of the committed history produce the same core UTxO state --- the universal diamond property.
- **Concurrent-to-serial refinement**: a stuttering simulation proving that every concurrent execution maps to a serial execution under the abstraction map.
- **MPST-to-ledger bridge**: bidirectional theorems connecting local trace conformance (per-role, per-shard) to global trace consistency, enabling S-BAC-style shard-local verification.
- **Proof-gated commits**: only transactions with verified proof commitments can extend the ledger history.
- **Invariant preservation**: the six-part ledger invariant (no double-spend, locked subset active, history nodup, committed implies verified, extended precedence acyclicity, full precedence acyclicity) is preserved by every step of the operational semantics.

The strong serializability theorem via bubble-sort is, to our knowledge, the first constructive, machine-checked proof of this property for a UTxO-based ledger with concurrent interleaving semantics. The combination of MPST coordination scripts with event-structure semantics and S-BAC deployment provides a principled path from protocol specification to shard-local verification.

ICE-UTxO demonstrates that the gap between single-shot UTxO validators and rich multi-step, multi-party interactions can be bridged without abandoning the UTxO model's core strengths: atomicity, parallelism, and deterministic validation. By making the transaction schedule an explicit, proof-carrying artifact, ICE-UTxO turns coordination from an implicit encoding challenge into a first-class, formally verified component of the ledger.
