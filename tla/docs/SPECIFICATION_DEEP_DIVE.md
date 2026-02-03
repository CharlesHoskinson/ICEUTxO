# Exhaustive Exposition: Starstream TLA+ Formal Specification

## Table of Contents

- [Part I: Introduction and Context](#part-i-introduction-and-context)
- [Part II: Architectural Foundation](#part-ii-architectural-foundation)
- [Part III: Transaction and Ledger Semantics](#part-iii-transaction-and-ledger-semantics)
- [Part IV: What the Specification Proves](#part-iv-what-the-specification-proves)
- [Part V: What the Specification Does NOT Prove](#part-v-what-the-specification-does-not-prove)
- [Part VI: How Engineers Can Use This Specification](#part-vi-how-engineers-can-use-this-specification)
- [Part VII: Open Problems and Future Work](#part-vii-open-problems-and-future-work)
- [Appendix: Quick Reference](#appendix-quick-reference)

## Part I: Introduction and Context

### 0.5 Reader orientation (quick links)

If you want short entry points before the deep dive:

- **Quick reference:** [QUICK_REFERENCE.md](QUICK_REFERENCE.md) (commands + invariants + module map)
- **Module reference:** [MODULES.md](MODULES.md)
- **Invariant catalog:** [INVARIANTS.md](INVARIANTS.md)
- **State machines:** [STATE_MACHINES.md](STATE_MACHINES.md)
- **Running TLC:** [USAGE.md](USAGE.md)

### 0.6 Glossary (minimal)

- **UTXO model**: State is carried by discrete “outputs” (UTXOs). Spending a UTXO consumes it and creates new UTXOs.
- **Stackless coroutine**: A resumable computation that stores its own state (PC + locals) instead of a call stack.
- **Coroutine frame**: The stored execution state of a UTXO (PC = program counter, locals, method ID, hash).
- **Algebraic effect**: A structured “request” raised by a coroutine that must be handled by a caller/handler.
- **Continuation**: The suspended point to resume after an effect is handled (modeled by `continuationId` + frame PC).
- **Coordination script**: The transaction-level script that sequences calls across multiple UTXOs.

**UTXO vs Account (quick intuition)**

```
Account model (Ethereum)         UTXO model (Starstream/Bitcoin)
---------------------------     --------------------------------
Alice.balance = 100             UTXO#1 (Alice, 100)
Send 30                         Spend UTXO#1
Alice.balance = 70              Create UTXO#2 (Bob, 30)
Bob.balance = 30                Create UTXO#3 (Alice, 70)
```

### 0.7 TLA+ mini-primer (just enough to read the spec)

- `EXTENDS` imports other modules.
- `CONSTANTS` are fixed model parameters (set in `Starstream.cfg`).
- `VARIABLES` are state variables that can change per step.
- `x'` (prime) means “the value of x in the next state”.
- `/\` means **and**, `\/` means **or**, `=>` means **implies**.
- `[]` means **always**, `<>` means **eventually**.
- `[k |-> v]` is a record; `r[k]` accesses field `k`.
- `{e : x \in S}` is set comprehension; `\A` and `\E` are “for all” / “exists”.

**TLA+ → Python/JavaScript quick equivalents**

| TLA+ | Python | JavaScript |
|------|--------|------------|
| `\A x \in S : P` | `all(P(x) for x in S)` | `S.every(x => P(x))` |
| `\E x \in S : P` | `any(P(x) for x in S)` | `S.some(x => P(x))` |
| `{e : x \in S}` | `{e for x in S}` | `new Set(S.map(x => e))` |
| `x \in S` | `x in S` | `S.has(x)` |
| `<<a, b>>` | `(a, b)` | `[a, b]` |
| `IF c THEN a ELSE b` | `a if c else b` | `c ? a : b` |

### 0.8 Specification status and limitations (summary)

**Implemented in the spec:**
- Full UTXO lifecycle including `Executing` and `Suspended_at_Effect`
- Two-step commit/abort (`Committing`, `Rollback`)
- Effect handling tied to suspended inputs + continuation matching
- Adversarial injection/rejection of invalid transactions

**Still out of scope:**
- Network/consensus behavior, ordering incentives (MEV)
- Gas/execution costs and DoS modeling
- Oracle/price feeds and economic attacks
- Cryptographic soundness (hashes/signatures are abstract)

### 1. What Starstream Is and Why Formal Verification Matters

Starstream is a blockchain protocol built on a UTXO (Unspent Transaction Output) model extended with stackless coroutines and algebraic effects. Unlike account-based blockchains where state lives in mutable contract storage, Starstream treats each UTXO as a self-contained execution context that can yield, suspend, raise effects, and eventually be consumed. This design provides strong isolation guarantees and enables fine-grained concurrency, but it also introduces subtle correctness concerns that are difficult to reason about informally.

Formal verification matters here because the failure modes are catastrophic and non-obvious. A double-spend bug in a transaction protocol means users lose funds. An effect-handling bug that leaks continuations could allow attackers to resume computations in unintended contexts. A lock ordering bug could deadlock the entire system. These are not hypothetical concerns; they are the kinds of bugs that have caused real financial losses in deployed blockchain systems. The Starstream TLA+ specification exists to catch these bugs before they reach production.

The specification models the protocol at the UTXO and transaction layer, not the bytecode execution layer. It captures the state machine of individual UTXOs, how transactions reserve and consume them, how effects propagate through coordination scripts, and how the global ledger maintains consistency under concurrent transaction execution. By model-checking this specification with TLC (the TLA+ model checker), we can systematically explore interleavings that would be impossible to test manually.

### 2. Why TLA+ (vs Coq, Isabelle, Alloy)

Choosing a formal methods tool involves tradeoffs. Coq and Isabelle are proof assistants that provide mechanized theorem proving. They can prove properties about infinite state spaces and establish universal guarantees. However, they require significant expertise to use, and proofs often take weeks or months to develop. For a protocol that is still evolving, this cost is prohibitive.

Alloy is a lightweight modeling language with automatic analysis, but it is designed for relational modeling rather than state machine exploration. It excels at finding bugs in data models but is less suited to temporal reasoning about system behavior over sequences of actions.

TLA+ occupies a middle ground. It is a state-based specification language with a model checker (TLC) that can exhaustively explore bounded state spaces. You write specifications that look like mathematical definitions, and TLC systematically explores all possible interleavings of actions to find invariant violations. The feedback loop is fast: you can write a spec in the morning and find bugs by afternoon. TLA+ is also particularly well-suited to concurrent systems, which is exactly what a multi-transaction blockchain protocol is.

The tradeoff is that TLC only explores bounded models. It cannot prove properties for arbitrary-sized systems. The Starstream spec uses bounds like `MAX_UTXOS = 3` and `MAX_PENDING_TXS = 2`. This is enough to find most concurrency bugs (which typically manifest with small numbers of interacting entities) but does not constitute a proof that the system is correct for all possible configurations. For Starstream, this is acceptable: the goal is to find bugs and build confidence, not to achieve formal proof.

### 3. The Scope of What This Specification Covers

The Starstream TLA+ specification covers the UTXO and transaction protocol layer. It models:

- UTXO lifecycle: creation, suspension at yield points, suspension waiting for effect handlers, reservation by transactions, execution within transaction context, and consumption
- Transaction phases: reservation of inputs, execution of coordination scripts, commitment or rollback
- Effect handling: raising effects from UTXO coroutines, handling effects in coordination scripts, resuming execution with handler results
- Ledger state: the set of live UTXOs, consumed UTXO IDs, locks held by pending transactions, transaction history
- Authorization: signature binding to transaction contents, owner-only spending

The specification does not model:

- Network communication or Byzantine fault tolerance
- Block propagation or consensus
- Smart contract bytecode execution (opcodes, gas, stack operations)
- Cryptographic primitives (signatures are abstract records, not actual crypto)
- ZK proof construction or verification (proofs are predicates, not circuits)

This scope is intentional. The UTXO/transaction layer is where the most subtle bugs live. Network and consensus concerns are largely orthogonal and can be modeled separately. Bytecode execution is a different verification target that requires different techniques (such as symbolic execution or denotational semantics).

### 4. The Concurrency Model Choice: Pessimistic Locking

The specification uses pessimistic locking as its concurrency model. When a transaction wants to use a set of UTXOs as inputs, it must first reserve (lock) all of them. If any UTXO is already locked by another transaction, the reservation fails and the transaction must abort or retry. Only after acquiring all locks can the transaction proceed to execution.

This is a conservative choice. An alternative is optimistic concurrency control, where transactions execute speculatively and validate their read-sets at commit time. Optimistic concurrency can provide higher throughput when conflicts are rare, but it is harder to reason about and introduces additional failure modes (speculative execution that gets rolled back). The pessimistic model exposes all the fundamental race conditions while being simpler to specify and verify.

The [interleavingTypes.md](../../interleavingTypes.md) design document describes both models and recommends the transactional interleaving state machine approach. The spec now includes **both**: a pessimistic locking model (`StarstreamSpec.tla`) and an optimistic-concurrency variant (`StarstreamSpecOptimistic.tla`) with explicit read/write sets and commit-time validation. The key insight is that both models share the same commit semantics: inputs are consumed atomically, outputs become visible atomically, and the observable ledger state is serializable.

### 5. How to Read This Document and Prerequisites

This document assumes familiarity with TLA+ syntax and basic concepts (state variables, actions, invariants, temporal operators). If you have not used TLA+ before, the official documentation and Lamport's "Specifying Systems" book are good starting points. You do not need expertise; basic comprehension of how TLA+ represents state machines is sufficient.

The document also assumes familiarity with UTXO-based transaction models (as in Bitcoin or Cardano) and basic blockchain concepts. Understanding of algebraic effects and coroutines is helpful but not required; the specification models these concepts at a level that does not require deep PL theory knowledge.

Code snippets in this document are taken directly from the specification modules. Line numbers refer to the actual files. When reading the specification itself, start with `StarstreamTypes.tla` for foundational definitions, then `StarstreamSpec.tla` for the top-level state machine, then `StarstreamInvariants.tla` for the properties being verified.

---

## Part II: Architectural Foundation

### 6. Module Dependency Structure

The Starstream TLA+ specification comprises 11 modules organized in a layered dependency structure:

```
StarstreamTypes.tla           (no dependencies - foundation)
    |
    +-- StarstreamFrame.tla   (extends Types)
    |       |
    |       +-- StarstreamUTXO.tla (extends Types, Frame)
    |       |
    |       +-- StarstreamEffects.tla (extends Types, Frame)
    |               |
    |               +-- StarstreamCoordination.tla (extends Types, Frame, UTXO, Effects)
    |
    +-- StarstreamAuth.tla (extends Types)
            |
            +-- StarstreamTransaction.tla (extends Types, Frame, UTXO, Effects, Coordination, Auth)
                    |
                    +-- StarstreamLedger.tla (extends all above)
                            |
                            +-- StarstreamSpec.tla (extends all above)
                                    |
                                    +-- StarstreamInvariants.tla (extends Spec, Auth)
                                            |
                                            +-- MC_Starstream.tla (extends Spec, Invariants)
```

Each module defines types, constructors, predicates, and operations for one conceptual layer. The dependency arrows indicate `EXTENDS` relationships. This layering means you can understand lower modules without reading higher ones, but not vice versa. The `MC_Starstream.tla` module and `Starstream.cfg` file configure model checking and exist outside the main logical hierarchy.

### 7. StarstreamTypes.tla: Constants, Enumerations, Token Bag Algebra

`StarstreamTypes.tla` is the foundation module. It defines:

**Model checking bounds** as constants that are instantiated by the configuration file:

```tla
CONSTANTS
    MAX_UTXOS,          \* Maximum UTXOs in ledger (e.g., 3)
    MAX_TX_INPUTS,      \* Maximum inputs per transaction (e.g., 2)
    MAX_TX_OUTPUTS,     \* Maximum outputs per transaction (e.g., 2)
    MAX_FRAME_VARS,     \* Maximum local variables in Frame (e.g., 4)
    MAX_PENDING_TXS,    \* Maximum concurrent pending transactions (e.g., 2)
    MAX_TOKEN_TOTAL,    \* Max per-asset total for overflow checks
    UTXO_ID_BOUND,      \* Maximum UTXO identifier value (e.g., 8)
    CHAIN_ID,           \* Chain identifier (prevents cross-chain replay)
    BLOCK_HEIGHT,       \* Block height (prevents cross-height replay)
    TOKEN_TYPES,        \* Set of token types (e.g., {"ADA", "NFT"})
    TOKEN_IDS           \* Set of token IDs (e.g., {1,2,3})
```

**Enumerations** for the various states and kinds used throughout the spec:

- `UTXOStates`: Created, Suspended_at_Yield, Suspended_at_Effect, Reserved, Executing, Consumed
- `EffectKinds`: Pure, Effectful, Runtime
- `EffectTags`: E1, E2, E3 (abstract tags for model checking)
- `CallTypes`: Query, Mutate, Consume
- `TxStates`: Idle, Reserve, Executing, Committing, Rollback, Committed, Failed
- `CoordPhases`: NotStarted, Gathering, Processing, Finalizing, Complete

**Token bag algebra** for per-asset accounting. Tokens are represented as nested functions from token type to token ID to quantity:

```tla
TokenBagType == [TOKEN_TYPES -> [TOKEN_IDS -> TokenQuantityRange]]

EmptyTokenBag == [t \in TOKEN_TYPES |-> [id \in TOKEN_IDS |-> 0]]

AddTokenBags(bag1, bag2) ==
    [t \in TOKEN_TYPES |->
        [id \in TOKEN_IDS |-> bag1[t][id] + bag2[t][id]]]
```

This per-asset representation is important for the balance invariants. A naive "total value" representation would conflate different token types and miss bugs where ADA is swapped for NFTs incorrectly.

### 8. StarstreamFrame.tla: Coroutine Frames, PC Semantics, Hash Integrity

A `Frame` represents the execution state of a UTXO's coroutine. It contains:

- `pc`: Program counter (0 = initial, -1 = terminated, positive = yield/effect point)
- `locals`: Local variable storage mapping variable names to datum values
- `methodId`: Which method is being executed
- `hash`: A computed hash of the other fields for integrity checking

The hash computation is modeled as a tuple rather than actual cryptography:

```tla
ComputeFrameHash(pc, locals, methodId) == <<pc, locals, methodId>>
```

This abstraction captures the essential property: the hash is a function of the frame contents. If anyone tampers with the frame, the hash will not match. The `IsFrame` predicate enforces this:

```tla
IsFrame(f) ==
    /\ IsValidPC(f.pc)
    /\ f.locals \in LocalsType
    /\ f.methodId \in MethodIdRange
    /\ f.hash = ComputeFrameHash(f.pc, f.locals, f.methodId)
```

Frame operations like `AdvancePC` and `SetLocal` call `Rehash`; `Resume` recomputes the hash directly. The `INV_FRAME_Integrity` invariant verifies that frame hashes remain consistent throughout execution.

**Implementation note:** Real systems must use collision-resistant hashing (e.g., SHA-256 or stronger) to prevent forged frames from passing integrity checks.

### 9. StarstreamAuth.tla: Content-Bound Signatures, Digest Structures

Authorization in Starstream requires that transaction signers prove they own the UTXOs being spent and that they are committing to specific transaction contents. `StarstreamAuth.tla` models this with content digests and signature records.

The signature binds the signer to the transaction contents via a hash:

```tla
TxContentsHash(tx) ==
    <<CHAIN_ID, BLOCK_HEIGHT, tx.id, tx.signer,
      TxInputsDigest(tx), TxOutputsDigest(tx),
      tx.readSet, tx.writeSet,
      TxCoordDigest(tx), TxProofsDigest(tx)>>
```

The digests include input UTXO IDs, output specifications, read/write sets, proof commitments, and coordination state. In the PTB-first model, the coordination digest commits to the PTB trace and cursor (`ptbIndex`) along with output specs and the effect stack. Legacy `pendingCalls`/`callIndex` are retained for backward compatibility but are not part of the digest. This binding prevents attacks where a malicious party reuses a signature with different inputs, outputs, or execution traces.

**Terminology note:** This document uses “hash” and “digest” interchangeably to refer to the same structured (non-cryptographic) commitment value in the model.

**Replay protection:** `TxContentsHash` also commits to `CHAIN_ID` and `BLOCK_HEIGHT` (modeled constants), which prevents cross-chain or cross-height replay in the model.

The `ValidSignature` predicate checks that the signature's claimed contents hash matches the actual transaction:

```tla
ValidSignature(sig, tx) ==
    /\ IsSignature(sig)
    /\ sig["owner"] = tx.signer
    /\ sig["txId"] = tx.id
    /\ sig["contentsHash"] = TxContentsHash(tx)
```

**Model-checking note:** `IsTxContentsHash` remains intentionally shallow, but it now checks the structure of all digest components (including PTB trace commitments) to avoid enumerating huge digest domains. The binding is enforced by equality with `TxContentsHash` in `ValidSignature`, not by full type membership.

Note that this models signatures as structured records, not cryptographic objects. TLA+ cannot verify cryptographic correctness; that is out of scope. What it can verify is that the protocol uses signatures correctly: checking ownership, binding to contents, and preventing replay.

### 10. StarstreamEffects.tla: Effect Records, Stack Operations, Continuation IDs

The effect system allows UTXO coroutines to raise effects that are handled by coordination scripts. An effect record contains:

```tla
EffectRecordSet ==
    [kind: EffectKinds,
     sourceUtxoId: UTXOIdRange,
     continuationId: ContinuationIdRange,
     tag: EffectTags,
     payload: DatumValues,
     handled: BOOLEAN,
     interfaceId: InterfaceIdRange,
     handlerStackId: 1..MAX_HANDLER_DEPTH,
     witLedgerKind: WitLedgerEffectKinds]
```

The `continuationId` is essential for correct resumption. When an effect is raised, the continuation ID identifies which coroutine context should receive the handler result. The `INV_EFFECT_ContinuationMatch` invariant (not directly named but implied by the effect handling logic) ensures that handlers resume the correct continuation.

Effects are now **interface-scoped**: `interfaceId` selects which handler stack should process the effect, and `handlerStackId` records the handler position. `witLedgerKind` mirrors the IVC interleaving prototype (resume/yield/burn/bind/unbind/new-utxo).

**Implementation note:** In production, `continuationId` should be a cryptographic commitment to the suspended frame (e.g., hash(frame || nonce)), not a predictable sequence. This prevents confused-deputy or collision attacks across contexts.

Effects are managed as a stack within coordination state:

```tla
PushEffect(stack, effect) == Append(stack, effect)
PopEffect(stack) == IF Len(stack) = 0 THEN stack ELSE SubSeq(stack, 1, Len(stack) - 1)
PeekEffect(stack) == IF Len(stack) = 0 THEN NULL ELSE stack[Len(stack)]
```

The stack semantics (LIFO ordering) matter for nested effects. If a handler raises another effect, the inner effect must be handled before the outer one can resume. The `NoDuplicatePendingEffects` predicate prevents multiple unhandled effects from the same UTXO.

### 11. StarstreamUTXO.tla: The 6-State UTXO Lifecycle Machine

The UTXO state machine is the heart of the specification. A UTXO record contains:

```tla
UTXORecordSet ==
    [id: UTXOIdRange,
     state: UTXOStates,
     frame: FrameSet,
     datum: DatumValues,
     tokens: TokenBagType,
     contractId: ContractIds,
     owner: OwnerAddrs,
     lockedBy: TxIdRange \cup {NO_TX}]
```

The six states form a lifecycle:

1. **Created**: Initial state after UTXO construction. Frame is at PC 0.
2. **Suspended_at_Yield**: Normal suspended state. Can be queried, reserved, or resumed.
3. **Suspended_at_Effect**: Waiting for an effect handler. Cannot be reserved until effect is handled.
4. **Reserved**: Locked by a pending transaction. Cannot be used by other transactions.
5. **Executing**: Running within transaction context. State transitions during coordination.
6. **Consumed**: Final state. The UTXO has been spent and can never be used again.

During execution, inputs move `Reserved -> Executing`. If an input raises an effect, it transitions to
`Suspended_at_Effect` (still locked by the same transaction) until the handler resumes it back to
`Executing`.

The state transition operators are pure functions that update UTXO records:

```tla
ReserveUTXO(u, txId) ==
    [u EXCEPT
        !.state = "Reserved",
        !.lockedBy = txId]

ConsumeUTXO(u) ==
    [u EXCEPT
        !.state = "Consumed",
        !.frame = Terminate(u.frame)]
```

The `lockedBy` field implements pessimistic locking. When a transaction reserves a UTXO, it sets `lockedBy` to its transaction ID. The `CanReserve` predicate checks that the UTXO is in the correct state and not already locked:

```tla
CanReserve(u) == /\ IsUTXORecord(u) /\ u.state = "Suspended_at_Yield" /\ u.lockedBy = NO_TX
```

---

## Part III: Transaction and Ledger Semantics

### 12. StarstreamCoordination.tla: Method Calls, Script Phases, Effect Integration

Coordination scripts orchestrate the execution of transactions. In the PTB-first model, coordination is validated against a PTB trace; the coordination state tracks the trace and a cursor alongside legacy call sequencing fields. The coordination state tracks execution progress:

```tla
CoordinationStateSet ==
    [phase: CoordPhases,
     inputUtxos: SUBSET UTXOIdRange,
     pendingCalls: Seq(MethodCallRecordSet),
     callIndex: 0..10,
     outputSpecs: Seq([datum: DatumValues, tokens: TokenBagType, contract: ContractIds, owner: OwnerAddrs]),
     effectStack: Seq(EffectRecordSet),
     handlerStacks: [InterfaceIdRange -> Seq(HandlerRecordSet)],
     installedHandlers: SUBSET HandlerRecordSet,
     ptbTrace: PTBTrace,
     ptbIndex: 0..MAX_TX_INPUTS,
     ivcConfig: IVCStateConfigType]
```

The phases are:

1. **NotStarted**: Initial state before coordination begins
2. **Gathering**: Collecting input UTXOs for the transaction
3. **Processing**: Executing method calls on inputs, handling effects
4. **Finalizing**: Creating output UTXOs from specifications
5. **Complete**: All calls executed, all effects handled, outputs ready

Method calls are legacy records specifying the operation:

```tla
MethodCallRecordSet ==
    [callType: CallTypes,       \* Query, Mutate, or Consume
     targetUtxo: UTXOIdRange,
     methodId: MethodIdRange,
     args: DatumValues,
     executed: BOOLEAN,
     result: DatumValues \cup {NULL}]
```

PTB traces are now the authoritative coordination inputs. The legacy call sequence fields remain for backward compatibility but are not committed in the transaction digest. During PTB validation, each PTB event step must preserve the session protocol (`SessionProtocolValid`), enforcing handler duality and effect tag matching throughout execution.

The `ExecuteCallOnUTXO` operator performs the appropriate state update based on call type:

```tla
ExecuteCallOnUTXO(call, utxo) ==
    CASE call.callType = "Query" -> ExecuteQuery(utxo)
      [] call.callType = "Mutate" -> ExecuteMutation(utxo, call.args, utxo.frame.pc + 1)
      [] call.callType = "Consume" -> utxo
      [] OTHER -> utxo
```

Note that `Consume` calls do not immediately consume the UTXO; actual consumption happens at transaction commit.

Coordination now also tracks **per-interface handler stacks**. Handlers can be installed/uninstalled during execution, and interface-scoped effects are routed to the top handler for that interface. The `installedHandlers` set is maintained as a summary of all handlers present in `handlerStacks`, and `ivcConfig` captures the IVC activation state for interleaving.

### 13. StarstreamTransaction.tla: The Multi-Phase Transaction Model

Transactions follow a multi-phase lifecycle: Reserve, Execute, **Committing/Rollback**, and terminal states (Committed or Failed). The transaction record captures all relevant state:

```tla
TransactionRecordSet ==
    [id: TxIdRange,
     signer: OwnerAddrs,
     signature: SignatureType,
     inputs: SUBSET UTXORecordSet,
     coordination: CoordinationStateSet,
     outputs: SUBSET UTXORecordSet,
     readSet: SUBSET UTXOIdRange,
     readSnapshot: SUBSET UTXORecordSet,
     writeSet: SUBSET UTXOIdRange,
     phase: TxStates,
     result: DatumValues \cup {NULL},
     proofCommitments: SUBSET ProofCommitmentType,
     proofPhase: ProofPhases]
```

The `readSet`/`writeSet` fields support optimistic concurrency validation, while `proofCommitments`/`proofPhase` track proof lifecycle. `SignTx` recomputes the signature after any state change, so signatures bind to these fields (via `TxContentsHash`).

The phase transitions are:

- **Idle -> Reserve**: Transaction specifies inputs and acquires locks
- **Reserve -> Executing**: All locks acquired, begin coordination execution
- **Executing -> Committing**: Coordination complete, balance validated, ready to commit (`BeginCommit`)
- **Executing -> Rollback**: Something went wrong, release locks and abort (`StartRollback`)
- **Committing -> Committed**: Success, inputs consumed, outputs published
- **Rollback -> Failed**: Failure recorded, no state changes to ledger

The signature is recomputed after each state change via the `SignTx` wrapper:

```tla
SignTx(tx) ==
    [tx EXCEPT !.signature = MakeSignature(tx.signer, tx.id, TxContentsHash(tx))]
```

This ensures that the signature always reflects the current transaction contents. The balance preservation check happens at commit time:

```tla
BalancePreserved(tx) ==
    TokenBagsEqual(SumInputTokens(tx), SumOutputTokens(tx))
```

### 14. StarstreamLedger.tla: Global State, Lock Management, Multi-Transaction Concurrency

The ledger is the global state of the system:

```tla
LedgerStateSet ==
    [utxoSet: SUBSET UTXORecordSet,
     consumedSet: SUBSET UTXOIdRange,
     lockedSet: SUBSET UTXOIdRange,
     nextUtxoId: UTXOIdRange \cup {UTXO_ID_BOUND + 1},
     nextTxId: TxIdRange \cup {UTXO_ID_BOUND + 1},
     pendingTxs: SUBSET TransactionRecordSet,
     txHistory: Seq(TransactionRecordSet),
     proofStore: SUBSET ProofCommitmentType,
     activeProofs: SUBSET ProcessIdRange]
```

Key fields:

- `utxoSet`: All live (non-consumed) UTXOs
- `consumedSet`: IDs of consumed UTXOs (for double-spend prevention)
- `lockedSet`: IDs of UTXOs currently locked by pending transactions
- `pendingTxs`: Set of in-flight transactions (plural, enabling concurrency)
- `txHistory`: Sequence of completed transactions for invariant checking
- `proofStore`: Global proof commitments (IVC steps, accumulators, witnesses)
- `activeProofs`: Process IDs with active proof commitments

The lock management operations ensure consistency:

```tla
ReserveUTXOsInSet(utxoSet, inputIds, txId) ==
    {IF u.id \in inputIds THEN ReserveUTXO(u, txId) ELSE u : u \in utxoSet}
```

The commit operation atomically consumes inputs and publishes outputs:

```tla
CommitTxInLedger(ledger, txId) ==
    LET tx == GetPendingTx(ledger, txId)
        committedTx == CommitTransaction(tx)
        inputIds == {u.id : u \in tx.inputs}
        newUtxoSet == {u \in ledger.utxoSet : u.id \notin inputIds} \cup tx.outputs
    IN [ledger EXCEPT
        !.utxoSet = newUtxoSet,
        !.consumedSet = @ \cup inputIds,
        !.lockedSet = @ \ inputIds,
        !.pendingTxs = @ \ {tx},
        !.txHistory = Append(@, committedTx)]
```

### 14.5 IEUTxO chunk semantics (draft)

The ledger module now includes an **IEUTxO-style** view of transaction validity and chunk validity for sequences of transactions. This is used to state serializability-oriented invariants over committed history:

- `IEUTxOTxValid(ledger, tx)` checks input/output shape, ownership validation, and freshness against the ledger.
- `ChunkValid(txs)` checks pairwise input/output disjointness and ensures inputs that reference earlier outputs validate against those outputs.
- `FilterCommitted` extracts committed transactions from `txHistory` so we can check `ChunkValid` over committed history (`INV_IEUTXO_CommittedHistoryChunk`).

These helpers are intended to support a future serializable-trace refinement mapping (Section 36).

### 15. StarstreamSpec.tla: Init, Next Relation, Fairness Conditions

`StarstreamSpec.tla` is the top-level specification that defines the state machine. It declares the state variable:

```tla
VARIABLES
    ledger

vars == <<ledger>>
```

The initial state creates a genesis ledger with sample UTXOs:

```tla
Init ==
    /\ ledger = GenesisLedger(InitialUTXOs)
```

The `Next` relation is a disjunction of all possible actions:

```tla
Next ==
    \/ \E c \in SampleContracts, o \in SampleOwners, d \in SampleDatums, t \in SampleTokenBags :
        CreateUTXO(c, o, d, t)
    \/ \E ids \in SUBSET {u.id : u \in ledger.utxoSet}, s \in SampleOwners :
        ReserveTx(ids, s)
    \/ \E txId \in TxIdRange : BeginExecute(txId)
    \/ \E txId \in TxIdRange : BeginCommit(txId)
    \/ \E txId \in TxIdRange : CommitTx(txId)
    \/ \E txId \in TxIdRange, reason \in DatumValues : StartRollback(txId, reason)
    \/ \E txId \in TxIdRange : FinishRollback(txId)
    \* ... and other actions
```

The spec also includes **adversarial actions** (`InjectInvalidTx`, `RejectInvalidTx`) to model malformed transactions and explicit rejection paths.

Each action has guards (preconditions) that must be satisfied. For example, `BeginCommit` requires:

```tla
BeginCommit(txId) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ LET tx == GetPendingTx(ledger, txId)
       IN /\ IsComplete(tx.coordination)
          /\ BalancePreserved(tx)
          /\ \A u \in tx.inputs : GetUTXO(ledger, u.id).state = "Reserved"
          /\ \A u \in tx.inputs : GetUTXO(ledger, u.id).lockedBy = txId
          /\ ValidSignature(tx.signature, tx)
          /\ InputsOwnedBySigner(tx)
          /\ AllTxProofsVerified(tx)
          /\ ledger' = UpdatePendingTx(ledger, txId, BeginCommitting(tx))
```

Commit is also gated on proof verification (`AllTxProofsVerified`), so interleaving proofs must be present and verified before the ledger will accept the transaction.

Fairness conditions ensure liveness properties can be checked:

```tla
WeakFairness ==
    /\ WF_vars(\E txId \in TxIdRange : BeginCommit(txId))
    /\ WF_vars(\E txId \in TxIdRange : CommitTx(txId))
    /\ WF_vars(\E txId \in TxIdRange, reason \in DatumValues : StartRollback(txId, reason))
    /\ WF_vars(\E txId \in TxIdRange : FinishRollback(txId))
```

Weak fairness on `BeginCommit`, `CommitTx`, and `FinishRollback` means that if these actions are continuously enabled, they will eventually be taken. This prevents TLC from finding spurious liveness violations where transactions stall indefinitely.

For effect-handling liveness, the spec also defines:

```tla
StrongFairness ==
    /\ SF_vars(\E txId \in TxIdRange, result \in DatumValues : HandleTxEffect(txId, result))
```

`HandleTxEffect` corresponds to the PTB Resume event; strong fairness ensures that
pending effects are not starved. Use `StrongFairSpec` when checking
`LIVE_EffectsEventuallyHandled`.

### 16. MC_Starstream.tla and Starstream.cfg: Model Checking Configuration

`MC_Starstream.tla` provides model checking configuration:

```tla
MC_MAX_UTXOS == 3
MC_MAX_TX_INPUTS == 2
MC_MAX_TX_OUTPUTS == 2
MC_MAX_FRAME_VARS == 4
MC_MAX_PENDING_TXS == 2
MC_MAX_TOKEN_TOTAL == 4
MC_UTXO_ID_BOUND == 8
MC_CHAIN_ID == 1
MC_BLOCK_HEIGHT == 0
MC_TOKEN_TYPES == {"ADA", "NFT"}
MC_TOKEN_IDS == {1, 2, 3}
MC_MAX_EFFECT_DEPTH == MC_MAX_TX_INPUTS
```

The state constraint bounds the state space:

```tla
MC_StateConstraint ==
    /\ Cardinality(ledger.utxoSet) <= MC_MAX_UTXOS
    /\ Cardinality(ledger.consumedSet) <= MC_UTXO_ID_BOUND
    /\ Cardinality(ledger.pendingTxs) <= MC_MAX_PENDING_TXS
    \* ... other constraints
```

`Starstream.cfg` is the TLC configuration file that ties everything together:

```
SPECIFICATION MC_Spec
CONSTANTS
    MAX_UTXOS = 3
    MAX_TX_INPUTS = 2
    ...
CONSTRAINT MC_StateConstraint
INVARIANTS
    MC_TypeOK
    MC_NoDoubleSpend
    MC_BalancePreserved
    MC_PendingInputsNotConsumed
    MC_EffectSourceSuspended
    MC_EffectContinuationMatch
    MC_Safety
    ...
CHECK_DEADLOCK FALSE
```

The `CHECK_DEADLOCK FALSE` setting is intentional. The specification allows stuttering (no state change), so TLC should not report deadlocks when all actions are disabled.

---

## Part IV: What the Specification Proves

### 17. Type Invariants: Structural Well-Formedness

Type invariants verify that all records conform to their expected structure throughout execution. The top-level type invariant is:

```tla
INV_TYPE_All ==
    /\ TypeOK
    /\ INV_TYPE_LedgerWellTyped
    /\ INV_TYPE_FramesWellTyped
    /\ INV_TYPE_TokenBagsWellTyped
    /\ INV_TYPE_PendingTxWellTyped
```

`INV_TYPE_LedgerWellTyped` checks that the ledger satisfies `IsValidLedger`:

```tla
IsValidLedger(ledger) ==
    /\ \A u \in ledger.utxoSet : IsUTXORecord(u)
    /\ ledger.nextUtxoId <= UTXO_ID_BOUND + 1
    /\ ledger.nextTxId <= UTXO_ID_BOUND + 1
    /\ \A tx \in ledger.pendingTxs : IsTransactionRecord(tx)
```

`INV_TYPE_FramesWellTyped` ensures all UTXO frames pass the `IsFrame` predicate, including the hash integrity check. `INV_TYPE_TokenBagsWellTyped` verifies token bags have the correct structure.

These invariants catch bugs where operations produce malformed records. They are the first line of defense and should never be violated if the specification is correctly written.

### 18. Authorization Invariants: Signature Binding, Owner-Only Spending

Authorization invariants prevent unauthorized spending:

```tla
INV_AUTH_ValidSpend ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsCommittedTx(tx) => ValidSignature(tx.signature, tx)

INV_AUTH_OwnerOnly ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsCommittedTx(tx) => InputsOwnedBySigner(tx)
```

`INV_AUTH_ValidSpend` ensures that every committed transaction has a valid signature over its contents. The signature binding to `TxContentsHash` prevents replay attacks: a signature for one transaction cannot be reused for a different transaction because the contents hash would not match.

`INV_AUTH_OwnerOnly` ensures that transaction signers can only spend UTXOs they own. Combined with valid signature checking, this prevents unauthorized parties from consuming others' assets.

### 19. Balance Invariants: Token Conservation, Per-Asset Accounting, NFT Uniqueness

Token bag algebra is defined in Section 7; this section focuses on how it is used for balance checks.

Balance invariants ensure tokens are neither created nor destroyed (except through explicit minting/burning, not modeled here):

```tla
INV_BALANCE_TxPreserved ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsCommittedTx(tx) => BalancePreserved(tx)
```

The `BalancePreserved` predicate compares input and output token bags:

```tla
BalancePreserved(tx) ==
    TokenBagsEqual(SumInputTokens(tx), SumOutputTokens(tx))
```

This is checked per token type and per token ID, not as a single total. If a transaction had 2 ADA and 1 NFT as inputs, it must have 2 ADA and 1 NFT as outputs. You cannot swap one for the other.

NFT uniqueness is enforced separately:

```tla
INV_BALANCE_NFTUnique ==
    \A id \in TOKEN_IDS :
        Cardinality({u \in ledger.utxoSet : u.tokens["NFT"][id] > 0}) <= 1
```

This ensures that each NFT ID appears in at most one UTXO at any time. Duplicating NFTs would violate their fundamental property of non-fungibility.

To prevent duplication races during finalization, pending outputs are constrained:

```tla
INV_BALANCE_PendingOutputsNoNFTDuplication ==
    \A tx \in ledger.pendingTxs :
        IsComplete(tx.coordination) =>
            \A id \in TOKEN_IDS :
                LET outputsWithNft ==
                        {u \in tx.outputs : u.tokens["NFT"][id] > 0}
                    otherUtxos ==
                        {u \in ledger.utxoSet :
                            /\ u.id \notin {i.id : i \in tx.inputs}
                            /\ u.tokens["NFT"][id] > 0}
                IN /\ Cardinality(outputsWithNft) <= 1
                   /\ otherUtxos = {}
```

To ensure arithmetic stays within safe bounds, we also enforce a per-asset overflow check:

```tla
INV_BALANCE_NoOverflow ==
    /\ \A tx \in ledger.pendingTxs :
        \A t \in TOKEN_TYPES : \A id \in TOKEN_IDS :
            /\ SumInputTokens(tx)[t][id] <= MAX_TOKEN_TOTAL
            /\ SumOutputTokens(tx)[t][id] <= MAX_TOKEN_TOTAL
    /\ \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        \A t \in TOKEN_TYPES : \A id \in TOKEN_IDS :
            /\ SumInputTokens(tx)[t][id] <= MAX_TOKEN_TOTAL
            /\ SumOutputTokens(tx)[t][id] <= MAX_TOKEN_TOTAL
```

This models **checked arithmetic**: any transaction whose per-asset totals exceed `MAX_TOKEN_TOTAL` should be rejected in the real system.

### 20. Linear Consumption Invariants: No Double-Spend, Exactly-Once Semantics

Linear consumption is the most important safety property. Each UTXO must be consumed at most once, and consumed UTXOs must never reappear:

```tla
INV_LINEAR_NoDoubleSpend ==
    {u.id : u \in ledger.utxoSet} \cap ledger.consumedSet = {}

INV_LINEAR_ConsumedTracked ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsCommittedTx(tx) => \A u \in tx.inputs : u.id \in ledger.consumedSet

INV_LINEAR_UniqueActiveIds ==
    \A u1, u2 \in ledger.utxoSet : u1 # u2 => u1.id # u2.id
```

`INV_LINEAR_NoDoubleSpend` is the core double-spend prevention: no UTXO ID can be both live (in `utxoSet`) and consumed (in `consumedSet`). `INV_LINEAR_ConsumedTracked` ensures that when a transaction commits, its input IDs are recorded in `consumedSet`. `INV_LINEAR_UniqueActiveIds` ensures no two live UTXOs share an ID.

Additionally, concurrent transactions cannot lock the same UTXO:

```tla
INV_LINEAR_NoDuplication ==
    \A tx1, tx2 \in ledger.pendingTxs :
        (tx1 # tx2) =>
            ({u.id : u \in tx1.inputs} \cap {u.id : u \in tx2.inputs} = {})
```

We also require pending transactions to avoid already-consumed inputs:

```tla
INV_LINEAR_PendingInputsNotConsumed ==
    \A tx \in ledger.pendingTxs :
        ({u.id : u \in tx.inputs} \cap ledger.consumedSet = {})
```

### 21. Lock/Reservation Invariants: Exclusive Locking, Consistency

Lock invariants ensure the pessimistic locking mechanism works correctly:

```tla
INV_LOCK_Exclusive ==
    \A u \in ledger.utxoSet :
        u.lockedBy = NO_TX \/ (\E tx \in ledger.pendingTxs : tx.id = u.lockedBy)

INV_LOCK_ValidReservation ==
    \A u \in ledger.utxoSet :
        u.lockedBy # NO_TX => u.state \in {"Reserved", "Executing", "Suspended_at_Effect"}

INV_LOCK_ConsistentSet ==
    LockedSetConsistent(ledger)

INV_LOCK_AtomicRelease ==
    \A u \in ledger.utxoSet :
        u.state \in {"Reserved", "Executing", "Suspended_at_Effect"} => u.lockedBy # NO_TX
```

`INV_LOCK_Exclusive` ensures that if a UTXO is locked, the locking transaction actually exists. `INV_LOCK_ValidReservation` ensures locked UTXOs are in appropriate states. `INV_LOCK_ConsistentSet` verifies the `lockedSet` field accurately reflects which UTXOs have non-zero `lockedBy` values.

`INV_LOCK_AtomicRelease` ensures lock release is coupled with a state change (no “unlocked Reserved/Executing” UTXOs).

These invariants prevent subtle bugs where locks are acquired but not properly tracked, or where transactions believe they hold locks they do not actually have.

### 22. Effect Handling Invariants: Continuation Matching, Stack Ordering

Effect invariants ensure the algebraic effect system behaves correctly:

```tla
INV_EFFECT_MustBeHandled ==
    \A tx \in ledger.pendingTxs :
        IsComplete(tx.coordination) => ~HasPendingEffects(tx.coordination)

INV_EFFECT_NoOrphans ==
    \A tx \in ledger.pendingTxs :
        \A e \in FcnRange(tx.coordination.effectStack) :
            e["sourceUtxoId"] \in {u["id"] : u \in tx.inputs}
```

`INV_EFFECT_MustBeHandled` ensures transactions cannot complete with unhandled effects. Effects must either be handled or cause the transaction to abort. `INV_EFFECT_NoOrphans` ensures all effects come from UTXOs that are actually inputs to the transaction.

Two additional effect invariants close execution gaps:

```tla
INV_EFFECT_SourceSuspended ==
    \A tx \in ledger.pendingTxs :
        \A e \in PendingEffects(tx.coordination.effectStack) :
            /\ UTXOExistsInLedger(ledger, e["sourceUtxoId"])
            /\ LET u == GetUTXO(ledger, e["sourceUtxoId"])
               IN /\ u.state = "Suspended_at_Effect"
                  /\ u.lockedBy = tx.id

INV_EFFECT_ContinuationMatch ==
    \A tx \in ledger.pendingTxs :
        \A e \in PendingEffects(tx.coordination.effectStack) :
            /\ UTXOExistsInLedger(ledger, e["sourceUtxoId"])
            /\ LET u == GetUTXO(ledger, e["sourceUtxoId"])
               IN e["continuationId"] = u.frame.pc

INV_EFFECT_StackDepthBounded ==
    \A tx \in ledger.pendingTxs :
        Len(tx.coordination.effectStack) <= MAX_EFFECT_DEPTH
```

These ensure that pending effects are tied to a suspended input UTXO, the continuation ID matches
the UTXO’s suspension point, and the effect stack stays within a bounded depth.

The `NoDuplicatePendingEffects` predicate in `StarstreamEffects.tla` prevents multiple pending effects from the same UTXO:

```tla
NoDuplicatePendingEffects(stack) ==
    \A i, j \in 1..Len(stack) :
        (i # j /\ ~stack[i]["handled"] /\ ~stack[j]["handled"])
        => stack[i]["sourceUtxoId"] # stack[j]["sourceUtxoId"]
```

### 23. Frame Integrity and Rollback Invariants

Frame integrity ensures coroutine state cannot be tampered with:

```tla
INV_FRAME_Integrity ==
    \A u \in ledger.utxoSet : u.frame.hash = ComputeFrameHash(u.frame.pc, u.frame.locals, u.frame.methodId)
```

This catches bugs where frame fields are modified without updating the hash, which would indicate either a specification bug or an attack.

Rollback invariants ensure failed transactions do not leak state:

```tla
INV_ROLLBACK_NoLeak ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsFailedTx(tx) =>
            /\ {u.id : u \in tx.outputs} \cap {u.id : u \in ledger.utxoSet} = {}
            /\ {u.id : u \in tx.inputs} \cap ledger.consumedSet = {}
```

If a transaction fails, its outputs must not appear in the live UTXO set, and its inputs must not be marked as consumed. The ledger state after rollback should be as if the transaction never happened (except for lock release).

---

## Part V: What the Specification Does NOT Prove

### 23.5 Security Model (in-scope vs out-of-scope)

**In scope (modeled / checked):**
- Double-spend prevention, unique active IDs
- Token conservation and NFT uniqueness (including pending output checks)
- Lock correctness and atomic lock release
- Effect handling completeness and continuation matching
- Authorization: signatures must match transaction contents; inputs owned by signer
- Adversarial malformed transactions (invalid signatures / wrong owner) are rejected

**Out of scope (implementation must handle):**
- Cryptographic soundness (hash collisions, signature malleability)
- Network/consensus ordering and MEV
- Gas/execution costs and DoS limits
- Oracles, price feeds, and economic attacks
- Cross-chain replay (beyond the modeled chain context)

### 24. Cryptographic Primitives

The specification models signatures as structured records with content hashes, not as actual cryptographic objects. The `MakeSignature` function simply constructs a record:

```tla
MakeSignature(owner, txId, contentsHash) ==
    [owner |-> owner, txId |-> txId, contentsHash |-> contentsHash]
```

There is no private key, no signing algorithm, no verification algorithm. The `ValidSignature` predicate checks structural properties (owner matches, contents hash matches) but does not verify any cryptographic computation.

This means the specification cannot catch bugs in signature implementation, key management, or cryptographic algorithm choice. It assumes signatures work correctly and verifies that the protocol uses them correctly. Cryptographic correctness must be established through other means (library audits, formal cryptographic proofs, hardware security modules).

### 25. Network and Consensus Layer

The specification has no network. There are no nodes, no message passing, no Byzantine fault tolerance, no leader election, no block propagation. The ledger is a single global state variable updated atomically by actions.

In a real blockchain, transactions arrive at different nodes at different times, nodes may disagree about transaction ordering, and malicious nodes may attempt to fork the chain. None of this is modeled. The specification assumes a single consistent view of the ledger.

This is appropriate for the protocol layer being modeled. Network and consensus concerns are largely orthogonal: if the UTXO/transaction protocol is correct, then a correct consensus mechanism will maintain correctness; if the protocol has bugs, no consensus mechanism can fix them. The two layers should be verified separately.

### 26. Smart Contract Bytecode Execution

The specification does not model bytecode execution. There are no opcodes, no stack operations, no gas metering, no memory allocation. Method calls are abstract operations that update UTXO state according to call type (Query, Mutate, Consume).

The `ExecuteCallOnUTXO` operator is a placeholder:

```tla
ExecuteCallOnUTXO(call, utxo) ==
    CASE call.callType = "Query" -> ExecuteQuery(utxo)
      [] call.callType = "Mutate" -> ExecuteMutation(utxo, call.args, utxo.frame.pc + 1)
      [] call.callType = "Consume" -> utxo
      [] OTHER -> utxo
```

Real execution would involve interpreting bytecode, managing execution context, handling errors, and computing results. The specification abstracts all of this into "the call succeeds with some result." Bytecode execution correctness must be verified separately, likely through symbolic execution or denotational semantics of the VM.

### 26.5 Adversarial Inputs (Partially Modeled)

The spec includes **adversarial actions** (`InjectInvalidTx`, `RejectInvalidTx`) to model malformed transactions with invalid signatures or wrong owners. This lets TLC explore scenarios where invalid inputs exist and must be rejected before commit.

| Action | Malformation injected | Expected handling | Where it is checked |
|--------|------------------------|-------------------|---------------------|
| `InjectInvalidTx` | Wrong-owner signature (sig.owner ≠ signer) | Must not reach commit | `ValidSignature`, `InputsOwnedBySigner` guards in `BeginCommit` |
| `RejectInvalidTx` | Removes pending tx with invalid sig/owner | Abort tx and release locks | `RejectInvalidTx` action + `INV_AUTH_*` invariants |

What is still **not modeled**:
- Parser bugs or malformed serialization
- Cryptographic breaks (forged signatures)
- Consensus-layer acceptance rules

### 27. Proof System Soundness

The specification **does** model proof commitments and their lifecycle, but it does **not** verify cryptographic soundness. Proofs are abstract records with a `commitmentHash`, verification key, and phase; they can be attached to transactions and stored in the ledger's `proofStore`.

Commit is gated on proof verification:

- `BeginCommit` / `CommitTx` require `AllTxProofsVerified(tx)`
- Invariants enforce that committed transactions only appear if their proofs are verified

What remains out of scope:

- ZK circuit correctness (soundness/completeness)
- Cryptographic binding between proof and execution
- Trusted setup / key management assumptions

Those properties must be validated with cryptographic tooling (Circom, Halo2, etc.) and audits.

---

## Part VI: How Engineers Can Use This Specification

### 28. Running TLC Model Checker

To run the model checker, you need TLA+ tools installed. The command line invocation is:

```bash
# Syntax check only (SANY)
java -cp tla2tools.jar tla2sany.SANY StarstreamSpec.tla

# Model check with default configuration
java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg

# Model check with multiple worker threads
java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg -workers 4
```

Download `tla2tools.jar` (and/or the Toolbox) from the TLA+ releases page and place it alongside `StarstreamSpec.tla` (or provide its full path in the command).

TLC will explore the state space defined by the initial state and Next relation, checking invariants at each state. Progress is reported as states explored and distinct states found. A typical run with the default bounds might explore tens of thousands of states.

**Proof hash bound:** Proof generation enumerates `SampleFrameHashes` (a small set of representative frame hashes) instead of the full `FrameHashRange` to avoid state explosion. If you need broader coverage, expand `SampleFrameHashes` carefully.

For liveness checking, modify `Starstream.cfg` to use `MC_FairSpec` and uncomment the `PROPERTIES` section. Liveness checking is more expensive and may require tighter bounds.

### 28.5 Complete workflow example (end-to-end)

1. **Edit** the spec (e.g., add a new invariant).
2. **Parse check**:
   ```bash
   java -cp tla2tools.jar tla2sany.SANY StarstreamSpec.tla
   ```
3. **Type-check only** (fast sanity):
   - Temporarily set `INVARIANTS` to `MC_TypeOK` in `Starstream.cfg`.
4. **Run safety**:
   ```bash
   java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg
   ```
5. **If failure**: read the trace, isolate the failing invariant, and rerun with just that invariant.
6. **Fix + rerun** until clean.

### 29. Interpreting Counterexample Traces

When TLC finds an invariant violation, it reports a counterexample trace: a sequence of states from initial to the violating state, with the action taken at each step. For example:

```
Error: Invariant MC_NoDoubleSpend is violated.
State 1: ledger = [utxoSet |-> {...}, consumedSet |-> {}, ...]
State 2: (ReserveTx) ledger = [utxoSet |-> {...}, ...]
State 3: (CommitTx) ledger = [utxoSet |-> {...}, consumedSet |-> {1}, ...]
State 4: (ReserveTx) ledger = ...
```

To interpret the trace:

1. Identify which action led to the violation (usually the last action before the invariant fails)
2. Examine the precondition of that action: why was it enabled when it should not have been?
3. Examine the postcondition: what state change violated the invariant?
4. Trace backwards to understand how the system reached that state

Common causes of violations:

- Missing guards in action definitions (an action is enabled when it should be blocked)
- Incorrect state updates (a field is not updated correctly)
- Missing invariant checks (the invariant is too weak)
- Model design bugs (the specification does not accurately reflect intended semantics)

### 30. Adding New Invariants

To add a new invariant:

1. Define it in `StarstreamInvariants.tla` following the naming convention (`INV_CATEGORY_Name`)
2. Add it to the appropriate combined invariant (e.g., `INV_Safety`)
3. Create a model-checking alias in `MC_Starstream.tla` (e.g., `MC_NewInvariant == INV_CATEGORY_Name`)
4. Add the alias to the `INVARIANTS` section of `Starstream.cfg`
5. Run TLC to verify the invariant holds

Example of adding a new invariant for token non-negativity:

```tla
\* In StarstreamInvariants.tla
INV_ATK_NoNegativeTokens ==
    \A u \in ledger.utxoSet :
        \A t \in TOKEN_TYPES : \A id \in TOKEN_IDS : u.tokens[t][id] >= 0
```

If the new invariant fails, either the invariant is wrong (too strong) or there is a bug in the specification.

### 31. Adding New Actions or States

To extend the specification with new functionality:

1. Define new constants/types in `StarstreamTypes.tla` if needed
2. Add new record fields or constructors in the appropriate module
3. Define new action(s) in `StarstreamSpec.tla` with appropriate guards
4. Add the action to the `Next` disjunction
5. Update invariants to account for the new state/action
6. Run TLC to verify existing invariants still hold

For example, to add a "partial reservation" feature:

1. Add a new UTXO state `PartiallyReserved` in `StarstreamTypes.tla`
2. Add a `partialLocks` field to transaction records
3. Define `PartialReserve` and `CompleteReserve` actions
4. Update lock invariants to handle partial locks
5. Verify no double-spend is possible with partial reservations

Be conservative. Adding features can introduce subtle bugs that only manifest in specific interleavings.

### 32. Performance Tuning

TLC performance depends on state space size, which grows exponentially with bound values. Strategies for managing performance:

**Reduce bounds**: Smaller values for `MAX_UTXOS`, `MAX_PENDING_TXS`, etc. reduce state space. Many bugs manifest with small values (2-3 concurrent transactions is enough to find most race conditions).

**State constraints**: The `MC_StateConstraint` predicate limits exploration. Tighter constraints mean faster checking at the cost of reduced coverage:

```tla
MC_StateConstraint ==
    /\ Len(ledger.txHistory) <= 3  \* Limit history length
    /\ Cardinality(ledger.pendingTxs) <= 2  \* Limit concurrent txs
```

**Symmetry sets**: If token types or owners are interchangeable, symmetry can reduce state space. Uncomment in `Starstream.cfg`:

```
SYMMETRY TokenTypeSymmetry
```

**Worker threads**: TLC parallelizes well. Use `-workers N` where N is the number of CPU cores.

**Simulation mode**: For very large state spaces, TLC can run in simulation mode, randomly sampling traces instead of exhaustively exploring. This is less thorough but can find bugs faster:

```bash
java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg -simulate
```

---

## Part VII: Open Problems and Future Work

### 33. Optimistic Concurrency Variant

The spec now includes an optimistic variant (`StarstreamSpecOptimistic.tla`) alongside the pessimistic model. It:

- Executes speculatively without locking inputs
- Tracks explicit `readSet` / `writeSet`
- Validates read-set stability and output freshness at commit
- Aborts if validation fails

This model can provide higher throughput when conflicts are rare (which is common with UTXO disjointness). The challenge is specifying correct validation semantics and ensuring serializability.

The [interleavingTypes.md](../../interleavingTypes.md) document describes this model conceptually. Remaining work is to **prove** serializability for the optimistic variant (e.g., via refinement to a serial spec) and to tighten adversarial cases around read/write-set manipulation.

### 34. Session Types Integration

The specification uses implicit protocol states (UTXO states encode valid action sequences) rather than explicit session types. A more principled approach would:

- Define session type protocols for UTXO lifecycles: `Created -> Yield -> (Effect <-> Resume)* -> Consume`
- Define session type protocols for effect handling: `Raise -> Handle -> Resume`
- Guard actions by session type state
- Prove that well-typed transactions never violate protocol

This would make the protocol structure more explicit and could enable compositional reasoning. The challenge is that TLA+ does not have native session type support; the protocol would need to be encoded as explicit state machines.

### 35. Proof/MCC Integration

The specification models **proof commitments and lifecycle** (generation, verification, failure) and gates commit on verified proofs. A more complete model would:

- Define stronger proof structure (what exactly is proved, how it binds to execution)
- Model proof composition (IVC/PCD chains) beyond simple commitments
- Connect proof validity to invariant preservation (beyond "marked Verified")
- Model MCC (Merkle-ized Computational Commitment) for storage

This would require careful design to avoid making the model unmanageably large. One approach is to model proofs as abstract capabilities that are "consumed" when used, similar to linear types.

### 36. Serializable-Trace Refinement

The [interleavingTypes.md](../../interleavingTypes.md) document mentions a serializable-trace property: every interleaving trace should be equivalent to some serial commit order. This is not directly stated as an invariant in the current specification.

The spec now includes **IEUTxO chunk validity** helpers (`IEUTxOTxValid`, `ChunkValid`) and invariants over committed history to set the stage for this proof. Proving serializability still requires a refinement mapping: show that the concurrent spec refines a serial spec where transactions execute atomically (see `StarstreamSerial.tla`).

### 37. Scaling Model Bounds

The current bounds (3 UTXOs, 2 pending transactions) are small. Larger bounds would increase confidence but also increase model checking time exponentially. Research directions:

- **Abstraction techniques**: Reduce state space by abstracting irrelevant details while preserving safety properties
- **Compositional verification**: Verify components separately and compose the results
- **Inductive invariants**: Prove invariants hold for arbitrary sizes using induction rather than enumeration
- **Bounded model checking**: Use SAT/SMT solvers (like Alloy or TLAPS) for larger bounds

The specification is designed to be extended in these directions. The modular structure supports compositional reasoning, and the invariants are written to be inductive where possible.

---

## Appendix: Quick Reference

### Module Summary

| Module | Purpose |
|--------|---------|
| `StarstreamTypes.tla` | Constants, enums, token bags |
| `StarstreamFrame.tla` | Coroutine frame with hash |
| `StarstreamAuth.tla` | Signatures, content binding |
| `StarstreamEffects.tla` | Effect records, stack ops |
| `StarstreamUTXO.tla` | 6-state UTXO machine |
| `StarstreamCoordination.tla` | Script execution, method calls |
| `StarstreamTransaction.tla` | Multi-phase transaction model |
| `StarstreamLedger.tla` | Global state, lock management |
| `StarstreamSpec.tla` | Init, Next, fairness |
| `StarstreamInvariants.tla` | All safety/liveness properties |
| `MC_Starstream.tla` | Model checking config |
| `Starstream.cfg` | TLC configuration file |

### Key Invariants

| Invariant | Property |
|-----------|----------|
| `INV_LINEAR_NoDoubleSpend` | Live and consumed sets disjoint |
| `INV_BALANCE_TxPreserved` | Input tokens equal output tokens |
| `INV_BALANCE_NoOverflow` | Per-asset totals stay within bounds |
| `INV_BALANCE_PendingOutputsNoNFTDuplication` | Pending outputs don’t duplicate NFTs |
| `INV_AUTH_ValidSpend` | Committed txs have valid signatures |
| `INV_AUTH_OwnerOnly` | Signers own their inputs |
| `INV_LOCK_Exclusive` | Locks reference existing txs |
| `INV_LOCK_AtomicRelease` | Lock release is atomic with state change |
| `INV_EFFECT_MustBeHandled` | No pending effects at completion |
| `INV_EFFECT_SourceSuspended` | Pending effects come from suspended inputs |
| `INV_EFFECT_ContinuationMatch` | Continuations match suspended frame PC |
| `INV_EFFECT_StackDepthBounded` | Effect stack depth is bounded |
| `INV_FRAME_Integrity` | Frame hashes are consistent |
| `INV_ROLLBACK_NoLeak` | Failed txs leave no trace |

### Command Reference

```bash
# Parse check (SANY)
java -cp tla2tools.jar tla2sany.SANY StarstreamSpec.tla

# Model check
java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg

# Parallel model check
java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg -workers 4

# Simulation mode
java -cp tla2tools.jar tlc2.TLC MC_Starstream.tla -config Starstream.cfg -simulate
```
