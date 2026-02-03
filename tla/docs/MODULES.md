# Module reference guide

This document lists each TLA+ module in the Starstream specification, its purpose, and key operators.

## Architecture layers

```
Layer 6: Alignment       StarstreamCircuitAlignment, StarstreamSessionProtocol
Layer 5: Verification    MC_Starstream, MC_StarstreamOptimistic, StarstreamInvariants
Layer 4: Composition     StarstreamSpec, StarstreamSpecOptimistic
Layer 3.5: Refinement    StarstreamSerialRefinement, StarstreamSerial
Layer 3: Orchestration   StarstreamLedger
Layer 2: Core            StarstreamTransaction, StarstreamCoordination, StarstreamPTB,
                         StarstreamEffects, StarstreamAuth, StarstreamProof
Layer 1: Foundation      StarstreamUTXO, StarstreamFrame, StarstreamTypes
```

---

## StarstreamTypes

**Layer:** Foundation
**Extends:** `Integers`, `Sequences`, `FiniteSets`, `TLC`
**Purpose:** Defines all constants, enumerations, and foundational type sets.

### Constants

| Constant | Description |
|----------|-------------|
| `MAX_UTXOS` | Maximum UTXOs in ledger |
| `MAX_TX_INPUTS` | Maximum inputs per transaction |
| `MAX_TX_OUTPUTS` | Maximum outputs per transaction |
| `MAX_FRAME_VARS` | Maximum local variables in frame |
| `MAX_PENDING_TXS` | Maximum concurrent pending transactions |
| `MAX_TOKEN_TOTAL` | Maximum per-asset total for overflow checks |
| `UTXO_ID_BOUND` | Maximum UTXO identifier value |
| `CHAIN_ID` | Chain identifier for replay protection |
| `BLOCK_HEIGHT` | Block height for replay protection |
| `TOKEN_TYPES` | Set of token types (e.g., `{"ADA", "NFT"}`) |
| `TOKEN_IDS` | Set of token IDs (e.g., `{1, 2, 3}`) |

### Enumerations

| Set | Values | Description |
|-----|--------|-------------|
| `UTXOStates` | `Created`, `Suspended_at_Yield`, `Suspended_at_Effect`, `Reserved`, `Executing`, `Consumed` | UTXO lifecycle states |
| `EffectKinds` | `Pure`, `Effectful`, `Runtime` | Effect categories |
| `EffectTags` | `E1`, `E2`, `E3` | Effect tags |
| `CallTypes` | `Query`, `Mutate`, `Consume` | Method call types |
| `TxStates` | `Idle`, `Reserve`, `Executing`, `Committing`, `Rollback`, `Committed`, `Failed` | Transaction phases |
| `CoordPhases` | `NotStarted`, `Gathering`, `Processing`, `Finalizing`, `Complete` | Coordination phases |
| `WitLedgerEffectKinds` | `Resume`, `Yield_Intermediate`, `Yield_Final`, `Burn`, `Bind`, `Unbind`, `NewUtxo` | IVC effect kinds |
| `ActivationStates` | `Inactive`, `Active`, `Suspended` | IVC activation states |
| `ProofKinds` | `IVC_Step`, `IVC_Accumulator`, `Witness` | Proof kinds |
| `ProofPhases` | `NotStarted`, `Generating`, `Verifying`, `Verified`, `Failed` | Proof lifecycle phases |

### Key operators

| Operator | Signature | Purpose |
|----------|-----------|---------|
| `EmptyTokenBag` | `TokenBagType` | Zero-valued token bag |
| `AddTokenBags(b1, b2)` | `TokenBagType x TokenBagType -> TokenBagType` | Add two token bags |
| `TokenBagsEqual(b1, b2)` | `TokenBagType x TokenBagType -> BOOLEAN` | Check token bag equality |
| `SumTokenBags(utxoSet)` | `SUBSET UTXO -> TokenBagType` | Sum tokens across UTXOs |
| `FoldSet(f, acc, s)` | `(a,b->a) x a x SET b -> a` | Fold over a set |
| `FcnRange(f)` | `f -> SET` | Range of a function (`{f[x] : x \in DOMAIN f}`) |
| `IsValidTokenBag(bag)` | `TokenBagType -> BOOLEAN` | Validate token bag structure |

---

## StarstreamFrame

**Layer:** Foundation
**Extends:** `StarstreamTypes`
**Purpose:** Models stackless coroutine frames with program counter, locals, and integrity hash.

### Frame record

```tla
[pc: PCRange,          \* pc = program counter
 locals: LocalsType,
 methodId: MethodIdRange,
 hash: FrameHashRange]
```

### Constructors

| Operator | Purpose |
|----------|---------|
| `InitFrame(method)` | Create initial frame at PC=0 |
| `FrameAtYield(pc, vars, method)` | Create frame at yield point |
| `TerminatedFrame(method)` | Create terminated frame (PC=-1) |

### Predicates

| Operator | Purpose |
|----------|---------|
| `IsFrame(f)` | Validate frame structure |
| `IsInitialFrame(f)` | Check if at start (PC=0) |
| `IsTerminatedFrame(f)` | Check if terminated (PC=-1) |
| `IsSuspendedFrame(f)` | Check if suspended (PC>0) |
| `IsResumableFrame(f)` | Check if can resume |

### Operations

| Operator | Purpose |
|----------|---------|
| `AdvancePC(frame, newPC)` | Update program counter |
| `SetLocal(frame, var, val)` | Set local variable |
| `GetLocal(frame, var)` | Read local variable |
| `Terminate(frame)` | Set PC to -1 |
| `Resume(frame, pc, locals)` | Resume with new state |
| `Rehash(frame)` | Recompute integrity hash |

---

## StarstreamAuth

**Layer:** Core
**Extends:** `StarstreamTypes`
**Purpose:** Models signature verification and ownership authorization.

### Signature record

```tla
[owner: OwnerAddrs,
 txId: TxIdRange,
 contentsHash: TxContentsHashType]
```

### Key operators

| Operator | Purpose |
|----------|---------|
| `MakeSignature(owner, txId, hash)` | Construct a signature |
| `ValidSignature(sig, tx)` | Verify signature matches transaction |
| `InputsOwnedBySigner(tx)` | Check all inputs owned by signer |
| `TxContentsHash(tx)` | Compute transaction digest |
| `TxInputsDigest(tx)` | Digest of input UTXOs |
| `TxOutputsDigest(tx)` | Digest of output UTXOs |
| `TxProofsDigest(tx)` | Digest of proof commitments |
| `TxCoordDigest(tx)` | Digest of coordination state |
| `PTBTraceCommitments(coord)` | Ordered PTB trace commitments (authoritative) |
| `CallCommitments(coord)` | Legacy ordered call sequence commitments |
| `OutputSpecCommitments(coord)` | Ordered output specification commitments |
| `EffectCommitments(coord)` | Ordered effect stack commitments |

**Note:** Coordination commitments are **ordered sequences**; reordering changes the digest. The digest now commits to the PTB trace and PTB cursor (`ptbIndex`). Legacy `pendingCalls`/`callIndex` are retained for backward compatibility but are not part of the digest.

**Replay protection:** `TxContentsHash` commits to `CHAIN_ID` and `BLOCK_HEIGHT`, binding signatures to chain context.

**Model-checking note:** `IsTxContentsHash` remains intentionally shallow, but it now checks the *structure* of all digest components (including PTB trace commitments). Correctness still relies on equality with `TxContentsHash` in `ValidSignature`.

---

## StarstreamProof

**Layer:** Core
**Extends:** `StarstreamTypes`, `StarstreamFrame`
**Purpose:** Models proof commitments, phases, and verification lifecycle.

### Proof commitment record

```tla
[proofKind: ProofKinds,
 ivcProcessId: ProcessIdRange,
 commitmentHash: FrameHashRange,
 verificationKey: 1..10,
 proofData: DatumValues,
 verified: BOOLEAN,
 phase: ProofPhases,
 stepNumber: 0..UTXO_ID_BOUND]
```

### Key operators

| Operator | Purpose |
|----------|---------|
| `NewProofCommitment(...)` | Construct a proof commitment |
| `IVCStepProof(pid, hash, step)` | IVC step proof constructor |
| `IVCAccumulatorProof(pid, hash)` | IVC accumulator proof constructor |
| `WitnessProof(pid, hash, data)` | Witness proof constructor |
| `BeginProofGeneration(proof)` | Mark proof as generating |
| `BeginProofVerification(proof)` | Mark proof as verifying |
| `MarkProofVerified(proof)` | Mark proof verified |
| `MarkProofFailed(proof)` | Mark proof failed |
| `HasPendingProofFor(proofSet, pid)` | Pending proof exists for pid |
| `VerifiedProofs(proofSet)` | All verified proofs |

---

## StarstreamEffects

**Layer:** Core
**Extends:** `StarstreamTypes`, `StarstreamFrame`
**Purpose:** Models the algebraic effect system for UTXO coroutines.

### Effect record

```tla
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

### Constructors

| Operator | Purpose |
|----------|---------|
| `NewEffect(kind, utxoId, contId, tag, payload)` | Create new effect (default interface/handler) |
| `NewEffectWithInterface(..., iface, witKind)` | Create effect with explicit interface + WitLedger kind |
| `PureEffect(...)` | Create Pure effect |
| `EffectfulEffect(...)` | Create Effectful effect |
| `RuntimeEffect(...)` | Create Runtime effect |
| `PureEffectOnInterface(...)` | Create Pure effect for interface |
| `EffectfulEffectOnInterface(...)` | Create Effectful effect for interface |
| `RuntimeEffectOnInterface(...)` | Create Runtime effect for interface |

### Stack operations

| Operator | Purpose |
|----------|---------|
| `EmptyEffectStack` | Empty stack `<<>>` |
| `PushEffect(stack, effect)` | Add effect to stack |
| `PopEffect(stack)` | Remove top effect |
| `PeekEffect(stack)` | View top effect |
| `HandleTopEffect(stack, result)` | Pop top effect after handling |
| `AllEffectsHandled(stack)` | Check all effects handled |
| `PendingEffects(stack)` | Get unhandled effects |

---

## StarstreamUTXO

**Layer:** Foundation
**Extends:** `StarstreamTypes`, `StarstreamFrame`
**Purpose:** Models UTXO records and state transitions.

### UTXO record

```tla
[id: UTXOIdRange,
 state: UTXOStates,
 frame: FrameSet,
 datum: DatumValues,
 tokens: TokenBagType,
 contractId: ContractIds,
 owner: OwnerAddrs,
 lockedBy: TxIdRange | NO_TX]
```

### Constructors

| Operator | Purpose |
|----------|---------|
| `NewUTXO(id, contract, owner, datum, tokens)` | Create new UTXO in Created state |
| `SuspendedUTXO(id, contract, owner, datum, tokens, frame)` | Create suspended UTXO |

### Predicates

| Operator | Purpose |
|----------|---------|
| `IsLive(u)` | UTXO is not consumed |
| `IsConsumed(u)` | UTXO is consumed |
| `IsReserved(u)` | UTXO is reserved by tx |
| `CanQuery(u)` | UTXO can be queried |
| `CanMutate(u)` | UTXO can be mutated |
| `CanConsume(u)` | UTXO can be consumed |
| `CanReserve(u)` | UTXO can be reserved |

### State transitions

| Operator | Transition |
|----------|------------|
| `CreateToYield(u, pc, datum)` | Created -> Suspended_at_Yield |
| `ReserveUTXO(u, txId)` | Suspended_at_Yield -> Reserved |
| `BeginExecuteUTXO(u)` | Reserved -> Executing |
| `EndExecuteUTXO(u)` | Executing -> Reserved |
| `ConsumeUTXO(u)` | * -> Consumed |
| `ReleaseReservation(u)` | Reserved -> Suspended_at_Yield |

**Note:** `BeginExecuteUTXO` / `EndExecuteUTXO` are wired into `StarstreamSpec` via `BeginExecute` and `FinalizeTx`.

---

## StarstreamCoordination

**Layer:** Core
**Extends:** `StarstreamTypes`, `StarstreamFrame`, `StarstreamUTXO`, `StarstreamEffects`, `StarstreamPTB`
**Purpose:** Models coordination script execution within transactions, with PTB trace validation as the authoritative driver.

### Coordination state

```tla
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

### Method call record (legacy)

```tla
[callType: CallTypes,
 targetUtxo: UTXOIdRange,
 methodId: MethodIdRange,
 args: DatumValues,
 executed: BOOLEAN,
 result: DatumValues | NULL]
```

### Constructors

| Operator | Purpose |
|----------|---------|
| `QueryCall(utxoId, method, args)` | Create read-only call |
| `MutateCall(utxoId, method, args)` | Create mutation call |
| `ConsumeCall(utxoId, method, args)` | Create consumption call |
| `InitCoordination` | Initial coordination state |
| `GatheringCoordination(inputs)` | Coordination gathering inputs |

### Phase transitions

| Operator | Transition |
|----------|------------|
| `BeginGathering(coord, inputIds)` | NotStarted -> Gathering |
| `BeginProcessingPTB(coord, trace)` | Gathering -> Processing (PTB validation) |
| `BeginProcessing(coord, calls)` | Gathering -> Processing (legacy call sequence) |
| `ExecuteNextCall(coord, result)` | Advance call index |
| `BeginFinalizing(coord, outputs)` | Processing -> Finalizing |
| `CompleteCoordination(coord)` | Finalizing -> Complete |

### Predicates

| Operator | Purpose |
|----------|---------|
| `IsProcessing(coord)` | In Processing phase |
| `IsComplete(coord)` | In Complete phase |
| `AllCallsExecuted(coord)` | All calls done |
| `HasPendingEffects(coord)` | Pending (unhandled) effects exist |
| `CurrentCall(coord)` | Get next call to execute |

### Handler stack ops

| Operator | Purpose |
|----------|---------|
| `InstallHandlerInCoord(coord, iface, handler)` | Push handler for interface |
| `UninstallHandlerInCoord(coord, iface)` | Pop handler for interface |
| `CoordHasHandlerFor(coord, iface)` | Handler exists for interface |
| `PendingEffectsForInterface(coord, iface)` | Pending effects by interface |

---

## StarstreamPTB

**Layer:** Core
**Extends:** `StarstreamTypes`
**Purpose:** Defines PTB event records and bounded PTB traces used for validation.

### Key operators

| Operator | Purpose |
|----------|---------|
| `PTBEventKinds` | Enumerated PTB event kinds |
| `PTBTrace` | Bounded sequence of PTB events (for TLC) |
| `IsPTBEvent(e)` | Event well-formedness check |
| `IsPTBTrace(t)` | Trace well-formedness check |

---

## StarstreamTransaction

**Layer:** Core
**Extends:** `StarstreamTypes`, `StarstreamFrame`, `StarstreamUTXO`, `StarstreamEffects`, `StarstreamCoordination`, `StarstreamAuth`, `StarstreamProof`
**Purpose:** Models transaction records and balance logic.

### Transaction Record

```tla
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
 result: DatumValues | NULL,
 proofCommitments: SUBSET ProofCommitmentType,
 proofPhase: ProofPhases]
```

### Constructors

| Operator | Purpose |
|----------|---------|
| `NewTransaction(txId, signer)` | Create idle transaction |
| `TransactionWithInputs(txId, signer, inputs)` | Create with inputs |

### Predicates

| Operator | Purpose |
|----------|---------|
| `IsCommittedTx(tx)` | Transaction committed |
| `IsFailedTx(tx)` | Transaction failed |
| `IsCompleteTx(tx)` | Committed or failed |
| `BalancePreserved(tx)` | Inputs equal outputs |

### Operations

| Operator | Purpose |
|----------|---------|
| `SumInputTokens(tx)` | Total tokens in inputs |
| `SumOutputTokens(tx)` | Total tokens in outputs |
| `BeginCommitting(tx)` | Move tx to Committing phase |
| `BeginRollback(tx, reason)` | Move tx to Rollback phase |
| `CommitTransaction(tx)` | Mark as committed |
| `AbortTransaction(tx, reason)` | Mark as failed |
| `SignTx(tx)` | Update signature |
| `AddProofToTx(tx, proof)` | Attach proof commitment |
| `VerifyProofInTx(tx, proof)` | Mark proof verified |
| `AllTxProofsVerified(tx)` | All proofs verified |

---

## StarstreamLedger

**Layer:** Orchestration
**Extends:** `StarstreamTypes`, `StarstreamFrame`, `StarstreamUTXO`, `StarstreamEffects`, `StarstreamCoordination`, `StarstreamTransaction`
**Purpose:** Models global ledger state and operations.

### Ledger State

```tla
[utxoSet: SUBSET UTXORecordSet,
 consumedSet: SUBSET UTXOIdRange,
 lockedSet: SUBSET UTXOIdRange,
 nextUtxoId: UTXOIdRange | UTXO_ID_BOUND+1,
 nextTxId: TxIdRange | UTXO_ID_BOUND+1,
 pendingTxs: SUBSET TransactionRecordSet,
 txHistory: Seq(TransactionRecordSet),
 proofStore: SUBSET ProofCommitmentType,
 activeProofs: SUBSET ProcessIdRange]
```

### Constructors

| Operator | Purpose |
|----------|---------|
| `EmptyLedger` | Empty ledger state |
| `GenesisLedger(initialUtxos)` | Ledger with initial UTXOs |

### Operations

| Operator | Purpose |
|----------|---------|
| `CreateUTXOInLedger(ledger, ...)` | Add new UTXO |
| `UpdateUTXOInLedger(ledger, utxo)` | Update existing UTXO |
| `BeginTxInLedger(ledger, inputIds, signer)` | Start transaction |
| `CommitTxInLedger(ledger, txId)` | Commit transaction |
| `AbortTxInLedger(ledger, txId, reason)` | Abort transaction |
| `GetUTXO(ledger, id)` | Retrieve UTXO by ID |
| `GetPendingTx(ledger, id)` | Retrieve pending tx by ID |
| `AddProofToLedger(ledger, proof)` | Add proof commitment |
| `UpdateProofInLedger(ledger, old, new)` | Update proof commitment |
| `RemoveProofFromLedger(ledger, proof)` | Remove proof commitment |
| `GetProofForProcess(ledger, pid)` | Find proof by process id |
| `HasActiveProofFor(ledger, pid)` | Process has active proof |

### IEUTxO helpers

| Operator | Purpose |
|----------|---------|
| `IEUTxOTxValid(ledger, tx)` | IEUTxO validity predicate for a tx |
| `ChunkValid(txs)` | Validity for a sequence (chunk) of transactions |
| `InputsLiveInLedger(ledger, tx)` | Inputs exist in current UTXO set |
| `FreshOutputIds(ledger, tx)` | Outputs not already used/consumed |

### Invariants

| Operator | Purpose |
|----------|---------|
| `NoDoubleSpend(ledger)` | Active and consumed disjoint |
| `UniqueActiveIds(ledger)` | No duplicate UTXO IDs |
| `LockedSetConsistent(ledger)` | Locked set matches UTXO locks |

---

## StarstreamSpec

**Layer:** Composition
**Extends:** All core modules
**Purpose:** Defines initial state, actions, and temporal specification.

### State variables

| Variable | Type | Purpose |
|----------|------|---------|
| `ledger` | `LedgerStateSet` | Global ledger state |

### Actions

| Action | Purpose |
|--------|---------|
| `CreateUTXO(contract, owner, datum, tokens)` | Create new UTXO |
| `ReserveTx(inputIds, signer)` | Start new transaction |
| `BeginExecute(txId)` | Begin tx execution |
| `StartPTB(txId, trace)` | Start PTB trace processing |
| `ProcessPTBEvent(txId)` | Advance PTB trace (Raise/Resume/Install/Uninstall/Read/etc.) |
| `HandleTxEffect(txId, result)` | PTB Resume event (alias used for liveness fairness) |
| `FinalizeTx(txId, outputSpecs)` | Finalize outputs |
| `BeginCommit(txId)` | Enter Committing phase |
| `CommitTx(txId)` | Commit transaction |
| `StartRollback(txId, reason)` | Enter Rollback phase |
| `FinishRollback(txId)` | Finalize rollback as Failed |
| `BeginTxProofGeneration(txId, pid, hash)` | Begin proof generation |
| `VerifyTxProof(txId, pid)` | Verify proof for tx |
| `InjectInvalidTx(inputIds, signer, badOwner)` | Inject malformed tx (adversarial) |
| `RejectInvalidTx(txId, reason)` | Reject malformed tx |
| `QueryUTXO(utxoId)` | Query UTXO (no-op) |
| `YieldUTXO(utxoId, pc, datum)` | Yield from Created |

### Specifications

| Spec | Definition | Purpose |
|------|------------|---------|
| `Spec` | `Init /\ [][Next]_vars` | Basic safety spec |
| `FairSpec` | `Spec /\ WeakFairness` | With weak fairness |
| `StrongFairSpec` | `FairSpec /\ StrongFairness` | With strong fairness |

---

## StarstreamSpecOptimistic

**Layer:** Composition
**Extends:** `StarstreamSpec`
**Purpose:** Optimistic-concurrency variant with explicit read/write sets and commit-time validation.

### Key actions

| Action | Purpose |
|--------|---------|
| `OptBeginTx(ids, signer)` | Begin optimistic tx (no locking) |
| `OptBeginExecute(txId)` | Enter execution phase |
| `OptFinalizeTx(txId, outputSpecs)` | Finalize outputs |
| `OptBeginCommit(txId)` | Validate read set + outputs before commit |
| `OptCommitTx(txId)` | Commit if still valid |
| `OptStartRollback(txId, reason)` | Abort optimistic tx |

**Note:** Optimistic validation uses `ReadSetValid` and `OutputsFresh` at commit time, and signatures commit to read/write sets.

---

## StarstreamInvariants

**Layer:** Verification
**Extends:** All modules including `StarstreamSpec`
**Purpose:** Defines all safety invariants and liveness properties.

See [INVARIANTS.md](INVARIANTS.md) for complete catalog.

---

## MC_Starstream

**Layer:** Verification
**Extends:** `StarstreamSpec`, `StarstreamInvariants`, `TLC`
**Purpose:** Model checking configuration and helpers.

### Constant definitions

```tla
MC_MAX_UTXOS == 3
MC_MAX_TX_INPUTS == 2
MC_UTXO_ID_BOUND == 8
MC_TOKEN_TYPES == {"ADA", "NFT"}
...
```

### Symmetry sets

```tla
TokenTypeSymmetry == Permutations(MC_TOKEN_TYPES)
OwnerSymmetry == Permutations({"Alice", "Bob", "Charlie"})
```

**Note:** These are only used if `SYMMETRY ...` is enabled in `Starstream.cfg` (commented out by default).

### Trace helpers

| Operator | Purpose |
|----------|---------|
| `MC_FindDoubleSpend` | Find double-spend trace |
| `MC_FindBalanceViolation` | Find balance violation |
| `MC_FindCompletedTx` | Find state with completed tx |
| `MC_FindFailedTx` | Find state with failed tx |

---

## Starstream.cfg

**Type:** TLC Configuration File
**Purpose:** Configure model checker constants and properties.

### Sections

```
SPECIFICATION MC_Spec
CONSTANTS (model bounds)
CONSTRAINT MC_StateConstraint
INVARIANTS (safety properties to check)
PROPERTIES (liveness properties - commented by default)
CHECK_DEADLOCK FALSE
```

See [USAGE.md](USAGE.md) for configuration details.

---

## StarstreamSerial

**Layer:** Refinement
**Extends:** `StarstreamTypes`, `StarstreamUTXO`
**Purpose:** Defines the serial (atomic) specification used as the refinement target.

### Key operators

| Operator | Purpose |
|----------|---------|
| `SerialSpec` | Temporal specification for serial execution |
| `SerialCommit(tx)` | Atomic commit of a single transaction |
| `SerialAbort(tx)` | Atomic abort of a single transaction |

---

## StarstreamSerialRefinement

**Layer:** Refinement
**Extends:** `StarstreamSpec`, `StarstreamSerial`, `StarstreamCircuitAlignment`
**Purpose:** Defines the refinement mapping from the concurrent spec to the serial spec. Proves that every concurrent behavior refines a serial behavior.

### Abstraction map

| Operator | Purpose |
|----------|---------|
| `NormalizeState(state)` | Map intermediate UTXO states to Suspended_at_Yield |
| `AbsUTXO(u)` | Abstract a single UTXO (normalize state, remove lock) |
| `AbsUtxoSet(ledger)` | Abstract the entire UTXO set |
| `aUtxoSet`, `aConsumedSet`, `aTxHistory` | Abstract state variables |

### Trace abstraction

| Operator | Purpose |
|----------|---------|
| `CommittedTxsIn(history)` | Extract committed transactions from history |
| `SerialOrdering` | Serial ordering derived from commit order |
| `TxTraceSerializable(tx)` | Transaction trace satisfies interleaving constraints |

### Stuttering map

| Operator | Purpose |
|----------|---------|
| `IsStutteringAction` | Predicate for stuttering steps |
| `IsVisibleCommit(txId)` | Predicate for visible commit steps |

### Theorems

| Theorem | Purpose |
|---------|---------|
| `SerialRefinement` | Main claim: `Spec => SerialSpec` |
| `AbsTypeOK` | Abstraction preserves type invariant |
| `StutteringPreservation` | Stuttering steps preserve abstract state |
| `CommitRefinesSerial` | CommitTx refines SerialCommit |
| `CircuitRequiredForCommit` | Circuit verification necessary for commit |
| `CommitOrderSerializable` | Commit order is conflict-serializable |

### Circuit connection

| Operator | Purpose |
|----------|---------|
| `HasCircuitWitness(tx)` | Committed tx has valid circuit witness |
| `RefinementWitness(tx)` | Full refinement witness (circuit + ledger) |
| `AllCommittedHaveWitnesses` | All committed txs have witnesses |

---

## StarstreamCircuitAlignment

**Layer:** Alignment
**Extends:** All core modules
**Purpose:** Maps each LedgerOperation variant from the interleaving proof circuit to TLA+ actions, invariants, and types. Bridges the ZK circuit and the TLA+ specification.

### Section 1: LedgerOperation map

| Circuit Op | TLA+ Action | Notes |
|-----------|-------------|-------|
| `Resume` | HandleTxEffect | PTB resume event |
| `Yield_Intermediate` | ProcessPTBEvent | PTB raise event |
| `Yield_Final` | FinalizeTx | Final yield |
| `Burn` | CommitTx (input consumption) | UTXO consumption |
| `Bind` | ProcessPTBEvent | PTB install handler |
| `Unbind` | ProcessPTBEvent | PTB uninstall handler |
| `NewUtxo` | FinalizeTx (output creation) | UTXO creation |
| `NewCoord` | ReserveTx | Coordination creation |
| `GetHandler` | RouteEffectToHandler | Handler lookup |
| `RefCreate` | CreateUTXOInLedger | Reference creation |
| `RefConsume` | ConsumeUTXO | Reference consumption |
| `RefRead` | QueryUTXO | Reference read |

### Section 4: Alignment validation

| Operator | Purpose |
|----------|---------|
| `ValidCircuitStep(coord, effect)` | Circuit step well-formedness |
| `ResumeAligned(coord, effect)` | Resume operation alignment |
| `YieldAligned(coord, effect)` | Yield operation alignment |
| `BurnAligned(tx, effect)` | Burn operation alignment |
| `BindAligned(coord, effect)` | Bind operation alignment |
| `StepAligned(ledger, tx, coord, effect)` | Full step alignment |

### Section 5: New invariants

| Invariant | Purpose |
|-----------|---------|
| `INV_CIRCUIT_NoSelfResume` | No process resumes itself |
| `INV_CIRCUIT_ActivationConsistent` | Activation state matches IVC config |
| `INV_CIRCUIT_RefArenaBounded` | Reference arena within capacity |
| `INV_CIRCUIT_HandlerNodeLinked` | Handler stack nodes properly linked |
| `INV_CIRCUIT_InitializationConsistent` | Init state matches coordination phase |
| `INV_CIRCUIT_EffectOpcodeSingleStep` | One opcode per IVC step |
| `INV_CIRCUIT_DualTraceConsistency` | Resume inputs match yield outputs |
| `INV_CIRCUIT_ValueCommitmentIntegrity` | Frame hashes match computation |
| `INV_CIRCUIT_All` | Conjunction of all circuit invariants |

### Section 6: Gap analysis

| Operator | Purpose |
|----------|---------|
| `CircuitVerifiable(tx)` | Properties circuit can verify |
| `RequiresLedgerValidation(tx)` | Properties requiring ledger validation |
| `FullyVerified(ledger, tx)` | Circuit + ledger complete verification |

---

## StarstreamSessionProtocol

**Layer:** Alignment
**Extends:** `StarstreamTypes`, `StarstreamFrame`, `StarstreamEffects`, `StarstreamCoordination`
**Purpose:** Formalizes the effect handler install/uninstall/get protocol as session types encoded as TLA+ action guards. `SessionProtocolValid` is enforced during PTB event processing in `StarstreamSpec`.

### Session type (informal)

```
Coroutine = !Raise(tag, payload, iface) . ?Resume(value) . Coroutine | end
Handler   = ?Effect(tag, payload) . !Result(value) . Handler | end
Coord     = InstallHandler(iface) . Coord | UninstallHandler(iface) . Coord
          | !Dispatch(effect, handler) . ?Result(value) . Coord | Commit
```

### Protocol guards

| Guard | Purpose |
|-------|---------|
| `GuardInstallHandler(coord, iface)` | Handler install precondition |
| `GuardUninstallHandler(coord, iface)` | Handler uninstall precondition |
| `GuardRaiseEffect(coord, iface, utxoId)` | Effect raise precondition |
| `GuardHandleEffect(coord, iface)` | Effect handle precondition |
| `GuardGetHandler(coord, iface)` | Handler lookup precondition |
| `GuardProtocolCommit(coord)` | Protocol-level commit precondition |

### Sequencing rules

| Rule | Purpose |
|------|---------|
| `InstallBeforeRaise` | Handler must exist before effects raised |
| `AllHandledBeforeCommit` | All effects resolved before commit |
| `NoSelfResume` | Process cannot resume itself |

### Linearity constraints

| Constraint | Purpose |
|------------|---------|
| `EffectLinearity` | At most one pending effect per UTXO |
| `HandlerLinearity` | Each effect handled by exactly one handler |
| `ContinuationLinearity` | Unique continuation IDs among pending effects |

### UTXO lifecycle session type

| Operator | Purpose |
|----------|---------|
| `ValidUTXOTransition(from, to)` | Valid UTXO state transitions |
| `INV_UTXO_SessionType(l, l')` | All UTXO transitions follow session type |

### Protocol composition

| Operator | Purpose |
|----------|---------|
| `InterfacesIndependent(coord, i1, i2)` | Two interfaces don't share resources |
| `InterfaceIsolation(coord)` | All active interfaces are independent |
| `ProtocolWellFormed(coord)` | Full protocol well-formedness check |
| `SessionProtocolValid(coord)` | Session protocol validity (duality + matching) |

