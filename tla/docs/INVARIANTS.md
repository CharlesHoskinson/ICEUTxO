# Invariants catalog

This document provides a catalog of invariants in the Starstream TLA+ specification, organized by category.

## Summary

| Category | Count | Purpose |
|----------|-------|---------|
| TYPE | 5 | Data structure well-formedness |
| AUTH | 2 | Authorization correctness |
| BALANCE | 5 | Token conservation |
| LINEAR | 6 | No double-spend, linear types |
| IEUTXO | 7 | IEUTxO chunk/serializability scaffolding |
| LOCK | 4 | Reservation correctness |
| OPT | 2 | Optimistic read/write-set consistency |
| OPT_EFFECT | 2 | Optimistic effect handling |
| LIFECYCLE | 3 | State machine correctness |
| EFFECT | 10 | Effect handling (including interfaces) |
| PROOF | 8 | Proof lifecycle correctness |
| FRAME | 1 | Frame integrity |
| ATK | 3 | Attack prevention |
| ROLLBACK | 1 | Failure cleanup |
| LIVENESS | 3 | Progress guarantees |

---

## Choosing invariants (quick guide)

| Concern | Recommended invariants |
|---------|------------------------|
| Type sanity / schema issues | `INV_TYPE_All` |
| Double-spend / replay | `INV_LINEAR_NoDoubleSpend`, `INV_LINEAR_ConsumedTracked`, `INV_ATK_NoReplay` |
| Unauthorized spend | `INV_AUTH_ValidSpend`, `INV_AUTH_OwnerOnly` |
| Token conservation | `INV_BALANCE_TxPreserved`, `INV_BALANCE_NoOverflow` |
| NFT duplication | `INV_BALANCE_NFTUnique`, `INV_BALANCE_PendingOutputsNoNFTDuplication` |
| Locking / reservation bugs | `INV_LOCK_Exclusive`, `INV_LOCK_ValidReservation`, `INV_LOCK_AtomicRelease` |
| Effect handling safety | `INV_EFFECT_MustBeHandled`, `INV_EFFECT_SourceSuspended`, `INV_EFFECT_ContinuationMatch` |
| Interface handler correctness | `INV_EFFECT_InterfaceConsistent`, `INV_EFFECT_EffectsMatchInstalledHandlers` |
| Optimistic read/write validation | `INV_OPT_ReadSetConsistent`, `INV_OPT_WriteSetConsistent` |
| Proof gating | `INV_PROOF_VerificationInvariant`, `INV_PROOF_CommittedVerified` |
| IEUTxO chunk validity | `INV_IEUTXO_CommittedHistoryChunk` |
| Rollback correctness | `INV_ROLLBACK_NoLeak` |

If you want a broad safety sweep, use `INV_Safety` (it includes the main safety invariants).

---

## Type invariants

Type invariants ensure data structures are well-formed at all times. **Check these first** - type errors cause confusing failures in other invariants.

### INV_TYPE_LedgerWellTyped

**Definition:**
```tla
INV_TYPE_LedgerWellTyped ==
    IsValidLedger(ledger)
```

**What It Checks:** The global ledger state satisfies `IsValidLedger`:
- All UTXOs in `utxoSet` are valid UTXO records
- `nextUtxoId` and `nextTxId` are within bounds
- All pending transactions are valid transaction records

**Dependencies:** None (foundational)

---

### INV_TYPE_FramesWellTyped

**Definition:**
```tla
INV_TYPE_FramesWellTyped ==
    \A u \in ledger.utxoSet : IsFrame(u.frame)
```

**What It Checks:** Every UTXO has a valid frame with:
- Valid program counter
- Valid locals mapping
- Valid method ID
- Correct integrity hash

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

### INV_TYPE_TokenBagsWellTyped

**Definition:**
```tla
INV_TYPE_TokenBagsWellTyped ==
    \A u \in ledger.utxoSet : IsValidTokenBag(u.tokens)
```

**What It Checks:** Every UTXO has a valid token bag with:
- Domain equals `TOKEN_TYPES`
- Each type maps to all `TOKEN_IDS`
- All quantities in `TokenQuantityRange`

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

### INV_TYPE_PendingTxWellTyped

**Definition:**
```tla
INV_TYPE_PendingTxWellTyped ==
    \A tx \in ledger.pendingTxs : IsTransactionRecord(tx)
```

**What It Checks:** Every pending transaction has valid:
- Transaction ID and signer
- Signature record
- Input and output UTXO sets
- Coordination state
- Phase and result

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

### INV_TYPE_All

**Definition:**
```tla
INV_TYPE_All ==
    /\ TypeOK
    /\ INV_TYPE_LedgerWellTyped
    /\ INV_TYPE_FramesWellTyped
    /\ INV_TYPE_TokenBagsWellTyped
    /\ INV_TYPE_PendingTxWellTyped
```

**What It Checks:** Conjunction of all type invariants.

**Usage:** Use as first invariant when debugging.

---

## Auth invariants

Authorization invariants ensure committed spends are authorized.

### INV_AUTH_ValidSpend

**Definition:**
```tla
INV_AUTH_ValidSpend ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsCommittedTx(tx) => ValidSignature(tx.signature, tx)
```

**What It Checks:** Every **committed** transaction has a signature that:
- Is from the declared signer
- Matches the transaction ID
- Commits to the transaction contents (inputs, outputs, coordination)

**What It Prevents:**
- Forged signatures
- Signature/content mismatch
- Replay of signatures on different transactions

**Dependencies:** Transaction records in `txHistory` are well-formed (by construction in the current spec).

---

### INV_AUTH_OwnerOnly

**Definition:**
```tla
INV_AUTH_OwnerOnly ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsCommittedTx(tx) => InputsOwnedBySigner(tx)
```

**What It Checks:** All input UTXOs of a **committed** transaction are owned by the transaction's signer.

**What It Prevents:**
- Spending someone else's UTXOs
- Authorization bypass

**Dependencies:** Transaction records in `txHistory` are well-formed (by construction in the current spec).

**Note:** Pending transactions are constructed via `SignTx` and `ReserveTx` in the current model, so invalid
pending signatures or owners are not explored unless you add adversarial actions.

---

## Balance invariants

Balance invariants ensure token conservation.

### INV_BALANCE_TxPreserved

**Definition:**
```tla
INV_BALANCE_TxPreserved ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsCommittedTx(tx) => BalancePreserved(tx)
```

**What It Checks:** For every committed transaction in history, the sum of input tokens equals the sum of output tokens.

**What It Prevents:**
- Token inflation (creating tokens from nothing)
- Token destruction (losing tokens)

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

### INV_BALANCE_PendingTxValid

**Definition:**
```tla
INV_BALANCE_PendingTxValid ==
    \A tx \in ledger.pendingTxs :
        IsComplete(tx.coordination) => BalancePreserved(tx)
```

**What It Checks:** Once a pending transaction's coordination is complete, balance must be preserved.

**What It Prevents:** Committing transactions with unbalanced token flows.

**Dependencies:** `INV_TYPE_PendingTxWellTyped`

---

### INV_BALANCE_NFTUnique

**Definition:**
```tla
INV_BALANCE_NFTUnique ==
    \A id \in TOKEN_IDS :
        Cardinality({u \in ledger.utxoSet : u.tokens["NFT"][id] > 0}) <= 1
```

**What It Checks:** Each NFT ID appears in at most one UTXO across the entire ledger.

**What It Prevents:**
- NFT duplication
- Multiple copies of unique assets

**Dependencies:** `INV_TYPE_TokenBagsWellTyped`

---

### INV_BALANCE_PendingOutputsNoNFTDuplication

**Definition:**
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

**What It Checks:** Once coordination is complete, pending outputs do not duplicate NFTs among themselves or with unrelated live UTXOs.

**What It Prevents:** NFT duplication races during finalization.

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

### INV_BALANCE_NoOverflow

**Definition:**
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

**What It Checks:** Each per-asset input and output sum fits within `MAX_TOKEN_TOTAL`.

**What It Prevents:** Arithmetic overflow or wrap-around when summing token quantities.

**Implementation note:** Real implementations must use checked arithmetic and reject any transaction whose per-asset totals exceed the maximum representable value.

**Dependencies:** `INV_TYPE_PendingTxWellTyped`

---

## Linear invariants

Linear type invariants ensure UTXOs are consumed exactly once.

### INV_LINEAR_NoDoubleSpend

**Definition:**
```tla
INV_LINEAR_NoDoubleSpend ==
    {u.id : u \in ledger.utxoSet} \cap ledger.consumedSet = {}
```

**What It Checks:** No UTXO ID appears in both the active set and consumed set.

**What It Prevents:**
- Double-spending a UTXO
- Resurrection of consumed UTXOs

**Dependencies:** `INV_TYPE_LedgerWellTyped`

**Note:** This is the main double-spend prevention invariant.

---

### INV_LINEAR_ConsumedTracked

**Definition:**
```tla
INV_LINEAR_ConsumedTracked ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsCommittedTx(tx) => \A u \in tx.inputs : u.id \in ledger.consumedSet
```

**What It Checks:** All inputs of committed transactions are in the consumed set.

**What It Prevents:** Losing track of spent UTXOs (enables replay).

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

### INV_LINEAR_UniqueActiveIds

**Definition:**
```tla
INV_LINEAR_UniqueActiveIds ==
    \A u1, u2 \in ledger.utxoSet : u1 # u2 => u1.id # u2.id
```

**What It Checks:** All active UTXOs have distinct IDs.

**What It Prevents:** Multiple UTXOs with same ID (ambiguous spending).

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

### INV_LINEAR_NoDoubleConsume

**Definition:**
```tla
INV_LINEAR_NoDoubleConsume ==
    \A tx1, tx2 \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        (tx1 # tx2 /\ IsCommittedTx(tx1) /\ IsCommittedTx(tx2)) =>
            ({u.id : u \in tx1.inputs} \cap {u.id : u \in tx2.inputs} = {})
```

**What It Checks:** No two committed transactions share any input UTXO.

**What It Prevents:** Same UTXO being input to multiple committed transactions.

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

### INV_LINEAR_NoDuplication

**Definition:**
```tla
INV_LINEAR_NoDuplication ==
    \A tx1, tx2 \in ledger.pendingTxs :
        (tx1 # tx2) =>
            ({u.id : u \in tx1.inputs} \cap {u.id : u \in tx2.inputs} = {})
```

**What It Checks:** No two pending transactions share any input UTXO.

**What It Prevents:** Concurrent transactions attempting to spend same UTXO.

**Dependencies:** `INV_TYPE_PendingTxWellTyped`

---

### INV_LINEAR_PendingInputsNotConsumed

**Definition:**
```tla
INV_LINEAR_PendingInputsNotConsumed ==
    \A tx \in ledger.pendingTxs :
        ({u.id : u \in tx.inputs} \cap ledger.consumedSet = {})
```

**What It Checks:** Pending transactions never reference UTXO IDs already in `consumedSet`.

**What It Prevents:** Committing or executing with already-consumed inputs.

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

## IEUTxO / Chunk invariants

These invariants align pending/committing transactions and committed history with IEUTxO-style validity.

### INV_IEUTXO_PendingShape

**Definition:**
```tla
INV_IEUTXO_PendingShape ==
    \A tx \in ledger.pendingTxs :
        /\ UniqueInputIds(tx)
        /\ UniqueOutputIds(tx)
        /\ InputOutputDisjoint(tx)
```

**What It Checks:** Pending transactions have unique inputs/outputs and no input-output overlap.

---

### INV_IEUTXO_CommittingNonEmpty

**Definition:**
```tla
INV_IEUTXO_CommittingNonEmpty ==
    \A tx \in ledger.pendingTxs :
        tx.phase = "Committing" => TxNonEmpty(tx)
```

**What It Checks:** Committing transactions have at least one input and one output.

---

### INV_IEUTXO_PendingOutputsFresh

**Definition:**
```tla
INV_IEUTXO_PendingOutputsFresh ==
    \A tx \in ledger.pendingTxs :
        OutputIds(tx) \cap (UTXOIds(ledger.utxoSet) \cup ledger.consumedSet) = {}
```

**What It Checks:** Pending outputs are fresh relative to live + consumed IDs.

---

### INV_IEUTXO_PendingOutputsDistinct

**Definition:**
```tla
INV_IEUTXO_PendingOutputsDistinct ==
    \A tx1, tx2 \in ledger.pendingTxs :
        tx1 # tx2 => OutputIds(tx1) \cap OutputIds(tx2) = {}
```

**What It Checks:** Distinct pending txs do not mint the same output IDs.

---

### INV_IEUTXO_CommittingInputsValidate

**Definition:**
```tla
INV_IEUTXO_CommittingInputsValidate ==
    \A tx \in ledger.pendingTxs :
        tx.phase = "Committing" => TxInputsValidate(ledger, tx)
```

**What It Checks:** Committing tx inputs validate against ledger + signature rules.

---

### INV_IEUTXO_CommittingProofsVerified

**Definition:**
```tla
INV_IEUTXO_CommittingProofsVerified ==
    \A tx \in ledger.pendingTxs :
        tx.phase = "Committing" => AllTxProofsVerified(tx)
```

**What It Checks:** Committing txs have verified proof commitments.

---

### INV_IEUTXO_CommittedHistoryChunk

**Definition:**
```tla
INV_IEUTXO_CommittedHistoryChunk ==
    ChunkValid(CommittedHistory)
```

**What It Checks:** The committed history (filtered to committed txs) forms a valid IEUTxO chunk.

---

## Lock invariants

Lock invariants ensure reservation system correctness.

### INV_LOCK_Exclusive

**Definition:**
```tla
INV_LOCK_Exclusive ==
    \A u \in ledger.utxoSet :
        u.lockedBy = NO_TX \/ (\E tx \in ledger.pendingTxs : tx.id = u.lockedBy)
```

**What It Checks:** If a UTXO is locked, the locking transaction exists in pending set.

**What It Prevents:**
- Orphaned locks (UTXO locked by nonexistent tx)
- Lock escape after tx completion

**Dependencies:** `INV_TYPE_LedgerWellTyped`, `INV_TYPE_PendingTxWellTyped`

---

### INV_LOCK_ValidReservation

**Definition:**
```tla
INV_LOCK_ValidReservation ==
    \A u \in ledger.utxoSet :
        u.lockedBy # NO_TX => u.state \in {"Reserved", "Executing", "Suspended_at_Effect"}
```

**What It Checks:** Locked UTXOs are in Reserved, Executing, or Suspended_at_Effect state.

**What It Prevents:** Lock on UTXO in incompatible state.

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

### INV_LOCK_ConsistentSet

**Definition:**
```tla
INV_LOCK_ConsistentSet ==
    LockedSetConsistent(ledger)

\* Where:
LockedSetConsistent(ledger) ==
    ledger.lockedSet = {u.id : u \in {x \in ledger.utxoSet : x.lockedBy # NO_TX}}
```

**What It Checks:** The `lockedSet` exactly equals IDs of locked UTXOs.

**What It Prevents:** Inconsistency between lock tracking structures.

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

### INV_LOCK_AtomicRelease

**Definition:**
```tla
INV_LOCK_AtomicRelease ==
    \A u \in ledger.utxoSet :
        u.state \in {"Reserved", "Executing", "Suspended_at_Effect"} => u.lockedBy # NO_TX
```

**What It Checks:** If a UTXO is in a lock-required state, it must still be locked.

**What It Prevents:** Non-atomic lock release leaving a UTXO in a locked state with `lockedBy = NO_TX`.

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

## Optimistic concurrency invariants

These invariants capture read/write-set consistency for the optimistic variant.

### INV_OPT_ReadSetConsistent

**Definition:**
```tla
INV_OPT_ReadSetConsistent ==
    \A tx \in ledger.pendingTxs :
        tx.readSet = {u.id : u \in tx.readSnapshot}
```

**What It Checks:** Read-set equals the IDs in the read snapshot.

---

### INV_OPT_WriteSetConsistent

**Definition:**
```tla
INV_OPT_WriteSetConsistent ==
    \A tx \in ledger.pendingTxs :
        tx.writeSet = {u.id : u \in tx.inputs} \cup {u.id : u \in tx.outputs}
```

**What It Checks:** Write-set equals inputs plus newly created outputs.

---

## Lifecycle invariants

Lifecycle invariants ensure state machine correctness.

### INV_LIFECYCLE_ConsumedIsFinal

**Definition:**
```tla
INV_LIFECYCLE_ConsumedIsFinal ==
    \A u \in ledger.utxoSet : u.state # "Consumed"
```

**What It Checks:** No UTXO in the active set is in Consumed state.

**What It Prevents:** Zombie UTXOs (consumed but still active).

**Note:** Consumed UTXOs are removed from `utxoSet` and their IDs added to `consumedSet`.

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

### INV_LIFECYCLE_ActiveAreLive

**Definition:**
```tla
INV_LIFECYCLE_ActiveAreLive ==
    \A u \in ledger.utxoSet : IsLive(u)
```

**What It Checks:** All UTXOs in active set are live (not consumed).

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

### INV_LIFECYCLE_FrameConsistent

**Definition:**
```tla
INV_LIFECYCLE_FrameConsistent ==
    \A u \in ledger.utxoSet :
        /\ (u.state = "Created") => (u.frame.pc = 0)
        /\ (u.state = "Consumed") => (u.frame.pc = -1)
        /\ (u.state = "Suspended_at_Yield") => (u.frame.pc >= 0)
        /\ (u.state = "Suspended_at_Effect") => (u.frame.pc >= 0)
```

**What It Checks:** Frame PC (program counter) is consistent with UTXO state:
- Created: PC = 0 (initial)
- Consumed: PC = -1 (terminated)
- Suspended: PC >= 0 (valid resumption point)

**What It Prevents:** State/frame mismatch.

**Dependencies:** `INV_TYPE_FramesWellTyped`

---

## Effect invariants

Effect invariants ensure algebraic effects are properly handled, including interface routing and handler stack consistency.

### INV_EFFECT_MustBeHandled

**Definition:**
```tla
INV_EFFECT_MustBeHandled ==
    \A tx \in ledger.pendingTxs :
        IsComplete(tx.coordination) => ~HasPendingEffects(tx.coordination)
```

**What It Checks:** When coordination is complete, no pending effects remain.

**What It Prevents:**
- Committing with unhandled effects
- Effect leaks

**Dependencies:** `INV_TYPE_PendingTxWellTyped`

---

### INV_EFFECT_NoOrphans

**Definition:**
```tla
INV_EFFECT_NoOrphans ==
    \A tx \in ledger.pendingTxs :
        \A e \in FcnRange(tx.coordination.effectStack) :
            e.sourceUtxoId \in {u.id : u \in tx.inputs}
```

**What It Checks:** All effects on the stack came from input UTXOs of that transaction.

**What It Prevents:** Effects from unknown sources.

**Dependencies:** `INV_TYPE_PendingTxWellTyped`

---

### INV_EFFECT_SourceSuspended

**Definition:**
```tla
INV_EFFECT_SourceSuspended ==
    \A tx \in ledger.pendingTxs :
        \A e \in PendingEffects(tx.coordination.effectStack) :
            /\ UTXOExistsInLedger(ledger, e["sourceUtxoId"])
            /\ LET u == GetUTXO(ledger, e["sourceUtxoId"])
               IN /\ u.state = "Suspended_at_Effect"
                  /\ u.lockedBy = tx.id
```

**What It Checks:** Any pending effect is tied to a UTXO that is suspended for effects and still locked by the same transaction.

**What It Prevents:** Handling effects from UTXOs that are no longer in a suspended effect state.

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

### INV_EFFECT_ContinuationMatch

**Definition:**
```tla
INV_EFFECT_ContinuationMatch ==
    \A tx \in ledger.pendingTxs :
        \A e \in PendingEffects(tx.coordination.effectStack) :
            /\ UTXOExistsInLedger(ledger, e["sourceUtxoId"])
            /\ LET u == GetUTXO(ledger, e["sourceUtxoId"])
               IN e["continuationId"] = u.frame.pc
```

**What It Checks:** Each pending effect’s continuation matches the suspended UTXO’s current program counter.

**What It Prevents:** Resuming the wrong continuation for a given UTXO.

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

### INV_EFFECT_StackDepthBounded

**Definition:**
```tla
INV_EFFECT_StackDepthBounded ==
    \A tx \in ledger.pendingTxs :
        Len(tx.coordination.effectStack) <= MAX_EFFECT_DEPTH
```

**What It Checks:** Pending effect stacks never exceed the configured depth bound.

**What It Prevents:** Effect-stack growth that could lead to resource exhaustion.

**Dependencies:** `INV_TYPE_PendingTxWellTyped`

---

### INV_OPT_EFFECT_SourceSuspended

**Definition:**
```tla
INV_OPT_EFFECT_SourceSuspended ==
    \A tx \in ledger.pendingTxs :
        \A e \in PendingEffects(tx.coordination.effectStack) :
            \E u \in tx.inputs :
                /\ u.id = e["sourceUtxoId"]
                /\ u.state = "Suspended_at_Effect"
```

**What It Checks:** For optimistic execution, pending effects originate from suspended input UTXOs.

---

### INV_OPT_EFFECT_ContinuationMatch

**Definition:**
```tla
INV_OPT_EFFECT_ContinuationMatch ==
    \A tx \in ledger.pendingTxs :
        \A e \in PendingEffects(tx.coordination.effectStack) :
            \E u \in tx.inputs :
                /\ u.id = e["sourceUtxoId"]
                /\ e["continuationId"] = u.frame.pc
```

**What It Checks:** Pending effect continuations match the input UTXO frame for optimistic runs.

---

### INV_EFFECT_InterfaceConsistent

**Definition:**
```tla
INV_EFFECT_InterfaceConsistent ==
    \A tx \in ledger.pendingTxs :
        \A e \in FcnRange(tx.coordination.effectStack) :
            e.interfaceId \in InterfaceIdRange
```

**What It Checks:** All effects target valid interfaces.

---

### INV_EFFECT_PerInterfaceDepth

**Definition:**
```tla
INV_EFFECT_PerInterfaceDepth ==
    \A tx \in ledger.pendingTxs :
        \A iface \in InterfaceIdRange :
            Len(tx.coordination.handlerStacks[iface]) <= MAX_HANDLER_DEPTH
```

**What It Checks:** Handler stacks stay within depth bounds per interface.

---

### INV_EFFECT_EffectsMatchInstalledHandlers

**Definition:**
```tla
INV_EFFECT_EffectsMatchInstalledHandlers ==
    \A tx \in ledger.pendingTxs :
        \A e \in PendingEffects(tx.coordination.effectStack) :
            HasHandlerFor(tx.coordination.handlerStacks, e.interfaceId)
```

**What It Checks:** Pending effects have handlers installed for their interface.

---

### INV_EFFECT_InstalledHandlersConsistent

**Definition:**
```tla
INV_EFFECT_InstalledHandlersConsistent ==
    \A tx \in ledger.pendingTxs :
        InstalledHandlersConsistent(tx.coordination)
```

**What It Checks:** `installedHandlers` matches the contents of handler stacks.

---

### INV_EFFECT_ValidHandlerStacks

**Definition:**
```tla
INV_EFFECT_ValidHandlerStacks ==
    \A tx \in ledger.pendingTxs :
        ValidHandlerStacks(tx.coordination)
```

**What It Checks:** Handler stacks are well-formed and obey depth bounds.

---

## Proof invariants

Proof invariants ensure proof commitments are well-scoped and correctly phased.

### INV_PROOF_IntegrityBound

**Definition:**
```tla
INV_PROOF_IntegrityBound ==
    \A proof \in ledger.proofStore :
        proof.ivcProcessId \in ProcessIdRange /\ IsValidProof(proof)
```

**What It Checks:** Proofs in the ledger have valid process IDs and structure.

---

### INV_PROOF_NoDoubleProof

**Definition:**
```tla
INV_PROOF_NoDoubleProof ==
    \A p1, p2 \in ledger.proofStore :
        (p1 # p2 /\ IsPendingProof(p1) /\ IsPendingProof(p2)) =>
            p1.ivcProcessId # p2.ivcProcessId
```

**What It Checks:** No two pending proofs share a process ID.

---

### INV_PROOF_VerificationInvariant

**Definition:**
```tla
INV_PROOF_VerificationInvariant ==
    \A proof \in ledger.proofStore :
        IsVerifiedProof(proof) => proof.phase = "Verified" /\ proof.verified
```

**What It Checks:** Verified proofs have consistent phase/flag state.

---

### INV_PROOF_ConsistentPhase

**Definition:**
```tla
INV_PROOF_ConsistentPhase ==
    \A tx \in ledger.pendingTxs :
        (tx.proofPhase = "Verified") => \A p \in tx.proofCommitments : p.verified
```

**What It Checks:** Transaction proof phase agrees with its commitments.

---

### INV_PROOF_CommittedVerified

**Definition:**
```tla
INV_PROOF_CommittedVerified ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsCommittedTx(tx) => AllTxProofsVerified(tx)
```

**What It Checks:** Committed transactions have verified proofs.

---

### INV_PROOF_ActiveProofsConsistent

**Definition:**
```tla
INV_PROOF_ActiveProofsConsistent ==
    ledger.activeProofs = {p.ivcProcessId : p \in ledger.proofStore}
```

**What It Checks:** `activeProofs` matches the proof store.

---

### INV_PROOF_TxProofsInLedger

**Definition:**
```tla
INV_PROOF_TxProofsInLedger ==
    \A tx \in ledger.pendingTxs :
        \A p \in tx.proofCommitments :
            \E lp \in ledger.proofStore :
                lp.ivcProcessId = p.ivcProcessId
```

**What It Checks:** Transaction proof commitments exist in the ledger store.

---

### INV_PROOF_ValidIVCConfig

**Definition:**
```tla
INV_PROOF_ValidIVCConfig ==
    \A tx \in ledger.pendingTxs :
        ValidIVCConfig(tx.coordination)
```

**What It Checks:** Coordination IVC configuration stays within valid ranges.

---

## Frame invariants

### INV_FRAME_Integrity

**Definition:**
```tla
INV_FRAME_Integrity ==
    \A u \in ledger.utxoSet :
        u.frame.hash = ComputeFrameHash(u.frame.pc, u.frame.locals, u.frame.methodId)
```

**What It Checks:** Frame hash matches computed hash of frame contents.

**What It Prevents:**
- Frame tampering
- Hash/content mismatch

**Dependencies:** `INV_TYPE_FramesWellTyped`

---

## ATK invariants

Attack prevention invariants guard against specific attack vectors.

### INV_ATK_NoReplay

**Definition:**
```tla
INV_ATK_NoReplay ==
    \A id \in ledger.consumedSet : ~(\E u \in ledger.utxoSet : u.id = id)
```

**What It Checks:** Consumed IDs do not appear in active UTXO set.

**What It Prevents:** Replay attacks using old UTXO IDs.

**Note:** Equivalent to `INV_LINEAR_NoDoubleSpend` but stated differently.

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

### INV_ATK_IdMonotonic

**Definition:**
```tla
INV_ATK_IdMonotonic ==
    /\ \A u \in ledger.utxoSet : u.id < ledger.nextUtxoId
    /\ \A id \in ledger.consumedSet : id < ledger.nextUtxoId
```

**What It Checks:** All UTXO IDs (active and consumed) are less than `nextUtxoId`.

**What It Prevents:**
- Using future IDs
- ID allocation bypass

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

### INV_ATK_NoNegativeTokens

**Definition:**
```tla
INV_ATK_NoNegativeTokens ==
    \A u \in ledger.utxoSet :
        \A t \in TOKEN_TYPES : \A id \in TOKEN_IDS : u.tokens[t][id] >= 0
```

**What It Checks:** All token quantities are non-negative.

**What It Prevents:** Negative balance exploitation.

**Dependencies:** `INV_TYPE_TokenBagsWellTyped`

---

## Rollback invariants

### INV_ROLLBACK_NoLeak

**Definition:**
```tla
INV_ROLLBACK_NoLeak ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsFailedTx(tx) =>
            /\ {u.id : u \in tx.outputs} \cap {u.id : u \in ledger.utxoSet} = {}
            /\ {u.id : u \in tx.inputs} \cap ledger.consumedSet = {}
```

**What It Checks:** For failed transactions:
1. No outputs leaked into active UTXO set
2. No inputs marked as consumed

**What It Prevents:**
- Output leaks on failure
- Inputs consumed by failed tx

**Dependencies:** `INV_TYPE_LedgerWellTyped`

---

## Safety vs liveness (primer)

**Safety** properties say “nothing bad ever happens.” In TLA+ they are usually invariants checked
at every state (e.g., no double-spend). Safety checks do **not** require fairness.

**Liveness** properties say “something good eventually happens.” They use temporal operators like:

- `[] P` — always P
- `<> P` — eventually P
- `P ~> Q` — if P happens, Q eventually happens (leads-to)

Liveness often requires **fairness** assumptions to avoid spurious counterexamples where the
system simply never schedules an enabled action. In this spec:

- `LIVE_TxEventuallyCommits`, `LIVE_TxEventuallyTerminates`, and `LIVE_CanReturnToIdle` use **weak fairness** (`MC_FairSpec`)
- `LIVE_EffectsEventuallyHandled` uses **strong fairness** (`MC_StrongFairSpec`)

---

## Liveness properties

Liveness properties require fairness conditions. Use `FairSpec` or `StrongFairSpec`.

### LIVE_TxEventuallyCommits

**Definition:**
```tla
LIVE_TxEventuallyCommits ==
    \A txId \in TxIdRange :
        (<>[]CommitEnabled(txId)) => <>CommittedTxId(txId)
```

**What It Checks:** If a transaction’s commit is eventually *always enabled* (stability), it eventually commits.

**Requires:** `FairSpec` (weak fairness on commit)

---

### LIVE_TxEventuallyTerminates

**Definition:**
```tla
LIVE_TxEventuallyTerminates ==
    \A txId \in TxIdRange :
        []( PendingTxId(txId) => <>~PendingTxId(txId) )
```

**What It Checks:** Every pending transaction eventually completes (commits or aborts).

**Requires:** `FairSpec` (weak fairness on commit/abort)

---

### LIVE_EffectsEventuallyHandled

**Definition:**
```tla
PendingTxHasEffects(txId) ==
    PendingTxId(txId) /\ HasPendingEffects(GetPendingTx(ledger, txId).coordination)

PendingTxEffectsCleared(txId) ==
    ~PendingTxId(txId) \/
        (PendingTxId(txId) /\ ~HasPendingEffects(GetPendingTx(ledger, txId).coordination))

LIVE_EffectsEventuallyHandled ==
    \A txId \in TxIdRange :
        PendingTxHasEffects(txId) ~> PendingTxEffectsCleared(txId)
```

**What It Checks:** If a pending transaction has outstanding effects, those effects are eventually cleared or the transaction leaves pending.

**Requires:** `StrongFairSpec` (strong fairness on `HandleTxEffect`)

---

### LIVE_CanReturnToIdle

**Definition:**
```tla
LIVE_CanReturnToIdle ==
    []<>(ledger.pendingTxs = {})
```

**What It Checks:** The system can always return to a state with no pending transactions.

**Requires:** `FairSpec`

---

## Combined safety invariant

### INV_Safety

**Definition:**
```tla
INV_Safety ==
    /\ INV_TYPE_All
    /\ INV_AUTH_ValidSpend
    /\ INV_AUTH_OwnerOnly
    /\ INV_BALANCE_TxPreserved
    /\ INV_BALANCE_NFTUnique
    /\ INV_BALANCE_PendingOutputsNoNFTDuplication
    /\ INV_BALANCE_NoOverflow
    /\ INV_LINEAR_NoDoubleSpend
    /\ INV_LINEAR_ConsumedTracked
    /\ INV_LINEAR_UniqueActiveIds
    /\ INV_LINEAR_PendingInputsNotConsumed
    /\ INV_IEUTXO_PendingShape
    /\ INV_IEUTXO_CommittingNonEmpty
    /\ INV_IEUTXO_PendingOutputsFresh
    /\ INV_IEUTXO_PendingOutputsDistinct
    /\ INV_IEUTXO_CommittingInputsValidate
    /\ INV_IEUTXO_CommittingProofsVerified
    /\ INV_IEUTXO_CommittedHistoryChunk
    /\ INV_LOCK_Exclusive
    /\ INV_LOCK_ValidReservation
    /\ INV_LOCK_ConsistentSet
    /\ INV_LOCK_AtomicRelease
    /\ INV_OPT_ReadSetConsistent
    /\ INV_OPT_WriteSetConsistent
    /\ INV_LIFECYCLE_ConsumedIsFinal
    /\ INV_EFFECT_MustBeHandled
    /\ INV_EFFECT_SourceSuspended
    /\ INV_EFFECT_ContinuationMatch
    /\ INV_EFFECT_StackDepthBounded
    /\ INV_EFFECT_InterfaceConsistent
    /\ INV_EFFECT_PerInterfaceDepth
    /\ INV_EFFECT_ValidHandlerStacks
    /\ INV_PROOF_IntegrityBound
    /\ INV_PROOF_NoDoubleProof
    /\ INV_PROOF_VerificationInvariant
    /\ INV_PROOF_ConsistentPhase
    /\ INV_PROOF_CommittedVerified
    /\ INV_PROOF_ActiveProofsConsistent
    /\ INV_PROOF_ValidIVCConfig
    /\ INV_ATK_NoReplay
    /\ INV_ATK_IdMonotonic
    /\ INV_ATK_NoNegativeTokens
    /\ INV_ROLLBACK_NoLeak
```

**Usage:** Check all safety properties at once. If this fails, check individual invariants to identify the issue.

---

## Checking order

When debugging invariant violations:

1. **INV_TYPE_All** - Check types first
2. **INV_LINEAR_NoDoubleSpend** - Core safety property
3. **INV_IEUTXO_*** - Chunk validity / serializability scaffolding
4. **INV_LOCK_*** - Reservation correctness
5. **INV_OPT_*** / **INV_OPT_EFFECT_*** - Optimistic consistency
6. **INV_LIFECYCLE_*** - State machine correctness
7. **INV_BALANCE_*** - Token conservation
8. **INV_AUTH_*** - Authorization
9. **INV_EFFECT_*** - Effect handling (including interfaces)
10. **INV_PROOF_*** - Proof lifecycle correctness
11. **INV_ATK_*** - Attack vectors
12. **INV_ROLLBACK_*** - Failure handling

