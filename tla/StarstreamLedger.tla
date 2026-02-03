--------------------------- MODULE StarstreamLedger ---------------------------
(***************************************************************************
 * Global Ledger State for Starstream
 ***************************************************************************)

EXTENDS StarstreamTypes, StarstreamFrame, StarstreamUTXO, StarstreamEffects,
        StarstreamCoordination, StarstreamTransaction

(***************************************************************************
 * LEDGER STATE TYPE
 ***************************************************************************)

LedgerStateSet ==
    [utxoSet: SUBSET UTXORecordSet,
     consumedSet: SUBSET UTXOIdRange,
     lockedSet: SUBSET UTXOIdRange,
     nextUtxoId: UTXOIdRange \cup {UTXO_ID_BOUND + 1},
     nextTxId: TxIdRange \cup {UTXO_ID_BOUND + 1},
     pendingTxs: SUBSET TransactionRecordSet,
     txHistory: Seq(TransactionRecordSet),
     proofStore: SUBSET ProofCommitmentType,   \* Global proof store
     activeProofs: SUBSET ProcessIdRange]       \* Process IDs with active proofs

(***************************************************************************
 * LEDGER CONSTRUCTORS
 ***************************************************************************)

EmptyLedger ==
    [utxoSet |-> {},
     consumedSet |-> {},
     lockedSet |-> {},
     nextUtxoId |-> 1,
     nextTxId |-> 1,
     pendingTxs |-> {},
     txHistory |-> <<>>,
     proofStore |-> {},
     activeProofs |-> {}]

GenesisLedger(initialUtxos) ==
    [utxoSet |-> initialUtxos,
     consumedSet |-> {},
     lockedSet |-> {},
     nextUtxoId |-> Cardinality(initialUtxos) + 1,
     nextTxId |-> 1,
     pendingTxs |-> {},
     txHistory |-> <<>>,
     proofStore |-> {},
     activeProofs |-> {}]

(***************************************************************************
 * LEDGER PREDICATES
 ***************************************************************************)

IsValidLedger(ledger) ==
    /\ \A u \in ledger.utxoSet : IsUTXORecord(u)
    /\ ledger.nextUtxoId <= UTXO_ID_BOUND + 1
    /\ ledger.nextTxId <= UTXO_ID_BOUND + 1
    /\ \A tx \in ledger.pendingTxs : IsTransactionRecord(tx)
    /\ \A p \in ledger.proofStore : IsProofCommitment(p)
    /\ ledger.activeProofs \subseteq ProcessIdRange

HasPendingTxs(ledger) == ledger.pendingTxs # {}

IsUsedId(ledger, id) ==
    \/ \E u \in ledger.utxoSet : u.id = id
    \/ id \in ledger.consumedSet

UTXOExistsInLedger(ledger, utxoId) ==
    \E u \in ledger.utxoSet : u.id = utxoId

GetUTXO(ledger, utxoId) ==
    CHOOSE u \in ledger.utxoSet : u.id = utxoId

GetPendingTx(ledger, txId) ==
    CHOOSE tx \in ledger.pendingTxs : tx.id = txId

(***************************************************************************
 * IEUTxO LEDGER SPEC (Draft)
 *
 * This section provides an IEUTxO-style view of the ledger and transaction
 * structure, with chunk composition rules for sequences of transactions.
 ***************************************************************************)

UTXOIds(utxoSet) == {u.id : u \in utxoSet}

InputIds(tx) == {u.id : u \in tx.inputs}
OutputIds(tx) == {u.id : u \in tx.outputs}

UniqueInputIds(tx) == UniqueUTXOIds(tx.inputs)

TxNonEmpty(tx) == /\ InputIds(tx) # {} /\ OutputIds(tx) # {}

FreshOutputIds(ledger, tx) ==
    OutputIds(tx) \cap (UTXOIds(ledger.utxoSet) \cup ledger.consumedSet) = {}

InputsLiveInLedger(ledger, tx) ==
    InputIds(tx) \subseteq UTXOIds(ledger.utxoSet)

InputsNotConsumed(ledger, tx) ==
    InputIds(tx) \cap ledger.consumedSet = {}

InputById(tx, id) ==
    CHOOSE u \in tx.inputs : u.id = id

OutputById(tx, id) ==
    CHOOSE o \in tx.outputs : o.id = id

\* Output-level validator predicate (owner + tx signature for now)
OutputValidatorAccepts(out, tx) ==
    /\ out.owner = tx.signer
    /\ ValidSignature(tx.signature, tx)

TxInputsValidate(ledger, tx) ==
    \A u \in tx.inputs :
        /\ UTXOExistsInLedger(ledger, u.id)
        /\ GetUTXO(ledger, u.id) = u
        /\ OutputValidatorAccepts(u, tx)

IEUTxOTxValid(ledger, tx) ==
    /\ IsTransactionRecord(tx)
    /\ TxNonEmpty(tx)
    /\ UniqueInputIds(tx)
    /\ UniqueOutputIds(tx)
    /\ InputOutputDisjoint(tx)
    /\ InputsLiveInLedger(ledger, tx)
    /\ InputsNotConsumed(ledger, tx)
    /\ FreshOutputIds(ledger, tx)
    /\ TxInputsValidate(ledger, tx)

\* Sequence helpers for chunk validity
IsTxSeq(txs) == \A i \in 1..Len(txs) : IsTransactionRecord(txs[i])

SeqInputIds(txs) == UNION {InputIds(txs[i]) : i \in 1..Len(txs)}
SeqOutputIds(txs) == UNION {OutputIds(txs[i]) : i \in 1..Len(txs)}

SeqInputsDistinct(txs) ==
    \A i, j \in 1..Len(txs) : i # j => InputIds(txs[i]) \cap InputIds(txs[j]) = {}

SeqOutputsDistinct(txs) ==
    \A i, j \in 1..Len(txs) : i # j => OutputIds(txs[i]) \cap OutputIds(txs[j]) = {}

InputMatchedByEarlierOutput(txs, idx, id) ==
    \E j \in 1..(idx - 1) : id \in OutputIds(txs[j])

InputRefsEarlierOutputs(txs) ==
    \A idx \in 1..Len(txs) :
        \A id \in InputIds(txs[idx]) :
            LET outIdxs == {j \in 1..Len(txs) : id \in OutputIds(txs[j])}
            IN outIdxs = {} \/ \A j \in outIdxs : j < idx

InputValidatedByEarlierOutputs(txs) ==
    \A idx \in 1..Len(txs) :
        \A id \in InputIds(txs[idx]) :
            IF InputMatchedByEarlierOutput(txs, idx, id)
            THEN \A j \in 1..(idx - 1) :
                    id \in OutputIds(txs[j]) =>
                        OutputValidatorAccepts(OutputById(txs[j], id), txs[idx])
            ELSE TRUE

ChunkValid(txs) ==
    /\ IsTxSeq(txs)
    /\ \A idx \in 1..Len(txs) :
        /\ TxNonEmpty(txs[idx])
        /\ UniqueInputIds(txs[idx])
        /\ UniqueOutputIds(txs[idx])
        /\ InputOutputDisjoint(txs[idx])
    /\ SeqInputsDistinct(txs)
    /\ SeqOutputsDistinct(txs)
    /\ InputRefsEarlierOutputs(txs)
    /\ InputValidatedByEarlierOutputs(txs)

UnspentInputs(txs) ==
    {id \in SeqInputIds(txs) :
        \A idx \in 1..Len(txs) :
            id \in InputIds(txs[idx]) => ~InputMatchedByEarlierOutput(txs, idx, id)}

OutputMatchedByLaterInput(txs, idx, id) ==
    \E k \in (idx + 1)..Len(txs) : id \in InputIds(txs[k])

UnspentOutputs(txs) ==
    {id \in SeqOutputIds(txs) :
        \A idx \in 1..Len(txs) :
            id \in OutputIds(txs[idx]) => ~OutputMatchedByLaterInput(txs, idx, id)}

BlockchainValid(txs) == ChunkValid(txs) /\ UnspentInputs(txs) = {}

LedgerSatisfiesExternalInputs(ledger, txs) ==
    \A idx \in 1..Len(txs) :
        \A id \in InputIds(txs[idx]) :
            IF InputMatchedByEarlierOutput(txs, idx, id)
            THEN TRUE
            ELSE /\ UTXOExistsInLedger(ledger, id)
                 /\ GetUTXO(ledger, id) = InputById(txs[idx], id)
                 /\ OutputValidatorAccepts(GetUTXO(ledger, id), txs[idx])

LedgerAcceptsChunk(ledger, txs) ==
    /\ ChunkValid(txs)
    /\ UnspentInputs(txs) \subseteq UTXOIds(ledger.utxoSet)
    /\ UnspentInputs(txs) \cap ledger.consumedSet = {}
    /\ SeqOutputIds(txs) \cap (UTXOIds(ledger.utxoSet) \cup ledger.consumedSet) = {}
    /\ LedgerSatisfiesExternalInputs(ledger, txs)

(***************************************************************************
 * LEDGER UTXO OPERATIONS
 ***************************************************************************)

AllocateId(ledger) == ledger.nextUtxoId
AllocateTxId(ledger) == ledger.nextTxId

CreateUTXOInLedger(ledger, contract, owner, datum, tokens) ==
    LET id == AllocateId(ledger)
        newUtxo == NewUTXO(id, contract, owner, datum, tokens)
    IN [ledger EXCEPT
        !.utxoSet = @ \cup {newUtxo},
        !.nextUtxoId = id + 1]

UpdateUTXOInLedger(ledger, updatedUtxo) ==
    [ledger EXCEPT !.utxoSet = UpdateUTXOInSet(@, updatedUtxo)]

ReserveUTXOsInSet(utxoSet, inputIds, txId) ==
    {IF u.id \in inputIds THEN ReserveUTXO(u, txId) ELSE u : u \in utxoSet}

BeginExecuteUTXOsInSet(utxoSet, inputIds) ==
    {IF u.id \in inputIds THEN BeginExecuteUTXO(u) ELSE u : u \in utxoSet}

EndExecuteUTXOsInSet(utxoSet, inputIds) ==
    {IF u.id \in inputIds THEN EndExecuteUTXO(u) ELSE u : u \in utxoSet}

ReleaseUTXOsInSet(utxoSet, inputUtxos) ==
    LET ids == {u.id : u \in inputUtxos}
        inputMap == [id \in ids |-> CHOOSE u \in inputUtxos : u.id = id]
    IN {IF u.id \in ids THEN ReleaseReservation(inputMap[u.id]) ELSE u : u \in utxoSet}

(***************************************************************************
 * LEDGER TRANSACTION OPERATIONS
 ***************************************************************************)

BeginTxInLedger(ledger, inputIds, signer) ==
    LET txId == AllocateTxId(ledger)
        inputUtxos == {u \in ledger.utxoSet : u.id \in inputIds}
        tx == TransactionWithInputs(txId, signer, inputUtxos)
    IN [ledger EXCEPT
        !.utxoSet = ReserveUTXOsInSet(@, inputIds, txId),
        !.lockedSet = @ \cup inputIds,
        !.pendingTxs = @ \cup {tx},
        !.nextTxId = txId + 1]

BeginOptTxInLedger(ledger, inputIds, signer) ==
    LET txId == AllocateTxId(ledger)
        inputUtxos == {u \in ledger.utxoSet : u.id \in inputIds}
        tx == TransactionWithInputs(txId, signer, inputUtxos)
    IN [ledger EXCEPT
        !.pendingTxs = @ \cup {tx},
        !.nextTxId = txId + 1]

UpdatePendingTx(ledger, txId, newTx) ==
    [ledger EXCEPT
        !.pendingTxs = {IF t.id = txId THEN newTx ELSE t : t \in ledger.pendingTxs}]

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

AbortTxInLedger(ledger, txId, reason) ==
    LET tx == GetPendingTx(ledger, txId)
        failedTx == AbortTransaction(tx, reason)
        inputIds == {u.id : u \in tx.inputs}
        restoredSet == ReleaseUTXOsInSet(ledger.utxoSet, tx.inputs)
    IN [ledger EXCEPT
        !.utxoSet = restoredSet,
        !.lockedSet = @ \ inputIds,
        !.pendingTxs = @ \ {tx},
        !.txHistory = Append(@, failedTx)]

AbortOptTxInLedger(ledger, txId, reason) ==
    LET tx == GetPendingTx(ledger, txId)
        failedTx == AbortTransaction(tx, reason)
    IN [ledger EXCEPT
        !.pendingTxs = @ \ {tx},
        !.txHistory = Append(@, failedTx)]

(***************************************************************************
 * LEDGER PROOF OPERATIONS
 ***************************************************************************)

\* Add a proof to the ledger's proof store
AddProofToLedger(ledger, proof) ==
    [ledger EXCEPT
        !.proofStore = @ \cup {proof},
        !.activeProofs = @ \cup {proof.ivcProcessId}]

\* Remove a proof from the ledger's proof store
RemoveProofFromLedger(ledger, proof) ==
    LET remainingProofs == ledger.proofStore \ {proof}
        remainingActive == {p.ivcProcessId : p \in remainingProofs}
    IN [ledger EXCEPT
        !.proofStore = remainingProofs,
        !.activeProofs = remainingActive]

\* Update a proof in the ledger's proof store
UpdateProofInLedger(ledger, oldProof, newProof) ==
    [ledger EXCEPT
        !.proofStore = (@ \ {oldProof}) \cup {newProof}]

\* Get proof for a process ID from ledger
GetProofForProcess(ledger, pid) ==
    FindProofByProcessId(ledger.proofStore, pid)

\* Check if ledger has active proof for process
HasActiveProofFor(ledger, pid) ==
    pid \in ledger.activeProofs

\* Get all verified proofs in ledger
LedgerVerifiedProofs(ledger) ==
    VerifiedProofs(ledger.proofStore)

\* Get all pending proofs in ledger
LedgerPendingProofs(ledger) ==
    PendingProofs(ledger.proofStore)

(***************************************************************************
 * LEDGER INVARIANTS
 ***************************************************************************)

NoDoubleSpend(ledger) ==
    {u.id : u \in ledger.utxoSet} \cap ledger.consumedSet = {}

UniqueActiveIds(ledger) ==
    UniqueUTXOIds(ledger.utxoSet)

AllActiveLive(ledger) ==
    \A u \in ledger.utxoSet : IsLive(u)

ValidNextId(ledger) ==
    /\ \A u \in ledger.utxoSet : u.id < ledger.nextUtxoId
    /\ \A id \in ledger.consumedSet : id < ledger.nextUtxoId

LockedSetConsistent(ledger) ==
    ledger.lockedSet = {u["id"] : u \in {x \in ledger.utxoSet : x["lockedBy"] # NO_TX}}

TotalTokensPreserved(ledger, ledgerNext) ==
    TokenBagsEqual(SumTokenBags(ledger.utxoSet), SumTokenBags(ledgerNext.utxoSet))

=============================================================================
