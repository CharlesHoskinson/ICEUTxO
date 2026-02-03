----------------------- MODULE StarstreamSpecOptimistic -----------------------
(***************************************************************************
 * Optimistic concurrency variant for Starstream.
 *
 * No reservations/locks are taken during execution. Transactions record a
 * read snapshot and validate at commit time that inputs are unchanged.
 ***************************************************************************) 

EXTENDS StarstreamSpec

(***************************************************************************
 * HELPERS
 ***************************************************************************) 

ReadSnapshotConsistent(tx) ==
    tx.readSet = {u.id : u \in tx.readSnapshot}

ReadSetValid(tx, ledg) ==
    /\ ReadSnapshotConsistent(tx)
    /\ \A u \in tx.readSnapshot :
        /\ UTXOExistsInLedger(ledg, u.id)
        /\ GetUTXO(ledg, u.id) = u

OutputsFresh(tx, ledg) ==
    OutputIds(tx) \cap (UTXOIds(ledg.utxoSet) \cup ledg.consumedSet) = {}

MarkRead(tx, utxoId) ==
    SignTx([tx EXCEPT !.readSet = tx.readSet \cup {utxoId}])

MarkWrite(tx, utxoId) ==
    SignTx([tx EXCEPT !.writeSet = tx.writeSet \cup {utxoId}])

UpdateInput(tx, updatedUtxo) ==
    [tx EXCEPT !.inputs = UpdateUTXOInSet(tx.inputs, updatedUtxo)]

GetTxInput(tx, utxoId) ==
    CHOOSE u \in tx.inputs : u.id = utxoId

BeginExecuteInputs(tx) ==
    LET ids == {u.id : u \in tx.inputs}
    IN [tx EXCEPT !.inputs = BeginExecuteUTXOsInSet(tx.inputs, ids)]

EndExecuteInputs(tx) ==
    LET ids == {u.id : u \in tx.inputs}
    IN [tx EXCEPT !.inputs = EndExecuteUTXOsInSet(tx.inputs, ids)]

(***************************************************************************
 * ACTIONS: OPTIMISTIC TRANSACTION LIFECYCLE
 ***************************************************************************) 

OptBeginTx(inputIds, signer) ==
    /\ Cardinality(ledger.pendingTxs) < MAX_PENDING_TXS
    /\ inputIds # {}
    /\ Cardinality(inputIds) <= MAX_TX_INPUTS
    /\ inputIds \subseteq {u.id : u \in ledger.utxoSet}
    /\ \A id \in inputIds : CanQuery(GetUTXO(ledger, id))
    /\ \A id \in inputIds : GetUTXO(ledger, id).owner = signer
    /\ ledger' = BeginOptTxInLedger(ledger, inputIds, signer)

OptBeginExecute(txId) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Reserve"
    /\ LET tx == GetPendingTx(ledger, txId)
           tx1 == BeginExecuteInputs(tx)
           tx2 == BeginExecution(tx1)
       IN ledger' = UpdatePendingTx(ledger, txId, tx2)

OptStartProcessing(txId, calls) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ LET tx == GetPendingTx(ledger, txId)
       IN /\ IsGathering(tx.coordination)
          /\ calls \in SampleCallSeqsForInputs(tx.coordination.inputUtxos)
          /\ LET newCoord == BeginProcessing(tx.coordination, calls)
                 newTx == UpdateCoordination(tx, newCoord)
             IN ledger' = UpdatePendingTx(ledger, txId, newTx)

OptProcessTxCall(txId, callResult) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ LET tx == GetPendingTx(ledger, txId)
           coord == tx.coordination
       IN /\ IsProcessing(coord)
          /\ ~AllCallsExecuted(coord)
          /\ LET call == CurrentCall(coord)
             IN /\ call.targetUtxo \in InputIds(tx)
                /\ LET utxo == GetTxInput(tx, call.targetUtxo)
                       updatedUtxo == ExecuteCallOnUTXO(call, utxo)
                       tx1 == UpdateInput(tx, updatedUtxo)
                       tx2 == ExecuteCallInTx(tx1, callResult)
                       tx3 == MarkRead(tx2, call.targetUtxo)
                       tx4 == IF call.callType \in {"Mutate", "Consume"}
                              THEN MarkWrite(tx3, call.targetUtxo)
                              ELSE tx3
                   IN /\ CanExecuteCall(call, utxo)
                      /\ utxo.state = "Executing"
                      /\ ledger' = UpdatePendingTx(ledger, txId, tx4)

OptRaiseTxEffect(txId, effectKind, utxoId, continuationId, tag, payload) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ utxoId \in InputIds(GetPendingTx(ledger, txId))
    /\ LET tx == GetPendingTx(ledger, txId)
       IN /\ IsProcessing(tx.coordination)
          /\ utxoId \notin UTXOsWithPendingEffects(tx.coordination)
          /\ LET utxo == GetTxInput(tx, utxoId)
                 updatedUtxo == RaiseEffectUTXO(utxo, utxo.frame.pc)
                 tx1 == UpdateInput(tx, updatedUtxo)
                 tx2 == RaiseEffectInTx(tx1, effectKind, utxoId, continuationId, tag, payload)
                 tx3 == MarkRead(tx2, utxoId)
                 tx4 == MarkWrite(tx3, utxoId)
             IN /\ utxo.state = "Executing"
                /\ continuationId = utxo.frame.pc
                /\ ledger' = UpdatePendingTx(ledger, txId, tx4)

OptHandleTxEffect(txId, handlerResult) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ LET tx == GetPendingTx(ledger, txId)
           effect == PeekEffect(tx.coordination.effectStack)
       IN /\ IsProcessing(tx.coordination)
          /\ HasPendingEffects(tx.coordination)
          /\ effect.sourceUtxoId \in InputIds(tx)
          /\ LET utxo == GetTxInput(tx, effect.sourceUtxoId)
                 updatedUtxo == ResumeEffectUTXO(utxo, utxo.frame.pc, handlerResult)
                 tx1 == UpdateInput(tx, updatedUtxo)
                 tx2 == HandleEffectInTx(tx1, handlerResult)
                 tx3 == MarkWrite(tx2, effect.sourceUtxoId)
              IN /\ utxo.state = "Suspended_at_Effect"
                 /\ ledger' = UpdatePendingTx(ledger, txId, tx3)

OptProcessPTBEvent(txId) ==
    \/ \E result \in DatumValues :
        OptProcessTxCall(txId, result)
    \/ \E kind \in EffectKinds, id \in UTXOIdRange,
          cont \in ContinuationIdRange, tag \in EffectTags, payload \in DatumValues :
        OptRaiseTxEffect(txId, kind, id, cont, tag, payload)
    \/ \E result \in DatumValues :
        OptHandleTxEffect(txId, result)

OptFinalizeTx(txId, outputSpecs) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ LET tx == GetPendingTx(ledger, txId)
       IN /\ IsProcessing(tx.coordination)
          /\ AllCallsExecuted(tx.coordination)
          /\ ~HasPendingEffects(tx.coordination)
          /\ Len(outputSpecs) <= MAX_TX_OUTPUTS
          /\ Len(outputSpecs) > 0
          /\ LET outputs == {SuspendedUTXO(
                               ledger.nextUtxoId + i - 1,
                               outputSpecs[i].contract,
                               outputSpecs[i].owner,
                               outputSpecs[i].datum,
                               outputSpecs[i].tokens,
                               FrameAtYield(1, [v \in VarNames |-> NULL], 0))
                             : i \in 1..Len(outputSpecs)}
                 tx1 == EndExecuteInputs(tx)
                 tx2 == FinalizeOutputs(tx1, outputSpecs, outputs)
             IN /\ ledger' = [UpdatePendingTx(ledger, txId, tx2) EXCEPT
                               !.nextUtxoId = ledger.nextUtxoId + Len(outputSpecs)]

OptBeginCommit(txId) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ LET tx == GetPendingTx(ledger, txId)
       IN /\ IsComplete(tx.coordination)
          /\ BalancePreserved(tx)
          /\ ReadSetValid(tx, ledger)
          /\ OutputsFresh(tx, ledger)
          /\ \A u \in tx.inputs : u.state = "Reserved"
          /\ ValidSignature(tx.signature, tx)
          /\ InputsOwnedBySigner(tx)
          /\ AllTxProofsVerified(tx)
          /\ ledger' = UpdatePendingTx(ledger, txId, BeginCommitting(tx))

OptCommitTx(txId) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Committing"
    /\ LET tx == GetPendingTx(ledger, txId)
       IN /\ ReadSetValid(tx, ledger)
          /\ OutputsFresh(tx, ledger)
          /\ AllTxProofsVerified(tx)
          /\ ledger' = CommitTxInLedger(ledger, txId)

OptStartRollback(txId, reason) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase \in {"Reserve", "Executing", "Committing"}
    /\ ledger' = UpdatePendingTx(ledger, txId, BeginRollback(GetPendingTx(ledger, txId), reason))

OptFinishRollback(txId) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Rollback"
    /\ ledger' = AbortOptTxInLedger(ledger, txId, GetPendingTx(ledger, txId).result)

(***************************************************************************
 * NEXT STATE RELATION
 ***************************************************************************) 

OptNext ==
    \/ \E c \in SampleContracts, o \in SampleOwners, d \in SampleDatums, t \in SampleTokenBags :
        CreateUTXO(c, o, d, t)

    \/ \E ids \in SUBSET {u.id : u \in ledger.utxoSet}, s \in SampleOwners :
        /\ ids # {}
        /\ Cardinality(ids) <= MAX_TX_INPUTS
        /\ OptBeginTx(ids, s)

    \/ \E txId \in TxIdRange : OptBeginExecute(txId)

    \/ \E tx \in ledger.pendingTxs :
        \E calls \in SampleCallSeqsForInputs(tx.coordination.inputUtxos) :
            OptStartProcessing(tx.id, calls)

    \/ \E txId \in TxIdRange :
        OptProcessPTBEvent(txId)

    \/ \E txId \in TxIdRange, specs \in SampleOutputSpecs :
        /\ Len(specs) <= MAX_TX_OUTPUTS
        /\ Len(specs) > 0
        /\ OptFinalizeTx(txId, specs)

    \/ \E txId \in TxIdRange : OptBeginCommit(txId)

    \/ \E txId \in TxIdRange : OptCommitTx(txId)

    \/ \E txId \in TxIdRange, reason \in DatumValues : OptStartRollback(txId, reason)

    \/ \E txId \in TxIdRange : OptFinishRollback(txId)

    \/ \E id \in UTXOIdRange : QueryUTXO(id)

    \/ \E id \in UTXOIdRange, pc \in PCRange, d \in DatumValues :
        YieldUTXO(id, pc, d)

OptStuttering == UNCHANGED vars

OptNextOrStutter == OptNext \/ OptStuttering

(***************************************************************************
 * FAIRNESS CONDITIONS
 ***************************************************************************) 

OptWeakFairness ==
    /\ WF_vars(\E txId \in TxIdRange : OptBeginCommit(txId))
    /\ WF_vars(\E txId \in TxIdRange : OptCommitTx(txId))
    /\ WF_vars(\E txId \in TxIdRange, reason \in DatumValues : OptStartRollback(txId, reason))
    /\ WF_vars(\E txId \in TxIdRange : OptFinishRollback(txId))

OptStrongFairness ==
    /\ SF_vars(\E txId \in TxIdRange, result \in DatumValues : OptHandleTxEffect(txId, result))

(***************************************************************************
 * SPECIFICATIONS
 ***************************************************************************) 

OptSpec == Init /\ [][OptNext]_vars

OptFairSpec == OptSpec /\ OptWeakFairness

OptStrongFairSpec == OptFairSpec /\ OptStrongFairness

=============================================================================
