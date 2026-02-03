--------------------------- MODULE StarstreamSpec ---------------------------
(***************************************************************************
 * Starstream UTXO/Transaction Protocol
 *
 * See IMPLEMENTATION-STATUS.md for Starstream compiler alignment.
 ***************************************************************************)

EXTENDS StarstreamTypes, StarstreamFrame, StarstreamUTXO, StarstreamEffects, StarstreamPTB,
        StarstreamCoordination, StarstreamTransaction, StarstreamLedger, StarstreamAuth,
        StarstreamProof, StarstreamSessionProtocol

(***************************************************************************
 * STATE VARIABLES
 ***************************************************************************)

VARIABLES
    ledger

vars == <<ledger>>

(***************************************************************************
 * TYPE INVARIANT
 ***************************************************************************)

TypeOK ==
    /\ IsValidLedger(ledger)

(***************************************************************************
 * INITIAL STATE
 ***************************************************************************)

AdaId == CHOOSE i \in TOKEN_IDS : TRUE

AdaBag(amount) ==
    [t \in TOKEN_TYPES |-> [id \in TOKEN_IDS |-> IF t = "ADA" /\ id = AdaId THEN amount ELSE 0]]

SampleTokenBags == {EmptyTokenBag, AdaBag(2)}

SampleOwners == {"Alice", "Bob"}
SampleContracts == {"Token"}
SampleDatums == {"Empty", "Locked"}
SampleFrameHashes ==
    {ComputeFrameHash(0, [v \in VarNames |-> NULL], 0),
     ComputeFrameHash(1, [v \in VarNames |-> NULL], 0)}

SampleOutputSpec1 ==
    [datum |-> "Empty",
     tokens |-> AdaBag(2),
     contract |-> "Token",
     owner |-> "Alice"]

SampleOutputSpec2 ==
    [datum |-> "Empty",
     tokens |-> AdaBag(2),
     contract |-> "Token",
     owner |-> "Bob"]

SampleOutputSpecs == {<<SampleOutputSpec1>>, <<SampleOutputSpec2>>}

InitialUTXOs ==
    LET utxo1 == SuspendedUTXO(1, "Token", "Alice", "Empty",
                               AdaBag(2),
                               FrameAtYield(1, [v \in VarNames |-> NULL], 0))
        utxo2 == SuspendedUTXO(2, "Token", "Bob", "Empty",
                               AdaBag(2),
                               FrameAtYield(1, [v \in VarNames |-> NULL], 0))
    IN {utxo1, utxo2}

Init ==
    /\ ledger = GenesisLedger(InitialUTXOs)

(***************************************************************************
 * ACTIONS: UTXO CREATION
 ***************************************************************************)

CreateUTXO(contract, owner, datum, tokens) ==
    /\ Cardinality(ledger.utxoSet) < MAX_UTXOS
    /\ ledger.nextUtxoId <= UTXO_ID_BOUND
    /\ ledger' = CreateUTXOInLedger(ledger, contract, owner, datum, tokens)

(***************************************************************************
 * ACTIONS: TRANSACTION LIFECYCLE (Reserve/Execute/Commit/Rollback)
 ***************************************************************************)

ReserveTx(inputIds, signer) ==
    /\ Cardinality(ledger.pendingTxs) < MAX_PENDING_TXS
    /\ inputIds # {}
    /\ Cardinality(inputIds) <= MAX_TX_INPUTS
    /\ inputIds \subseteq {u.id : u \in ledger.utxoSet}
    /\ \A tx \in ledger.pendingTxs :
        ({u.id : u \in tx.inputs} \cap inputIds = {})
    /\ \A id \in inputIds : CanReserve(GetUTXO(ledger, id))
    /\ \A id \in inputIds : GetUTXO(ledger, id).owner = signer
    /\ ledger' = BeginTxInLedger(ledger, inputIds, signer)

BeginExecute(txId) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Reserve"
    /\ LET tx == GetPendingTx(ledger, txId)
           newTx == BeginExecution(tx)
           inputIds == {u.id : u \in tx.inputs}
           updatedUtxoSet == BeginExecuteUTXOsInSet(ledger.utxoSet, inputIds)
       IN /\ \A u \in tx.inputs : GetUTXO(ledger, u.id).state = "Reserved"
          /\ \A u \in tx.inputs : GetUTXO(ledger, u.id).lockedBy = txId
          /\ ledger' =
                UpdatePendingTx([ledger EXCEPT !.utxoSet = updatedUtxoSet], txId, newTx)

StartProcessing(txId, calls) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ LET tx == GetPendingTx(ledger, txId)
       IN /\ IsGathering(tx.coordination)
          /\ calls \in SampleCallSeqsForInputs(tx.coordination.inputUtxos)
          /\ LET newCoord == BeginProcessing(tx.coordination, calls)
                 newTx == UpdateCoordination(tx, newCoord)
             IN ledger' = UpdatePendingTx(ledger, txId, newTx)

ProcessTxCall(txId, callResult) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ LET tx == GetPendingTx(ledger, txId)
           coord == tx.coordination
       IN /\ IsProcessing(coord)
          /\ ~AllCallsExecuted(coord)
          /\ LET call == CurrentCall(coord)
             IN /\ call.targetUtxo \in coord.inputUtxos
                /\ UTXOExistsInLedger(ledger, call.targetUtxo)
                /\ LET utxo == GetUTXO(ledger, call.targetUtxo)
                       updatedUtxo == ExecuteCallOnUTXO(call, utxo)
                       newTx == ExecuteCallInTx(tx, callResult)
                   IN /\ CanExecuteCall(call, utxo)
                      /\ utxo.state = "Executing"
                      /\ utxo.lockedBy = txId
                      /\ ledger' = UpdatePendingTx(UpdateUTXOInLedger(ledger, updatedUtxo), txId, newTx)

(***************************************************************************
 * ACTIONS: PTB VALIDATION (trace-driven)
 ***************************************************************************)

StartPTB(txId, trace) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ LET tx == GetPendingTx(ledger, txId)
       IN /\ IsGathering(tx.coordination)
          /\ trace \in PTBTrace
          /\ LET newCoord == BeginProcessingPTB(tx.coordination, trace)
                 newTx == UpdateCoordination(tx, newCoord)
             IN ledger' = UpdatePendingTx(ledger, txId, newTx)

PTBAdvanceOnly(txId, tx, coord) ==
    LET newCoord == AdvancePTB(coord)
        newTx == UpdateCoordination(tx, newCoord)
    IN /\ SessionProtocolValid(newCoord)
       /\ ledger' = UpdatePendingTx(ledger, txId, newTx)

PTBRaise(txId, tx, coord, evt) ==
    /\ evt.kind = "Raise"
    /\ evt.utxoId \in {u.id : u \in tx.inputs}
    /\ GetUTXO(ledger, evt.utxoId).lockedBy = txId
    /\ IsProcessing(coord)
    /\ CoordHasHandlerFor(coord, evt.interfaceId)
    /\ evt.utxoId \notin UTXOsWithPendingEffects(coord)
    /\ LET utxo == GetUTXO(ledger, evt.utxoId)
           updatedUtxo == RaiseEffectUTXO(utxo, utxo.frame.pc)
           coord1 == RaiseOnInterfaceInCoord(coord, evt.effectKind, evt.utxoId,
                       evt.continuationId, evt.tag, evt.payload, evt.interfaceId, evt.witKind)
           coord2 == AdvancePTB(coord1)
           newTx == UpdateCoordination(tx, coord2)
       IN /\ utxo.state = "Executing"
          /\ evt.continuationId = utxo.frame.pc
          /\ SessionProtocolValid(coord2)
          /\ ledger' = UpdatePendingTx(UpdateUTXOInLedger(ledger, updatedUtxo), txId, newTx)

PTBResume(txId, tx, coord, evt) ==
    /\ evt.kind = "Resume"
    /\ IsProcessing(coord)
    /\ LET effects == PendingEffectsForInterface(coord, evt.interfaceId)
       IN /\ effects # {}
          /\ LET effect == CHOOSE e \in effects : TRUE
                 utxo == GetUTXO(ledger, effect.sourceUtxoId)
                 updatedUtxo == ResumeEffectUTXO(utxo, utxo.frame.pc, evt.handlerResult)
                 coord1 == HandleEffectInCoord(coord, evt.handlerResult)
                 coord2 == AdvancePTB(coord1)
                 newTx == UpdateCoordination(tx, coord2)
             IN /\ UTXOExistsInLedger(ledger, effect.sourceUtxoId)
                /\ utxo.state = "Suspended_at_Effect"
                /\ utxo.lockedBy = txId
                /\ SessionProtocolValid(coord2)
                /\ ledger' = UpdatePendingTx(UpdateUTXOInLedger(ledger, updatedUtxo), txId, newTx)

PTBInstall(txId, tx, coord, evt) ==
    /\ evt.kind = "Install"
    /\ LET handlerId == HandlerStackDepth(coord.handlerStacks, evt.interfaceId) + 1
           processId == UtxoToProcessId(CHOOSE id \in coord.inputUtxos : TRUE)
           handler == NewHandler(handlerId, evt.interfaceId, processId, evt.effectMask, 5)
           coord1 == InstallHandlerInCoord(coord, evt.interfaceId, handler)
           coord2 == AdvancePTB(coord1)
           newTx == UpdateCoordination(tx, coord2)
       IN /\ handlerId <= MAX_HANDLER_DEPTH
          /\ SessionProtocolValid(coord2)
          /\ ledger' = UpdatePendingTx(ledger, txId, newTx)

PTBUninstall(txId, tx, coord, evt) ==
    /\ evt.kind = "Uninstall"
    /\ CoordHasHandlerFor(coord, evt.interfaceId)
    /\ LET coord1 == UninstallHandlerInCoord(coord, evt.interfaceId)
           coord2 == AdvancePTB(coord1)
           newTx == UpdateCoordination(tx, coord2)
       IN /\ SessionProtocolValid(coord2)
          /\ ledger' = UpdatePendingTx(ledger, txId, newTx)

PTBRead(txId, tx, coord, evt) ==
    /\ evt.kind = "Read"
    /\ evt.utxoId \in {u.id : u \in tx.inputs}
    /\ UTXOExistsInLedger(ledger, evt.utxoId)
    /\ PTBAdvanceOnly(txId, tx, coord)

PTBSnapshot(txId, tx, coord, evt) ==
    /\ evt.kind = "Snapshot"
    /\ evt.utxoId \in {u.id : u \in tx.inputs}
    /\ UTXOExistsInLedger(ledger, evt.utxoId)
    /\ PTBAdvanceOnly(txId, tx, coord)

PTBLock(txId, tx, coord, evt) ==
    /\ evt.kind = "Lock"
    /\ evt.utxoId \in {u.id : u \in tx.inputs}
    /\ GetUTXO(ledger, evt.utxoId).lockedBy = txId
    /\ PTBAdvanceOnly(txId, tx, coord)

PTBConsume(txId, tx, coord, evt) ==
    /\ evt.kind = "Consume"
    /\ evt.utxoId \in {u.id : u \in tx.inputs}
    /\ PTBAdvanceOnly(txId, tx, coord)

PTBProduce(txId, tx, coord, evt) ==
    /\ evt.kind = "Produce"
    /\ evt.utxoId \in UTXOIdRange
    /\ PTBAdvanceOnly(txId, tx, coord)

ProcessPTBEvent(txId) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ LET tx == GetPendingTx(ledger, txId)
           coord == tx.coordination
       IN /\ IsProcessing(coord)
          /\ SessionProtocolValid(coord)
          /\ HasNextPTB(coord)
          /\ LET evt == NextPTBEvent(coord)
             IN CASE evt.kind = "Raise" -> PTBRaise(txId, tx, coord, evt)
                [] evt.kind = "Resume" -> HandleTxEffect(txId, evt.handlerResult)
                [] evt.kind = "Install" -> PTBInstall(txId, tx, coord, evt)
                [] evt.kind = "Uninstall" -> PTBUninstall(txId, tx, coord, evt)
                [] evt.kind = "Read" -> PTBRead(txId, tx, coord, evt)
                [] evt.kind = "Snapshot" -> PTBSnapshot(txId, tx, coord, evt)
                [] evt.kind = "Lock" -> PTBLock(txId, tx, coord, evt)
                [] evt.kind = "Consume" -> PTBConsume(txId, tx, coord, evt)
                [] evt.kind = "Produce" -> PTBProduce(txId, tx, coord, evt)
                [] OTHER -> FALSE

RaiseTxEffect(txId, effectKind, utxoId, continuationId, tag, payload) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ utxoId \in {u.id : u \in GetPendingTx(ledger, txId).inputs}
    /\ GetUTXO(ledger, utxoId).lockedBy = txId
    /\ LET tx == GetPendingTx(ledger, txId)
       IN /\ IsProcessing(tx.coordination)
          /\ utxoId \notin UTXOsWithPendingEffects(tx.coordination)
          /\ LET utxo == GetUTXO(ledger, utxoId)
                 updatedUtxo == RaiseEffectUTXO(utxo, utxo.frame.pc)
                 newTx == RaiseEffectInTx(tx, effectKind, utxoId, continuationId, tag, payload)
             IN /\ utxo.state = "Executing"
                /\ continuationId = utxo.frame.pc
                /\ ledger' = UpdatePendingTx(UpdateUTXOInLedger(ledger, updatedUtxo), txId, newTx)

HandleTxEffect(txId, handlerResult) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ LET tx == GetPendingTx(ledger, txId)
           coord == tx.coordination
       IN /\ IsProcessing(coord)
          /\ HasNextPTB(coord)
          /\ LET evt == NextPTBEvent(coord)
             IN /\ evt.kind = "Resume"
                /\ evt.handlerResult = handlerResult
                /\ PTBResume(txId, tx, coord, evt)

FinalizeTx(txId, outputSpecs) ==
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
                 inputIds == {u.id : u \in tx.inputs}
                 updatedUtxoSet == EndExecuteUTXOsInSet(ledger.utxoSet, inputIds)
                 newTx == FinalizeOutputs(tx, outputSpecs, outputs)
             IN /\ \A u \in tx.inputs : GetUTXO(ledger, u.id).state = "Executing"
                /\ ledger' = [UpdatePendingTx([ledger EXCEPT !.utxoSet = updatedUtxoSet], txId, newTx) EXCEPT
                               !.nextUtxoId = ledger.nextUtxoId + Len(outputSpecs)]

BeginCommit(txId) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ LET tx == GetPendingTx(ledger, txId)
           inputIds == {u.id : u \in tx.inputs}
       IN /\ IsComplete(tx.coordination)
          /\ BalancePreserved(tx)
          /\ \A u \in tx.inputs : GetUTXO(ledger, u.id).state = "Reserved"
          /\ \A u \in tx.inputs : GetUTXO(ledger, u.id).lockedBy = txId
          /\ ValidSignature(tx.signature, tx)
          /\ InputsOwnedBySigner(tx)
          /\ AllTxProofsVerified(tx)
          /\ ledger' = UpdatePendingTx(ledger, txId, BeginCommitting(tx))

CommitTx(txId) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Committing"
    /\ LET tx == GetPendingTx(ledger, txId)
       IN /\ \A u \in tx.inputs : GetUTXO(ledger, u.id).lockedBy = txId
          /\ AllTxProofsVerified(tx)
    /\ ledger' = CommitTxInLedger(ledger, txId)

StartRollback(txId, reason) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase \in {"Reserve", "Executing", "Committing"}
    /\ ledger' = UpdatePendingTx(ledger, txId, BeginRollback(GetPendingTx(ledger, txId), reason))

FinishRollback(txId) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Rollback"
    /\ ledger' = AbortTxInLedger(ledger, txId, GetPendingTx(ledger, txId).result)

InjectInvalidTx(inputIds, signer, badOwner) ==
    /\ inputIds # {}
    /\ Cardinality(inputIds) <= MAX_TX_INPUTS
    /\ inputIds \subseteq {u.id : u \in ledger.utxoSet}
    /\ \A id \in inputIds : CanReserve(GetUTXO(ledger, id))
    /\ \A tx \in ledger.pendingTxs :
        ({u.id : u \in tx.inputs} \cap inputIds = {})
    /\ badOwner \in OwnerAddrs
    /\ badOwner # signer
    /\ Cardinality(ledger.pendingTxs) < MAX_PENDING_TXS
    /\ LET txId == AllocateTxId(ledger)
           inputUtxos == {u \in ledger.utxoSet : u.id \in inputIds}
           inputIds0 == {u.id : u \in inputUtxos}
           tx0 == [id |-> txId,
                   signer |-> signer,
                   signature |-> MakeSignature(signer, txId, <<>>),
                   inputs |-> inputUtxos,
                   coordination |-> GatheringCoordination(inputIds0),
                   outputs |-> {},
                   readSet |-> inputIds0,
                   readSnapshot |-> inputUtxos,
                   writeSet |-> inputIds0,
                   phase |-> "Reserve",
                   result |-> NULL,
                   proofCommitments |-> {},
                   proofPhase |-> "NotStarted"]
           badSig == MakeSignature(badOwner, txId, TxContentsHash(tx0))
           tx == [tx0 EXCEPT !.signature = badSig]
       IN ledger' = [ledger EXCEPT !.pendingTxs = @ \cup {tx}, !.nextTxId = txId + 1]

RejectInvalidTx(txId, reason) ==
    /\ \E tx \in ledger.pendingTxs :
        /\ tx.id = txId
        /\ (~ValidSignature(tx.signature, tx) \/ ~InputsOwnedBySigner(tx))
    /\ ledger' = AbortTxInLedger(ledger, txId, reason)

(***************************************************************************
 * ACTIONS: UTXO OPERATIONS (Outside Transaction)
 ***************************************************************************)

QueryUTXO(utxoId) ==
    /\ UTXOExistsInLedger(ledger, utxoId)
    /\ CanQuery(GetUTXO(ledger, utxoId))
    /\ UNCHANGED ledger

YieldUTXO(utxoId, yieldPC, newDatum) ==
    /\ UTXOExistsInLedger(ledger, utxoId)
    /\ LET utxo == GetUTXO(ledger, utxoId)
       IN /\ utxo.state = "Created"
          /\ ledger' = UpdateUTXOInLedger(ledger, CreateToYield(utxo, yieldPC, newDatum))

(***************************************************************************
 * ACTIONS: HANDLER STACK OPERATIONS
 ***************************************************************************)

\* Install a handler on an interface for a transaction
InstallTxHandler(txId, interfaceId, effectMask) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ LET tx == GetPendingTx(ledger, txId)
           coord == tx.coordination
           handlerId == HandlerStackDepth(coord.handlerStacks, interfaceId) + 1
           processId == UtxoToProcessId(CHOOSE id \in coord.inputUtxos : TRUE)
           handler == NewHandler(handlerId, interfaceId, processId, effectMask, 5)
       IN /\ handlerId <= MAX_HANDLER_DEPTH
          /\ LET newCoord == InstallHandlerInCoord(coord, interfaceId, handler)
                 newTx == UpdateCoordination(tx, newCoord)
             IN ledger' = UpdatePendingTx(ledger, txId, newTx)

\* Uninstall the top handler from an interface for a transaction
UninstallTxHandler(txId, interfaceId) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ LET tx == GetPendingTx(ledger, txId)
           coord == tx.coordination
       IN /\ CoordHasHandlerFor(coord, interfaceId)
          /\ LET newCoord == UninstallHandlerInCoord(coord, interfaceId)
                 newTx == UpdateCoordination(tx, newCoord)
             IN ledger' = UpdatePendingTx(ledger, txId, newTx)

\* Raise an effect on a specific interface with WitLedger kind
RaiseTxEffectOnInterface(txId, effectKind, utxoId, continuationId,
                         tag, payload, interfaceId, witKind) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ utxoId \in {u.id : u \in GetPendingTx(ledger, txId).inputs}
    /\ GetUTXO(ledger, utxoId).lockedBy = txId
    /\ LET tx == GetPendingTx(ledger, txId)
       IN /\ IsProcessing(tx.coordination)
          /\ CoordHasHandlerFor(tx.coordination, interfaceId)
          /\ utxoId \notin UTXOsWithPendingEffects(tx.coordination)
          /\ LET utxo == GetUTXO(ledger, utxoId)
                 updatedUtxo == RaiseEffectUTXO(utxo, utxo.frame.pc)
                 newCoord == RaiseOnInterfaceInCoord(tx.coordination, effectKind,
                               utxoId, continuationId, tag, payload, interfaceId, witKind)
                 newTx == UpdateCoordination(tx, newCoord)
             IN /\ utxo.state = "Executing"
                /\ continuationId = utxo.frame.pc
                /\ ledger' = UpdatePendingTx(UpdateUTXOInLedger(ledger, updatedUtxo), txId, newTx)

\* Handle an effect on a specific interface
HandleTxEffectOnInterface(txId, interfaceId, handlerResult) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ LET tx == GetPendingTx(ledger, txId)
           effects == PendingEffectsForInterface(tx.coordination, interfaceId)
       IN /\ IsProcessing(tx.coordination)
          /\ effects # {}
          /\ LET effect == CHOOSE e \in effects : TRUE
             IN /\ UTXOExistsInLedger(ledger, effect.sourceUtxoId)
                /\ LET utxo == GetUTXO(ledger, effect.sourceUtxoId)
                       updatedUtxo == ResumeEffectUTXO(utxo, utxo.frame.pc, handlerResult)
                       newTx == HandleEffectInTx(tx, handlerResult)
                   IN /\ utxo.state = "Suspended_at_Effect"
                      /\ utxo.lockedBy = txId
                      /\ ledger' = UpdatePendingTx(UpdateUTXOInLedger(ledger, updatedUtxo), txId, newTx)

(***************************************************************************
 * ACTIONS: PROOF OPERATIONS
 ***************************************************************************)

\* Begin proof generation for a transaction
BeginTxProofGeneration(txId, processId, hash) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId /\ tx.phase = "Executing"
    /\ ~HasActiveProofFor(ledger, processId)
    /\ LET tx == GetPendingTx(ledger, txId)
           proof == IVCStepProof(processId, hash, 1)
           newTx == AddProofToTx(tx, proof)
           newLedger == AddProofToLedger(ledger, proof)
       IN ledger' = UpdatePendingTx(newLedger, txId, BeginTxProofGen(newTx, proof))

\* Verify a proof for a transaction
VerifyTxProof(txId, processId) ==
    /\ \E tx \in ledger.pendingTxs : tx.id = txId
    /\ HasActiveProofFor(ledger, processId)
    /\ LET tx == GetPendingTx(ledger, txId)
           oldProof == CHOOSE p \in tx.proofCommitments : p.ivcProcessId = processId
           ledgerProof == GetProofForProcess(ledger, processId)
       IN /\ IsPendingProof(oldProof)
          /\ LET newTx == MarkTxProofVerified(tx, oldProof)
                 newLedgerProof == MarkProofVerified(ledgerProof)
                 newLedger == UpdateProofInLedger(ledger, ledgerProof, newLedgerProof)
             IN ledger' = UpdatePendingTx(newLedger, txId, newTx)

(***************************************************************************
 * NEXT STATE RELATION
 ***************************************************************************)

Next ==
    \/ \E c \in SampleContracts, o \in SampleOwners, d \in SampleDatums, t \in SampleTokenBags :
        CreateUTXO(c, o, d, t)

    \/ \E ids \in SUBSET {u.id : u \in ledger.utxoSet}, s \in SampleOwners :
        /\ ids # {}
        /\ Cardinality(ids) <= MAX_TX_INPUTS
        /\ ReserveTx(ids, s)

    \/ \E txId \in TxIdRange : BeginExecute(txId)

    \/ \E tx \in ledger.pendingTxs :
        \E trace \in PTBTrace :
            StartPTB(tx.id, trace)

    \/ \E txId \in TxIdRange :
        ProcessPTBEvent(txId)

    \/ \E txId \in TxIdRange, specs \in SampleOutputSpecs :
        /\ Len(specs) <= MAX_TX_OUTPUTS
        /\ Len(specs) > 0
        /\ FinalizeTx(txId, specs)

    \/ \E txId \in TxIdRange : BeginCommit(txId)

    \/ \E txId \in TxIdRange : CommitTx(txId)

    \/ \E txId \in TxIdRange, reason \in DatumValues : StartRollback(txId, reason)

    \/ \E txId \in TxIdRange : FinishRollback(txId)

    \/ \E ids \in SUBSET {u.id : u \in ledger.utxoSet},
          s \in SampleOwners,
          bad \in SampleOwners :
        /\ ids # {}
        /\ Cardinality(ids) <= MAX_TX_INPUTS
        /\ s # bad
        /\ InjectInvalidTx(ids, s, bad)

    \/ \E txId \in TxIdRange, reason \in DatumValues : RejectInvalidTx(txId, reason)

    \/ \E id \in UTXOIdRange : QueryUTXO(id)

    \/ \E id \in UTXOIdRange, pc \in PCRange, d \in DatumValues :
        YieldUTXO(id, pc, d)

    \* Proof operations
    \/ \E txId \in TxIdRange, pid \in ProcessIdRange, hash \in SampleFrameHashes :
        BeginTxProofGeneration(txId, pid, hash)

    \/ \E txId \in TxIdRange, pid \in ProcessIdRange :
        VerifyTxProof(txId, pid)

Stuttering == UNCHANGED vars

NextOrStutter == Next \/ Stuttering

(***************************************************************************
 * FAIRNESS CONDITIONS
 ***************************************************************************)

WeakFairness ==
    /\ WF_vars(\E txId \in TxIdRange : BeginCommit(txId))
    /\ WF_vars(\E txId \in TxIdRange : CommitTx(txId))
    /\ WF_vars(\E txId \in TxIdRange, reason \in DatumValues : StartRollback(txId, reason))
    /\ WF_vars(\E txId \in TxIdRange : FinishRollback(txId))

StrongFairness ==
    /\ SF_vars(\E txId \in TxIdRange, result \in DatumValues : HandleTxEffect(txId, result))

(***************************************************************************
 * SPECIFICATIONS
 ***************************************************************************)

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WeakFairness

StrongFairSpec == FairSpec /\ StrongFairness

(***************************************************************************
 * HELPERS FOR MODEL CHECKING
 ***************************************************************************)

StateConstraint ==
    /\ Cardinality(ledger.utxoSet) <= MAX_UTXOS
    /\ Cardinality(ledger.consumedSet) <= UTXO_ID_BOUND
    /\ Cardinality(ledger.pendingTxs) <= MAX_PENDING_TXS
    /\ ledger.nextUtxoId <= UTXO_ID_BOUND + 1
    /\ \A tx \in ledger.pendingTxs :
        /\ Len(tx.coordination.effectStack) <= MAX_EFFECT_DEPTH
        /\ Len(tx.coordination.pendingCalls) <= MAX_TX_INPUTS
        /\ Len(tx.coordination.ptbTrace) <= MAX_TX_INPUTS
        /\ \A iface \in InterfaceIdRange :
            Len(tx.coordination.handlerStacks[iface]) <= MAX_HANDLER_DEPTH
        /\ Cardinality(tx.proofCommitments) <= MAX_TX_INPUTS
    /\ Len(ledger.txHistory) <= 3
    /\ Cardinality(ledger.proofStore) <= MAX_PENDING_TXS * MAX_TX_INPUTS

ActionConstraint == TRUE

=============================================================================
