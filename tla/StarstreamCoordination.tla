------------------------ MODULE StarstreamCoordination ------------------------
(***************************************************************************
 * Coordination Script Execution for Starstream
 ***************************************************************************)

EXTENDS StarstreamTypes, StarstreamFrame, StarstreamUTXO, StarstreamEffects, StarstreamPTB

(***************************************************************************
 * METHOD CALL RECORD TYPE
 ***************************************************************************)

MethodCallRecordSet ==
    [callType: CallTypes,
     targetUtxo: UTXOIdRange,
     methodId: MethodIdRange,
     args: DatumValues,
     executed: BOOLEAN,
     result: DatumValues \cup {NULL}]

(***************************************************************************
 * COORDINATION STATE TYPE
 ***************************************************************************)

CoordinationStateSet ==
    [phase: CoordPhases,
     inputUtxos: SUBSET UTXOIdRange,
     pendingCalls: Seq(MethodCallRecordSet),
     callIndex: 0..10,
     outputSpecs: Seq([datum: DatumValues, tokens: TokenBagType, contract: ContractIds, owner: OwnerAddrs]),
     effectStack: Seq(EffectRecordSet),
     handlerStacks: [InterfaceIdRange -> Seq(HandlerRecordSet)],  \* Per-interface handler stacks
     installedHandlers: SUBSET HandlerRecordSet,                   \* All installed handlers
     ptbTrace: PTBTrace,                                            \* PTB validation trace
     ptbIndex: 0..MAX_TX_INPUTS,                                    \* Next PTB event index
     ivcConfig: IVCStateConfigType]                                \* IVC state configuration

\* Structural predicates (avoid enumerating large record sets in TLC)
IsMethodCallRecord(call) ==
    /\ call.callType \in CallTypes
    /\ call.targetUtxo \in UTXOIdRange
    /\ call.methodId \in MethodIdRange
    /\ call.args \in DatumValues
    /\ call.executed \in BOOLEAN
    /\ call.result \in DatumValues \cup {NULL}

IsOutputSpecRecord(spec) ==
    /\ spec.datum \in DatumValues
    /\ spec.tokens \in TokenBagType
    /\ spec.contract \in ContractIds
    /\ spec.owner \in OwnerAddrs

IsHandlerRecord(handler) ==
    /\ handler.handlerId \in 1..MAX_HANDLER_DEPTH
    /\ handler.interfaceId \in InterfaceIdRange
    /\ handler.installedBy \in ProcessIdRange
    /\ handler.effectMask \subseteq EffectTags
    /\ handler.priority \in 0..10

IsCoordinationState(coord) ==
    /\ coord.phase \in CoordPhases
    /\ coord.inputUtxos \subseteq UTXOIdRange
    /\ \A i \in 1..Len(coord.pendingCalls) : IsMethodCallRecord(coord.pendingCalls[i])
    /\ coord.callIndex \in 0..10
    /\ \A i \in 1..Len(coord.outputSpecs) : IsOutputSpecRecord(coord.outputSpecs[i])
    /\ \A i \in 1..Len(coord.effectStack) : IsEffectRecord(coord.effectStack[i])
    /\ \A iface \in InterfaceIdRange :
        /\ \A i \in 1..Len(coord.handlerStacks[iface]) :
            IsHandlerRecord(coord.handlerStacks[iface][i])
    /\ \A h \in coord.installedHandlers : IsHandlerRecord(h)
    /\ coord.ptbTrace \in PTBTrace
    /\ coord.ptbIndex \in 0..MAX_TX_INPUTS
    /\ coord.ptbIndex <= Len(coord.ptbTrace)
    /\ coord.ivcConfig.id_curr \in ProcessIdRange \cup {-1}
    /\ coord.ivcConfig.id_prev \in ProcessIdRange \cup {-1}
    /\ coord.ivcConfig.activation \in ActivationStates
    /\ coord.ivcConfig.safe_to_ledger \in BOOLEAN

(***************************************************************************
 * METHOD CALL CONSTRUCTORS
 ***************************************************************************)

QueryCall(utxoId, method, arguments) ==
    [callType |-> "Query",
     targetUtxo |-> utxoId,
     methodId |-> method,
     args |-> arguments,
     executed |-> FALSE,
     result |-> NULL]

MutateCall(utxoId, method, arguments) ==
    [callType |-> "Mutate",
     targetUtxo |-> utxoId,
     methodId |-> method,
     args |-> arguments,
     executed |-> FALSE,
     result |-> NULL]

ConsumeCall(utxoId, method, arguments) ==
    [callType |-> "Consume",
     targetUtxo |-> utxoId,
     methodId |-> method,
     args |-> arguments,
     executed |-> FALSE,
     result |-> NULL]

(***************************************************************************
 * SAMPLE CALL SETS (for TLC enumeration)
 ***************************************************************************)

SampleCallTargets(inputIds) == inputIds
SampleCallsForInputs(inputIds) ==
    {QueryCall(id, 0, "Empty") : id \in SampleCallTargets(inputIds)} \cup
    {MutateCall(id, 0, "Locked") : id \in SampleCallTargets(inputIds)} \cup
    {ConsumeCall(id, 0, "Empty") : id \in SampleCallTargets(inputIds)}

SampleCallSeqsForInputs(inputIds) ==
    {<<>>} \cup {<<c>> : c \in SampleCallsForInputs(inputIds)}

(***************************************************************************
 * COORDINATION CONSTRUCTORS
 ***************************************************************************)

InitCoordination ==
    [phase |-> "NotStarted",
     inputUtxos |-> {},
     pendingCalls |-> <<>>,
     callIndex |-> 0,
     outputSpecs |-> <<>>,
     effectStack |-> EmptyEffectStack,
     handlerStacks |-> EmptyHandlerStacks,
     installedHandlers |-> {},
     ptbTrace |-> <<>>,
     ptbIndex |-> 0,
     ivcConfig |-> DefaultIVCConfig]

GatheringCoordination(inputs) ==
    [phase |-> "Gathering",
     inputUtxos |-> inputs,
     pendingCalls |-> <<>>,
     callIndex |-> 0,
     outputSpecs |-> <<>>,
     effectStack |-> EmptyEffectStack,
     handlerStacks |-> EmptyHandlerStacks,
     installedHandlers |-> {},
     ptbTrace |-> <<>>,
     ptbIndex |-> 0,
     ivcConfig |-> DefaultIVCConfig]

\* Coordination with custom IVC config
GatheringCoordinationWithIVC(inputs, ivcCfg) ==
    [phase |-> "Gathering",
     inputUtxos |-> inputs,
     pendingCalls |-> <<>>,
     callIndex |-> 0,
     outputSpecs |-> <<>>,
     effectStack |-> EmptyEffectStack,
     handlerStacks |-> EmptyHandlerStacks,
     installedHandlers |-> {},
     ptbTrace |-> <<>>,
     ptbIndex |-> 0,
     ivcConfig |-> ivcCfg]

(***************************************************************************
 * COORDINATION PREDICATES
 ***************************************************************************)

IsInitialCoordination(coord) == coord.phase = "NotStarted"
IsGathering(coord) == coord.phase = "Gathering"
IsProcessing(coord) == coord.phase = "Processing"
IsFinalizing(coord) == coord.phase = "Finalizing"
IsComplete(coord) == coord.phase = "Complete"

AllCallsExecuted(coord) == coord.callIndex >= Len(coord.pendingCalls)
HasPendingEffects(coord) == PendingEffects(coord.effectStack) # {}

CurrentCall(coord) ==
    IF coord.callIndex < Len(coord.pendingCalls)
    THEN coord.pendingCalls[coord.callIndex + 1]
    ELSE NULL

HasNextPTB(coord) == coord.ptbIndex < Len(coord.ptbTrace)

NextPTBEvent(coord) == coord.ptbTrace[coord.ptbIndex + 1]

AdvancePTB(coord) == [coord EXCEPT !.ptbIndex = @ + 1]

BeginProcessingPTB(coord, trace) ==
    [coord EXCEPT
        !.phase = "Processing",
        !.ptbTrace = trace,
        !.ptbIndex = 0,
        !.pendingCalls = <<>>,
        !.callIndex = 0]

(***************************************************************************
 * COORDINATION PHASE TRANSITIONS (pure record updates)
 ***************************************************************************)

BeginGathering(coord, inputIds) ==
    [coord EXCEPT !.phase = "Gathering", !.inputUtxos = inputIds]

BeginProcessing(coord, calls) ==
    [coord EXCEPT !.phase = "Processing", !.pendingCalls = calls, !.callIndex = 0]

ExecuteNextCall(coord, result) ==
    LET idx == coord.callIndex + 1
        updatedCalls == [coord.pendingCalls EXCEPT
                         ![idx] = [@ EXCEPT !.executed = TRUE, !.result = result]]
    IN [coord EXCEPT !.pendingCalls = updatedCalls, !.callIndex = idx]

HandleEffectInCoord(coord, handlerResult) ==
    LET result == HandleTopEffect(coord.effectStack, handlerResult)
    IN [coord EXCEPT !.effectStack = result[1]]

BeginFinalizing(coord, outputs) ==
    [coord EXCEPT !.phase = "Finalizing", !.outputSpecs = outputs]

CompleteCoordination(coord) ==
    [coord EXCEPT !.phase = "Complete"]

(***************************************************************************
 * EFFECT INTEGRATION
 ***************************************************************************)

RaiseInCoordination(coord, effectKind, utxoId, continuationId, tag, payload) ==
    [coord EXCEPT
        !.effectStack = RaiseEffectOp(coord.effectStack, effectKind, utxoId, continuationId, tag, payload)]

\* Raise effect on a specific interface with WitLedger kind
RaiseOnInterfaceInCoord(coord, effectKind, utxoId, continuationId, tag, payload, iface, witKind) ==
    LET effect == NewEffectWithInterface(effectKind, utxoId, continuationId, tag, payload, iface, witKind)
    IN [coord EXCEPT !.effectStack = Append(@, effect)]

UTXOsWithPendingEffects(coord) ==
    {e["sourceUtxoId"] : e \in PendingEffects(coord.effectStack)}

(***************************************************************************
 * HANDLER STACK MANAGEMENT
 ***************************************************************************)

\* Install a handler on an interface in this coordination
InstallHandlerInCoord(coord, interfaceId, handler) ==
    [coord EXCEPT
        !.handlerStacks = InstallHandler(@, interfaceId, handler),
        !.installedHandlers = @ \cup {handler}]

\* Uninstall the top handler from an interface
UninstallHandlerInCoord(coord, interfaceId) ==
    IF Len(coord.handlerStacks[interfaceId]) = 0 THEN coord
    ELSE
        LET handler == GetHandlerFor(coord.handlerStacks, interfaceId)
        IN [coord EXCEPT
            !.handlerStacks = UninstallHandler(@, interfaceId),
            !.installedHandlers = @ \ {handler}]

\* Check if coordination has a handler for an interface
CoordHasHandlerFor(coord, interfaceId) ==
    HasHandlerFor(coord.handlerStacks, interfaceId)

\* Get all pending effects for a specific interface
PendingEffectsForInterface(coord, interfaceId) ==
    {e \in PendingEffects(coord.effectStack) : e.interfaceId = interfaceId}

(***************************************************************************
 * IVC CONFIGURATION MANAGEMENT
 ***************************************************************************)

\* Update IVC configuration
UpdateIVCConfig(coord, newConfig) ==
    [coord EXCEPT !.ivcConfig = newConfig]

\* Set current process ID in IVC config
SetCurrentProcessId(coord, pid) ==
    [coord EXCEPT !.ivcConfig.id_curr = pid]

\* Set previous process ID in IVC config
SetPreviousProcessId(coord, pid) ==
    [coord EXCEPT !.ivcConfig.id_prev = pid]

\* Set activation state
SetActivationState(coord, state) ==
    [coord EXCEPT !.ivcConfig.activation = state]

\* Mark as safe to ledger
MarkSafeToLedger(coord) ==
    [coord EXCEPT !.ivcConfig.safe_to_ledger = TRUE]

\* Check if coordination is safe to commit to ledger
IsSafeToLedger(coord) == coord.ivcConfig.safe_to_ledger

\* Check if coordination is active
IsActiveCoordination(coord) == coord.ivcConfig.activation = "Active"

(***************************************************************************
 * CALL EXECUTION HELPERS
 ***************************************************************************)

CanExecuteCall(call, utxo) ==
    /\ call.targetUtxo = utxo.id
    /\ ~call.executed
    /\ CASE call.callType = "Query" -> CanQuery(utxo)
         [] call.callType = "Mutate" -> CanMutate(utxo)
         [] call.callType = "Consume" -> CanConsume(utxo)
         [] OTHER -> FALSE

ExecuteCallOnUTXO(call, utxo) ==
    CASE call.callType = "Query" -> ExecuteQuery(utxo)
      [] call.callType = "Mutate" -> ExecuteMutation(utxo, call.args, utxo.frame.pc + 1)
      [] call.callType = "Consume" -> utxo
      [] OTHER -> utxo

(***************************************************************************
 * COORDINATION INVARIANTS
 ***************************************************************************)

ValidPhaseTransition(coord, coordNext) ==
    \/ (coord.phase = "NotStarted" /\ coordNext.phase = "Gathering")
    \/ (coord.phase = "Gathering" /\ coordNext.phase = "Processing")
    \/ (coord.phase = "Processing" /\ coordNext.phase \in {"Processing", "Finalizing"})
    \/ (coord.phase = "Finalizing" /\ coordNext.phase = "Complete")
    \/ (coord.phase = "Complete" /\ coordNext.phase = "Complete")

AllInputsReferenced(coord) ==
    coord.inputUtxos \subseteq
        {coord.pendingCalls[i].targetUtxo : i \in 1..Len(coord.pendingCalls)}

NoEffectsAtCompletion(coord) ==
    IsComplete(coord) => ~HasPendingEffects(coord)

(***************************************************************************
 * HANDLER STACK COORDINATION INVARIANTS
 ***************************************************************************)

\* Handler stacks are well-formed
ValidHandlerStacks(coord) ==
    ValidHandlerStackDepths(coord.handlerStacks)

\* Installed handlers set matches handler stacks
InstalledHandlersConsistent(coord) ==
    coord.installedHandlers = AllInstalledHandlers(coord.handlerStacks)

\* IVC config is valid
ValidIVCConfig(coord) ==
    /\ coord.ivcConfig.id_curr \in ProcessIdRange \cup {-1}
    /\ coord.ivcConfig.id_prev \in ProcessIdRange \cup {-1}
    /\ coord.ivcConfig.activation \in ActivationStates

=============================================================================
