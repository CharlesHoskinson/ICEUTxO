--------------------------- MODULE StarstreamEffects ---------------------------
(***************************************************************************
 * Effect System for Starstream
 *
 * Models the algebraic effect system used for:
 * - Raising effects from UTXO coroutines
 * - Handling effects in coordination scripts
 * - Resuming execution after effect handling
 ***************************************************************************)

EXTENDS StarstreamTypes, StarstreamFrame

(***************************************************************************
 * EFFECT RECORD TYPE
 ***************************************************************************)

EffectRecordSet ==
    [kind: EffectKinds,
     sourceUtxoId: UTXOIdRange,
     continuationId: ContinuationIdRange,
     tag: EffectTags,
     payload: DatumValues,
     handled: BOOLEAN,
     interfaceId: InterfaceIdRange,               \* Interface this effect targets
     handlerStackId: 1..MAX_HANDLER_DEPTH,        \* Position in handler stack
     witLedgerKind: WitLedgerEffectKinds,         \* WitLedgerEffect kind from IVC
     fuel: FuelRange]                             \* Remaining budget for effect subtree (termination)

(***************************************************************************
 * EFFECT CONSTRUCTORS
 ***************************************************************************)

\* Legacy constructor for backward compatibility (uses default interface/handler/fuel)
NewEffect(effectKind, utxoId, continuationId, tag, payload) ==
    [kind |-> effectKind,
     sourceUtxoId |-> utxoId,
     continuationId |-> continuationId,
     tag |-> tag,
     payload |-> payload,
     handled |-> FALSE,
     interfaceId |-> 1,                  \* Default interface
     handlerStackId |-> 1,               \* Default handler position
     witLedgerKind |-> "Resume",         \* Default WitLedger kind
     fuel |-> MAX_EFFECT_FUEL]           \* Default max fuel

\* Full constructor with interface, WitLedger kind, and fuel
NewEffectWithInterface(effectKind, utxoId, continuationId, tag, payload, iface, witKind) ==
    [kind |-> effectKind,
     sourceUtxoId |-> utxoId,
     continuationId |-> continuationId,
     tag |-> tag,
     payload |-> payload,
     handled |-> FALSE,
     interfaceId |-> iface,
     handlerStackId |-> 1,
     witLedgerKind |-> witKind,
     fuel |-> MAX_EFFECT_FUEL]           \* Default max fuel

\* Full constructor with explicit fuel (for budget-splitting termination)
NewEffectWithFuel(effectKind, utxoId, continuationId, tag, payload, iface, witKind, f) ==
    [kind |-> effectKind,
     sourceUtxoId |-> utxoId,
     continuationId |-> continuationId,
     tag |-> tag,
     payload |-> payload,
     handled |-> FALSE,
     interfaceId |-> iface,
     handlerStackId |-> 1,
     witLedgerKind |-> witKind,
     fuel |-> f]

PureEffect(utxoId, continuationId, tag, payload) ==
    NewEffect("Pure", utxoId, continuationId, tag, payload)

EffectfulEffect(utxoId, continuationId, tag, payload) ==
    NewEffect("Effectful", utxoId, continuationId, tag, payload)

RuntimeEffect(utxoId, continuationId, tag, payload) ==
    NewEffect("Runtime", utxoId, continuationId, tag, payload)

\* Interface-aware effect constructors
PureEffectOnInterface(utxoId, continuationId, tag, payload, iface, witKind) ==
    NewEffectWithInterface("Pure", utxoId, continuationId, tag, payload, iface, witKind)

EffectfulEffectOnInterface(utxoId, continuationId, tag, payload, iface, witKind) ==
    NewEffectWithInterface("Effectful", utxoId, continuationId, tag, payload, iface, witKind)

RuntimeEffectOnInterface(utxoId, continuationId, tag, payload, iface, witKind) ==
    NewEffectWithInterface("Runtime", utxoId, continuationId, tag, payload, iface, witKind)

(***************************************************************************
 * EFFECT PREDICATES
 ***************************************************************************)

IsEffectRecord(e) ==
    /\ IsValidEffectKind(e.kind)
    /\ IsValidUTXOId(e.sourceUtxoId)
    /\ e.continuationId \in ContinuationIdRange
    /\ e.tag \in EffectTags
    /\ e.payload \in DatumValues
    /\ e.handled \in BOOLEAN
    /\ e.interfaceId \in InterfaceIdRange
    /\ e.handlerStackId \in 1..MAX_HANDLER_DEPTH
    /\ e.witLedgerKind \in WitLedgerEffectKinds

IsPendingEffect(e) == /\ IsEffectRecord(e) /\ ~e.handled
IsHandledEffect(e) == /\ IsEffectRecord(e) /\ e.handled
IsPureEffect(e) == /\ IsEffectRecord(e) /\ e.kind = "Pure"
IsEffectfulEffect(e) == /\ IsEffectRecord(e) /\ e.kind = "Effectful"
IsRuntimeEffect(e) == /\ IsEffectRecord(e) /\ e.kind = "Runtime"

(***************************************************************************
 * EFFECT OPERATIONS
 ***************************************************************************)

MarkHandled(effect) == [effect EXCEPT !.handled = TRUE]

HandlerResult(effect, resultValue) ==
    [sourceEffect |-> effect,
     result |-> resultValue,
     success |-> TRUE]

FailedHandlerResult(effect, errorValue) ==
    [sourceEffect |-> effect,
     result |-> errorValue,
     success |-> FALSE]

(***************************************************************************
 * EFFECT STACK OPERATIONS
 ***************************************************************************)

EmptyEffectStack == <<>>

PushEffect(stack, effect) == Append(stack, effect)

PopEffect(stack) == IF Len(stack) = 0 THEN stack ELSE SubSeq(stack, 1, Len(stack) - 1)

PeekEffect(stack) == IF Len(stack) = 0 THEN NULL ELSE stack[Len(stack)]

IsEmptyEffectStack(stack) == Len(stack) = 0

PendingEffects(stack) ==
    {e \in FcnRange(stack) : ~e["handled"]}

AllEffectsHandled(stack) ==
    \A e \in FcnRange(stack) : e["handled"]

\* Unused by the main spec actions but retained as a utility for debugging
\* and trace exploration. Returns the first pending effect for a given UTXO.
FindPendingEffectForUTXO(stack, utxoId) ==
    LET pending == {i \in 1..Len(stack) :
                    /\ stack[i]["sourceUtxoId"] = utxoId
                    /\ ~stack[i]["handled"]}
    IN IF pending = {} THEN NULL
       ELSE stack[CHOOSE i \in pending : \A j \in pending : i <= j]

(***************************************************************************
 * EFFECT HANDLING TRANSITIONS
 ***************************************************************************)

RaiseEffectOp(stack, effectKind, utxoId, continuationId, tag, payload) ==
    PushEffect(stack, NewEffect(effectKind, utxoId, continuationId, tag, payload))

HandleTopEffect(stack, resultValue) ==
    IF IsEmptyEffectStack(stack) THEN <<stack, NULL>>
    ELSE
        LET top == PeekEffect(stack)
            handled == MarkHandled(top)
            newStack == PopEffect(stack)
        IN <<newStack, HandlerResult(handled, resultValue)>>

HandleEffectAt(stack, idx, resultValue) ==
    IF idx < 1 \/ idx > Len(stack) THEN stack
    ELSE [stack EXCEPT ![idx] = MarkHandled(stack[idx])]

ClearHandledEffects(stack) ==
    SelectSeq(stack, LAMBDA e : ~e.handled)

(***************************************************************************
 * EFFECT INVARIANTS
 ***************************************************************************)

ValidEffectStack(stack) ==
    \A e \in FcnRange(stack) : IsEffectRecord(e)

OrderedEffectStack(stack) ==
    \A i, j \in 1..Len(stack) :
        (i < j /\ ~stack[i]["handled"] /\ ~stack[j]["handled"])
        => stack[i]["continuationId"] <= stack[j]["continuationId"]

NoDuplicatePendingEffects(stack) ==
    \A i, j \in 1..Len(stack) :
        (i # j /\ ~stack[i]["handled"] /\ ~stack[j]["handled"])
        => stack[i]["sourceUtxoId"] # stack[j]["sourceUtxoId"]

(***************************************************************************
 * HANDLER STACK OPERATIONS (Per-Interface Routing)
 *
 * Each interface has its own handler stack for effect routing.
 * Handlers are installed/uninstalled per-interface.
 ***************************************************************************)

\* Empty handler stacks for all interfaces
EmptyHandlerStacks == [iface \in InterfaceIdRange |-> <<>>]

\* Install a handler on an interface's stack
InstallHandler(stacks, interfaceId, handler) ==
    IF Len(stacks[interfaceId]) >= MAX_HANDLER_DEPTH THEN stacks
    ELSE [stacks EXCEPT ![interfaceId] = Append(@, handler)]

\* Uninstall the top handler from an interface's stack
UninstallHandler(stacks, interfaceId) ==
    IF Len(stacks[interfaceId]) = 0 THEN stacks
    ELSE [stacks EXCEPT ![interfaceId] = SubSeq(@, 1, Len(@) - 1)]

\* Get the top handler for an interface (or NULL if none)
GetHandlerFor(stacks, interfaceId) ==
    IF Len(stacks[interfaceId]) = 0 THEN NULL
    ELSE stacks[interfaceId][Len(stacks[interfaceId])]

\* Check if an interface has at least one handler
HasHandlerFor(stacks, interfaceId) ==
    Len(stacks[interfaceId]) > 0

\* Get handler stack depth for an interface
HandlerStackDepth(stacks, interfaceId) == Len(stacks[interfaceId])

\* Get all installed handlers across all interfaces
AllInstalledHandlers(stacks) ==
    UNION {FcnRange(stacks[iface]) : iface \in InterfaceIdRange}

\* Check if a specific handler is installed on any interface
IsHandlerInstalled(stacks, handler) ==
    \E iface \in InterfaceIdRange : handler \in FcnRange(stacks[iface])

\* Route effect to appropriate handler based on interface
RouteEffectToHandler(stacks, effect) ==
    GetHandlerFor(stacks, effect.interfaceId)

\* Create a new handler record
NewHandler(hid, iface, installerPid, mask, prio) ==
    [handlerId |-> hid,
     interfaceId |-> iface,
     installedBy |-> installerPid,
     effectMask |-> mask,
     priority |-> prio]

(***************************************************************************
 * HANDLER STACK INVARIANTS
 ***************************************************************************)

\* All handler stacks are within depth bounds
ValidHandlerStackDepths(stacks) ==
    \A iface \in InterfaceIdRange : Len(stacks[iface]) <= MAX_HANDLER_DEPTH

\* Handler IDs are unique within each stack
UniqueHandlerIds(stacks) ==
    \A iface \in InterfaceIdRange :
        \A i, j \in 1..Len(stacks[iface]) :
            (i # j) => stacks[iface][i].handlerId # stacks[iface][j].handlerId

\* Handlers are installed on their declared interface
HandlersOnCorrectInterface(stacks) ==
    \A iface \in InterfaceIdRange :
        \A i \in 1..Len(stacks[iface]) :
            stacks[iface][i].interfaceId = iface

=============================================================================
