--------------------------- MODULE StarstreamPTB ---------------------------
(***************************************************************************
 * PTB Event Representation (validation-oriented)
 *
 * PTB events mirror the Action labels in the Lean coordination model.
 * We use a bounded trace set for TLC enumeration.
 ***************************************************************************)

EXTENDS StarstreamTypes

(***************************************************************************
 * EVENT TYPES
 ***************************************************************************)

PTBEventKinds == {
    "Raise",
    "Resume",
    "Install",
    "Uninstall",
    "Read",
    "Snapshot",
    "Lock",
    "Consume",
    "Produce"
}

\* Optional numeric sentinels for PTB fields.
\* Keeping these numeric avoids TLC mixed string/int equality errors.
NO_UTXO_ID == -1
NO_INTERFACE_ID == -1
NO_CONTINUATION_ID == -1

PTBEvent ==
    [kind: PTBEventKinds,
     utxoId: {NO_UTXO_ID} \cup UTXOIdRange,
     interfaceId: {NO_INTERFACE_ID} \cup InterfaceIdRange,
     effectKind: {NULL} \cup EffectKinds,
     continuationId: {NO_CONTINUATION_ID} \cup ContinuationIdRange,
     tag: {NULL} \cup EffectTags,
     payload: {NULL} \cup DatumValues,
     witKind: {NULL} \cup WitLedgerEffectKinds,
     handlerResult: {NULL} \cup DatumValues,
     effectMask: SUBSET EffectTags]

IsPTBEvent(e) ==
    /\ e.kind \in PTBEventKinds
    /\ e.utxoId \in {NO_UTXO_ID} \cup UTXOIdRange
    /\ e.interfaceId \in {NO_INTERFACE_ID} \cup InterfaceIdRange
    /\ e.effectKind \in {NULL} \cup EffectKinds
    /\ e.continuationId \in {NO_CONTINUATION_ID} \cup ContinuationIdRange
    /\ e.tag \in {NULL} \cup EffectTags
    /\ e.payload \in {NULL} \cup DatumValues
    /\ e.witKind \in {NULL} \cup WitLedgerEffectKinds
    /\ e.handlerResult \in {NULL} \cup DatumValues
    /\ e.effectMask \subseteq EffectTags
    /\ CASE e.kind = "Raise" ->
            /\ e.utxoId # NO_UTXO_ID
            /\ e.interfaceId # NO_INTERFACE_ID
            /\ e.effectKind # NULL
            /\ e.continuationId # NO_CONTINUATION_ID
            /\ e.tag # NULL
            /\ e.payload # NULL
            /\ e.witKind # NULL
       [] e.kind = "Resume" ->
            /\ e.interfaceId # NO_INTERFACE_ID
            /\ e.handlerResult # NULL
       [] e.kind = "Install" ->
            /\ e.interfaceId # NO_INTERFACE_ID
       [] e.kind = "Uninstall" ->
            /\ e.interfaceId # NO_INTERFACE_ID
       [] e.kind \in {"Read", "Snapshot", "Lock", "Consume", "Produce"} ->
            /\ e.utxoId # NO_UTXO_ID
       [] OTHER -> FALSE

(***************************************************************************
 * TRACE SET (bounded for TLC)
 * Keep this intentionally tiny for model checking tractability.
 ***************************************************************************)

SampleRaiseEvent ==
    [kind |-> "Raise",
     utxoId |-> 1,
     interfaceId |-> 1,
     effectKind |-> "Pure",
     continuationId |-> 0,
     tag |-> "E1",
     payload |-> "Empty",
     witKind |-> "Resume",
     handlerResult |-> NULL,
     effectMask |-> {}]

SampleResumeEvent ==
    [kind |-> "Resume",
     utxoId |-> NO_UTXO_ID,
     interfaceId |-> 1,
     effectKind |-> NULL,
     continuationId |-> NO_CONTINUATION_ID,
     tag |-> NULL,
     payload |-> NULL,
     witKind |-> NULL,
     handlerResult |-> "V0",
     effectMask |-> {}]

SamplePTBEvents == {SampleRaiseEvent, SampleResumeEvent}

PTBTrace ==
    {<<>>}
    \cup {<<e>> : e \in SamplePTBEvents}
    \cup {<<e1, e2>> : e1 \in SamplePTBEvents, e2 \in SamplePTBEvents}

IsPTBTrace(t) ==
    /\ t \in PTBTrace
    /\ \A i \in 1..Len(t) : IsPTBEvent(t[i])

=============================================================================
