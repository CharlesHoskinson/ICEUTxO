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

PTBEvent ==
    [kind: PTBEventKinds,
     utxoId: UTXOIdRange \cup {NULL},
     interfaceId: InterfaceIdRange \cup {NULL},
     effectKind: EffectKinds \cup {NULL},
     continuationId: ContinuationIdRange \cup {NULL},
     tag: EffectTags \cup {NULL},
     payload: DatumValues \cup {NULL},
     witKind: WitLedgerEffectKinds \cup {NULL},
     handlerResult: DatumValues \cup {NULL},
     effectMask: SUBSET EffectTags]

IsPTBEvent(e) ==
    /\ e.kind \in PTBEventKinds
    /\ e.utxoId \in UTXOIdRange \cup {NULL}
    /\ e.interfaceId \in InterfaceIdRange \cup {NULL}
    /\ e.effectKind \in EffectKinds \cup {NULL}
    /\ e.continuationId \in ContinuationIdRange \cup {NULL}
    /\ e.tag \in EffectTags \cup {NULL}
    /\ e.payload \in DatumValues \cup {NULL}
    /\ e.witKind \in WitLedgerEffectKinds \cup {NULL}
    /\ e.handlerResult \in DatumValues \cup {NULL}
    /\ e.effectMask \subseteq EffectTags
    /\ CASE e.kind = "Raise" ->
            /\ e.utxoId # NULL
            /\ e.interfaceId # NULL
            /\ e.effectKind # NULL
            /\ e.continuationId # NULL
            /\ e.tag # NULL
            /\ e.payload # NULL
            /\ e.witKind # NULL
       [] e.kind = "Resume" ->
            /\ e.interfaceId # NULL
            /\ e.handlerResult # NULL
       [] e.kind = "Install" ->
            /\ e.interfaceId # NULL
       [] e.kind = "Uninstall" ->
            /\ e.interfaceId # NULL
       [] e.kind \in {"Read", "Snapshot", "Lock", "Consume", "Produce"} ->
            /\ e.utxoId # NULL
       [] OTHER -> FALSE

(***************************************************************************
 * TRACE SET (bounded for TLC)
 ***************************************************************************)

PTBTrace ==
    {t \in Seq(PTBEvent) : Len(t) <= MAX_TX_INPUTS}

IsPTBTrace(t) ==
    /\ t \in PTBTrace
    /\ \A i \in 1..Len(t) : IsPTBEvent(t[i])

=============================================================================
