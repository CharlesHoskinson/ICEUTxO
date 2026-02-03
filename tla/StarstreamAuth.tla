--------------------------- MODULE StarstreamAuth ---------------------------
(***************************************************************************
 * Authorization and Signature Verification
 *
 * This module provides a signature model that binds a signer to the
 * transaction contents (inputs, outputs, coordination state, and effects).
 *
 * NOTE: We model "hash" as a structured value for TLC; no cryptography.
 ***************************************************************************)

EXTENDS StarstreamTypes, StarstreamProof, StarstreamPTB

(***************************************************************************
 * DIGEST TYPE SETS
 ***************************************************************************)

TxInputsDigestType == SUBSET UTXOIdRange

OutputDigestType ==
    UTXOIdRange \X OwnerAddrs \X ContractIds \X DatumValues \X TokenBagType

TxOutputsDigestType == SUBSET OutputDigestType

ProofCommitmentDigestType == DatumValues

TxProofsDigestType == SUBSET ProofCommitmentDigestType

CallCommitmentType ==
    CallTypes \X UTXOIdRange \X MethodIdRange \X DatumValues \X BOOLEAN \X (DatumValues \cup {NULL})

CallCommitmentSeqType == Seq(CallCommitmentType)

OutputSpecCommitmentType ==
    DatumValues \X TokenBagType \X ContractIds \X OwnerAddrs

OutputSpecCommitmentSeqType == Seq(OutputSpecCommitmentType)

EffectCommitmentType ==
    EffectKinds \X UTXOIdRange \X ContinuationIdRange \X EffectTags \X DatumValues \X BOOLEAN

EffectCommitmentSeqType == Seq(EffectCommitmentType)

CoordCallIndexRange == 0..10

\* PTB event commitments (authoritative coordination digest)
PTBEventCommitmentType ==
    PTBEventKinds \X (UTXOIdRange \cup {NULL}) \X (InterfaceIdRange \cup {NULL}) \X
    (EffectKinds \cup {NULL}) \X (ContinuationIdRange \cup {NULL}) \X
    (EffectTags \cup {NULL}) \X (DatumValues \cup {NULL}) \X
    (WitLedgerEffectKinds \cup {NULL}) \X (DatumValues \cup {NULL}) \X (SUBSET EffectTags)

PTBTraceCommitmentSeqType == Seq(PTBEventCommitmentType)

TxCoordDigestType ==
    CoordPhases \X (SUBSET UTXOIdRange) \X OutputSpecCommitmentSeqType \X
    EffectCommitmentSeqType \X PTBTraceCommitmentSeqType \X (0..MAX_TX_INPUTS)

TxContentsHashType == DatumValues

SignatureType ==
    [owner: OwnerAddrs, txId: TxIdRange, contentsHash: TxContentsHashType]

(***************************************************************************
 * CONTENT DIGESTS
 ***************************************************************************)

TxInputsDigest(tx) ==
    {u["id"] : u \in tx.inputs}

TxOutputsDigest(tx) ==
    {<<u["id"], u["owner"], u["contractId"], u["datum"], u["tokens"]>> : u \in tx.outputs}

CallCommitment(call) ==
    <<call["callType"], call["targetUtxo"], call["methodId"],
      call["args"], call["executed"], call["result"]>>

CallCommitments(coord) ==
    [i \in 1..Len(coord.pendingCalls) |-> CallCommitment(coord.pendingCalls[i])]

OutputSpecCommitment(spec) ==
    <<spec["datum"], spec["tokens"], spec["contract"], spec["owner"]>>

OutputSpecCommitments(coord) ==
    [i \in 1..Len(coord.outputSpecs) |-> OutputSpecCommitment(coord.outputSpecs[i])]

EffectCommitment(effect) ==
    <<effect["kind"], effect["sourceUtxoId"], effect["continuationId"],
      effect["tag"], effect["payload"], effect["handled"]>>

EffectCommitments(coord) ==
    [i \in 1..Len(coord.effectStack) |-> EffectCommitment(coord.effectStack[i])]

PTBEventCommitment(evt) ==
    <<evt.kind, evt.utxoId, evt.interfaceId, evt.effectKind,
      evt.continuationId, evt.tag, evt.payload, evt.witKind,
      evt.handlerResult, evt.effectMask>>

PTBTraceCommitments(coord) ==
    [i \in 1..Len(coord.ptbTrace) |-> PTBEventCommitment(coord.ptbTrace[i])]

ProofCommitmentDigest(proof) ==
    <<proof.proofKind, proof.ivcProcessId, proof.commitmentHash,
      proof.verificationKey, proof.stepNumber>>

TxProofsDigest(tx) ==
    {ProofCommitmentDigest(p) : p \in tx.proofCommitments}

TxCoordDigest(tx) ==
    <<tx.coordination.phase,
      tx.coordination.inputUtxos,
      OutputSpecCommitments(tx.coordination),
      EffectCommitments(tx.coordination),
      PTBTraceCommitments(tx.coordination),
      tx.coordination.ptbIndex>>

TxContentsHash(tx) ==
    <<CHAIN_ID, BLOCK_HEIGHT, tx.id, tx.signer,
      TxInputsDigest(tx), TxOutputsDigest(tx),
      tx.readSet, tx.writeSet,
      TxCoordDigest(tx), TxProofsDigest(tx)>>

(***************************************************************************
 * SIGNATURES
 ***************************************************************************)

MakeSignature(owner, txId, contentsHash) ==
    [owner |-> owner, txId |-> txId, contentsHash |-> contentsHash]

IsProofCommitmentDigest(p) ==
    /\ Len(p) = 5
    /\ p[1] \in ProofKinds
    /\ p[2] \in ProcessIdRange
    /\ p[3] \in FrameHashRange
    /\ p[4] \in 1..10
    /\ p[5] \in 0..UTXO_ID_BOUND

IsTxProofsDigest(pds) ==
    \A p \in pds : IsProofCommitmentDigest(p)

IsOutputDigest(o) ==
    /\ Len(o) = 5
    /\ o[1] \in UTXOIdRange
    /\ o[2] \in OwnerAddrs
    /\ o[3] \in ContractIds
    /\ o[4] \in DatumValues
    /\ o[5] \in TokenBagType

IsTxInputsDigest(ids) ==
    \A id \in ids : id \in UTXOIdRange

IsReadSetDigest(ids) ==
    \A id \in ids : id \in UTXOIdRange

IsWriteSetDigest(ids) ==
    \A id \in ids : id \in UTXOIdRange

IsTxOutputsDigest(outs) ==
    \A o \in outs : IsOutputDigest(o)

IsCallCommitment(c) ==
    /\ Len(c) = 6
    /\ c[1] \in CallTypes
    /\ c[2] \in UTXOIdRange
    /\ c[3] \in MethodIdRange
    /\ c[4] \in DatumValues
    /\ c[5] \in BOOLEAN
    /\ c[6] \in DatumValues \cup {NULL}

IsCallCommitmentSeq(cseq) ==
    \A i \in 1..Len(cseq) : IsCallCommitment(cseq[i])

IsOutputSpecCommitment(os) ==
    /\ Len(os) = 4
    /\ os[1] \in DatumValues
    /\ os[2] \in TokenBagType
    /\ os[3] \in ContractIds
    /\ os[4] \in OwnerAddrs

IsOutputSpecCommitmentSeq(oseq) ==
    \A i \in 1..Len(oseq) : IsOutputSpecCommitment(oseq[i])

IsEffectCommitment(e) ==
    /\ Len(e) = 6
    /\ e[1] \in EffectKinds
    /\ e[2] \in UTXOIdRange
    /\ e[3] \in ContinuationIdRange
    /\ e[4] \in EffectTags
    /\ e[5] \in DatumValues
    /\ e[6] \in BOOLEAN

IsEffectCommitmentSeq(eseq) ==
    \A i \in 1..Len(eseq) : IsEffectCommitment(eseq[i])

IsPTBEventCommitment(p) ==
    /\ Len(p) = 10
    /\ p[1] \in PTBEventKinds
    /\ p[2] \in UTXOIdRange \cup {NULL}
    /\ p[3] \in InterfaceIdRange \cup {NULL}
    /\ p[4] \in EffectKinds \cup {NULL}
    /\ p[5] \in ContinuationIdRange \cup {NULL}
    /\ p[6] \in EffectTags \cup {NULL}
    /\ p[7] \in DatumValues \cup {NULL}
    /\ p[8] \in WitLedgerEffectKinds \cup {NULL}
    /\ p[9] \in DatumValues \cup {NULL}
    /\ p[10] \subseteq EffectTags

IsPTBTraceCommitmentSeq(pseq) ==
    \A i \in 1..Len(pseq) : IsPTBEventCommitment(pseq[i])

IsTxCoordDigest(d) ==
    /\ Len(d) = 6
    /\ d[1] \in CoordPhases
    /\ d[2] \subseteq UTXOIdRange
    /\ IsOutputSpecCommitmentSeq(d[3])
    /\ IsEffectCommitmentSeq(d[4])
    /\ IsPTBTraceCommitmentSeq(d[5])
    /\ d[6] \in 0..MAX_TX_INPUTS

IsTxContentsHash(ch) ==
    /\ Len(ch) = 10
    /\ ch[1] \in ChainIdRange
    /\ ch[2] \in BlockHeightRange
    /\ ch[3] \in TxIdRange
    /\ ch[4] \in OwnerAddrs
    /\ IsTxInputsDigest(ch[5])
    /\ IsTxOutputsDigest(ch[6])
    /\ IsReadSetDigest(ch[7])
    /\ IsWriteSetDigest(ch[8])
    /\ IsTxCoordDigest(ch[9])
    /\ IsTxProofsDigest(ch[10])

IsSignature(sig) ==
    /\ sig.owner \in OwnerAddrs
    /\ sig.txId \in TxIdRange
    /\ IsTxContentsHash(sig.contentsHash)

ValidSignature(sig, tx) ==
    /\ IsSignature(sig)
    /\ sig["owner"] = tx.signer
    /\ sig["txId"] = tx.id
    /\ sig["contentsHash"] = TxContentsHash(tx)

InputsOwnedBySigner(tx) ==
    \A u \in tx.inputs : u["owner"] = tx.signer

=============================================================================
