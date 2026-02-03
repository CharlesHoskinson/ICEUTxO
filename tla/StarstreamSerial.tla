--------------------------- MODULE StarstreamSerial ---------------------------
(***************************************************************************
 * Serial (atomic) specification for Starstream.
 * This abstracts away intermediate reservation/execution steps and models
 * only the externally-visible effects on the ledger state.
 ***************************************************************************/

EXTENDS StarstreamTypes, StarstreamFrame, StarstreamUTXO, StarstreamEffects,
        StarstreamCoordination, StarstreamTransaction, StarstreamAuth, StarstreamSpec

(***************************************************************************
 * ABSTRACT STATE VARIABLES
 ***************************************************************************/

VARIABLES
    aUtxoSet,
    aConsumedSet,
    aTxHistory

avars == <<aUtxoSet, aConsumedSet, aTxHistory>>

(***************************************************************************
 * HELPERS
 ***************************************************************************/

UTXOIds(utxoSet) == {u.id : u \in utxoSet}
InputIds(tx) == {u.id : u \in tx.inputs}
OutputIds(tx) == {u.id : u \in tx.outputs}

FreshOutputIds(tx) ==
    OutputIds(tx) \cap (UTXOIds(aUtxoSet) \cup aConsumedSet) = {}

(***************************************************************************
 * TYPE INVARIANT
 ***************************************************************************/

SerialTypeOK ==
    /\ aUtxoSet \subseteq UTXORecordSet
    /\ aConsumedSet \subseteq UTXOIdRange
    /\ aTxHistory \in Seq(TransactionRecordSet)
    /\ \A u \in aUtxoSet : IsUTXORecord(u)
    /\ \A tx \in {aTxHistory[i] : i \in 1..Len(aTxHistory)} : IsTransactionRecord(tx)

(***************************************************************************
 * INITIAL STATE
 ***************************************************************************/

SerialInit ==
    /\ aUtxoSet = InitialUTXOs
    /\ aConsumedSet = {}
    /\ aTxHistory = <<>>

(***************************************************************************
 * ACTIONS
 ***************************************************************************/

SerialCreateUTXO(contract, owner, datum, tokens, newId) ==
    /\ newId \in UTXOIdRange
    /\ newId \notin UTXOIds(aUtxoSet) \cup aConsumedSet
    /\ aUtxoSet' = aUtxoSet \cup {NewUTXO(newId, contract, owner, datum, tokens)}
    /\ UNCHANGED <<aConsumedSet, aTxHistory>>

SerialYieldUTXO(utxoId, yieldPC, newDatum) ==
    /\ utxoId \in UTXOIds(aUtxoSet)
    /\ LET u == FindUTXO(aUtxoSet, utxoId)
       IN /\ u.state = "Created"
          /\ aUtxoSet' = UpdateUTXOInSet(aUtxoSet, CreateToYield(u, yieldPC, newDatum))
          /\ UNCHANGED <<aConsumedSet, aTxHistory>>

SerialQueryUTXO(utxoId) ==
    /\ utxoId \in UTXOIds(aUtxoSet)
    /\ UNCHANGED avars

SerialCommit(tx) ==
    /\ tx \in TransactionRecordSet
    /\ InputIds(tx) # {}
    /\ InputIds(tx) \subseteq UTXOIds(aUtxoSet)
    /\ InputIds(tx) \cap aConsumedSet = {}
    /\ OutputIds(tx) # {}
    /\ FreshOutputIds(tx)
    /\ IsComplete(tx.coordination)
    /\ InputsOwnedBySigner(tx)
    /\ BalancePreserved(tx)
    /\ ValidSignature(tx.signature, tx)
    /\ aUtxoSet' = {u \in aUtxoSet : u.id \notin InputIds(tx)} \cup tx.outputs
    /\ aConsumedSet' = aConsumedSet \cup InputIds(tx)
    /\ aTxHistory' = Append(aTxHistory, CommitTransaction(tx))

SerialAbort(tx, reason) ==
    /\ tx \in TransactionRecordSet
    /\ InputIds(tx) # {}
    /\ InputIds(tx) \subseteq UTXOIds(aUtxoSet)
    /\ InputIds(tx) \cap aConsumedSet = {}
    /\ reason \in DatumValues
    /\ aUtxoSet' = aUtxoSet
    /\ aConsumedSet' = aConsumedSet
    /\ aTxHistory' = Append(aTxHistory, AbortTransaction(tx, reason))

(***************************************************************************
 * NEXT-STATE RELATION
 ***************************************************************************/

SerialNext ==
    \/ \E c \in SampleContracts, o \in SampleOwners, d \in SampleDatums, t \in SampleTokenBags, id \in UTXOIdRange :
        SerialCreateUTXO(c, o, d, t, id)

    \/ \E id \in UTXOIdRange, pc \in PCRange, d \in DatumValues :
        SerialYieldUTXO(id, pc, d)

    \/ \E id \in UTXOIdRange :
        SerialQueryUTXO(id)

    \/ \E tx \in TransactionRecordSet :
        SerialCommit(tx)

    \/ \E tx \in TransactionRecordSet, reason \in DatumValues :
        SerialAbort(tx, reason)

(***************************************************************************
 * SPECIFICATION
 ***************************************************************************/

SerialSpec == SerialInit /\ [][SerialNext]_avars

=============================================================================
