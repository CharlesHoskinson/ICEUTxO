---------------------- MODULE StarstreamSerialRefinement ----------------------
(***************************************************************************
 * Refinement Mapping from Concurrent Spec to Serial Spec
 *
 * This module defines the explicit refinement mapping that shows every
 * behavior of the concurrent specification (StarstreamSpec) is also a
 * behavior of the serial specification (StarstreamSerial).
 *
 * The interleaving proof circuit is the CONSTRUCTIVE WITNESS for this
 * refinement: it produces a ZK proof that a specific execution satisfies
 * the interleaving constraints. This TLA+ refinement theorem proves that
 * ALL such executions (verified by the circuit) are serializable.
 *
 * STRUCTURE:
 *   1. Abstraction Map — projects concurrent state to serial state
 *   2. Trace Abstraction — maps interleaved traces to serial ordering
 *   3. Stuttering Map — identifies which concurrent steps are visible
 *   4. Refinement Theorem — the main claim
 *   5. Auxiliary Lemmas — supporting the refinement proof
 ***************************************************************************)

EXTENDS StarstreamSpec, StarstreamUTXO, StarstreamTypes,
        StarstreamCircuitAlignment

(***************************************************************************
 * 1. ABSTRACTION MAP
 *
 * The abstraction map projects the concurrent ledger state onto the
 * serial (abstract) state by:
 *   - Normalizing intermediate UTXO states to "Suspended_at_Yield"
 *   - Removing lock annotations
 *   - Preserving only committed transaction history
 *   - Ignoring pending transactions (they are not yet observable)
 ***************************************************************************)

NormalizeState(state) ==
    IF state \in {"Reserved", "Executing", "Suspended_at_Effect"}
    THEN "Suspended_at_Yield"
    ELSE state

AbsUTXO(u) ==
    [u EXCEPT
        !.state = NormalizeState(u.state),
        !.lockedBy = NO_TX]

AbsUtxoSet(ledgerState) ==
    {AbsUTXO(u) : u \in ledgerState.utxoSet}

\* Abstract projections from concrete state
absUtxoSet == AbsUtxoSet(ledger)
absConsumedSet == ledger.consumedSet
absTxHistory == ledger.txHistory

\* Instantiate the serial spec with the abstraction map.
\* Variables are substituted with abstraction functions; constants
\* are forwarded from StarstreamSpec (available via EXTENDS).
SerialSpecRef == INSTANCE StarstreamSerial WITH
    aUtxoSet       <- AbsUtxoSet(ledger),
    aConsumedSet   <- ledger.consumedSet,
    aTxHistory     <- ledger.txHistory,
    InitialUTXOs   <- InitialUTXOs,
    SampleContracts <- SampleContracts,
    SampleOwners   <- SampleOwners,
    SampleDatums   <- SampleDatums,
    SampleTokenBags <- SampleTokenBags

(***************************************************************************
 * 2. TRACE ABSTRACTION — Interleaved Trace to Serial Ordering
 *
 * The interleaving proof circuit produces a merged trace of host calls
 * across all WASM programs in a transaction. This section defines how
 * that interleaved trace maps to a serial ordering of commits.
 *
 * Key insight: the circuit proves that the interleaved execution of
 * host calls within a transaction is consistent. The ledger then
 * commits transactions atomically. The serial ordering is simply the
 * commit order in txHistory.
 ***************************************************************************)

\* Extract committed transactions from history
RECURSIVE CommittedTxsIn(_)
CommittedTxsIn(history) ==
    IF history = <<>> THEN <<>>
    ELSE
        LET head == history[1]
            tail == IF Len(history) = 1 THEN <<>> ELSE SubSeq(history, 2, Len(history))
        IN IF IsCommittedTx(head)
           THEN <<head>> \o CommittedTxsIn(tail)
           ELSE CommittedTxsIn(tail)

\* The serial ordering is the subsequence of committed transactions
SerialOrdering == CommittedTxsIn(ledger.txHistory)

\* A transaction's interleaved trace is serializable if the circuit
\* verified it and all its effects were properly matched
TxTraceSerializable(tx) ==
    /\ AllTxProofsVerified(tx)
    /\ IsComplete(tx.coordination)
    /\ ~HasPendingEffects(tx.coordination)
    /\ CircuitVerifiable(tx)

(***************************************************************************
 * 3. STUTTERING MAP
 *
 * Most concurrent actions are stuttering steps from the serial spec's
 * perspective. Only CommitTx corresponds to a visible step (SerialCommit),
 * and only AbortTx corresponds to a visible step (SerialAbort).
 *
 * Concurrent Action          | Serial Equivalent     | Stuttering?
 * ---------------------------+-----------------------+------------
 * CreateUTXO                 | SerialCreateUTXO      | No
 * YieldUTXO                  | SerialYieldUTXO       | No
 * QueryUTXO                  | SerialQueryUTXO       | No (but UNCHANGED)
 * ReserveTx                  | (none)                | Yes
 * BeginExecute               | (none)                | Yes
 * StartProcessing            | (none)                | Yes
 * ProcessTxCall              | (none)                | Yes
 * RaiseTxEffect              | (none)                | Yes
 * HandleTxEffect             | (none)                | Yes
 * InstallTxHandler           | (none)                | Yes
 * UninstallTxHandler         | (none)                | Yes
 * RaiseTxEffectOnInterface   | (none)                | Yes
 * HandleTxEffectOnInterface  | (none)                | Yes
 * FinalizeTx                 | (none)                | Yes
 * BeginCommit                | (none)                | Yes
 * CommitTx                   | SerialCommit          | No
 * StartRollback              | (none)                | Yes
 * FinishRollback             | SerialAbort           | No
 * BeginTxProofGeneration     | (none)                | Yes
 * VerifyTxProof              | (none)                | Yes
 ***************************************************************************)

\* Predicate: this action is a stuttering step (no abstract state change)
IsStutteringAction ==
    /\ AbsUtxoSet(ledger') = AbsUtxoSet(ledger)
    /\ ledger'.consumedSet = ledger.consumedSet
    /\ ledger'.txHistory = ledger.txHistory

\* Predicate: a commit action is visible at the abstract level
IsVisibleCommit(txId) ==
    /\ \E tx \in ledger.pendingTxs :
        /\ tx.id = txId
        /\ tx.phase = "Committing"
        /\ TxTraceSerializable(tx)

(***************************************************************************
 * 4. REFINEMENT THEOREM
 *
 * The main claim: every behavior of the concurrent spec satisfies the
 * serial spec under the abstraction map defined above.
 *
 * Proof sketch:
 *   (a) Init => SerialInit under the abstraction map
 *       - AbsUtxoSet(GenesisLedger(InitialUTXOs)) = InitialUTXOs
 *         (since initial UTXOs are already in Suspended_at_Yield with NO_TX)
 *       - consumedSet starts empty, txHistory starts empty
 *
 *   (b) [Next]_vars => [SerialNext]_avars under the abstraction map
 *       - Stuttering steps: Reserve, Execute, Process, Raise, Handle,
 *         Install, Uninstall, Finalize, BeginCommit, Proof ops
 *         all leave abstract state unchanged
 *       - CommitTx maps to SerialCommit:
 *         * Inputs consumed in concrete => consumed in abstract
 *         * Outputs added in concrete => added in abstract
 *         * Balance preservation holds by INV_BALANCE_TxPreserved
 *         * Proofs verified by AllTxProofsVerified guard
 *       - AbortTx maps to SerialAbort:
 *         * Inputs restored in concrete => not consumed in abstract
 *         * No outputs added
 *       - CreateUTXO maps to SerialCreateUTXO
 *       - YieldUTXO maps to SerialYieldUTXO
 *
 *   (c) The interleaving proof circuit provides the witness that
 *       intra-transaction execution is consistent, which is required
 *       for the CommitTx guard (AllTxProofsVerified).
 *       Without a valid circuit proof, CommitTx is not enabled,
 *       so the refinement only needs to consider verified executions.
 ***************************************************************************)

THEOREM SerialRefinement ==
    Spec => SerialSpecRef!SerialSpec
\* Mechanized as concurrent_refines_serial in StarstreamPilot.lean.
\* The proof proceeds by showing Init => SerialInit under the abstraction
\* map, then case-splitting Next into stuttering steps (which leave the
\* abstract variables unchanged) and visible steps (CommitTx, AbortTx,
\* CreateUTXO, YieldUTXO) that correspond to serial actions.
PROOF OMITTED

(***************************************************************************
 * 5. AUXILIARY LEMMAS
 *
 * Supporting lemmas for the refinement proof.
 ***************************************************************************)

\* Lemma: The abstraction map preserves the type invariant
THEOREM AbsTypeOK ==
    TypeOK => SerialSpecRef!SerialTypeOK
\* Mechanized as embed_ledgerInvariant in ConservativeExtension.lean.
\* AbsUTXO preserves record structure: NormalizeState maps each state
\* to a valid UTXOState, and clearing lockedBy yields a valid record.
PROOF OMITTED

\* Lemma: Stuttering steps preserve abstract state
\* For any action that only modifies pendingTxs, lockedSet, or proof state,
\* the abstract variables (aUtxoSet, aConsumedSet, aTxHistory) are unchanged.
THEOREM StutteringPreservation ==
    /\ ledger'.utxoSet = ledger.utxoSet
    /\ ledger'.consumedSet = ledger.consumedSet
    /\ ledger'.txHistory = ledger.txHistory
    => /\ AbsUtxoSet(ledger') = AbsUtxoSet(ledger)
       /\ ledger'.consumedSet = ledger.consumedSet
       /\ ledger'.txHistory = ledger.txHistory
\* Follows from the definition of AbsUtxoSet: if utxoSet is unchanged
\* then AbsUtxoSet is unchanged, since it applies a pointwise map.
\* Corresponding stuttering lemmas in StarstreamPilot.lean.
PROOF OMITTED

\* Lemma: CommitTx refines SerialCommit
\* When a transaction commits in the concurrent spec, it corresponds to
\* a SerialCommit step in the serial spec.
THEOREM CommitRefinesSerial ==
    \A txId \in TxIdRange :
        /\ CommitTx(txId)
        /\ TxTraceSerializable(GetPendingTx(ledger, txId))
        => \E tx \in TransactionRecordSet : SerialSpecRef!SerialCommit(tx)
\* Mechanized as the commit case of concurrent_refines_serial in
\* StarstreamPilot.lean. The witness tx is the pending transaction
\* record; its inputs are consumed and outputs are added atomically.
PROOF OMITTED

\* Lemma: Circuit verification is necessary for commit
\* A transaction can only commit if the interleaving proof circuit
\* has verified its execution trace.
THEOREM CircuitRequiredForCommit ==
    \A txId \in TxIdRange :
        CommitTx(txId) => AllTxProofsVerified(GetPendingTx(ledger, txId))
\* Mechanized as commit_requires_proof in StarstreamPilot.lean.
\* Follows directly from the AllTxProofsVerified guard in CommitTx.
PROOF OMITTED

\* Lemma: The serial ordering induced by txHistory is conflict-serializable
\* The circuit ensures intra-tx consistency; the ledger's UTXO locking
\* ensures inter-tx conflict freedom for committed transactions.
THEOREM CommitOrderSerializable ==
    /\ \A i, j \in 1..Len(ledger.txHistory) :
        /\ i < j
        /\ IsCommittedTx(ledger.txHistory[i])
        /\ IsCommittedTx(ledger.txHistory[j])
        => \* No input overlap between committed transactions
           {u.id : u \in ledger.txHistory[i].inputs} \cap
           {u.id : u \in ledger.txHistory[j].inputs} = {}
\* Mechanized as acyclic_strong_serializable in StarstreamPilot.lean.
\* Committed transactions consume their inputs, moving them to
\* consumedSet; a later commit cannot use already-consumed inputs.
PROOF OMITTED

(***************************************************************************
 * 6. CIRCUIT ↔ REFINEMENT CONNECTION
 *
 * The interleaving proof circuit is the constructive witness for the
 * refinement. This section makes the connection explicit.
 *
 * For each committed transaction tx:
 *   - The circuit proves: the interleaved host call trace of tx is
 *     consistent (message matching, value consistency, order consistency)
 *   - The TLA+ refinement proves: any tx with consistent interleaving
 *     corresponds to a serial commit step
 *   - Together: circuit proof + ledger validation = serializable commit
 *
 * The refinement does NOT prove the circuit is sound (that requires
 * a theorem prover like Lean/Coq/Isabelle). It proves that IF the
 * circuit accepts a trace, THEN that trace is serializable.
 ***************************************************************************)

\* A committed transaction has a valid circuit witness
HasCircuitWitness(tx) ==
    /\ IsCommittedTx(tx)
    /\ AllTxProofsVerified(tx)
    /\ tx.proofCommitments # {}

\* The refinement witness for a specific transaction
RefinementWitness(tx) ==
    /\ HasCircuitWitness(tx)
    /\ BalancePreserved(tx)
    /\ ValidSignature(tx.signature, tx)
    /\ InputsOwnedBySigner(tx)

\* All committed transactions have refinement witnesses
AllCommittedHaveWitnesses ==
    \A tx \in {ledger.txHistory[i] : i \in 1..Len(ledger.txHistory)} :
        IsCommittedTx(tx) => RefinementWitness(tx)

=============================================================================
