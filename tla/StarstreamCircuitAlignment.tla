-------------------- MODULE StarstreamCircuitAlignment --------------------
(***************************************************************************
 * Circuit ↔ TLA+ Alignment Module for Starstream
 *
 * This module formally maps each LedgerOperation variant from the
 * interleaving proof circuit (IVC/Neo folding) to the corresponding
 * TLA+ action, invariant, and type.
 *
 * PURPOSE:
 * The interleaving proof circuit verifies cross-program communication
 * (resume/yield/effect operations) within a transaction. This module
 * provides the formal bridge between:
 *   - Circuit wire names (id_curr, id_prev, activation, etc.)
 *   - TLA+ state variables and type definitions
 *   - Invariants that must hold at each circuit step
 *
 * The circuit merges per-process traces into a single interleaved trace
 * and proves:
 *   1. Message matching: resume inputs match yield outputs (dual traces)
 *   2. Value consistency: exchanged values match commitments
 *   3. Order consistency: resume targets match correct process IDs
 *   4. State invariants: no self-resume, linearity, handler stacks, etc.
 *
 * STRUCTURE:
 *   Section 1 — LedgerOperation ↔ TLA+ Action Map
 *   Section 2 — Circuit Wire ↔ TLA+ Variable Map
 *   Section 3 — Per-Step Invariant Map
 *   Section 4 — Alignment Validation Predicates
 *   Section 5 — Gap Analysis Predicates
 ***************************************************************************)

EXTENDS StarstreamTypes, StarstreamFrame, StarstreamUTXO, StarstreamEffects,
        StarstreamCoordination, StarstreamTransaction, StarstreamLedger,
        StarstreamProof

(***************************************************************************
 * SECTION 1: LedgerOperation ↔ TLA+ Action Map
 *
 * Each variant of the circuit's LedgerOperation enum maps to one or
 * more TLA+ actions in StarstreamSpec.tla.
 *
 * Circuit LedgerOperation  | TLA+ Action(s)                | Module
 * -------------------------+--------------------------------+------------------
 * Resume                   | HandleTxEffect,                | StarstreamSpec
 *                          | HandleTxEffectOnInterface       |
 * Yield_Intermediate       | RaiseTxEffect,                 | StarstreamSpec
 *                          | RaiseTxEffectOnInterface        |
 * Yield_Final              | FinalizeTx                     | StarstreamSpec
 * Burn                     | CommitTx (input consumption)   | StarstreamSpec
 * Bind                     | InstallTxHandler               | StarstreamSpec
 * Unbind                   | UninstallTxHandler             | StarstreamSpec
 * NewUtxo                  | FinalizeTx (output creation)   | StarstreamSpec
 * NewCoord                 | ReserveTx (coord creation)     | StarstreamSpec
 * GetHandler               | RouteEffectToHandler           | StarstreamEffects
 * RefCreate                | CreateUTXOInLedger             | StarstreamLedger
 * RefConsume               | ConsumeUTXO                    | StarstreamUTXO
 * RefRead                  | QueryUTXO / ExecuteQuery       | StarstreamSpec
 ***************************************************************************)

\* Symbolic constants for LedgerOperation variants (circuit enum)
CircuitOps == {
    "Resume",
    "Yield_Intermediate",
    "Yield_Final",
    "Burn",
    "Bind",
    "Unbind",
    "NewUtxo",
    "NewCoord",
    "GetHandler",
    "RefCreate",
    "RefConsume",
    "RefRead"
}

\* Maps circuit op to the corresponding WitLedgerEffectKind in TLA+
CircuitOpToWitKind(op) ==
    CASE op = "Resume"             -> "Resume"
      [] op = "Yield_Intermediate" -> "Yield_Intermediate"
      [] op = "Yield_Final"        -> "Yield_Final"
      [] op = "Burn"               -> "Burn"
      [] op = "Bind"               -> "Bind"
      [] op = "Unbind"             -> "Unbind"
      [] op = "NewUtxo"            -> "NewUtxo"
      [] OTHER                     -> "Resume"  \* Non-WitLedger ops default

\* Circuit ops that have direct WitLedgerEffectKind equivalents
WitLedgerCircuitOps == {"Resume", "Yield_Intermediate", "Yield_Final",
                         "Burn", "Bind", "Unbind", "NewUtxo"}

\* Circuit ops that are ref/coordination operations (no WitLedger equivalent)
RefCircuitOps == {"NewCoord", "GetHandler", "RefCreate", "RefConsume", "RefRead"}

(***************************************************************************
 * SECTION 2: Circuit Wire ↔ TLA+ Variable Map
 *
 * Each circuit wire in StepCircuit maps to a TLA+ expression.
 *
 * Circuit Wire       | TLA+ Expression                        | Module
 * --------------------+----------------------------------------+------------------
 * id_curr            | ivcConfig.id_curr                      | StarstreamCoordination
 * id_prev            | ivcConfig.id_prev                      | StarstreamCoordination
 * activation         | ivcConfig.activation                   | StarstreamCoordination
 * safe_to_ledger     | ivcConfig.safe_to_ledger               | StarstreamCoordination
 * opcode             | witLedgerKind (on effect record)       | StarstreamEffects
 * host_calls_root    | ComputeFrameHash(...)                  | StarstreamFrame
 * process_id         | ProcessIdRange (coord or UTXO)         | StarstreamTypes
 * continuation_id    | continuationId (on effect record)      | StarstreamEffects
 * interface_id       | interfaceId (on effect record)         | StarstreamEffects
 * handler_stack_id   | handlerStackId (on effect record)      | StarstreamEffects
 * handler_id         | handlerId (on handler record)          | StarstreamCoordination
 * value_commitment   | frame.hash                             | StarstreamFrame
 * proof_commitment   | commitmentHash (on proof record)       | StarstreamProof
 * step_number        | stepNumber (on proof record)           | StarstreamProof
 ***************************************************************************)

\* IVC state from coordination (mirrors circuit's IVC accumulator state)
CircuitIVCState(coord) ==
    [id_curr        |-> coord.ivcConfig.id_curr,
     id_prev        |-> coord.ivcConfig.id_prev,
     activation     |-> coord.ivcConfig.activation,
     safe_to_ledger |-> coord.ivcConfig.safe_to_ledger]

\* Process ID classification (matches circuit's is_coordinator/is_utxo checks)
CircuitIsCoordinator(pid) == IsCoordinatorProcessId(pid)
CircuitIsUTXO(pid)        == IsUtxoProcessId(pid)

(***************************************************************************
 * SECTION 3: Per-Step Invariant Map
 *
 * Each circuit constraint maps to one or more TLA+ invariants.
 *
 * Circuit Constraint           | TLA+ Invariant                  | Module
 * -----------------------------+---------------------------------+------------------
 * No self-resume               | INV_EFFECT_NoSelfResume (new)   | This module
 * Continuation linearity       | NoDuplicatePendingEffects       | StarstreamEffects
 * Message matching (dual)      | INV_EFFECT_ContinuationMatch    | StarstreamInvariants
 * Value consistency            | INV_FRAME_Integrity             | StarstreamInvariants
 * Handler installed for op     | INV_EFFECT_EffectsMatchInstalledHandlers | StarstreamInvariants
 * Handler stack depth bounded  | INV_EFFECT_PerInterfaceDepth    | StarstreamInvariants
 * One active opcode per step   | NoDuplicatePendingEffects       | StarstreamEffects
 * Valid process ID range       | INV_PROOF_IntegrityBound        | StarstreamInvariants
 * Proof phase consistency      | INV_PROOF_ConsistentPhase       | StarstreamInvariants
 * IVC config valid             | INV_PROOF_ValidIVCConfig        | StarstreamInvariants
 * Activation state consistent  | INV_CIRCUIT_ActivationConsistent| This module (NEW)
 * Reference arena bounds       | INV_CIRCUIT_RefArenaBounded     | This module (NEW)
 * Handler node linking         | INV_CIRCUIT_HandlerNodeLinked   | This module (NEW)
 ***************************************************************************)

(***************************************************************************
 * SECTION 4: Alignment Validation Predicates
 *
 * These predicates verify that TLA+ state is consistent with what the
 * circuit would expect at each step of the interleaved trace.
 ***************************************************************************)

\* A circuit step is well-formed if the opcode maps to a valid WitLedgerEffectKind
\* and the IVC state is consistent
ValidCircuitStep(coord, effect) ==
    /\ effect.witLedgerKind \in WitLedgerEffectKinds
    /\ ValidIVCConfig(coord)
    /\ coord.ivcConfig.id_curr \in ProcessIdRange
    /\ coord.ivcConfig.activation \in ActivationStates

\* Resume operation alignment: the circuit's resume must match TLA+'s effect handling
\* The target process must not be the source process (no self-resume)
ResumeAligned(coord, effect) ==
    /\ effect.witLedgerKind = "Resume"
    /\ UtxoToProcessId(effect.sourceUtxoId) # coord.ivcConfig.id_curr  \* No self-resume (convert to ProcessId space)
    /\ HasHandlerFor(coord.handlerStacks, effect.interfaceId)
    /\ effect.continuationId \in ContinuationIdRange

\* Yield alignment: the yielding process must be the current IVC process
YieldAligned(coord, effect) ==
    /\ effect.witLedgerKind \in {"Yield_Intermediate", "Yield_Final"}
    /\ UtxoToProcessId(effect.sourceUtxoId) = coord.ivcConfig.id_curr
       \/ IsCoordinatorProcessId(coord.ivcConfig.id_curr)

\* Burn alignment: consumed UTXO must be in the transaction inputs
BurnAligned(tx, effect) ==
    /\ effect.witLedgerKind = "Burn"
    /\ effect.sourceUtxoId \in {u.id : u \in tx.inputs}

\* Bind alignment: handler installation must respect stack bounds
BindAligned(coord, effect) ==
    /\ effect.witLedgerKind = "Bind"
    /\ Len(coord.handlerStacks[effect.interfaceId]) < MAX_HANDLER_DEPTH

\* Unbind alignment: handler removal must have a handler to remove
UnbindAligned(coord, effect) ==
    /\ effect.witLedgerKind = "Unbind"
    /\ HasHandlerFor(coord.handlerStacks, effect.interfaceId)

\* NewUtxo alignment: output IDs must be fresh
NewUtxoAligned(ledger, effect) ==
    /\ effect.witLedgerKind = "NewUtxo"
    /\ ~UTXOExistsInLedger(ledger, effect.sourceUtxoId)

\* Full step alignment: one circuit step passes all relevant checks
StepAligned(ledger, tx, coord, effect) ==
    /\ ValidCircuitStep(coord, effect)
    /\ CASE effect.witLedgerKind = "Resume"
            -> ResumeAligned(coord, effect)
         [] effect.witLedgerKind \in {"Yield_Intermediate", "Yield_Final"}
            -> YieldAligned(coord, effect)
         [] effect.witLedgerKind = "Burn"
            -> BurnAligned(tx, effect)
         [] effect.witLedgerKind = "Bind"
            -> BindAligned(coord, effect)
         [] effect.witLedgerKind = "Unbind"
            -> UnbindAligned(coord, effect)
         [] effect.witLedgerKind = "NewUtxo"
            -> NewUtxoAligned(ledger, effect)
         [] OTHER -> TRUE

(***************************************************************************
 * SECTION 5: NEW Invariants (Circuit-side constraints not in original TLA+)
 *
 * These invariants correspond to circuit constraints that were not
 * previously formalized in the TLA+ specification.
 *
 * NOTE: These invariants reference the `ledger` state variable, which is
 * defined in StarstreamSpec.tla. They are designed to be evaluated in the
 * context of StarstreamInvariants.tla, which EXTENDS StarstreamSpec and
 * this module. Do NOT evaluate these in isolation.
 ***************************************************************************)

\* INV_CIRCUIT_NoSelfResume
\* The circuit enforces that a process cannot resume itself.
\* In TLA+: when handling an effect (Resume), the source UTXO must differ
\* from the currently active process.
INV_CIRCUIT_NoSelfResume(ledger) ==
    \A tx \in ledger.pendingTxs :
        \A e \in PendingEffects(tx.coordination.effectStack) :
            e.witLedgerKind = "Resume" =>
                UtxoToProcessId(e.sourceUtxoId) # tx.coordination.ivcConfig.id_curr

\* INV_CIRCUIT_ActivationConsistent
\* The circuit requires activation state consistency:
\* - Active processes must have valid id_curr
\* - Inactive processes must have id_curr = -1
\* - Suspended processes must have a valid id_prev
INV_CIRCUIT_ActivationConsistent(ledger) ==
    \A tx \in ledger.pendingTxs :
        /\ (tx.coordination.ivcConfig.activation = "Active") =>
            tx.coordination.ivcConfig.id_curr \in ProcessIdRange
        /\ (tx.coordination.ivcConfig.activation = "Inactive") =>
            tx.coordination.ivcConfig.id_curr = -1
        /\ (tx.coordination.ivcConfig.activation = "Suspended") =>
            /\ tx.coordination.ivcConfig.id_curr \in ProcessIdRange
            /\ tx.coordination.ivcConfig.id_prev \in ProcessIdRange

\* INV_CIRCUIT_RefArenaBounded
\* The circuit's reference arena has bounded capacity.
\* In TLA+: the number of active UTXOs per transaction is bounded by inputs + outputs.
INV_CIRCUIT_RefArenaBounded(ledger) ==
    \A tx \in ledger.pendingTxs :
        Cardinality(tx.inputs) + Cardinality(tx.outputs) <= MAX_UTXOS

\* INV_CIRCUIT_HandlerNodeLinked
\* The circuit requires handler stack nodes to form valid linked structures:
\* - Each handler in a stack references the correct interface
\* - Handler IDs are monotonically increasing within a stack
\* - The top handler is the one used for effect dispatch
INV_CIRCUIT_HandlerNodeLinked(ledger) ==
    \A tx \in ledger.pendingTxs :
        \A iface \in InterfaceIdRange :
            LET stack == tx.coordination.handlerStacks[iface]
            IN /\ \A i \in 1..Len(stack) : stack[i].interfaceId = iface
               /\ \A i, j \in 1..Len(stack) :
                    (i < j) => stack[i].handlerId < stack[j].handlerId

\* INV_CIRCUIT_InitializationConsistent
\* The circuit verifies initialization state is consistent with activation:
\* - NotStarted coordination has Inactive IVC config
\* - Complete coordination has safe_to_ledger = TRUE (if proofs verified)
INV_CIRCUIT_InitializationConsistent(ledger) ==
    \A tx \in ledger.pendingTxs :
        /\ (tx.coordination.phase = "NotStarted") =>
            tx.coordination.ivcConfig.activation = "Inactive"
        /\ (tx.coordination.phase = "Complete" /\ AllTxProofsVerified(tx)) =>
            tx.coordination.ivcConfig.safe_to_ledger = TRUE

\* INV_CIRCUIT_EffectOpcodeSingleStep
\* The circuit processes exactly one opcode per IVC step.
\* In TLA+: at most one pending effect per source UTXO at any time.
INV_CIRCUIT_EffectOpcodeSingleStep(ledger) ==
    \A tx \in ledger.pendingTxs :
        NoDuplicatePendingEffects(tx.coordination.effectStack)

\* INV_CIRCUIT_DualTraceConsistency
\* Resume inputs must match yield outputs (the "dual trace" property).
\* This is the core message-matching invariant of the interleaving circuit.
\* Expressed in TLA+: when an effect is handled, the continuation ID must
\* match the source UTXO's frame PC (its yield point).
INV_CIRCUIT_DualTraceConsistency(ledger) ==
    \A tx \in ledger.pendingTxs :
        \A e \in PendingEffects(tx.coordination.effectStack) :
            /\ UTXOExistsInLedger(ledger, e.sourceUtxoId)
            /\ LET u == GetUTXO(ledger, e.sourceUtxoId)
               IN e.continuationId = u.frame.pc

\* INV_CIRCUIT_ValueCommitmentIntegrity
\* The circuit checks that frame hashes (value commitments) are consistent.
\* This binds individual WASM proofs to the aggregate interleaving proof.
INV_CIRCUIT_ValueCommitmentIntegrity(ledger) ==
    \A u \in ledger.utxoSet :
        u.frame.hash = ComputeFrameHash(u.frame.pc, u.frame.locals, u.frame.methodId)

\* Combined circuit alignment invariant
INV_CIRCUIT_All(ledger) ==
    /\ INV_CIRCUIT_NoSelfResume(ledger)
    /\ INV_CIRCUIT_ActivationConsistent(ledger)
    /\ INV_CIRCUIT_RefArenaBounded(ledger)
    /\ INV_CIRCUIT_HandlerNodeLinked(ledger)
    /\ INV_CIRCUIT_InitializationConsistent(ledger)
    /\ INV_CIRCUIT_EffectOpcodeSingleStep(ledger)
    /\ INV_CIRCUIT_DualTraceConsistency(ledger)
    /\ INV_CIRCUIT_ValueCommitmentIntegrity(ledger)

(***************************************************************************
 * SECTION 6: Gap Analysis — Properties NOT in Circuit
 *
 * These are TLA+ invariants that the circuit does NOT enforce.
 * They must be validated at the ledger level or by separate mechanisms.
 *
 * Gap                          | TLA+ Invariant                   | Resolution
 * -----------------------------+----------------------------------+------------------
 * Optimistic concurrency       | INV_OPT_ReadSetConsistent        | Ledger validates
 * Token balance preservation   | INV_BALANCE_TxPreserved          | Separate circuit
 * Authorization/signatures     | INV_AUTH_ValidSpend               | Signature verify
 * Liveness (fairness)          | LIVE_TxEventuallyTerminates      | Runtime concern
 * Read-set validation          | INV_OPT_ReadSetConsistent        | Ledger validates
 * NFT uniqueness               | INV_BALANCE_NFTUnique            | Ledger validates
 * Rollback safety              | INV_ROLLBACK_NoLeak              | Ledger validates
 ***************************************************************************)

\* Predicate: properties the circuit can verify
CircuitVerifiable(tx) ==
    /\ \A e \in FcnRange(tx.coordination.effectStack) :
        /\ e.witLedgerKind \in WitLedgerEffectKinds
        /\ ValidCircuitStep(tx.coordination, e)
    /\ ValidIVCConfig(tx.coordination)

\* Predicate: properties requiring ledger-level validation
RequiresLedgerValidation(tx) ==
    /\ BalancePreserved(tx)
    /\ ValidSignature(tx.signature, tx)
    /\ InputsOwnedBySigner(tx)

\* Complete verification: circuit + ledger together
FullyVerified(ledger, tx) ==
    /\ CircuitVerifiable(tx)
    /\ RequiresLedgerValidation(tx)
    /\ AllTxProofsVerified(tx)

=============================================================================
