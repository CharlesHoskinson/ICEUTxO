--------------------- MODULE StarstreamSessionProtocol ---------------------
(***************************************************************************
 * Effect Handler Protocol as Session Types in TLA+ Guards
 *
 * This module formalizes the handler install/uninstall/get protocol using
 * session-type-like constraints expressed as TLA+ action guards.
 *
 * Session types constrain intra-transaction protocols. They do NOT define
 * ledger-level concurrency (that's the interleaving model). Instead, they
 * ensure that effect/handler interactions within a transaction follow
 * correct sequencing, linearity, and matching rules.
 *
 * PROTOCOL OVERVIEW:
 *
 * The effect handler protocol defines valid sequences of operations on
 * handler stacks and effect stacks within a single transaction. The
 * protocol has three participants:
 *   1. Coroutine (UTXO program) — raises effects, receives resume values
 *   2. Coordination script — orchestrates handler installation and dispatch
 *   3. Handler — installed on an interface, handles effects, produces values
 *
 * SESSION TYPE (informal):
 *   Coroutine = !Raise(tag, payload, iface) . ?Resume(value) . Coroutine
 *             | end
 *
 *   Handler   = ?Effect(tag, payload) . !Result(value) . Handler
 *             | end
 *
 *   Coord     = InstallHandler(iface) . Coord
 *             | UninstallHandler(iface) . Coord
 *             | !Dispatch(effect, handler) . ?Result(value) . Coord
 *             | Commit
 *
 * PROTOCOL PHASES:
 *   1. Setup — Install handlers on interfaces
 *   2. Execution — Coroutines run, raise effects, effects are dispatched
 *   3. Teardown — Uninstall handlers, finalize
 *   4. Commit — No pending effects, all handlers consistent
 *
 * FORMALIZATION APPROACH:
 *   Each session-type constraint is encoded as a TLA+ predicate that
 *   serves as an action guard (precondition). The conjunction of these
 *   guards ensures the protocol is followed.
 ***************************************************************************)

EXTENDS StarstreamTypes, StarstreamFrame, StarstreamEffects,
        StarstreamCoordination

(***************************************************************************
 * SECTION 1: Protocol State Machine
 *
 * The handler protocol follows a state machine within each transaction.
 * This state machine is orthogonal to the coordination phase machine
 * but constrains which operations are valid at each point.
 ***************************************************************************)

\* Protocol states for a single interface within a transaction
ProtocolStates == {
    "Uninitialized",   \* No handler installed
    "Ready",           \* Handler installed, awaiting effects
    "Dispatching",     \* Effect raised, handler processing
    "Completed"        \* Handler uninstalled or tx complete
}

\* Derive the protocol state for an interface within a coordination
InterfaceProtocolState(coord, iface) ==
    LET hasHandler == HasHandlerFor(coord.handlerStacks, iface)
        hasPending == PendingEffectsForInterface(coord, iface) # {}
    IN CASE ~hasHandler /\ ~hasPending -> "Uninitialized"
         [] hasHandler /\ ~hasPending  -> "Ready"
         [] hasHandler /\ hasPending   -> "Dispatching"
         [] ~hasHandler /\ hasPending  -> "Uninitialized"  \* Error state
         [] OTHER                      -> "Uninitialized"

(***************************************************************************
 * SECTION 2: Session Type Guards (Action Preconditions)
 *
 * Each guard corresponds to a session-type rule. The guards are used
 * as conjuncts in the action definitions in StarstreamSpec.tla.
 ***************************************************************************)

\* GUARD: InstallHandler is valid
\* Session type rule: handler can only be installed when interface is
\* Uninitialized or Ready (stacking), and stack depth allows it.
\*
\* Session notation: Coord = InstallHandler(iface) . Coord
\* Precondition: no pending effects on this interface during install
GuardInstallHandler(coord, iface) ==
    /\ Len(coord.handlerStacks[iface]) < MAX_HANDLER_DEPTH
    /\ PendingEffectsForInterface(coord, iface) = {}

\* GUARD: UninstallHandler is valid
\* Session type rule: handler can only be removed when no effects are
\* pending on that interface (all dispatched effects must be resolved).
\*
\* Session notation: Coord = UninstallHandler(iface) . Coord
\* Precondition: interface is in Ready state (no pending effects)
GuardUninstallHandler(coord, iface) ==
    /\ HasHandlerFor(coord.handlerStacks, iface)
    /\ PendingEffectsForInterface(coord, iface) = {}

\* GUARD: RaiseEffect is valid
\* Session type rule: a coroutine can raise an effect only if a handler
\* is installed for the target interface and the coroutine doesn't already
\* have a pending effect.
\*
\* Session notation: Coroutine = !Raise(tag, payload, iface) . ?Resume(value)
\* Precondition: handler exists, no duplicate pending for this source
GuardRaiseEffect(coord, iface, sourceUtxoId) ==
    /\ HasHandlerFor(coord.handlerStacks, iface)
    /\ sourceUtxoId \notin UTXOsWithPendingEffects(coord)

\* GUARD: HandleEffect (dispatch to handler) is valid
\* Session type rule: an effect can be handled only if there is a pending
\* effect on the interface and the handler is still installed.
\*
\* Session notation: Handler = ?Effect(tag, payload) . !Result(value)
\* Precondition: interface has pending effects and a handler
GuardHandleEffect(coord, iface) ==
    /\ HasHandlerFor(coord.handlerStacks, iface)
    /\ PendingEffectsForInterface(coord, iface) # {}

\* GUARD: GetHandler (route effect to handler) is valid
\* Session type rule: looking up a handler requires the interface to have
\* at least one handler installed.
\*
\* Session notation: Coord = !Dispatch(effect, handler) . ?Result(value)
\* Precondition: handler stack is non-empty for the target interface
GuardGetHandler(coord, iface) ==
    HasHandlerFor(coord.handlerStacks, iface)

\* GUARD: Commit is valid (from protocol perspective)
\* Session type rule: a transaction can commit only when all effects
\* are resolved and the protocol is in a terminal state.
\*
\* Session notation: Coord = Commit
\* Precondition: no pending effects on any interface
GuardProtocolCommit(coord) ==
    /\ ~HasPendingEffects(coord)
    /\ IsComplete(coord)

(***************************************************************************
 * SECTION 3: Protocol Sequencing Rules
 *
 * These predicates encode the valid orderings of protocol operations.
 * They correspond to session-type sequencing constraints.
 ***************************************************************************)

\* Rule: Install-before-Raise
\* A handler must be installed on an interface before any effect can be
\* raised on that interface. This is enforced by GuardRaiseEffect.
InstallBeforeRaise(coord, iface) ==
    PendingEffectsForInterface(coord, iface) # {} =>
        HasHandlerFor(coord.handlerStacks, iface)

\* Rule: Raise-before-Handle
\* An effect must be raised before it can be handled. This is enforced
\* by GuardHandleEffect requiring pending effects.
RaiseBeforeHandle(coord, iface) ==
    TRUE  \* Enforced by GuardHandleEffect structure

\* Rule: Handle-before-Resume
\* The handler must produce a result before the coroutine can resume.
\* This is enforced by the effect stack: handling pops the effect and
\* the resume value is passed back to the coroutine.
HandleBeforeResume ==
    TRUE  \* Enforced by HandleTopEffect / HandleEffectInCoord structure

\* Rule: All-Handled-before-Commit
\* All effects must be handled before the transaction can commit.
\* This is the terminal condition of the session protocol.
AllHandledBeforeCommit(coord) ==
    IsComplete(coord) => ~HasPendingEffects(coord)

\* Rule: No-Self-Resume (from circuit alignment)
\* A process cannot resume itself. The handler dispatching the resume
\* must target a different process than the one that raised the effect.
NoSelfResume(coord, effect) ==
    UtxoToProcessId(effect.sourceUtxoId) # coord.ivcConfig.id_curr

(***************************************************************************
 * SECTION 4: Linearity Constraints
 *
 * Session types enforce linearity: each effect is raised exactly once,
 * handled exactly once, and consumed exactly once. These constraints
 * map to TLA+ invariants.
 ***************************************************************************)

\* Each UTXO has at most one pending effect at a time
EffectLinearity(coord) ==
    NoDuplicatePendingEffects(coord.effectStack)

\* Each effect is handled by exactly one handler (the top of the stack)
HandlerLinearity(coord) ==
    \A e \in PendingEffects(coord.effectStack) :
        RouteEffectToHandler(coord.handlerStacks, e) # NULL

\* Continuation IDs are unique among pending effects
ContinuationLinearity(coord) ==
    \A i, j \in 1..Len(coord.effectStack) :
        (i # j /\ ~coord.effectStack[i].handled /\ ~coord.effectStack[j].handled)
        => coord.effectStack[i].continuationId # coord.effectStack[j].continuationId

(***************************************************************************
 * SECTION 5: Protocol Well-Formedness
 *
 * A coordination state satisfies the handler protocol if all session-type
 * constraints are met. This is the conjunction of all guards and rules.
 ***************************************************************************)

\* Full protocol well-formedness predicate
ProtocolWellFormed(coord) ==
    /\ \A iface \in InterfaceIdRange :
        /\ InstallBeforeRaise(coord, iface)
    /\ AllHandledBeforeCommit(coord)
    /\ EffectLinearity(coord)
    /\ HandlerLinearity(coord)
    /\ ContinuationLinearity(coord)
    /\ ValidHandlerStacks(coord)
    /\ InstalledHandlersConsistent(coord)

\* Protocol invariant: all pending transactions satisfy the protocol
INV_PROTOCOL_WellFormed(ledger) ==
    \A tx \in ledger.pendingTxs :
        ProtocolWellFormed(tx.coordination)

(***************************************************************************
 * SECTION 6: UTXO Lifecycle as Session Type
 *
 * The lifecycle of a UTXO within a transaction can be viewed as a
 * session type. This section formalizes that view.
 *
 * UTXO Lifecycle Protocol:
 *   Created . (Yield . (HandleEffect . Resume)*) . Consume
 *
 * Breakdown:
 *   - Created: initial state, UTXO has been constructed
 *   - Yield: coroutine yields control, suspending at a yield point
 *   - HandleEffect: an effect is raised and handled
 *   - Resume: coroutine resumes after handler produces a value
 *   - Consume: UTXO is consumed (spent), terminal state
 *
 * State machine:
 *   Created → Suspended_at_Yield → Reserved → Executing → ...
 *   Executing → Suspended_at_Effect → Executing → ...
 *   Executing → Consumed (terminal)
 ***************************************************************************)

\* Valid UTXO state transitions (session type transitions)
ValidUTXOTransition(fromState, toState) ==
    \/ (fromState = "Created" /\ toState = "Suspended_at_Yield")
    \/ (fromState = "Suspended_at_Yield" /\ toState = "Reserved")
    \/ (fromState = "Reserved" /\ toState = "Executing")
    \/ (fromState = "Executing" /\ toState = "Suspended_at_Effect")
    \/ (fromState = "Executing" /\ toState = "Suspended_at_Yield")
    \/ (fromState = "Executing" /\ toState = "Consumed")
    \/ (fromState = "Suspended_at_Effect" /\ toState = "Executing")
    \/ (fromState = "Reserved" /\ toState = "Suspended_at_Yield")  \* Release

\* UTXO lifecycle invariant: all transitions follow the session type
INV_UTXO_SessionType(ledger, ledgerNext) ==
    \A u \in ledger.utxoSet :
        \E uNext \in ledgerNext.utxoSet :
            u.id = uNext.id =>
                (u.state # uNext.state =>
                    ValidUTXOTransition(u.state, uNext.state))

(***************************************************************************
 * SECTION 7: Effect Protocol as Session Type
 *
 * The effect protocol between a coroutine and a handler is a binary
 * session type. This section formalizes the dual roles.
 *
 * Coroutine endpoint (client):
 *   S_c = !Raise(tag, payload) . ?Resume(value) . S_c
 *       | end
 *
 * Handler endpoint (server):
 *   S_h = ?Effect(tag, payload) . !Result(value) . S_h
 *       | end
 *
 * Duality: S_c is dual to S_h (send/receive roles are swapped).
 *
 * In TLA+: duality is enforced by the effect stack operations:
 * - RaiseEffectOp pushes an effect (coroutine sends)
 * - HandleTopEffect pops and marks handled (handler receives and sends result)
 * - Resume passes the result back (coroutine receives)
 ***************************************************************************)

\* Duality check: for every pending effect, a handler exists
DualityCheck(coord) ==
    \A e \in PendingEffects(coord.effectStack) :
        HasHandlerFor(coord.handlerStacks, e.interfaceId)

\* Effect matching: raised effect tag must be in the handler's effect mask
\* Note: handler cannot be NULL for pending effects (enforced by DualityCheck).
\* This is a conjunction, not an implication, to fail when handler is missing.
EffectTagMatching(coord) ==
    \A e \in PendingEffects(coord.effectStack) :
        LET handler == GetHandlerFor(coord.handlerStacks, e.interfaceId)
        IN /\ handler # NULL
           /\ e.tag \in handler.effectMask

\* Combined session protocol check for a coordination
SessionProtocolValid(coord) ==
    /\ ProtocolWellFormed(coord)
    /\ DualityCheck(coord)
    /\ EffectTagMatching(coord)

(***************************************************************************
 * SECTION 8: Protocol Composition
 *
 * When multiple interfaces are active in a transaction, their protocols
 * compose. This section defines how independent interface protocols
 * compose without interference.
 *
 * Composition rule: interfaces are independent if they don't share
 * handlers or effects. The composition is parallel (interleaved).
 ***************************************************************************)

\* Two interfaces are independent within a coordination
InterfacesIndependent(coord, iface1, iface2) ==
    /\ iface1 # iface2
    /\ FcnRange(coord.handlerStacks[iface1]) \cap
       FcnRange(coord.handlerStacks[iface2]) = {}

\* All active interfaces can operate independently
InterfaceIsolation(coord) ==
    \A i1, i2 \in InterfaceIdRange :
        (i1 # i2) => InterfacesIndependent(coord, i1, i2)

=============================================================================
