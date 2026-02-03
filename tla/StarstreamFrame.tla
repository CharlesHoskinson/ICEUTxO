--------------------------- MODULE StarstreamFrame ---------------------------
(***************************************************************************
 * Stackless Coroutine Frame for Starstream
 *
 * Models the execution frame of a UTXO's coroutine, containing:
 * - Program counter (PC) for resumption point
 * - Local variables storage
 * - Method identifier for dispatch
 * - Frame hash for integrity checking
 ***************************************************************************)

EXTENDS StarstreamTypes

(***************************************************************************
 * FRAME RECORD TYPE
 ***************************************************************************)

\* Hash of a frame is modeled as a tuple of its contents.
ComputeFrameHash(pc, locals, methodId) == <<pc, locals, methodId>>

FrameHashRange == {<<pc, locals, methodId>> : pc \in PCRange, locals \in LocalsType, methodId \in MethodIdRange}

FrameSet ==
    [pc: PCRange,
     locals: LocalsType,
     methodId: MethodIdRange,
     hash: FrameHashRange]

(***************************************************************************
 * FRAME CONSTRUCTORS
 ***************************************************************************)

InitFrame(method) ==
    LET locals == [v \in VarNames |-> NULL]
        hash == ComputeFrameHash(0, locals, method)
    IN [pc |-> 0, locals |-> locals, methodId |-> method, hash |-> hash]

FrameAtYield(yieldPoint, vars, method) ==
    LET hash == ComputeFrameHash(yieldPoint, vars, method)
    IN [pc |-> yieldPoint, locals |-> vars, methodId |-> method, hash |-> hash]

TerminatedFrame(method) ==
    LET locals == [v \in VarNames |-> NULL]
        hash == ComputeFrameHash(-1, locals, method)
    IN [pc |-> -1, locals |-> locals, methodId |-> method, hash |-> hash]

(***************************************************************************
 * FRAME PREDICATES
 ***************************************************************************)

IsFrame(f) ==
    /\ IsValidPC(f.pc)
    /\ f.locals \in LocalsType
    /\ f.methodId \in MethodIdRange
    /\ f.hash = ComputeFrameHash(f.pc, f.locals, f.methodId)

IsInitialFrame(f) == /\ IsFrame(f) /\ f.pc = 0
IsTerminatedFrame(f) == /\ IsFrame(f) /\ f.pc = -1
IsSuspendedFrame(f) == /\ IsFrame(f) /\ f.pc > 0 /\ f.pc # -1
IsResumableFrame(f) == /\ IsFrame(f) /\ f.pc >= 0 /\ f.pc # -1

(***************************************************************************
 * FRAME OPERATIONS
 ***************************************************************************)

Rehash(frame) == [frame EXCEPT !.hash = ComputeFrameHash(frame.pc, frame.locals, frame.methodId)]

AdvancePC(frame, newPC) ==
    Rehash([frame EXCEPT !.pc = newPC])

SetLocal(frame, varName, value) ==
    Rehash([frame EXCEPT !.locals[varName] = value])

GetLocal(frame, varName) == frame.locals[varName]

SetLocals(frame, updates) ==
    Rehash([frame EXCEPT !.locals = [v \in VarNames |->
        IF v \in DOMAIN updates THEN updates[v] ELSE frame.locals[v]]])

Terminate(frame) ==
    Rehash([frame EXCEPT !.pc = -1])

Resume(frame, newPC, newLocals) ==
    LET hash == ComputeFrameHash(newPC, newLocals, frame.methodId)
    IN [pc |-> newPC, locals |-> newLocals, methodId |-> frame.methodId, hash |-> hash]

(***************************************************************************
 * FRAME TRANSITIONS
 ***************************************************************************)

ExecuteToYield(frame, yieldPC, resultVar, resultVal) ==
    LET updated == SetLocal(frame, resultVar, resultVal)
    IN AdvancePC(updated, yieldPC)

ExecuteToTerminate(frame, resultVar, resultVal) ==
    LET updated == SetLocal(frame, resultVar, resultVal)
    IN Terminate(updated)

SuspendForEffect(frame, effectPC) ==
    AdvancePC(frame, effectPC)

ResumeFromEffect(frame, newPC, handlerResult) ==
    LET updated == SetLocal(frame, "result", handlerResult)
    IN AdvancePC(updated, newPC)

=============================================================================
