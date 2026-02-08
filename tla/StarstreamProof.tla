--------------------------- MODULE StarstreamProof ---------------------------
(***************************************************************************
 * Proof Commitment Types and Operations for Starstream
 *
 * This module formalizes proof validity for IVC alignment:
 * - Proof commitment types (IVC_Step, IVC_Accumulator, Witness)
 * - Proof lifecycle phases
 * - Proof validation predicates
 * - Proof operations for generation and verification
 ***************************************************************************)

EXTENDS StarstreamTypes, StarstreamFrame

(***************************************************************************
 * PROOF COMMITMENT TYPE
 ***************************************************************************)

ProofCommitmentType ==
    [proofKind: ProofKinds,
     ivcProcessId: ProcessIdRange,
     commitmentHash: FrameHashRange,
     verificationKey: 1..10,
     proofData: DatumValues,
     verified: BOOLEAN,
     phase: ProofPhases,
     stepNumber: 0..UTXO_ID_BOUND]

(***************************************************************************
 * PROOF CONSTRUCTORS
 ***************************************************************************)

\* Create a new proof commitment
NewProofCommitment(kind, processId, hash, vk, data) ==
    [proofKind |-> kind,
     ivcProcessId |-> processId,
     commitmentHash |-> hash,
     verificationKey |-> vk,
     proofData |-> data,
     verified |-> FALSE,
     phase |-> "NotStarted",
     stepNumber |-> 0]

\* Create an IVC step proof
IVCStepProof(processId, hash, stepNum) ==
    [proofKind |-> "IVC_Step",
     ivcProcessId |-> processId,
     commitmentHash |-> hash,
     verificationKey |-> 1,
     proofData |-> "Empty",
     verified |-> FALSE,
     phase |-> "NotStarted",
     stepNumber |-> stepNum]

\* Create an IVC accumulator proof
IVCAccumulatorProof(processId, hash) ==
    [proofKind |-> "IVC_Accumulator",
     ivcProcessId |-> processId,
     commitmentHash |-> hash,
     verificationKey |-> 1,
     proofData |-> "Empty",
     verified |-> FALSE,
     phase |-> "NotStarted",
     stepNumber |-> 0]

\* Create a witness proof
WitnessProof(processId, hash, data) ==
    [proofKind |-> "Witness",
     ivcProcessId |-> processId,
     commitmentHash |-> hash,
     verificationKey |-> 1,
     proofData |-> data,
     verified |-> FALSE,
     phase |-> "NotStarted",
     stepNumber |-> 0]

(***************************************************************************
 * PROOF PREDICATES
 ***************************************************************************)

\* Check if a proof record is well-formed
IsProofCommitment(proof) ==
    /\ proof.proofKind \in ProofKinds
    /\ proof.ivcProcessId \in ProcessIdRange
    /\ IsFrameHash(proof.commitmentHash)
    /\ proof.verificationKey \in 1..10
    /\ proof.proofData \in DatumValues
    /\ proof.verified \in BOOLEAN
    /\ proof.phase \in ProofPhases
    /\ proof.stepNumber \in 0..UTXO_ID_BOUND

\* Check if a proof is valid (structurally correct)
IsValidProof(proof) ==
    /\ IsProofCommitment(proof)
    /\ proof.ivcProcessId >= 0

\* Check if a proof has been verified
IsVerifiedProof(proof) ==
    /\ IsValidProof(proof)
    /\ proof.verified
    /\ proof.phase = "Verified"

\* Check if a proof is pending verification
IsPendingProof(proof) ==
    /\ IsValidProof(proof)
    /\ ~proof.verified
    /\ proof.phase \in {"NotStarted", "Generating", "Verifying"}

\* Check if a proof failed verification
IsFailedProof(proof) ==
    /\ IsValidProof(proof)
    /\ ~proof.verified
    /\ proof.phase = "Failed"

\* Check if proof is an IVC step proof
IsIVCStepProof(proof) == proof.proofKind = "IVC_Step"

\* Check if proof is an IVC accumulator proof
IsIVCAccumulatorProof(proof) == proof.proofKind = "IVC_Accumulator"

\* Check if proof is a witness proof
IsWitnessProof(proof) == proof.proofKind = "Witness"

(***************************************************************************
 * PROOF OPERATIONS
 ***************************************************************************)

\* Begin proof generation
BeginProofGeneration(proof) ==
    [proof EXCEPT !.phase = "Generating"]

\* Begin proof verification
BeginProofVerification(proof) ==
    [proof EXCEPT !.phase = "Verifying"]

\* Mark proof as verified
MarkProofVerified(proof) ==
    [proof EXCEPT !.verified = TRUE, !.phase = "Verified"]

\* Mark proof as failed
MarkProofFailed(proof) ==
    [proof EXCEPT !.verified = FALSE, !.phase = "Failed"]

\* Update proof step number
UpdateProofStep(proof, newStep) ==
    [proof EXCEPT !.stepNumber = newStep]

\* Update proof commitment hash (host_calls_roots)
UpdateProofHash(proof, newHash) ==
    [proof EXCEPT !.commitmentHash = newHash]

\* Update proof data
UpdateProofData(proof, newData) ==
    [proof EXCEPT !.proofData = newData]

(***************************************************************************
 * PROOF SET OPERATIONS
 ***************************************************************************)

\* Find a proof by process ID
FindProofByProcessId(proofSet, pid) ==
    IF \E p \in proofSet : p.ivcProcessId = pid
    THEN CHOOSE p \in proofSet : p.ivcProcessId = pid
    ELSE NULL

\* Check if a process has a pending proof
HasPendingProofFor(proofSet, pid) ==
    \E p \in proofSet : p.ivcProcessId = pid /\ IsPendingProof(p)

\* Get all verified proofs
VerifiedProofs(proofSet) ==
    {p \in proofSet : IsVerifiedProof(p)}

\* Get all pending proofs
PendingProofs(proofSet) ==
    {p \in proofSet : IsPendingProof(p)}

\* Get all failed proofs
FailedProofs(proofSet) ==
    {p \in proofSet : IsFailedProof(p)}

\* Add a proof to a set
AddProof(proofSet, proof) == proofSet \cup {proof}

\* Remove a proof from a set
RemoveProof(proofSet, proof) == proofSet \ {proof}

\* Update a proof in a set
UpdateProofInSet(proofSet, oldProof, newProof) ==
    (proofSet \ {oldProof}) \cup {newProof}

(***************************************************************************
 * PROOF INVARIANTS
 ***************************************************************************)

\* All proofs in a set are well-formed
AllProofsValid(proofSet) ==
    \A p \in proofSet : IsValidProof(p)

\* No duplicate process IDs among pending proofs
NoDuplicatePendingProofs(proofSet) ==
    \A p1, p2 \in proofSet :
        (p1 # p2 /\ IsPendingProof(p1) /\ IsPendingProof(p2)) =>
            p1.ivcProcessId # p2.ivcProcessId

\* Verified proofs have consistent state
VerifiedProofsConsistent(proofSet) ==
    \A p \in proofSet :
        IsVerifiedProof(p) => (p.verified /\ p.phase = "Verified")

\* Proof phase transitions are valid
ValidProofPhaseTransition(oldProof, newProof) ==
    \/ (oldProof.phase = "NotStarted" /\ newProof.phase \in {"Generating", "Failed"})
    \/ (oldProof.phase = "Generating" /\ newProof.phase \in {"Verifying", "Failed"})
    \/ (oldProof.phase = "Verifying" /\ newProof.phase \in {"Verified", "Failed"})
    \/ (oldProof.phase = newProof.phase)  \* No change is always valid

=============================================================================
