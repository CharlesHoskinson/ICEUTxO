--------------------------- MODULE StarstreamTypes ---------------------------
(***************************************************************************
 * Foundation Types for Starstream UTXO/Transaction Protocol
 *
 * This module defines all constants, enumerations, and type sets used
 * throughout the Starstream TLA+ specification.
 ***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

(***************************************************************************
 * MODEL CHECKING BOUNDS
 ***************************************************************************)

CONSTANTS
    MAX_UTXOS,          \* Maximum UTXOs in ledger (e.g., 3)
    MAX_TX_INPUTS,      \* Maximum inputs per transaction (e.g., 2)
    MAX_TX_OUTPUTS,     \* Maximum outputs per transaction (e.g., 2)
    MAX_FRAME_VARS,     \* Maximum local variables in Frame (e.g., 4)
    MAX_PENDING_TXS,    \* Maximum concurrent pending transactions (e.g., 2)
    MAX_TOKEN_TOTAL,    \* Max total tokens per asset to model overflow bounds
    UTXO_ID_BOUND,      \* Maximum UTXO identifier value (e.g., 8)
    CHAIN_ID,           \* Chain identifier (prevents cross-chain replay)
    BLOCK_HEIGHT,       \* Chain height (prevents cross-height replay)
    TOKEN_TYPES,        \* Set of token types (e.g., {"ADA", "NFT"})
    TOKEN_IDS,          \* Set of token IDs (e.g., {1,2,3})
    MAX_COORDINATORS,   \* Number of coordinator processes (e.g., 2)
    MAX_INTERFACES,     \* Number of effect interfaces (e.g., 3)
    MAX_HANDLER_DEPTH,  \* Maximum handler stack depth per interface (e.g., 3)
    MAX_EFFECT_FUEL     \* Maximum fuel per effect for termination (e.g., 10)

(***************************************************************************
 * DERIVED CONSTANTS
 ***************************************************************************)

\* Range of valid UTXO identifiers
UTXOIdRange == 1..UTXO_ID_BOUND

\* Range of valid transaction identifiers
TxIdRange == 1..UTXO_ID_BOUND

\* Range of valid program counter values (0 = initial, -1 = terminated)
PCRange == -1..10

\* Range of valid method identifiers
MethodIdRange == 0..5

\* Range of token quantities
TokenQuantityRange == 0..2

\* Range of continuation identifiers
ContinuationIdRange == 0..UTXO_ID_BOUND

\* Effect stack depth bound (derived)
MAX_EFFECT_DEPTH == MAX_TX_INPUTS

\* Fuel range for effect termination
FuelRange == 0..MAX_EFFECT_FUEL

\* Chain context ranges
ChainIdRange == 0..10
BlockHeightRange == 0..UTXO_ID_BOUND

(***************************************************************************
 * PROCESSID MAPPING (IVC Alignment)
 *
 * Unified ProcessId: coordinators [0..MAX_COORDINATORS-1], UTXOs [MAX_COORDINATORS..]
 * This maps the IVC prototype's ProcessId concept to TLA+ state.
 ***************************************************************************)

CoordinatorIdRange == 0..(MAX_COORDINATORS - 1)
ProcessIdRange == 0..(MAX_COORDINATORS + UTXO_ID_BOUND - 1)
InterfaceIdRange == 1..MAX_INTERFACES

IsUtxoProcessId(pid) == pid >= MAX_COORDINATORS
IsCoordinatorProcessId(pid) == pid < MAX_COORDINATORS
UtxoToProcessId(utxoId) == MAX_COORDINATORS + utxoId - 1
ProcessIdToUtxo(pid) == pid - MAX_COORDINATORS + 1

(***************************************************************************
 * ENUMERATIONS
 ***************************************************************************)

\* UTXO lifecycle states
UTXOStates == {
    "Created",              \* Just created, not yet yielded
    "Suspended_at_Yield",   \* Yielded, waiting for next action
    "Suspended_at_Effect",  \* Raised an effect, waiting for handler
    "Reserved",             \* Locked by a pending transaction
    "Executing",            \* Running in tx context
    "Consumed"              \* Consumed/spent (final state)
}

\* Effect kinds (from language-spec)
EffectKinds == {
    "Pure",         \* No side effects
    "Effectful",    \* Has side effects but reversible
    "Runtime"       \* Runtime effects (IO, storage, etc.)
}

\* Effect tags (small bounded domain for model checking)
EffectTags == {"E1", "E2", "E3"}

\* Method call types for coordination
CallTypes == {
    "Query",    \* Read-only operation
    "Mutate",   \* Modify UTXO state
    "Consume"   \* Spend/destroy UTXO
}

\* Transaction phases/states
TxStates == {
    "Idle",
    "Reserve",
    "Executing",
    "Committing",
    "Rollback",
    "Committed",
    "Failed"
}

\* Coordination script phases
CoordPhases == {
    "NotStarted",
    "Gathering",    \* Gathering inputs
    "Processing",   \* Processing calls
    "Finalizing",   \* Creating outputs
    "Complete"
}

(***************************************************************************
 * IVC-ALIGNED ENUMERATIONS
 ***************************************************************************)

\* WitLedgerEffect kinds from IVC interleaving prototype
WitLedgerEffectKinds == {
    "Resume",             \* Resume execution
    "Yield_Intermediate", \* Intermediate yield point
    "Yield_Final",        \* Final yield (end of handler)
    "Burn",               \* Consume/spend UTXO
    "Bind",               \* Bind handler to interface
    "Unbind",             \* Remove handler from interface
    "NewUtxo"             \* Create new UTXO
}

\* Activation states for IVC state configuration
ActivationStates == {"Inactive", "Active", "Suspended"}

\* Proof kinds for IVC verification
ProofKinds == {"IVC_Step", "IVC_Accumulator", "Witness"}

\* Proof phases for proof lifecycle
ProofPhases == {"NotStarted", "Generating", "Verifying", "Verified", "Failed"}

(***************************************************************************
 * TYPE SETS FOR TLC EFFICIENCY
 ***************************************************************************)

\* Set of possible variable names (for Frame locals)
VarNames == {"x", "y", "z", "result", "temp", "acc", "idx", "flag"}

\* Set of possible contract identifiers
ContractIds == {"Escrow", "Token", "Auction", "Vault", "DEX"}

\* Set of possible owner addresses
OwnerAddrs == {"Alice", "Bob", "Charlie", "Contract", "Treasury"}

\* Datum value domain (simplified)
DatumValues == {"Empty", "Locked", "Unlocked", "Pending", "Complete",
                "V0", "V1", "V2", "V3"}

(***************************************************************************
 * IVC-ALIGNED TYPE SETS
 ***************************************************************************)

\* IVC State Configuration (maps id_curr, id_prev, activation, safe_to_ledger)
IVCStateConfigType ==
    [id_curr: ProcessIdRange \cup {-1},
     id_prev: ProcessIdRange \cup {-1},
     activation: ActivationStates,
     safe_to_ledger: BOOLEAN]

\* Handler record for per-interface handler stacks
HandlerRecordSet ==
    [handlerId: 1..MAX_HANDLER_DEPTH,
     interfaceId: InterfaceIdRange,
     installedBy: ProcessIdRange,
     effectMask: SUBSET EffectTags,
     priority: 0..10]

\* Default IVC configuration
DefaultIVCConfig ==
    [id_curr |-> -1,
     id_prev |-> -1,
     activation |-> "Inactive",
     safe_to_ledger |-> FALSE]

(***************************************************************************
 * RECORD TYPE CONSTRUCTORS
 ***************************************************************************)

\* NULL value for optional fields (used in locals)
NULL == "NULL"

\* Sentinel for "no transaction" (used for lockedBy)
NO_TX == 0

\* Token bag type: mapping from token type -> token id -> quantity
TokenBagType == [TOKEN_TYPES -> [TOKEN_IDS -> TokenQuantityRange]]

\* Empty token bag
EmptyTokenBag == [t \in TOKEN_TYPES |-> [id \in TOKEN_IDS |-> 0]]

\* Frame locals type: mapping from variable name to value
LocalsType == [VarNames -> DatumValues \cup {NULL}]

(***************************************************************************
 * FOLD HELPERS (Define folds for sets and sequences)
 ***************************************************************************)

RECURSIVE FoldSet(_, _, _)
FoldSet(f(_, _), acc, s) ==
    IF s = {} THEN acc
    ELSE
        LET x == CHOOSE y \in s : TRUE
        IN FoldSet(f, f(acc, x), s \ {x})

RECURSIVE FoldSeq(_, _, _)
FoldSeq(f(_, _), acc, seq) ==
    IF Len(seq) = 0 THEN acc
    ELSE FoldSeq(f, f(acc, seq[1]), SubSeq(seq, 2, Len(seq)))

FcnRange(f) == { f[x] : x \in DOMAIN f }

\* Sum values in a set of naturals (for potential function)
SumSet(s) == FoldSet(LAMBDA a, b : a + b, 0, s)

\* Sum values of a function over its domain (for fuel potential)
FcnSum(f) == SumSet({ f[x] : x \in DOMAIN f })

(***************************************************************************
 * TYPE PREDICATES
 ***************************************************************************)

IsValidUTXOId(id) == id \in UTXOIdRange
IsValidUTXOState(s) == s \in UTXOStates
IsValidPC(pc) == pc \in PCRange
IsValidEffectKind(k) == k \in EffectKinds
IsValidCallType(ct) == ct \in CallTypes

IsValidTokenBag(bag) ==
    /\ DOMAIN bag = TOKEN_TYPES
    /\ \A t \in TOKEN_TYPES : DOMAIN bag[t] = TOKEN_IDS
    /\ \A t \in TOKEN_TYPES : \A id \in TOKEN_IDS : bag[t][id] \in TokenQuantityRange

(***************************************************************************
 * TOKEN BAG OPERATIONS
 ***************************************************************************)

AddTokenBags(bag1, bag2) ==
    [t \in TOKEN_TYPES |->
        [id \in TOKEN_IDS |-> bag1[t][id] + bag2[t][id]]]

TokenBagsEqual(bag1, bag2) ==
    \A t \in TOKEN_TYPES : \A id \in TOKEN_IDS : bag1[t][id] = bag2[t][id]

SumTokenBags(utxoSet) ==
    FoldSet(LAMBDA acc, u : AddTokenBags(acc, u.tokens), EmptyTokenBag, utxoSet)

TotalValue(bag) ==
    LET weight(t) == IF t = "ADA" THEN 1 ELSE 10
        SumIds(t) == FoldSet(LAMBDA acc, id : acc + bag[t][id], 0, TOKEN_IDS)
    IN FoldSet(LAMBDA acc, t : acc + (weight(t) * SumIds(t)), 0, TOKEN_TYPES)

=============================================================================
