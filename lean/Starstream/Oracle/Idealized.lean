import Std.Data.HashSet

set_option autoImplicit false

namespace Starstream.Oracle

open Std

abbrev UtxoId := Nat
abbrev TxId := Nat
abbrev Owner := String
abbrev Hash := String
abbrev TokenType := String
abbrev TokenId := Nat
abbrev TokenKey := Prod TokenType TokenId
abbrev Gas := Nat

structure Sig where
  owner : Owner
  txId : TxId
  contentsHash : Hash
  deriving DecidableEq

structure TokenBag where
  amounts : TokenKey -> Nat

namespace TokenBag

def empty : TokenBag :=
  { amounts := fun _ => 0 }

def add (a b : TokenBag) : TokenBag :=
  { amounts := fun k => a.amounts k + b.amounts k }

def listAll {A} (xs : List A) (p : A -> Bool) : Bool :=
  xs.foldl (fun acc x => acc && p x) true

def eqOn (keys : List TokenKey) (a b : TokenBag) : Bool :=
  listAll keys (fun k => decide (a.amounts k = b.amounts k))

end TokenBag

structure Utxo where
  id : UtxoId
  owner : Owner
  tokens : TokenBag
  datum : Nat

structure Tx where
  id : TxId
  signer : Owner
  inputs : List Utxo
  outputs : List Utxo
  sig : Sig

structure Ledger where
  utxos : List Utxo
  consumed : Std.HashSet UtxoId
  nextUtxoId : UtxoId
  txHistory : List Tx

structure Config where
  tokenKeys : List TokenKey
  hashTx : Tx -> Hash

inductive Err
  | emptyInputs
  | emptyOutputs
  | duplicateInputs
  | duplicateOutputs
  | inputsOutputsOverlap
  | inputMissing (id : UtxoId)
  | inputConsumed (id : UtxoId)
  | outputCollision (id : UtxoId)
  | invalidSignature
  | balanceMismatch
  | outOfGas
  deriving DecidableEq

inductive ChunkErr
  | txError (index : Nat) (err : Err)
  deriving DecidableEq

abbrev listAll {A} (xs : List A) (p : A -> Bool) : Bool :=
  TokenBag.listAll xs p

abbrev setOfList {A} [BEq A] [Hashable A] (xs : List A) : Std.HashSet A :=
  xs.foldl (fun s x => s.insert x) ({} : Std.HashSet A)

abbrev setUnion {A} [BEq A] [Hashable A] (a b : Std.HashSet A) : Std.HashSet A :=
  b.fold (fun s x => s.insert x) a

abbrev setDisjoint {A} [BEq A] [Hashable A] (a b : Std.HashSet A) : Bool :=
  a.fold (fun ok x => ok && !(b.contains x)) true

abbrev UtxoIds (us : List Utxo) : Std.HashSet UtxoId :=
  setOfList (us.map Utxo.id)

abbrev InputIds (tx : Tx) : Std.HashSet UtxoId :=
  UtxoIds tx.inputs

abbrev OutputIds (tx : Tx) : Std.HashSet UtxoId :=
  UtxoIds tx.outputs

abbrev idsNodup (us : List Utxo) : Bool :=
  decide ((us.map Utxo.id).Nodup)

abbrev inputsUnique (tx : Tx) : Bool :=
  idsNodup tx.inputs

abbrev outputsUnique (tx : Tx) : Bool :=
  idsNodup tx.outputs

abbrev inputsDisjointOutputs (tx : Tx) : Bool :=
  setDisjoint (InputIds tx) (OutputIds tx)

abbrev outputsFresh (l : Ledger) (tx : Tx) : Bool :=
  setDisjoint (OutputIds tx) (setUnion (UtxoIds l.utxos) l.consumed)

abbrev inputsLive (l : Ledger) (tx : Tx) : Bool :=
  listAll tx.inputs (fun u => (UtxoIds l.utxos).contains u.id)

abbrev inputsNotConsumed (l : Ledger) (tx : Tx) : Bool :=
  setDisjoint (InputIds tx) l.consumed

abbrev sumTokens (us : List Utxo) : TokenBag :=
  us.foldl (fun acc u => TokenBag.add acc u.tokens) TokenBag.empty

abbrev balancePreserved (cfg : Config) (tx : Tx) : Bool :=
  TokenBag.eqOn cfg.tokenKeys (sumTokens tx.inputs) (sumTokens tx.outputs)

abbrev validSignature (cfg : Config) (tx : Tx) : Bool :=
  decide (tx.sig.owner = tx.signer /\
    tx.sig.txId = tx.id /\
    tx.sig.contentsHash = cfg.hashTx tx)

def spend (g : Gas) : Except Err Gas :=
  if g = 0 then
    .error Err.outOfGas
  else
    .ok (g - 1)

def firstMissingInput (l : Ledger) (tx : Tx) : Option UtxoId :=
  let live := UtxoIds l.utxos
  match tx.inputs.find? (fun u => !(live.contains u.id)) with
  | none => none
  | some u => some u.id

def firstConsumedInput (l : Ledger) (tx : Tx) : Option UtxoId :=
  match tx.inputs.find? (fun u => l.consumed.contains u.id) with
  | none => none
  | some u => some u.id

def firstOutputCollision (l : Ledger) (tx : Tx) : Option UtxoId :=
  let occupied := setUnion (UtxoIds l.utxos) l.consumed
  match tx.outputs.find? (fun u => occupied.contains u.id) with
  | none => none
  | some u => some u.id

def checkTx (cfg : Config) (l : Ledger) (tx : Tx) (gas : Gas) : Except Err Unit := do
  let g <- spend gas
  if tx.inputs = [] then
    throw Err.emptyInputs
  let g <- spend g
  if tx.outputs = [] then
    throw Err.emptyOutputs
  let g <- spend g
  if inputsUnique tx then
    pure ()
  else
    throw Err.duplicateInputs
  let g <- spend g
  if outputsUnique tx then
    pure ()
  else
    throw Err.duplicateOutputs
  let g <- spend g
  if inputsDisjointOutputs tx then
    pure ()
  else
    throw Err.inputsOutputsOverlap
  let g <- spend g
  match firstMissingInput l tx with
  | some id => throw (Err.inputMissing id)
  | none => pure ()
  let g <- spend g
  match firstConsumedInput l tx with
  | some id => throw (Err.inputConsumed id)
  | none => pure ()
  let g <- spend g
  match firstOutputCollision l tx with
  | some id => throw (Err.outputCollision id)
  | none => pure ()
  let g <- spend g
  if validSignature cfg tx then
    pure ()
  else
    throw Err.invalidSignature
  let _ <- spend g
  if balancePreserved cfg tx then
    pure ()
  else
    throw Err.balanceMismatch

def removeInputs (us : List Utxo) (ids : Std.HashSet UtxoId) : List Utxo :=
  us.filter (fun u => !(ids.contains u.id))

abbrev maxId (us : List Utxo) : Nat :=
  us.foldl (fun m u => Nat.max m u.id) 0

def applyTx (cfg : Config) (l : Ledger) (tx : Tx) (gas : Gas) : Except Err Ledger := do
  _ <- checkTx cfg l tx gas
  let inputIds := InputIds tx
  let utxos' := removeInputs l.utxos inputIds ++ tx.outputs
  let consumed' := setUnion l.consumed inputIds
  let history' := l.txHistory ++ [tx]
  let nextUtxoId' := Nat.max l.nextUtxoId (maxId tx.outputs + 1)
  pure { l with utxos := utxos', consumed := consumed', txHistory := history', nextUtxoId := nextUtxoId' }

def applyChunk (cfg : Config) (l : Ledger) (txs : List Tx) (gasPerTx : Gas) : Except ChunkErr Ledger :=
  let rec go (idx : Nat) (lcur : Ledger) (rest : List Tx) : Except ChunkErr Ledger :=
    match rest with
    | [] => .ok lcur
    | tx :: tail =>
        match applyTx cfg lcur tx gasPerTx with
        | .ok lnext => go (idx + 1) lnext tail
        | .error err => .error (ChunkErr.txError idx err)
  go 0 l txs

def chunkValid (cfg : Config) (l : Ledger) (txs : List Tx) (gasPerTx : Gas) : Prop :=
  match applyChunk cfg l txs gasPerTx with
  | .ok _ => True
  | .error _ => False

end Starstream.Oracle
