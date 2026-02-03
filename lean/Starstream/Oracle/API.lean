import Starstream.Oracle.Idealized

set_option autoImplicit false

namespace Starstream.Oracle

structure TxInput where
  ledger : Ledger
  tx : Tx
  gas : Gas

structure ChunkInput where
  ledger : Ledger
  txs : List Tx
  gasPerTx : Gas

def checkTxInput (cfg : Config) (input : TxInput) : Except Err Unit :=
  checkTx cfg input.ledger input.tx input.gas

def applyTxInput (cfg : Config) (input : TxInput) : Except Err Ledger :=
  applyTx cfg input.ledger input.tx input.gas

/-- Deterministic single-step ledger transition (alias for applyTxInput). -/
def ledgerStep (cfg : Config) (input : TxInput) : Except Err Ledger :=
  applyTxInput cfg input

def applyChunkInput (cfg : Config) (input : ChunkInput) : Except ChunkErr Ledger :=
  applyChunk cfg input.ledger input.txs input.gasPerTx

def checkChunkInput (cfg : Config) (input : ChunkInput) : Except ChunkErr Unit := do
  _ <- applyChunkInput cfg input
  pure ()

end Starstream.Oracle
