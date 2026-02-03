import StarstreamPilot
import Starstream.Coordination.Script

namespace Starstream

/-! # SBAC Bridge Layer (Coordination Scripts + Ledger)

This file introduces *minimal* SBAC-facing predicates that connect
coordination-script witnesses to the existing ledger commit guards.
It does NOT model full network/protocol messaging; it only defines
the logical checks that a shard would perform in its prepare step.

We keep this lightweight to avoid breaking prior formalizations.
-/

abbrev ShardId := Nat

structure SBACConfig where
  shardOfUtxo : UTXOId → ShardId
  rolesOfShard : ShardId → Finset RoleId

structure CoordWitness where
  script : Script
  trace  : List EventId

def witnessGlobalOK (w : CoordWitness) : Prop :=
  Script.globalConform w.script w.trace

def witnessConsistent (w : CoordWitness) : Prop :=
  Script.traceConsistent w.script w.trace

def witnessLocalOK (w : CoordWitness) : Prop :=
  ∀ r ∈ w.script.roles,
    Script.localConform w.script r (w.script.traceProj r w.trace)

theorem witnessLocalOK_of_global (w : CoordWitness) (h : witnessGlobalOK w) :
    witnessLocalOK w := by
  intro r hr
  exact proj_localConform_of_globalConform w.script r w.trace h

theorem witnessGlobalOK_of_local_and_consistent (w : CoordWitness)
    (hwf : w.script.wellFormed)
    (hcons : witnessConsistent w) :
    witnessGlobalOK w := by
  exact globalConform_of_consistent w.script w.trace hwf hcons

structure CoordTx where
  tx      : Tx
  witness : CoordWitness

def coordCommitEnabled (m : Mode) (l : Ledger) (ctx : CoordTx) : Prop :=
  commitEnabledStrong m l ctx.tx ∧ witnessGlobalOK ctx.witness

def coordCommitEnabledLocal (m : Mode) (l : Ledger) (ctx : CoordTx) : Prop :=
  commitEnabledStrong m l ctx.tx ∧ witnessLocalOK ctx.witness

theorem coordCommitEnabledLocal_of_global {m : Mode} {l : Ledger} {ctx : CoordTx} :
    coordCommitEnabled m l ctx → coordCommitEnabledLocal m l ctx := by
  intro h
  rcases h with ⟨hcommit, hglob⟩
  exact ⟨hcommit, witnessLocalOK_of_global ctx.witness hglob⟩

def concernedUtxos (tx : Tx) : Finset UTXOId :=
  tx.inputs ∪ tx.readSet ∪ tx.outputs

def concernedShards (cfg : SBACConfig) (tx : Tx) : Finset ShardId :=
  (concernedUtxos tx).image cfg.shardOfUtxo

/-! ## Shard-local check (logical) -/

def shardLocalCheck (cfg : SBACConfig) (sh : ShardId) (l : Ledger) (ctx : CoordTx) : Prop :=
  -- local trace conformance for shard-associated roles
  (∀ r ∈ cfg.rolesOfShard sh,
      Script.localConform ctx.witness.script r
        (ctx.witness.script.traceProj r ctx.witness.trace)) ∧
  -- local UTXO liveness check (restrict inputs to shard)
  ((ctx.tx.inputs.filter (fun u => cfg.shardOfUtxo u = sh)) ⊆ l.utxos)

end Starstream
