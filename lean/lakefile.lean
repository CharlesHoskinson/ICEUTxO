import Lake
open Lake DSL

package starstream_lean

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.27.0"

@[default_target]
lean_lib Starstream where
  srcDir := "."
  roots := #[
    `StarstreamPilot,
    `Starstream.Oracle.Idealized,
    `Starstream.Oracle.API,
    `Starstream.Oracle.Proofs.PhaseA,
    `Starstream.Oracle.Proofs.PhaseB,
    `Starstream.Oracle.Proofs.PhaseC,
    `Starstream.Coordination.Script,
    `Starstream.Coordination.PTB,
    `Starstream.Coordination.SBAC,
    `Starstream.ConservativeExtension,
    `Starstream.OptimisticMode
  ]
