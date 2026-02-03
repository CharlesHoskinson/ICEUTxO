import Starstream.Oracle.Idealized

set_option autoImplicit false

namespace Starstream.Oracle

private theorem bind_ok {α β} (a : α) (f : α -> Except Err β) :
    Bind.bind (m := Except Err) (Except.ok a) f = f a := by
  rfl

private theorem bind_error {α β} (e : Err) (f : α -> Except Err β) :
    Bind.bind (m := Except Err) (Except.error e) f = Except.error e := by
  rfl

private theorem map_ok {α β} (f : α -> β) (a : α) :
    Functor.map (self := (inferInstance : Functor (Except Err))) f (Except.ok a) =
      Except.ok (f a) := by
  rfl

private theorem map_error {α β} (f : α -> β) (e : Err) :
    Functor.map (self := (inferInstance : Functor (Except Err))) f (Except.error e) =
      Except.error e := by
  rfl

private theorem checkTx_ok_implies_inputs_nonempty
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} :
    checkTx cfg l tx gas = .ok () -> Not (tx.inputs = []) := by
  intro h hnil
  cases gas with
  | zero =>
      cases (by simpa [checkTx, spend] using h)
  | succ g =>
      cases (by simpa [checkTx, spend, hnil] using h)

private theorem checkTx_ok_implies_outputs_nonempty
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} :
    checkTx cfg l tx gas = .ok () -> Not (tx.outputs = []) := by
  intro h hnil
  have hinputs : Not (tx.inputs = []) :=
    checkTx_ok_implies_inputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  cases gas with
  | zero =>
      cases (by simpa [checkTx, spend] using h)
  | succ g1 =>
      cases g1 with
      | zero =>
          cases (by simpa [checkTx, spend, hinputs] using h)
      | succ g2 =>
          cases (by simpa [checkTx, spend, hinputs, hnil] using h)

private theorem checkTx_ok_implies_inputs_unique
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} :
    checkTx cfg l tx gas = .ok () -> inputsUnique tx = true := by
  intro h
  have hinputs : Not (tx.inputs = []) :=
    checkTx_ok_implies_inputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputs : Not (tx.outputs = []) :=
    checkTx_ok_implies_outputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  by_cases huniq : inputsUnique tx = true
  case pos =>
    exact huniq
  case neg =>
    cases gas with
    | zero =>
        cases (by simpa [checkTx, spend] using h)
    | succ g1 =>
        cases g1 with
        | zero =>
            cases (by simpa [checkTx, spend, hinputs] using h)
        | succ g2 =>
            cases g2 with
            | zero =>
                cases (by simpa [checkTx, spend, hinputs, houtputs] using h)
            | succ g3 =>
                cases (by simpa [checkTx, spend, hinputs, houtputs, huniq] using h)

private theorem checkTx_ok_implies_outputs_unique
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} :
    checkTx cfg l tx gas = .ok () -> outputsUnique tx = true := by
  intro h
  have hinputs : Not (tx.inputs = []) :=
    checkTx_ok_implies_inputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputs : Not (tx.outputs = []) :=
    checkTx_ok_implies_outputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hinputsUnique : inputsUnique tx = true :=
    checkTx_ok_implies_inputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  by_cases huniq : outputsUnique tx = true
  case pos =>
    exact huniq
  case neg =>
    cases gas with
    | zero =>
        cases (by simpa [checkTx, spend] using h)
    | succ g1 =>
        cases g1 with
        | zero =>
            cases (by simpa [checkTx, spend, hinputs] using h)
        | succ g2 =>
            cases g2 with
            | zero =>
                cases (by simpa [checkTx, spend, hinputs, houtputs] using h)
            | succ g3 =>
                cases g3 with
                | zero =>
                    cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique] using h)
                | succ g4 =>
                    cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, huniq] using h)

private theorem checkTx_ok_implies_inputs_disjoint_outputs
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} :
    checkTx cfg l tx gas = .ok () -> inputsDisjointOutputs tx = true := by
  intro h
  have hinputs : Not (tx.inputs = []) :=
    checkTx_ok_implies_inputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputs : Not (tx.outputs = []) :=
    checkTx_ok_implies_outputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hinputsUnique : inputsUnique tx = true :=
    checkTx_ok_implies_inputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputsUnique : outputsUnique tx = true :=
    checkTx_ok_implies_outputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  by_cases hdis : inputsDisjointOutputs tx = true
  case pos =>
    exact hdis
  case neg =>
    cases gas with
    | zero =>
        cases (by simpa [checkTx, spend] using h)
    | succ g1 =>
        cases g1 with
        | zero =>
            cases (by simpa [checkTx, spend, hinputs] using h)
        | succ g2 =>
            cases g2 with
            | zero =>
                cases (by simpa [checkTx, spend, hinputs, houtputs] using h)
            | succ g3 =>
                cases g3 with
                | zero =>
                    cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique] using h)
                | succ g4 =>
                    cases g4 with
                    | zero =>
                        cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique] using h)
                    | succ g5 =>
                        cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis] using h)

theorem checkTx_ok_implies_missing_input_none
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} :
    checkTx cfg l tx gas = .ok () -> firstMissingInput l tx = none := by
  intro h
  have hinputs : Not (tx.inputs = []) :=
    checkTx_ok_implies_inputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputs : Not (tx.outputs = []) :=
    checkTx_ok_implies_outputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hinputsUnique : inputsUnique tx = true :=
    checkTx_ok_implies_inputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputsUnique : outputsUnique tx = true :=
    checkTx_ok_implies_outputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hdis : inputsDisjointOutputs tx = true :=
    checkTx_ok_implies_inputs_disjoint_outputs (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  cases hfm : firstMissingInput l tx with
  | none =>
      exact rfl
  | some id =>
      cases gas with
      | zero =>
          cases (by simpa [checkTx, spend] using h)
      | succ g1 =>
          cases g1 with
          | zero =>
              cases (by simpa [checkTx, spend, hinputs] using h)
          | succ g2 =>
              cases g2 with
              | zero =>
                  cases (by simpa [checkTx, spend, hinputs, houtputs] using h)
              | succ g3 =>
                  cases g3 with
                  | zero =>
                      cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique] using h)
                  | succ g4 =>
                      cases g4 with
                      | zero =>
                          cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique] using h)
                      | succ g5 =>
                          cases g5 with
                          | zero =>
                              cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis] using h)
                          | succ g6 =>
                              cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis, hfm] using h)

private theorem checkTx_ok_implies_consumed_input_none
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} :
    checkTx cfg l tx gas = .ok () -> firstConsumedInput l tx = none := by
  intro h
  have hinputs : Not (tx.inputs = []) :=
    checkTx_ok_implies_inputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputs : Not (tx.outputs = []) :=
    checkTx_ok_implies_outputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hinputsUnique : inputsUnique tx = true :=
    checkTx_ok_implies_inputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputsUnique : outputsUnique tx = true :=
    checkTx_ok_implies_outputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hdis : inputsDisjointOutputs tx = true :=
    checkTx_ok_implies_inputs_disjoint_outputs (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hmissing : firstMissingInput l tx = none :=
    checkTx_ok_implies_missing_input_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  cases hfm : firstConsumedInput l tx with
  | none =>
      exact rfl
  | some id =>
      cases gas with
      | zero =>
          cases (by simpa [checkTx, spend] using h)
      | succ g1 =>
          cases g1 with
          | zero =>
              cases (by simpa [checkTx, spend, hinputs] using h)
          | succ g2 =>
              cases g2 with
              | zero =>
                  cases (by simpa [checkTx, spend, hinputs, houtputs] using h)
              | succ g3 =>
                  cases g3 with
                  | zero =>
                      cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique] using h)
                  | succ g4 =>
                      cases g4 with
                      | zero =>
                          cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique] using h)
                      | succ g5 =>
                          cases g5 with
                          | zero =>
                              cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis] using h)
                          | succ g6 =>
                              cases g6 with
                              | zero =>
                                  cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis, hmissing] using h)
                              | succ g7 =>
                                  cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis, hmissing, hfm] using h)

theorem checkTx_ok_implies_output_collision_none
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} :
    checkTx cfg l tx gas = .ok () -> firstOutputCollision l tx = none := by
  intro h
  have hinputs : Not (tx.inputs = []) :=
    checkTx_ok_implies_inputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputs : Not (tx.outputs = []) :=
    checkTx_ok_implies_outputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hinputsUnique : inputsUnique tx = true :=
    checkTx_ok_implies_inputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputsUnique : outputsUnique tx = true :=
    checkTx_ok_implies_outputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hdis : inputsDisjointOutputs tx = true :=
    checkTx_ok_implies_inputs_disjoint_outputs (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hmissing : firstMissingInput l tx = none :=
    checkTx_ok_implies_missing_input_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hconsumed : firstConsumedInput l tx = none :=
    checkTx_ok_implies_consumed_input_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  cases hfm : firstOutputCollision l tx with
  | none =>
      exact rfl
  | some id =>
      cases gas with
      | zero =>
          cases (by simpa [checkTx, spend] using h)
      | succ g1 =>
          cases g1 with
          | zero =>
              cases (by simpa [checkTx, spend, hinputs] using h)
          | succ g2 =>
              cases g2 with
              | zero =>
                  cases (by simpa [checkTx, spend, hinputs, houtputs] using h)
              | succ g3 =>
                  cases g3 with
                  | zero =>
                      cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique] using h)
                  | succ g4 =>
                      cases g4 with
                      | zero =>
                          cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique] using h)
                      | succ g5 =>
                          cases g5 with
                          | zero =>
                              cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis] using h)
                          | succ g6 =>
                              cases g6 with
                              | zero =>
                                  cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis, hmissing] using h)
                              | succ g7 =>
                                  cases g7 with
                                  | zero =>
                                      cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis, hmissing, hconsumed] using h)
                                  | succ g8 =>
                                      cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis, hmissing, hconsumed, hfm] using h)

private theorem checkTx_ok_implies_validSignature
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} :
    checkTx cfg l tx gas = .ok () -> validSignature cfg tx = true := by
  intro h
  have hinputs : Not (tx.inputs = []) :=
    checkTx_ok_implies_inputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputs : Not (tx.outputs = []) :=
    checkTx_ok_implies_outputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hinputsUnique : inputsUnique tx = true :=
    checkTx_ok_implies_inputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputsUnique : outputsUnique tx = true :=
    checkTx_ok_implies_outputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hdis : inputsDisjointOutputs tx = true :=
    checkTx_ok_implies_inputs_disjoint_outputs (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hmissing : firstMissingInput l tx = none :=
    checkTx_ok_implies_missing_input_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hconsumed : firstConsumedInput l tx = none :=
    checkTx_ok_implies_consumed_input_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hcollision : firstOutputCollision l tx = none :=
    checkTx_ok_implies_output_collision_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  by_cases hsig : validSignature cfg tx = true
  case pos =>
    exact hsig
  case neg =>
    cases gas with
    | zero =>
        cases (by simpa [checkTx, spend] using h)
    | succ g1 =>
        cases g1 with
        | zero =>
            cases (by simpa [checkTx, spend, hinputs] using h)
        | succ g2 =>
            cases g2 with
            | zero =>
                cases (by simpa [checkTx, spend, hinputs, houtputs] using h)
            | succ g3 =>
                cases g3 with
                | zero =>
                    cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique] using h)
                | succ g4 =>
                    cases g4 with
                    | zero =>
                        cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique] using h)
                    | succ g5 =>
                        cases g5 with
                        | zero =>
                            cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis] using h)
                        | succ g6 =>
                            cases g6 with
                            | zero =>
                                cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis, hmissing] using h)
                            | succ g7 =>
                                cases g7 with
                                | zero =>
                                    cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis, hmissing, hconsumed] using h)
                                | succ g8 =>
                                    cases g8 with
                                    | zero =>
                                        cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis, hmissing, hconsumed, hcollision] using h)
                                    | succ g9 =>
                                        cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis, hmissing, hconsumed, hcollision, hsig] using h)

theorem checkTx_ok_implies_balancePreserved
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} :
    checkTx cfg l tx gas = .ok () -> balancePreserved cfg tx = true := by
  intro h
  have hinputs : Not (tx.inputs = []) :=
    checkTx_ok_implies_inputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputs : Not (tx.outputs = []) :=
    checkTx_ok_implies_outputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hinputsUnique : inputsUnique tx = true :=
    checkTx_ok_implies_inputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputsUnique : outputsUnique tx = true :=
    checkTx_ok_implies_outputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hdis : inputsDisjointOutputs tx = true :=
    checkTx_ok_implies_inputs_disjoint_outputs (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hmissing : firstMissingInput l tx = none :=
    checkTx_ok_implies_missing_input_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hconsumed : firstConsumedInput l tx = none :=
    checkTx_ok_implies_consumed_input_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hcollision : firstOutputCollision l tx = none :=
    checkTx_ok_implies_output_collision_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hsig : validSignature cfg tx = true :=
    checkTx_ok_implies_validSignature (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  by_cases hbal : balancePreserved cfg tx = true
  case pos =>
    exact hbal
  case neg =>
    cases gas with
    | zero =>
        cases (by simpa [checkTx, spend] using h)
    | succ g1 =>
        cases g1 with
        | zero =>
            cases (by simpa [checkTx, spend, hinputs] using h)
        | succ g2 =>
            cases g2 with
            | zero =>
                cases (by simpa [checkTx, spend, hinputs, houtputs] using h)
            | succ g3 =>
                cases g3 with
                | zero =>
                    cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique] using h)
                | succ g4 =>
                    cases g4 with
                    | zero =>
                        cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique] using h)
                    | succ g5 =>
                        cases g5 with
                        | zero =>
                            cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis] using h)
                        | succ g6 =>
                            cases g6 with
                            | zero =>
                                cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis, hmissing] using h)
                            | succ g7 =>
                                cases g7 with
                                | zero =>
                                    cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis, hmissing, hconsumed] using h)
                                | succ g8 =>
                                    cases g8 with
                                    | zero =>
                                        cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis, hmissing, hconsumed, hcollision] using h)
                                    | succ g9 =>
                                        cases g9 with
                                        | zero =>
                                            cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis, hmissing, hconsumed, hcollision, hsig] using h)
                                        | succ g10 =>
                                            cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique, hdis, hmissing, hconsumed, hcollision, hsig, hbal] using h)

private def succ10 (g : Gas) : Gas :=
  Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ g)))))))))

private def gasAtLeast10 (gas : Gas) : Prop :=
  ∃ g, gas = succ10 g

private theorem succ10_succ (g : Gas) : succ10 (Nat.succ g) = Nat.succ (succ10 g) := by
  rfl

private theorem ten_le_succ10 (g : Gas) : 10 ≤ succ10 g := by
  induction g with
  | zero =>
      exact Nat.le.refl
  | succ g ih =>
      rw [succ10_succ]
      exact Nat.le.step ih

private theorem gasAtLeast10_iff_ge10 (gas : Gas) : gasAtLeast10 gas ↔ 10 ≤ gas := by
  constructor
  · intro h
    rcases h with ⟨g, rfl⟩
    exact ten_le_succ10 g
  · intro h
    induction h with
    | refl =>
        exact ⟨0, rfl⟩
    | step h ih =>
        rcases ih with ⟨g, hg⟩
        exact ⟨Nat.succ g, by simp [hg, succ10_succ]⟩

private def checkTxPhaseAProp (_cfg : Config) (l : Ledger) (tx : Tx) : Prop :=
  Not (tx.inputs = []) ∧
  Not (tx.outputs = []) ∧
  inputsUnique tx = true ∧
  outputsUnique tx = true ∧
  inputsDisjointOutputs tx = true ∧
  firstMissingInput l tx = none ∧
  firstConsumedInput l tx = none ∧
  firstOutputCollision l tx = none ∧
  validSignature _cfg tx = true ∧
  balancePreserved _cfg tx = true

private theorem checkTx_ok_implies_phaseAProp
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} :
    checkTx cfg l tx gas = .ok () -> checkTxPhaseAProp cfg l tx := by
  intro h
  have hinputs : Not (tx.inputs = []) :=
    checkTx_ok_implies_inputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputs : Not (tx.outputs = []) :=
    checkTx_ok_implies_outputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hinputsUnique : inputsUnique tx = true :=
    checkTx_ok_implies_inputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputsUnique : outputsUnique tx = true :=
    checkTx_ok_implies_outputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hdis : inputsDisjointOutputs tx = true :=
    checkTx_ok_implies_inputs_disjoint_outputs (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hmissing : firstMissingInput l tx = none :=
    checkTx_ok_implies_missing_input_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hconsumed : firstConsumedInput l tx = none :=
    checkTx_ok_implies_consumed_input_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hcollision : firstOutputCollision l tx = none :=
    checkTx_ok_implies_output_collision_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hsig : validSignature cfg tx = true :=
    checkTx_ok_implies_validSignature (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hbal : balancePreserved cfg tx = true :=
    checkTx_ok_implies_balancePreserved (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  exact
    And.intro hinputs
      (And.intro houtputs
        (And.intro hinputsUnique
          (And.intro houtputsUnique
            (And.intro hdis
              (And.intro hmissing
                (And.intro hconsumed
                  (And.intro hcollision
                    (And.intro hsig hbal))))))))

private theorem checkTx_ok_implies_gasAtLeast10
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} :
    checkTx cfg l tx gas = .ok () -> gasAtLeast10 gas := by
  intro h
  have hinputs : Not (tx.inputs = []) :=
    checkTx_ok_implies_inputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputs : Not (tx.outputs = []) :=
    checkTx_ok_implies_outputs_nonempty (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hinputsUnique : inputsUnique tx = true :=
    checkTx_ok_implies_inputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have houtputsUnique : outputsUnique tx = true :=
    checkTx_ok_implies_outputs_unique (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hdis : inputsDisjointOutputs tx = true :=
    checkTx_ok_implies_inputs_disjoint_outputs (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hmissing : firstMissingInput l tx = none :=
    checkTx_ok_implies_missing_input_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hconsumed : firstConsumedInput l tx = none :=
    checkTx_ok_implies_consumed_input_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hcollision : firstOutputCollision l tx = none :=
    checkTx_ok_implies_output_collision_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hsig : validSignature cfg tx = true :=
    checkTx_ok_implies_validSignature (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  have hbal : balancePreserved cfg tx = true :=
    checkTx_ok_implies_balancePreserved (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
  cases gas with
  | zero =>
      cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique,
        hdis, hmissing, hconsumed, hcollision, hsig, hbal] using h)
  | succ g1 =>
      cases g1 with
      | zero =>
          cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique,
            hdis, hmissing, hconsumed, hcollision, hsig, hbal] using h)
      | succ g2 =>
          cases g2 with
          | zero =>
              cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique,
                hdis, hmissing, hconsumed, hcollision, hsig, hbal] using h)
          | succ g3 =>
              cases g3 with
              | zero =>
                  cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique,
                    hdis, hmissing, hconsumed, hcollision, hsig, hbal] using h)
              | succ g4 =>
                  cases g4 with
                  | zero =>
                      cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique,
                        hdis, hmissing, hconsumed, hcollision, hsig, hbal] using h)
                  | succ g5 =>
                      cases g5 with
                      | zero =>
                          cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique,
                            hdis, hmissing, hconsumed, hcollision, hsig, hbal] using h)
                      | succ g6 =>
                          cases g6 with
                          | zero =>
                              cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique,
                                hdis, hmissing, hconsumed, hcollision, hsig, hbal] using h)
                          | succ g7 =>
                              cases g7 with
                              | zero =>
                                  cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique,
                                    hdis, hmissing, hconsumed, hcollision, hsig, hbal] using h)
                              | succ g8 =>
                                  cases g8 with
                                  | zero =>
                                      cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique,
                                        hdis, hmissing, hconsumed, hcollision, hsig, hbal] using h)
                                  | succ g9 =>
                                      cases g9 with
                                      | zero =>
                                          cases (by simpa [checkTx, spend, hinputs, houtputs, hinputsUnique, houtputsUnique,
                                            hdis, hmissing, hconsumed, hcollision, hsig, hbal] using h)
                                      | succ g10 =>
                                          exact ⟨g10, rfl⟩

private theorem checkTx_ok_iff_phaseAProp_succ10
    {cfg : Config} {l : Ledger} {tx : Tx} {g : Gas} :
    checkTx cfg l tx (succ10 g) = .ok () ↔ checkTxPhaseAProp cfg l tx := by
  constructor
  · intro h
    exact checkTx_ok_implies_phaseAProp (cfg := cfg) (l := l) (tx := tx) (gas := succ10 g) h
  · intro hprop
    rcases hprop with
      ⟨hinputs, houtputs, hinputsUnique, houtputsUnique, hdis,
        hmissing, hconsumed, hcollision, hsig, hbal⟩
    simp [checkTx, spend, succ10, hinputs, houtputs, hinputsUnique, houtputsUnique,
      hdis, hmissing, hconsumed, hcollision, hsig, hbal,
      bind_ok, map_ok]

private theorem checkTx_ok_iff_phaseAProp
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} :
    checkTx cfg l tx gas = .ok () ↔ gasAtLeast10 gas ∧ checkTxPhaseAProp cfg l tx := by
  constructor
  · intro h
    have hgas : gasAtLeast10 gas :=
      checkTx_ok_implies_gasAtLeast10 (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
    have hprop : checkTxPhaseAProp cfg l tx :=
      checkTx_ok_implies_phaseAProp (cfg := cfg) (l := l) (tx := tx) (gas := gas) h
    exact And.intro hgas hprop
  · intro h
    rcases h with ⟨⟨g, hgas⟩, hprop⟩
    subst hgas
    exact (checkTx_ok_iff_phaseAProp_succ10 (cfg := cfg) (l := l) (tx := tx) (g := g)).2 hprop

private theorem checkTx_ok_iff_phaseAProp_ge10
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} :
    checkTx cfg l tx gas = .ok () ↔ 10 ≤ gas ∧ checkTxPhaseAProp cfg l tx := by
  constructor
  · intro h
    have h' := (checkTx_ok_iff_phaseAProp (cfg := cfg) (l := l) (tx := tx) (gas := gas)).1 h
    rcases h' with ⟨hgas, hprop⟩
    have hge : 10 ≤ gas := (gasAtLeast10_iff_ge10 gas).1 hgas
    exact And.intro hge hprop
  · intro h
    rcases h with ⟨hge, hprop⟩
    have hgas : gasAtLeast10 gas := (gasAtLeast10_iff_ge10 gas).2 hge
    exact (checkTx_ok_iff_phaseAProp (cfg := cfg) (l := l) (tx := tx) (gas := gas)).2
      (And.intro hgas hprop)

end Starstream.Oracle
