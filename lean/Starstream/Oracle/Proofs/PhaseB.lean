import Starstream.Oracle.Idealized
import Starstream.Oracle.Proofs.PhaseA

set_option autoImplicit false

namespace Starstream.Oracle

private theorem mem_foldl_insert_list
    {xs : List UtxoId} {a : Std.HashSet UtxoId} {x : UtxoId} :
    x ∈ List.foldl (fun s y => s.insert y) a xs ↔ x ∈ a ∨ x ∈ xs := by
  induction xs generalizing a with
  | nil =>
      simp
  | cons y ys ih =>
      constructor
      · intro h
        have h' : x ∈ a.insert y ∨ x ∈ ys :=
          (ih (a := a.insert y)).1 h
        cases h' with
        | inl hmem =>
            have hmem' := (Std.HashSet.mem_insert (m := a) (k := y) (a := x)).1 hmem
            cases hmem' with
            | inl hbeq =>
                have hxy : x = y := by
                  have : y = x := (beq_iff_eq).1 hbeq
                  exact this.symm
                exact Or.inr (by simp [hxy])
            | inr hxA =>
                exact Or.inl hxA
        | inr hys =>
            exact Or.inr (by simp [hys])
      · intro h
        have h' : x ∈ a.insert y ∨ x ∈ ys := by
          cases h with
          | inl hxA =>
              have hxA' : x ∈ a.insert y :=
                (Std.HashSet.mem_insert (m := a) (k := y) (a := x)).2 (Or.inr hxA)
              exact Or.inl hxA'
          | inr hxyys =>
              have hxyys' : x = y ∨ x ∈ ys := by
                have h' := hxyys
                simp at h'
                exact h'
              cases hxyys' with
              | inl hxy =>
                  have hyx : y == x := (beq_iff_eq).2 hxy.symm
                  have hxA' : x ∈ a.insert y :=
                    (Std.HashSet.mem_insert (m := a) (k := y) (a := x)).2 (Or.inl hyx)
                  exact Or.inl hxA'
              | inr hys =>
                  exact Or.inr hys
        exact (ih (a := a.insert y)).2 h'

private theorem mem_setOfList {xs : List UtxoId} {x : UtxoId} :
    x ∈ setOfList xs ↔ x ∈ xs := by
  simp [setOfList, mem_foldl_insert_list]

private theorem mem_UtxoIds {us : List Utxo} {x : UtxoId} :
    x ∈ UtxoIds us ↔ x ∈ us.map Utxo.id := by
  simp [UtxoIds, mem_setOfList]

private theorem mem_UtxoIds_append {us vs : List Utxo} {x : UtxoId} :
    x ∈ UtxoIds (us ++ vs) ↔ x ∈ UtxoIds us ∨ x ∈ UtxoIds vs := by
  constructor
  · intro h
    have h' : x ∈ (us ++ vs).map Utxo.id := (mem_UtxoIds).1 h
    have h'' : x ∈ us.map Utxo.id ∨ x ∈ vs.map Utxo.id := by
      have hmap := h'
      rw [List.map_append] at hmap
      exact (List.mem_append.1 hmap)
    cases h'' with
    | inl hu => exact Or.inl ((mem_UtxoIds).2 hu)
    | inr hv => exact Or.inr ((mem_UtxoIds).2 hv)
  · intro h
    cases h with
    | inl hu =>
        have hu' : x ∈ us.map Utxo.id := (mem_UtxoIds).1 hu
        have h' : x ∈ (us ++ vs).map Utxo.id := by
          have hmap : x ∈ us.map Utxo.id ++ vs.map Utxo.id :=
            (List.mem_append.2 (Or.inl hu'))
          rw [← List.map_append] at hmap
          exact hmap
        exact (mem_UtxoIds).2 h'
    | inr hv =>
        have hv' : x ∈ vs.map Utxo.id := (mem_UtxoIds).1 hv
        have h' : x ∈ (us ++ vs).map Utxo.id := by
          have hmap : x ∈ us.map Utxo.id ++ vs.map Utxo.id :=
            (List.mem_append.2 (Or.inr hv'))
          rw [← List.map_append] at hmap
          exact hmap
        exact (mem_UtxoIds).2 h'

private theorem mem_InputIds {tx : Tx} {x : UtxoId} :
    x ∈ InputIds tx ↔ x ∈ tx.inputs.map Utxo.id := by
  simp [InputIds, UtxoIds, mem_setOfList]

private theorem mem_OutputIds {tx : Tx} {x : UtxoId} :
    x ∈ OutputIds tx ↔ x ∈ tx.outputs.map Utxo.id := by
  simp [OutputIds, UtxoIds, mem_setOfList]

private theorem find?_eq_none_iff {α : Type} {xs : List α} {p : α -> Bool} :
    xs.find? p = none ↔ ∀ x, x ∈ xs -> p x = false := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      constructor
      · intro h
        cases hx : p x with
        | true =>
            have : False := by
              have h0 := h
              simp only [List.find?, hx] at h0
              cases h0
            intro y hy
            exact (False.elim this)
        | false =>
            have h' : xs.find? p = none := by
              have h0 := h
              simp only [List.find?, hx] at h0
              exact h0
            have ih' := (ih).1 h'
            intro y hy
            have hy' : y = x ∨ y ∈ xs := by
              have h0 := hy
              simp at h0
              exact h0
            cases hy' with
            | inl hxy =>
                subst hxy
                simp [hx]
            | inr hyxs =>
                exact ih' y hyxs
      · intro h
        cases hx : p x with
        | true =>
            have hpx : p x = false := h x (by simp)
            have : False := by
              have h0 := hpx
              rw [hx] at h0
              cases h0
            exact (False.elim this)
        | false =>
            have h' : xs.find? p = none := by
              apply (ih).2
              intro y hy
              exact h y (by simp [hy])
            simp only [List.find?, hx]
            exact h'

private theorem decide_eq_bool {b : Bool} : decide (b = true) = b := by
  cases b <;> rfl

private theorem mem_removeInputs_orig
    {us : List Utxo} {ids : Std.HashSet UtxoId} {u : Utxo} :
    u ∈ removeInputs us ids -> u ∈ us := by
  intro h
  have h' : u ∈ us ∧ (!decide (ids.contains u.id = true)) = true := by
    have h0 := h
    rw [removeInputs] at h0
    rcases (List.mem_filter.1 h0) with ⟨hu, hnot⟩
    refine And.intro hu ?_
    rw [decide_eq_bool]
    exact hnot
  exact h'.1

private theorem mem_removeInputs_not_in_inputs
    {us : List Utxo} {ids : Std.HashSet UtxoId} {u : Utxo} :
    u ∈ removeInputs us ids -> ids.contains u.id = false := by
  intro h
  have h' : u ∈ us ∧ (!decide (ids.contains u.id = true)) = true := by
    have h0 := h
    rw [removeInputs] at h0
    rcases (List.mem_filter.1 h0) with ⟨hu, hnot⟩
    refine And.intro hu ?_
    rw [decide_eq_bool]
    exact hnot
  have h0 := h'.2
  cases hcontains : ids.contains u.id with
  | true =>
      have : False := by
        have h1 := h0
        rw [decide_eq_bool] at h1
        rw [hcontains] at h1
        cases h1
      exact (False.elim this)
  | false =>
      rfl

private theorem mem_UtxoIds_removeInputs_in_live
    {us : List Utxo} {ids : Std.HashSet UtxoId} {x : UtxoId} :
    x ∈ UtxoIds (removeInputs us ids) -> x ∈ UtxoIds us := by
  intro h
  have h' : x ∈ (removeInputs us ids).map Utxo.id :=
    (mem_UtxoIds).1 h
  rcases (List.mem_map.1 h') with ⟨u, hu, rfl⟩
  have hu' : u ∈ us := mem_removeInputs_orig (us := us) (ids := ids) (u := u) hu
  exact (mem_UtxoIds).2 (by
    exact List.mem_map.2 ⟨u, hu', rfl⟩)

private theorem mem_UtxoIds_removeInputs_not_in_inputs
    {us : List Utxo} {ids : Std.HashSet UtxoId} {x : UtxoId} :
    x ∈ UtxoIds (removeInputs us ids) -> ids.contains x = false := by
  intro h
  have h' : x ∈ (removeInputs us ids).map Utxo.id :=
    (mem_UtxoIds).1 h
  rcases (List.mem_map.1 h') with ⟨u, hu, rfl⟩
  exact mem_removeInputs_not_in_inputs (us := us) (ids := ids) (u := u) hu

private theorem foldl_and_eq_true_iff
    {α : Type} {xs : List α} {p : α -> Bool} {acc : Bool} :
    List.foldl (fun a x => a && p x) acc xs = true ↔
      acc = true ∧ ∀ x, x ∈ xs -> p x = true := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      constructor
      · intro h
        have h' := (ih (acc := acc && p x)).1 h
        rcases h' with ⟨haccpx, hall⟩
        have haccpx' : acc = true ∧ p x = true :=
          (Bool.and_eq_true_iff).1 haccpx
        refine And.intro haccpx'.1 ?_
        intro y hy
        have hy' : y = x ∨ y ∈ xs := by
          have h0 := hy
          simp at h0
          exact h0
        cases hy' with
        | inl hxy =>
            subst hxy
            exact haccpx'.2
        | inr hyxs =>
            exact hall y hyxs
      · intro h
        rcases h with ⟨hacc, hall⟩
        have hpx : p x = true := hall x (by simp)
        have hall' : ∀ y, y ∈ xs -> p y = true := by
          intro y hy
          exact hall y (by simp [hy])
        refine (ih (acc := acc && p x)).2 ?_
        constructor
        · cases hacc
          simp [hpx]
        · exact hall'

private theorem setDisjoint_mem_false
    {a b : Std.HashSet UtxoId} {x : UtxoId} :
    setDisjoint a b = true -> x ∈ a -> b.contains x = false := by
  intro hdis hmem
  have hfold : List.foldl (fun ok x => ok && Bool.not (b.contains x)) true a.toList = true := by
    have h0 := hdis
    simp [setDisjoint, Std.HashSet.fold_eq_foldl_toList] at h0
    exact h0
  have hforall' :
      ∀ y, y ∈ a.toList -> Bool.not (b.contains y) = true := by
    have h' :=
      (foldl_and_eq_true_iff (xs := a.toList) (p := fun y => Bool.not (b.contains y)) (acc := true)).1 hfold
    exact h'.2
  have hmemList : x ∈ a.toList := (Std.HashSet.mem_toList).2 hmem
  have hnot : Bool.not (b.contains x) = true := hforall' x hmemList
  cases hb : b.contains x with
  | true =>
      have : False := by
        have h0 := hnot
        rw [hb] at h0
        cases h0
      exact (False.elim this)
  | false =>
      rfl

private theorem setDisjoint_of_forall
    {a b : Std.HashSet UtxoId} :
    (∀ x, x ∈ a -> b.contains x = false) -> setDisjoint a b = true := by
  intro h
  have hlist :
      ∀ x, x ∈ a.toList -> Bool.not (b.contains x) = true := by
    intro x hx
    have hx' : x ∈ a := (Std.HashSet.mem_toList).1 hx
    have hnot : b.contains x = false := h x hx'
    cases hb : b.contains x with
    | true =>
        have : False := by
          have h0 := hnot
          rw [hb] at h0
          cases h0
        exact (False.elim this)
    | false =>
        rfl
  have hfold :
      List.foldl (fun ok x => ok && Bool.not (b.contains x)) true a.toList = true := by
    have h' :=
      (foldl_and_eq_true_iff (xs := a.toList) (p := fun y => Bool.not (b.contains y)) (acc := true)).2
        (And.intro rfl hlist)
    exact h'
  simp [setDisjoint, Std.HashSet.fold_eq_foldl_toList]
  exact hfold

private theorem mem_setUnion_iff
    {a b : Std.HashSet UtxoId} {x : UtxoId} :
    x ∈ setUnion a b ↔ x ∈ a ∨ x ∈ b := by
  have hfold :
      x ∈ List.foldl (fun s y => s.insert y) a b.toList ↔
        x ∈ a ∨ x ∈ b.toList := by
    exact mem_foldl_insert_list (xs := b.toList) (a := a) (x := x)
  have hfold' :
      x ∈ setUnion a b ↔ x ∈ a ∨ x ∈ b.toList := by
    simp only [setUnion, Std.HashSet.fold_eq_foldl_toList]
    exact hfold
  exact hfold'.trans (by
    constructor
    · intro h
      cases h with
      | inl hleft => exact Or.inl hleft
      | inr hright => exact Or.inr ((Std.HashSet.mem_toList (m := b) (k := x)).1 hright)
    · intro h
      cases h with
      | inl hleft => exact Or.inl hleft
      | inr hright => exact Or.inr ((Std.HashSet.mem_toList (m := b) (k := x)).2 hright))

private theorem contains_setUnion_false_left
    {a b : Std.HashSet UtxoId} {x : UtxoId} :
    (setUnion a b).contains x = false -> a.contains x = false := by
  intro h
  cases ha : a.contains x with
  | true =>
      have hmemA : x ∈ a := (Std.HashSet.mem_iff_contains).2 ha
      have hmemUnion : x ∈ setUnion a b :=
        (mem_setUnion_iff (a := a) (b := b) (x := x)).2 (Or.inl hmemA)
      have hUnion : (setUnion a b).contains x = true :=
        (Std.HashSet.mem_iff_contains).1 hmemUnion
      have : False := by
        have h0 := h
        rw [hUnion] at h0
        cases h0
      exact (False.elim this)
  | false =>
      rfl

private theorem contains_setUnion_false_right
    {a b : Std.HashSet UtxoId} {x : UtxoId} :
    (setUnion a b).contains x = false -> b.contains x = false := by
  intro h
  cases hb : b.contains x with
  | true =>
      have hmemB : x ∈ b := (Std.HashSet.mem_iff_contains).2 hb
      have hmemUnion : x ∈ setUnion a b :=
        (mem_setUnion_iff (a := a) (b := b) (x := x)).2 (Or.inr hmemB)
      have hUnion : (setUnion a b).contains x = true :=
        (Std.HashSet.mem_iff_contains).1 hmemUnion
      have : False := by
        have h0 := h
        rw [hUnion] at h0
        cases h0
      exact (False.elim this)
  | false =>
      rfl

private theorem contains_setUnion_false
    {a b : Std.HashSet UtxoId} {x : UtxoId} :
    a.contains x = false -> b.contains x = false ->
      (setUnion a b).contains x = false := by
  intro ha hb
  cases hmem : (setUnion a b).contains x with
  | true =>
      have hmem' : x ∈ setUnion a b := (Std.HashSet.mem_iff_contains).2 hmem
      have hmem'' := (mem_setUnion_iff (a := a) (b := b) (x := x)).1 hmem'
      cases hmem'' with
      | inl ha' =>
          have : a.contains x = true := (Std.HashSet.mem_iff_contains).1 ha'
          have : False := by
            have h0 := this
            rw [ha] at h0
            cases h0
          exact (False.elim this)
      | inr hb' =>
          have : b.contains x = true := (Std.HashSet.mem_iff_contains).1 hb'
          have : False := by
            have h0 := this
            rw [hb] at h0
            cases h0
          exact (False.elim this)
  | false =>
      rfl

private theorem firstMissingInput_none_inputs_live
    {l : Ledger} {tx : Tx} :
    firstMissingInput l tx = none ->
    ∀ x, x ∈ InputIds tx -> (UtxoIds l.utxos).contains x = true := by
  intro hnone x hx
  have hfind : tx.inputs.find? (fun u => Bool.not ((UtxoIds l.utxos).contains u.id)) = none := by
    cases hcase : tx.inputs.find? (fun u => Bool.not ((UtxoIds l.utxos).contains u.id)) with
    | none =>
        rfl
    | some u =>
        have : False := by
          have h0 := hnone
          simp only [firstMissingInput, hcase] at h0
          cases h0
        exact (False.elim this)
  have hall :
      ∀ u, u ∈ tx.inputs -> Bool.not ((UtxoIds l.utxos).contains u.id) = false := by
    exact (find?_eq_none_iff (xs := tx.inputs)
      (p := fun u => Bool.not ((UtxoIds l.utxos).contains u.id))).1 hfind
  have hx' : x ∈ tx.inputs.map Utxo.id := (mem_InputIds).1 hx
  rcases (List.mem_map.1 hx') with ⟨u, hu, rfl⟩
  have hnot : Bool.not ((UtxoIds l.utxos).contains u.id) = false := hall u hu
  cases hcontains : (UtxoIds l.utxos).contains u.id with
  | true =>
      rfl
  | false =>
      have : False := by
        have h0 := hnot
        rw [hcontains] at h0
        cases h0
      exact (False.elim this)

private theorem firstOutputCollision_none_outputs_fresh
    {l : Ledger} {tx : Tx} :
    firstOutputCollision l tx = none ->
    ∀ x, x ∈ OutputIds tx ->
      (setUnion (UtxoIds l.utxos) l.consumed).contains x = false := by
  intro hnone x hx
  have hfind : tx.outputs.find? (fun u =>
      (setUnion (UtxoIds l.utxos) l.consumed).contains u.id) = none := by
    cases hcase : tx.outputs.find? (fun u =>
        (setUnion (UtxoIds l.utxos) l.consumed).contains u.id) with
    | none =>
        rfl
    | some u =>
        have : False := by
          have h0 := hnone
          simp only [firstOutputCollision, hcase] at h0
          cases h0
        exact (False.elim this)
  have hall :
      ∀ u, u ∈ tx.outputs ->
        (setUnion (UtxoIds l.utxos) l.consumed).contains u.id = false := by
    exact (find?_eq_none_iff (xs := tx.outputs)
      (p := fun u => (setUnion (UtxoIds l.utxos) l.consumed).contains u.id)).1 hfind
  have hx' : x ∈ tx.outputs.map Utxo.id := (mem_OutputIds).1 hx
  rcases (List.mem_map.1 hx') with ⟨u, hu, rfl⟩
  exact hall u hu

private theorem applyTx_ok_implies_checkTx_ok
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} {l' : Ledger} :
    applyTx cfg l tx gas = .ok l' -> checkTx cfg l tx gas = .ok () := by
  intro h
  cases hcheck : checkTx cfg l tx gas with
  | error err =>
      cases (by
        have h0 := h
        simp [applyTx, hcheck] at h0
        exact h0)
  | ok u =>
      cases u
      simp

private theorem applyTx_ok_implies_fields
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} {l' : Ledger} :
    applyTx cfg l tx gas = .ok l' ->
      l'.utxos = removeInputs l.utxos (InputIds tx) ++ tx.outputs ∧
      l'.consumed = setUnion l.consumed (InputIds tx) ∧
      l'.txHistory = l.txHistory ++ [tx] ∧
      l'.nextUtxoId = Nat.max l.nextUtxoId (maxId tx.outputs + 1) := by
  intro h
  cases hcheck : checkTx cfg l tx gas with
  | error err =>
      cases (by
        have h0 := h
        simp [applyTx, hcheck] at h0
        exact h0)
  | ok u =>
      cases u
      simp [applyTx, hcheck] at h
      cases h
      exact And.intro rfl (And.intro rfl (And.intro rfl rfl))

private theorem applyTx_ok_implies_utxos
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} {l' : Ledger} :
    applyTx cfg l tx gas = .ok l' ->
      l'.utxos = removeInputs l.utxos (InputIds tx) ++ tx.outputs := by
  intro h
  exact (applyTx_ok_implies_fields (cfg := cfg) (l := l) (tx := tx) (gas := gas) (l' := l') h).1

private theorem applyTx_ok_implies_consumed
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} {l' : Ledger} :
    applyTx cfg l tx gas = .ok l' ->
      l'.consumed = setUnion l.consumed (InputIds tx) := by
  intro h
  exact (applyTx_ok_implies_fields (cfg := cfg) (l := l) (tx := tx) (gas := gas) (l' := l') h).2.1

private theorem applyTx_ok_implies_txHistory
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} {l' : Ledger} :
    applyTx cfg l tx gas = .ok l' ->
      l'.txHistory = l.txHistory ++ [tx] := by
  intro h
  exact (applyTx_ok_implies_fields (cfg := cfg) (l := l) (tx := tx) (gas := gas) (l' := l') h).2.2.1

private theorem applyTx_ok_implies_nextUtxoId
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} {l' : Ledger} :
    applyTx cfg l tx gas = .ok l' ->
      l'.nextUtxoId = Nat.max l.nextUtxoId (maxId tx.outputs + 1) := by
  intro h
  exact (applyTx_ok_implies_fields (cfg := cfg) (l := l) (tx := tx) (gas := gas) (l' := l') h).2.2.2

theorem applyTx_removes_inputs
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} {l' : Ledger} :
    applyTx cfg l tx gas = .ok l' ->
      l'.utxos = removeInputs l.utxos (InputIds tx) ++ tx.outputs := by
  intro h
  exact applyTx_ok_implies_utxos (cfg := cfg) (l := l) (tx := tx) (gas := gas) (l' := l') h

theorem applyTx_updates_consumed
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} {l' : Ledger} :
    applyTx cfg l tx gas = .ok l' ->
      l'.consumed = setUnion l.consumed (InputIds tx) := by
  intro h
  exact applyTx_ok_implies_consumed (cfg := cfg) (l := l) (tx := tx) (gas := gas) (l' := l') h

theorem applyTx_no_double_spend
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} {l' : Ledger} :
    applyTx cfg l tx gas = .ok l' ->
      l'.utxos = removeInputs l.utxos (InputIds tx) ++ tx.outputs ∧
      l'.consumed = setUnion l.consumed (InputIds tx) := by
  intro h
  exact And.intro
    (applyTx_removes_inputs (cfg := cfg) (l := l) (tx := tx) (gas := gas) (l' := l') h)
    (applyTx_updates_consumed (cfg := cfg) (l := l) (tx := tx) (gas := gas) (l' := l') h)

private theorem applyTx_live_consumed_disjoint
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} {l' : Ledger} :
    applyTx cfg l tx gas = .ok l' ->
      setDisjoint (UtxoIds (removeInputs l.utxos (InputIds tx) ++ tx.outputs))
        (setUnion l.consumed (InputIds tx)) = true ->
      setDisjoint (UtxoIds l'.utxos) l'.consumed = true := by
  intro h hdis
  have hfields := applyTx_ok_implies_fields (cfg := cfg) (l := l) (tx := tx) (gas := gas) (l' := l') h
  rcases hfields with ⟨hutxos, hconsumed, _hrest⟩
  simp [hutxos, hconsumed]
  exact hdis

theorem applyTx_preserves_balance
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} {l' : Ledger} :
    applyTx cfg l tx gas = .ok l' ->
    balancePreserved cfg tx = true := by
  intro h
  have hcheck : checkTx cfg l tx gas = .ok () :=
    applyTx_ok_implies_checkTx_ok (cfg := cfg) (l := l) (tx := tx) (gas := gas) (l' := l') h
  exact checkTx_ok_implies_balancePreserved (cfg := cfg) (l := l) (tx := tx) (gas := gas) hcheck

theorem applyTx_preserves_live_consumed_disjoint
    {cfg : Config} {l : Ledger} {tx : Tx} {gas : Gas} {l' : Ledger} :
    applyTx cfg l tx gas = .ok l' ->
    setDisjoint (UtxoIds l.utxos) l.consumed = true ->
    setDisjoint (UtxoIds l'.utxos) l'.consumed = true := by
  intro h hdis
  have hcheck : checkTx cfg l tx gas = .ok () :=
    applyTx_ok_implies_checkTx_ok (cfg := cfg) (l := l) (tx := tx) (gas := gas) (l' := l') h
  have hmissing : firstMissingInput l tx = none :=
    checkTx_ok_implies_missing_input_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) hcheck
  have hcollision : firstOutputCollision l tx = none :=
    checkTx_ok_implies_output_collision_none (cfg := cfg) (l := l) (tx := tx) (gas := gas) hcheck
  have hinputs_live :
      ∀ x, x ∈ InputIds tx -> (UtxoIds l.utxos).contains x = true :=
    firstMissingInput_none_inputs_live (l := l) (tx := tx) hmissing
  have houtputs_fresh :
      ∀ x, x ∈ OutputIds tx ->
        (setUnion (UtxoIds l.utxos) l.consumed).contains x = false :=
    firstOutputCollision_none_outputs_fresh (l := l) (tx := tx) hcollision
  have hdis' :
      setDisjoint (UtxoIds (removeInputs l.utxos (InputIds tx) ++ tx.outputs))
        (setUnion l.consumed (InputIds tx)) = true := by
    apply setDisjoint_of_forall
    intro x hx
    have hx' := (mem_UtxoIds_append (us := removeInputs l.utxos (InputIds tx))
      (vs := tx.outputs) (x := x)).1 hx
    cases hx' with
    | inl hxRemove =>
        have hxLive : x ∈ UtxoIds l.utxos :=
          mem_UtxoIds_removeInputs_in_live (us := l.utxos) (ids := InputIds tx) (x := x) hxRemove
        have hconsumedFalse : l.consumed.contains x = false :=
          setDisjoint_mem_false (a := UtxoIds l.utxos) (b := l.consumed) (x := x) hdis hxLive
        have hinputFalse : (InputIds tx).contains x = false :=
          mem_UtxoIds_removeInputs_not_in_inputs (us := l.utxos) (ids := InputIds tx) (x := x) hxRemove
        exact contains_setUnion_false (a := l.consumed) (b := InputIds tx) (x := x) hconsumedFalse hinputFalse
    | inr hxOut =>
        have hoccupiedFalse :
            (setUnion (UtxoIds l.utxos) l.consumed).contains x = false :=
          houtputs_fresh x (by
            exact hxOut)
        have hconsumedFalse : l.consumed.contains x = false :=
          contains_setUnion_false_right (a := UtxoIds l.utxos) (b := l.consumed) (x := x) hoccupiedFalse
        have hliveFalse : (UtxoIds l.utxos).contains x = false :=
          contains_setUnion_false_left (a := UtxoIds l.utxos) (b := l.consumed) (x := x) hoccupiedFalse
        have hinputFalse : (InputIds tx).contains x = false := by
          cases hin : (InputIds tx).contains x with
          | true =>
              have hxIn : x ∈ InputIds tx := (Std.HashSet.mem_iff_contains).2 hin
              have hliveTrue : (UtxoIds l.utxos).contains x = true :=
                hinputs_live x hxIn
              have : False := by
                have h0 := hliveTrue
                rw [hliveFalse] at h0
                cases h0
              exact (False.elim this)
          | false =>
              rfl
        exact contains_setUnion_false (a := l.consumed) (b := InputIds tx) (x := x) hconsumedFalse hinputFalse
  exact applyTx_live_consumed_disjoint (cfg := cfg) (l := l) (tx := tx) (gas := gas) (l' := l') h hdis'

end Starstream.Oracle
