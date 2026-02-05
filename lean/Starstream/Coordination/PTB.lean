import Starstream.Coordination.SBAC

namespace Starstream

/-! # PTB compilation skeleton (event-structure extraction)

Not yet in Starstream (compiles to WASM instead). Defines PTB-style
program representation and translation to event-structure Scripts.
-/

namespace PTB

structure Command where
  action    : Action
  uses      : Finset Nat          -- result indices consumed by this command
  conflicts : Finset Nat          -- explicit conflict edges (choice/guards)
  deriving DecidableEq

structure Program where
  cmds : List Command
  deriving DecidableEq

structure Config where
  roles    : Finset RoleId
  roleKind : RoleId → RoleKind

structure AccessConfig extends Config where
  utxoRole  : UTXOId → RoleId
  ifaceRole : InterfaceId → RoleId

def defaultCommand : Command :=
  { action := Action.read 0 0, uses := ∅, conflicts := ∅ }

def Program.length (p : Program) : Nat := p.cmds.length

def Program.events (p : Program) : Finset EventId :=
  Finset.range p.length

def Program.cmdAt (p : Program) (i : Nat) : Command :=
  p.cmds.getD i defaultCommand

def Program.actionAt (p : Program) (i : Nat) : Action :=
  (p.cmdAt i).action

def Program.usesAt (p : Program) (i : Nat) : Finset Nat :=
  (p.cmdAt i).uses

def Program.conflictsAt (p : Program) (i : Nat) : Finset Nat :=
  (p.cmdAt i).conflicts

end PTB

-- Define Action extensions in the Starstream namespace (outside PTB)
def Action.readUtxos : Action → Finset UTXOId
  | .read _ u     => {u}
  | .snapshot _ u => {u}
  | _             => ∅

def Action.writeUtxos : Action → Finset UTXOId
  | .consume _ u => {u}
  | .produce _ u => {u}
  | .lock _ u    => {u}
  | _            => ∅

def Action.consumedUtxos : Action → Finset UTXOId
  | .consume _ u => {u}
  | _            => ∅

def Action.utxoAccesses (a : Action) : Finset UTXOId :=
  a.readUtxos ∪ a.writeUtxos

def Action.ifaceUses : Action → Finset InterfaceId
  | .raise _ _ iface _     => {iface}
  | .resume _ _ iface _    => {iface}
  | .install _ _ h         => {h.iface}
  | .uninstall _ _ iface   => {iface}
  | _                      => ∅

def Action.ifaceInstalls : Action → Finset InterfaceId
  | .install _ _ h => {h.iface}
  | _              => ∅

def Action.ifaceUninstalls : Action → Finset InterfaceId
  | .uninstall _ _ iface => {iface}
  | _                    => ∅

namespace PTB

/-! ### Access Roles and Overlap -/

def Action.accessRoles (cfg : AccessConfig) : Action → Finset RoleId
  | .read _ u | .consume _ u | .produce _ u | .lock _ u | .snapshot _ u =>
      {cfg.utxoRole u}
  | .raise _ _ iface _ | .resume _ _ iface _ =>
      {cfg.ifaceRole iface}
  | .install _ _ h =>
      {cfg.ifaceRole h.iface}
  | .uninstall _ _ iface =>
      {cfg.ifaceRole iface}

def overlap {α} [DecidableEq α] (s t : Finset α) : Prop :=
  (s ∩ t).Nonempty

/-! ### Dependencies and Relations -/

/-- Data dependency: command i produces a result consumed by command j. -/
def Program.dataDep (p : Program) (i j : Nat) : Prop :=
  i ∈ p.usesAt j

/-- UTxO dependency: commands access overlapping UTxOs with at least one write. -/
def Program.utxoDep (p : Program) (i j : Nat) : Prop :=
  let ai := p.actionAt i
  let aj := p.actionAt j
  overlap ai.writeUtxos aj.utxoAccesses ∨ overlap aj.writeUtxos ai.utxoAccesses

/-- Handler dependency: one command installs/uninstalls an interface the other uses. -/
def Program.handlerDep (p : Program) (i j : Nat) : Prop :=
  let ai := p.actionAt i
  let aj := p.actionAt j
  overlap ai.ifaceInstalls aj.ifaceUses ∨ overlap ai.ifaceUses aj.ifaceUninstalls

/-- Explicit conflict declared via the conflicts field of commands. -/
def Program.explicitConflict (p : Program) (i j : Nat) : Prop :=
  j ∈ p.conflictsAt i ∨ i ∈ p.conflictsAt j

/-- Two commands conflict if they overlap on consumed UTxOs, interface installs,
or have an explicit conflict declared. -/
def Program.conflictRel (p : Program) (i j : Nat) : Prop :=
  i < p.length ∧ j < p.length ∧ i ≠ j ∧
    (overlap (p.actionAt i).consumedUtxos (p.actionAt j).consumedUtxos ∨
     overlap (p.actionAt i).ifaceInstalls (p.actionAt j).ifaceInstalls ∨
     p.explicitConflict i j)

/-- Causal order: i must execute before j due to data, UTxO, or handler dependency. -/
def Program.orderRel (p : Program) (i j : Nat) : Prop :=
  i < p.length ∧ j < p.length ∧ i < j ∧
    (p.dataDep i j ∨ p.utxoDep i j ∨ p.handlerDep i j)

/-! ### Program to Script Compilation -/

/-- Compile a PTB program to an event-structure script. Events are indexed by
command position; order and conflict relations are derived from dependencies. -/
def Program.toScript (cfg : Config) (p : Program) : Script :=
  { roles    := cfg.roles
  , roleKind := cfg.roleKind
  , events   := p.events
  , label    := p.actionAt
  , order    := p.orderRel
  , conflict := p.conflictRel
  }

def Program.depOK (p : Program) : Prop :=
  ∀ j < p.length, ∀ i ∈ p.usesAt j, i < j

def Program.noSelfConflict (p : Program) : Prop :=
  ∀ i < p.length, i ∉ p.conflictsAt i

def Program.rolesOK (cfg : Config) (p : Program) : Prop :=
  ∀ i < p.length, Action.participants (p.actionAt i) ⊆ cfg.roles

def Program.roleKindOK (cfg : Config) (p : Program) : Prop :=
  ∀ i < p.length,
    match p.actionAt i with
    | .read r _ | .consume r _ | .produce r _ | .lock r _ | .snapshot r _ =>
        cfg.roleKind r = RoleKind.utxo
    | _ => True

def Program.accessRolesOK (cfg : AccessConfig) (p : Program) : Prop :=
  ∀ i < p.length, Action.accessRoles cfg (p.actionAt i) ⊆ Action.participants (p.actionAt i)

def Program.explicitConflictShared (cfg : AccessConfig) (p : Program) : Prop :=
  ∀ i j, p.explicitConflict i j →
    Script.shareRole (p.toScript cfg.toConfig) i j

def Program.noConflicts (p : Program) : Prop :=
  ∀ i j, i < p.length → j < p.length → ¬ p.conflictRel i j

def Program.conflictFree (p : Program) (keep : Nat → Bool) : Prop :=
  ∀ i j, i < p.length → j < p.length → keep i = true → keep j = true →
    ¬ p.conflictRel i j

def Program.downClosed (p : Program) (keep : Nat → Bool) : Prop :=
  ∀ i j, keep j = true → p.orderRel i j → keep i = true

/-! ### Trace Definitions -/

def Program.traceFrom : Nat → Nat → List EventId
  | start, 0 => []
  | start, n + 1 => start :: traceFrom (start + 1) n

def Program.trace (p : Program) : List EventId :=
  Program.traceFrom 0 p.length

def Program.traceFromKeep : Nat → Nat → (Nat → Bool) → List EventId
  | start, 0, _ => []
  | start, n + 1, keep =>
      if keep start
      then start :: traceFromKeep (start + 1) n keep
      else traceFromKeep (start + 1) n keep

def Program.traceOf (p : Program) (keep : Nat → Bool) : List EventId :=
  Program.traceFromKeep 0 p.length keep

/-! ### Relation Properties -/

lemma overlap_symm {α} [DecidableEq α] {s t : Finset α} :
    overlap s t → overlap t s := by
  intro h
  simpa [overlap, Finset.inter_comm] using h

lemma Program.explicitConflict_symm {p : Program} {i j : Nat} :
    p.explicitConflict i j ↔ p.explicitConflict j i := by
  simp [Program.explicitConflict, or_comm, or_left_comm]

lemma Action.accessRoles_of_consumed {cfg : AccessConfig} {a : Action} {u : UTXOId}
    (h : u ∈ a.consumedUtxos) : cfg.utxoRole u ∈ Action.accessRoles cfg a := by
  cases a <;> simp only [Action.consumedUtxos, Action.accessRoles, Finset.mem_singleton] at h ⊢
  all_goals (try exact h)
  all_goals (try simp_all)

lemma Action.accessRoles_of_ifaceInstall {cfg : AccessConfig} {a : Action} {i : InterfaceId}
    (h : i ∈ a.ifaceInstalls) : cfg.ifaceRole i ∈ Action.accessRoles cfg a := by
  cases a <;> simp only [Action.ifaceInstalls, Action.accessRoles, Finset.mem_singleton] at h ⊢
  all_goals (try exact h)
  all_goals (try simp_all)

lemma Script.shareRole_not_disjoint {s : Script} {e f : EventId} :
    s.shareRole e f → ¬ s.disjointRoles e f := by
  intro hshare hdisj
  rcases hshare with ⟨r, hr⟩
  have ⟨hre, hrf⟩ := Finset.mem_inter.mp hr
  exact Finset.disjoint_left.mp hdisj hre hrf

lemma Program.conflictRel_symm {p : Program} {i j : Nat} :
    p.conflictRel i j ↔ p.conflictRel j i := by
  constructor
  · intro h
    rcases h with ⟨hi, hj, hneq, hrest⟩
    refine ⟨hj, hi, Ne.symm hneq, ?_⟩
    rcases hrest with hrest | hrest | hrest
    · exact Or.inl (overlap_symm hrest)
    · exact Or.inr (Or.inl (overlap_symm hrest))
    · exact Or.inr (Or.inr ((Program.explicitConflict_symm).2 hrest))
  · intro h
    rcases h with ⟨hi, hj, hneq, hrest⟩
    refine ⟨hj, hi, Ne.symm hneq, ?_⟩
    rcases hrest with hrest | hrest | hrest
    · exact Or.inl (overlap_symm hrest)
    · exact Or.inr (Or.inl (overlap_symm hrest))
    · exact Or.inr (Or.inr ((Program.explicitConflict_symm).1 hrest))

/-- Conflicting commands share at least one role: via UTxO overlap, interface
overlap, or explicit conflict hypothesis. -/
lemma Program.shareRole_of_conflictRel
    (cfg : AccessConfig) (p : Program)
    (hroles : p.accessRolesOK cfg)
    (hexplShared : p.explicitConflictShared cfg) :
    ∀ i j, p.conflictRel i j →
      Script.shareRole (p.toScript cfg.toConfig) i j := by
  intro i j hconf
  rcases hconf with ⟨hi, hj, _, hcase⟩
  rcases hcase with hoverlap_utxo | hoverlap_iface | hexpl
  · -- consumedUtxos overlap
    rcases hoverlap_utxo with ⟨u, hu⟩
    have hu_i := (Finset.mem_inter.mp hu).1
    have hu_j := (Finset.mem_inter.mp hu).2
    simp only [Script.shareRole, Program.toScript]
    exact ⟨cfg.utxoRole u, Finset.mem_inter.mpr
      ⟨hroles i hi (Action.accessRoles_of_consumed hu_i),
       hroles j hj (Action.accessRoles_of_consumed hu_j)⟩⟩
  · -- ifaceInstalls overlap
    rcases hoverlap_iface with ⟨iface, hiface⟩
    have hi_i := (Finset.mem_inter.mp hiface).1
    have hi_j := (Finset.mem_inter.mp hiface).2
    simp only [Script.shareRole, Program.toScript]
    exact ⟨cfg.ifaceRole iface, Finset.mem_inter.mpr
      ⟨hroles i hi (Action.accessRoles_of_ifaceInstall hi_i),
       hroles j hj (Action.accessRoles_of_ifaceInstall hi_j)⟩⟩
  · exact hexplShared i j hexpl

def Program.crossRoleSafe (cfg : AccessConfig) (p : Program) : Prop :=
  ∀ i j, p.conflictRel i j → ¬ (p.toScript cfg.toConfig).disjointRoles i j

theorem Program.crossRoleSafe_of_access
    (cfg : AccessConfig) (p : Program)
    (hroles : p.accessRolesOK cfg)
    (hexpl : p.explicitConflictShared cfg) :
    p.crossRoleSafe cfg := by
  intro i j hconf hdisj
  have hshare := Program.shareRole_of_conflictRel cfg p hroles hexpl i j hconf
  exact (Script.shareRole_not_disjoint hshare) hdisj

lemma Program.orderRel_lt {p : Program} {i j : Nat} (h : p.orderRel i j) : i < j := by
  rcases h with ⟨_hi, _hj, hij, _⟩
  exact hij

lemma Program.transGen_order_lt {p : Program} {i j : Nat}
    (h : Relation.TransGen p.orderRel i j) : i < j := by
  induction h with
  | single h1 => exact Program.orderRel_lt h1
  | tail _ h2 ih => exact Nat.lt_trans ih (Program.orderRel_lt h2)

lemma finset_range_succ (k : Nat) :
    insert k (Finset.range k) = Finset.range (k + 1) := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_range]
  omega

lemma filter_insert_true {p : EventId → Bool} {C : Finset EventId} {e : EventId}
    (h : p e = true) :
    (insert e C).filter (fun x => p x = true) = insert e (C.filter (fun x => p x = true)) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · intro ⟨hx, hp⟩
    rcases hx with rfl | hxC
    · exact Or.inl rfl
    · exact Or.inr ⟨hxC, hp⟩
  · intro hx
    rcases hx with rfl | ⟨hxC, hp⟩
    · exact ⟨Or.inl rfl, h⟩
    · exact ⟨Or.inr hxC, hp⟩

/-! ### Trace Validity -/

/-- PTB compilation preserves well-formedness: the resulting script satisfies
orderDom, conflictDom, conflictIrrefl, conflictSymm, orderAcyclic, rolesOK, roleKindOK. -/
theorem Program.toScript_wellFormed
    (cfg : Config) (p : Program)
    (hroles : p.rolesOK cfg)
    (hkind : p.roleKindOK cfg) :
    (p.toScript cfg).wellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e f hord -- orderDom
    simp only [Program.toScript, Program.events, Finset.mem_range]
    rcases hord with ⟨he, hf, _, _⟩; exact ⟨he, hf⟩
  · intro e f hconf -- conflictDom
    simp only [Program.toScript, Program.events, Finset.mem_range]
    rcases hconf with ⟨he, hf, _, _⟩; exact ⟨he, hf⟩
  · intro e _ hconf -- conflictIrrefl
    rcases hconf with ⟨_, _, hneq, _⟩; exact hneq rfl
  · intro e f hconf -- conflictSymm
    exact Program.conflictRel_symm.1 hconf
  · intro e hcycle -- orderAcyclic
    exact Nat.lt_irrefl e (Program.transGen_order_lt hcycle)
  · intro e he -- rolesOK
    simp only [Program.toScript, Program.events, Finset.mem_range] at he
    exact hroles e he
  · intro e he -- roleKindOK
    simp only [Program.toScript, Program.events, Finset.mem_range] at he
    exact hkind e he

/-- A sequential trace through a conflict-free program is valid: each command
is enabled when executed. Proof by induction on trace length. -/
theorem Program.validTraceAux_traceFrom
    (cfg : Config) (p : Program)
    (hno : p.noConflicts) :
    ∀ start n, start + n ≤ p.length →
      Script.validTraceAux (p.toScript cfg) (Finset.range start) (Program.traceFrom start n) := by
  intro start n
  induction n generalizing start with
  | zero => intro _; simp only [Program.traceFrom, Script.validTraceAux]
  | succ n ih =>
      intro hbound
      simp only [Program.traceFrom, Script.validTraceAux]
      have hstart_bound : start < p.length :=
        Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos n)) hbound
      constructor
      · simp only [Script.enabled, Program.toScript, Program.events]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [Finset.mem_range]; exact hstart_bound
        · simp only [Finset.mem_range, Nat.lt_irrefl, not_false_eq_true]
        · intro e' hord; simp only [Finset.mem_range]; exact Program.orderRel_lt hord
        · intro f hf hconf
          simp only [Finset.mem_range] at hf
          exact hno start f hstart_bound (Nat.lt_trans hf hstart_bound) hconf
      · rw [finset_range_succ]
        exact ih (start + 1) (by omega : start + 1 + n ≤ p.length)

/-- Full sequential trace of a conflict-free program is valid. -/
theorem Program.validTrace_trace
    (cfg : Config) (p : Program)
    (hno : p.noConflicts) :
    Script.validTrace (p.toScript cfg) (p.trace) := by
  have haux :=
    Program.validTraceAux_traceFrom cfg p hno 0 p.length (by simp)
  simpa [Program.trace, Script.validTrace] using haux

/-- A filtered trace is valid when the filter is conflict-free and down-closed.
Down-closure ensures order dependencies; conflict-freedom prevents conflicts. -/
theorem Program.validTraceAux_traceFromKeep
    (cfg : Config) (p : Program) (keep : Nat → Bool)
    (hconf : p.conflictFree keep)
    (hdown : p.downClosed keep) :
    ∀ start n, start + n ≤ p.length →
      Script.validTraceAux (p.toScript cfg)
        ((Finset.range start).filter (fun x => keep x = true))
        (Program.traceFromKeep start n keep) := by
  intro start n
  induction n generalizing start with
  | zero => intro _; simp only [Program.traceFromKeep, Script.validTraceAux]
  | succ n ih =>
      intro hbound
      have hstart_bound : start < p.length :=
        Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos n)) hbound
      simp only [Program.traceFromKeep]
      by_cases hk : keep start = true
      · simp only [hk, ↓reduceIte, Script.validTraceAux]
        constructor
        · simp only [Script.enabled, Program.toScript, Program.events]
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [Finset.mem_range]; exact hstart_bound
          · simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_irrefl,
              false_and, not_false_eq_true]
          · intro e' hord
            simp only [Finset.mem_filter, Finset.mem_range, Program.orderRel_lt hord,
              hdown e' start hk hord, and_self]
          · intro f hf hconflict
            simp only [Finset.mem_filter, Finset.mem_range] at hf
            exact hconf start f hstart_bound (Nat.lt_trans hf.1 hstart_bound) hk hf.2 hconflict
        · have heq : insert start ((Finset.range start).filter (fun x => keep x = true)) =
              (Finset.range (start + 1)).filter (fun x => keep x = true) := by
            ext x; simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
            constructor
            · intro h
              cases h with
              | inl hxeq => subst hxeq; exact ⟨Nat.lt_succ_self x, hk⟩
              | inr hand => exact ⟨Nat.lt_succ_of_lt hand.1, hand.2⟩
            · intro ⟨hlt, hkx⟩
              by_cases hxeq : x = start
              · exact Or.inl hxeq
              · right; constructor
                · cases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with
                  | inl hlt' => exact hlt'
                  | inr heq => exact absurd heq hxeq
                · exact hkx
          rw [heq]; exact ih (start + 1) (by omega)
      · simp only [hk, Bool.false_eq_true, ↓reduceIte]
        have heq : (Finset.range start).filter (fun x => keep x = true) =
            (Finset.range (start + 1)).filter (fun x => keep x = true) := by
          ext x; simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · intro ⟨hlt, hkx⟩; exact ⟨Nat.lt_succ_of_lt hlt, hkx⟩
          · intro ⟨hlt, hkx⟩
            have hne : x ≠ start := fun hxeq => hk (hxeq ▸ hkx)
            constructor
            · cases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with
              | inl hlt' => exact hlt'
              | inr heq => exact absurd heq hne
            · exact hkx
        rw [heq]; exact ih (start + 1) (by omega)

theorem Program.validTrace_traceOf
    (cfg : Config) (p : Program) (keep : Nat → Bool)
    (hconf : p.conflictFree keep)
    (hdown : p.downClosed keep) :
    Script.validTrace (p.toScript cfg) (p.traceOf keep) := by
  have haux :=
    Program.validTraceAux_traceFromKeep cfg p keep hconf hdown 0 p.length (by simp)
  simpa [Program.traceOf, Script.validTrace] using haux

/-! ### Membership and Ordering Lemmas -/

/-- Membership characterization: i is in the filtered trace iff it's in range
and passes the filter predicate. -/
lemma Program.mem_traceFromKeep_iff
    (keep : Nat → Bool) :
    ∀ start n i,
      i ∈ Program.traceFromKeep start n keep ↔
        start ≤ i ∧ i < start + n ∧ keep i = true := by
  intro start n
  induction n generalizing start with
  | zero =>
      intro i
      simp only [Program.traceFromKeep, List.not_mem_nil, false_iff, Nat.add_zero]
      intro ⟨hle, hlt, _⟩
      exact Nat.not_lt.mpr hle hlt
  | succ n ih =>
      intro i
      simp only [Program.traceFromKeep]
      by_cases hk : keep start = true
      · simp only [hk, ↓reduceIte, List.mem_cons]
        constructor
        · intro h
          cases h with
          | inl heq =>
            subst heq
            exact ⟨Nat.le_refl i, Nat.lt_add_of_pos_right (Nat.succ_pos n), hk⟩
          | inr hmem =>
            have ⟨hle, hlt, hki⟩ := (ih (start + 1) i).mp hmem
            exact ⟨Nat.le_of_succ_le hle, Nat.lt_of_lt_of_eq hlt (Nat.add_right_comm start 1 n), hki⟩
        · intro ⟨hle, hlt, hki⟩
          by_cases heq : i = start
          · exact Or.inl heq
          · right
            rw [ih (start + 1) i]
            have hle' : start + 1 ≤ i := Nat.lt_of_le_of_ne hle (Ne.symm heq)
            have hlt' : i < start + 1 + n := by rw [Nat.add_right_comm]; exact hlt
            exact ⟨hle', hlt', hki⟩
      · simp only [hk, Bool.false_eq_true, ↓reduceIte]
        rw [ih (start + 1) i]
        have heq_add : start + 1 + n = start + (n + 1) := by ring
        constructor
        · intro ⟨hle, hlt, hki⟩
          have hle' : start ≤ i := Nat.le_of_succ_le hle
          have hlt' : i < start + (n + 1) := heq_add ▸ hlt
          exact ⟨hle', hlt', hki⟩
        · intro ⟨hle, hlt, hki⟩
          have hne : i ≠ start := by
            intro heq
            rw [heq] at hki
            simp only [Bool.true_eq_false] at hk
            exact hk hki
          have hle' : start + 1 ≤ i := Nat.lt_of_le_of_ne hle (Ne.symm hne)
          have hlt' : i < start + 1 + n := heq_add ▸ hlt
          exact ⟨hle', hlt', hki⟩

lemma Program.mem_traceOf_iff
    (p : Program) (keep : Nat → Bool) (i : Nat) :
    i ∈ p.traceOf keep ↔ i < p.length ∧ keep i = true := by
  have h := (Program.mem_traceFromKeep_iff keep 0 p.length i)
  simpa [Program.traceOf] using h

/-- Numeric order implies list order: if i < j and both are in the trace,
then i appears before j in the list. -/
lemma Program.before_traceFromKeep_of_lt
    (keep : Nat → Bool) :
    ∀ start n i j,
      i < j →
      i ∈ Program.traceFromKeep start n keep →
      j ∈ Program.traceFromKeep start n keep →
      Before (Program.traceFromKeep start n keep) i j := by
  intro start n
  induction n generalizing start with
  | zero => intro i j _ hi _; simp only [Program.traceFromKeep, List.not_mem_nil] at hi
  | succ n ih =>
      intro i j hij hi hj
      simp only [Program.traceFromKeep] at hi hj ⊢
      by_cases hk : keep start = true
      · simp only [hk, ↓reduceIte] at hi hj ⊢
        cases hi with
        | head =>
          have hj' : j ∈ Program.traceFromKeep (start + 1) n keep := by
            cases hj with
            | head => exact absurd hij (Nat.lt_irrefl _)
            | tail _ hj'' => exact hj''
          exact before_head hj'
        | tail _ hi' =>
          have hj' : j ∈ Program.traceFromKeep (start + 1) n keep := by
            cases hj with
            | head =>
              have ⟨hle, _, _⟩ := (Program.mem_traceFromKeep_iff keep (start + 1) n i).mp hi'
              exact absurd hij (Nat.not_lt.mpr (Nat.le_of_succ_le hle))
            | tail _ hj'' => exact hj''
          exact before_cons_of_tail (ih (start + 1) i j hij hi' hj')
      · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hi hj ⊢
        exact ih (start + 1) i j hij hi hj

lemma Program.before_traceOf_of_order
    (cfg : Config) (p : Program) (keep : Nat → Bool)
    (hdown : p.downClosed keep)
    {i j : Nat}
    (hj : j ∈ p.traceOf keep)
    (hord : p.orderRel i j) :
    Before (p.traceOf keep) i j := by
  have hj' : j < p.length ∧ keep j = true := (Program.mem_traceOf_iff p keep j).1 hj
  have hkeepi : keep i = true := hdown i j hj'.2 hord
  have hij : i < j := Program.orderRel_lt hord
  rcases hord with ⟨hiLen, _hjLen, _hij, _⟩
  have hi : i ∈ p.traceOf keep := (Program.mem_traceOf_iff p keep i).2 ⟨hiLen, hkeepi⟩
  exact Program.before_traceFromKeep_of_lt keep 0 p.length i j hij hi hj

/-! ### Witness Construction -/

theorem Program.crossRoleConsistent_traceOf
    (cfg : AccessConfig) (p : Program) (keep : Nat → Bool)
    (hdown : p.downClosed keep)
    (hcross : p.crossRoleSafe cfg) :
    (p.toScript cfg.toConfig).crossRoleConsistent (p.traceOf keep) := by
  refine ⟨?conflict, ?order⟩
  · intro e f he hf hdisj
    have hnot : ¬ p.conflictRel e f := by
      intro hcf
      exact (hcross e f hcf) hdisj
    have hnot' : ¬ p.conflictRel f e := by
      intro hcf
      have hcf' : p.conflictRel e f := (Program.conflictRel_symm).1 hcf
      exact hnot hcf'
    exact ⟨hnot, hnot'⟩
  · intro e' e hdisj hord he
    exact Program.before_traceOf_of_order (cfg := cfg.toConfig) (p := p) (keep := keep) hdown he hord

/-- Construct a coordination witness from a PTB program and filter. -/
def Program.toWitness (cfg : AccessConfig) (p : Program) (keep : Nat → Bool) : CoordWitness :=
  { script := p.toScript cfg.toConfig, trace := p.traceOf keep }

/-- A PTB program with valid configuration produces a globally-conforming
coordination witness. -/
theorem Program.witnessGlobalOK_of
    (cfg : AccessConfig) (p : Program) (keep : Nat → Bool)
    (hroles : p.rolesOK cfg.toConfig)
    (hkind : p.roleKindOK cfg.toConfig)
    (hconf : p.conflictFree keep)
    (hdown : p.downClosed keep) :
    witnessGlobalOK (Program.toWitness cfg p keep) := by
  dsimp [Program.toWitness, witnessGlobalOK, Script.globalConform]
  refine ⟨Program.toScript_wellFormed cfg.toConfig p hroles hkind, ?_⟩
  exact Program.validTrace_traceOf cfg.toConfig p keep hconf hdown

end PTB

end Starstream
