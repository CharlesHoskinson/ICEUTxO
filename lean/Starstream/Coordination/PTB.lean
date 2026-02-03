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
  deriving Repr

structure Program where
  cmds : List Command
  deriving Repr

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

def Program.dataDep (p : Program) (i j : Nat) : Prop :=
  i ∈ p.usesAt j

def Program.utxoDep (p : Program) (i j : Nat) : Prop :=
  let ai := p.actionAt i
  let aj := p.actionAt j
  overlap ai.writeUtxos aj.utxoAccesses ∨ overlap aj.writeUtxos ai.utxoAccesses

def Program.handlerDep (p : Program) (i j : Nat) : Prop :=
  let ai := p.actionAt i
  let aj := p.actionAt j
  overlap ai.ifaceInstalls aj.ifaceUses ∨ overlap ai.ifaceUses aj.ifaceUninstalls

def Program.explicitConflict (p : Program) (i j : Nat) : Prop :=
  j ∈ p.conflictsAt i ∨ i ∈ p.conflictsAt j

def Program.conflictRel (p : Program) (i j : Nat) : Prop :=
  i < p.length ∧ j < p.length ∧ i ≠ j ∧
    (overlap (p.actionAt i).consumedUtxos (p.actionAt j).consumedUtxos ∨
     overlap (p.actionAt i).ifaceInstalls (p.actionAt j).ifaceInstalls ∨
     p.explicitConflict i j)

def Program.orderRel (p : Program) (i j : Nat) : Prop :=
  i < p.length ∧ j < p.length ∧ i < j ∧
    (p.dataDep i j ∨ p.utxoDep i j ∨ p.handlerDep i j)

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

lemma overlap_symm {α} [DecidableEq α] {s t : Finset α} :
    overlap s t → overlap t s := by
  intro h
  simpa [overlap, Finset.inter_comm] using h

lemma Program.explicitConflict_symm {p : Program} {i j : Nat} :
    p.explicitConflict i j ↔ p.explicitConflict j i := by
  simp [Program.explicitConflict, or_comm, or_left_comm]

lemma Action.accessRoles_of_consumed {cfg : AccessConfig} {a : Action} {u : UTXOId}
    (h : u ∈ a.consumedUtxos) : cfg.utxoRole u ∈ Action.accessRoles cfg a := by
  cases a <;> simp [Action.consumedUtxos, Action.accessRoles] at h ⊢

lemma Action.accessRoles_of_ifaceInstall {cfg : AccessConfig} {a : Action} {i : InterfaceId}
    (h : i ∈ a.ifaceInstalls) : cfg.ifaceRole i ∈ Action.accessRoles cfg a := by
  cases a <;> simp [Action.ifaceInstalls, Action.accessRoles] at h ⊢

lemma Script.shareRole_not_disjoint {s : Script} {e f : EventId} :
    s.shareRole e f → ¬ s.disjointRoles e f := by
  intro hshare hdisj
  rcases hshare with ⟨r, hr⟩
  rcases Finset.mem_inter.mp hr with ⟨hre, hrf⟩
  have hdisj' := Finset.disjoint_left.mp hdisj
  exact (hdisj' r hre hrf)

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

lemma Program.shareRole_of_conflictRel
    (cfg : AccessConfig) (p : Program)
    (hroles : p.accessRolesOK cfg)
    (hexplShared : p.explicitConflictShared cfg) :
    ∀ i j, p.conflictRel i j →
      Script.shareRole (p.toScript cfg.toConfig) i j := by
  intro i j hconf
  rcases hconf with ⟨hi, hj, _hneq, hrest⟩
  rcases hrest with hcons | hinst | hexpl
  · rcases hcons with ⟨u, hu⟩
    rcases Finset.mem_inter.mp hu with ⟨hui, huj⟩
    have hri : cfg.utxoRole u ∈ Action.participants (p.actionAt i) := by
      have hacc := hroles i hi
      exact hacc (Action.accessRoles_of_consumed (a := p.actionAt i) hui)
    have hrj : cfg.utxoRole u ∈ Action.participants (p.actionAt j) := by
      have hacc := hroles j hj
      exact hacc (Action.accessRoles_of_consumed (a := p.actionAt j) huj)
    exact ⟨cfg.utxoRole u, Finset.mem_inter.mpr ⟨hri, hrj⟩⟩
  · rcases hinst with ⟨iface, hiI, hjI⟩
    have hri : cfg.ifaceRole iface ∈ Action.participants (p.actionAt i) := by
      have hacc := hroles i hi
      exact hacc (Action.accessRoles_of_ifaceInstall (a := p.actionAt i) hiI)
    have hrj : cfg.ifaceRole iface ∈ Action.participants (p.actionAt j) := by
      have hacc := hroles j hj
      exact hacc (Action.accessRoles_of_ifaceInstall (a := p.actionAt j) hjI)
    exact ⟨cfg.ifaceRole iface, Finset.mem_inter.mpr ⟨hri, hrj⟩⟩
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
  | tail h1 h2 ih =>
      exact lt_trans (Program.orderRel_lt h1) ih

lemma finset_range_succ (k : Nat) :
    insert k (Finset.range k) = Finset.range (k + 1) := by
  ext x
  by_cases hx : x = k
  · subst hx
    simp [Finset.mem_range]
  · have hx' : x < k ↔ x < k + 1 := by
      constructor
      · intro hlt
        exact Nat.lt_trans hlt (Nat.lt_succ_self k)
      · intro hlt
        have hle : x ≤ k := Nat.lt_succ_iff.mp hlt
        exact lt_of_le_of_ne hle (Ne.symm hx)
    simp [Finset.mem_range, hx, hx']

lemma filter_insert_true {p : EventId → Bool} {C : Finset EventId} {e : EventId}
    (h : p e = true) :
    (insert e C).filter p = insert e (C.filter p) := by
  ext x
  by_cases hx : x = e
  · subst hx
    simp [h]
  · simp [Finset.mem_filter, Finset.mem_insert, hx, h]

theorem Program.toScript_wellFormed
    (cfg : Config) (p : Program)
    (hroles : p.rolesOK cfg)
    (hkind : p.roleKindOK cfg) :
    (p.toScript cfg).wellFormed := by
  -- Unpack Script.wellFormed
  refine ⟨?orderDom, ?confDom, ?confIrrefl, ?confSymm, ?acyc, ?rolesOK, ?roleKindOK⟩
  · intro e f horder
    rcases horder with ⟨he, hf, _hij, _⟩
    exact ⟨by simpa [Program.events] using he, by simpa [Program.events] using hf⟩
  · intro e f hconf'
    rcases hconf' with ⟨he, hf, _hneq, _⟩
    exact ⟨by simpa [Program.events] using he, by simpa [Program.events] using hf⟩
  · intro e he hcf
    rcases hcf with ⟨_he, _hf, hneq, _⟩
    exact hneq rfl
  · intro e f hcf
    rcases hcf with ⟨he, hf, hneq, hrest⟩
    refine ⟨hf, he, Ne.symm hneq, ?_⟩
    rcases hrest with hrest | hrest | hrest
    · exact Or.inl (overlap_symm hrest)
    · exact Or.inr (Or.inl (overlap_symm hrest))
    · exact Or.inr (Or.inr ((Program.explicitConflict_symm).1 hrest))
  · intro e hcycle
    have hlt : e < e := Program.transGen_order_lt hcycle
    exact (lt_irrefl _ hlt)
  · intro e he
    have helt : e < p.length := by
      simpa [Program.toScript, Program.events] using he
    exact hroles e helt
  · intro e he
    have helt : e < p.length := by
      simpa [Program.toScript, Program.events] using he
    exact hkind e helt

theorem Program.validTraceAux_traceFrom
    (cfg : Config) (p : Program)
    (hno : p.noConflicts) :
    ∀ start n, start + n ≤ p.length →
      Script.validTraceAux (p.toScript cfg) (Finset.range start) (Program.traceFrom start n) := by
  intro start n hlen
  induction n with
  | zero =>
      simp [Program.traceFrom, Script.validTraceAux]
  | succ n ih =>
      have hstart_lt : start < p.length := by
        have hpos : 0 < n + 1 := Nat.succ_pos _
        have hlt : start < start + (n + 1) := Nat.lt_add_of_pos_right hpos
        exact Nat.lt_of_lt_of_le hlt hlen
      have hmem : start ∈ (p.toScript cfg).events := by
        simp [Program.toScript, Program.events, hstart_lt]
      have hnotin : start ∉ Finset.range start := by
        simp [Finset.mem_range]
      have hpreds : ∀ e', (p.toScript cfg).order e' start → e' ∈ Finset.range start := by
        intro e' horder
        have hlt : e' < start := Program.orderRel_lt horder
        simpa [Finset.mem_range] using hlt
      have hconf : ∀ f ∈ Finset.range start, ¬ (p.toScript cfg).conflict start f := by
        intro f hf
        have hf_lt : f < start := by
          simpa [Finset.mem_range] using hf
        have hf_len : f < p.length := lt_trans hf_lt hstart_lt
        exact hno start f hstart_lt hf_len
      have hen : (p.toScript cfg).enabled start (Finset.range start) := by
        exact ⟨hmem, hnotin, hpreds, hconf⟩
      have hlen' : start + 1 + n ≤ p.length := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlen
      have ih' := ih (start + 1) hlen'
      have ih'' : Script.validTraceAux (p.toScript cfg)
          (insert start (Finset.range start)) (Program.traceFrom (start + 1) n) := by
        simpa [finset_range_succ] using ih'
      simp [Program.traceFrom, Script.validTraceAux, hen, ih'']

theorem Program.validTrace_trace
    (cfg : Config) (p : Program)
    (hno : p.noConflicts) :
    Script.validTrace (p.toScript cfg) (p.trace) := by
  have haux :=
    Program.validTraceAux_traceFrom cfg p hno 0 p.length (by simp)
  simpa [Program.trace, Script.validTrace] using haux

theorem Program.validTraceAux_traceFromKeep
    (cfg : Config) (p : Program) (keep : Nat → Bool)
    (hconf : p.conflictFree keep)
    (hdown : p.downClosed keep) :
    ∀ start n, start + n ≤ p.length →
      Script.validTraceAux (p.toScript cfg)
        ((Finset.range start).filter keep)
        (Program.traceFromKeep start n keep) := by
  intro start n hlen
  induction n with
  | zero =>
      simp [Program.traceFromKeep, Script.validTraceAux]
  | succ n ih =>
      by_cases hkeep : keep start = true
      · have hstart_lt : start < p.length := by
          have hpos : 0 < n + 1 := Nat.succ_pos _
          have hlt : start < start + (n + 1) := Nat.lt_add_of_pos_right hpos
          exact Nat.lt_of_lt_of_le hlt hlen
        have hmem : start ∈ (p.toScript cfg).events := by
          simp [Program.toScript, Program.events, hstart_lt]
        have hnotin : start ∉ (Finset.range start).filter keep := by
          simp [Finset.mem_filter, Finset.mem_range]
        have hpreds :
            ∀ e', (p.toScript cfg).order e' start →
              e' ∈ (Finset.range start).filter keep := by
          intro e' horder
          have hlt : e' < start := Program.orderRel_lt horder
          have hkeep' : keep e' = true := hdown e' start hkeep horder
          exact Finset.mem_filter.mpr ⟨by simpa [Finset.mem_range] using hlt, hkeep'⟩
        have hconf' :
            ∀ f ∈ (Finset.range start).filter keep,
              ¬ (p.toScript cfg).conflict start f := by
          intro f hf
          have hf_lt : f < start := by
            have hf' : f < start := (Finset.mem_filter.mp hf).1
            simpa [Finset.mem_range] using hf'
          have hf_len : f < p.length := lt_trans hf_lt hstart_lt
          have hkeepf : keep f = true := (Finset.mem_filter.mp hf).2
          exact hconf start f hstart_lt hf_len hkeep hkeepf
        have hen : (p.toScript cfg).enabled start ((Finset.range start).filter keep) := by
          exact ⟨hmem, hnotin, hpreds, hconf'⟩
        have hlen' : start + 1 + n ≤ p.length := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlen
        have ih' := ih (start + 1) hlen'
        have hctx :
            (Finset.range (start + 1)).filter keep =
              insert start ((Finset.range start).filter keep) := by
          simpa [finset_range_succ] using
            (filter_insert_true (p := keep) (C := Finset.range start) (e := start) hkeep)
        have ih'' :
            Script.validTraceAux (p.toScript cfg)
              (insert start ((Finset.range start).filter keep))
              (Program.traceFromKeep (start + 1) n keep) := by
          simpa [hctx] using ih'
        simp [Program.traceFromKeep, hkeep, Script.validTraceAux, hen, ih'']
      · have hlen' : start + 1 + n ≤ p.length := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlen
        have ih' := ih (start + 1) hlen'
        have hctx :
            (Finset.range (start + 1)).filter keep =
              (Finset.range start).filter keep := by
          simpa [finset_range_succ] using
            (filter_insert_false (p := keep) (C := Finset.range start) (e := start) hkeep)
        have ih'' :
            Script.validTraceAux (p.toScript cfg)
              ((Finset.range start).filter keep)
              (Program.traceFromKeep (start + 1) n keep) := by
          simpa [hctx] using ih'
        simpa [Program.traceFromKeep, hkeep, Script.validTraceAux] using ih''

theorem Program.validTrace_traceOf
    (cfg : Config) (p : Program) (keep : Nat → Bool)
    (hconf : p.conflictFree keep)
    (hdown : p.downClosed keep) :
    Script.validTrace (p.toScript cfg) (p.traceOf keep) := by
  have haux :=
    Program.validTraceAux_traceFromKeep cfg p keep hconf hdown 0 p.length (by simp)
  simpa [Program.traceOf, Script.validTrace] using haux

lemma Program.mem_traceFromKeep_iff
    (keep : Nat → Bool) :
    ∀ start n i,
      i ∈ Program.traceFromKeep start n keep ↔
        start ≤ i ∧ i < start + n ∧ keep i = true := by
  intro start n
  induction n with
  | zero =>
      intro i
      simp [Program.traceFromKeep]
  | succ n ih =>
      intro i
      by_cases hkeep : keep start = true
      · simp [Program.traceFromKeep, hkeep] at *
        constructor
        · intro h
          cases h with
          | inl h1 =>
              subst h1
              refine ⟨le_rfl, ?_, hkeep⟩
              have : start < start + (n + 1) := Nat.lt_add_of_pos_right (Nat.succ_pos _)
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
          | inr h1 =>
              have ih' := (ih i).1 h1
              rcases ih' with ⟨hlo, hhi, hkeepi⟩
              refine ⟨le_trans (Nat.le_succ _) hlo, ?_, hkeepi⟩
              have : i < start + (n + 1) := by
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hhi
              exact this
        · intro h
          rcases h with ⟨hlo, hhi, hkeepi⟩
          by_cases hEq : i = start
          · left; exact hEq
          · right
            have hlo' : start + 1 ≤ i := by
              have hlo' : start ≤ i := hlo
              exact Nat.succ_le_of_lt (lt_of_le_of_ne hlo' hEq.symm)
            have hhi' : i < start + 1 + n := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hhi
            have ih' := (ih i).2 ⟨hlo', hhi', hkeepi⟩
            exact ih'
      · simp [Program.traceFromKeep, hkeep] at *
        constructor
        · intro h
          have ih' := (ih i).1 h
          rcases ih' with ⟨hlo, hhi, hkeepi⟩
          refine ⟨le_trans (Nat.le_succ _) hlo, ?_, hkeepi⟩
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hhi
        · intro h
          rcases h with ⟨hlo, hhi, hkeepi⟩
          have hneq : i ≠ start := by
            intro hEq
            subst hEq
            have htrue : keep start = true := by simpa using hkeepi
            have htf : (true = false) := by exact htrue.trans hkeep
            cases htf
          have hlo' : start + 1 ≤ i :=
            Nat.succ_le_of_lt (lt_of_le_of_ne hlo hneq)
          have hhi' : i < start + 1 + n := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hhi
          exact (ih i).2 ⟨hlo', hhi', hkeepi⟩

lemma Program.mem_traceOf_iff
    (p : Program) (keep : Nat → Bool) (i : Nat) :
    i ∈ p.traceOf keep ↔ i < p.length ∧ keep i = true := by
  have h := (Program.mem_traceFromKeep_iff keep 0 p.length i)
  simpa [Program.traceOf] using h

lemma Program.before_traceFromKeep_of_lt
    (keep : Nat → Bool) :
    ∀ start n i j,
      i < j →
      i ∈ Program.traceFromKeep start n keep →
      j ∈ Program.traceFromKeep start n keep →
      Before (Program.traceFromKeep start n keep) i j := by
  intro start n
  induction n with
  | zero =>
      intro i j _ hi _
      cases hi
  | succ n ih =>
      intro i j hij hi hj
      by_cases hkeep : keep start = true
      · simp [Program.traceFromKeep, hkeep] at hi hj ⊢
        cases hi with
        | inl hi_eq =>
            subst hi_eq
            exact before_head hj
        | inr hi_tail =>
            cases hj with
            | inl hj_eq =>
                subst hj_eq
                exact (Nat.lt_irrefl _ hij).elim
            | inr hj_tail =>
                exact before_cons_of_tail (ih _ _ hij hi_tail hj_tail)
      · simp [Program.traceFromKeep, hkeep] at hi hj ⊢
        exact ih _ _ hij hi hj

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

def Program.toWitness (cfg : AccessConfig) (p : Program) (keep : Nat → Bool) : CoordWitness :=
  { script := p.toScript cfg.toConfig, trace := p.traceOf keep }

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
