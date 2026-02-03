import StarstreamPilot

namespace Starstream

open Finset

/-! # Coordination Script Core (MPST-style)

Not yet in Starstream. Specifies target semantics for coordination scripts.

Key alignment points:
- `UTXOId`, `InterfaceId`, `Handler`, `Effect` come from `StarstreamPilot.lean`
- Roles are identified by `ProcessId` (aliased to `RoleId`)
- Scripts are event structures (partial order + conflict)
- Projection is defined by role participation
- Local actions erase global sender/receiver into in/out tags
- Enablement/configuration semantics follow standard event-structure rules
- All definitions are ASCII-only and intended to be Lean-friendly
-/

abbrev RoleId := ProcessId
abbrev EventId := Nat

/-! ## Role Kinds -/

inductive RoleKind where
  | utxo
  | iface
  | shard
  deriving DecidableEq, Repr

/-! ## Actions (global labels) -/

inductive Action where
  | raise     (from to : RoleId) (iface : InterfaceId) (tag : Nat)
  | resume    (from to : RoleId) (iface : InterfaceId) (tag : Nat)
  | install   (from to : RoleId) (h : Handler)
  | uninstall (from to : RoleId) (iface : InterfaceId)
  | read      (r : RoleId) (u : UTXOId)
  | consume   (r : RoleId) (u : UTXOId)
  | produce   (r : RoleId) (u : UTXOId)
  | lock      (r : RoleId) (u : UTXOId)
  | snapshot  (r : RoleId) (u : UTXOId)
  deriving DecidableEq, Repr

/-! ## Local Actions (projection labels) -/

inductive LocalAction where
  | inRaise    (from : RoleId) (iface : InterfaceId) (tag : Nat)
  | outRaise   (to   : RoleId) (iface : InterfaceId) (tag : Nat)
  | inResume   (from : RoleId) (iface : InterfaceId) (tag : Nat)
  | outResume  (to   : RoleId) (iface : InterfaceId) (tag : Nat)
  | inInstall  (from : RoleId) (h : Handler)
  | outInstall (to   : RoleId) (h : Handler)
  | inUninstall  (from : RoleId) (iface : InterfaceId)
  | outUninstall (to   : RoleId) (iface : InterfaceId)
  | localRead    (u : UTXOId)
  | localConsume (u : UTXOId)
  | localProduce (u : UTXOId)
  | localLock    (u : UTXOId)
  | localSnapshot (u : UTXOId)
  | silent
  deriving DecidableEq, Repr

/-! ## Participation and projection helpers -/

def Action.participants : Action → Finset RoleId
  | .raise from to _ _     => insert to (singleton from)
  | .resume from to _ _    => insert to (singleton from)
  | .install from to _     => insert to (singleton from)
  | .uninstall from to _   => insert to (singleton from)
  | .read r _              => singleton r
  | .consume r _           => singleton r
  | .produce r _           => singleton r
  | .lock r _              => singleton r
  | .snapshot r _          => singleton r

def Action.toLocal (r : RoleId) : Action → Option LocalAction
  | .raise from to iface tag =>
      if r = from then some (.outRaise to iface tag)
      else if r = to then some (.inRaise from iface tag)
      else none
  | .resume from to iface tag =>
      if r = from then some (.outResume to iface tag)
      else if r = to then some (.inResume from iface tag)
      else none
  | .install from to h =>
      if r = from then some (.outInstall to h)
      else if r = to then some (.inInstall from h)
      else none
  | .uninstall from to iface =>
      if r = from then some (.outUninstall to iface)
      else if r = to then some (.inUninstall from iface)
      else none
  | .read r' u =>
      if r = r' then some (.localRead u) else none
  | .consume r' u =>
      if r = r' then some (.localConsume u) else none
  | .produce r' u =>
      if r = r' then some (.localProduce u) else none
  | .lock r' u =>
      if r = r' then some (.localLock u) else none
  | .snapshot r' u =>
      if r = r' then some (.localSnapshot u) else none

/-! ## Global Script (event structure) -/

structure Script where
  roles    : Finset RoleId
  roleKind : RoleId → RoleKind
  events   : Finset EventId
  label    : EventId → Action
  order    : EventId → EventId → Prop
  conflict : EventId → EventId → Prop

def Script.relevant (s : Script) (r : RoleId) (e : EventId) : Bool :=
  (Action.toLocal r (s.label e)).isSome

/-! ## Well-formedness -/

def Script.orderDom (s : Script) : Prop :=
  ∀ e f, s.order e f → e ∈ s.events ∧ f ∈ s.events

def Script.conflictDom (s : Script) : Prop :=
  ∀ e f, s.conflict e f → e ∈ s.events ∧ f ∈ s.events

def Script.conflictIrrefl (s : Script) : Prop :=
  ∀ e ∈ s.events, ¬ s.conflict e e

def Script.conflictSymm (s : Script) : Prop :=
  ∀ e f, s.conflict e f → s.conflict f e

def Script.orderAcyclic (s : Script) : Prop :=
  ∀ e, ¬ Relation.TransGen s.order e e

def Script.rolesOK (s : Script) : Prop :=
  ∀ e ∈ s.events, Action.participants (s.label e) ⊆ s.roles

def Script.roleKindOK (s : Script) : Prop :=
  ∀ e ∈ s.events,
    match s.label e with
    | .read r _ | .consume r _ | .produce r _ | .lock r _ | .snapshot r _ =>
        s.roleKind r = RoleKind.utxo
    | _ => True

def Script.wellFormed (s : Script) : Prop :=
  s.orderDom ∧ s.conflictDom ∧ s.conflictIrrefl ∧ s.conflictSymm ∧ s.orderAcyclic ∧
  s.rolesOK ∧ s.roleKindOK

/-! ## Local Script -/

structure LocalScript where
  events   : Finset EventId
  label    : EventId → LocalAction
  order    : EventId → EventId → Prop
  conflict : EventId → EventId → Prop

def LocalScript.orderDom (s : LocalScript) : Prop :=
  ∀ e f, s.order e f → e ∈ s.events ∧ f ∈ s.events

def LocalScript.conflictDom (s : LocalScript) : Prop :=
  ∀ e f, s.conflict e f → e ∈ s.events ∧ f ∈ s.events

def LocalScript.conflictIrrefl (s : LocalScript) : Prop :=
  ∀ e ∈ s.events, ¬ s.conflict e e

def LocalScript.conflictSymm (s : LocalScript) : Prop :=
  ∀ e f, s.conflict e f → s.conflict f e

def LocalScript.orderAcyclic (s : LocalScript) : Prop :=
  ∀ e, ¬ Relation.TransGen s.order e e

def LocalScript.wellFormed (s : LocalScript) : Prop :=
  s.orderDom ∧ s.conflictDom ∧ s.conflictIrrefl ∧ s.conflictSymm ∧ s.orderAcyclic

/-! ## Event-structure semantics (global) -/

def Script.conflictFree (s : Script) (C : Finset EventId) : Prop :=
  ∀ e ∈ C, ∀ f ∈ C, ¬ s.conflict e f

def Script.downClosed (s : Script) (C : Finset EventId) : Prop :=
  ∀ e ∈ C, ∀ e', s.order e' e → e' ∈ C

def Script.isConfig (s : Script) (C : Finset EventId) : Prop :=
  C ⊆ s.events ∧ s.conflictFree C ∧ s.downClosed C

def Script.enabled (s : Script) (e : EventId) (C : Finset EventId) : Prop :=
  e ∈ s.events ∧ e ∉ C ∧
  (∀ e', s.order e' e → e' ∈ C) ∧
  (∀ f ∈ C, ¬ s.conflict e f)

def Script.step (s : Script) (C C' : Finset EventId) : Prop :=
  ∃ e, s.enabled e C ∧ C' = insert e C

def Script.validTraceAux (s : Script) (C : Finset EventId) : List EventId → Prop
  | []      => True
  | e :: es => s.enabled e C ∧ Script.validTraceAux s (insert e C) es

def Script.validTrace (s : Script) (tr : List EventId) : Prop :=
  Script.validTraceAux s ∅ tr

/-! ## Event-structure semantics (local) -/

def LocalScript.conflictFree (s : LocalScript) (C : Finset EventId) : Prop :=
  ∀ e ∈ C, ∀ f ∈ C, ¬ s.conflict e f

def LocalScript.downClosed (s : LocalScript) (C : Finset EventId) : Prop :=
  ∀ e ∈ C, ∀ e', s.order e' e → e' ∈ C

def LocalScript.isConfig (s : LocalScript) (C : Finset EventId) : Prop :=
  C ⊆ s.events ∧ s.conflictFree C ∧ s.downClosed C

def LocalScript.enabled (s : LocalScript) (e : EventId) (C : Finset EventId) : Prop :=
  e ∈ s.events ∧ e ∉ C ∧
  (∀ e', s.order e' e → e' ∈ C) ∧
  (∀ f ∈ C, ¬ s.conflict e f)

def LocalScript.step (s : LocalScript) (C C' : Finset EventId) : Prop :=
  ∃ e, s.enabled e C ∧ C' = insert e C

def LocalScript.validTraceAux (s : LocalScript) (C : Finset EventId) : List EventId → Prop
  | []      => True
  | e :: es => s.enabled e C ∧ LocalScript.validTraceAux s (insert e C) es

def LocalScript.validTrace (s : LocalScript) (tr : List EventId) : Prop :=
  LocalScript.validTraceAux s ∅ tr

/-! ## Projection -/

def Script.projEvents (s : Script) (r : RoleId) : Finset EventId :=
  s.events.filter (s.relevant r)

def Script.project (s : Script) (r : RoleId) : LocalScript :=
  let ev := s.projEvents r
  let lab : EventId → LocalAction :=
    fun e =>
      match Action.toLocal r (s.label e) with
      | some la => la
      | none    => LocalAction.silent
  let ord : EventId → EventId → Prop :=
    fun e f => s.order e f ∧ e ∈ ev ∧ f ∈ ev
  let conf : EventId → EventId → Prop :=
    fun e f => s.conflict e f ∧ e ∈ ev ∧ f ∈ ev
  { events := ev, label := lab, order := ord, conflict := conf }

/-! ## Conformance (global/local) and trace projection -/

def Script.traceProj (s : Script) (r : RoleId) (tr : List EventId) : List EventId :=
  tr.filter (s.relevant r)

def Script.globalConform (s : Script) (tr : List EventId) : Prop :=
  s.wellFormed ∧ Script.validTrace s tr

def Script.localConform (s : Script) (r : RoleId) (tr : List EventId) : Prop :=
  (s.project r).wellFormed ∧ LocalScript.validTrace (s.project r) tr

/-! ## Witness-level trace consistency -/

def Before (tr : List EventId) (a b : EventId) : Prop :=
  ∃ l1 l2, tr = l1 ++ a :: l2 ∧ b ∈ l2

def Script.traceConsistentAux (s : Script) (C : Finset EventId) (tr : List EventId) : Prop :=
  tr.Nodup ∧
  (∀ e, e ∈ tr → e ∈ s.events) ∧
  (∀ e, e ∈ tr → e ∉ C) ∧
  (∀ e, e ∈ tr → ∀ f, f ∈ C → ¬ s.conflict e f) ∧
  tr.Pairwise (fun a b => ¬ s.conflict a b ∧ ¬ s.conflict b a) ∧
  (∀ e' e, s.order e' e → e ∈ tr → e' ∈ C ∨ Before tr e' e)

def Script.traceConsistent (s : Script) (tr : List EventId) : Prop :=
  Script.traceConsistentAux s ∅ tr

lemma mem_left_of_before {tr : List EventId} {a b : EventId}
    (h : Before tr a b) : a ∈ tr := by
  rcases h with ⟨l1, l2, h, _⟩
  subst h
  simp

lemma mem_right_of_before {tr : List EventId} {a b : EventId}
    (h : Before tr a b) : b ∈ tr := by
  rcases h with ⟨l1, l2, h, hb⟩
  subst h
  simp [hb]

lemma before_cons_of_tail {e : EventId} {es : List EventId} {a b : EventId}
    (h : Before es a b) : Before (e :: es) a b := by
  rcases h with ⟨l1, l2, h, hb⟩
  refine ⟨e :: l1, l2, ?_, hb⟩
  simp [h, List.append_assoc]

lemma before_cons_tail {e : EventId} {es : List EventId} {a b : EventId}
    (h : Before (e :: es) a b) (hne : a ≠ e) : Before es a b := by
  rcases h with ⟨l1, l2, h, hb⟩
  cases l1 with
  | nil =>
      -- then a = e, contradiction
      simp at h
      have h1 : e = a := by
        injection h with h1
        exact h1
      exact (hne h1.symm).elim
  | cons x xs =>
      -- l1 = e :: xs, so es = xs ++ a :: l2
      have h' : e :: es = x :: (xs ++ a :: l2) := by
        simpa [List.append_assoc] using h
      have h1 : e = x := by
        injection h' with h1
        exact h1
      have h2 : es = xs ++ a :: l2 := by
        injection h' with _ h2
        exact h2
      refine ⟨xs, l2, h2, hb⟩

lemma mem_tail_of_before_head {e : EventId} {es : List EventId} {b : EventId} :
    Before (e :: es) e b → b ∈ es := by
  intro h
  rcases h with ⟨l1, l2, h, hb⟩
  cases l1 with
  | nil =>
      simp at h
      have h2 : es = l2 := by
        injection h with _ h2
        exact h2
      simpa [h2] using hb
  | cons x xs =>
      have h' : e :: es = x :: (xs ++ e :: l2) := by
        simpa [List.append_assoc] using h
      have h2 : es = xs ++ e :: l2 := by
        injection h' with _ h2
        exact h2
      have : b ∈ xs ++ e :: l2 := by
        simpa [h2] using hb
      simpa [h2] using this

/-! ## Cross-role consistency and reconstruction -/

def Script.shareRole (s : Script) (e f : EventId) : Prop :=
  (Action.participants (s.label e) ∩ Action.participants (s.label f)).Nonempty

def Script.disjointRoles (s : Script) (e f : EventId) : Prop :=
  Disjoint (Action.participants (s.label e)) (Action.participants (s.label f))

def Script.crossRoleConsistent (s : Script) (tr : List EventId) : Prop :=
  (∀ e f, e ∈ tr → f ∈ tr → s.disjointRoles e f →
      (¬ s.conflict e f ∧ ¬ s.conflict f e)) ∧
  (∀ e' e, s.disjointRoles e' e → s.order e' e → e ∈ tr → Before tr e' e)

lemma shareRole_exists {s : Script} {e f : EventId}
    (h : s.shareRole e f) :
    ∃ r, r ∈ Action.participants (s.label e) ∧
         r ∈ Action.participants (s.label f) := by
  rcases h with ⟨r, hr⟩
  rcases Finset.mem_inter.mp hr with ⟨hre, hrf⟩
  exact ⟨r, hre, hrf⟩

lemma relevant_of_participant {s : Script} {r : RoleId} {e : EventId}
    (hr : r ∈ Action.participants (s.label e)) :
    s.relevant r e = true := by
  cases h : s.label e with
  | raise from to iface tag =>
      simp [Script.relevant, Action.toLocal, Action.participants, h] at hr ⊢
      rcases hr with hr | hr
      · simp [hr]
      · simp [hr]
  | resume from to iface tag =>
      simp [Script.relevant, Action.toLocal, Action.participants, h] at hr ⊢
      rcases hr with hr | hr
      · simp [hr]
      · simp [hr]
  | install from to hnd =>
      simp [Script.relevant, Action.toLocal, Action.participants, h] at hr ⊢
      rcases hr with hr | hr
      · simp [hr]
      · simp [hr]
  | uninstall from to iface =>
      simp [Script.relevant, Action.toLocal, Action.participants, h] at hr ⊢
      rcases hr with hr | hr
      · simp [hr]
      · simp [hr]
  | read r' u =>
      simp [Script.relevant, Action.toLocal, Action.participants, h] at hr ⊢
      simpa using hr
  | consume r' u =>
      simp [Script.relevant, Action.toLocal, Action.participants, h] at hr ⊢
      simpa using hr
  | produce r' u =>
      simp [Script.relevant, Action.toLocal, Action.participants, h] at hr ⊢
      simpa using hr
  | lock r' u =>
      simp [Script.relevant, Action.toLocal, Action.participants, h] at hr ⊢
      simpa using hr
  | snapshot r' u =>
      simp [Script.relevant, Action.toLocal, Action.participants, h] at hr ⊢
      simpa using hr

lemma mem_traceProj_of_relevant {s : Script} {r : RoleId} {tr : List EventId} {e : EventId}
    (hre : s.relevant r e = true) (he : e ∈ tr) :
    e ∈ s.traceProj r tr := by
  simp [Script.traceProj, List.mem_filter, he, hre]

lemma before_head {e : EventId} {es : List EventId} {x : EventId}
    (hx : x ∈ es) : Before (e :: es) e x := by
  refine ⟨[], es, ?_, hx⟩
  simp

lemma LocalScript.validTraceAux_order (s : LocalScript) :
    ∀ (C : Finset EventId) (tr : List EventId),
      LocalScript.validTraceAux s C tr →
      ∀ e' e, s.order e' e → e ∈ tr → e' ∈ C ∨ Before tr e' e
  | C, [], _ => by
      intro e' e _ he; cases he
  | C, (e :: es), h => by
      rcases h with ⟨hen, htail⟩
      intro e' x hord hx
      cases hx with
      | head =>
          -- x = e, predecessors must be in C
          have : ∀ e', s.order e' e → e' ∈ C := hen.2.2.1
          exact Or.inl (this _ hord)
      | tail hx' =>
          have ih := LocalScript.validTraceAux_order s (insert e C) es htail
          have hcase := ih e' x hord hx'
          rcases hcase with hC | hbefore
          · rcases hC with hC | hC
            · exact Or.inl hC
            · -- e' = e, so e' before x
              have : Before (e :: es) e x := before_head hx'
              exact Or.inr this
          · exact Or.inr (before_cons_of_tail hbefore)

lemma before_of_filter {p : EventId → Bool} {tr : List EventId} {a b : EventId}
    (hnd : tr.Nodup) (ha : p a = true) (hb : p b = true) :
    Before (tr.filter p) a b → Before tr a b := by
  induction tr with
  | nil => intro h; cases h with | _ l1 l2 h hb => cases h
  | cons x xs ih =>
      intro h
      by_cases hx : p x = true
      · have hnd' : xs.Nodup := by simpa using (List.nodup_cons.mp hnd).2
        -- filter = x :: filter xs
        have hf : (x :: xs).filter p = x :: xs.filter p := by
          simp [hx]
        by_cases hax : a = x
        · subst hax
          -- a is head; b must be in filtered tail
          rcases h with ⟨l1, l2, h, hbmem⟩
          -- nodup ensures a appears only at head
          have : b ∈ xs := by
            have : b ∈ xs.filter p := by
              -- b is in l2 which is a suffix of filtered list
              -- use membership in filtered tail
              have : b ∈ (x :: xs).filter p := by
                simpa [hf] using hbmem
              simpa [hx] using this
            exact (List.mem_filter.mp this).1
          exact ⟨[], xs, by simp, this⟩
        · -- a in tail filter
          have h' : Before (xs.filter p) a b := by
            rcases h with ⟨l1, l2, h, hbmem⟩
            cases l1 with
            | nil =>
                simp at h
                exact (hax (by injection h with h1; exact h1)).elim
            | cons y ys =>
                -- strip head
                have : xs.filter p = ys ++ a :: l2 := by
                  simpa [hf, List.append_assoc] using h
                exact ⟨ys, l2, this, hbmem⟩
          exact before_cons_of_tail (ih hnd' ha hb h')
      · -- head filtered out
        have hnd' : xs.Nodup := by simpa using (List.nodup_cons.mp hnd).2
        have hf : (x :: xs).filter p = xs.filter p := by
          simp [hx]
        have h' : Before (xs.filter p) a b := by
          simpa [hf] using h
        exact before_cons_of_tail (ih hnd' ha hb h')

lemma before_filter_of_before {p : EventId → Bool} {tr : List EventId} {a b : EventId}
    (ha : p a = true) (hb : p b = true) :
    Before tr a b → Before (tr.filter p) a b := by
  induction tr with
  | nil =>
      intro h
      cases h with
      | _ l1 l2 h _ => cases h
  | cons x xs ih =>
      intro h
      by_cases hx : p x = true
      · by_cases hax : a = x
        · subst hax
          have hbmem : b ∈ xs := mem_tail_of_before_head h
          refine ⟨[], xs.filter p, ?_, ?_⟩
          · simp [hx]
          · exact List.mem_filter.mpr ⟨hbmem, hb⟩
        · have h' : Before xs a b := before_cons_tail h hax
          have ih' := ih h'
          have : Before (x :: xs.filter p) a b := before_cons_of_tail ih'
          simpa [hx] using this
      · have hax : a ≠ x := by
          intro hax
          subst hax
          simpa [hx] using ha
        have h' : Before xs a b := before_cons_tail h hax
        have ih' := ih h'
        simpa [hx] using ih'

lemma LocalScript.validTraceAux_events (s : LocalScript) :
    ∀ (C : Finset EventId) (tr : List EventId),
      LocalScript.validTraceAux s C tr →
      ∀ e ∈ tr, e ∈ s.events
  | C, [], _ => by
      intro e he
      cases he
  | C, (e :: es), h => by
      rcases h with ⟨hen, htail⟩
      intro x hx
      cases hx with
      | head => exact hen.1
      | tail hx' =>
          exact LocalScript.validTraceAux_events s (insert e C) es htail x hx'

lemma LocalScript.validTraceAux_no_conflict_with_C (s : LocalScript) :
    ∀ (C : Finset EventId) (tr : List EventId),
      LocalScript.validTraceAux s C tr →
      ∀ x ∈ tr, ∀ f ∈ C, ¬ s.conflict x f
  | C, [], _ => by
      intro x hx
      cases hx
  | C, (e :: es), h => by
      rcases h with ⟨hen, htail⟩
      intro x hx f hf
      cases hx with
      | head =>
          exact hen.2.2.2 f hf
      | tail hx' =>
          have ih :=
            LocalScript.validTraceAux_no_conflict_with_C s (insert e C) es htail x hx' f
              (by simp [hf])
          exact ih

lemma LocalScript.validTraceAux_no_conflict_before (s : LocalScript) :
    ∀ (C : Finset EventId) (tr : List EventId),
      LocalScript.validTraceAux s C tr →
      ∀ a b, Before tr a b → ¬ s.conflict b a
  | C, [], _ => by
      intro a b h
      cases h with
      | _ l1 l2 h _ => cases h
  | C, (e :: es), h => by
      rcases h with ⟨hen, htail⟩
      intro a b hbefore
      by_cases hax : a = e
      · subst hax
        have hb : b ∈ es := mem_tail_of_before_head hbefore
        have hnoc :=
          LocalScript.validTraceAux_no_conflict_with_C s (insert e C) es htail b hb e
            (by simp)
        simpa using hnoc
      · have hbefore' : Before es a b := before_cons_tail hbefore hax
        have ih :=
          LocalScript.validTraceAux_no_conflict_before s (insert e C) es htail a b hbefore'
        exact ih

lemma local_no_conflict_before {s : Script} {r : RoleId} {tr : List EventId}
    (hlocal : Script.localConform s r (s.traceProj r tr)) :
    ∀ a b, Before (s.traceProj r tr) a b → ¬ s.conflict b a := by
  rcases hlocal with ⟨_hwf, htrace⟩
  have htrace' : LocalScript.validTraceAux (s.project r) ∅ (s.traceProj r tr) := by
    simpa [LocalScript.validTrace] using htrace
  intro a b hbefore
  have hloc : ¬ (s.project r).conflict b a :=
    LocalScript.validTraceAux_no_conflict_before (s.project r) ∅ (s.traceProj r tr) htrace' a b hbefore
  intro hcf
  have ha : a ∈ (s.project r).events := by
    have ha' : a ∈ s.traceProj r tr := mem_left_of_before hbefore
    exact LocalScript.validTraceAux_events (s.project r) ∅ (s.traceProj r tr) htrace' a ha'
  have hb : b ∈ (s.project r).events := by
    have hb' : b ∈ s.traceProj r tr := mem_right_of_before hbefore
    exact LocalScript.validTraceAux_events (s.project r) ∅ (s.traceProj r tr) htrace' b hb'
  exact hloc ⟨hcf, hb, ha⟩

lemma local_validTrace_order_before {s : Script} {r : RoleId} {tr : List EventId}
    (hwf : s.wellFormed)
    (hlocal : Script.localConform s r (s.traceProj r tr))
    (hnd : tr.Nodup)
    {e' e : EventId}
    (hre' : s.relevant r e' = true) (hre : s.relevant r e = true)
    (hord : s.order e' e) (he : e ∈ tr) :
    Before tr e' e := by
  rcases hwf with ⟨hordDom, _hconfDom, _hconfIrr, _hconfSymm, _hacyc, _hroles, _hkind⟩
  rcases hlocal with ⟨_hwf, htrace⟩
  have hproj : LocalScript.validTraceAux (s.project r) ∅ (s.traceProj r tr) := by
    simpa [LocalScript.validTrace] using htrace
  have horder : (s.project r).order e' e := by
    have he'ev : e' ∈ (s.project r).events := by
      have he'events : e' ∈ s.events := (hordDom _ _ hord).1
      simp [Script.project, Script.projEvents, Script.relevant, hre', he'events, Finset.mem_filter]
    have heev : e ∈ (s.project r).events := by
      have hevents : e ∈ s.events := (hordDom _ _ hord).2
      simp [Script.project, Script.projEvents, Script.relevant, hre, hevents, Finset.mem_filter]
    exact ⟨hord, he'ev, heev⟩
  have heproj : e ∈ s.traceProj r tr := mem_traceProj_of_relevant hre he
  have hbefore_proj :
      Before (s.traceProj r tr) e' e := by
    have haux := LocalScript.validTraceAux_order (s.project r) ∅ (s.traceProj r tr) hproj
    have hcase := haux e' e horder heproj
    rcases hcase with hC | hB
    · cases hC
    · exact hB
  exact before_of_filter hnd hre' hre hbefore_proj

lemma Script.traceConsistent_of_local_and_cross (s : Script) (tr : List EventId)
    (hwf : s.wellFormed)
    (hnd : tr.Nodup)
    (hevents : ∀ e, e ∈ tr → e ∈ s.events)
    (hlocal : ∀ r ∈ s.roles, Script.localConform s r (s.traceProj r tr))
    (hcross : s.crossRoleConsistent tr) :
    s.traceConsistent tr := by
  classical
  rcases hwf with ⟨hordDom, _hconfDom, _hconfIrr, hconfSymm, _hacyc, hroles, _hkind⟩
  rcases hcross with ⟨hcross_conflict, hcross_order⟩
  refine ⟨hnd, hevents, ?_, ?_, ?_, ?_⟩
  · intro e he; intro hc; exact hc
  · intro e he f hf; cases hf
  · -- pairwise conflict-free: disjoint via cross-role, shared via local traces
    induction tr with
    | nil => exact List.Pairwise.nil
    | cons a xs ih =>
        have hhead : ∀ b ∈ xs, ¬ s.conflict a b ∧ ¬ s.conflict b a := by
          intro b hb
          by_cases hdisj : s.disjointRoles a b
          · exact hcross_conflict a b (by simp) (by simpa using hb) hdisj
          · -- shared role
            have hshare : s.shareRole a b := by
              by_cases hne :
                  (Action.participants (s.label a) ∩ Action.participants (s.label b)).Nonempty
              · exact hne
              · have hdisj' : s.disjointRoles a b := by
                  refine Finset.disjoint_left.mpr ?_
                  intro r hra hrb
                  have : r ∈ (Action.participants (s.label a) ∩ Action.participants (s.label b)) :=
                    Finset.mem_inter.mpr ⟨hra, hrb⟩
                  exact (hne ⟨r, this⟩).elim
                exact (hdisj hdisj').elim
            rcases shareRole_exists (s := s) hshare with ⟨r, hra, hrb⟩
            have hra' : s.relevant r a = true := relevant_of_participant (s := s) hra
            have hrb' : s.relevant r b = true := relevant_of_participant (s := s) hrb
            have hr : r ∈ s.roles := by
              have hsub : Action.participants (s.label a) ⊆ s.roles :=
                hroles a (hevents a (by simp))
              exact hsub hra
            have hloc := hlocal r hr
            have hbefore_global : Before (a :: xs) a b := before_head hb
            have hbefore_proj : Before (s.traceProj r (a :: xs)) a b :=
              before_filter_of_before hra' hrb' hbefore_global
            have hnb : ¬ s.conflict b a :=
              local_no_conflict_before (s := s) (r := r) (tr := a :: xs) hloc a b hbefore_proj
            have hna : ¬ s.conflict a b := by
              intro hcf
              exact hnb (hconfSymm _ _ hcf)
            exact ⟨hna, hnb⟩
        refine List.pairwise_cons.2 ?_
        exact ⟨hhead, ih⟩
  · -- order consistency: disjoint via cross-role, shared via local traces
    intro e' e hord he
    by_cases hdisj : s.disjointRoles e' e
    · exact hcross_order e' e hdisj hord he
    · have hshare : s.shareRole e' e := by
        by_cases hne :
            (Action.participants (s.label e') ∩ Action.participants (s.label e)).Nonempty
        · exact hne
        · have hdisj' : s.disjointRoles e' e := by
            refine Finset.disjoint_left.mpr ?_
            intro r hre' hre
            have : r ∈ (Action.participants (s.label e') ∩ Action.participants (s.label e)) :=
              Finset.mem_inter.mpr ⟨hre', hre⟩
            exact (hne ⟨r, this⟩).elim
          exact (hdisj hdisj').elim
      rcases shareRole_exists (s := s) hshare with ⟨r, hre', hre⟩
      have hre' : s.relevant r e' = true := relevant_of_participant (s := s) hre'
      have hre : s.relevant r e = true := relevant_of_participant (s := s) hre
      have hr : r ∈ s.roles := by
        have hsub : Action.participants (s.label e) ⊆ s.roles :=
          hroles e (hevents e he)
        exact hsub hre
      have hloc := hlocal r hr
      exact local_validTrace_order_before (s := s) (r := r) (tr := tr)
        hwf hloc hnd hre' hre hord he

lemma before_head_false {e : EventId} {es : List EventId} {a : EventId}
    (hnd : (e :: es).Nodup) : ¬ Before (e :: es) a e := by
  intro h
  rcases h with ⟨l1, l2, h, hb⟩
  -- show e ∈ es, contradicting nodup
  have : e ∈ es := by
    cases l1 with
    | nil =>
        -- e :: es = a :: l2, so es = l2 and e ∈ l2
        simp at h
        have h2 : es = l2 := by
          injection h with _ h2
          exact h2
        simpa [h2] using hb
    | cons x xs =>
        -- e :: es = (x :: xs) ++ a :: l2, so es = xs ++ a :: l2
        have h' : e :: es = x :: (xs ++ a :: l2) := by
          simpa [List.append_assoc] using h
        have h2 : es = xs ++ a :: l2 := by
          injection h' with _ h2
          exact h2
        have : e ∈ xs ++ a :: l2 := by
          simpa [h2] using hb
        simpa [h2] using this
  have hne : e ∉ es := (List.nodup_cons.mp hnd).1
  exact (hne this)

lemma traceConsistentAux_validTraceAux (s : Script) :
    ∀ (C : Finset EventId) (tr : List EventId),
      s.traceConsistentAux C tr →
      Script.validTraceAux s C tr
  | C, [], _ => by
      simp [Script.validTraceAux]
  | C, (e :: es), h => by
      rcases h with ⟨hnd, hevents, hfresh, hconfC, hpair, horder⟩
      have he : e ∈ s.events := hevents e (by simp)
      have hnotin : e ∉ C := hfresh e (by simp)
      have hpreds : ∀ e', s.order e' e → e' ∈ C := by
        intro e' hord
        have hcase := horder e' e hord (by simp)
        rcases hcase with hC | hbefore
        · exact hC
        · have : False := before_head_false hnd hbefore
          exact (False.elim this)
      have hconf : ∀ f ∈ C, ¬ s.conflict e f := by
        intro f hf; exact hconfC e (by simp) f hf
      have hen : s.enabled e C := by
        exact ⟨he, hnotin, hpreds, hconf⟩
      -- Build consistency for tail with updated C
      have hnd' : es.Nodup := by
        simpa using (List.nodup_cons.mp hnd).2
      have hevents' : ∀ x, x ∈ es → x ∈ s.events := by
        intro x hx; exact hevents x (by simp [hx])
      have hfresh' : ∀ x, x ∈ es → x ∉ insert e C := by
        intro x hx
        have hne : e ∉ es := (List.nodup_cons.mp hnd).1
        have hxne : x ≠ e := by
          intro hxe; subst hxe; exact hne hx
        intro hxC
        have hxC' : x = e ∨ x ∈ C := by
          simpa using hxC
        rcases hxC' with rfl | hC
        · exact (hxne rfl).elim
        · exact (hfresh x (by simp [hx]) hC)
      have hconfC' : ∀ x, x ∈ es → ∀ f, f ∈ insert e C → ¬ s.conflict x f := by
        intro x hx f hf
        have hf' : f = e ∨ f ∈ C := by
          simpa using hf
        rcases hf' with rfl | hC
        · -- conflict with head: use Pairwise
          have hp : ∀ y ∈ es, ¬ s.conflict y e := by
            have : List.Pairwise (fun a b => ¬ s.conflict a b ∧ ¬ s.conflict b a) (e :: es) := hpair
            have hhead := (List.pairwise_cons.mp this).1
            intro y hy
            have := hhead y hy
            exact this.2
          exact hp x hx
        · exact hconfC x (by simp [hx]) f hC
      have hpair' : es.Pairwise (fun a b => ¬ s.conflict a b ∧ ¬ s.conflict b a) := by
        simpa using (List.pairwise_cons.mp hpair).2
      have horder' : ∀ e' x, s.order e' x → x ∈ es → e' ∈ insert e C ∨ Before es e' x := by
        intro e' x hord hx
        have hcase := horder e' x hord (by simp [hx])
        rcases hcase with hC | hbefore
        · exact Or.inl (by simp [hC])
        · by_cases hne : e' = e
          · exact Or.inl (by simp [hne])
          · exact Or.inr (before_cons_tail hbefore hne)
      have htail : s.traceConsistentAux (insert e C) es :=
        ⟨hnd', hevents', hfresh', hconfC', hpair', horder'⟩
      exact ⟨hen, traceConsistentAux_validTraceAux s (insert e C) es htail⟩

theorem traceConsistent_implies_validTrace (s : Script) (tr : List EventId)
    (h : s.traceConsistent tr) : Script.validTrace s tr :=
  traceConsistentAux_validTraceAux s ∅ tr h

theorem globalConform_of_consistent (s : Script) (tr : List EventId)
    (hwf : s.wellFormed) (h : s.traceConsistent tr) : s.globalConform tr := by
  exact ⟨hwf, traceConsistent_implies_validTrace s tr h⟩

/-! ## Projection lemmas (core) -/

lemma filter_insert_false {p : EventId → Bool} {C : Finset EventId} {e : EventId}
    (h : p e = false) :
    (insert e C).filter p = C.filter p := by
  ext x
  simp [Finset.mem_filter, h]

lemma proj_validTraceAux (s : Script) (r : RoleId) :
    ∀ (C : Finset EventId) (tr : List EventId),
      Script.validTraceAux s C tr →
      LocalScript.validTraceAux (s.project r) (C.filter (s.relevant r))
        (tr.filter (s.relevant r))
  | C, [], _ => by
      simp [LocalScript.validTraceAux]
  | C, (e :: es), h => by
      have h1 : s.enabled e C := h.1
      have h2 : Script.validTraceAux s (insert e C) es := h.2
      by_cases hre : s.relevant r e = true
      · -- event is relevant: must be enabled in local projection
        have hevent : e ∈ (s.project r).events := by
          -- e ∈ events and relevant => e ∈ filtered events
          simp [Script.project, Script.projEvents, Script.relevant, hre,
            Finset.mem_filter, h1.1]
        have hnotin : e ∉ C.filter (s.relevant r) := by
          intro hc
          have : e ∈ C := (Finset.mem_filter.mp hc).1
          exact h1.2.1 this
        have hpreds : ∀ e', (s.project r).order e' e → e' ∈ C.filter (s.relevant r) := by
          intro e' horder
          rcases horder with ⟨hord, he', _⟩
          have he'c : e' ∈ C := h1.2.2.1 _ hord
          exact (Finset.mem_filter.mpr ⟨he'c, (Finset.mem_filter.mp he').2⟩)
        have hconf : ∀ f ∈ C.filter (s.relevant r), ¬ (s.project r).conflict e f := by
          intro f hf
          rcases Finset.mem_filter.mp hf with ⟨hfC, _⟩
          intro hcf
          exact (h1.2.2.2 f hfC) hcf.1
        have hen : (s.project r).enabled e (C.filter (s.relevant r)) := by
          exact ⟨hevent, hnotin, hpreds, hconf⟩
        -- proceed with local trace
        have ih := proj_validTraceAux s r (insert e C) es h2
        -- simplify filtered list and context
        have hctx : (insert e C).filter (s.relevant r) = insert e (C.filter (s.relevant r)) := by
          ext x
          by_cases hx : x = e
          · subst hx
            simp [Finset.mem_filter, hre, h1.2.1]
          · simp [Finset.mem_filter, hx, hre]
        -- local trace uses e :: filtered tail
        simp [LocalScript.validTraceAux, Script.traceProj, hre, hctx, hen, ih]
      · -- event is irrelevant: drop it from local trace
        have ih := proj_validTraceAux s r (insert e C) es h2
        have hctx : (insert e C).filter (s.relevant r) = C.filter (s.relevant r) :=
          filter_insert_false (C := C) (e := e) (p := s.relevant r) (by simpa using hre)
        -- filter drops e
        simp [Script.traceProj, hre, LocalScript.validTraceAux, hctx] at ih
        simpa [Script.traceProj, hre, LocalScript.validTraceAux, hctx] using ih

theorem proj_validTrace (s : Script) (r : RoleId) (tr : List EventId)
    (h : Script.validTrace s tr) :
    LocalScript.validTrace (s.project r) (s.traceProj r tr) := by
  simpa [Script.traceProj] using (proj_validTraceAux s r ∅ tr h)

theorem project_wellFormed (s : Script) (r : RoleId) (h : s.wellFormed) :
    (s.project r).wellFormed := by
  rcases h with ⟨hord, hconf, hirr, hsymm, hacyc, _hroles, _hkind⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e f horder
    rcases horder with ⟨hord', he, hf⟩
    have he' : e ∈ s.events := (Finset.mem_filter.mp he).1
    have hf' : f ∈ s.events := (Finset.mem_filter.mp hf).1
    exact ⟨he, hf⟩
  · intro e f hcf
    rcases hcf with ⟨hcf', he, hf⟩
    exact ⟨he, hf⟩
  · intro e he
    have he' : e ∈ s.events := (Finset.mem_filter.mp he).1
    intro hcf
    exact hirr e he' hcf.1
  · intro e f hcf
    rcases hcf with ⟨hcf', he, hf⟩
    exact ⟨hsymm _ _ hcf', hf, he⟩
  · intro e hcycle
    apply hacyc e
    exact Relation.TransGen.mono (fun a b hrel => hrel.1) hcycle

theorem proj_localConform_of_globalConform (s : Script) (r : RoleId) (tr : List EventId)
    (h : s.globalConform tr) :
    s.localConform r (s.traceProj r tr) := by
  rcases h with ⟨hwf, htr⟩
  refine ⟨project_wellFormed s r hwf, ?_⟩
  exact proj_validTrace s r tr htr

end Starstream
