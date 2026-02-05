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
  | raise     (src dst : RoleId) (iface : InterfaceId) (tag : Nat)
  | resume    (src dst : RoleId) (iface : InterfaceId) (tag : Nat)
  | install   (src dst : RoleId) (h : Handler)
  | uninstall (src dst : RoleId) (iface : InterfaceId)
  | read      (r : RoleId) (u : UTXOId)
  | consume   (r : RoleId) (u : UTXOId)
  | produce   (r : RoleId) (u : UTXOId)
  | lock      (r : RoleId) (u : UTXOId)
  | snapshot  (r : RoleId) (u : UTXOId)
  deriving DecidableEq

/-! ## Local Actions (projection labels) -/

inductive LocalAction where
  | inRaise    (src : RoleId) (iface : InterfaceId) (tag : Nat)
  | outRaise   (dst : RoleId) (iface : InterfaceId) (tag : Nat)
  | inResume   (src : RoleId) (iface : InterfaceId) (tag : Nat)
  | outResume  (dst : RoleId) (iface : InterfaceId) (tag : Nat)
  | inInstall  (src : RoleId) (h : Handler)
  | outInstall (dst : RoleId) (h : Handler)
  | inUninstall  (src : RoleId) (iface : InterfaceId)
  | outUninstall (dst : RoleId) (iface : InterfaceId)
  | localRead    (u : UTXOId)
  | localConsume (u : UTXOId)
  | localProduce (u : UTXOId)
  | localLock    (u : UTXOId)
  | localSnapshot (u : UTXOId)
  | silent
  deriving DecidableEq

/-! ## Participation and projection helpers -/

def Action.participants : Action → Finset RoleId
  | .raise src dst _ _     => insert dst (singleton src)
  | .resume src dst _ _    => insert dst (singleton src)
  | .install src dst _     => insert dst (singleton src)
  | .uninstall src dst _   => insert dst (singleton src)
  | .read r _              => singleton r
  | .consume r _           => singleton r
  | .produce r _           => singleton r
  | .lock r _              => singleton r
  | .snapshot r _          => singleton r

def Action.toLocal (r : RoleId) : Action → Option LocalAction
  | .raise src dst iface tag =>
      if r = src then some (.outRaise dst iface tag)
      else if r = dst then some (.inRaise src iface tag)
      else none
  | .resume src dst iface tag =>
      if r = src then some (.outResume dst iface tag)
      else if r = dst then some (.inResume src iface tag)
      else none
  | .install src dst h =>
      if r = src then some (.outInstall dst h)
      else if r = dst then some (.inInstall src h)
      else none
  | .uninstall src dst iface =>
      if r = src then some (.outUninstall dst iface)
      else if r = dst then some (.inUninstall src iface)
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
  s.events.filter (fun e => s.relevant r e = true)

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
  rcases h with ⟨l1, l2, heq, hb⟩
  cases l1 with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq
      exact (hne heq.1.symm).elim
  | cons x xs =>
      simp only [List.cons_append, List.cons.injEq] at heq
      refine ⟨xs, l2, heq.2, hb⟩

lemma mem_tail_of_before_head {e : EventId} {es : List EventId} {b : EventId} :
    Before (e :: es) e b → b ∈ es := by
  intro h
  rcases h with ⟨l1, l2, heq, hb⟩
  cases l1 with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq
      simp [heq.2, hb]
  | cons x xs =>
      simp only [List.cons_append, List.cons.injEq] at heq
      simp [heq.2, hb]

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
  unfold Script.relevant
  cases h : s.label e with
  | raise src dst iface tag =>
      rw [h, Action.participants] at hr
      simp only [mem_insert, mem_singleton] at hr
      simp only [Action.toLocal, h]
      rcases hr with h1 | h2
      · subst h1; by_cases hc : r = src <;> simp [hc]
      · subst h2; simp
  | resume src dst iface tag =>
      rw [h, Action.participants] at hr
      simp only [mem_insert, mem_singleton] at hr
      simp only [Action.toLocal, h]
      rcases hr with h1 | h2
      · subst h1; by_cases hc : r = src <;> simp [hc]
      · subst h2; simp
  | install src dst hand =>
      rw [h, Action.participants] at hr
      simp only [mem_insert, mem_singleton] at hr
      simp only [Action.toLocal, h]
      rcases hr with h1 | h2
      · subst h1; by_cases hc : r = src <;> simp [hc]
      · subst h2; simp
  | uninstall src dst iface =>
      rw [h, Action.participants] at hr
      simp only [mem_insert, mem_singleton] at hr
      simp only [Action.toLocal, h]
      rcases hr with h1 | h2
      · subst h1; by_cases hc : r = src <;> simp [hc]
      · subst h2; simp
  | read r' u =>
      rw [h, Action.participants] at hr
      simp only [mem_singleton] at hr
      simp [Action.toLocal, h, hr]
  | consume r' u =>
      rw [h, Action.participants] at hr
      simp only [mem_singleton] at hr
      simp [Action.toLocal, h, hr]
  | produce r' u =>
      rw [h, Action.participants] at hr
      simp only [mem_singleton] at hr
      simp [Action.toLocal, h, hr]
  | lock r' u =>
      rw [h, Action.participants] at hr
      simp only [mem_singleton] at hr
      simp [Action.toLocal, h, hr]
  | snapshot r' u =>
      rw [h, Action.participants] at hr
      simp only [mem_singleton] at hr
      simp [Action.toLocal, h, hr]

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
  | C, (e :: es), h => fun e' x hord hx => by
      rcases h with ⟨hen, htail⟩
      cases hx with
      | head => -- x = e case
          have : ∀ e', s.order e' e → e' ∈ C := hen.2.2.1
          exact Or.inl (this _ hord)
      | @tail _ _ hxes => -- hxes : x ∈ es
          have ih := LocalScript.validTraceAux_order s (insert e C) es htail
          have hcase := ih e' x hord hxes
          rcases hcase with hC | hbefore
          · simp only [Finset.mem_insert] at hC
            rcases hC with rfl | hC
            · exact Or.inr (before_head hxes)
            · exact Or.inl hC
          · exact Or.inr (before_cons_of_tail hbefore)

/-- Filtering a list preserves the `Before` relation (lifting direction).

If `a` appears before `b` in the filtered list `tr.filter p`, then `a` also appears
before `b` in the original list `tr`. This is the "information lifting" direction:
properties of the filtered list imply properties of the original.

The converse is `before_filter_of_before`.

**Proof strategy:** Induction on the list with nested case analysis:
- Base case: trivial since both filtered and unfiltered empty lists are identical
- Inductive case: case split on whether the head passes the filter predicate,
  then on whether `a` equals the head -/
lemma before_of_filter {p : EventId → Bool} {tr : List EventId} {a b : EventId}
    (hnd : tr.Nodup) (ha : p a = true) (hb : p b = true) :
    Before (tr.filter p) a b → Before tr a b := by
  intro h
  induction tr with
  | nil =>
      -- Both [].filter p and [] are empty, so the hypothesis equals the goal
      exact h
  | cons x xs ih =>
      by_cases hpx : p x = true
      · -- Case: p x = true, so filter keeps x
        -- (x :: xs).filter p = x :: xs.filter p
        simp only [List.filter, hpx] at h
        by_cases hax : a = x
        · -- Subcase: a = x (a is the head of the filtered list)
          subst hax
          -- h : Before (x :: xs.filter p) x b, so b is in the filtered tail
          have hbmem : b ∈ xs.filter p := mem_tail_of_before_head h
          -- Membership in filtered list implies membership in original
          have hbxs : b ∈ xs := List.mem_of_mem_filter hbmem
          -- Construct Before (x :: xs) x b directly
          exact before_head hbxs
        · -- Subcase: a ≠ x (a appears later in the list)
          -- Strip the head to get Before in the filtered tail
          have h' : Before (xs.filter p) a b := before_cons_tail h hax
          -- Extract Nodup for the tail from the cons
          have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
          -- Apply IH and lift back through cons
          exact before_cons_of_tail (ih hnd' h')
      · -- Case: p x = false, so filter skips x
        -- (x :: xs).filter p = xs.filter p
        simp only [List.filter, hpx] at h
        -- Extract Nodup for the tail
        have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
        -- Apply IH directly (h is already about xs.filter p) and lift
        exact before_cons_of_tail (ih hnd' h)

lemma before_filter_of_before {p : EventId → Bool} {tr : List EventId} {a b : EventId}
    (ha : p a = true) (hb : p b = true) :
    Before tr a b → Before (tr.filter p) a b := by
  induction tr with
  | nil =>
      intro h
      rcases h with ⟨l1, l2, heq, _⟩
      simp at heq
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
  | C, (e :: es), h => fun x hx => by
      rcases h with ⟨hen, htail⟩
      cases hx with
      | head => exact hen.1
      | @tail _ _ hx' => exact LocalScript.validTraceAux_events s (insert e C) es htail x hx'

lemma LocalScript.validTraceAux_no_conflict_with_C (s : LocalScript) :
    ∀ (C : Finset EventId) (tr : List EventId),
      LocalScript.validTraceAux s C tr →
      ∀ x ∈ tr, ∀ f ∈ C, ¬ s.conflict x f
  | C, [], _ => by
      intro x hx
      cases hx
  | C, (e :: es), h => fun x hx f hf => by
      rcases h with ⟨hen, htail⟩
      cases hx with
      | head => exact hen.2.2.2 f hf
      | @tail _ _ hx' =>
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
      rcases h with ⟨l1, l2, heq, _⟩
      simp at heq
  | C, (hd :: es), h => by
      rcases h with ⟨hen, htail⟩
      intro a b hbefore
      by_cases hax : a = hd
      · subst hax
        have hb : b ∈ es := mem_tail_of_before_head hbefore
        have hnoc :=
          LocalScript.validTraceAux_no_conflict_with_C s (insert a C) es htail b hb a
            (by simp)
        simpa using hnoc
      · have hbefore' : Before es a b := before_cons_tail hbefore hax
        have ih :=
          LocalScript.validTraceAux_no_conflict_before s (insert hd C) es htail a b hbefore'
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

/-- Order dependencies are preserved when lifting from local to global traces.

If role `r` conforms to its projected trace and there is an ordering dependency
`e' → e` in the global script, then `e'` must appear before `e` in the global trace.
This bridges local validity (from `localConform`) with global trace ordering.

**Proof strategy:** The proof connects local and global views in three steps:
1. Show that the global order `s.order e' e` induces the projected order
   `(s.project r).order e' e` (using the relevance hypotheses and `wellFormed.orderDom`)
2. Apply `LocalScript.validTraceAux_order` to the projected trace to establish
   `Before (s.traceProj r tr) e' e`
3. Use `before_of_filter` to lift the `Before` relation from the projected trace
   back to the original trace -/
lemma local_validTrace_order_before {s : Script} {r : RoleId} {tr : List EventId}
    (hwf : s.wellFormed)
    (hlocal : Script.localConform s r (s.traceProj r tr))
    (hnd : tr.Nodup)
    {e' e : EventId}
    (hre' : s.relevant r e' = true) (hre : s.relevant r e = true)
    (hord : s.order e' e) (he : e ∈ tr) :
    Before tr e' e := by
  -- Extract valid trace from local conformance
  have htrace : LocalScript.validTrace (s.project r) (s.traceProj r tr) := hlocal.2
  -- Show e is in projected trace
  have he_proj : e ∈ s.traceProj r tr := List.mem_filter.mpr ⟨he, hre⟩
  -- Show projected order holds: need e', e ∈ s.projEvents r
  have he'_events : e' ∈ s.events := (hwf.1 _ _ hord).1
  have he_events : e ∈ s.events := (hwf.1 _ _ hord).2
  have he'_proj_events : e' ∈ s.projEvents r :=
    Finset.mem_filter.mpr ⟨he'_events, hre'⟩
  have he_proj_events : e ∈ s.projEvents r :=
    Finset.mem_filter.mpr ⟨he_events, hre⟩
  have hord_proj : (s.project r).order e' e := ⟨hord, he'_proj_events, he_proj_events⟩
  -- Apply validTraceAux_order with C = ∅
  have horder_result := LocalScript.validTraceAux_order (s.project r) ∅
    (s.traceProj r tr) htrace e' e hord_proj he_proj
  -- Since e' ∉ ∅, we have Before in projected trace
  rcases horder_result with h_empty | h_before
  · simp at h_empty
  · -- Lift to original trace using before_of_filter
    exact before_of_filter hnd hre' hre h_before

/-- Main soundness theorem: local conformance + cross-role consistency implies trace consistency.

This theorem combines local validity (each role's trace conforms to its projection) with
cross-role consistency (conflicts and order dependencies respect role boundaries) to establish
global trace consistency.

**Proof strategy:**
The 6 conjuncts of `traceConsistentAux` are proven as follows:
1. `tr.Nodup` - given by `hnd`
2. Events in trace are in script events - given by `hevents`
3. Events not in C (C = ∅) - trivial
4. No conflicts with C (C = ∅) - vacuously true
5. Pairwise no conflicts - uses role dichotomy:
   - Shared role: `local_no_conflict_before` + conflict symmetry
   - Disjoint roles: `hcross` directly
6. Order dependencies satisfied - uses role dichotomy:
   - Shared role: `local_validTrace_order_before`
   - Disjoint roles: `hcross` directly -/
lemma Script.traceConsistent_of_local_and_cross (s : Script) (tr : List EventId)
    (hwf : s.wellFormed)
    (hnd : tr.Nodup)
    (hevents : ∀ e, e ∈ tr → e ∈ s.events)
    (hlocal : ∀ r ∈ s.roles, Script.localConform s r (s.traceProj r tr))
    (hcross : s.crossRoleConsistent tr) :
    s.traceConsistent tr := by
  unfold Script.traceConsistent Script.traceConsistentAux
  refine ⟨hnd, hevents, ?_, ?_, ?_, ?_⟩
  -- Conjunct (3): e ∈ tr → e ∉ ∅
  · intro e _; simp
  -- Conjunct (4): e ∈ tr → f ∈ ∅ → ¬ conflict e f (vacuously true)
  · intro e _ f hf; simp at hf
  -- Conjunct (5): Pairwise no conflicts within the trace
  · -- Key insight: for any ordered pair (a before b), we prove no conflicts via role dichotomy.
    -- Either a and b share a role (use local conformance) or have disjoint roles (use hcross).
    suffices hpair : ∀ a b, a ∈ tr → b ∈ tr → Before tr a b →
        ¬ s.conflict a b ∧ ¬ s.conflict b a by
      -- Derive Pairwise from hpair by induction on tr
      clear hlocal hcross  -- These are captured in hpair
      induction tr with
      | nil => exact List.Pairwise.nil
      | cons x xs ih =>
          have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
          apply List.Pairwise.cons
          · -- Head x is non-conflicting with all elements y in tail xs
            intro y hy
            have hx_mem : x ∈ x :: xs := List.mem_cons.mpr (Or.inl rfl)
            have hy_mem : y ∈ x :: xs := List.mem_cons_of_mem x hy
            exact hpair x y hx_mem hy_mem (before_head hy)
          · -- Tail xs is pairwise by IH (lifting membership and Before)
            apply ih hnd'
            · intro e he; exact hevents e (List.mem_cons_of_mem x he)
            · intro a b ha hb hab
              exact hpair a b (List.mem_cons_of_mem x ha) (List.mem_cons_of_mem x hb)
                (before_cons_of_tail hab)
    -- Prove hpair: for any pair with a before b, no conflicts in either direction
    intro a b ha hb hab
    -- Role dichotomy: either a and b share a participant, or their participants are disjoint
    by_cases hshare : s.shareRole a b
    · -- Case: shared role - use local conformance
      -- Extract the shared role r
      obtain ⟨r, hra, hrb⟩ := shareRole_exists hshare
      have hrel_a := relevant_of_participant hra
      have hrel_b := relevant_of_participant hrb
      -- r is in the script's roles (by wellFormed.rolesOK)
      have hr_role : r ∈ s.roles := hwf.2.2.2.2.2.1 a (hevents a ha) hra
      have hloc := hlocal r hr_role
      -- a before b in the projected trace (filtering preserves Before)
      have hab_proj : Before (s.traceProj r tr) a b :=
        before_filter_of_before hrel_a hrel_b hab
      -- local_no_conflict_before gives ¬ conflict b a
      have hncba : ¬ s.conflict b a := local_no_conflict_before hloc a b hab_proj
      -- By conflict symmetry (from wellFormed), ¬ conflict a b follows
      have hncab : ¬ s.conflict a b := fun hc => hncba (hwf.2.2.2.1 a b hc)
      exact ⟨hncab, hncba⟩
    · -- Case: disjoint roles - use crossRoleConsistent directly
      have hdisj : s.disjointRoles a b := by
        -- shareRole and disjointRoles partition all pairs (complementary definitions)
        simp only [Script.shareRole, Script.disjointRoles] at hshare ⊢
        rwa [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at hshare
      exact hcross.1 a b ha hb hdisj
  -- Conjunct (6): Order dependencies are satisfied (predecessors appear before successors)
  · intro e' e hord he
    -- With C = ∅, the disjunction e' ∈ C ∨ Before tr e' e reduces to Before tr e' e
    right
    -- Role dichotomy again: shared role vs disjoint roles
    by_cases hshare : s.shareRole e' e
    · -- Case: shared role - use local_validTrace_order_before
      obtain ⟨r, hre', hre⟩ := shareRole_exists hshare
      have hrel_e' := relevant_of_participant hre'
      have hrel_e := relevant_of_participant hre
      -- e' is in events (by wellFormed.orderDom)
      have he'_events : e' ∈ s.events := (hwf.1 e' e hord).1
      have hr_role : r ∈ s.roles := hwf.2.2.2.2.2.1 e' he'_events hre'
      have hloc := hlocal r hr_role
      exact local_validTrace_order_before hwf hloc hnd hrel_e' hrel_e hord he
    · -- Case: disjoint roles - crossRoleConsistent.2 gives Before directly
      have hdisj : s.disjointRoles e' e := by
        simp only [Script.shareRole, Script.disjointRoles] at hshare ⊢
        rwa [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at hshare
      exact hcross.2 e' e hdisj hord he

/-- The head of a Nodup list cannot have any element "before" it.

If `Before (e :: es) a e` held, then `e` would appear in the suffix `l2` after `a`,
but `e` is also the head. This would mean `e` appears twice, contradicting `Nodup`.

**Proof strategy:** By contradiction. Assume `Before (e :: es) a e`, which gives us
witnesses `l1, l2` such that `e :: es = l1 ++ a :: l2` and `e ∈ l2`. We case split
on whether `l1` is empty:
- If `l1 = []`: Then `es = l2`, so `e ∈ es`, contradicting `Nodup`.
- If `l1 = x :: l1'`: Then `es = l1' ++ a :: l2`, so `e ∈ l2 ⊆ es`, again contradicting `Nodup`. -/
lemma before_head_false {e : EventId} {es : List EventId} {a : EventId}
    (hnd : (e :: es).Nodup) : ¬ Before (e :: es) a e := by
  -- Assume Before holds and derive contradiction
  intro ⟨l1, l2, heq, he_in_l2⟩
  -- Key fact from Nodup: the head e does not appear in the tail es
  have hne : e ∉ es := (List.nodup_cons.mp hnd).1
  -- Case split on the prefix l1 (before element a)
  cases l1 with
  | nil =>
      -- Case l1 = []: the equation becomes e :: es = [] ++ a :: l2 = a :: l2
      simp only [List.nil_append] at heq
      -- By list injection: e = a and es = l2
      have hes : es = l2 := List.cons.inj heq |>.2
      -- Since e ∈ l2 and es = l2, we have e ∈ es
      rw [hes] at hne
      -- But hne says e ∉ es - contradiction
      exact hne he_in_l2
  | cons x l1' =>
      -- Case l1 = x :: l1': the equation becomes e :: es = x :: (l1' ++ a :: l2)
      simp only [List.cons_append] at heq
      -- By list injection: e = x and es = l1' ++ a :: l2
      have hes : es = l1' ++ a :: l2 := List.cons.inj heq |>.2
      -- Since e ∈ l2 and l2 is a suffix of es, we have e ∈ es
      have he_in_es : e ∈ es := by
        rw [hes]
        -- l2 ⊆ a :: l2 ⊆ l1' ++ a :: l2 = es
        exact List.mem_append_right l1' (List.mem_cons_of_mem a he_in_l2)
      -- But hne says e ∉ es - contradiction
      exact hne he_in_es

lemma traceConsistentAux_validTraceAux (s : Script) :
    ∀ (C : Finset EventId) (tr : List EventId),
      s.traceConsistentAux C tr →
      Script.validTraceAux s C tr
  | C, [], _ => by simp [Script.validTraceAux]
  | C, (hd :: es), h => by
      simp only [Script.validTraceAux]
      obtain ⟨hnodup, hevents, hnotC, hconflC, hpair, horder⟩ := h
      have hnd_tail := (List.nodup_cons.mp hnodup).2
      have hhd_notin_es := (List.nodup_cons.mp hnodup).1
      constructor
      · unfold Script.enabled
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact hevents hd (List.mem_cons.mpr (Or.inl rfl))
        · exact hnotC hd (List.mem_cons.mpr (Or.inl rfl))
        · intro e' hord
          rcases horder e' hd hord (List.mem_cons.mpr (Or.inl rfl)) with he'C | hbefore
          · exact he'C
          · exfalso; exact before_head_false hnodup hbefore
        · exact hconflC hd (List.mem_cons.mpr (Or.inl rfl))
      · apply traceConsistentAux_validTraceAux
        refine ⟨hnd_tail, ?_, ?_, ?_, ?_, ?_⟩
        · exact fun e he => hevents e (List.mem_cons_of_mem hd he)
        · intro e he
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun heq => hhd_notin_es (heq ▸ he), hnotC e (List.mem_cons_of_mem hd he)⟩
        · intro e he f hf
          simp only [Finset.mem_insert] at hf
          rcases hf with rfl | hfC
          · exact (List.rel_of_pairwise_cons hpair he).2
          · exact hconflC e (List.mem_cons_of_mem hd he) f hfC
        · exact List.Pairwise.of_cons hpair
        · intro e' e hord he
          rcases horder e' e hord (List.mem_cons_of_mem hd he) with he'C | hbefore
          · exact Or.inl (Finset.mem_insert_of_mem he'C)
          · rcases hbefore with ⟨l1, l2, heq, he_in_l2⟩
            cases l1 with
            | nil => simp at heq; exact Or.inl (heq.1 ▸ Finset.mem_insert_self hd C)
            | cons _ l1' => simp at heq; exact Or.inr ⟨l1', l2, heq.2, he_in_l2⟩

theorem traceConsistent_implies_validTrace (s : Script) (tr : List EventId)
    (h : s.traceConsistent tr) : Script.validTrace s tr :=
  traceConsistentAux_validTraceAux s ∅ tr h

theorem globalConform_of_consistent (s : Script) (tr : List EventId)
    (hwf : s.wellFormed) (h : s.traceConsistent tr) : s.globalConform tr := by
  exact ⟨hwf, traceConsistent_implies_validTrace s tr h⟩

/-! ## Projection lemmas (core) -/

lemma filter_insert_false {p : EventId → Bool} {C : Finset EventId} {e : EventId}
    (h : p e = false) :
    (insert e C).filter (fun x => p x = true) = C.filter (fun x => p x = true) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · intro ⟨hx, hp⟩
    rcases hx with rfl | hxC
    · simp [h] at hp
    · exact ⟨hxC, hp⟩
  · intro ⟨hxC, hp⟩
    exact ⟨Or.inr hxC, hp⟩

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

lemma proj_validTraceAux (s : Script) (r : RoleId) :
    ∀ (C : Finset EventId) (tr : List EventId),
      Script.validTraceAux s C tr →
      LocalScript.validTraceAux (s.project r) (C.filter (fun e => s.relevant r e = true))
        (tr.filter (fun e => s.relevant r e = true))
  | C, [], _ => by simp [LocalScript.validTraceAux]
  | C, (e :: es), h => by
      rcases h with ⟨hen, htail⟩
      simp only [List.filter_cons]
      by_cases hrel : s.relevant r e = true
      · simp only [hrel, ↓reduceIte, LocalScript.validTraceAux]
        constructor
        · simp only [LocalScript.enabled, Script.project, Script.projEvents]
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [Finset.mem_filter]; exact ⟨hen.1, hrel⟩
          · simp only [Finset.mem_filter, not_and]; exact fun he_in_C => absurd he_in_C hen.2.1
          · intro e' ⟨hord, he', _⟩
            simp only [Finset.mem_filter] at he' ⊢
            exact ⟨hen.2.2.1 e' hord, he'.2⟩
          · intro f hf hconf
            simp only [Finset.mem_filter] at hf
            exact hen.2.2.2 f hf.1 hconf.1
        · rw [← filter_insert_true hrel]
          exact proj_validTraceAux s r (insert e C) es htail
      · have hrel_false : s.relevant r e = false := by
          cases h' : s.relevant r e <;> [rfl; exact absurd h' (by simp [hrel])]
        simp only [hrel_false, Bool.false_eq_true, ↓reduceIte]
        rw [← filter_insert_false hrel_false]
        exact proj_validTraceAux s r (insert e C) es htail

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
