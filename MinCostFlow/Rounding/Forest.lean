module

public import MinCostFlow.Rounding.Walks
public import Mathlib.Data.Rat.Floor
import Mathlib.Data.List.Perm.Basic

/-!
# Dynamic forest specification and mathematical model (Kang–Payor Sections 2.1 and 4)

This file defines `MathForest`, a computable mathematical forest on vertices `0, …, n - 1` whose
edges store an identifier `eid`, canonical endpoints `(u, v)`, integral cost, rational flow, and
forward/backward availabilities. It implements and specifies the six dynamic-tree operations of
Kang–Payor Section 2.1 (`Link`, `Cut`, `FindRoot`, `PathAdd`, `PathMin` with ties broken closest
to the start vertex `u`, and `PathSum`), handling directed edge orientations along arbitrary `u`-`v`
paths.

It also defines the abstract interface `DynForest` (data only) together with its correctness
predicate `DynForest.IsSpec`, and constructs the canonical instance `mathDynForest` satisfying
`DynForest.IsSpec`.
-/

@[expose] public section

namespace MinCostFlow.Rounding

/-- An active fractional edge stored in the dynamic forest. -/
structure ForestEdge where
  /-- Edge index in the underlying instance. -/
  eid : ℕ
  /-- Canonical tail vertex `u`. -/
  u : ℕ
  /-- Canonical head vertex `v`. -/
  v : ℕ
  /-- Integral cost per unit flow in direction `u → v`. -/
  cost : ℤ
  /-- Current flow in direction `u → v`. -/
  flow : ℚ
  /-- Forward availability `⌈f_e⌉ - flow` (pushing `u → v`). -/
  availFwd : ℚ
  /-- Backward availability `flow - ⌊f_e⌋` (pushing `v → u`). -/
  availBwd : ℚ
  deriving DecidableEq

namespace ForestEdge

/-- Project a `ForestEdge` to its underlying `RawEdge`. -/
def toRaw (e : ForestEdge) : RawEdge :=
  ⟨e.eid, e.u, e.v⟩

/-- Apply `δ` units of flow in orientation `fwd` (`true` for `u → v`, `false` for `v → u`). -/
def addFlow (e : ForestEdge) (fwd : Bool) (δ : ℚ) : ForestEdge :=
  if fwd then
    { e with
      flow := e.flow + δ
      availFwd := e.availFwd - δ
      availBwd := e.availBwd + δ }
  else
    { e with
      flow := e.flow - δ
      availFwd := e.availFwd + δ
      availBwd := e.availBwd - δ }

@[simp]
theorem toRaw_addFlow (e : ForestEdge) (fwd : Bool) (δ : ℚ) :
    (e.addFlow fwd δ).toRaw = e.toRaw := by
  cases fwd <;> rfl

@[simp]
theorem eid_addFlow (e : ForestEdge) (fwd : Bool) (δ : ℚ) :
    (e.addFlow fwd δ).eid = e.eid := by
  cases fwd <;> rfl

@[simp]
theorem u_addFlow (e : ForestEdge) (fwd : Bool) (δ : ℚ) :
    (e.addFlow fwd δ).u = e.u := by
  cases fwd <;> rfl

@[simp]
theorem v_addFlow (e : ForestEdge) (fwd : Bool) (δ : ℚ) :
    (e.addFlow fwd δ).v = e.v := by
  cases fwd <;> rfl

@[simp]
theorem cost_addFlow (e : ForestEdge) (fwd : Bool) (δ : ℚ) :
    (e.addFlow fwd δ).cost = e.cost := by
  cases fwd <;> rfl

end ForestEdge

/-- Result of a `PathMin` query on a nonempty simple path `u → v`: an edge `eid` traversed from
`x` (closer to `u`) to `y` (closer to `v`), with availability `avail` in direction `x → y` and
canonical flow `flow`. -/
structure PathHit where
  eid : ℕ
  x : ℕ
  y : ℕ
  avail : ℚ
  flow : ℚ
  deriving DecidableEq

/-- A directed edge traversal step along a path. -/
structure PathStep where
  edge : ForestEdge
  fwd : Bool
  deriving DecidableEq

namespace PathStep

/-- The underlying `RawEdge` of a `PathStep`. -/
def toRaw (s : PathStep) : RawEdge :=
  s.edge.toRaw

/-- The `u`-side (source) endpoint of this step. -/
def src (s : PathStep) : ℕ :=
  if s.fwd then s.edge.u else s.edge.v

/-- The `v`-side (destination) endpoint of this step. -/
def dst (s : PathStep) : ℕ :=
  if s.fwd then s.edge.v else s.edge.u

/-- Signed cost of traversing this step. -/
def signedCost (s : PathStep) : ℤ :=
  if s.fwd then s.edge.cost else -s.edge.cost

/-- Availability in the traversal direction of this step. -/
def dirAvail (s : PathStep) : ℚ :=
  if s.fwd then s.edge.availFwd else s.edge.availBwd

/-- Reverse the orientation of a `PathStep`. -/
def flip (s : PathStep) : PathStep :=
  { edge := s.edge, fwd := !s.fwd }

/-- Convert a step to a `PathHit`. -/
def toHit (s : PathStep) : PathHit :=
  ⟨s.edge.eid, s.src, s.dst, s.dirAvail, s.edge.flow⟩

@[simp]
theorem toRaw_flip (s : PathStep) : s.flip.toRaw = s.toRaw := rfl

@[simp]
theorem src_flip (s : PathStep) : s.flip.src = s.dst := by
  rcases s with ⟨edge, (_ | _)⟩ <;> rfl

@[simp]
theorem dst_flip (s : PathStep) : s.flip.dst = s.src := by
  rcases s with ⟨edge, (_ | _)⟩ <;> rfl

@[simp]
theorem signedCost_flip (s : PathStep) : s.flip.signedCost = -s.signedCost := by
  rcases s with ⟨edge, (_ | _)⟩ <;> simp [flip, signedCost]

end PathStep

/-- A directed walk of `PathStep`s from `a` to `b` using edges in `edges`. -/
inductive IsStepWalk (edges : List ForestEdge) : ℕ → ℕ → List PathStep → Prop where
  | nil (a : ℕ) : IsStepWalk edges a a []
  | fwd {a b : ℕ} {e : ForestEdge} {rest : List PathStep} :
      e ∈ edges → e.u = a → IsStepWalk edges e.v b rest →
      IsStepWalk edges a b ({ edge := e, fwd := true } :: rest)
  | bwd {a b : ℕ} {e : ForestEdge} {rest : List PathStep} :
      e ∈ edges → e.v = a → IsStepWalk edges e.u b rest →
      IsStepWalk edges a b ({ edge := e, fwd := false } :: rest)

namespace IsStepWalk

theorem to_isWalk {edges : List ForestEdge} {a b : ℕ} {steps : List PathStep}
    (h : IsStepWalk edges a b steps) :
    IsWalk (edges.map ForestEdge.toRaw) a b (steps.map PathStep.toRaw) := by
  induction h with
  | nil a => exact .nil a
  | fwd he hu _ ih =>
    exact .cons (List.mem_map_of_mem he) (Or.inl ⟨hu, rfl⟩) ih
  | bwd he hv _ ih =>
    exact .cons (List.mem_map_of_mem he) (Or.inr ⟨rfl, hv⟩) ih

theorem mem_edges {edges : List ForestEdge} {a b : ℕ} {steps : List PathStep}
    (h : IsStepWalk edges a b steps) : ∀ s ∈ steps, s.edge ∈ edges := by
  induction h with
  | nil _ => simp
  | fwd he _ _ ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact he
    · exact ih s hs
  | bwd he _ _ ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact he
    · exact ih s hs

theorem mono {edges₁ edges₂ : List ForestEdge} (hsub : ∀ e ∈ edges₁, e ∈ edges₂)
    {a b : ℕ} {steps : List PathStep} (h : IsStepWalk edges₁ a b steps) :
    IsStepWalk edges₂ a b steps := by
  induction h with
  | nil a => exact .nil a
  | fwd he hu _ ih => exact .fwd (hsub _ he) hu ih
  | bwd he hv _ ih => exact .bwd (hsub _ he) hv ih

theorem mono_of_mem {edges₁ edges₂ : List ForestEdge} {a b : ℕ} {steps : List PathStep}
    (h : IsStepWalk edges₁ a b steps) (hsub : ∀ s ∈ steps, s.edge ∈ edges₂) :
    IsStepWalk edges₂ a b steps := by
  induction h with
  | nil a => exact .nil a
  | fwd he hu _ ih =>
    exact .fwd (hsub _ List.mem_cons_self) hu
      (ih fun s hs => hsub s (List.mem_cons_of_mem _ hs))
  | bwd he hv _ ih =>
    exact .bwd (hsub _ List.mem_cons_self) hv
      (ih fun s hs => hsub s (List.mem_cons_of_mem _ hs))

theorem append {edges : List ForestEdge} {a b c : ℕ} {p q : List PathStep}
    (hp : IsStepWalk edges a b p) (hq : IsStepWalk edges b c q) :
    IsStepWalk edges a c (p ++ q) := by
  induction hp with
  | nil _ => exact hq
  | fwd he hu _ ih => exact .fwd he hu (ih hq)
  | bwd he hv _ ih => exact .bwd he hv (ih hq)

theorem split_append {edges : List ForestEdge} {a c : ℕ} {p q : List PathStep}
    (h : IsStepWalk edges a c (p ++ q)) :
    ∃ b, IsStepWalk edges a b p ∧ IsStepWalk edges b c q := by
  induction p generalizing a with
  | nil => exact ⟨a, .nil a, h⟩
  | cons s p ih =>
    cases h with
    | fwd he hu hrest =>
      obtain ⟨b, hp, hq⟩ := ih hrest
      exact ⟨b, .fwd he hu hp, hq⟩
    | bwd he hv hrest =>
      obtain ⟨b, hp, hq⟩ := ih hrest
      exact ⟨b, .bwd he hv hp, hq⟩

theorem reverse {edges : List ForestEdge} {a b : ℕ} {steps : List PathStep}
    (h : IsStepWalk edges a b steps) :
    IsStepWalk edges b a (steps.reverse.map PathStep.flip) := by
  induction h with
  | nil a => exact .nil a
  | fwd he hu _ ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
    exact ih.append (.bwd he rfl (hu ▸ .nil _))
  | bwd he hv _ ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
    exact ih.append (.fwd he rfl (hv ▸ .nil _))

theorem src_dst_cons {edges : List ForestEdge} {a b : ℕ} {s : PathStep} {rest : List PathStep}
    (h : IsStepWalk edges a b (s :: rest)) :
    s.src = a ∧ IsStepWalk edges s.dst b rest := by
  cases h with
  | fwd _ hu hrest => exact ⟨hu, hrest⟩
  | bwd _ hv hrest => exact ⟨hv, hrest⟩

theorem nil_iff {edges : List ForestEdge} {a b : ℕ} :
    IsStepWalk edges a b [] ↔ a = b := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil a

end IsStepWalk

/-- Total signed cost along a list of `PathStep`s. -/
def stepsCost (steps : List PathStep) : ℤ :=
  (steps.map PathStep.signedCost).sum

theorem stepsCost_append (p q : List PathStep) :
    stepsCost (p ++ q) = stepsCost p + stepsCost q := by
  simp [stepsCost, List.map_append, List.sum_append]

theorem stepsCost_reverse_flip (steps : List PathStep) :
    stepsCost (steps.reverse.map PathStep.flip) = -stepsCost steps := by
  induction steps with
  | nil => simp [stepsCost]
  | cons s rest ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, stepsCost,
      List.sum_append, List.sum_cons, List.sum_nil, PathStep.signedCost_flip] at ih ⊢
    omega

/-- Minimum-availability step hit on a path, breaking ties in favor of the step closest to the
start of `steps` (using `≤`). -/
def stepsMinHit : List PathStep → Option PathHit
  | [] => none
  | s :: rest =>
    let h0 := s.toHit
    match stepsMinHit rest with
    | none => some h0
    | some h1 => if h0.avail ≤ h1.avail then some h0 else some h1

theorem stepsMinHit_eq_none_iff {steps : List PathStep} :
    stepsMinHit steps = none ↔ steps = [] := by
  cases steps with
  | nil => simp [stepsMinHit]
  | cons s rest =>
    simp only [stepsMinHit]
    cases stepsMinHit rest with
    | none => simp
    | some h1 =>
      by_cases h : s.toHit.avail ≤ h1.avail <;> simp [h]

/-- Specification of `stepsMinHit`: if `stepsMinHit steps = some hit`, then `steps` splits as
`pre ++ s :: post` with `s.toHit = hit`, every step in `pre` having strictly larger `dirAvail`,
and every step in `post` having `dirAvail ≥ hit.avail`. -/
theorem stepsMinHit_spec {steps : List PathStep} {hit : PathHit}
    (h : stepsMinHit steps = some hit) :
    ∃ pre s post, steps = pre ++ s :: post ∧ s.toHit = hit ∧
      (∀ t ∈ pre, hit.avail < t.dirAvail) ∧
      (∀ t ∈ post, hit.avail ≤ t.dirAvail) := by
  induction steps generalizing hit with
  | nil => simp [stepsMinHit] at h
  | cons s rest ih =>
    simp only [stepsMinHit] at h
    cases hrec : stepsMinHit rest with
    | none =>
      rw [hrec] at h
      simp only [Option.some.injEq] at h
      have hnil : rest = [] := stepsMinHit_eq_none_iff.mp hrec
      subst hnil
      exact ⟨[], s, [], rfl, h, by simp, by simp⟩
    | some h1 =>
      rw [hrec] at h
      dsimp only at h
      obtain ⟨pre, s1, post, hsplit, hs1, hpre, hpost⟩ := ih hrec
      by_cases hle : s.toHit.avail ≤ h1.avail
      · rw [ite_eq_left hle] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨[], s, rest, rfl, rfl, by simp, fun t ht => ?_⟩
        rw [hsplit, List.mem_append, List.mem_cons] at ht
        have hs1_avail : s1.dirAvail = h1.avail := by rw [← hs1]; rfl
        rcases ht with ht | rfl | ht
        · exact le_trans hle (le_of_lt (hpre t ht))
        · exact le_trans hle (le_of_eq hs1_avail.symm)
        · exact le_trans hle (hpost t ht)
      · rw [ite_eq_right hle] at h
        simp only [Option.some.injEq] at h
        subst h
        push Not at hle
        refine ⟨s :: pre, s1, post, by rw [hsplit]; rfl, hs1, fun t ht => ?_, hpost⟩
        rcases List.mem_cons.mp ht with rfl | ht
        · simpa [PathStep.toHit] using hle
        · exact hpre t ht

/-- Computable simple-path search in a finite list of `ForestEdge`s. -/
def findStepsLoop (all rem : List ForestEdge) (a b : ℕ) : Option (List PathStep) :=
  if a = b then some []
  else match rem with
  | [] => none
  | e :: rest =>
    if _he : e ∈ all then
      if e.u = a then
        match findStepsLoop (all.erase e) (all.erase e) e.v b with
        | some tail => some ({ edge := e, fwd := true } :: tail)
        | none => findStepsLoop all rest a b
      else if e.v = a then
        match findStepsLoop (all.erase e) (all.erase e) e.u b with
        | some tail => some ({ edge := e, fwd := false } :: tail)
        | none => findStepsLoop all rest a b
      else findStepsLoop all rest a b
    else findStepsLoop all rest a b
termination_by (all.length, rem.length)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ (by simp)
    | exact Prod.Lex.left _ _ (by
        have := List.length_erase_of_mem (by assumption : e ∈ all)
        have := List.length_pos_of_mem (by assumption : e ∈ all)
        omega)

/-- Find the simple directed step walk from `a` to `b` in `edges`. -/
def findSteps (edges : List ForestEdge) (a b : ℕ) : Option (List PathStep) :=
  findStepsLoop edges edges a b

private theorem eid_nodup_erase {all : List ForestEdge} (hnd : (all.map ForestEdge.eid).Nodup)
    (e : ForestEdge) : ((all.erase e).map ForestEdge.eid).Nodup :=
  (List.erase_sublist.map ForestEdge.eid).nodup hnd

private theorem ne_of_mem_erase_eid_nodup {all : List ForestEdge}
    (hnd : (all.map ForestEdge.eid).Nodup) {e t : ForestEdge}
    (he : e ∈ all) (ht : t ∈ all.erase e) : t.eid ≠ e.eid := by
  intro heq
  have hnd_all : all.Nodup := hnd.of_map _
  have hmem_t : t ∈ all := List.mem_of_mem_erase ht
  have ht_ne : t ≠ e := fun h => hnd_all.not_mem_erase (h ▸ ht)
  have hsub : ∀ xs : List ForestEdge, (xs.map ForestEdge.eid).Nodup →
      ∀ x y, x ∈ xs → y ∈ xs → x ≠ y → x.eid ≠ y.eid := by
    intro xs hxs x y hx hy hne hxy
    induction xs with
    | nil => simp at hx
    | cons z zs ih =>
      rw [List.map_cons, List.nodup_cons] at hxs
      rcases List.mem_cons.mp hx with hxz | hx <;> rcases List.mem_cons.mp hy with hyz | hy
      · exact absurd (hxz.trans hyz.symm) hne
      · exact hxs.1 (hxz ▸ hxy ▸ List.mem_map_of_mem hy)
      · exact hxs.1 (hyz ▸ hxy.symm ▸ List.mem_map_of_mem hx)
      · exact ih hxs.2 hx hy
  exact hsub all hnd t e hmem_t he ht_ne heq

private theorem findSteps_sound_aux (k : ℕ) :
    ∀ all, all.length ≤ k → (all.map ForestEdge.eid).Nodup →
      ∀ rem, (∀ e ∈ rem, e ∈ all) → ∀ a b steps, findStepsLoop all rem a b = some steps →
        IsStepWalk all a b steps ∧ (steps.map PathStep.toRaw).Nodup := by
  induction k with
  | zero =>
    intro all hlen _ rem hsub a b steps h
    have hall : all = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hall
    have hrem : rem = [] := by
      cases rem with
      | nil => rfl
      | cons e _ => exact absurd (hsub e List.mem_cons_self) (by simp)
    subst hrem
    rw [findStepsLoop.eq_def] at h
    split_ifs at h with hab
    subst hab
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨.nil a, List.nodup_nil⟩
  | succ k ih =>
    intro all hlen hnd rem
    induction rem with
    | nil =>
      intro _ a b steps h
      rw [findStepsLoop.eq_def] at h
      split_ifs at h with hab
      subst hab
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨.nil a, List.nodup_nil⟩
    | cons e rest ih_rem =>
      intro hsub a b steps h
      have hsub_rest : ∀ x ∈ rest, x ∈ all := fun x hx => hsub x (List.mem_cons_of_mem _ hx)
      rw [findStepsLoop.eq_def] at h
      by_cases hab : a = b
      · subst hab
        simp only [↓reduceIte, Option.some.injEq] at h
        subst h
        exact ⟨.nil a, List.nodup_nil⟩
      · simp only [hab, ↓reduceIte] at h
        by_cases he : e ∈ all
        · rw [dite_eq_left_of_eq_true (eq_true he)] at h
          by_cases hu : e.u = a
          · rw [ite_eq_left hu] at h
            cases hrec : findStepsLoop (all.erase e) (all.erase e) e.v b with
            | none =>
              rw [hrec] at h
              dsimp only at h
              exact ih_rem hsub_rest a b steps h
            | some tail =>
              rw [hrec] at h
              simp only [Option.some.injEq] at h
              subst h
              have hlen_er : (all.erase e).length ≤ k := by
                have := List.length_erase_of_mem he
                omega
              obtain ⟨htail, htail_nd⟩ :=
                ih (all.erase e) hlen_er (eid_nodup_erase hnd e) (all.erase e) (fun _ hx => hx) e.v b tail hrec
              have hnot : e.toRaw ∉ tail.map PathStep.toRaw := by
                intro hm
                rw [List.mem_map] at hm
                obtain ⟨t, ht_mem, ht_raw⟩ := hm
                have hne_eid := ne_of_mem_erase_eid_nodup hnd he (htail.mem_edges t ht_mem)
                exact hne_eid (congrArg RawEdge.eid ht_raw)
              refine ⟨.fwd he hu (htail.mono fun x hx => List.mem_of_mem_erase hx), ?_⟩
              simpa only [List.map_cons, List.nodup_cons] using ⟨hnot, htail_nd⟩
          · rw [ite_eq_right hu] at h
            by_cases hv : e.v = a
            · rw [ite_eq_left hv] at h
              cases hrec : findStepsLoop (all.erase e) (all.erase e) e.u b with
              | none =>
                rw [hrec] at h
                dsimp only at h
                exact ih_rem hsub_rest a b steps h
              | some tail =>
                rw [hrec] at h
                simp only [Option.some.injEq] at h
                subst h
                have hlen_er : (all.erase e).length ≤ k := by
                  have := List.length_erase_of_mem he
                  omega
                obtain ⟨htail, htail_nd⟩ :=
                  ih (all.erase e) hlen_er (eid_nodup_erase hnd e) (all.erase e) (fun _ hx => hx) e.u b tail hrec
                have hnot : e.toRaw ∉ tail.map PathStep.toRaw := by
                  intro hm
                  rw [List.mem_map] at hm
                  obtain ⟨t, ht_mem, ht_raw⟩ := hm
                  have hne_eid := ne_of_mem_erase_eid_nodup hnd he (htail.mem_edges t ht_mem)
                  exact hne_eid (congrArg RawEdge.eid ht_raw)
                refine ⟨.bwd he hv (htail.mono fun x hx => List.mem_of_mem_erase hx), ?_⟩
                simpa only [List.map_cons, List.nodup_cons] using ⟨hnot, htail_nd⟩
            · rw [ite_eq_right hv] at h
              exact ih_rem hsub_rest a b steps h
        · exact absurd (hsub e List.mem_cons_self) he

theorem findSteps_sound {all : List ForestEdge} (hnd : (all.map ForestEdge.eid).Nodup)
    {a b : ℕ} {steps : List PathStep} (h : findSteps all a b = some steps) :
    IsStepWalk all a b steps ∧ (steps.map PathStep.toRaw).Nodup :=
  findSteps_sound_aux all.length all (Nat.le_refl _) hnd all (fun _ hx => hx) a b steps h

private theorem findSteps_complete_aux (k : ℕ) :
    ∀ all, all.length ≤ k → (all.map ForestEdge.eid).Nodup →
      IsAcyclic (all.map ForestEdge.toRaw) →
      ∀ rem, (∀ e ∈ rem, e ∈ all) → ∀ a b steps,
        IsStepWalk all a b steps → (steps.map PathStep.toRaw).Nodup →
        (∀ s rest, steps = s :: rest → s.edge ∈ rem) →
        (findStepsLoop all rem a b).isSome := by
  induction k with
  | zero =>
    intro all hlen _ _ rem _ a b steps hw _ hfirst
    have hall : all = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hall
    rw [findStepsLoop.eq_def]
    split_ifs with hab
    · simp
    · cases hw with
      | nil _ => exact absurd rfl hab
      | fwd he _ _ => simp at he
      | bwd he _ _ => simp at he
  | succ k ih =>
    intro all hlen hnd hacyc rem
    induction rem with
    | nil =>
      intro _ a b steps hw _ hfirst
      rw [findStepsLoop.eq_def]
      split_ifs with hab
      · simp
      · cases hw with
        | nil _ => exact absurd rfl hab
        | fwd he _ _ => exact absurd (hfirst _ _ rfl) (by simp)
        | bwd he _ _ => exact absurd (hfirst _ _ rfl) (by simp)
    | cons e remTail ih_rem =>
      intro hsub a b steps hw hnd_s hfirst
      have he_all : e ∈ all := hsub e List.mem_cons_self
      have hsub_tail : ∀ x ∈ remTail, x ∈ all := fun x hx => hsub x (List.mem_cons_of_mem _ hx)
      rw [findStepsLoop.eq_def]
      split_ifs with hab
      · simp
      · cases hw with
        | nil _ => exact absurd rfl hab
        | @fwd _ _ e₀ rest he₀ hu₀ hrest =>
          let s : PathStep := { edge := e₀, fwd := true }
          have hs_mem : e₀ ∈ e :: remTail := hfirst s rest rfl
          have ih_er : ∀ (heq : e = e₀),
              (findStepsLoop (all.erase e) (all.erase e) e.v b).isSome := by
            intro heq
            subst heq
            have hrest_er : IsStepWalk (all.erase e) e.v b rest := by
              refine hrest.mono_of_mem fun t ht => ?_
              have ht_in : t.edge ∈ all := hrest.mem_edges t ht
              have ht_ne : t.edge ≠ e := by
                intro hteq
                rw [List.map_cons, List.nodup_cons] at hnd_s
                apply hnd_s.1
                rw [List.mem_map]
                exact ⟨t, ht, by simp [PathStep.toRaw, hteq]⟩
              exact (List.mem_erase_of_ne ht_ne).mpr ht_in
            have hlen_er : (all.erase e).length ≤ k := by
              have := List.length_erase_of_mem he_all
              omega
            have hacyc_er : IsAcyclic ((all.erase e).map ForestEdge.toRaw) :=
              hacyc.mono fun x hx => by
                rw [List.mem_map] at hx ⊢
                obtain ⟨y, hy, rfl⟩ := hx
                exact ⟨y, List.mem_of_mem_erase hy, rfl⟩
            have hnd_rest : (rest.map PathStep.toRaw).Nodup := by
              rw [List.map_cons, List.nodup_cons] at hnd_s
              exact hnd_s.2
            exact ih (all.erase e) hlen_er (eid_nodup_erase hnd e) hacyc_er (all.erase e)
              (fun _ hx => hx) e.v b rest hrest_er hnd_rest
              (fun s' _ hs' => hrest_er.mem_edges s' (hs' ▸ List.mem_cons_self))
          have hfallback : ∀ (hne_e : e ≠ e₀),
              (findStepsLoop all remTail a b).isSome := by
            intro hne_e
            have hs_tail : e₀ ∈ remTail := by
              rcases List.mem_cons.mp hs_mem with h1 | h2
              · exact absurd h1.symm hne_e
              · exact h2
            have ih_t := ih_rem hsub_tail a b (s :: rest) (.fwd he₀ hu₀ hrest) hnd_s
              (fun s' rest' h => by cases h; exact hs_tail)
            exact ih_t
          dsimp only
          rw [dite_eq_left_of_eq_true (eq_true he_all)]
          by_cases hu : e.u = a
          · rw [ite_eq_left hu]
            cases hrec : findStepsLoop (all.erase e) (all.erase e) e.v b with
            | some _ => simp
            | none =>
              have hne_e : e ≠ e₀ := by
                intro heq
                have := ih_er heq
                simp [hrec] at this
              exact hfallback hne_e
          · rw [ite_eq_right hu]
            by_cases hv : e.v = a
            · rw [ite_eq_left hv]
              cases hrec : findStepsLoop (all.erase e) (all.erase e) e.u b with
              | some _ => simp
              | none =>
                have hne_e : e ≠ e₀ := fun heq => hu (heq ▸ hu₀)
                exact hfallback hne_e
            · rw [ite_eq_right hv]
              exact hfallback (fun heq => hu (heq ▸ hu₀))
        | @bwd _ _ e₀ rest he₀ hv₀ hrest =>
          let s : PathStep := { edge := e₀, fwd := false }
          have hs_mem : e₀ ∈ e :: remTail := hfirst s rest rfl
          have ih_er : ∀ (heq : e = e₀),
              (findStepsLoop (all.erase e) (all.erase e) e.u b).isSome := by
            intro heq
            subst heq
            have hrest_er : IsStepWalk (all.erase e) e.u b rest := by
              refine hrest.mono_of_mem fun t ht => ?_
              have ht_in : t.edge ∈ all := hrest.mem_edges t ht
              have ht_ne : t.edge ≠ e := by
                intro hteq
                rw [List.map_cons, List.nodup_cons] at hnd_s
                apply hnd_s.1
                rw [List.mem_map]
                exact ⟨t, ht, by simp [PathStep.toRaw, hteq]⟩
              exact (List.mem_erase_of_ne ht_ne).mpr ht_in
            have hlen_er : (all.erase e).length ≤ k := by
              have := List.length_erase_of_mem he_all
              omega
            have hacyc_er : IsAcyclic ((all.erase e).map ForestEdge.toRaw) :=
              hacyc.mono fun x hx => by
                rw [List.mem_map] at hx ⊢
                obtain ⟨y, hy, rfl⟩ := hx
                exact ⟨y, List.mem_of_mem_erase hy, rfl⟩
            have hnd_rest : (rest.map PathStep.toRaw).Nodup := by
              rw [List.map_cons, List.nodup_cons] at hnd_s
              exact hnd_s.2
            exact ih (all.erase e) hlen_er (eid_nodup_erase hnd e) hacyc_er (all.erase e)
              (fun _ hx => hx) e.u b rest hrest_er hnd_rest
              (fun s' _ hs' => hrest_er.mem_edges s' (hs' ▸ List.mem_cons_self))
          have hfallback : ∀ (hne_e : e ≠ e₀),
              (findStepsLoop all remTail a b).isSome := by
            intro hne_e
            have hs_tail : e₀ ∈ remTail := by
              rcases List.mem_cons.mp hs_mem with h1 | h2
              · exact absurd h1.symm hne_e
              · exact h2
            have ih_t := ih_rem hsub_tail a b (s :: rest) (.bwd he₀ hv₀ hrest) hnd_s
              (fun s' rest' h => by cases h; exact hs_tail)
            exact ih_t
          dsimp only
          rw [dite_eq_left_of_eq_true (eq_true he_all)]
          by_cases hu : e.u = a
          · rw [ite_eq_left hu]
            cases hrec : findStepsLoop (all.erase e) (all.erase e) e.v b with
            | some _ => simp
            | none =>
              have hne_e : e ≠ e₀ := by
                intro heq
                have hne := hacyc.no_selfLoop (List.mem_map_of_mem he_all)
                exact hne (hu.trans (heq ▸ hv₀).symm)
              exact hfallback hne_e
          · rw [ite_eq_right hu]
            by_cases hv : e.v = a
            · rw [ite_eq_left hv]
              cases hrec : findStepsLoop (all.erase e) (all.erase e) e.u b with
              | some _ => simp
              | none =>
                have hne_e : e ≠ e₀ := by
                  intro heq
                  have := ih_er heq
                  simp [hrec] at this
                exact hfallback hne_e
            · rw [ite_eq_right hv]
              exact hfallback (fun heq => hv (heq ▸ hv₀))

/-- Uniqueness of `IsStepWalk` when `eid`s are distinct and the underlying graph is acyclic. -/
theorem isStepWalk_unique {edges : List ForestEdge}
    (hnd_eid : (edges.map ForestEdge.eid).Nodup)
    (hacyc : IsAcyclic (edges.map ForestEdge.toRaw))
    {a b : ℕ} {p₁ p₂ : List PathStep}
    (hp₁ : IsStepWalk edges a b p₁) (hnd₁ : (p₁.map PathStep.toRaw).Nodup)
    (hp₂ : IsStepWalk edges a b p₂) (hnd₂ : (p₂.map PathStep.toRaw).Nodup) :
    p₁ = p₂ := by
  have hraw : p₁.map PathStep.toRaw = p₂.map PathStep.toRaw :=
    hacyc.walk_unique hp₁.to_isWalk hnd₁ hp₂.to_isWalk hnd₂
  clear hnd₁ hnd₂
  induction p₁ generalizing a p₂ with
  | nil =>
    cases p₂ with
    | nil => rfl
    | cons _ _ => simp at hraw
  | cons s₁ r₁ ih =>
    cases p₂ with
    | nil => simp at hraw
    | cons s₂ r₂ =>
      simp only [List.map_cons, List.cons.injEq] at hraw
      obtain ⟨hraw_hd, hraw_tl⟩ := hraw
      have he_eq : s₁.edge = s₂.edge := by
        have h1 : s₁.edge ∈ edges := hp₁.mem_edges s₁ List.mem_cons_self
        have h2 : s₂.edge ∈ edges := hp₂.mem_edges s₂ List.mem_cons_self
        have heid : s₁.edge.eid = s₂.edge.eid := congrArg RawEdge.eid hraw_hd
        clear hraw_tl hraw_hd hp₁ hp₂ ih r₁ r₂ hacyc
        induction edges with
        | nil => simp at h1
        | cons z zs ihz =>
          rw [List.map_cons, List.nodup_cons] at hnd_eid
          rcases List.mem_cons.mp h1 with h1 | h1 <;> rcases List.mem_cons.mp h2 with h2 | h2
          · exact h1.trans h2.symm
          · exact absurd (h1 ▸ heid ▸ List.mem_map_of_mem h2) hnd_eid.1
          · exact absurd (h2 ▸ heid.symm ▸ List.mem_map_of_mem h1) hnd_eid.1
          · exact ihz hnd_eid.2 h1 h2
      have hsrc₁ := hp₁.src_dst_cons
      have hsrc₂ := hp₂.src_dst_cons
      have hne : s₁.edge.u ≠ s₁.edge.v :=
        hacyc.no_selfLoop (List.mem_map_of_mem (hp₁.mem_edges s₁ List.mem_cons_self))
      have hfwd_eq : s₁.fwd = s₂.fwd := by
        have hs_eq : s₁.src = s₂.src := hsrc₁.1.trans hsrc₂.1.symm
        cases hf1 : s₁.fwd <;> cases hf2 : s₂.fwd
        · rfl
        · simp [PathStep.src, hf1, hf2, he_eq] at hs_eq
          exact absurd (he_eq ▸ hs_eq.symm) hne
        · simp [PathStep.src, hf1, hf2, he_eq] at hs_eq
          exact absurd (he_eq ▸ hs_eq) hne
        · rfl
      have hs_eq : s₁ = s₂ := by
        cases s₁; cases s₂
        simp only [PathStep.mk.injEq] at *
        exact ⟨he_eq, hfwd_eq⟩
      subst hs_eq
      have hr_eq : r₁ = r₂ := ih hsrc₁.2 hsrc₂.2 hraw_tl
      simp [hr_eq]

/-- Convert any `Nodup` `IsWalk` in `edges.map toRaw` into a `IsStepWalk` in `edges`. -/
theorem exists_stepWalk_of_isWalk {edges : List ForestEdge}
    (hacyc : IsAcyclic (edges.map ForestEdge.toRaw))
    {a b : ℕ} {es : List RawEdge} (hw : IsWalk (edges.map ForestEdge.toRaw) a b es)
    (hnd : es.Nodup) :
    ∃ steps, IsStepWalk edges a b steps ∧ steps.map PathStep.toRaw = es := by
  induction hw with
  | nil a => exact ⟨[], .nil a, rfl⟩
  | cons he hc hrest ih =>
    rename_i a' w b' r es'
    rw [List.nodup_cons] at hnd
    obtain ⟨steps', hsteps', hmap'⟩ := ih hnd.2
    rw [List.mem_map] at he
    obtain ⟨e, he_mem, he_raw⟩ := he
    have hne : e.u ≠ e.v := by
      have hne_r := hacyc.no_selfLoop (he_raw ▸ (List.mem_map_of_mem he_mem : e.toRaw ∈ _))
      rw [← he_raw] at hne_r
      exact hne_r
    rcases hc with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · have heu : e.u = a' := by rw [← he_raw] at hu; exact hu
      have hev : e.v = w := by rw [← he_raw] at hv; exact hv
      refine ⟨{ edge := e, fwd := true } :: steps', .fwd he_mem heu (hev ▸ hsteps'), ?_⟩
      simp [PathStep.toRaw, he_raw, hmap']
    · have hev : e.v = a' := by rw [← he_raw] at hv; exact hv
      have heu : e.u = w := by rw [← he_raw] at hu; exact hu
      refine ⟨{ edge := e, fwd := false } :: steps', .bwd he_mem hev (heu ▸ hsteps'), ?_⟩
      simp [PathStep.toRaw, he_raw, hmap']

/-- Mathematical representation of a dynamic forest on `n` vertices `0, …, n - 1`. -/
structure MathForest where
  n : ℕ
  edges : List ForestEdge
  deriving DecidableEq

namespace MathForest

/-- Underlying `RawEdge` list of `F`. -/
def rawEdges (F : MathForest) : List RawEdge :=
  F.edges.map ForestEdge.toRaw

/-- Empty forest on `n` vertices. -/
def empty (n : ℕ) : MathForest :=
  ⟨n, []⟩

/-- Validity invariant of a `MathForest`: endpoints in bounds, no self-loops, distinct edge IDs,
and acyclic multigraph structure. -/
def Valid (F : MathForest) : Prop :=
  (∀ e ∈ F.edges, e.u < F.n ∧ e.v < F.n ∧ e.u ≠ e.v) ∧
  (F.edges.map ForestEdge.eid).Nodup ∧
  IsAcyclic F.rawEdges

/-- Connectivity in `F`: there is a walk between `a` and `b`. -/
def SameComp (F : MathForest) (a b : ℕ) : Prop :=
  ∃ es, IsWalk F.rawEdges a b es

/-- Order-independent equivalence of two `MathForest`s. -/
def SameState (F₁ F₂ : MathForest) : Prop :=
  F₁.n = F₂.n ∧ F₁.edges.Perm F₂.edges

theorem empty_valid (n : ℕ) : (empty n).Valid := by
  refine ⟨by simp [empty], by simp [empty], fun a es hw _ => ?_⟩
  cases hw with
  | nil _ => rfl
  | cons he _ _ => simp [empty, rawEdges] at he

theorem SameComp.refl (F : MathForest) (a : ℕ) : F.SameComp a a :=
  ⟨[], .nil a⟩

theorem SameComp.symm {F : MathForest} {a b : ℕ} (h : F.SameComp a b) : F.SameComp b a :=
  let ⟨es, hw⟩ := h
  ⟨es.reverse, hw.reverse⟩

theorem SameComp.trans {F : MathForest} {a b c : ℕ}
    (h1 : F.SameComp a b) (h2 : F.SameComp b c) : F.SameComp a c :=
  let ⟨p, hp⟩ := h1
  let ⟨q, hq⟩ := h2
  ⟨p ++ q, hp.append hq⟩

theorem SameState.refl (F : MathForest) : F.SameState F :=
  ⟨rfl, List.Perm.refl _⟩

theorem SameState.symm {F₁ F₂ : MathForest} (h : F₁.SameState F₂) : F₂.SameState F₁ :=
  ⟨h.1.symm, h.2.symm⟩

theorem SameState.trans {F₁ F₂ F₃ : MathForest} (h1 : F₁.SameState F₂) (h2 : F₂.SameState F₃) :
    F₁.SameState F₃ :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem SameState.valid_iff {F₁ F₂ : MathForest} (h : F₁.SameState F₂) :
    F₁.Valid ↔ F₂.Valid := by
  obtain ⟨hn, hp⟩ := h
  have hraw : F₁.rawEdges.Perm F₂.rawEdges := hp.map ForestEdge.toRaw
  have heid : (F₁.edges.map ForestEdge.eid).Perm (F₂.edges.map ForestEdge.eid) :=
    hp.map ForestEdge.eid
  constructor <;> rintro ⟨hb, hnd, hacyc⟩
  · refine ⟨fun e he => ?_, heid.nodup_iff.mp hnd, hacyc.mono fun z hz => hraw.symm.subset hz⟩
    rw [← hn]
    exact hb e (hp.symm.subset he)
  · refine ⟨fun e he => ?_, heid.nodup_iff.mpr hnd, hacyc.mono fun z hz => hraw.subset hz⟩
    rw [hn]
    exact hb e (hp.subset he)

theorem SameState.sameComp_iff {F₁ F₂ : MathForest} (h : F₁.SameState F₂) (a b : ℕ) :
    F₁.SameComp a b ↔ F₂.SameComp a b := by
  have hraw : F₁.rawEdges.Perm F₂.rawEdges := h.2.map ForestEdge.toRaw
  exact ⟨fun ⟨es, hw⟩ => ⟨es, hw.mono fun z hz => hraw.subset hz⟩,
    fun ⟨es, hw⟩ => ⟨es, hw.mono fun z hz => hraw.symm.subset hz⟩⟩

theorem findSteps_eq_of_isStepWalk {F : MathForest} (hV : F.Valid)
    {a b : ℕ} {steps : List PathStep} (hw : IsStepWalk F.edges a b steps)
    (hnd : (steps.map PathStep.toRaw).Nodup) :
    findSteps F.edges a b = some steps := by
  have hsome := findSteps_complete_aux F.edges.length F.edges (Nat.le_refl _) hV.2.1 hV.2.2
    F.edges (fun _ hx => hx) a b steps hw hnd (fun s _ hs => hw.mem_edges s (hs ▸ List.mem_cons_self))
  rw [Option.isSome_iff_exists] at hsome
  obtain ⟨steps', hfs⟩ := hsome
  obtain ⟨hw', hnd'⟩ := findSteps_sound hV.2.1 hfs
  have heq := isStepWalk_unique hV.2.1 hV.2.2 hw' hnd' hw hnd
  simpa [findSteps, heq] using hfs

theorem findSteps_some_of_sameComp {F : MathForest} (hV : F.Valid) {a b : ℕ}
    (h : F.SameComp a b) :
    ∃ steps, findSteps F.edges a b = some steps ∧
      IsStepWalk F.edges a b steps ∧ (steps.map PathStep.toRaw).Nodup := by
  obtain ⟨es, hw⟩ := h
  obtain ⟨es', hw', hnd', _⟩ := exists_nodup_walk_of_walk hw
  obtain ⟨steps, hsteps, hmap⟩ := exists_stepWalk_of_isWalk hV.2.2 hw' hnd'
  have hnd_s : (steps.map PathStep.toRaw).Nodup := hmap ▸ hnd'
  exact ⟨steps, findSteps_eq_of_isStepWalk hV hsteps hnd_s, hsteps, hnd_s⟩

theorem SameState.findSteps_eq {F₁ F₂ : MathForest} (h : F₁.SameState F₂) (hV₁ : F₁.Valid)
    (a b : ℕ) : findSteps F₁.edges a b = findSteps F₂.edges a b := by
  have hV₂ : F₂.Valid := h.valid_iff.mp hV₁
  cases h1 : findSteps F₁.edges a b with
  | none =>
    by_contra hne
    cases h2 : findSteps F₂.edges a b with
    | none => exact hne (by simp [h2])
    | some steps₂ =>
      obtain ⟨hw₂, hnd₂⟩ := findSteps_sound hV₂.2.1 h2
      have hw₁ : IsStepWalk F₁.edges a b steps₂ := hw₂.mono fun e he => h.2.symm.subset he
      have h1' := findSteps_eq_of_isStepWalk hV₁ hw₁ hnd₂
      rw [h1] at h1'
      simp at h1'
  | some steps₁ =>
    obtain ⟨hw₁, hnd₁⟩ := findSteps_sound hV₁.2.1 h1
    have hw₂ : IsStepWalk F₂.edges a b steps₁ := hw₁.mono fun e he => h.2.subset he
    exact (findSteps_eq_of_isStepWalk hV₂ hw₂ hnd₁).symm

theorem findSteps_self (F : MathForest) (u : ℕ) :
    findSteps F.edges u u = some [] := by
  unfold findSteps
  rw [findStepsLoop.eq_def]
  simp

theorem findSteps_reverse {F : MathForest} (hV : F.Valid) {u v : ℕ} {steps : List PathStep}
    (h : findSteps F.edges u v = some steps) :
    findSteps F.edges v u = some (steps.reverse.map PathStep.flip) := by
  obtain ⟨hw, hnd⟩ := findSteps_sound hV.2.1 h
  have hnd_rev : ((steps.reverse.map PathStep.flip).map PathStep.toRaw).Nodup := by
    have hmap : (steps.reverse.map PathStep.flip).map PathStep.toRaw =
        (steps.map PathStep.toRaw).reverse := by
      simp [List.map_map, Function.comp_def, List.map_reverse]
    rw [hmap, List.nodup_reverse]
    exact hnd
  exact findSteps_eq_of_isStepWalk hV hw.reverse hnd_rev

/-- `FindRoot`: smallest reachable vertex in `0, …, n - 1` (or `v` if out of bounds). -/
def findRoot (F : MathForest) (v : ℕ) : ℕ :=
  ((List.range F.n).find? fun r => (findSteps F.edges v r).isSome).getD v

theorem findRoot_lt {F : MathForest} (_hV : F.Valid) {v : ℕ} (hv : v < F.n) :
    F.findRoot v < F.n := by
  unfold findRoot
  cases h : (List.range F.n).find? fun r => (findSteps F.edges v r).isSome with
  | none => exact hv
  | some r =>
    have hmem := List.mem_of_find?_eq_some h
    simpa [List.mem_range] using hmem

theorem findRoot_eq_iff {F : MathForest} (hV : F.Valid) {u v : ℕ}
    (hu : u < F.n) (hv : v < F.n) :
    F.findRoot u = F.findRoot v ↔ F.SameComp u v := by
  have hreach_iff : ∀ x r, r < F.n →
      ((findSteps F.edges x r).isSome = true ↔ F.SameComp x r) := by
    intro x r _
    constructor
    · intro h
      rw [Option.isSome_iff_exists] at h
      obtain ⟨steps, hfs⟩ := h
      obtain ⟨hw, _⟩ := findSteps_sound hV.2.1 hfs
      exact ⟨_, hw.to_isWalk⟩
    · intro hsc
      obtain ⟨steps, hfs, _⟩ := findSteps_some_of_sameComp hV hsc
      simp [hfs]
  have hfind_spec : ∀ x, x < F.n →
      ∃ r, (List.range F.n).find? (fun r => (findSteps F.edges x r).isSome) = some r ∧
        r < F.n ∧ F.SameComp x r ∧ ∀ r' < r, ¬ F.SameComp x r' := by
    intro x hx
    have hex : ∃ r ∈ List.range F.n, (findSteps F.edges x r).isSome = true :=
      ⟨x, List.mem_range.mpr hx, by simp [findSteps_self]⟩
    have hnot_none : (List.range F.n).find? (fun r => (findSteps F.edges x r).isSome) ≠ none := by
      intro hnone
      obtain ⟨r, hr_mem, hr_sat⟩ := hex
      exact absurd hr_sat (by simpa using List.find?_eq_none.mp hnone r hr_mem)
    cases hf : (List.range F.n).find? (fun r => (findSteps F.edges x r).isSome) with
    | none => exact (hnot_none hf).elim
    | some r =>
      have hr_mem : r ∈ List.range F.n := List.mem_of_find?_eq_some hf
      have hr_lt : r < F.n := List.mem_range.mp hr_mem
      have hr_sat : (findSteps F.edges x r).isSome = true :=
        List.find?_some (p := fun r => (findSteps F.edges x r).isSome) hf
      refine ⟨r, rfl, hr_lt, (hreach_iff x r hr_lt).mp hr_sat, fun r' hr' hsc' => ?_⟩
      have hr'_lt : r' < F.n := Nat.lt_trans hr' hr_lt
      have hr'_sat : (findSteps F.edges x r').isSome = true :=
        (hreach_iff x r' hr'_lt).mpr hsc'
      have hf_min := List.find?_eq_some_iff_append.mp hf
      obtain ⟨_, p, q, hrange_eq, hp_not⟩ := hf_min
      have hpw : (List.range F.n).Pairwise (· < ·) := List.pairwise_lt_range
      rw [hrange_eq] at hpw
      have hr_lt_q : ∀ y ∈ q, r < y := by
        have := (List.pairwise_append.mp hpw).2.1
        rw [List.pairwise_cons] at this
        exact this.1
      have hr'_in_app : r' ∈ p ++ r :: q := hrange_eq ▸ List.mem_range.mpr hr'_lt
      have hr'_mem : r' ∈ p := by
        rcases List.mem_append.mp hr'_in_app with hr'_p | hr'_tail
        · exact hr'_p
        · rcases List.mem_cons.mp hr'_tail with rfl | hr'_q
          · exact absurd hr' (Nat.lt_irrefl _)
          · exact absurd (Nat.lt_trans hr' (hr_lt_q r' hr'_q)) (Nat.lt_irrefl _)
      have hnot_r' := hp_not r' hr'_mem
      simp [hr'_sat] at hnot_r'
  obtain ⟨ru, hru_find, hru_lt, hru_sc, hru_min⟩ := hfind_spec u hu
  obtain ⟨rv, hrv_find, hrv_lt, hrv_sc, hrv_min⟩ := hfind_spec v hv
  have hfu : F.findRoot u = ru := by simp [findRoot, hru_find]
  have hfv : F.findRoot v = rv := by simp [findRoot, hrv_find]
  rw [hfu, hfv]
  constructor
  · intro heq
    subst heq
    exact hru_sc.trans hrv_sc.symm
  · intro huv
    have hvu : F.SameComp v u := huv.symm
    have h1 : rv ≤ ru := by
      by_contra hlt
      push Not at hlt
      exact hrv_min ru hlt (hvu.trans hru_sc)
    have h2 : ru ≤ rv := by
      by_contra hlt
      push Not at hlt
      exact hru_min rv hlt (huv.trans hrv_sc)
    omega

/-- `Link`: add edge `e` to `F`. -/
def link (F : MathForest) (e : ForestEdge) : MathForest :=
  { F with edges := e :: F.edges }

theorem link_valid {F : MathForest} (hV : F.Valid) {e : ForestEdge}
    (hu : e.u < F.n) (hv : e.v < F.n) (hdisc : ¬ F.SameComp e.u e.v)
    (heid : ∀ e' ∈ F.edges, e'.eid ≠ e.eid) :
    (F.link e).Valid := by
  have hne : e.u ≠ e.v := fun h => hdisc (h ▸ SameComp.refl F e.u)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hu, hv, hne⟩
    · exact hV.1 x hx
  · rw [link, List.map_cons, List.nodup_cons]
    refine ⟨?_, hV.2.1⟩
    intro hm
    rw [List.mem_map] at hm
    obtain ⟨e', he', heq⟩ := hm
    exact heid e' he' heq
  · exact hV.2.2.link hne (fun es hw => hdisc ⟨es, hw⟩)

/-- `Cut`: remove the edge between `x` and `y`. -/
def cut (F : MathForest) (x y : ℕ) : MathForest :=
  { F with edges := F.edges.filter fun e => !((e.u == x && e.v == y) || (e.u == y && e.v == x)) }

theorem cut_valid {F : MathForest} (hV : F.Valid) (x y : ℕ) :
    (F.cut x y).Valid := by
  refine ⟨fun e he => hV.1 e (List.mem_of_mem_filter he), ?_, ?_⟩
  · exact (List.filter_sublist.map ForestEdge.eid).nodup hV.2.1
  · exact hV.2.2.mono fun z hz => by
      unfold rawEdges at hz ⊢
      rw [List.mem_map] at hz ⊢
      obtain ⟨e, he, rfl⟩ := hz
      exact ⟨e, List.mem_of_mem_filter he, rfl⟩

/-- `PathSum`: sum of signed edge costs along the path `u → v`. -/
def pathSum (F : MathForest) (u v : ℕ) : ℤ :=
  match findSteps F.edges u v with
  | none => 0
  | some steps => stepsCost steps

/-- `PathMin`: minimum-availability edge along `u → v` (breaking ties closest to `u`). -/
def pathMin (F : MathForest) (u v : ℕ) : Option PathHit :=
  (findSteps F.edges u v).bind stepsMinHit

/-- Update an edge `e` by looking up its `eid` in `steps`. -/
def applyStepsDelta (steps : List PathStep) (δ : ℚ) (e : ForestEdge) : ForestEdge :=
  match steps.find? fun s => s.edge.eid == e.eid with
  | none => e
  | some s => e.addFlow s.fwd δ

/-- `PathAdd`: push `δ` units of flow along the path `u → v`. -/
def pathAdd (F : MathForest) (u v : ℕ) (δ : ℚ) : MathForest :=
  match findSteps F.edges u v with
  | none => F
  | some steps => { F with edges := F.edges.map (applyStepsDelta steps δ) }

end MathForest

end MinCostFlow.Rounding
