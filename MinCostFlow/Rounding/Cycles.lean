module

public import MinCostFlow.Rounding.Algorithm
public import MinCostFlow.Rounding.Rounding
import Mathlib.Tactic.Ring

/-!
# Loop invariant and cycle-cancelling step proof (Kang–Payor Section 4)

This file defines `LoopInv`, the loop invariant of the Section 4 flow-rounding algorithm
(`roundFlowLoop`), and proves `roundEdgeStep_preserves`: each edge iteration preserves demand
routing, feasibility (via `[⌊f_e⌋, ⌈f_e⌉]` bounds), non-increasing cost (via
`costed_cycle_cancel` applied to the tree-path cycle circulation), strict fractionality of edges
remaining in the dynamic forest, exact operation count bounds, fixed-point `2^{-P}` closure, and
magnitude bounds on computed rationals and costs.
-/

@[expose] public section

namespace MinCostFlow.Rounding

private theorem le_foldr_max_of_mem : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ≤ l.foldr max 0 := by
  intro l x hx
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_max_left _ _
    · exact le_trans (ih hx) (Nat.le_max_right _ _)

theorem edge_cost_abs_le_maxCost (I : Instance) (j : Fin I.m) :
    |(I.edge j).cost| ≤ (I.maxCost : ℤ) := by
  have hmem : (I.edge j).cost.natAbs ∈ I.edges.map fun e => e.cost.natAbs :=
    List.mem_map_of_mem (List.getElem_mem j.2)
  have hle : (I.edge j).cost.natAbs ≤ I.maxCost := le_foldr_max_of_mem hmem
  have habs : |(I.edge j).cost| = ((I.edge j).cost.natAbs : ℤ) := Int.abs_eq_natAbs _
  linarith [Int.ofNat_le.mpr hle]

/-- Every edge `s` on `steps` is updated by `pathAdd a b δ` to `s.edge.addFlow s.fwd δ`, so
`findSteps` on `(F.pathAdd a b δ).edges` returns the mapped step list. -/
theorem pathAdd_findSteps {F : MathForest} (hV : F.Valid) {a b : ℕ}
    {steps : List PathStep} (hfs : findSteps F.edges a b = some steps) (δ : ℚ) :
    findSteps (F.pathAdd a b δ).edges a b =
      some (steps.map fun s => { s with edge := s.edge.addFlow s.fwd δ }) := by
  have hV' := F.pathAdd_valid hV a b δ
  obtain ⟨hw, hnd⟩ := findSteps_sound hV.2.1 hfs
  let steps' := steps.map fun s => { s with edge := s.edge.addFlow s.fwd δ }
  have hmem' : ∀ s ∈ steps, s.edge.addFlow s.fwd δ ∈ (F.pathAdd a b δ).edges := by
    intro s hs
    have he_in : s.edge ∈ F.edges := hw.mem_edges s hs
    have happ := MathForest.applyStepsDelta_of_mem hV hfs δ hs
    have hmem_map : MathForest.applyStepsDelta steps δ s.edge ∈
        F.edges.map (MathForest.applyStepsDelta steps δ) := List.mem_map_of_mem he_in
    rw [happ] at hmem_map
    simpa [MathForest.pathAdd, hfs] using hmem_map
  have hw' : IsStepWalk (F.pathAdd a b δ).edges a b steps' := by
    have haux : ∀ {edges' : List ForestEdge} {x y : ℕ} {l : List PathStep},
        IsStepWalk F.edges x y l → (∀ s ∈ l, s.edge.addFlow s.fwd δ ∈ edges') →
        IsStepWalk edges' x y (l.map fun s => { s with edge := s.edge.addFlow s.fwd δ }) := by
      intro edges' x y l hwl hml
      induction hwl with
      | nil z => exact .nil z
      | @fwd u v e rest _ hu _ ih =>
        have he' := hml { edge := e, fwd := true } List.mem_cons_self
        exact .fwd he' (by simpa using hu) (ih fun s hs => hml s (List.mem_cons_of_mem _ hs))
      | @bwd u v e rest _ hv _ ih =>
        have he' := hml { edge := e, fwd := false } List.mem_cons_self
        exact .bwd he' (by simpa using hv) (ih fun s hs => hml s (List.mem_cons_of_mem _ hs))
    exact haux hw hmem'
  have hnd' : (steps'.map PathStep.toRaw).Nodup := by
    have hmap : steps'.map PathStep.toRaw = steps.map PathStep.toRaw := by
      simp [steps', List.map_map, Function.comp_def, PathStep.toRaw]
    rw [hmap]
    exact hnd
  exact MathForest.findSteps_eq_of_isStepWalk hV' hw' hnd'

/-- Signed cost along a walk is bounded by `steps.length * maxCost`. -/
theorem stepsCost_abs_le {I : Instance} {f : Fin I.m → ℚ} {steps : List PathStep}
    (hWeak : ∀ s ∈ steps, ForestEdgeWeakInv I f s.edge) :
    |stepsCost steps| ≤ (steps.length : ℤ) * (I.maxCost : ℤ) := by
  induction steps with
  | nil => simp [stepsCost]
  | cons s rest ih =>
    have hs := hWeak s List.mem_cons_self
    obtain ⟨j, _, _, _, hcost, _⟩ := hs
    have hsc : |s.signedCost| ≤ (I.maxCost : ℤ) := by
      have hc := edge_cost_abs_le_maxCost I j
      cases hf : s.fwd <;> simp [PathStep.signedCost, hf, hcost, abs_neg] <;> exact hc
    have ihr := ih (fun t ht => hWeak t (List.mem_cons_of_mem _ ht))
    have hadd : stepsCost (s :: rest) = s.signedCost + stepsCost rest := by
      simp [stepsCost]
    rw [hadd]
    have htri := abs_add_le s.signedCost (stepsCost rest)
    have hmul : ((s :: rest).length : ℤ) * (I.maxCost : ℤ) =
        (I.maxCost : ℤ) + (rest.length : ℤ) * (I.maxCost : ℤ) := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
    linarith

/-- Loop invariant at step `k ≤ I.m`: edges `0, …, k - 1` have been processed. -/
def LoopInv (D : DynForest) (I : Instance) (f : Fin I.m → ℚ)
    (P : ℕ) (M : ℚ) (k : ℕ) (st : RoundState D I) : Prop :=
  D.Inv st.df ∧
  (D.toForest st.df).n = I.n ∧
  (∀ e ∈ (D.toForest st.df).edges, ForestEdgeStrictInv I f e ∧ e.eid < k) ∧
  (∀ j : Fin I.m, j.1 < k → j.1 ∉ (D.toForest st.df).edges.map ForestEdge.eid →
    ∃ z : ℤ, st.flowArr j = z) ∧
  (∀ j : Fin I.m, k ≤ j.1 →
    j.1 ∉ (D.toForest st.df).edges.map ForestEdge.eid ∧ st.flowArr j = f j) ∧
  I.Routes (fun j => (actualFlow (D.toForest st.df) st.flowArr j : ℝ)) ∧
  (∀ j : Fin I.m,
    (⌊f j⌋ : ℚ) ≤ actualFlow (D.toForest st.df) st.flowArr j ∧
    actualFlow (D.toForest st.df) st.flowArr j ≤ (⌈f j⌉ : ℚ)) ∧
  I.cost (fun j => (actualFlow (D.toForest st.df) st.flowArr j : ℝ)) ≤
    I.cost (fun j => (f j : ℝ)) ∧
  st.counts.findRootOps ≤ 2 * k ∧
  st.counts.linkOps ≤ k ∧
  st.counts.cutOps + (D.toForest st.df).edges.length = st.counts.linkOps ∧
  st.counts.pathSumOps ≤ k ∧
  st.counts.pathAddOps ≤ k ∧
  st.counts.pathMinOps ≤ 2 * k + 2 * st.counts.cutOps ∧
  st.counts.otherSteps ≤ 14 * k + 5 * st.counts.cutOps ∧
  ((∀ j, IsFixedPoint P (f j)) →
    (∀ e ∈ (D.toForest st.df).edges,
      IsFixedPoint P e.flow ∧ IsFixedPoint P e.availFwd ∧ IsFixedPoint P e.availBwd) ∧
    (∀ j, IsFixedPoint P (st.flowArr j)) ∧
    (∀ q ∈ st.computedRats, IsFixedPoint P q)) ∧
  ((∀ j, |f j| + 1 ≤ M) →
    (∀ q ∈ st.computedRats, |q| ≤ M) ∧
    (∀ j, |st.flowArr j| ≤ M)) ∧
  (∀ c ∈ st.computedCosts, |c| ≤ (min I.n I.m : ℤ) * (I.maxCost : ℤ))

private theorem stepEdge_eq_of_eid {es : List ForestEdge} (hnd : (es.map ForestEdge.eid).Nodup)
    {e₁ e₂ : ForestEdge} (h₁ : e₁ ∈ es) (h₂ : e₂ ∈ es) (heid : e₁.eid = e₂.eid) :
    e₁ = e₂ := by
  induction es with
  | nil => simp at h₁
  | cons z zs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h₁ with h1 | h1 <;> rcases List.mem_cons.mp h₂ with h2 | h2
    · exact h1.trans h2.symm
    · exact absurd (h1 ▸ heid ▸ List.mem_map_of_mem h2) hnd.1
    · exact absurd (h2 ▸ heid.symm ▸ List.mem_map_of_mem h1) hnd.1
    · exact ih hnd.2 h1 h2

/-- Telescoping vertex-incidence sum along a `IsStepWalk`. -/
private theorem stepWalk_incidence_sum {F : MathForest} {a b : ℕ} {steps : List PathStep}
    (hw : IsStepWalk F.edges a b steps) (w : ℕ) :
    (steps.map fun s =>
      ((if w = s.edge.u then (1 : ℝ) else 0) - (if w = s.edge.v then 1 else 0)) *
        (if s.fwd then 1 else -1)).sum =
    (if w = a then (1 : ℝ) else 0) - (if w = b then (1 : ℝ) else 0) := by
  induction hw with
  | nil x => simp
  | @fwd x y e rest _ hu _ ih =>
    simp only [List.map_cons, List.sum_cons, ↓reduceIte, mul_one, hu] at ih ⊢
    linarith
  | @bwd x y e rest _ hv _ ih =>
    simp only [List.map_cons, List.sum_cons, Bool.false_eq_true, ↓reduceIte, hv] at ih ⊢
    linarith

private theorem eid_nodup_of_steps {F : MathForest} (hV : F.Valid)
    {a b : ℕ} {steps : List PathStep} (hfs : findSteps F.edges a b = some steps) :
    (steps.map fun s => s.edge.eid).Nodup := by
  obtain ⟨hw, hnd⟩ := findSteps_sound hV.2.1 hfs
  have hmem : ∀ s ∈ steps, s.edge ∈ F.edges := hw.mem_edges
  clear hfs hw
  induction steps with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd ⊢
    refine ⟨fun hm => ?_, ih hnd.2 (fun s hs => hmem s (List.mem_cons_of_mem _ hs))⟩
    rw [List.mem_map] at hm
    obtain ⟨t, ht, heid⟩ := hm
    have heq_e : t.edge = x.edge :=
      stepEdge_eq_of_eid hV.2.1 (hmem t (List.mem_cons_of_mem _ ht)) (hmem x List.mem_cons_self) heid
    exact hnd.1 (List.mem_map.mpr ⟨t, ht, by simp [PathStep.toRaw, heq_e]⟩)

private theorem sum_cycle_aux {I : Instance} (j : Fin I.m)
    (g : Fin I.m → ℝ) (val : PathStep → ℝ) (c0 : ℝ) (c : Fin I.m → ℝ)
    (l : List PathStep) (hnd_eid : (l.map fun s => s.edge.eid).Nodup)
    (hlt : ∀ s ∈ l, s.edge.eid < j.1)
    (hstep : ∀ s ∈ l, ∀ k : Fin I.m, k.1 = s.edge.eid →
      g k * (if s.fwd then (1 : ℝ) else -1) = val s)
    (hc : ∀ k, c k = if k = j then c0 else
      match l.find? fun s => s.edge.eid == k.1 with
      | none => 0
      | some s => if s.fwd then 1 else -1) :
    ∑ k : Fin I.m, g k * c k = g j * c0 + (l.map val).sum := by
  have hsplit : ∑ k : Fin I.m, g k * c k =
      g j * c j + ∑ k ∈ Finset.univ.erase j, g k * c k :=
    (Finset.add_sum_erase Finset.univ (fun k => g k * c k) (Finset.mem_univ j)).symm
  rw [hsplit]
  have hcj : c j = c0 := by rw [hc j, ite_eq_left rfl]
  rw [hcj]
  congr 1
  have hcongr_erase : ∑ k ∈ Finset.univ.erase j, g k * c k =
      ∑ k ∈ Finset.univ.erase j, g k *
        (match l.find? fun s => s.edge.eid == k.1 with
          | none => 0 | some s => if s.fwd then 1 else -1) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hc k, ite_eq_right (Finset.mem_erase.mp hk).1]
  rw [hcongr_erase]
  suffices gen : ∀ (xs : List PathStep) (S : Finset (Fin I.m)),
      (xs.map fun s => s.edge.eid).Nodup →
      (∀ s ∈ xs, ∀ k : Fin I.m, k.1 = s.edge.eid →
        g k * (if s.fwd then (1 : ℝ) else -1) = val s) →
      (∀ s ∈ xs, ∃ k ∈ S, k.1 = s.edge.eid) →
      ∑ k ∈ S, g k * (match xs.find? fun s => s.edge.eid == k.1 with
        | none => 0 | some s => if s.fwd then 1 else -1) =
      (xs.map val).sum by
    exact gen l (Finset.univ.erase j) hnd_eid hstep fun s hs =>
      ⟨⟨s.edge.eid, Nat.lt_trans (hlt s hs) j.2⟩,
        Finset.mem_erase.mpr ⟨fun h => (ne_of_lt (hlt s hs)) (congrArg Fin.val h), Finset.mem_univ _⟩,
        rfl⟩
  intro xs S
  induction xs generalizing S with
  | nil => intro _ _ _; simp
  | cons s rest ih =>
    intro hnd_xs hstep_xs hcov
    rw [List.map_cons, List.nodup_cons] at hnd_xs
    obtain ⟨ks, hks_mem, hks_eq⟩ := hcov s List.mem_cons_self
    rw [← Finset.add_sum_erase S _ hks_mem]
    have hhead : g ks * (match (s :: rest).find? (fun t => t.edge.eid == ks.1) with
        | none => 0 | some t => if t.fwd then 1 else -1) = val s := by
      simp [hks_eq, hstep_xs s List.mem_cons_self ks hks_eq]
    rw [hhead, List.map_cons, List.sum_cons]
    congr 1
    have hcongr_tail : ∑ k ∈ S.erase ks, g k *
        (match (s :: rest).find? (fun t => t.edge.eid == k.1) with
          | none => (0 : ℝ) | some t => if t.fwd then 1 else -1) =
        ∑ k ∈ S.erase ks, g k *
        (match rest.find? (fun t => t.edge.eid == k.1) with
          | none => 0 | some t => if t.fwd then 1 else -1) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hne_eid : s.edge.eid ≠ k.1 := fun h =>
        (Finset.mem_erase.mp hk).1 (Fin.ext (h.symm.trans hks_eq.symm))
      have hbeq : (s.edge.eid == k.1) = false := beq_eq_false_iff_ne.mpr hne_eid
      simp [List.find?, hbeq]
    rw [hcongr_tail]
    exact ih (S.erase ks) hnd_xs.2
      (fun t ht => hstep_xs t (List.mem_cons_of_mem _ ht))
      fun t ht => by
        obtain ⟨k, hkS, hk_eq⟩ := hcov t (List.mem_cons_of_mem _ ht)
        refine ⟨k, Finset.mem_erase.mpr ⟨?_, hkS⟩, hk_eq⟩
        intro hkeq
        apply hnd_xs.1
        have hteq : t.edge.eid = s.edge.eid := hk_eq.symm.trans ((congrArg Fin.val hkeq).trans hks_eq)
        rw [← hteq]
        exact List.mem_map_of_mem ht

/-- Key cycle-push lemma: given a simple step walk `steps` from `a` to `b` in `df` (where
either `a = v, b = u, signJ = 1` or `a = u, b = v, signJ = -1`), pushing `δ > 0` along `a → b`
in `df` and `signJ * δ` on edge `j` updates `actualFlow` by a circulation of non-positive cost,
preserves `I.Routes` and `[⌊f k⌋, ⌈f k⌉]` bounds, does not increase `I.cost`, and leaves
`steps₁` in `df₁ := D.pathAdd df a b δ` ready for `removeZeroEdges`. -/
private theorem pushCycle_preserves {D : DynForest} (hSpec : D.IsSpec) {I : Instance}
    {f : Fin I.m → ℚ} {df : D.State} {flowArr : Fin I.m → ℚ}
    (hInv : D.Inv df) (hStrict : ∀ e ∈ (D.toForest df).edges, ForestEdgeStrictInv I f e)
    (hRoutes : I.Routes (fun k => (actualFlow (D.toForest df) flowArr k : ℝ)))
    (hBounds : ∀ k : Fin I.m,
      (⌊f k⌋ : ℚ) ≤ actualFlow (D.toForest df) flowArr k ∧
      actualFlow (D.toForest df) flowArr k ≤ (⌈f k⌉ : ℚ))
    {j : Fin I.m} (hj_not : j.1 ∉ (D.toForest df).edges.map ForestEdge.eid)
    (hj_eq : flowArr j = f j)
    {a b : ℕ} {steps : List PathStep}
    (hfs : findSteps (D.toForest df).edges a b = some steps)
    (hlt : ∀ s ∈ steps, s.edge.eid < j.1)
    (signJ : ℤ)
    (hEnds : (a = (I.edge j).head ∧ b = (I.edge j).tail ∧ signJ = 1) ∨
             (a = (I.edge j).tail ∧ b = (I.edge j).head ∧ signJ = -1))
    {δ : ℚ} (hδ_pos : 0 < δ)
    (hδ_j : (signJ = 1 ∧ δ ≤ (⌈f j⌉ : ℚ) - f j) ∨ (signJ = -1 ∧ δ ≤ f j - (⌊f j⌋ : ℚ)))
    (hδ_steps : ∀ s ∈ steps, δ ≤ s.dirAvail)
    (hCost : stepsCost steps + signJ * (I.edge j).cost ≤ 0) :
    let newFlow := f j + (signJ : ℚ) * δ
    let flowArr₁ := fun k : Fin I.m => if k = j then newFlow else flowArr k
    let df₁ := D.pathAdd df a b δ
    let steps₁ := steps.map fun s => { s with edge := s.edge.addFlow s.fwd δ }
    D.Inv df₁ ∧
    findSteps (D.toForest df₁).edges a b = some steps₁ ∧
    (∀ e ∈ (D.toForest df₁).edges, ForestEdgeWeakInv I f e) ∧
    (∀ e ∈ (D.toForest df₁).edges, (∀ s ∈ steps₁, s.edge ≠ e) → ForestEdgeStrictInv I f e) ∧
    (∀ s ∈ steps₁, 0 ≤ s.dirAvail ∧ 0 < s.flip.dirAvail) ∧
    I.Routes (fun k => (actualFlow (D.toForest df₁) flowArr₁ k : ℝ)) ∧
    (∀ k : Fin I.m,
      (⌊f k⌋ : ℚ) ≤ actualFlow (D.toForest df₁) flowArr₁ k ∧
      actualFlow (D.toForest df₁) flowArr₁ k ≤ (⌈f k⌉ : ℚ)) ∧
    I.cost (fun k => (actualFlow (D.toForest df₁) flowArr₁ k : ℝ)) ≤
      I.cost (fun k => (actualFlow (D.toForest df) flowArr k : ℝ)) := by
  intro newFlow flowArr₁ df₁ steps₁
  have hV : (D.toForest df).Valid := hSpec.2.1 df hInv
  obtain ⟨hw, _⟩ := findSteps_sound hV.2.1 hfs
  have hconn : (D.toForest df).SameComp a b := ⟨_, hw.to_isWalk⟩
  obtain ⟨hInv₁, hSame₁⟩ := hSpec.2.2.2.2.2.1 df a b δ hInv hconn
  have hV₁ : (D.toForest df₁).Valid := hSpec.2.1 df₁ hInv₁
  have hV_pa : ((D.toForest df).pathAdd a b δ).Valid := (D.toForest df).pathAdd_valid hV a b δ
  have hfs_pa := pathAdd_findSteps hV hfs δ
  have hfs₁ : findSteps (D.toForest df₁).edges a b = some steps₁ := by
    rw [hSame₁.findSteps_eq hV₁]
    exact hfs_pa
  have hnd_eid := eid_nodup_of_steps hV hfs
  have hmem_pa_iff : ∀ e' ∈ ((D.toForest df).pathAdd a b δ).edges,
      ∃ e ∈ (D.toForest df).edges, e' = MathForest.applyStepsDelta steps δ e := by
    intro e' he'
    simp only [MathForest.pathAdd, hfs, List.mem_map] at he'
    obtain ⟨e, he, heq⟩ := he'
    exact ⟨e, he, heq.symm⟩
  have hWeak₁ : ∀ e' ∈ (D.toForest df₁).edges, ForestEdgeWeakInv I f e' := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := hmem_pa_iff e' (hSame₁.2.subset he')
    have hs_strict := hStrict e he
    by_cases hin : ∃ s ∈ steps, s.edge = e
    · obtain ⟨s, hs_mem, rfl⟩ := hin
      rw [MathForest.applyStepsDelta_of_mem hV hfs δ hs_mem]
      obtain ⟨⟨k, heid, hu, hv, hcost, hfrac, hlo, hhi, hfwd, hbwd⟩, hpf, hpb⟩ := hs_strict
      have hδ_s := hδ_steps s hs_mem
      refine ⟨k, by simp [heid], by simp [hu], by simp [hv], by simp [hcost], hfrac, ?_⟩
      rcases sf : s.fwd with _ | _
      · simp [PathStep.dirAvail, sf] at hδ_s
        simp [ForestEdge.addFlow]
        refine ⟨by linarith, by linarith, by linarith, by linarith⟩
      · simp [PathStep.dirAvail, sf] at hδ_s
        simp [ForestEdge.addFlow]
        refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · push Not at hin
      rw [MathForest.applyStepsDelta_of_not_mem hV hfs δ he hin]
      exact hs_strict.1
  have hOff₁ : ∀ e' ∈ (D.toForest df₁).edges,
      (∀ s ∈ steps₁, s.edge ≠ e') → ForestEdgeStrictInv I f e' := by
    intro e' he' hnot
    obtain ⟨e, he, rfl⟩ := hmem_pa_iff e' (hSame₁.2.subset he')
    have hin : ∀ s ∈ steps, s.edge ≠ e := by
      intro s hs heq
      apply hnot { s with edge := s.edge.addFlow s.fwd δ } (List.mem_map_of_mem hs)
      dsimp only
      rw [← MathForest.applyStepsDelta_of_mem hV hfs δ hs, heq]
    rw [MathForest.applyStepsDelta_of_not_mem hV hfs δ he hin]
    exact hStrict e he
  have hPath₁ : ∀ s ∈ steps₁, 0 ≤ s.dirAvail ∧ 0 < s.flip.dirAvail := by
    intro s₁ hs₁
    rw [List.mem_map] at hs₁
    obtain ⟨s, hs_mem, rfl⟩ := hs₁
    have hs_strict := hStrict s.edge (hw.mem_edges s hs_mem)
    have hδ_s := hδ_steps s hs_mem
    cases sf : s.fwd
    · simp [PathStep.dirAvail, PathStep.flip, ForestEdge.addFlow, sf] at hδ_s ⊢
      exact ⟨by linarith, by linarith [hs_strict.2.1]⟩
    · simp [PathStep.dirAvail, PathStep.flip, ForestEdge.addFlow, sf] at hδ_s ⊢
      exact ⟨by linarith, by linarith [hs_strict.2.2]⟩
  let Δ : Fin I.m → ℝ := fun k =>
    if k = j then (signJ : ℝ)
    else match steps.find? fun s => s.edge.eid == k.1 with
      | none => 0
      | some s => if s.fwd then 1 else -1
  have hWeak_steps : ∀ s ∈ steps, ForestEdgeWeakInv I f s.edge :=
    fun s hs => (hStrict s.edge (hw.mem_edges s hs)).1
  have hCirc : IsCirculation I Δ := by
    intro w
    let val : PathStep → ℝ := fun s =>
      ((if (w : ℕ) = s.edge.u then (1 : ℝ) else 0) -
        (if (w : ℕ) = s.edge.v then 1 else 0)) * (if s.fwd then 1 else -1)
    have hstep_w : ∀ s ∈ steps, ∀ k : Fin I.m, k.1 = s.edge.eid →
        (I.edge k).b w * (if s.fwd then (1 : ℝ) else -1) = val s := by
      intro s hs k hk
      obtain ⟨k', heid', hu', hv', _⟩ := hWeak_steps s hs
      have hkk' : k = k' := Fin.ext (hk.trans heid')
      rw [hkk']
      simp only [Edge.b, val, hu', hv']
    have hsum := sum_cycle_aux j (fun k => (I.edge k).b w) val (signJ : ℝ) Δ steps
      hnd_eid hlt hstep_w (fun _ => rfl)
    rw [hsum, stepWalk_incidence_sum hw (w : ℕ)]
    rcases hEnds with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp [Edge.b]
    · simp [Edge.b]
  have hCost_Δ : I.cost Δ ≤ 0 := by
    unfold Instance.cost
    let val : PathStep → ℝ := fun s => (s.signedCost : ℝ)
    have hstep_c : ∀ s ∈ steps, ∀ k : Fin I.m, k.1 = s.edge.eid →
        ((I.edge k).cost : ℝ) * (if s.fwd then (1 : ℝ) else -1) = val s := by
      intro s hs k hk
      obtain ⟨k', heid', _, _, hcost', _⟩ := hWeak_steps s hs
      have hkk' : k = k' := Fin.ext (hk.trans heid')
      rw [hkk']
      simp only [val, ← hcost']
      cases hf : s.fwd <;> simp [PathStep.signedCost, hf]
    have hsum := sum_cycle_aux j (fun k => ((I.edge k).cost : ℝ)) val (signJ : ℝ) Δ steps
      hnd_eid hlt hstep_c (fun _ => rfl)
    rw [hsum]
    have hcost_eq : (steps.map val).sum = (stepsCost steps : ℝ) := by
      have aux : ∀ l : List PathStep, (l.map val).sum = (stepsCost l : ℝ) := by
        intro l
        induction l with
        | nil => simp [stepsCost, val]
        | cons s rest ih =>
          simp only [List.map_cons, List.sum_cons, val] at ih ⊢
          unfold stepsCost at ih ⊢
          simp only [List.map_cons, List.sum_cons, Int.cast_add] at ih ⊢
          rw [ih]
      exact aux steps
    rw [hcost_eq]
    have hcast : ((I.edge j).cost : ℝ) * (signJ : ℝ) + (stepsCost steps : ℝ) =
        ((stepsCost steps + signJ * (I.edge j).cost : ℤ) : ℝ) := by
      push_cast; ring
    rw [hcast]
    exact_mod_cast hCost
  have hact_eq : ∀ k : Fin I.m,
      (actualFlow (D.toForest df₁) flowArr₁ k : ℝ) =
      (actualFlow (D.toForest df) flowArr k : ℝ) + (δ : ℝ) * Δ k := by
    intro k
    rw [actualFlow_sameState hSame₁ hV₁ flowArr₁ k]
    by_cases hkj : k = j
    · subst hkj
      have hk_not_pa : k.1 ∉ ((D.toForest df).pathAdd a b δ).edges.map ForestEdge.eid := by
        simp only [MathForest.pathAdd, hfs, List.map_map, Function.comp_def]
        intro hm
        rw [List.mem_map] at hm
        obtain ⟨e, he, heq⟩ := hm
        have heid_eq : (MathForest.applyStepsDelta steps δ e).eid = e.eid := by
          unfold MathForest.applyStepsDelta
          cases steps.find? fun s => s.edge.eid == e.eid with
          | none => rfl
          | some s => simp
        rw [heid_eq] at heq
        exact hj_not (heq ▸ List.mem_map_of_mem he)
      rw [actualFlow_of_not_mem flowArr₁ hk_not_pa, actualFlow_of_not_mem flowArr hj_not]
      dsimp [flowArr₁, newFlow, Δ]
      rw [ite_eq_left rfl, ite_eq_left rfl, hj_eq]
      push_cast
      ring
    · have hflow_k : flowArr₁ k = flowArr k := by dsimp [flowArr₁]; rw [ite_eq_right hkj]
      by_cases hk_in : k.1 ∈ (D.toForest df).edges.map ForestEdge.eid
      · rw [List.mem_map] at hk_in
        obtain ⟨e, he, hek⟩ := hk_in
        have hact_before : actualFlow (D.toForest df) flowArr k = e.flow :=
          actualFlow_of_mem hV.2.1 flowArr he hek
        let e' := MathForest.applyStepsDelta steps δ e
        have he'_in : e' ∈ ((D.toForest df).pathAdd a b δ).edges := by
          simp only [MathForest.pathAdd, hfs, List.mem_map]
          exact ⟨e, he, rfl⟩
        have he'_eid : e'.eid = k.1 := by
          dsimp [e', MathForest.applyStepsDelta]
          cases steps.find? fun s => s.edge.eid == e.eid with
          | none => exact hek
          | some s => simp [hek]
        have hact_after : actualFlow ((D.toForest df).pathAdd a b δ) flowArr₁ k = e'.flow :=
          actualFlow_of_mem hV_pa.2.1 flowArr₁ he'_in he'_eid
        rw [hact_after, hact_before]
        dsimp [Δ]
        rw [ite_eq_right hkj]
        by_cases hmem_s : ∃ s ∈ steps, s.edge = e
        · obtain ⟨s, hs_mem, rfl⟩ := hmem_s
          have happ := MathForest.applyStepsDelta_of_mem hV hfs δ hs_mem
          have hfind : steps.find? (fun t => t.edge.eid == k.1) = some s := by
            rw [← hek]
            have aux : ∀ es : List PathStep, (es.map fun t => t.edge.eid).Nodup →
                s ∈ es → es.find? (fun t => t.edge.eid == s.edge.eid) = some s := by
              intro es hnd' hs'
              induction es with
              | nil => simp at hs'
              | cons x xs ih =>
                rw [List.map_cons, List.nodup_cons] at hnd'
                simp only [List.find?]
                rcases List.mem_cons.mp hs' with rfl | hs_tail
                · simp
                · have hne : x.edge.eid ≠ s.edge.eid := fun h =>
                    hnd'.1 (h ▸ List.mem_map_of_mem hs_tail)
                  have hbeq : (x.edge.eid == s.edge.eid) = false := beq_eq_false_iff_ne.mpr hne
                  rw [hbeq]
                  exact ih hnd'.2 hs_tail
            exact aux steps hnd_eid hs_mem
          rw [hfind]
          dsimp [e']
          rw [happ]
          cases sf : s.fwd <;> (simp [ForestEdge.addFlow]; try ring)
        · push Not at hmem_s
          have happ := MathForest.applyStepsDelta_of_not_mem hV hfs δ he hmem_s
          have hnone : steps.find? (fun t => t.edge.eid == k.1) = none := by
            rw [List.find?_eq_none]
            intro s hs
            simp only [beq_iff_eq]
            intro hseq
            apply hmem_s s hs
            exact stepEdge_eq_of_eid hV.2.1 (hw.mem_edges s hs) he (hseq.trans hek.symm)
          rw [hnone]
          dsimp [e']
          rw [happ]
          simp
      · have hk_not_pa : k.1 ∉ ((D.toForest df).pathAdd a b δ).edges.map ForestEdge.eid := by
          simp only [MathForest.pathAdd, hfs, List.map_map, Function.comp_def]
          intro hm
          rw [List.mem_map] at hm
          obtain ⟨e, he, heq⟩ := hm
          have heid_eq : (MathForest.applyStepsDelta steps δ e).eid = e.eid := by
            unfold MathForest.applyStepsDelta
            cases steps.find? fun s => s.edge.eid == e.eid with
            | none => rfl
            | some s => simp
          rw [heid_eq] at heq
          exact hk_in (heq ▸ List.mem_map_of_mem he)
        have hnone : steps.find? (fun t => t.edge.eid == k.1) = none := by
          rw [List.find?_eq_none]
          intro s hs
          simp only [beq_iff_eq]
          intro hseq
          exact hk_in (List.mem_map.mpr ⟨s.edge, hw.mem_edges s hs, hseq⟩)
        rw [actualFlow_of_not_mem flowArr₁ hk_not_pa, actualFlow_of_not_mem flowArr hk_in, hflow_k]
        dsimp [Δ]
        rw [ite_eq_right hkj, hnone]
        simp
  have hRoutes₁ : I.Routes (fun k => (actualFlow (D.toForest df₁) flowArr₁ k : ℝ)) := by
    have hc := costed_cycle_cancel hRoutes hCirc (by exact_mod_cast hδ_pos.le : (0 : ℝ) ≤ δ)
    dsimp only at hc
    rw [ite_eq_left hCost_Δ, one_mul] at hc
    have hfun : (fun k => (actualFlow (D.toForest df₁) flowArr₁ k : ℝ)) =
        (fun k => (actualFlow (D.toForest df) flowArr k : ℝ) + (δ : ℝ) * Δ k) :=
      funext hact_eq
    rw [hfun]
    exact hc.1
  have hCost₁ : I.cost (fun k => (actualFlow (D.toForest df₁) flowArr₁ k : ℝ)) ≤
      I.cost (fun k => (actualFlow (D.toForest df) flowArr k : ℝ)) := by
    have hc := costed_cycle_cancel hRoutes hCirc (by exact_mod_cast hδ_pos.le : (0 : ℝ) ≤ δ)
    dsimp only at hc
    rw [ite_eq_left hCost_Δ, one_mul] at hc
    have hfun : (fun k => (actualFlow (D.toForest df₁) flowArr₁ k : ℝ)) =
        (fun k => (actualFlow (D.toForest df) flowArr k : ℝ) + (δ : ℝ) * Δ k) :=
      funext hact_eq
    rw [hfun]
    exact hc.2.1
  have hBounds₁ : ∀ k : Fin I.m,
      (⌊f k⌋ : ℚ) ≤ actualFlow (D.toForest df₁) flowArr₁ k ∧
      actualFlow (D.toForest df₁) flowArr₁ k ≤ (⌈f k⌉ : ℚ) := by
    intro k
    rw [actualFlow_sameState hSame₁ hV₁ flowArr₁ k]
    by_cases hk_in : k.1 ∈ ((D.toForest df).pathAdd a b δ).edges.map ForestEdge.eid
    · rw [List.mem_map] at hk_in
      obtain ⟨e', he', hek⟩ := hk_in
      rw [actualFlow_of_mem hV_pa.2.1 flowArr₁ he' hek]
      have he'_df₁ : e' ∈ (D.toForest df₁).edges := hSame₁.2.symm.subset he'
      obtain ⟨j', heid', _, _, _, _, hlo, hhi, _⟩ := hWeak₁ e' he'_df₁
      have : j' = k := Fin.ext (heid'.symm.trans hek)
      subst this
      exact ⟨hlo, hhi⟩
    · rw [actualFlow_of_not_mem flowArr₁ hk_in]
      by_cases hkj : k = j
      · subst hkj
        dsimp [flowArr₁, newFlow]
        rw [ite_eq_left rfl]
        rcases hδ_j with ⟨rfl, hδ_le⟩ | ⟨rfl, hδ_le⟩
        · simp only [Int.cast_one, one_mul]
          exact ⟨le_trans (Int.floor_le (f k)) (by linarith), by linarith⟩
        · simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul]
          exact ⟨by linarith, le_trans (by linarith) (Int.le_ceil (f k))⟩
      · have hnot_df : k.1 ∉ (D.toForest df).edges.map ForestEdge.eid := by
          intro hm
          rw [List.mem_map] at hm
          obtain ⟨e, he, heq⟩ := hm
          apply hk_in
          simp only [MathForest.pathAdd, hfs, List.mem_map]
          refine ⟨MathForest.applyStepsDelta steps δ e, ⟨e, he, rfl⟩, ?_⟩
          unfold MathForest.applyStepsDelta
          cases steps.find? fun s => s.edge.eid == e.eid with
          | none => exact heq
          | some s => simp [heq]
        dsimp [flowArr₁]
        rw [ite_eq_right hkj]
        have := hBounds k
        rw [actualFlow_of_not_mem flowArr hnot_df] at this
        exact this
  exact ⟨hInv₁, hfs₁, hWeak₁, hOff₁, hPath₁, hRoutes₁, hBounds₁, hCost₁⟩

private theorem removeZeroEdges_n_eq {D : DynForest} (hSpec : D.IsSpec) {I : Instance} :
    ∀ fuel df flowArr counts rats a b, D.Inv df →
      let r := removeZeroEdges D I df flowArr counts rats a b fuel
      D.Inv r.1 ∧ (D.toForest r.1).n = (D.toForest df).n := by
  intro fuel
  induction fuel with
  | zero => intro df flowArr counts rats a b hInv; exact ⟨hInv, rfl⟩
  | succ fuel ih =>
    intro df flowArr counts rats a b hInv
    dsimp only [removeZeroEdges]
    cases D.pathMin df a b with
    | none => exact ⟨hInv, rfl⟩
    | some hit =>
      dsimp only
      by_cases hpos : hit.avail > 0
      · rw [ite_eq_left hpos]; exact ⟨hInv, rfl⟩
      · rw [ite_eq_right hpos]
        obtain ⟨hInv₁, hSame₁⟩ := hSpec.2.2.2.2.1 df hit.x hit.y hInv
        obtain ⟨hInv₂, hn₂⟩ := ih _ _ _ _ a hit.x hInv₁
        obtain ⟨hInv₃, hn₃⟩ := ih _ _ _ _ hit.y b hInv₂
        exact ⟨hInv₃, hn₃.trans (hn₂.trans hSame₁.1)⟩

private theorem actualFlow_link_eq {D : DynForest} (hSpec : D.IsSpec) {I : Instance}
    {df : D.State} (hInv : D.Inv df) {fe : ForestEdge}
    (hu : fe.u < (D.toForest df).n) (hv : fe.v < (D.toForest df).n)
    (hdisc : ¬ (D.toForest df).SameComp fe.u fe.v)
    (hnot : ∀ e' ∈ (D.toForest df).edges, e'.eid ≠ fe.eid)
    (flowArr : Fin I.m → ℚ) {j : Fin I.m} (hje : fe.eid = j.1) (hjf : fe.flow = flowArr j)
    (m : Fin I.m) :
    actualFlow (D.toForest (D.link df fe)) flowArr m = actualFlow (D.toForest df) flowArr m := by
  have hLink := hSpec.2.2.2.1 df fe hInv hu hv hdisc hnot
  have hV := hSpec.2.1 df hInv
  have hV' := hSpec.2.1 (D.link df fe) hLink.1
  have hfe_in : fe ∈ (D.toForest (D.link df fe)).edges :=
    hLink.2.2.symm.subset List.mem_cons_self
  by_cases hmj : m = j
  · subst hmj
    have hnot_m : m.1 ∉ (D.toForest df).edges.map ForestEdge.eid := by
      intro hm
      rw [List.mem_map] at hm
      obtain ⟨e, he, heq⟩ := hm
      exact hnot e he (heq.trans hje.symm)
    rw [actualFlow_of_mem hV'.2.1 flowArr hfe_in hje, actualFlow_of_not_mem flowArr hnot_m, hjf]
  · have hne : fe.eid ≠ m.1 := by rw [hje]; exact Fin.val_ne_of_ne (Ne.symm hmj)
    by_cases hm : m.1 ∈ (D.toForest df).edges.map ForestEdge.eid
    · rw [List.mem_map] at hm
      obtain ⟨e, he, heq⟩ := hm
      have he' : e ∈ (D.toForest (D.link df fe)).edges :=
        hLink.2.2.symm.subset (List.mem_cons_of_mem _ he)
      rw [actualFlow_of_mem hV'.2.1 flowArr he' heq, actualFlow_of_mem hV.2.1 flowArr he heq]
    · have hm' : m.1 ∉ (D.toForest (D.link df fe)).edges.map ForestEdge.eid := by
        intro hmem
        rw [List.mem_map] at hmem
        obtain ⟨e, he, heq⟩ := hmem
        rcases List.mem_cons.mp (hLink.2.2.subset he) with rfl | he_old
        · exact hne heq
        · exact hm (List.mem_map.mpr ⟨e, he_old, heq⟩)
      rw [actualFlow_of_not_mem flowArr hm', actualFlow_of_not_mem flowArr hm]

/-- Shared cycle-branch preservation proof covering both signs (`cycCostFwd ≤ 0` and `> 0`). -/
private theorem cycBranch_preserves {D : DynForest} (hSpec : D.IsSpec) {I : Instance}
    (hValid : I.IsValid) {f : Fin I.m → ℚ} {P : ℕ} {M : ℚ}
    {k : ℕ} (hk : k < I.m) {st : RoundState D I} (hInv : LoopInv D I f P M k st)
    (hj_frac : ¬ ∃ z : ℤ, f ⟨k, hk⟩ = z)
    {a b : ℕ} {steps : List PathStep}
    (hfs : findSteps (D.toForest st.df).edges a b = some steps)
    (signJ : ℤ) (availJ : ℚ)
    (hEnds : (a = (I.edge ⟨k, hk⟩).head ∧ b = (I.edge ⟨k, hk⟩).tail ∧ signJ = 1 ∧
               availJ = (⌈f ⟨k, hk⟩⌉ : ℚ) - f ⟨k, hk⟩) ∨
             (a = (I.edge ⟨k, hk⟩).tail ∧ b = (I.edge ⟨k, hk⟩).head ∧ signJ = -1 ∧
               availJ = f ⟨k, hk⟩ - (⌊f ⟨k, hk⟩⌋ : ℚ)))
    (hCost : stepsCost steps + signJ * (I.edge ⟨k, hk⟩).cost ≤ 0)
    {counts₂ : RoundCounts} {rats₁ : List ℚ} {costs₂ : List ℤ}
    (hc2_fr : counts₂.findRootOps = st.counts.findRootOps + 2)
    (hc2_lk : counts₂.linkOps = st.counts.linkOps)
    (hc2_cut : counts₂.cutOps = st.counts.cutOps)
    (hc2_pa : counts₂.pathAddOps = st.counts.pathAddOps)
    (hc2_pm : counts₂.pathMinOps = st.counts.pathMinOps)
    (hc2_ps : counts₂.pathSumOps = st.counts.pathSumOps + 1)
    (hc2_os : counts₂.otherSteps = st.counts.otherSteps + 6)
    (hr1_fp : (∀ j, IsFixedPoint P (f j)) → ∀ q ∈ rats₁, IsFixedPoint P q)
    (hr1_M : (∀ j, |f j| + 1 ≤ M) → ∀ q ∈ rats₁, |q| ≤ M)
    (hcosts2 : ∀ c ∈ costs₂, |c| ≤ (min I.n I.m : ℤ) * (I.maxCost : ℤ)) :
    let j : Fin I.m := ⟨k, hk⟩
    let hitOpt := D.pathMin st.df a b
    let δ := match hitOpt with
      | none => availJ
      | some hit => min availJ hit.avail
    let newFlow := f j + (signJ : ℚ) * δ
    let flowArr₁ := fun m : Fin I.m => if m = j then newFlow else st.flowArr m
    let df₁ := D.pathAdd st.df a b δ
    let counts₃ :=
      { counts₂ with
        pathMinOps := counts₂.pathMinOps + 1
        pathAddOps := counts₂.pathAddOps + 1
        otherSteps := counts₂.otherSteps + 3 }
    let rats₃ :=
      match hitOpt with
      | none => newFlow :: δ :: rats₁
      | some hit => newFlow :: δ :: hit.avail :: rats₁
    let (df₂, flowArr₂, counts₄, rats₄) :=
      removeZeroEdges D I df₁ flowArr₁ counts₃ rats₃ a b (I.m + 1)
    let st' : RoundState D I :=
      if isIntRat newFlow then
        { df := df₂
          flowArr := flowArr₂
          counts := { counts₄ with otherSteps := counts₄.otherSteps + 1 }
          computedRats := rats₄
          computedCosts := costs₂ }
      else
        let newAFwd : ℚ := (⌈f j⌉ : ℚ) - newFlow
        let newABwd : ℚ := newFlow - (⌊f j⌋ : ℚ)
        let fe : ForestEdge :=
          { eid := j.1, u := (I.edge j).tail, v := (I.edge j).head,
            cost := (I.edge j).cost, flow := newFlow, availFwd := newAFwd, availBwd := newABwd }
        { df := D.link df₂ fe
          flowArr := flowArr₂
          counts :=
            { counts₄ with
              linkOps := counts₄.linkOps + 1
              otherSteps := counts₄.otherSteps + 3 }
          computedRats := newABwd :: newAFwd :: rats₄
          computedCosts := costs₂ }
    LoopInv D I f P M (k + 1) st' := by
  intro j hitOpt δ newFlow flowArr₁ df₁ counts₃ rats₃
  obtain ⟨hDInv, hn, hEdges, hProcInt, hUnproc, hRoutes, hBounds, hCost_le,
    hc_fr, hc_lk, hc_cut, hc_ps, hc_pa, hc_pm, hc_os, hFP, hM, _⟩ := hInv
  have hV : (D.toForest st.df).Valid := hSpec.2.1 st.df hDInv
  obtain ⟨hw, _⟩ := findSteps_sound hV.2.1 hfs
  have hconn : (D.toForest st.df).SameComp a b := ⟨_, hw.to_isWalk⟩
  have hPM_eq : hitOpt = (D.toForest st.df).pathMin a b :=
    hSpec.2.2.2.2.2.2.1 st.df a b hDInv hconn
  have hlt : ∀ s ∈ steps, s.edge.eid < j.1 := fun s hs =>
    (hEdges s.edge (hw.mem_edges s hs)).2
  have haFwd_pos : 0 < (⌈f j⌉ : ℚ) - f j := by
    have : f j < (⌈f j⌉ : ℚ) := lt_of_le_of_ne (Int.le_ceil (f j)) (fun h => hj_frac ⟨⌈f j⌉, h⟩)
    linarith
  have haBwd_pos : 0 < f j - (⌊f j⌋ : ℚ) := by
    have : (⌊f j⌋ : ℚ) < f j := lt_of_le_of_ne (Int.floor_le (f j)) (fun h => hj_frac ⟨⌊f j⌋, h.symm⟩)
    linarith
  have havailJ_pos : 0 < availJ := by
    rcases hEnds with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> assumption
  have hδ_spec : 0 < δ ∧ δ ≤ availJ ∧ (∀ s ∈ steps, δ ≤ s.dirAvail) ∧
      (hitOpt = none → δ = availJ) ∧
      (∀ hit, hitOpt = some hit → (∃ s ∈ steps, s.dirAvail = hit.avail) ∧
        δ = min availJ hit.avail ∧ 0 < hit.avail ∧ hit.avail ≤ 1) := by
    dsimp [δ]
    rw [hPM_eq]
    unfold MathForest.pathMin
    rw [hfs, Option.bind_some]
    cases hmin : stepsMinHit steps with
    | none =>
      have hnil : steps = [] := stepsMinHit_eq_none_iff.mp hmin
      subst hnil
      refine ⟨havailJ_pos, le_refl _, by simp, fun _ => rfl, fun hit h => by simp at h⟩
    | some hit =>
      obtain ⟨pre, s, post, hsplit, hs_hit, hpre, hpost⟩ := stepsMinHit_spec hmin
      have hs_in : s ∈ steps := by rw [hsplit]; simp
      have hs_strict := (hEdges s.edge (hw.mem_edges s hs_in)).1
      have hhit_avail : hit.avail = s.dirAvail := by rw [← hs_hit]; rfl
      have hhit_pos : 0 < hit.avail := by
        rw [hhit_avail]
        cases hf : s.fwd <;> simp [PathStep.dirAvail, hf, hs_strict.2.1, hs_strict.2.2]
      have hhit_le1 : hit.avail ≤ 1 := by
        rw [hhit_avail]
        have hb := hs_strict.1.avail_bounds
        cases hf : s.fwd <;> simp [PathStep.dirAvail, hf, hb.2.1, hb.2.2.2.1]
      refine ⟨lt_min havailJ_pos hhit_pos, min_le_left _ _, fun t ht => ?_,
        fun h => by simp at h, fun hit' heq => ?_⟩
      · rw [hsplit, List.mem_append, List.mem_cons] at ht
        rcases ht with ht | rfl | ht
        · exact le_trans (min_le_right _ _) (le_of_lt (hpre t ht))
        · exact le_trans (min_le_right _ _) (le_of_eq hhit_avail)
        · exact le_trans (min_le_right _ _) (hpost t ht)
      · simp only [Option.some.injEq] at heq
        subst heq
        exact ⟨⟨s, hs_in, hhit_avail.symm⟩, rfl, hhit_pos, hhit_le1⟩
  obtain ⟨hδ_pos, hδ_le_J, hδ_steps, hδ_none, hδ_some⟩ := hδ_spec
  have hEnds' : (a = (I.edge j).head ∧ b = (I.edge j).tail ∧ signJ = 1) ∨
                (a = (I.edge j).tail ∧ b = (I.edge j).head ∧ signJ = -1) := by
    rcases hEnds with ⟨h1, h2, h3, _⟩ | ⟨h1, h2, h3, _⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1, h2, h3⟩
  have hδ_j : (signJ = 1 ∧ δ ≤ (⌈f j⌉ : ℚ) - f j) ∨ (signJ = -1 ∧ δ ≤ f j - (⌊f j⌋ : ℚ)) := by
    rcases hEnds with ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
    · exact Or.inl ⟨rfl, hδ_le_J⟩
    · exact Or.inr ⟨rfl, hδ_le_J⟩
  have hj_unproc := hUnproc j (Nat.le_refl k)
  obtain ⟨hInv₁, hfs₁, hWeak₁, hOff₁, hPath₁, hRoutes₁, hBounds₁, hCost₁⟩ :=
    pushCycle_preserves hSpec hDInv (fun e he => (hEdges e he).1) hRoutes hBounds
      hj_unproc.1 hj_unproc.2 hfs hlt signJ hEnds' hδ_pos hδ_j hδ_steps hCost
  -- Show `(D.toForest df₁).edges.length < I.m + 1`
  have hlen₁_lt : (D.toForest df₁).edges.length < I.m + 1 := by
    have hSame₁ := (hSpec.2.2.2.2.2.1 st.df a b δ hDInv hconn).2
    have hlen_eq1 : (D.toForest df₁).edges.length =
        ((D.toForest st.df).pathAdd a b δ).edges.length := hSame₁.2.length_eq
    have hlen_eq2 : ((D.toForest st.df).pathAdd a b δ).edges.length =
        (D.toForest st.df).edges.length := (D.toForest st.df).pathAdd_edges_length a b δ
    omega
  -- Fixed point and M bounds for `df₁` and `rats₃`
  have hFP_all : (∀ m, IsFixedPoint P (f m)) →
      (∀ e ∈ (D.toForest df₁).edges,
        IsFixedPoint P e.flow ∧ IsFixedPoint P e.availFwd ∧ IsFixedPoint P e.availBwd) ∧
      (∀ q ∈ rats₃, IsFixedPoint P q) := by
    intro hfP
    obtain ⟨hFP_df, hFP_arr, hFP_rats⟩ := hFP hfP
    have hFP_aJ : IsFixedPoint P availJ := by
      rcases hEnds with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
      · exact isFixedPoint_sub (isFixedPoint_int P _) (hfP j)
      · exact isFixedPoint_sub (hfP j) (isFixedPoint_int P _)
    have hFP_hit : ∀ hit, hitOpt = some hit → IsFixedPoint P hit.avail := by
      intro hit hhit
      have hhit_spec := hδ_some hit hhit
      obtain ⟨s, hs_in, hs_av⟩ := hhit_spec.1
      have hfp_s := hFP_df s.edge (hw.mem_edges s hs_in)
      rw [← hs_av]
      cases sf : s.fwd <;> simp [PathStep.dirAvail, sf, hfp_s.2.1, hfp_s.2.2]
    have hFP_δ : IsFixedPoint P δ := by
      cases hhit : hitOpt with
      | none => rw [hδ_none hhit]; exact hFP_aJ
      | some hit => rw [(hδ_some hit hhit).2.1]; exact isFixedPoint_min hFP_aJ (hFP_hit hit hhit)
    have hFP_newFlow : IsFixedPoint P newFlow := by
      rcases hEnds with ⟨_, _, rfl, _⟩ | ⟨_, _, rfl, _⟩
      · have : newFlow = f j + δ := by simp [newFlow]
        rw [this]; exact isFixedPoint_add (hfP j) hFP_δ
      · have : newFlow = f j - δ := by simp [newFlow]; ring
        rw [this]; exact isFixedPoint_sub (hfP j) hFP_δ
    refine ⟨?_, ?_⟩
    · intro e' he'
      have hSame₁ := (hSpec.2.2.2.2.2.1 st.df a b δ hDInv hconn).2
      have he'_pa := hSame₁.2.subset he'
      simp only [MathForest.pathAdd, hfs, List.mem_map] at he'_pa
      obtain ⟨e, he, rfl⟩ := he'_pa
      have hfp_e := hFP_df e he
      unfold MathForest.applyStepsDelta
      cases steps.find? fun s => s.edge.eid == e.eid with
      | none => exact hfp_e
      | some s =>
        cases sf : s.fwd <;> simp [ForestEdge.addFlow, sf]
        · exact ⟨isFixedPoint_sub hfp_e.1 hFP_δ, isFixedPoint_add hfp_e.2.1 hFP_δ,
            isFixedPoint_sub hfp_e.2.2 hFP_δ⟩
        · exact ⟨isFixedPoint_add hfp_e.1 hFP_δ, isFixedPoint_sub hfp_e.2.1 hFP_δ,
            isFixedPoint_add hfp_e.2.2 hFP_δ⟩
    · intro q hq
      dsimp [rats₃] at hq
      cases hhit : hitOpt with
      | none =>
        rw [hhit] at hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hFP_newFlow
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact hFP_δ
          · exact hr1_fp hfP q hq
      | some hit =>
        rw [hhit] at hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hFP_newFlow
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact hFP_δ
          · rcases List.mem_cons.mp hq with rfl | hq
            · exact hFP_hit hit hhit
            · exact hr1_fp hfP q hq
  have hM_rats₃ : (∀ m, |f m| + 1 ≤ M) → ∀ q ∈ rats₃, |q| ≤ M := by
    intro hMf q hq
    have h1M : (1 : ℚ) ≤ M := by
      have := hMf j; have : (0 : ℚ) ≤ |f j| := abs_nonneg _; linarith
    have hδ_le_1 : δ ≤ 1 := by
      rcases hEnds with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
      · have : (⌈f j⌉ : ℚ) < f j + 1 := Int.ceil_lt_add_one (f j)
        have : f j - (⌊f j⌋ : ℚ) ≤ 1 := by
          have := Int.sub_one_lt_floor (f j); linarith
        linarith [Int.floor_le (f j)]
      · have := Int.sub_one_lt_floor (f j)
        linarith
    have hM_newFlow : |newFlow| ≤ M := by
      have h3 := Int.ceil_lt_add_one (f j)
      have h4 := Int.sub_one_lt_floor (f j)
      have hlo : (⌊f j⌋ : ℚ) ≤ newFlow := by
        rcases hEnds with ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
        · simp [newFlow]; linarith [Int.floor_le (f j)]
        · simp [newFlow]; linarith
      have hhi : newFlow ≤ (⌈f j⌉ : ℚ) := by
        rcases hEnds with ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
        · simp [newFlow]; linarith
        · simp [newFlow]; linarith [Int.le_ceil (f j)]
      have hfj := hMf j
      rw [abs_le]
      have hab : -|f j| ≤ f j ∧ f j ≤ |f j| := abs_le.mp (le_refl _)
      constructor <;> linarith
    dsimp [rats₃] at hq
    cases hhit : hitOpt with
    | none =>
      rw [hhit] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hM_newFlow
      · rcases List.mem_cons.mp hq with rfl | hq
        · rw [abs_of_pos hδ_pos]; linarith
        · exact hr1_M hMf q hq
    | some hit =>
      rw [hhit] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hM_newFlow
      · rcases List.mem_cons.mp hq with rfl | hq
        · rw [abs_of_pos hδ_pos]; linarith
        · rcases List.mem_cons.mp hq with rfl | hq
          · have hs_hit := (hδ_some hit hhit).2.2
            rw [abs_of_pos hs_hit.1]; linarith
          · exact hr1_M hMf q hq
  suffices hgen : ∀ (fuel : ℕ), (D.toForest df₁).edges.length < fuel →
      let (df₂, flowArr₂, counts₄, rats₄) :=
        removeZeroEdges D I df₁ flowArr₁ counts₃ rats₃ a b fuel
      let st' : RoundState D I :=
        if isIntRat newFlow then
          { df := df₂
            flowArr := flowArr₂
            counts := { counts₄ with otherSteps := counts₄.otherSteps + 1 }
            computedRats := rats₄
            computedCosts := costs₂ }
        else
          let newAFwd : ℚ := (⌈f j⌉ : ℚ) - newFlow
          let newABwd : ℚ := newFlow - (⌊f j⌋ : ℚ)
          let fe : ForestEdge :=
            { eid := j.1, u := (I.edge j).tail, v := (I.edge j).head,
              cost := (I.edge j).cost, flow := newFlow, availFwd := newAFwd, availBwd := newABwd }
          { df := D.link df₂ fe
            flowArr := flowArr₂
            counts :=
              { counts₄ with
                linkOps := counts₄.linkOps + 1
                otherSteps := counts₄.otherSteps + 3 }
            computedRats := newABwd :: newAFwd :: rats₄
            computedCosts := costs₂ }
      LoopInv D I f P M (k + 1) st' from hgen (I.m + 1) hlen₁_lt
  intro fuel hfuel_lt
  have hrm := removeZeroEdges_spec hSpec fuel df₁ flowArr₁ counts₃ rats₃ a b
    (steps.map fun s => { s with edge := s.edge.addFlow s.fwd δ })
    hInv₁ hfs₁ hfuel_lt hWeak₁ hPath₁
  have hr_n := removeZeroEdges_n_eq hSpec fuel df₁ flowArr₁ counts₃ rats₃ a b hInv₁
  generalize hres : removeZeroEdges D I df₁ flowArr₁ counts₃ rats₃ a b fuel = res₂ at hrm hr_n ⊢
  rcases res₂ with ⟨df₂, flowArr₂, counts₄, rats₄⟩
  dsimp only at hrm hr_n ⊢
  obtain ⟨hInv₂, hact₂, hsub₂, hkeep₂, hrem₂, hstrict₂, hflow_out₂, hflow_int₂, hdisc₂,
    hc₂_fr, hc₂_lk, hc₂_pa, hc₂_ps, hlen₂, hcut₂, hpm₂, hos₂, hFP_rats₂, hM_rats₂, hcases₂⟩ := hrm
  have hSame₁ := (hSpec.2.2.2.2.2.1 st.df a b δ hDInv hconn).2
  have hV₂ : (D.toForest df₂).Valid := hSpec.2.1 df₂ hInv₂
  have hn_pa : ((D.toForest st.df).pathAdd a b δ).n = (D.toForest st.df).n := by
    simp [MathForest.pathAdd, hfs]
  have hn₂ : (D.toForest df₂).n = I.n :=
    hr_n.2.trans (hSame₁.1.trans (hn_pa.trans hn))
  have heid_lt_df₁ : ∀ e ∈ (D.toForest df₁).edges, e.eid < k := by
    intro e he
    have he_pa := hSame₁.2.subset he
    simp only [MathForest.pathAdd, hfs, List.mem_map] at he_pa
    obtain ⟨e₀, he₀, rfl⟩ := he_pa
    have heid_eq : (MathForest.applyStepsDelta steps δ e₀).eid = e₀.eid := by
      unfold MathForest.applyStepsDelta
      cases steps.find? fun s => s.edge.eid == e₀.eid <;> simp
    rw [heid_eq]
    exact (hEdges e₀ he₀).2
  have heid_lt_df₂ : ∀ e ∈ (D.toForest df₂).edges, e.eid < k := fun e he =>
    heid_lt_df₁ e (hsub₂ e he)
  have hj_not_df₁ : j.1 ∉ (D.toForest df₁).edges.map ForestEdge.eid := by
    intro hm
    rw [List.mem_map] at hm
    obtain ⟨e, he, heq⟩ := hm
    have := heid_lt_df₁ e he
    have hj1 : j.1 = k := rfl
    omega
  have hj_not_df₂ : j.1 ∉ (D.toForest df₂).edges.map ForestEdge.eid := fun hm => by
    rw [List.mem_map] at hm
    obtain ⟨e, he, heq⟩ := hm
    exact hj_not_df₁ (List.mem_map.mpr ⟨e, hsub₂ e he, heq⟩)
  have hj_arr₂ : flowArr₂ j = newFlow := by
    rw [hflow_out₂ j hj_not_df₁]
    simp [flowArr₁]
  have hStrict₂ : ∀ e ∈ (D.toForest df₂).edges, ForestEdgeStrictInv I f e := by
    intro e he
    have he₁ := hsub₂ e he
    by_cases hin : ∃ s ∈ steps.map fun s => { s with edge := s.edge.addFlow s.fwd δ }, s.edge = e
    · obtain ⟨s, hs_in, hs_eq⟩ := hin
      subst hs_eq
      exact hstrict₂ s hs_in he
    · push Not at hin
      exact hOff₁ e he₁ hin
  have hact_newFlow : actualFlow (D.toForest df₁) flowArr₁ j = newFlow := by
    rw [actualFlow_of_not_mem flowArr₁ hj_not_df₁]
    simp [flowArr₁]
  have hlo_new : (⌊f j⌋ : ℚ) ≤ newFlow := by
    rw [← hact_newFlow]; exact (hBounds₁ j).1
  have hhi_new : newFlow ≤ (⌈f j⌉ : ℚ) := by
    rw [← hact_newFlow]; exact (hBounds₁ j).2
  have hm_lt_df₁_iff : ∀ m : Fin I.m,
      m.1 ∈ (D.toForest df₁).edges.map ForestEdge.eid ↔
      m.1 ∈ (D.toForest st.df).edges.map ForestEdge.eid := by
    intro m
    simp only [List.mem_map]
    constructor
    · rintro ⟨e', he', heq⟩
      have he'_pa := hSame₁.2.subset he'
      simp only [MathForest.pathAdd, hfs, List.mem_map] at he'_pa
      obtain ⟨e, he, rfl⟩ := he'_pa
      have heid_eq : (MathForest.applyStepsDelta steps δ e).eid = e.eid := by
        unfold MathForest.applyStepsDelta
        cases steps.find? fun s => s.edge.eid == e.eid <;> simp
      exact ⟨e, he, heid_eq ▸ heq⟩
    · rintro ⟨e, he, heq⟩
      have he_pa : MathForest.applyStepsDelta steps δ e ∈ ((D.toForest st.df).pathAdd a b δ).edges := by
        simp only [MathForest.pathAdd, hfs, List.mem_map]
        exact ⟨e, he, rfl⟩
      have heid_eq : (MathForest.applyStepsDelta steps δ e).eid = e.eid := by
        unfold MathForest.applyStepsDelta
        cases steps.find? fun s => s.edge.eid == e.eid <;> simp
      exact ⟨_, hSame₁.2.symm.subset he_pa, heid_eq.trans heq⟩
  have hProcInt₂ : ∀ m : Fin I.m, m.1 < k →
      m.1 ∉ (D.toForest df₂).edges.map ForestEdge.eid → ∃ z : ℤ, flowArr₂ m = z := by
    intro m hm_lt hm_not₂
    have hmj : m ≠ j := fun h => by subst h; exact Nat.lt_irrefl _ hm_lt
    by_cases hm₁ : m.1 ∈ (D.toForest df₁).edges.map ForestEdge.eid
    · exact hflow_int₂ m hm₁ hm_not₂
    · rw [hflow_out₂ m hm₁]
      dsimp [flowArr₁]
      rw [ite_eq_right hmj]
      exact hProcInt m hm_lt ((hm_lt_df₁_iff m).not.mp hm₁)
  have hUnproc₂ : ∀ m : Fin I.m, k + 1 ≤ m.1 →
      m.1 ∉ (D.toForest df₂).edges.map ForestEdge.eid ∧ flowArr₂ m = f m := by
    intro m hm_ge
    have hnot_st := (hUnproc m (Nat.le_trans (Nat.le_succ k) hm_ge)).1
    have hf_eq := (hUnproc m (Nat.le_trans (Nat.le_succ k) hm_ge)).2
    have hmj : m ≠ j := fun h => by
      have hj1 : j.1 = k := rfl
      rw [h] at hm_ge
      omega
    have hnot₁ : m.1 ∉ (D.toForest df₁).edges.map ForestEdge.eid :=
      mt (hm_lt_df₁_iff m).mp hnot_st
    have hnot₂ : m.1 ∉ (D.toForest df₂).edges.map ForestEdge.eid := fun hm => by
      rw [List.mem_map] at hm
      obtain ⟨e, he, heq⟩ := hm
      exact hnot₁ (List.mem_map.mpr ⟨e, hsub₂ e he, heq⟩)
    refine ⟨hnot₂, ?_⟩
    rw [hflow_out₂ m hnot₁]
    dsimp [flowArr₁]
    rw [ite_eq_right hmj, hf_eq]
  have hRoutes₂ : I.Routes (fun m => (actualFlow (D.toForest df₂) flowArr₂ m : ℝ)) := by
    convert hRoutes₁ using 2 with m
    rw [hact₂ m]
  have hBounds₂ : ∀ m : Fin I.m,
      (⌊f m⌋ : ℚ) ≤ actualFlow (D.toForest df₂) flowArr₂ m ∧
      actualFlow (D.toForest df₂) flowArr₂ m ≤ (⌈f m⌉ : ℚ) := by
    intro m; rw [hact₂ m]; exact hBounds₁ m
  have hCost₂ : I.cost (fun m => (actualFlow (D.toForest df₂) flowArr₂ m : ℝ)) ≤
      I.cost (fun m => (f m : ℝ)) := by
    have hceq : I.cost (fun m => (actualFlow (D.toForest df₂) flowArr₂ m : ℝ)) =
        I.cost (fun m => (actualFlow (D.toForest df₁) flowArr₁ m : ℝ)) := by
      congr 1 with m; rw [hact₂ m]
    rw [hceq]; exact le_trans hCost₁ hCost_le
  have hlen₁_eq : (D.toForest df₁).edges.length = (D.toForest st.df).edges.length := by
    rw [hSame₁.2.length_eq, (D.toForest st.df).pathAdd_edges_length]
  have hcut_total : counts₄.cutOps + (D.toForest df₂).edges.length = st.counts.linkOps := by
    change counts₄.cutOps + (D.toForest df₂).edges.length =
      counts₃.cutOps + (D.toForest df₁).edges.length at hcut₂
    have h3 : counts₃.cutOps = st.counts.cutOps := hc2_cut
    omega
  have hpm_total : counts₄.pathMinOps ≤ 2 * (k + 1) + 2 * counts₄.cutOps := by
    change counts₄.pathMinOps + 2 * counts₃.cutOps =
      counts₃.pathMinOps + 2 * counts₄.cutOps + 1 at hpm₂
    have h1 : counts₃.cutOps = st.counts.cutOps := hc2_cut
    have h2 : counts₃.pathMinOps = st.counts.pathMinOps + 1 := by simp [counts₃, hc2_pm]
    omega
  have hos_total : counts₄.otherSteps + 5 * st.counts.cutOps ≤
      st.counts.otherSteps + 5 * counts₄.cutOps + 11 := by
    change counts₄.otherSteps + 5 * counts₃.cutOps ≤
      counts₃.otherSteps + 5 * counts₄.cutOps + 2 at hos₂
    have h1 : counts₃.cutOps = st.counts.cutOps := hc2_cut
    have h2 : counts₃.otherSteps = st.counts.otherSteps + 9 := by
      simp [counts₃, hc2_os]
    omega
  have hFP_mid : (∀ m, IsFixedPoint P (f m)) →
      (∀ e ∈ (D.toForest df₂).edges,
        IsFixedPoint P e.flow ∧ IsFixedPoint P e.availFwd ∧ IsFixedPoint P e.availBwd) ∧
      (∀ m, IsFixedPoint P (flowArr₂ m)) ∧
      (∀ q ∈ rats₄, IsFixedPoint P q) := by
    intro hfP
    obtain ⟨hFP_df₁, hFP_rats₃⟩ := hFP_all hfP
    obtain ⟨_, hFP_arr, _⟩ := hFP hfP
    have hFP_new : IsFixedPoint P newFlow := hFP_rats₃ newFlow (by
      cases hhit : hitOpt with
      | none => simp [rats₃, hhit]
      | some hit => simp [rats₃, hhit])
    refine ⟨fun e he => hFP_df₁ e (hsub₂ e he), fun m => ?_, hFP_rats₂ P hFP_df₁ hFP_rats₃⟩
    rcases hcases₂ m with hm | ⟨e, he, _, hfl⟩
    · rw [hm]
      dsimp [flowArr₁]
      by_cases hmj : m = j
      · rw [ite_eq_left hmj]; exact hFP_new
      · rw [ite_eq_right hmj]; exact hFP_arr m
    · rw [hfl]; exact (hFP_df₁ e he).1
  have hM_mid : (∀ m, |f m| + 1 ≤ M) →
      (∀ q ∈ rats₄, |q| ≤ M) ∧ (∀ m, |flowArr₂ m| ≤ M) := by
    intro hMf
    obtain ⟨_, hM_arr⟩ := hM hMf
    have hM_rats₃' := hM_rats₃ hMf
    have hM_new : |newFlow| ≤ M := hM_rats₃' newFlow (by
      cases hhit : hitOpt with
      | none => simp [rats₃, hhit]
      | some hit => simp [rats₃, hhit])
    refine ⟨hM_rats₂ M hMf hM_rats₃', fun m => ?_⟩
    rcases hcases₂ m with hm | ⟨e, he, _, hfl⟩
    · rw [hm]
      dsimp [flowArr₁]
      by_cases hmj : m = j
      · rw [ite_eq_left hmj]; exact hM_new
      · rw [ite_eq_right hmj]; exact hM_arr m
    · rw [hfl]
      obtain ⟨m₀, _, hfb⟩ := (hWeak₁ e he).flow_bounds
      exact le_trans hfb (hMf m₀)
  by_cases hint : isIntRat newFlow = true
  · rw [ite_eq_left hint]
    have hnew_int : ∃ z : ℤ, newFlow = z := isIntRat_iff.mp hint
    refine ⟨hInv₂, hn₂, fun e he => ⟨hStrict₂ e he, Nat.lt_succ_of_lt (heid_lt_df₂ e he)⟩,
      fun m hm_lt hm_not => ?_, fun m hm_ge => hUnproc₂ m hm_ge, hRoutes₂, hBounds₂, hCost₂,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcosts2⟩
    · by_cases hmj : m = j
      · rw [hmj]; dsimp only; rw [hj_arr₂]; exact hnew_int
      · have hj1 : j.1 = k := rfl
        have hne : m.1 ≠ j.1 := Fin.val_ne_of_ne hmj
        exact hProcInt₂ m (by omega) hm_not
    · change counts₄.findRootOps ≤ 2 * (k + 1)
      rw [hc₂_fr]; dsimp only [counts₃]; rw [hc2_fr]; omega
    · change counts₄.linkOps ≤ k + 1
      rw [hc₂_lk]; dsimp only [counts₃]; rw [hc2_lk]; omega
    · change counts₄.cutOps + (D.toForest df₂).edges.length = counts₄.linkOps
      rw [hcut_total, hc₂_lk]; dsimp only [counts₃]; exact hc2_lk.symm
    · change counts₄.pathSumOps ≤ k + 1
      rw [hc₂_ps]; dsimp only [counts₃]; rw [hc2_ps]; omega
    · change counts₄.pathAddOps ≤ k + 1
      rw [hc₂_pa]; dsimp only [counts₃]; rw [hc2_pa]; omega
    · exact hpm_total
    · change counts₄.otherSteps + 1 ≤ 14 * (k + 1) + 5 * counts₄.cutOps
      omega
    · exact hFP_mid
    · exact hM_mid
  · rw [ite_eq_right hint]
    have hj_nint : ¬ ∃ z : ℤ, newFlow = z := mt isIntRat_iff.mpr hint
    let newAFwd : ℚ := (⌈f j⌉ : ℚ) - newFlow
    let newABwd : ℚ := newFlow - (⌊f j⌋ : ℚ)
    let fe : ForestEdge :=
      { eid := j.1, u := (I.edge j).tail, v := (I.edge j).head,
        cost := (I.edge j).cost, flow := newFlow, availFwd := newAFwd, availBwd := newABwd }
    have hdisc_ab : ¬ (D.toForest df₂).SameComp a b := by
      apply hdisc₂
      cases hhit : hitOpt with
      | none =>
        exfalso; apply hj_nint
        have hδ_eq : δ = availJ := hδ_none hhit
        rcases hEnds with ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
        · exact ⟨⌈f j⌉, by dsimp only [newFlow, j]; rw [hδ_eq]; push_cast; ring⟩
        · exact ⟨⌊f j⌋, by dsimp only [newFlow, j]; rw [hδ_eq]; push_cast; ring⟩
      | some hit =>
        obtain ⟨⟨s, hs_in, hs_av⟩, hδ_eq, _⟩ := hδ_some hit hhit
        have hlt_av : hit.avail < availJ := by
          by_contra hle
          push Not at hle
          apply hj_nint
          have hδ_J : δ = availJ := by rw [hδ_eq]; exact min_eq_left hle
          rcases hEnds with ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
          · exact ⟨⌈f j⌉, by dsimp only [newFlow, j]; rw [hδ_J]; push_cast; ring⟩
          · exact ⟨⌊f j⌋, by dsimp only [newFlow, j]; rw [hδ_J]; push_cast; ring⟩
        have hδ_hit : δ = hit.avail := by rw [hδ_eq]; exact min_eq_right (le_of_lt hlt_av)
        refine ⟨{ s with edge := s.edge.addFlow s.fwd δ }, List.mem_map_of_mem hs_in, ?_⟩
        cases sf : s.fwd
        · simp [PathStep.dirAvail, ForestEdge.addFlow, sf] at hs_av ⊢
          linarith
        · simp [PathStep.dirAvail, ForestEdge.addFlow, sf] at hs_av ⊢
          linarith
    have hdisc_uv : ¬ (D.toForest df₂).SameComp fe.u fe.v := by
      intro ⟨w, hw⟩
      apply hdisc_ab
      rcases hEnds with ⟨ha, hb, _, _⟩ | ⟨ha, hb, _, _⟩
      · exact ⟨w.reverse, ha ▸ hb ▸ hw.reverse⟩
      · exact ⟨w, ha ▸ hb ▸ hw⟩
    have huv_bound : fe.u < (D.toForest df₂).n ∧ fe.v < (D.toForest df₂).n := by
      rw [hn₂]
      exact hValid.1 (I.edge j) (List.getElem_mem j.2)
    have hnot_fe : ∀ e' ∈ (D.toForest df₂).edges, e'.eid ≠ fe.eid := fun e' he' =>
      Nat.ne_of_lt (heid_lt_df₂ e' he')
    have hLink := hSpec.2.2.2.1 df₂ fe hInv₂ huv_bound.1 huv_bound.2 hdisc_uv hnot_fe
    have hV_link : (D.toForest (D.link df₂ fe)).Valid := hSpec.2.1 _ hLink.1
    have hact_link : ∀ m : Fin I.m,
        actualFlow (D.toForest (D.link df₂ fe)) flowArr₂ m =
        actualFlow (D.toForest df₂) flowArr₂ m :=
      actualFlow_link_eq hSpec hInv₂ huv_bound.1 huv_bound.2 hdisc_uv hnot_fe flowArr₂
        rfl hj_arr₂.symm
    have hStrict_fe : ForestEdgeStrictInv I f fe := by
      have hp_fwd : 0 < newAFwd := by
        dsimp [newAFwd]
        exact sub_pos.mpr (lt_of_le_of_ne hhi_new (fun h => hj_nint ⟨⌈f j⌉, h⟩))
      have hp_bwd : 0 < newABwd := by
        dsimp [newABwd]
        exact sub_pos.mpr (lt_of_le_of_ne hlo_new (fun h => hj_nint ⟨⌊f j⌋, h.symm⟩))
      exact ⟨⟨j, rfl, rfl, rfl, rfl, hj_frac, hlo_new, hhi_new, rfl, rfl⟩, hp_fwd, hp_bwd⟩
    refine ⟨hLink.1, hLink.2.1.trans hn₂, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcosts2⟩
    · intro e he
      rcases List.mem_cons.mp (hLink.2.2.subset he) with rfl | he₂
      · exact ⟨hStrict_fe, Nat.lt_succ_self k⟩
      · exact ⟨hStrict₂ e he₂, Nat.lt_succ_of_lt (heid_lt_df₂ e he₂)⟩
    · intro m hm_lt hm_not
      have hm_lt_k : m.1 < k := by
        by_contra hge
        have hj1 : j.1 = k := rfl
        have hmeq : m = j := Fin.ext (by omega)
        rw [hmeq] at hm_not
        apply hm_not
        exact List.mem_map.mpr ⟨fe, hLink.2.2.symm.subset List.mem_cons_self, rfl⟩
      have hm_not₂ : m.1 ∉ (D.toForest df₂).edges.map ForestEdge.eid := fun hm => by
        rw [List.mem_map] at hm
        obtain ⟨e, he, heq⟩ := hm
        exact hm_not (List.mem_map.mpr ⟨e, hLink.2.2.symm.subset (List.mem_cons_of_mem _ he), heq⟩)
      exact hProcInt₂ m hm_lt_k hm_not₂
    · intro m hm_ge
      have hne_fe : m.1 ≠ fe.eid := by
        dsimp [fe]; have hj1 : j.1 = k := rfl; omega
      have h2 := hUnproc₂ m hm_ge
      refine ⟨fun hm => ?_, h2.2⟩
      rw [List.mem_map] at hm
      obtain ⟨e, he, heq⟩ := hm
      rcases List.mem_cons.mp (hLink.2.2.subset he) with rfl | he₂
      · exact hne_fe heq.symm
      · exact h2.1 (List.mem_map.mpr ⟨e, he₂, heq⟩)
    · convert hRoutes₂ using 2 with m; rw [hact_link m]
    · intro m; rw [hact_link m]; exact hBounds₂ m
    · have hceq : I.cost (fun m => (actualFlow (D.toForest (D.link df₂ fe)) flowArr₂ m : ℝ)) =
          I.cost (fun m => (actualFlow (D.toForest df₂) flowArr₂ m : ℝ)) := by
        congr 1 with m; rw [hact_link m]
      rw [hceq]; exact hCost₂
    · change counts₄.findRootOps ≤ 2 * (k + 1)
      rw [hc₂_fr]; dsimp only [counts₃]; rw [hc2_fr]; omega
    · change counts₄.linkOps + 1 ≤ k + 1
      rw [hc₂_lk]; dsimp only [counts₃]; rw [hc2_lk]; omega
    · change counts₄.cutOps + (D.toForest (D.link df₂ fe)).edges.length = counts₄.linkOps + 1
      have hlen_link : (D.toForest (D.link df₂ fe)).edges.length = (D.toForest df₂).edges.length + 1 := by
        rw [hLink.2.2.length_eq]; rfl
      have hl_eq : counts₄.linkOps = st.counts.linkOps := by rw [hc₂_lk]; dsimp only [counts₃]; exact hc2_lk
      rw [hlen_link]
      omega
    · change counts₄.pathSumOps ≤ k + 1
      rw [hc₂_ps]; dsimp only [counts₃]; rw [hc2_ps]; omega
    · change counts₄.pathAddOps ≤ k + 1
      rw [hc₂_pa]; dsimp only [counts₃]; rw [hc2_pa]; omega
    · exact hpm_total
    · change counts₄.otherSteps + 3 ≤ 14 * (k + 1) + 5 * counts₄.cutOps
      omega
    · intro hfP
      obtain ⟨hFP_df₂, hFP_arr₂, hFP_rats₄⟩ := hFP_mid hfP
      have hFP_new : IsFixedPoint P newFlow := by
        rw [← hj_arr₂]; exact hFP_arr₂ j
      have hFP_newAFwd : IsFixedPoint P newAFwd :=
        isFixedPoint_sub (isFixedPoint_int P _) hFP_new
      have hFP_newABwd : IsFixedPoint P newABwd :=
        isFixedPoint_sub hFP_new (isFixedPoint_int P _)
      refine ⟨fun e he => ?_, hFP_arr₂, fun q hq => ?_⟩
      · rcases List.mem_cons.mp (hLink.2.2.subset he) with rfl | he₂
        · exact ⟨hFP_new, hFP_newAFwd, hFP_newABwd⟩
        · exact hFP_df₂ e he₂
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact hFP_newABwd
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact hFP_newAFwd
          · exact hFP_rats₄ q hq
    · intro hMf
      obtain ⟨hM_rats₄, hM_arr₂⟩ := hM_mid hMf
      have h1M : (1 : ℚ) ≤ M := by
        have := hMf j; have : (0 : ℚ) ≤ |f j| := abs_nonneg _; linarith
      have hb_fe := hStrict_fe.1.avail_bounds
      have hM_af : |newAFwd| ≤ M := by
        have h0 : 0 ≤ newAFwd := hb_fe.1
        have h1 : newAFwd ≤ 1 := hb_fe.2.1
        rw [abs_of_nonneg h0]; linarith
      have hM_ab : |newABwd| ≤ M := by
        have h0 : 0 ≤ newABwd := hb_fe.2.2.1
        have h1 : newABwd ≤ 1 := hb_fe.2.2.2.1
        rw [abs_of_nonneg h0]; linarith
      refine ⟨fun q hq => ?_, hM_arr₂⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hM_ab
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact hM_af
        · exact hM_rats₄ q hq

theorem roundEdgeStep_preserves {D : DynForest} (hSpec : D.IsSpec) {I : Instance}
    (hValid : I.IsValid) {f : Fin I.m → ℚ} {P : ℕ} {M : ℚ}
    {k : ℕ} (hk : k < I.m) {st : RoundState D I} (hInv : LoopInv D I f P M k st) :
    LoopInv D I f P M (k + 1) (roundEdgeStep D I f st ⟨k, hk⟩) := by
  let j : Fin I.m := ⟨k, hk⟩
  have hInv_copy := hInv
  obtain ⟨hDInv, hn, hEdges, hProcInt, hUnproc, hRoutes, hBounds, hCost_le,
    hc_fr, hc_lk, hc_cut, hc_ps, hc_pa, hc_pm, hc_os, hFP, hM, hcosts⟩ := hInv
  by_cases hfj_int : isIntRat (f j) = true
  · dsimp only [roundEdgeStep]
    rw [ite_eq_left hfj_int]
    have hfj_z : ∃ z : ℤ, f j = z := isIntRat_iff.mp hfj_int
    refine ⟨hDInv, hn, fun e he => ⟨(hEdges e he).1, Nat.lt_succ_of_lt (hEdges e he).2⟩,
      fun m hm_lt hm_not => ?_, fun m hm_ge => hUnproc m (Nat.le_trans (Nat.le_succ k) hm_ge),
      hRoutes, hBounds, hCost_le, by dsimp only; omega, by dsimp only; omega,
      hc_cut, by dsimp only; omega, by dsimp only; omega,
      by dsimp only; omega, by dsimp only; omega, hFP, hM, hcosts⟩
    by_cases hmj : m = j
    · rw [hmj, (hUnproc j (le_refl k)).2]; exact hfj_z
    · have hj1 : j.1 = k := rfl
      have hne : m.1 ≠ j.1 := Fin.val_ne_of_ne hmj
      exact hProcInt m (by omega) hm_not
  · have hj_frac : ¬ ∃ z : ℤ, f j = z := mt isIntRat_iff.mpr hfj_int
    have huv : (I.edge j).tail < (D.toForest st.df).n ∧
        (I.edge j).head < (D.toForest st.df).n := by
      rw [hn]; exact hValid.1 (I.edge j) (List.getElem_mem j.2)
    have hr_iff : D.findRoot st.df (I.edge j).tail = D.findRoot st.df (I.edge j).head ↔
        (D.toForest st.df).SameComp (I.edge j).tail (I.edge j).head :=
      (hSpec.2.2.1 st.df (I.edge j).head hDInv huv.2).2 (I.edge j).tail huv.1
    have hFP_rats₁ : (∀ m, IsFixedPoint P (f m)) →
        ∀ q ∈ ((f j - (⌊f j⌋ : ℚ)) :: ((⌈f j⌉ : ℚ) - f j) :: st.computedRats),
          IsFixedPoint P q := by
      intro hfP q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact isFixedPoint_sub (hfP j) (isFixedPoint_int P _)
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact isFixedPoint_sub (isFixedPoint_int P _) (hfP j)
        · exact (hFP hfP).2.2 q hq
    have hM_rats₁ : (∀ m, |f m| + 1 ≤ M) →
        ∀ q ∈ ((f j - (⌊f j⌋ : ℚ)) :: ((⌈f j⌉ : ℚ) - f j) :: st.computedRats),
          |q| ≤ M := by
      intro hMf q hq
      have h1M : (1 : ℚ) ≤ M := by
        have := hMf j; have : (0 : ℚ) ≤ |f j| := abs_nonneg _; linarith
      rcases List.mem_cons.mp hq with rfl | hq
      · have h0 : 0 ≤ f j - (⌊f j⌋ : ℚ) := sub_nonneg.mpr (Int.floor_le (f j))
        have h1 : f j - (⌊f j⌋ : ℚ) ≤ 1 := by
          have := Int.sub_one_lt_floor (f j); linarith
        rw [abs_of_nonneg h0]; linarith
      · rcases List.mem_cons.mp hq with rfl | hq
        · have h0 : 0 ≤ (⌈f j⌉ : ℚ) - f j := sub_nonneg.mpr (Int.le_ceil (f j))
          have h1 : (⌈f j⌉ : ℚ) - f j ≤ 1 := by
            have := Int.ceil_lt_add_one (f j); linarith
          rw [abs_of_nonneg h0]; linarith
        · exact (hM hMf).1 q hq
    by_cases hdisc_r : D.findRoot st.df (I.edge j).tail ≠ D.findRoot st.df (I.edge j).head
    · dsimp only [roundEdgeStep]
      rw [ite_eq_right hfj_int]
      rw [ite_eq_left hdisc_r]
      have hdisc : ¬ (D.toForest st.df).SameComp (I.edge j).tail (I.edge j).head :=
        mt hr_iff.mpr hdisc_r
      have hnot_fe : ∀ e' ∈ (D.toForest st.df).edges, e'.eid ≠ j.1 := fun e' he' =>
        Nat.ne_of_lt (hEdges e' he').2
      let fe : ForestEdge :=
        { eid := j.1, u := (I.edge j).tail, v := (I.edge j).head,
          cost := (I.edge j).cost, flow := f j,
          availFwd := (⌈f j⌉ : ℚ) - f j, availBwd := f j - (⌊f j⌋ : ℚ) }
      have hLink := hSpec.2.2.2.1 st.df fe hDInv huv.1 huv.2 hdisc hnot_fe
      have hact_eq := actualFlow_link_eq hSpec hDInv huv.1 huv.2 hdisc hnot_fe st.flowArr
        (fe := fe) rfl (hUnproc j (le_refl k)).2.symm
      have hStrict_fe : ForestEdgeStrictInv I f fe := by
        have hp_f : 0 < (⌈f j⌉ : ℚ) - f j := by
          have : f j < (⌈f j⌉ : ℚ) := lt_of_le_of_ne (Int.le_ceil (f j)) (fun h => hj_frac ⟨⌈f j⌉, h⟩)
          linarith
        have hp_b : 0 < f j - (⌊f j⌋ : ℚ) := by
          have : (⌊f j⌋ : ℚ) < f j := lt_of_le_of_ne (Int.floor_le (f j)) (fun h => hj_frac ⟨⌊f j⌋, h.symm⟩)
          linarith
        exact ⟨⟨j, rfl, rfl, rfl, rfl, hj_frac, Int.floor_le _, Int.le_ceil _, rfl, rfl⟩, hp_f, hp_b⟩
      refine ⟨hLink.1, hLink.2.1.trans hn, ?_, ?_, ?_, ?_, ?_, ?_,
        by dsimp only; omega, by dsimp only; omega, ?_, by dsimp only; omega,
        by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, ?_, ?_, hcosts⟩
      · intro e he
        rcases List.mem_cons.mp (hLink.2.2.subset he) with rfl | he₀
        · exact ⟨hStrict_fe, Nat.lt_succ_self k⟩
        · exact ⟨(hEdges e he₀).1, Nat.lt_succ_of_lt (hEdges e he₀).2⟩
      · intro m hm_lt hm_not
        have hm_lt_k : m.1 < k := by
          by_contra hge
          have hj1 : j.1 = k := rfl
          have hmj : m = j := Fin.ext (by omega)
          rw [hmj] at hm_not
          exact hm_not (List.mem_map.mpr ⟨fe, hLink.2.2.symm.subset List.mem_cons_self, rfl⟩)
        have hm_not₀ : m.1 ∉ (D.toForest st.df).edges.map ForestEdge.eid := fun hm => by
          rw [List.mem_map] at hm
          obtain ⟨e, he, heq⟩ := hm
          exact hm_not (List.mem_map.mpr ⟨e, hLink.2.2.symm.subset (List.mem_cons_of_mem _ he), heq⟩)
        exact hProcInt m hm_lt_k hm_not₀
      · intro m hm_ge
        have hne_fe : m.1 ≠ fe.eid := by dsimp [fe]; have hj1 : j.1 = k := rfl; omega
        have hu := hUnproc m (Nat.le_trans (Nat.le_succ k) hm_ge)
        refine ⟨fun hm => ?_, hu.2⟩
        rw [List.mem_map] at hm
        obtain ⟨e, he, heq⟩ := hm
        rcases List.mem_cons.mp (hLink.2.2.subset he) with rfl | he₀
        · exact hne_fe heq.symm
        · exact hu.1 (List.mem_map.mpr ⟨e, he₀, heq⟩)
      · convert hRoutes using 2 with m; rw [hact_eq m]
      · intro m; rw [hact_eq m]; exact hBounds m
      · have hceq : I.cost (fun m => (actualFlow (D.toForest (D.link st.df fe)) st.flowArr m : ℝ)) =
            I.cost (fun m => (actualFlow (D.toForest st.df) st.flowArr m : ℝ)) := by
          congr 1 with m; rw [hact_eq m]
        rw [hceq]; exact hCost_le
      · change st.counts.cutOps + (D.toForest (D.link st.df fe)).edges.length = st.counts.linkOps + 1
        have hlen_l : (D.toForest (D.link st.df fe)).edges.length = (D.toForest st.df).edges.length + 1 := by
          rw [hLink.2.2.length_eq]; rfl
        rw [hlen_l]; omega
      · intro hfP
        obtain ⟨hFP_df, hFP_arr, _⟩ := hFP hfP
        refine ⟨fun e he => ?_, hFP_arr, hFP_rats₁ hfP⟩
        rcases List.mem_cons.mp (hLink.2.2.subset he) with rfl | he₀
        · exact ⟨hfP j, isFixedPoint_sub (isFixedPoint_int P _) (hfP j),
            isFixedPoint_sub (hfP j) (isFixedPoint_int P _)⟩
        · exact hFP_df e he₀
      · intro hMf
        exact ⟨hM_rats₁ hMf, (hM hMf).2⟩
    · have hr_eq : D.findRoot st.df (I.edge j).tail = D.findRoot st.df (I.edge j).head :=
        not_ne_iff.mp hdisc_r
      have hconn_uv : (D.toForest st.df).SameComp (I.edge j).tail (I.edge j).head :=
        hr_iff.mp hr_eq
      have hV : (D.toForest st.df).Valid := hSpec.2.1 st.df hDInv
      obtain ⟨stepsUV, hfsUV, hwUV, hndUV⟩ :=
        MathForest.findSteps_some_of_sameComp hV hconn_uv
      have hpathCost_eq : D.pathSum st.df (I.edge j).tail (I.edge j).head = stepsCost stepsUV := by
        rw [hSpec.2.2.2.2.2.2.2 st.df (I.edge j).tail (I.edge j).head hDInv hconn_uv]
        simp [MathForest.pathSum, hfsUV]
      have hlen_lt_min : stepsUV.length + 1 ≤ min I.n I.m := by
        have hlen_n : stepsUV.length < I.n := by
          rw [← hn]
          have hn_edges : ∀ z ∈ (D.toForest st.df).rawEdges,
              z.u < (D.toForest st.df).n ∧ z.v < (D.toForest st.df).n := by
            intro z hz
            unfold MathForest.rawEdges at hz
            rw [List.mem_map] at hz
            obtain ⟨e, he, rfl⟩ := hz
            have hev := hV.1 e he
            exact ⟨hev.1, hev.2.1⟩
          have hu_v : (I.edge j).tail < (D.toForest st.df).n := huv.1
          simpa [List.length_map] using
            hV.2.2.walk_length_lt hn_edges hu_v hwUV.to_isWalk hndUV
        have hlen_m : stepsUV.length ≤ (D.toForest st.df).edges.length := by
          have hsub_raw : stepsUV.map PathStep.toRaw ⊆ (D.toForest st.df).rawEdges := by
            intro z hz
            rw [List.mem_map] at hz
            obtain ⟨s, hs, rfl⟩ := hz
            exact List.mem_map.mpr ⟨s.edge, hwUV.mem_edges s hs, rfl⟩
          have hl := hndUV.length_le_of_subset hsub_raw
          simpa [MathForest.rawEdges] using hl
        omega
      have hpathCost_abs : |stepsCost stepsUV| ≤ (stepsUV.length : ℤ) * (I.maxCost : ℤ) :=
        stepsCost_abs_le (fun s hs => (hEdges s.edge (hwUV.mem_edges s hs)).1.1)
      have hmaxC_nn : (0 : ℤ) ≤ (I.maxCost : ℤ) := Int.natCast_nonneg _
      let pathCost := D.pathSum st.df (I.edge j).tail (I.edge j).head
      let cycCostFwd := (I.edge j).cost - pathCost
      let counts₂ : RoundCounts :=
        { st.counts with
          findRootOps := st.counts.findRootOps + 2
          pathSumOps := st.counts.pathSumOps + 1
          otherSteps := st.counts.otherSteps + 6 }
      let rats₁ := (f j - (⌊f j⌋ : ℚ)) :: ((⌈f j⌉ : ℚ) - f j) :: st.computedRats
      let costs₂ := cycCostFwd :: pathCost :: st.computedCosts
      have hcosts_new : ∀ c ∈ costs₂, |c| ≤ (min I.n I.m : ℤ) * (I.maxCost : ℤ) := by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · dsimp [cycCostFwd, pathCost]
          rw [hpathCost_eq]
          have hc1 := edge_cost_abs_le_maxCost I j
          have htri := abs_sub (I.edge j).cost (stepsCost stepsUV)
          have hmul : ((stepsUV.length : ℤ) + 1) * (I.maxCost : ℤ) ≤
              (min I.n I.m : ℤ) * (I.maxCost : ℤ) := by
            apply mul_le_mul_of_nonneg_right _ hmaxC_nn
            exact_mod_cast hlen_lt_min
          linarith
        · rcases List.mem_cons.mp hc with rfl | hc
          · dsimp [pathCost]
            rw [hpathCost_eq]
            have hmul : (stepsUV.length : ℤ) * (I.maxCost : ℤ) ≤
                (min I.n I.m : ℤ) * (I.maxCost : ℤ) := by
              apply mul_le_mul_of_nonneg_right _ hmaxC_nn
              exact_mod_cast Nat.le_trans (Nat.le_succ _) hlen_lt_min
            linarith
          · exact hcosts c hc
      by_cases hcyc_le : cycCostFwd ≤ 0
      · have hfsVU : findSteps (D.toForest st.df).edges (I.edge j).head (I.edge j).tail =
            some (stepsUV.reverse.map PathStep.flip) :=
          MathForest.findSteps_reverse hV hfsUV
        have hcostVU : stepsCost (stepsUV.reverse.map PathStep.flip) +
            (1 : ℤ) * (I.edge j).cost ≤ 0 := by
          rw [stepsCost_reverse_flip, ← hpathCost_eq]
          change -pathCost + (1 : ℤ) * (I.edge j).cost ≤ 0
          linarith [show cycCostFwd = (I.edge j).cost - pathCost from rfl]
        have hbr := cycBranch_preserves hSpec hValid hk hInv_copy hj_frac hfsVU 1
          ((⌈f j⌉ : ℚ) - f j) (Or.inl ⟨rfl, rfl, rfl, rfl⟩) hcostVU
          (counts₂ := counts₂) (rats₁ := rats₁) (costs₂ := costs₂)
          rfl rfl rfl rfl rfl rfl rfl hFP_rats₁ hM_rats₁ hcosts_new
        dsimp only [roundEdgeStep]
        rw [ite_eq_right hfj_int]
        rw [ite_eq_right hdisc_r]
        rw [ite_eq_left hcyc_le]
        dsimp only at hbr
        have hone : ∀ d : ℚ, (↑(1 : ℤ) : ℚ) * d = d := fun d => by norm_num
        simp only [hone] at hbr
        exact hbr
      · have hfsUV' : findSteps (D.toForest st.df).edges (I.edge j).tail (I.edge j).head =
            some stepsUV := hfsUV
        have hcostUV : stepsCost stepsUV + (-1 : ℤ) * (I.edge j).cost ≤ 0 := by
          rw [← hpathCost_eq]
          change pathCost + (-1 : ℤ) * (I.edge j).cost ≤ 0
          linarith [show cycCostFwd = (I.edge j).cost - pathCost from rfl]
        have hbr := cycBranch_preserves hSpec hValid hk hInv_copy hj_frac hfsUV' (-1)
          (f j - (⌊f j⌋ : ℚ)) (Or.inr ⟨rfl, rfl, rfl, rfl⟩) hcostUV
          (counts₂ := counts₂) (rats₁ := rats₁) (costs₂ := costs₂)
          rfl rfl rfl rfl rfl rfl rfl hFP_rats₁ hM_rats₁ hcosts_new
        dsimp only [roundEdgeStep]
        rw [ite_eq_right hfj_int]
        rw [ite_eq_right hdisc_r]
        rw [ite_eq_right hcyc_le]
        dsimp only at hbr
        have hneg : ∀ d : ℚ, f ⟨k, hk⟩ + (↑(-1 : ℤ) : ℚ) * d = f ⟨k, hk⟩ - d := fun d => by
          push_cast; ring
        simp only [hneg] at hbr
        exact hbr

end MinCostFlow.Rounding
