module

public import MinCostFlow.Rounding.Cycles
import Mathlib.Tactic.FieldSimp

/-!
# Flow rounding: Lemma 4.1 (Kang–Payor Section 4)

This file proves the loop-invariant base case and inductive theorem (`roundFlowLoop_inv`), the
rational soundness, termination, exact operation-count, fixed-point precision, and magnitude-bound
theorem (`roundFlow_correct`), and **Lemma 4.1** of `arXiv:2309.16629v1` (page 13, from Kang–Payor
`arXiv:1507.08139v1`, Section 4) for flows whose entries are multiples of `2^{-P}`.
-/

@[expose] public section

namespace MinCostFlow.Rounding

/-- Maximum absolute value among the coordinates of a rational flow `f` (`0` if `I.m = 0`). -/
def maxAbsFlow (I : Instance) (f : Fin I.m → ℚ) : ℚ :=
  (List.finRange I.m).foldr (fun j acc => max |f j| acc) 0

private theorem maxAbsFlow_nonneg_aux {α : Type*} (g : α → ℚ) :
    ∀ l : List α, 0 ≤ l.foldr (fun j acc => max |g j| acc) 0 := by
  intro l
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons]
    exact le_trans ih (le_max_right _ _)

private theorem le_maxAbsFlow_aux {α : Type*} (g : α → ℚ) :
    ∀ l : List α, ∀ x ∈ l, |g x| ≤ l.foldr (fun j acc => max |g j| acc) 0 := by
  intro l x hx
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih hx) (le_max_right _ _)

theorem maxAbsFlow_nonneg (I : Instance) (f : Fin I.m → ℚ) : 0 ≤ maxAbsFlow I f :=
  maxAbsFlow_nonneg_aux f (List.finRange I.m)

theorem abs_le_maxAbsFlow {I : Instance} (f : Fin I.m → ℚ) (j : Fin I.m) :
    |f j| ≤ maxAbsFlow I f :=
  le_maxAbsFlow_aux f (List.finRange I.m) j (List.mem_finRange j)

/-- The loop invariant holds after processing the first `k ≤ I.m` edges of `I`. -/
theorem roundFlowLoop_inv {D : DynForest} (hSpec : D.IsSpec) {I : Instance}
    (hValid : I.IsValid) {f : Fin I.m → ℚ} (hRoutes : I.Routes fun j => (f j : ℝ))
    (P : ℕ) (M : ℚ) (k : ℕ) (hk : k ≤ I.m) :
    LoopInv D I f P M k (roundFlowLoop D I f k hk) := by
  induction k with
  | zero =>
    dsimp only [roundFlowLoop]
    have hInit := hSpec.1 I.n
    have hEmpty : (D.toForest (D.init I.n)).edges = [] :=
      List.eq_nil_of_length_eq_zero (by simpa [MathForest.empty] using hInit.2.2.length_eq)
    have hn_eq : (D.toForest (D.init I.n)).n = I.n := hInit.2.1
    have hact_eq : ∀ j : Fin I.m, actualFlow (D.toForest (D.init I.n)) f j = f j := fun j =>
      actualFlow_of_not_mem f (by simp [hEmpty])
    refine ⟨hInit.1, hn_eq, ?_, ?_, ?_, ?_, ?_, ?_,
      by dsimp only; omega, by dsimp only; omega, ?_, by dsimp only; omega,
      by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, ?_, ?_, ?_⟩
    · intro e he; simp [hEmpty] at he
    · intro j hj; omega
    · intro j _; exact ⟨by simp [hEmpty], rfl⟩
    · convert hRoutes using 2 with j; rw [hact_eq j]
    · intro j; rw [hact_eq j]; exact ⟨Int.floor_le _, Int.le_ceil _⟩
    · have hceq : I.cost (fun j => (actualFlow (D.toForest (D.init I.n)) f j : ℝ)) =
          I.cost (fun j => (f j : ℝ)) := by
        congr 1 with j; rw [hact_eq j]
      rw [hceq]
    · simp [hEmpty]
    · intro hfP
      refine ⟨fun e he => by simp [hEmpty] at he, hfP, fun q hq => ?_⟩
      simp only [List.mem_map, List.mem_finRange, true_and] at hq
      obtain ⟨j, rfl⟩ := hq
      exact hfP j
    · intro hMf
      refine ⟨fun q hq => ?_, fun j => ?_⟩
      · simp only [List.mem_map, List.mem_finRange, true_and] at hq
        obtain ⟨j, rfl⟩ := hq
        linarith [hMf j]
      · linarith [hMf j]
    · intro c hc; simp at hc
  | succ k ih =>
    dsimp only [roundFlowLoop]
    exact roundEdgeStep_preserves hSpec hValid hk (ih (Nat.le_of_succ_le hk))

/-- Correctness, termination (emptiness of the final fractional forest), explicit operation counts
(`treeOps ≤ 10 * I.m`, `otherSteps ≤ 19 * I.m`), `2^{-P}` fixed-point closure, and magnitude bounds
for `roundFlow D I f` on rational feasible flows `f`. -/
theorem roundFlow_correct {D : DynForest} (hSpec : D.IsSpec) {I : Instance}
    (hValid : I.IsValid) {f : Fin I.m → ℚ}
    (hFeas : I.IsFeasible fun j => (f j : ℝ)) (P : ℕ) (M : ℚ) :
    let res := roundFlow D I f
    let f' : Fin I.m → ℝ := fun j => (res.flowArr j : ℝ)
    (D.toForest res.df).edges = [] ∧
    (∀ j : Fin I.m, ∃ z : ℤ, res.flowArr j = z) ∧
    IsIntegral f' ∧
    I.IsFeasible f' ∧
    I.cost f' ≤ I.cost (fun j => (f j : ℝ)) ∧
    res.counts.treeOps ≤ 10 * I.m ∧
    res.counts.otherSteps ≤ 19 * I.m ∧
    ((∀ j, IsFixedPoint P (f j)) →
      (∀ j, IsFixedPoint P (res.flowArr j)) ∧
      (∀ q ∈ res.computedRats, IsFixedPoint P q)) ∧
    ((∀ j, |f j| + 1 ≤ M) →
      (∀ j, |res.flowArr j| ≤ M) ∧
      (∀ q ∈ res.computedRats, |q| ≤ M)) ∧
    (∀ c ∈ res.computedCosts, |c| ≤ (min I.n I.m : ℤ) * (I.maxCost : ℤ)) := by
  intro res f'
  have hInv := roundFlowLoop_inv hSpec hValid hFeas.1 P M I.m (Nat.le_refl _)
  change LoopInv D I f P M I.m res at hInv
  obtain ⟨hDInv, _, hEdges, hProcInt, _, hRoutes_act, hBounds_act, hCost_act,
    hc_fr, hc_lk, hc_cut, hc_ps, hc_pa, hc_pm, hc_os, hFP, hM, hcosts⟩ := hInv
  have hV : (D.toForest res.df).Valid := hSpec.2.1 res.df hDInv
  let outFlow : Fin I.m → ℝ := fun j => (actualFlow (D.toForest res.df) res.flowArr j : ℝ)
  have hsub_frac : fracEdges I outFlow ⊆ (D.toForest res.df).rawEdges := by
    intro r hr
    obtain ⟨j, rfl, hj_frac⟩ := mem_fracEdges_iff.mp hr
    by_cases hm : j.1 ∈ (D.toForest res.df).edges.map ForestEdge.eid
    · rw [List.mem_map] at hm
      obtain ⟨e, he, heq⟩ := hm
      obtain ⟨k, heid_k, hu_k, hv_k, _⟩ := (hEdges e he).1.1
      have hjk : j = k := Fin.ext (heq.symm.trans heid_k)
      subst hjk
      have hraw : rawEdge I j = e.toRaw := by
        simp [rawEdge, ForestEdge.toRaw, heid_k, hu_k, hv_k]
      rw [hraw]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    · exfalso
      obtain ⟨z, hz⟩ := hProcInt j j.2 hm
      exact hj_frac ⟨z, by dsimp [outFlow]; rw [actualFlow_of_not_mem res.flowArr hm, hz]; simp⟩
  have hout_int : IsIntegral outFlow :=
    lemma_3_1 hValid hRoutes_act (hV.2.2.mono hsub_frac)
  have hEmpty : (D.toForest res.df).edges = [] := by
    cases hlist : (D.toForest res.df).edges with
    | nil => rfl
    | cons e rest =>
      exfalso
      have he : e ∈ (D.toForest res.df).edges := by rw [hlist]; exact List.mem_cons_self
      have hStrict := (hEdges e he).1
      have he_lt := (hEdges e he).2
      let j : Fin I.m := ⟨e.eid, he_lt⟩
      obtain ⟨z, hz⟩ := hout_int j
      have hact_e : actualFlow (D.toForest res.df) res.flowArr j = e.flow :=
        actualFlow_of_mem hV.2.1 res.flowArr he rfl
      apply hStrict.isFrac
      refine ⟨z, ?_⟩
      dsimp [outFlow] at hz
      rw [hact_e] at hz
      exact_mod_cast hz
  have hact_eq : ∀ j : Fin I.m, actualFlow (D.toForest res.df) res.flowArr j = res.flowArr j :=
    fun j => actualFlow_of_not_mem res.flowArr (by simp [hEmpty])
  have hcut_le : res.counts.cutOps ≤ I.m := by
    rw [hEmpty, List.length_nil] at hc_cut
    omega
  have hInt_arr : ∀ j : Fin I.m, ∃ z : ℤ, res.flowArr j = z := by
    intro j
    obtain ⟨z, hz⟩ := hout_int j
    refine ⟨z, ?_⟩
    dsimp [outFlow] at hz
    rw [hact_eq j] at hz
    exact_mod_cast hz
  have hFeas_f' : I.IsFeasible f' := by
    refine lemma_3_3_feasible hFeas ?_ ?_
    · convert hRoutes_act using 2 with j
      rw [hact_eq j]
    · intro j
      have hb := hBounds_act j
      rw [hact_eq j] at hb
      have hfloor_eq : ⌊(f j : ℝ)⌋ = ⌊f j⌋ :=
        Int.floor_eq_iff.mpr ⟨by exact_mod_cast Int.floor_le (f j),
          by exact_mod_cast Int.lt_floor_add_one (f j)⟩
      have hceil_eq : ⌈(f j : ℝ)⌉ = ⌈f j⌉ :=
        Int.ceil_eq_iff.mpr ⟨by exact_mod_cast (by linarith [Int.ceil_lt_add_one (f j)] : (⌈f j⌉ : ℚ) - 1 < f j),
          by exact_mod_cast Int.le_ceil (f j)⟩
      simp only [availFwd, availBwd, f', hceil_eq, hfloor_eq, sub_nonneg]
      exact ⟨by exact_mod_cast hb.2, by exact_mod_cast hb.1⟩
  have hCost_f' : I.cost f' ≤ I.cost (fun j => (f j : ℝ)) := by
    have hceq : I.cost f' = I.cost outFlow := by
      congr 1 with j; dsimp [f', outFlow]; rw [hact_eq j]
    rw [hceq]
    exact hCost_act
  have hTreeOps : res.counts.treeOps ≤ 10 * I.m := by
    unfold RoundCounts.treeOps
    omega
  have hOtherSteps : res.counts.otherSteps ≤ 19 * I.m := by
    omega
  refine ⟨hEmpty, hInt_arr, fun j => by obtain ⟨z, hz⟩ := hInt_arr j; exact ⟨z, by simp [f', hz]⟩,
    hFeas_f', hCost_f', hTreeOps, hOtherSteps, ?_, ?_, hcosts⟩
  · intro hfP
    have h := hFP hfP
    exact ⟨h.2.1, h.2.2⟩
  · intro hMf
    have h := hM hMf
    exact ⟨h.2, h.1⟩

/-- **Lemma 4.1** (`arXiv:2309.16629v1`, page 13, from [KangP15, Section 4]):
Given a valid min-cost flow instance `I` and a feasible fractional flow `f : Fin I.m → ℝ` whose
coordinates are multiples of `2^{-P}`, there is an exact rational representation `fQ` of `f` on
which Section 4's dynamic-forest algorithm `roundFlow D I fQ` returns an integral feasible flow
`f'` of cost `I.cost f' ≤ I.cost f`, performing at most `20 * I.m` dynamic-tree operations (`≤ 10 * I.m`)
and at most `20 * I.m` other steps (`≤ 19 * I.m`). Every intermediate and output rational is a
multiple of `2^{-P}` bounded in absolute value by `maxAbsFlow I fQ + 1` (and every intermediate
cost is an integer bounded in absolute value by `min I.n I.m * I.maxCost`). -/
theorem lemma_4_1 {D : DynForest} (hSpec : D.IsSpec) {I : Instance} (hValid : I.IsValid)
    {f : Fin I.m → ℝ} (hFeas : I.IsFeasible f) {P : ℕ}
    (hfP : ∀ j : Fin I.m, ∃ z : ℤ, f j = (z : ℝ) / (2 : ℝ) ^ P) :
    ∃ fQ : Fin I.m → ℚ, (∀ j, (fQ j : ℝ) = f j) ∧
      let res := roundFlow D I fQ
      let f' : Fin I.m → ℝ := fun j => (res.flowArr j : ℝ)
      let M : ℚ := maxAbsFlow I fQ + 1
      IsIntegral f' ∧
      I.IsFeasible f' ∧
      I.cost f' ≤ I.cost f ∧
      res.counts.treeOps ≤ 20 * I.m ∧
      res.counts.otherSteps ≤ 20 * I.m ∧
      (∀ j, IsFixedPoint P (res.flowArr j)) ∧
      (∀ q ∈ res.computedRats, IsFixedPoint P q) ∧
      (∀ j, |res.flowArr j| ≤ M) ∧
      (∀ q ∈ res.computedRats, |q| ≤ M) ∧
      (∀ c ∈ res.computedCosts, |c| ≤ (min I.n I.m : ℤ) * (I.maxCost : ℤ)) := by
  let fQ : Fin I.m → ℚ := fun j => ((⌊f j * (2 : ℝ) ^ P⌋ : ℤ) : ℚ) / (2 : ℚ) ^ P
  have hfQ_real : ∀ j, (fQ j : ℝ) = f j := by
    intro j
    obtain ⟨z, hz⟩ := hfP j
    have h2 : (2 : ℝ) ^ P ≠ 0 := pow_ne_zero P (by norm_num)
    have hmul : f j * (2 : ℝ) ^ P = (z : ℝ) := by
      rw [hz]
      field_simp [h2]
    have hfl : ⌊f j * (2 : ℝ) ^ P⌋ = z := by
      rw [hmul, Int.floor_intCast]
    dsimp [fQ]
    rw [hfl]
    push_cast
    exact hz.symm
  have hFeasQ : I.IsFeasible fun j => (fQ j : ℝ) := by
    convert hFeas using 2 with j
    exact hfQ_real j
  have hFPQ : ∀ j, IsFixedPoint P (fQ j) := fun j => ⟨⌊f j * (2 : ℝ) ^ P⌋, rfl⟩
  let M : ℚ := maxAbsFlow I fQ + 1
  have hMQ : ∀ j, |fQ j| + 1 ≤ M := fun j => by
    dsimp [M]
    linarith [abs_le_maxAbsFlow fQ j]
  have hcorr := roundFlow_correct hSpec hValid hFeasQ P M
  have hcost_eq : I.cost (fun j => (fQ j : ℝ)) = I.cost f := by
    congr 1 with j
    exact hfQ_real j
  refine ⟨fQ, hfQ_real, hcorr.2.2.1, hcorr.2.2.2.1, hcost_eq ▸ hcorr.2.2.2.2.1,
    le_trans hcorr.2.2.2.2.2.1 (by omega), le_trans hcorr.2.2.2.2.2.2.1 (by omega),
    (hcorr.2.2.2.2.2.2.2.1 hFPQ).1, (hcorr.2.2.2.2.2.2.2.1 hFPQ).2,
    (hcorr.2.2.2.2.2.2.2.2.1 hMQ).1, (hcorr.2.2.2.2.2.2.2.2.1 hMQ).2,
    hcorr.2.2.2.2.2.2.2.2.2⟩

end MinCostFlow.Rounding
