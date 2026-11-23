module

public import MinCostFlow.IPM.FractionalCycle
public import MinCostFlow.IPM.Optimum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# An integral optimum for the cost search

Section 4 of Chen et al., arXiv:2203.00671v2 (page 24), searches for an
integer optimal cost. On the compact set of optimal flows, maximize the
sum of squared coordinates. A cycle of fractional edges permits two
opposite small feasible steps. Optimality makes their costs equal, but
their squared coordinate sums cannot both be at most the maximum.
The fractional edges therefore form a forest. Kang--Payor Lemma 3.1,
already proved in the rounding library, makes the flow integral.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

private theorem fractional_steps (I : Instance) (f d : Fin I.m → ℝ)
    (hf : I.IsFeasible f) (hd : IsCirculation I d)
    (hfrac : ∀ e, d e ≠ 0 → ¬ ∃ z : ℤ, f e = z) :
    ∃ t : ℝ, 0 < t ∧ I.IsFeasible (fun e => f e+t*d e) ∧
      I.IsFeasible (fun e => f e-t*d e) := by
  classical
  let margin : Fin I.m → ℝ := fun e =>
    min (f e-(I.edge e).lower) ((I.edge e).upper-f e)
  have hm : ∀ e, d e ≠ 0 → 0 < margin e := by
    intro e he
    have hne := hfrac e he
    apply lt_min
    · exact sub_pos.mpr (lt_of_le_of_ne (hf.2 e).1 (fun h => hne ⟨(I.edge e).lower, h.symm⟩))
    · exact sub_pos.mpr (lt_of_le_of_ne (hf.2 e).2 (fun h => hne ⟨(I.edge e).upper, h⟩))
  let rate : Fin I.m → ℝ := fun e => if d e = 0 then 1 else margin e/(|d e|+1)
  have hr : ∀ e, 0 < rate e := by
    intro e
    dsimp only [rate]
    split_ifs with he
    · norm_num
    · exact div_pos (hm e he) (by linarith only [abs_nonneg (d e)])
  let S : Finset ℝ := insert 1 (Finset.univ.image rate)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let t := S.min' hS
  have ht : 0 < t := by
    apply (Finset.lt_min'_iff S hS).mpr
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx
      exact hr e
  have hsize : ∀ e, |t*d e| ≤ margin e := by
    intro e
    by_cases he : d e = 0
    · simp only [he, mul_zero, abs_zero]
      exact le_min (sub_nonneg.mpr (hf.2 e).1) (sub_nonneg.mpr (hf.2 e).2)
    · have hmin : t ≤ rate e := Finset.min'_le S _
        (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩))
      have heq : rate e*(|d e|+1) = margin e := by
        dsimp only [rate]
        rw [ite_eq_right he, div_mul_cancel₀ _ (by linarith only [abs_nonneg (d e)] : |d e|+1 ≠ 0)]
      have hprod := mul_le_mul_of_nonneg_right hmin (abs_nonneg (d e))
      rw [abs_mul, abs_of_pos ht]
      nlinarith only [hprod, heq, hr e]
  have hroute : ∀ s : ℝ, I.Routes (fun e => f e+s*d e) := by
    intro s v
    calc
      _ = (∑ e, (I.edge e).b v*f e)+s*(∑ e, (I.edge e).b v*d e) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = I.d v := by rw [hf.1 v, hd v, mul_zero, add_zero]
  refine ⟨t, ht, ⟨hroute t, ?_⟩, ⟨?_, ?_⟩⟩
  · intro e
    have hh := abs_le.mp (hsize e)
    have hlo := min_le_left (f e-(I.edge e).lower) ((I.edge e).upper-f e)
    have hup := min_le_right (f e-(I.edge e).lower) ((I.edge e).upper-f e)
    change margin e ≤ _ at hlo hup
    constructor <;> linarith only [hh.1, hh.2, hlo, hup]
  · simpa only [neg_mul, ← sub_eq_add_neg] using hroute (-t)
  · intro e
    have hh := abs_le.mp (hsize e)
    have hlo := min_le_left (f e-(I.edge e).lower) ((I.edge e).upper-f e)
    have hup := min_le_right (f e-(I.edge e).lower) ((I.edge e).upper-f e)
    change margin e ≤ _ at hlo hup
    constructor <;> linarith only [hh.1, hh.2, hlo, hup]

/-- Any feasible instance has an integral minimum-cost flow. This supplies
the integer optimal value needed by the binary search proposed in Section 4
(page 24) of Chen et al., arXiv:2203.00671v2. -/
theorem exists_integral_minCostFlow (I : Instance) (hI : I.IsValid)
    (hne : ∃ f, I.IsFeasible f) :
    ∃ f, I.IsMinCostFlow f ∧ Rounding.IsIntegral f := by
  classical
  obtain ⟨fstar, hs⟩ := exists_minCostFlow I hne
  let S : Set (Fin I.m → ℝ) := {f | I.IsFeasible f ∧ I.cost f = I.cost fstar}
  have hS : IsCompact S := (isCompact_feasible I).inter_right
    (isClosed_eq (continuous_cost I) continuous_const)
  have hneS : S.Nonempty := ⟨fstar, hs.1, rfl⟩
  have hcont : Continuous (fun f : Fin I.m → ℝ => ∑ e, (f e)^2) :=
    continuous_finsetSum _ fun e _ => (continuous_apply e).pow 2
  obtain ⟨f, hf, hmax⟩ := hS.exists_isMaxOn hneS hcont.continuousOn
  have hopt : I.IsMinCostFlow f := ⟨hf.1, fun g hg => by rw [hf.2]; exact hs.2 g hg⟩
  refine ⟨f, hopt, Rounding.lemma_3_1 hI hf.1.1 ?_⟩
  by_contra hcycle
  obtain ⟨d, hd, ⟨e, he⟩, hfrac⟩ := fractional_cycle_direction I f hcycle
  obtain ⟨t, ht, hp, hn⟩ := fractional_steps I f d hf.1 hd hfrac
  have hcp : I.cost (fun e => f e+t*d e) = I.cost f+t*I.cost d := by
    simp only [Instance.cost, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hcn : I.cost (fun e => f e-t*d e) = I.cost f-t*I.cost d := by
    simp only [Instance.cost, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hop := hopt.2 _ hp
  have hon := hopt.2 _ hn
  rw [hcp] at hop
  rw [hcn] at hon
  have hc : t*I.cost d = 0 := by linarith only [hop, hon]
  have hmp := hmax (show (fun e => f e+t*d e) ∈ S from ⟨hp, by rw [hcp, hc, add_zero, hf.2]⟩)
  have hmn := hmax (show (fun e => f e-t*d e) ∈ S from ⟨hn, by rw [hcn, hc, sub_zero, hf.2]⟩)
  change (∑ e, (f e+t*d e)^2) ≤ ∑ e, (f e)^2 at hmp
  change (∑ e, (f e-t*d e)^2) ≤ ∑ e, (f e)^2 at hmn
  have hidentity : (∑ e, (f e+t*d e)^2)+(∑ e, (f e-t*d e)^2) =
      2*(∑ e, (f e)^2)+2*t^2*(∑ e, (d e)^2) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hsumpos : 0 < ∑ e, (d e)^2 := lt_of_lt_of_le (sq_pos_of_ne_zero he)
    (Finset.single_le_sum (fun j _ => sq_nonneg (d j)) (Finset.mem_univ e))
  have hpos : 0 < 2*t^2*(∑ e, (d e)^2) := mul_pos
    (mul_pos (by norm_num) (sq_pos_of_pos ht)) hsumpos
  linarith only [hmp, hmn, hidentity, hpos]

/-- Integral flows have integer cost because each edge cost is an integer. -/
theorem integral_cost (I : Instance) (f : Fin I.m → ℝ) (hf : Rounding.IsIntegral f) :
    ∃ z : ℤ, I.cost f = z := by
  choose z hz using hf
  refine ⟨∑ e, (I.edge e).cost*z e, ?_⟩
  simp only [Instance.cost, Int.cast_sum, Int.cast_mul, hz]

end MinCostFlow.IPM
