module

public import MinCostFlow.IPM.RecoveryWalk
import MinCostFlow.IPM.StepTaylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Feasible small residual-cycle steps

The real-flow repair of Appendix B.1 (page 92) of Chen et al., arXiv:2203.00671v2,
takes a sufficiently small step along a residual cycle. Each coordinate
has the sign of the difference of two feasible flows. A finite positive
minimum makes the step stay between their coordinate values. This proves
feasibility without assuming that the starting flow is integral.
-/

public section
namespace MinCostFlow.IPM

private theorem exists_uniform_step {m : ℕ} (d p : Fin m → ℝ)
    (hzero : ∀ e, d e = 0 → p e = 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ e, t*|p e| ≤ |d e| := by
  classical
  let rate : Fin m → ℝ := fun e => if d e = 0 then 1 else |d e|/(|p e|+1)
  have hr : ∀ e, 0 < rate e := by
    intro e
    dsimp only [rate]
    split_ifs with h
    · norm_num
    · exact div_pos (abs_pos.mpr h) (by linarith only [abs_nonneg (p e)])
  let S : Finset ℝ := insert 1 (Finset.univ.image rate)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have ht : 0 < S.min' hS := by
    apply (Finset.lt_min'_iff S hS).mpr
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx
      exact hr e
  refine ⟨S.min' hS, ht, ?_⟩
  intro e
  by_cases hz : d e = 0
  · simp only [hzero e hz, abs_zero, mul_zero, hz, le_refl]
  · have hmin : S.min' hS ≤ rate e :=
      Finset.min'_le S (rate e) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩))
    have hprod := mul_le_mul_of_nonneg_right hmin (abs_nonneg (p e))
    have heq : rate e*(|p e|+1) = |d e| := by
      dsimp only [rate]
      rw [ite_eq_right hz, div_mul_cancel₀ _ (by linarith only [abs_nonneg (p e)] : |p e|+1 ≠ 0)]
    nlinarith only [hprod, heq, hr e]

/-- A sufficiently small supported circulation step stays feasible.
The comparison flow is used only for its coordinate capacity bounds. -/
theorem exists_feasible_walk_step (I : Instance) (g f : Fin I.m → ℝ)
    (hg : I.IsFeasible g) (hf : I.IsFeasible f) (P : List (Fin I.m × Bool))
    (hP : ∀ a ∈ P, ArcSupported (fun e => f e-g e) a)
    (hcirc : IsCirculation I (instanceWalkFlow P)) :
    ∃ t : ℝ, 0 < t ∧ I.IsFeasible (fun e => g e+t*instanceWalkFlow P e) := by
  have hsign := instanceWalkFlow_signs P (fun e => f e-g e) hP
  obtain ⟨t, ht, hsize⟩ := exists_uniform_step (fun e => f e-g e) (instanceWalkFlow P)
    (fun e he => (hsign e).2.2 he)
  refine ⟨t, ht, ?_, ?_⟩
  · intro v
    simp only [mul_add, Finset.sum_add_distrib]
    have hz : (∑ e, (I.edge e).b v*(t*instanceWalkFlow P e)) = 0 := by
      calc
        _ = t*(∑ e, (I.edge e).b v*instanceWalkFlow P e) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          ring
        _ = 0 := by rw [hcirc v, mul_zero]
    rw [hz, add_zero]
    exact hg.1 v
  · intro e
    rcases le_total 0 (f e-g e) with hd | hd
    · have hp : 0 ≤ instanceWalkFlow P e := (hsign e).1 hd
      have hbound := hsize e
      rw [abs_of_nonneg hp, abs_of_nonneg hd] at hbound
      have hstep := mul_nonneg ht.le hp
      constructor <;> linarith only [(hg.2 e).1, (hf.2 e).2, hbound, hstep]
    · have hp : instanceWalkFlow P e ≤ 0 := (hsign e).2.1 hd
      have hbound := hsize e
      rw [abs_of_nonpos hp, abs_of_nonpos hd] at hbound
      have hstep := mul_nonpos_of_nonneg_of_nonpos ht.le hp
      constructor <;> linarith only [(hf.2 e).1, (hg.2 e).2, hbound, hstep]

/-- No negative-cost supported circulation can occur at an optimum when
its residual comparison flow is feasible. -/
theorem no_negative_supported_walk (I : Instance) (g f : Fin I.m → ℝ)
    (hg : I.IsMinCostFlow g) (hf : I.IsFeasible f) (P : List (Fin I.m × Bool))
    (hP : ∀ a ∈ P, ArcSupported (fun e => f e-g e) a)
    (hcirc : IsCirculation I (instanceWalkFlow P)) : 0 ≤ I.cost (instanceWalkFlow P) := by
  by_contra hnegative
  have hnegative' : I.cost (instanceWalkFlow P) < 0 := lt_of_not_ge hnegative
  obtain ⟨t, ht, hfeas⟩ := exists_feasible_walk_step I g f hg.1 hf P hP hcirc
  have hopt := hg.2 _ hfeas
  have hcost : I.cost (fun e => g e+t*instanceWalkFlow P e) =
      I.cost g+t*I.cost (instanceWalkFlow P) := by
    rw [cost_add]
    congr 1
    simp only [Instance.cost, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hcost] at hopt
  have hlt := mul_neg_of_pos_of_neg ht hnegative'
  linarith only [hopt, hlt]

end MinCostFlow.IPM
