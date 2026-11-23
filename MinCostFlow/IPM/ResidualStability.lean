module

public import MinCostFlow.IPM.WeightedBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Residual stability

Lemma 4.8 (page 29) of Chen et al., arXiv:2203.00671v2, follows by separating the
cost term of the gradient from the barrier term. The latter has weighted
coordinate magnitude at most `α`. Hölder's inequality and the ratio
condition then bound the cost change. The proof needs only a positive
residual, so the target value may be a guess.
-/

public section
namespace MinCostFlow.IPM

private theorem barrier_gradient_tolerance (I : Instance) (a F : ℝ)
    (f : Fin I.m → ℝ) (hf : StrictlyInside I f) (ha : 0 ≤ a) :
    GradientTolerance (lengths I a f) (gradient I a F f)
      (fun e => 20 * I.m * (residual I F f)⁻¹ * (I.edge e).cost) a := by
  intro e
  have hp := Real.rpow_pos_of_pos (sub_pos.mpr (hf e).2) (-1-a)
  have hq := Real.rpow_pos_of_pos (sub_pos.mpr (hf e).1) (-1-a)
  rw [abs_div, abs_of_pos (lengths_pos I a f hf e)]
  apply (div_le_iff₀ (lengths_pos I a f hf e)).mpr
  unfold gradient lengths
  rw [show 20 * (I.m : ℝ) * (residual I F f)⁻¹ * (I.edge e).cost +
      a * Real.rpow ((I.edge e).upper - f e) (-1-a) -
      a * Real.rpow (f e - (I.edge e).lower) (-1-a) -
      20 * I.m * (residual I F f)⁻¹ * (I.edge e).cost =
      a * Real.rpow ((I.edge e).upper - f e) (-1-a) -
      a * Real.rpow (f e - (I.edge e).lower) (-1-a) by ring]
  simp only [Real.rpow_eq_pow]
  apply abs_le.mpr
  constructor <;> nlinarith only [mul_nonneg ha hp.le, mul_nonneg ha hq.le]

/-- The cost term differs from the full gradient only by a barrier term of
weighted magnitude at most `α`, as used in Lemma 4.8 (page 29). -/
theorem abs_cost_term_le (I : Instance) (a F : ℝ) (f x : Fin I.m → ℝ)
    (hf : StrictlyInside I f) (ha : 0 ≤ a) :
    |20 * I.m * (residual I F f)⁻¹ * I.cost x| ≤
      |dot (gradient I a F f) x| + a * weightedLength (lengths I a f) x := by
  let c : Fin I.m → ℝ := fun e => 20 * I.m * (residual I F f)⁻¹ * (I.edge e).cost
  have he := abs_dot_error_le (lengths I a f) (gradient I a F f) c x a
    (lengths_pos I a f hf) (barrier_gradient_tolerance I a F f hf ha)
  have hid : dot c x = 20 * I.m * (residual I F f)⁻¹ * I.cost x := by
    simp only [dot, c, Instance.cost, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hid] at he
  have htri := abs_sub_le (20 * I.m * (residual I F f)⁻¹ * I.cost x)
    (dot (gradient I a F f) x) 0
  rw [sub_zero, sub_zero] at htri
  rw [abs_sub_comm] at he
  linarith only [htri, he]

/-- Lemma 4.8 (page 29) (residual stability). The proof uses `0 ≤ α ≤ 1/2`;
these bounds follow from the paper's parameter choice in its nondegenerate
range. No optimality assumption on the target is required. -/
theorem lemma_4_8 (I : Instance) (a F ε κ : ℝ) (f gApprox lApprox x : Fin I.m → ℝ)
    (hm : 0 < I.m) (hf : StrictlyInside I f) (hr : 0 < residual I F f)
    (ha : 0 ≤ a) (ha' : a ≤ 1/2) (hε : ε ≤ 1/2)
    (hκ : 0 < κ) (hκ' : κ < 1)
    (hg : GradientTolerance (lengths I a f) gApprox (gradient I a F f) ε)
    (hl : VectorApprox 2 lApprox (lengths I a f))
    (hx : 0 < weightedLength lApprox x)
    (hquality : dot gApprox x / weightedLength lApprox x ≤ -κ) :
    |I.cost x| / residual I F f ≤ |dot gApprox x| / (κ * I.m) := by
  have hlen := weightedLength_le_two I a f lApprox x hf hl
  have herr := abs_dot_error_le (lengths I a f) gApprox (gradient I a F f) x ε
    (lengths_pos I a f hf) hg
  have hcost := abs_cost_term_le I a F f x hf ha
  have hgrad : |dot (gradient I a F f) x| ≤
      |dot gApprox x| + ε * weightedLength (lengths I a f) x := by
    have ht := abs_sub_le (dot (gradient I a F f) x) (dot gApprox x) 0
    rw [sub_zero, sub_zero] at ht
    rw [abs_sub_comm] at herr
    linarith only [ht, herr]
  have hnonneg : 0 ≤ weightedLength (lengths I a f) x :=
    Finset.sum_nonneg fun e _ => abs_nonneg _
  have hbound : ε * weightedLength (lengths I a f) x +
      a * weightedLength (lengths I a f) x ≤
      2 * weightedLength lApprox x := by
    have heps := mul_le_mul_of_nonneg_right hε hnonneg
    have halpha := mul_le_mul_of_nonneg_right ha' hnonneg
    linarith only [heps, halpha, hlen]
  have hratio := (div_le_iff₀ hx).mp hquality
  have hneg : dot gApprox x < 0 :=
    lt_of_le_of_lt hratio (mul_neg_of_neg_of_pos (neg_neg_of_pos hκ) hx)
  have hq : κ * weightedLength lApprox x ≤ |dot gApprox x| := by
    rw [abs_of_neg hneg]
    linarith only [hratio]
  have hm' : (0 : ℝ) < I.m := Nat.cast_pos.mpr hm
  have hfactor : 0 < 20 * (I.m : ℝ) * (residual I F f)⁻¹ :=
    mul_pos (mul_pos (by norm_num) hm') (inv_pos.mpr hr)
  rw [abs_mul, abs_of_pos hfactor] at hcost
  have hc : 20 * I.m * (|I.cost x| / residual I F f) ≤
      |dot gApprox x| + 2 * weightedLength lApprox x := by
    rw [div_eq_mul_inv]
    nlinarith only [hcost, hgrad, hbound]
  apply (le_div_iff₀ (mul_pos hκ hm')).mpr
  have hmul := mul_le_mul_of_nonneg_left hc hκ.le
  have hga : 0 ≤ |dot gApprox x| := abs_nonneg _
  have hsmall := mul_le_mul_of_nonneg_right hκ'.le hga
  have hcpos : 0 ≤ |I.cost x| / residual I F f := div_nonneg (abs_nonneg _) hr.le
  nlinarith only [hmul, hq, hsmall, mul_nonneg (mul_nonneg hκ.le hm'.le) hcpos]

end MinCostFlow.IPM
