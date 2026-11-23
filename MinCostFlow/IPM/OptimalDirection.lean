module

public import MinCostFlow.IPM.WeightedBounds
public import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The direction to an optimum

Lemma 4.7 (page 28) of Chen et al., arXiv:2203.00671v2, bounds the ratio of the
direction from the current flow to an optimum. Its proof bounds each edge's
barrier contribution, sums these bounds, and uses the potential budget.
The matrix in the gradient error hypothesis is `L(f)`, correcting the
source's `L(g)`.
-/

public section
namespace MinCostFlow.IPM

private theorem power_times_slack (p a : ℝ) (hp : 0 < p) :
    Real.rpow p (-1-a) * p = Real.rpow p (-a) := by
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_add_one hp.ne', show (-1-a)+1 = -a by ring]

private theorem edge_direction_bound (p q a d : ℝ)
    (hp : 0 < p) (hq : 0 < q) (ha : 0 ≤ a) (hd : -q ≤ d ∧ d ≤ p) :
    (a * Real.rpow p (-1-a) - a * Real.rpow q (-1-a)) * d ≤
      -a * (Real.rpow p (-1-a) + Real.rpow q (-1-a)) * |d| +
        2*a*(Real.rpow p (-a) + Real.rpow q (-a)) := by
  have hp' : 0 ≤ Real.rpow p (-1-a) := (Real.rpow_pos_of_pos hp _).le
  have hq' : 0 ≤ Real.rpow q (-1-a) := (Real.rpow_pos_of_pos hq _).le
  have hp0 : 0 ≤ Real.rpow p (-a) := (Real.rpow_pos_of_pos hp _).le
  have hq0 : 0 ≤ Real.rpow q (-a) := (Real.rpow_pos_of_pos hq _).le
  have hep := power_times_slack p a hp
  have heq := power_times_slack q a hq
  rcases le_total 0 d with hd0 | hd0
  · rw [abs_of_nonneg hd0]
    have hmul := mul_le_mul_of_nonneg_left hd.2 (mul_nonneg ha hp')
    rw [mul_assoc a _ p, hep] at hmul
    nlinarith only [hmul, mul_nonneg ha hq0]
  · rw [abs_of_nonpos hd0]
    have hmul := mul_le_mul_of_nonneg_left hd.1 (mul_nonneg ha hq')
    rw [mul_neg, mul_assoc a _ q, heq] at hmul
    nlinarith only [hmul, mul_nonneg ha hp0]

/-- The barrier estimate in the proof of Lemma 4.7 (page 28), before the potential
budget is applied. The comparison flow has cost at most the target. -/
theorem gradient_dot_direction_le_of_cost_le (I : Instance) (a F : ℝ) (f fstar : Fin I.m → ℝ)
    (hf : StrictlyInside I f) (hs : I.IsFeasible fstar) (ha : 0 ≤ a)
    (hr : 0 < residual I F f) (hF : I.cost fstar ≤ F) :
    dot (gradient I a F f) (fun e => fstar e - f e) ≤
      -20 * I.m - a * weightedLength (lengths I a f) (fun e => fstar e - f e) +
        2*a*(potential I a F f - 20*I.m*Real.log (residual I F f)) := by
  have hcost : I.cost (fun e => fstar e - f e) ≤ -residual I F f := by
    simp only [Instance.cost, mul_sub, Finset.sum_sub_distrib, residual] at *
    linarith only [hF]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun e (_ : e ∈ Finset.univ) =>
    edge_direction_bound ((I.edge e).upper - f e) (f e - (I.edge e).lower) a
      (fstar e - f e) (sub_pos.mpr (hf e).2) (sub_pos.mpr (hf e).1) ha
      ⟨by linarith only [(hs.2 e).1], by linarith only [(hs.2 e).2]⟩
  have hdot : dot (gradient I a F f) (fun e => fstar e - f e) =
      20 * I.m * (residual I F f)⁻¹ * I.cost (fun e => fstar e - f e) +
      ∑ e, (a * Real.rpow ((I.edge e).upper - f e) (-1-a) -
        a * Real.rpow (f e - (I.edge e).lower) (-1-a)) * (fstar e - f e) := by
    simp only [dot, gradient, Instance.cost, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hdot]
  have hfactor : 0 ≤ 20*(I.m : ℝ)*(residual I F f)⁻¹ :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (inv_nonneg.mpr hr.le)
  have hcostbound := mul_le_mul_of_nonneg_left hcost hfactor
  have hc : 20 * (I.m : ℝ) * (residual I F f)⁻¹ * -residual I F f = -20 * I.m := by
    field_simp
  rw [hc] at hcostbound
  have hlen : weightedLength (lengths I a f) (fun e => fstar e - f e) =
      ∑ e, (Real.rpow ((I.edge e).upper - f e) (-1-a) +
        Real.rpow (f e - (I.edge e).lower) (-1-a)) * |fstar e - f e| := by
    apply Finset.sum_congr rfl
    intro e _
    rw [abs_mul, abs_of_pos (lengths_pos I a f hf e)]
    rfl
  rw [hlen]
  simp_rw [mul_assoc] at hsum
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hb : potential I a F f - 20*I.m*Real.log (residual I F f) =
      ∑ e, edgeBarrier I a e (f e) := by
    unfold potential
    ring
  rw [hb]
  simp only [edgeBarrier]
  rw [← Finset.mul_sum] at hsum
  simp only [← mul_assoc] at hsum
  linarith only [hsum, hcostbound]

/-- The barrier estimate in Lemma 4.7 (page 28) for a comparison flow
whose cost equals the target. -/
theorem gradient_dot_direction_le (I : Instance) (a F : ℝ) (f fstar : Fin I.m → ℝ)
    (hf : StrictlyInside I f) (hs : I.IsFeasible fstar) (ha : 0 ≤ a)
    (hr : 0 < residual I F f) (hF : I.cost fstar = F) :
    dot (gradient I a F f) (fun e => fstar e - f e) ≤
      -20 * I.m - a * weightedLength (lengths I a f) (fun e => fstar e - f e) +
        2*a*(potential I a F f - 20*I.m*Real.log (residual I F f)) :=
  gradient_dot_direction_le_of_cost_le I a F f fstar hf hs ha hr hF.le

/-- Lemma 4.7 (page 28) (quality of `f* - f`). The explicit budget
`2α(Φ-20m log residual) ≤ m` is the step supplied in the source by
`Φ ≤ 200m log(mU)`, `log residual ≥ -10 log(mU)`, and
`α = 1/(1000 log(mU))`. The bound `α ≤ 19/25` pays for `100m`
in the denominator. -/
theorem direction_of_cost_le_of_budget (I : Instance) (a F ε : ℝ) (f fstar gApprox lApprox : Fin I.m → ℝ)
    (hm : 0 < I.m) (hf : StrictlyInside I f) (hs : I.IsFeasible fstar)
    (ha : 0 ≤ a) (ha' : a ≤ 19/25) (hr : 0 < residual I F f)
    (hF : I.cost fstar ≤ F) (hε : ε ≤ a/2)
    (hg : GradientTolerance (lengths I a f) gApprox (gradient I a F f) ε)
    (hl : VectorApprox 2 lApprox (lengths I a f))
    (hbudget : 2*a*(potential I a F f - 20*I.m*Real.log (residual I F f)) ≤ I.m) :
    dot gApprox (fun e => fstar e - f e) /
      (100*I.m + weightedLength lApprox (fun e => fstar e - f e)) ≤ -a/4 := by
  have hmain := gradient_dot_direction_le_of_cost_le I a F f fstar hf hs ha hr hF
  have herr := abs_dot_error_le (lengths I a f) gApprox (gradient I a F f)
    (fun e => fstar e - f e) ε (lengths_pos I a f hf) hg
  have hlen := weightedLength_approx_le_two lApprox (lengths I a f)
    (fun e => fstar e - f e) hl
  have hn : 0 ≤ weightedLength (lengths I a f) (fun e => fstar e - f e) :=
    Finset.sum_nonneg fun e _ => abs_nonneg _
  have hn' : 0 ≤ weightedLength lApprox (fun e => fstar e - f e) :=
    Finset.sum_nonneg fun e _ => abs_nonneg _
  have hm' : (0 : ℝ) < I.m := Nat.cast_pos.mpr hm
  apply (div_le_iff₀ (by linarith only [hm', hn'] :
    0 < 100*(I.m : ℝ) + weightedLength lApprox (fun e => fstar e - f e))).mpr
  have heps := mul_le_mul_of_nonneg_right hε hn
  have hupper := (abs_le.mp herr).2
  have hpay := mul_le_mul_of_nonneg_right ha' hm'.le
  have hlen' := mul_le_mul_of_nonneg_left hlen ha
  nlinarith only [hmain, hupper, hbudget, heps, hpay, hlen']

/-- Lemma 4.7 (page 28) (quality of `f* - f`). The explicit budget
`2α(Φ-20m log residual) ≤ m` is the step supplied in the source by
`Φ ≤ 200m log(mU)`, `log residual ≥ -10 log(mU)`, and
`α = 1/(1000 log(mU))`. The bound `α ≤ 19/25` pays for `100m`
in the denominator. -/
theorem optimal_direction_of_budget (I : Instance) (a F ε : ℝ) (f fstar gApprox lApprox : Fin I.m → ℝ)
    (hm : 0 < I.m) (hf : StrictlyInside I f) (hs : I.IsMinCostFlow fstar)
    (ha : 0 ≤ a) (ha' : a ≤ 19/25) (hr : 0 < residual I F f)
    (hF : I.cost fstar = F) (hε : ε ≤ a/2)
    (hg : GradientTolerance (lengths I a f) gApprox (gradient I a F f) ε)
    (hl : VectorApprox 2 lApprox (lengths I a f))
    (hbudget : 2*a*(potential I a F f - 20*I.m*Real.log (residual I F f)) ≤ I.m) :
    dot gApprox (fun e => fstar e - f e) /
      (100*I.m + weightedLength lApprox (fun e => fstar e - f e)) ≤ -a/4 := by
  have hmain := gradient_dot_direction_le I a F f fstar hf hs.1 ha hr hF
  have herr := abs_dot_error_le (lengths I a f) gApprox (gradient I a F f)
    (fun e => fstar e - f e) ε (lengths_pos I a f hf) hg
  have hlen := weightedLength_approx_le_two lApprox (lengths I a f)
    (fun e => fstar e - f e) hl
  have hn : 0 ≤ weightedLength (lengths I a f) (fun e => fstar e - f e) :=
    Finset.sum_nonneg fun e _ => abs_nonneg _
  have hn' : 0 ≤ weightedLength lApprox (fun e => fstar e - f e) :=
    Finset.sum_nonneg fun e _ => abs_nonneg _
  have hm' : (0 : ℝ) < I.m := Nat.cast_pos.mpr hm
  apply (div_le_iff₀ (by linarith only [hm', hn'] :
    0 < 100*(I.m : ℝ) + weightedLength lApprox (fun e => fstar e - f e))).mpr
  have heps := mul_le_mul_of_nonneg_right hε hn
  have hupper := (abs_le.mp herr).2
  have hpay := mul_le_mul_of_nonneg_right ha' hm'.le
  have hlen' := mul_le_mul_of_nonneg_left hlen ha
  nlinarith only [hmain, hupper, hbudget, heps, hpay, hlen']

/-- Lemma 4.7 (page 28) with the source's exponent and potential hypotheses. The
length scaling in the error condition is `L(f)`, correcting `L(g)` in
the source. An error at most `α/2` suffices, including equality. -/
theorem lemma_4_7 (I : Instance) (U F ε : ℝ) (f fstar gApprox lApprox : Fin I.m → ℝ)
    (hm : 0 < I.m) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hf : StrictlyInside I f) (hs : I.IsMinCostFlow fstar)
    (hr : 0 < residual I F f) (hF : I.cost fstar = F)
    (hε : ε ≤ alpha I U / 2)
    (hg : GradientTolerance (lengths I (alpha I U) f) gApprox
      (gradient I (alpha I U) F f) ε)
    (hl : VectorApprox 2 lApprox (lengths I (alpha I U) f))
    (hpot : potential I (alpha I U) F f ≤ 200*I.m*Real.log (I.m*U))
    (hres : -10*Real.log (I.m*U) ≤ Real.log (residual I F f)) :
    dot gApprox (fun e => fstar e - f e) /
      (100*I.m + weightedLength lApprox (fun e => fstar e - f e)) ≤ -alpha I U/4 := by
  have ha := alpha_pos I U hsize
  have ha' := alpha_le I U hsize
  apply optimal_direction_of_budget I (alpha I U) F ε f fstar gApprox lApprox
    hm hf hs ha.le (by linarith only [ha']) hr hF hε hg hl
  have hm' : (0 : ℝ) ≤ I.m := Nat.cast_nonneg _
  have hlog := mul_le_mul_of_nonneg_left hres (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) hm')
  have hbar : potential I (alpha I U) F f - 20*I.m*Real.log (residual I F f) ≤
      400*I.m*Real.log (I.m*U) := by linarith only [hpot, hlog]
  calc
    2*alpha I U*(potential I (alpha I U) F f - 20*I.m*Real.log (residual I F f)) ≤
        2*alpha I U*(400*I.m*Real.log (I.m*U)) :=
      mul_le_mul_of_nonneg_left hbar (mul_nonneg (by norm_num) ha.le)
    _ = 800*I.m*(alpha I U*Real.log (I.m*U)) := by ring
    _ = (4/5 : ℝ)*I.m := by rw [alpha_mul_log I U hsize]; ring
    _ ≤ I.m := by linarith only [hm']

/-- The direction estimate of Lemma 4.7 (page 28) for an upper guess.
The comparison flow is feasible and has cost at most the target. The
length scaling in the error condition is `L(f)`, correcting `L(g)` in
the source. An error at most `α/2` suffices, including equality. -/
theorem direction_of_cost_le (I : Instance) (U F ε : ℝ) (f fstar gApprox lApprox : Fin I.m → ℝ)
    (hm : 0 < I.m) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hf : StrictlyInside I f) (hs : I.IsFeasible fstar)
    (hr : 0 < residual I F f) (hF : I.cost fstar ≤ F)
    (hε : ε ≤ alpha I U / 2)
    (hg : GradientTolerance (lengths I (alpha I U) f) gApprox
      (gradient I (alpha I U) F f) ε)
    (hl : VectorApprox 2 lApprox (lengths I (alpha I U) f))
    (hpot : potential I (alpha I U) F f ≤ 200*I.m*Real.log (I.m*U))
    (hres : -10*Real.log (I.m*U) ≤ Real.log (residual I F f)) :
    dot gApprox (fun e => fstar e - f e) /
      (100*I.m + weightedLength lApprox (fun e => fstar e - f e)) ≤ -alpha I U/4 := by
  have ha := alpha_pos I U hsize
  have ha' := alpha_le I U hsize
  apply direction_of_cost_le_of_budget I (alpha I U) F ε f fstar gApprox lApprox
    hm hf hs ha.le (by linarith only [ha']) hr hF hε hg hl
  have hm' : (0 : ℝ) ≤ I.m := Nat.cast_nonneg _
  have hlog := mul_le_mul_of_nonneg_left hres (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) hm')
  have hbar : potential I (alpha I U) F f - 20*I.m*Real.log (residual I F f) ≤
      400*I.m*Real.log (I.m*U) := by linarith only [hpot, hlog]
  calc
    2*alpha I U*(potential I (alpha I U) F f - 20*I.m*Real.log (residual I F f)) ≤
        2*alpha I U*(400*I.m*Real.log (I.m*U)) :=
      mul_le_mul_of_nonneg_left hbar (mul_nonneg (by norm_num) ha.le)
    _ = 800*I.m*(alpha I U*Real.log (I.m*U)) := by ring
    _ = (4/5 : ℝ)*I.m := by rw [alpha_mul_log I U hsize]; ring
    _ ≤ I.m := by linarith only [hm']

end MinCostFlow.IPM
