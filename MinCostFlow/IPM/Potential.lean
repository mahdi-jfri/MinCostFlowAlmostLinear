module

public import MinCostFlow.IPM.Definitions
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Small potential implies small residual cost

Lemma 4.1 (page 24) of Chen et al., arXiv:2203.00671v2, follows by dropping the
nonnegative barrier and exponentiating. The target need not be optimal:
the proof works for every target below the current cost.
-/

public section

namespace MinCostFlow.IPM

/-- The barrier terms in the potential are nonnegative in their domain. -/
theorem barrier_nonneg (I : Instance) (a : ℝ) (f : Fin I.m → ℝ)
    (hf : StrictlyInside I f) : 0 ≤ ∑ e, edgeBarrier I a e (f e) := by
  apply Finset.sum_nonneg
  intro e _
  exact add_nonneg (Real.rpow_nonneg (sub_pos.mpr (hf e).2).le _)
    (Real.rpow_nonneg (sub_pos.mpr (hf e).1).le _)

/-- Lemma 4.1 (page 24) of Chen et al., Section 4: the residual is at most
`exp(Φ/(20m))`. This also holds with a guess `F` in place of `F*`. -/
theorem lemma_4_1 (I : Instance) (a F : ℝ) (f : Fin I.m → ℝ)
    (hm : 0 < I.m) (hf : StrictlyInside I f) (hr : 0 < residual I F f) :
    residual I F f ≤ Real.exp (potential I a F f / (20 * I.m)) := by
  have hm' : (0 : ℝ) < 20 * I.m := mul_pos (by norm_num) (Nat.cast_pos.mpr hm)
  have hlog : 20 * I.m * Real.log (residual I F f) ≤ potential I a F f := by
    exact le_add_of_nonneg_right (barrier_nonneg I a f hf)
  have hdiv : Real.log (residual I F f) ≤ potential I a F f / (20 * I.m) :=
    (le_div_iff₀ hm').mpr (by simpa only [mul_comm] using hlog)
  simpa only [Real.exp_log hr] using Real.exp_le_exp.mpr hdiv

/-- The final bound in Lemma 4.1 (page 24): potential at most `-200m log(mU)`
implies residual at most `(mU)⁻¹⁰`. -/
theorem lemma_4_1_small (I : Instance) (a F U : ℝ) (f : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 < U) (hf : StrictlyInside I f)
    (hr : 0 < residual I F f)
    (hpot : potential I a F f ≤ -200 * I.m * Real.log (I.m * U)) :
    residual I F f ≤ Real.rpow (I.m * U) (-10) := by
  have hm' : (0 : ℝ) < 20 * I.m := mul_pos (by norm_num) (Nat.cast_pos.mpr hm)
  have hx : (0 : ℝ) < I.m * U := mul_pos (Nat.cast_pos.mpr hm) hU
  apply (lemma_4_1 I a F f hm hf hr).trans
  change _ ≤ (I.m * U) ^ (-10 : ℝ)
  rw [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ hm').mpr
  calc
    potential I a F f ≤ -200 * I.m * Real.log (I.m * U) := hpot
    _ = Real.log (I.m * U) * -10 * (20 * I.m) := by ring

end MinCostFlow.IPM
