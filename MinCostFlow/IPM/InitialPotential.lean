module

public import MinCostFlow.IPM.InitialConstruction
public import MinCostFlow.IPM.InitialSize
import MinCostFlow.IPM.InitialDomain
import MinCostFlow.IPM.InitialCost
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The initial potential bound

Appendix B.1 (page 92) of Chen et al., arXiv:2203.00671v2, bounds the initial
cost residual and the power barriers separately. Half-unit slacks make
each barrier at most two. Our explicit edge-count bound allows all
original endpoint vertices, yielding residual at most `18(mU)³`.
This still gives potential at most `200 M log(mU)`, with `M` the actual
augmented edge count. A zero residual is an optimal initial flow and
must be treated before entering the logarithm's analytic domain.
-/

public section
namespace MinCostFlow.IPM

/-- A half-unit slack contributes at most two to the barrier for exponents up to one. -/
theorem power_barrier_le_two (x a : ℝ) (hx : (1/2 : ℝ) ≤ x)
    (ha : 0 ≤ a) (ha' : a ≤ 1) : Real.rpow x (-a) ≤ 2 := by
  have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1/2) hx (neg_nonpos.mpr ha)
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha'
  rw [Real.rpow_one] at hpow
  simp only [Real.rpow_neg_eq_inv_rpow] at h
  norm_num only [one_div, inv_inv] at h
  simpa only [Real.rpow_eq_pow, Real.rpow_neg_eq_inv_rpow] using h.trans hpow

/-- The initial barrier sum is at most four per augmented edge. -/
theorem initial_barrier_le (I : Instance) (K : ℤ) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (∑ e, edgeBarrier (initialInstance I K) a e (initialFlow I K e)) ≤
      4*(initialInstance I K).m := by
  calc
    _ ≤ ∑ _ : Fin (initialInstance I K).m, (4 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      have hs := initialFlow_slacks I K e
      have hu := power_barrier_le_two _ a hs.2 ha ha'
      have hl := power_barrier_le_two _ a hs.1 ha ha'
      simpa only [edgeBarrier, show (2 : ℝ)+2 = 4 by norm_num] using add_le_add hu hl
    _ = _ := by simp [mul_comm]

private theorem log_residual_bound (x r : ℝ) (hx : 2 ≤ x) (hr : 0 < r)
    (hbound : r ≤ 18*x^3) : Real.log r ≤ 8*Real.log x := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have h18 : (18 : ℝ) ≤ x^5 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 5
    norm_num at hp
    exact le_trans (by norm_num : (18 : ℝ) ≤ 32) hp
  have hl18 := Real.log_le_log (by norm_num : (0 : ℝ) < 18) h18
  rw [Real.log_pow] at hl18
  have hlog := Real.log_le_log hr hbound
  rw [Real.log_mul (by norm_num : (18 : ℝ) ≠ 0) (pow_ne_zero 3 hxpos.ne'), Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hl18 hlog
  linarith only [hl18, hlog]

/-- The initial potential bound from Lemma 4.12 (page 31) and Appendix B.1 (page 92). The
coefficient `M` is the actual augmented edge count (at most `3m`), as
used by the potential definition. The target is the augmented optimum.
The proof uses only `0 ≤ a ≤ 1`, so it applies to the IPM exponent. -/
theorem initial_potential_le (I : Instance) (U a F : ℝ) (K : ℤ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hi : IsolatedDemandsZero I)
    (hK : 0 ≤ (K : ℝ)) (hK' : (K : ℝ) ≤ 4*I.m*U^2)
    (ha : 0 ≤ a) (ha' : a ≤ 1)
    (gstar : Fin (initialInstance I K).m → ℝ)
    (hgstar : (initialInstance I K).IsMinCostFlow gstar)
    (hF : (initialInstance I K).cost gstar = F)
    (hr : 0 < residual (initialInstance I K) F (initialFlow I K)) :
    potential (initialInstance I K) a F (initialFlow I K) ≤
      200*(initialInstance I K).m*Real.log (I.m*U) := by
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hup := initialFlow_cost_le I U K hm hU hnums hi hK hK'
  have hlo := initialInstance_cost_ge I U K hU0 hnums hK gstar hgstar.1
  rw [hF] at hlo
  have hm' : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
  have hscale : I.m*U^2 ≤ (I.m : ℝ)^3*U^3 := by
    have hmpow : (1 : ℝ) ≤ (I.m : ℝ)^2 := by nlinarith only [hm']
    have hfactor : 1 ≤ (I.m : ℝ)^2*U := by
      have h := mul_le_mul_of_nonneg_right hmpow hU0
      nlinarith only [h, hU]
    have h := mul_le_mul_of_nonneg_left hfactor (mul_nonneg (Nat.cast_nonneg I.m) (sq_nonneg U))
    nlinarith only [h]
  have hres : residual (initialInstance I K) F (initialFlow I K) ≤ 18*(I.m*U)^3 := by
    dsimp only [residual]
    nlinarith only [hup, hlo, hscale]
  have hlog := log_residual_bound (I.m*U) _ hsize hr hres
  have hbar := initial_barrier_le I K a ha ha'
  have hlogsize := log_size_ge_half I U hsize
  have hM : (0 : ℝ) ≤ (initialInstance I K).m := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hlog (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) hM)
  have hpay := mul_le_mul_of_nonneg_left hlogsize hM
  unfold potential
  nlinarith only [hmul, hbar, hpay]

end MinCostFlow.IPM
