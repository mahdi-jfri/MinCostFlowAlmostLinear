module

public import MinCostFlow.IPM.HiddenWitness
import MinCostFlow.IPM.GuessBounds
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Explicit length and width bounds for hidden stability

Chen et al., arXiv:2203.00671v2, Lemma 9.2 (pages 70--71), bounds
slacks from the potential budget before the residual stopping threshold.
The barrier sum is at most `400m log(mU)`. Taking logarithms bounds each
inverse slack power, then each length and width. These are the bounds
for item 5 of Definition 4.4 (page 14 of arXiv:2309.16629v1).
-/

noncomputable section
public section
namespace MinCostFlow.IPM

/-- The explicit barrier budget before the IPM stopping threshold. -/
@[expose] def ipmBarrierBound (I : Instance) (U : ℝ) : ℝ := 400*I.m*Real.log (I.m*U)

/-- The logarithmic upper bound on an individual length summand. -/
@[expose] def ipmLogScale (I : Instance) (U : ℝ) : ℝ :=
  (1+alpha I U)/alpha I U*Real.log (ipmBarrierBound I U)

/-- The explicit `Ψ` used for item 5 of hidden stability. With the source
choice `α = 1/(1000 log(mU))`, this has order `log²(mU)`. -/
@[expose] def ipmPsi (I : Instance) (U : ℝ) : ℝ :=
  Real.log 100+2*Real.log (2*U)+ipmLogScale I U

/-- The barrier budget is at least one in the nondegenerate IPM range. -/
theorem ipmBarrierBound_ge_one (I : Instance) (U : ℝ) (hm : 0 < I.m)
    (hsize : 2 ≤ (I.m : ℝ)*U) : (1 : ℝ) ≤ ipmBarrierBound I U := by
  have hlog := log_size_ge_half I U hsize
  have hmR : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
  have hh := mul_le_mul hmR hlog (by norm_num : (0 : ℝ) ≤ 1/2) (Nat.cast_nonneg I.m)
  unfold ipmBarrierBound
  nlinarith only [hh]

/-- The logarithmic length bound is nonnegative. -/
theorem ipmLogScale_nonneg (I : Instance) (U : ℝ) (hm : 0 < I.m)
    (hsize : 2 ≤ (I.m : ℝ)*U) : 0 ≤ ipmLogScale I U := by
  have ha := alpha_pos I U hsize
  exact mul_nonneg (div_nonneg (by linarith only [ha]) ha.le)
    (Real.log_nonneg (ipmBarrierBound_ge_one I U hm hsize))

private theorem power_length_summand_le (p a B : ℝ) (hp : 0 < p) (ha : 0 < a)
    (_hB : 0 < B) (hpower : Real.rpow p (-a) ≤ B) :
    Real.rpow p (-1-a) ≤ Real.exp ((1+a)/a*Real.log B) := by
  have hh := Real.log_le_log (Real.rpow_pos_of_pos hp (-a)) hpower
  rw [Real.log_rpow hp] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (by linarith only [ha] : 0 ≤ 1+a)
  have hid : a*((1+a)/a*Real.log B) = (1+a)*Real.log B := by field_simp
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_def_of_pos hp]
  apply Real.exp_le_exp.mpr
  apply (mul_le_mul_iff_right₀ ha).mp
  nlinarith only [hmul, hid]

/-- Every true IPM length is at most twice the exponential of the explicit
logarithmic scale. Unlike the source's displayed slack estimate, this
uses the barrier sum, not the possibly negative full potential. -/
theorem ipm_lengths_upper (I : Instance) (U F : ℝ) (f : Fin I.m → ℝ)
    (hm : 0 < I.m) (hsize : 2 ≤ (I.m : ℝ)*U) (hf : StrictlyInside I f)
    (hpot : potential I (alpha I U) F f ≤ 200*I.m*Real.log (I.m*U))
    (hreslog : -10*Real.log (I.m*U) ≤ Real.log (residual I F f)) (e : Fin I.m) :
    lengths I (alpha I U) f e ≤ 2*Real.exp (ipmLogScale I U) := by
  have ha := alpha_pos I U hsize
  have hB : 0 < ipmBarrierBound I U := lt_of_lt_of_le (by norm_num) (ipmBarrierBound_ge_one I U hm hsize)
  have hlog := mul_le_mul_of_nonneg_left hreslog
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) (Nat.cast_nonneg I.m))
  have hsum : (∑ e, edgeBarrier I (alpha I U) e (f e)) ≤ ipmBarrierBound I U := by
    unfold potential at hpot
    unfold ipmBarrierBound
    linarith only [hpot, hlog]
  have hedge : edgeBarrier I (alpha I U) e (f e) ≤ ipmBarrierBound I U :=
    (Finset.single_le_sum (fun j _ => add_nonneg
      (Real.rpow_nonneg (sub_pos.mpr (hf j).2).le _)
      (Real.rpow_nonneg (sub_pos.mpr (hf j).1).le _)) (Finset.mem_univ e)).trans hsum
  have hp : 0 ≤ Real.rpow ((I.edge e).upper-f e) (-alpha I U) :=
    (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).2) _).le
  have hq : 0 ≤ Real.rpow (f e-(I.edge e).lower) (-alpha I U) :=
    (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).1) _).le
  have hup := power_length_summand_le _ _ _ (sub_pos.mpr (hf e).2) ha hB
    (by unfold edgeBarrier at hedge; linarith only [hedge, hq])
  have hlo := power_length_summand_le _ _ _ (sub_pos.mpr (hf e).1) ha hB
    (by unfold edgeBarrier at hedge; linarith only [hedge, hp])
  simpa only [lengths, ipmLogScale, two_mul] using add_le_add hup hlo

/-- A true length is bounded below by `(2U)^(-2)` when `U ≥ 1`. -/
theorem ipm_lengths_lower (I : Instance) (U : ℝ) (f : Fin I.m → ℝ)
    (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U) (hnums : NumbersBounded I U)
    (hf : StrictlyInside I f) (e : Fin I.m) :
    Real.rpow (2*U) (-2) ≤ lengths I (alpha I U) f e := by
  have ha := alpha_pos I U hsize
  have ha' : alpha I U ≤ 1 := (alpha_le I U hsize).trans (by norm_num)
  have hp : ((I.edge e).upper : ℝ)-f e ≤ 2*U := by
    have hl := (abs_le.mp (hnums.2 e).1).1
    have hu := (abs_le.mp (hnums.2 e).2.1).2
    linarith only [hl, hu, (hf e).1]
  have h1 := Real.rpow_le_rpow_of_exponent_le (by linarith only [hU] : 1 ≤ 2*U)
    (by linarith only [ha'] : (-2 : ℝ) ≤ -1-alpha I U)
  have h2 := Real.rpow_le_rpow_of_nonpos (sub_pos.mpr (hf e).2) hp
    (by linarith only [ha] : -1-alpha I U ≤ 0)
  have h3 : 0 ≤ Real.rpow (f e-(I.edge e).lower) (-1-alpha I U) :=
    (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).1) _).le
  exact (h1.trans h2).trans (le_add_of_nonneg_right h3)

private theorem log_window (U Q ℓ w : ℝ) (hU : 1 ≤ U) (hQ : 0 ≤ Q)
    (hℓlo : (1/2 : ℝ)*Real.rpow (2*U) (-2) ≤ ℓ) (hℓhi : ℓ ≤ 4*Real.exp Q)
    (hwlo : (50 : ℝ) ≤ w) (hwhi : w ≤ 100*U*Real.exp Q) :
    0 < w ∧ |Real.log w| ≤ Real.log 100+2*Real.log (2*U)+Q ∧
      0 < ℓ ∧ |Real.log ℓ| ≤ Real.log 100+2*Real.log (2*U)+Q := by
  have hU0 : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have h2U : 0 < 2*U := mul_pos (by norm_num) hU0
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos h2U (-2 : ℝ))) hℓlo
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hwlo
  have hlog2U : 0 ≤ Real.log (2*U) := Real.log_nonneg (by linarith only [hU])
  have hlog100 : Real.log 2 ≤ Real.log 100 := Real.log_le_log (by norm_num) (by norm_num)
  have hlog4 : Real.log 4 ≤ Real.log 100 := Real.log_le_log (by norm_num) (by norm_num)
  have hlogU : Real.log U ≤ Real.log (2*U) := Real.log_le_log hU0 (by linarith only [hU])
  have hwloglo : 0 ≤ Real.log w := Real.log_nonneg (by linarith only [hwlo])
  have hwloghi := Real.log_le_log hw0 hwhi
  rw [Real.log_mul (mul_ne_zero (by norm_num) hU0.ne') (Real.exp_ne_zero Q),
    Real.log_mul (by norm_num : (100 : ℝ) ≠ 0) hU0.ne', Real.log_exp] at hwloghi
  have hℓloghi := Real.log_le_log hℓ0 hℓhi
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (Real.exp_ne_zero Q), Real.log_exp] at hℓloghi
  have hlowerpos : 0 < (1/2 : ℝ)*Real.rpow (2*U) (-2) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos h2U _)
  have hℓloglo := Real.log_le_log hlowerpos hℓlo
  simp only [Real.rpow_eq_pow] at hℓloglo
  rw [Real.log_mul (by norm_num : (1/2 : ℝ) ≠ 0)
    (Real.rpow_pos_of_pos h2U (-2 : ℝ)).ne', Real.log_rpow h2U] at hℓloglo
  have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), Real.log_one, zero_sub]
  rw [hhalf] at hℓloglo
  refine ⟨hw0, abs_le.mpr ⟨?_, ?_⟩, hℓ0, abs_le.mpr ⟨?_, ?_⟩⟩
  all_goals linarith only [hwloglo, hwloghi, hℓloglo, hℓloghi, hlog2U, hlog100, hlog4, hlogU, hQ,
    Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 100)]

/-- Explicit item-5 bounds for the IPM's stored length and hidden width.
The parameter is `ipmPsi I U`; its formula includes all constants. -/
theorem hiddenWidth_log_bounds (I : Instance) (U F : ℝ) (fstar f ℓ : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f) (hroute : I.Routes f)
    (hs : I.IsFeasible fstar) (hl : VectorApprox 2 ℓ (lengths I (alpha I U) f))
    (hpot : potential I (alpha I U) F f ≤ 200*I.m*Real.log (I.m*U))
    (hreslog : -10*Real.log (I.m*U) ≤ Real.log (residual I F f)) (e : Fin I.m) :
    0 < hiddenWidth fstar f ℓ e ∧ |Real.log (hiddenWidth fstar f ℓ e)| ≤ ipmPsi I U ∧
      0 < ℓ e ∧ |Real.log (ℓ e)| ≤ ipmPsi I U := by
  have hupper := ipm_lengths_upper I U F f hm hsize hf hpot hreslog e
  have hlower := ipm_lengths_lower I U f hU hsize hnums hf e
  have hℓhi : ℓ e ≤ 4*Real.exp (ipmLogScale I U) := by
    linarith only [(hl e).2.2.2, hupper]
  have hℓlo : (1/2 : ℝ)*Real.rpow (2*U) (-2) ≤ ℓ e := by
    have hh := (hl e).2.2.1
    norm_num at hh
    linarith only [hh, hlower]
  have hdelta : |fstar e-f e| ≤ 2*U := by
    have h1 := feasible_abs_le I U hnums fstar hs e
    have h2 := feasible_abs_le I U hnums f (feasible_of_inside I f hroute hf) e
    have htri := abs_sub_le (fstar e) 0 (f e)
    simp only [sub_zero, zero_sub, abs_neg] at htri
    linarith only [h1, h2, htri]
  have hQ := ipmLogScale_nonneg I U hm hsize
  have hexp : 1 ≤ Real.exp (ipmLogScale I U) := Real.one_le_exp_iff.mpr hQ
  have hUE : 1 ≤ U*Real.exp (ipmLogScale I U) := by
    have hh := mul_le_mul hU hexp (by norm_num : (0 : ℝ) ≤ 1)
      (le_trans (by norm_num) hU)
    simpa only [one_mul] using hh
  have hwupper : hiddenWidth fstar f ℓ e ≤ 100*U*Real.exp (ipmLogScale I U) := by
    have hprod := mul_le_mul hℓhi hdelta (abs_nonneg (fstar e-f e))
      (by positivity : 0 ≤ 4*Real.exp (ipmLogScale I U))
    rw [← abs_of_pos (hl e).1, ← abs_mul] at hprod
    unfold hiddenWidth
    nlinarith only [hprod, hUE]
  exact log_window U (ipmLogScale I U) (ℓ e) (hiddenWidth fstar f ℓ e) hU hQ hℓlo hℓhi
    (hiddenWidth_ge fstar f ℓ e) hwupper

end MinCostFlow.IPM
