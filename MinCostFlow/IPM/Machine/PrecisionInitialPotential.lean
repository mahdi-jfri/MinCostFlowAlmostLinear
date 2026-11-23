module

public import MinCostFlow.IPM.Machine.PrecisionStepDecrease
import MinCostFlow.IPM.Parameters
import all MinCostFlow.IPM.InitialPotential
import Mathlib.Tactic.Linarith

/-!
# The initial potential with the stored exponent

The half-unit slacks in Lemma 4.12 (Chen et al., arXiv:2203.00671v2,
page 31) bound each power barrier by two for every exponent in `[0,1]`.
The initial target-search potential bound therefore holds unchanged at
`alphaPrime`. This uses the same cost-residual and barrier estimates
as the analytic initialization proof.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- The initial potential estimate for an explicitly supplied exponent
in `[0,1]`, uniformly over targets in the bounded cost interval. -/
theorem guess_initial_potential_at_exponent (I : Instance) (U a F : ℝ) (f : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (ha : 0 ≤ a) (haUpper : a ≤ 1)
    (hnums : NumbersBounded I U) (hf : I.IsFeasible f)
    (hslack : ∀ e, (1/2 : ℝ) ≤ f e-(I.edge e).lower ∧
      (1/2 : ℝ) ≤ (I.edge e).upper-f e)
    (hF : -(I.m*U^2) ≤ F) (hr : 0 < residual I F f) :
    potential I a F f ≤ 200*I.m*Real.log (I.m*U) := by
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hx : 0 < (I.m : ℝ)*U := lt_of_lt_of_le (by norm_num) hsize
  have hm1 : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
  have hUle : U ≤ I.m*U := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hm1 hU0
  have hprod := mul_le_mul_of_nonneg_left hUle hx.le
  have hprod2 := mul_le_mul_of_nonneg_right hsize (sq_nonneg ((I.m : ℝ)*U))
  have hcost := (abs_le.mp (feasible_cost_abs_le I U hU0 hnums f hf)).2
  have hres : residual I F f ≤ ((I.m : ℝ)*U)^3 := by
    dsimp only [residual]
    nlinarith only [hcost, hF, hprod, hprod2]
  have hlog := Real.log_le_log hr hres
  rw [Real.log_pow] at hlog
  have hbar : (∑ e, edgeBarrier I a e (f e)) ≤ 4*I.m := by
    calc
      _ ≤ ∑ _ : Fin I.m, (4 : ℝ) := by
        apply Finset.sum_le_sum
        intro e _
        have hl := power_barrier_le_two _ _ (hslack e).1 ha haUpper
        have hu := power_barrier_le_two _ _ (hslack e).2 ha haUpper
        simpa only [edgeBarrier, show (2 : ℝ)+2 = 4 by norm_num] using add_le_add hu hl
      _ = _ := by simp [mul_comm]
  have hlogsize := log_size_ge_half I U hsize
  have hmul := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) (Nat.cast_nonneg I.m))
  have hpay := mul_le_mul_of_nonneg_left hlogsize (Nat.cast_nonneg I.m)
  unfold potential
  norm_num only [Nat.cast_ofNat] at hmul
  nlinarith only [hmul, hbar, hpay]

/-- The machine's dyadic exponent satisfies the same initial budget.
The target's nonpositive residual is handled by the stopping guard. -/
theorem guess_initial_potential_alphaPrime (I : Instance) (U : ℕ) (F : ℝ)
    (f : Fin I.m → ℝ) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ I.m*U)
    (hnums : NumbersBounded I U) (hf : I.IsFeasible f)
    (hslack : ∀ e, (1/2:ℝ) ≤ f e-(I.edge e).lower ∧
      (1/2:ℝ) ≤ (I.edge e).upper-f e)
    (hF : -(I.m*(U:ℝ)^2) ≤ F) (hr : 0 < residual I F f) :
    potential I (Num.IPM.alphaPrime I.m U) F f ≤
      200*I.m*Real.log (I.m*(U:ℝ)) := by
  have hs : (2:ℝ) ≤ I.m*(U:ℝ) := by exact_mod_cast hsize
  have ha := Num.IPM.alphaPrime_bounds I U hsize
  have hlo : 0 ≤ Num.IPM.alphaPrime I.m U :=
    (div_nonneg (alpha_pos I U hs).le (by norm_num : (0:ℝ) ≤ 10)).trans ha.1
  have hhi : Num.IPM.alphaPrime I.m U ≤ 1 :=
    (ha.2.trans (alpha_le I U hs)).trans (by norm_num)
  exact guess_initial_potential_at_exponent I U _ F f hm (by exact_mod_cast hU)
    hs hlo hhi hnums hf hslack hF hr

end MinCostFlow.IPM.Machine
