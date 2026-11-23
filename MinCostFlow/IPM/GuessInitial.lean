module

public import MinCostFlow.IPM.GuessBounds
public import MinCostFlow.IPM.InitialConstruction
public import MinCostFlow.IPM.InitialSize
import MinCostFlow.IPM.IntegralOptimum
import MinCostFlow.IPM.InitialDomain
import MinCostFlow.IPM.InitialNumbers
import MinCostFlow.IPM.Parameters
import all MinCostFlow.IPM.InitialPotential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Initial potential for all guesses in the bounded interval

The cost search proposed in Section 4 of Chen et al., arXiv:2203.00671v2
(page 24), must start an IPM run for each tested target, not just for the
true optimum. The midpoint construction of Lemma 4.12 (page 31) has
half-unit slacks. These bound its barrier sum by four per edge. A target
at least `-mU²` bounds its positive initial residual by `2mU²`, giving
the same initial potential budget for every guess in the search interval.
-/

public section
namespace MinCostFlow.IPM

/-- A feasible half-unit-slack initial flow meets the IPM potential budget
for every target in the bounded cost interval with positive residual. -/
theorem guess_initial_potential (I : Instance) (U F : ℝ) (f : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hf : I.IsFeasible f)
    (hslack : ∀ e, (1/2 : ℝ) ≤ f e-(I.edge e).lower ∧
      (1/2 : ℝ) ≤ (I.edge e).upper-f e)
    (hF : -(I.m*U^2) ≤ F) (hr : 0 < residual I F f) :
    potential I (alpha I U) F f ≤ 200*I.m*Real.log (I.m*U) := by
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
  have ha := alpha_pos I U hsize
  have ha' : alpha I U ≤ 1 := (alpha_le I U hsize).trans (by norm_num)
  have hbar : (∑ e, edgeBarrier I (alpha I U) e (f e)) ≤ 4*I.m := by
    calc
      _ ≤ ∑ _ : Fin I.m, (4 : ℝ) := by
        apply Finset.sum_le_sum
        intro e _
        have hl := power_barrier_le_two _ _ (hslack e).1 ha.le ha'
        have hu := power_barrier_le_two _ _ (hslack e).2 ha.le ha'
        simpa only [edgeBarrier, show (2 : ℝ)+2 = 4 by norm_num] using add_le_add hu hl
      _ = _ := by simp [mul_comm]
  have hlogsize := log_size_ge_half I U hsize
  have hmul := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) (Nat.cast_nonneg I.m))
  have hpay := mul_le_mul_of_nonneg_left hlogsize (Nat.cast_nonneg I.m)
  unfold potential
  norm_num only [Nat.cast_ofNat] at hmul
  nlinarith only [hmul, hbar, hpay]

/-- The numeric bounds of Lemma 4.12 imply one common bound `4mU²`
for all entries of its augmented instance, including demands. -/
theorem augmented_numbersBounded (I : Instance) (U : ℝ) (K : ℤ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hnums : NumbersBounded I U)
    (hK : |(K : ℝ)| ≤ 4*I.m*U^2) :
    NumbersBounded (initialInstance I K) (4*I.m*U^2) := by
  have h := initialInstance_numbers I U K hm hU hnums hK
  refine ⟨fun v => (h.1 v).trans ?_, h.2⟩
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hpow : U ≤ U^2 := by nlinarith only [hU]
  have hp := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg I.m))
  have hn : 0 ≤ (I.m : ℝ)*U^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg U)
  linarith only [hp, hn]

/-- On the augmented instance of Lemma 4.12 (page 31), the optimal value
is an integer in `[-M V², M V²]`, with its actual edge count `M` and
`V = 4mU²`. The initial feasible flow supplies nonemptiness. -/
theorem augmented_integer_optimum (I : Instance) (U : ℝ) (K : ℤ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hnums : NumbersBounded I U)
    (hK : |(K : ℝ)| ≤ 4*I.m*U^2)
    (hvalid : (initialInstance I K).IsValid)
    (hfeas : (initialInstance I K).IsFeasible (initialFlow I K)) :
    ∃ f z, (initialInstance I K).IsMinCostFlow f ∧
      (initialInstance I K).cost f = (z : ℤ) ∧
      |(z : ℝ)| ≤ (initialInstance I K).m*(4*I.m*U^2)^2 := by
  obtain ⟨f, hf, hint⟩ := exists_integral_minCostFlow (initialInstance I K) hvalid ⟨_, hfeas⟩
  obtain ⟨z, hz⟩ := integral_cost (initialInstance I K) f hint
  refine ⟨f, z, hf, hz, ?_⟩
  rw [← hz]
  exact feasible_cost_abs_le (initialInstance I K) (4*I.m*U^2)
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg U))
    (augmented_numbersBounded I U K hm hU hnums hK) f hf.1

/-- Every admissible target for the augmented instance has the required
initial potential bound. This discharges the test's initial-budget
hypothesis separately for each guess. -/
theorem augmented_guess_initial_potential (I : Instance) (U F : ℝ) (K : ℤ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hnums : NumbersBounded I U)
    (hK : |(K : ℝ)| ≤ 4*I.m*U^2) (hM : 0 < (initialInstance I K).m)
    (hfeas : (initialInstance I K).IsFeasible (initialFlow I K))
    (hF : -((initialInstance I K).m*(4*I.m*U^2)^2) ≤ F)
    (hr : 0 < residual (initialInstance I K) F (initialFlow I K)) :
    potential (initialInstance I K) (alpha (initialInstance I K) (4*I.m*U^2)) F
      (initialFlow I K) ≤
      200*(initialInstance I K).m*Real.log ((initialInstance I K).m*(4*I.m*U^2)) := by
  have hm1 : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
  have hM1 : (1 : ℝ) ≤ (initialInstance I K).m := Nat.one_le_cast.mpr hM
  have hpow : (1 : ℝ) ≤ U^2 := by nlinarith only [hU]
  have hp := mul_le_mul hm1 hpow (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg I.m)
  have hV : (4 : ℝ) ≤ 4*I.m*U^2 := by nlinarith only [hp]
  have hsize : (2 : ℝ) ≤ (initialInstance I K).m*(4*I.m*U^2) := by
    have hh := mul_le_mul_of_nonneg_right hM1 (le_trans (by norm_num) hV)
    nlinarith only [hh, hV]
  exact guess_initial_potential (initialInstance I K) (4*I.m*U^2) F (initialFlow I K)
    hM (le_trans (by norm_num) hV) hsize (augmented_numbersBounded I U K hm hU hnums hK)
    hfeas (initialFlow_slacks I K) hF hr

end MinCostFlow.IPM
