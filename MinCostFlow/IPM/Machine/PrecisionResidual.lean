module

public import MinCostFlow.IPM.Machine.PrecisionDyadic
public import MinCostFlow.IPM.GuessBounds
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Residual ranges before the stopping guard

The target search stays in the integer interval bounded in Section 4 of
Chen et al., arXiv:2203.00671v2 (page 24). Before the one-quarter stopping
guard, this bounds the residual above and below in the same binary range
as the slacks. It also supplies the logarithmic premise used to extract
the barrier budget from the potential.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- The slack range exponent also covers twice the cost-search radius. -/
theorem twice_search_radius_le_dyadic (m U : ℕ) (hm : 0 < m) (hU : 0 < U) :
    2*(m:ℝ)*(U:ℝ)^2 ≤ (2:ℝ)^(slackRangeExponent m U) := by
  have hb : 0 < m.size := Nat.size_pos.mpr hm
  have hu : 0 < U.size := Nat.size_pos.mpr hU
  have hsquare : m.size+U.size ≤ (m.size+U.size)^2 := by
    have hn : 1 ≤ m.size+U.size := by omega
    nlinarith only [hn]
  have hs : m.size+2*U.size+1 ≤ slackRangeExponent m U := by
    unfold slackRangeExponent
    omega
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hs
  have hm' := Nat.lt_size_self m
  have hu' := Nat.lt_size_self U
  have hprod := Nat.mul_le_mul (Nat.le_of_lt hm')
    (Nat.pow_le_pow_left (Nat.le_of_lt hu') 2)
  have hbound : 2*m*U^2 ≤ (2:ℕ)^(slackRangeExponent m U) := by
    calc
      2*m*U^2 = 2*(m*U^2) := by ring
      _ ≤ 2*((2^m.size)*(2^U.size)^2) := Nat.mul_le_mul_left 2 hprod
      _ = (2^m.size * 2^(U.size*2))*2 := by rw [pow_mul]; ring
      _ = 2^(m.size+U.size*2+1) := by rw [pow_add,pow_add]; simp only [pow_one]
      _ = 2^(m.size+2*U.size+1) := by rw [Nat.mul_comm U.size 2]
      _ ≤ _ := hpow
  exact_mod_cast hbound

/-- The threshold `1/4` exceeds the lower dyadic endpoint. -/
theorem dyadic_le_quarter (m U : ℕ) (hm : 0 < m) (hU : 0 < U) :
    1/(2:ℝ)^(slackRangeExponent m U) ≤ 1/4 := by
  have hb : 0 < m.size := Nat.size_pos.mpr hm
  have hu : 0 < U.size := Nat.size_pos.mpr hU
  have he : 2 ≤ slackRangeExponent m U := by
    unfold slackRangeExponent
    have hs : 1 ≤ (m.size+U.size)^2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    omega
  have hh : (4:ℝ) ≤ (2:ℝ)^(slackRangeExponent m U) := by
    convert (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) he) using 1; norm_num
  exact one_div_le_one_div_of_le (by norm_num) hh

/-- A nonterminal residual satisfies both numerical range premises. -/
theorem residual_dyadic_range (I : Instance) (U : ℕ) (F : ℝ)
    (f : Fin I.m → ℝ) (hm : 0 < I.m) (hU : 0 < U)
    (hnums : NumbersBounded I U) (hf : I.IsFeasible f)
    (hF : -((I.m:ℝ)*(U:ℝ)^2) ≤ F) (hr : 1/4 < residual I F f) :
    1/(2:ℝ)^(slackRangeExponent I.m U) ≤ residual I F f ∧
      residual I F f ≤ (2:ℝ)^(slackRangeExponent I.m U) := by
  have hc := (abs_le.mp (feasible_cost_abs_le I U (Nat.cast_nonneg _) hnums f hf)).2
  refine ⟨(dyadic_le_quarter I.m U hm hU).trans hr.le, ?_⟩
  apply le_trans (b := 2*(I.m:ℝ)*(U:ℝ)^2)
  · unfold residual
    linarith only [hc,hF]
  · exact twice_search_radius_le_dyadic I.m U hm hU

/-- The nonterminal guard supplies the log-residual premise in the
potential-to-barrier argument. -/
theorem residual_log_lower_of_nonterminal (I : Instance) (U F : ℝ)
    (f : Fin I.m → ℝ) (hsize : 2 ≤ (I.m:ℝ)*U)
    (hr : 1/4 < residual I F f) :
    -10*Real.log (I.m*U) ≤ Real.log (residual I F f) := by
  have hl := log_size_ge_half I U hsize
  have hquarter := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<1/4)
  have hmono := Real.log_le_log (by norm_num : (0:ℝ)<1/4) hr.le
  norm_num at hquarter
  linarith only [hl,hquarter,hmono]

end MinCostFlow.IPM.Machine
