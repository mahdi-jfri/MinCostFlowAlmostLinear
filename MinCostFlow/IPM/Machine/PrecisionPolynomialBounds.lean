module

public import MinCostFlow.IPM.Machine.PrecisionHiddenRange
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Hidden parameters on the polynomially bounded solver input

The augmented instance has a common integer bound at most `4m^81`
when the original capacities are at most `m^40`. Thus its dyadic barrier
exponent already gives a hidden parameter of order `1/log m` without
computing a real-valued gradient scaling. The selected binary ranges
also give an explicit squared-log bound for item 5 of hidden stability.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- The explicit hidden logarithmic bound grows at most quadratically
in the input logarithm. -/
theorem precisionHiddenPsi_le_log_square (m U : ℕ) (hsize : 2 ≤ m*U) :
    precisionHiddenPsi m U ≤ 28000000*(Real.log ((m*U:ℕ):ℝ))^2 := by
  have hbits := (Num.IPM.alpha_bit_length_bounds hsize).2
  have hm : 0 < m := Nat.pos_of_ne_zero (by intro he; simp [he] at hsize)
  have hb : (1:ℝ) ≤ ((m.size+U.size:ℕ):ℝ) := by
    exact_mod_cast (show 1 ≤ m.size+U.size by have hh := Nat.size_pos.mpr hm; omega)
  have hlog : 0 ≤ Real.log ((m*U:ℕ):ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m*U by omega))
  have hsq := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ((m.size+U.size:ℕ):ℝ)) hbits 2
  have hsmall : ((m.size+U.size:ℕ):ℝ) ≤ ((m.size+U.size:ℕ):ℝ)^2 := by nlinarith only [hb]
  have hone : (1:ℝ) ≤ ((m.size+U.size:ℕ):ℝ)^2 := by nlinarith only [hb]
  have heq : precisionHiddenPsi m U =
      1100000*((m.size+U.size:ℕ):ℝ)^2+2*((m.size+U.size:ℕ):ℝ)+116 := by
    simp only [precisionHiddenPsi,ipmRangeExponent,slackRangeExponent,gradientCoefficientExponent,
      Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
  rw [heq]
  nlinarith only [hsq,hsmall,hone,sq_nonneg (Real.log ((m*U:ℕ):ℝ))]

/-- The common augmented integer bound `4m^81` gives an explicit bound
on the logarithm driving the precision choices. -/
theorem polynomial_input_log_bound (m U : ℕ) (hm : 0 < m) (hU : 0 < U)
    (hpoly : U ≤ 4*m^81) :
    Real.log ((m*U:ℕ):ℝ) ≤ 84*Real.log ((m:ℝ)+2) := by
  have hm0 : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hx : (0:ℝ) < ((m*U:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos hm hU
  have hpoly' : ((m*U:ℕ):ℝ) ≤ 4*(m:ℝ)^82 := by
    have hh := Nat.mul_le_mul_left m hpoly
    have he : m*(4*m^81)=4*m^82 := by rw [pow_succ]; ring
    rw [he] at hh
    exact_mod_cast hh
  have hlog := Real.log_le_log hx hpoly'
  rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (pow_pos hm0 82).ne',Real.log_pow] at hlog
  have hmlog := Real.log_le_log hm0 (by linarith only [hm0] : (m:ℝ) ≤ m+2)
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hfour : (4:ℝ) ≤ ((m:ℝ)+2)^2 := by nlinarith only [hm1]
  have hlog4 := Real.log_le_log (by norm_num : (0:ℝ)<4) hfour
  rw [Real.log_pow] at hlog4
  norm_num only [Nat.cast_ofNat] at hlog hlog4
  linarith only [hlog,hmlog,hlog4]

/-- Item 5's hidden parameter is explicitly `O(log²(m+2))` on the
polynomially bounded solver instance. -/
theorem precisionHiddenPsi_polynomial_input (m U : ℕ) (hm : 0 < m)
    (hU : 0 < U) (hsize : 2 ≤ m*U) (hpoly : U ≤ 4*m^81) :
    precisionHiddenPsi m U ≤ 200000000000*(Real.log ((m:ℝ)+2))^2 := by
  have hpsi := precisionHiddenPsi_le_log_square m U hsize
  have hlog := polynomial_input_log_bound m U hm hU hpoly
  have hx : 0 ≤ Real.log ((m*U:ℕ):ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m*U by omega))
  have hsquare := pow_le_pow_left₀ hx hlog 2
  nlinarith only [hpsi,hsquare,sq_nonneg (Real.log ((m:ℝ)+2))]

/-- Explicit `1/Theta(log(m+2))` bounds for the dyadic hidden parameter
on the polynomially bounded augmented instance. -/
theorem dyadic_hidden_parameter_bounds (I : Instance) (U : ℕ) (hm : 0 < I.m)
    (hU : 4 ≤ U) (hpoly : U ≤ 4*I.m^81) :
    1/(6720000*Real.log ((I.m:ℝ)+2)) ≤ Num.IPM.alphaPrime I.m U/8 ∧
      Num.IPM.alphaPrime I.m U/8 ≤ 1/(8000*Real.log ((I.m:ℝ)+2)) := by
  have hm1 : 1 ≤ I.m := hm
  have hmul := Nat.mul_le_mul_left I.m hU
  have hmm : (0:ℝ) ≤ I.m := Nat.cast_nonneg _
  have hsize : 2 ≤ I.m*U := by omega
  have hlog := polynomial_input_log_bound I.m U hm (by omega) hpoly
  have hpad : 0 < Real.log ((I.m:ℝ)+2) := Real.log_pos (by linarith only [hmm])
  have hx : 0 < Real.log ((I.m*U:ℕ):ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < I.m*U by omega))
  have hlower : Real.log ((I.m:ℝ)+2) ≤ Real.log ((I.m*U:ℕ):ℝ) := by
    apply Real.log_le_log (by linarith only [hmm])
    exact_mod_cast (show I.m+2 ≤ I.m*U by omega)
  have ha := Num.IPM.alphaPrime_bounds I U hsize
  have heqlo : (alpha I U/10)/8=1/(80000*Real.log ((I.m*U:ℕ):ℝ)) := by
    unfold alpha
    rw [Nat.cast_mul]
    ring
  have heqhi : alpha I U/8=1/(8000*Real.log ((I.m*U:ℕ):ℝ)) := by
    unfold alpha
    rw [Nat.cast_mul]
    ring
  constructor
  · have hd : 80000*Real.log ((I.m*U:ℕ):ℝ) ≤ 6720000*Real.log ((I.m:ℝ)+2) := by linarith only [hlog]
    have hh := one_div_le_one_div_of_le (mul_pos (by norm_num) hx) hd
    exact hh.trans (heqlo ▸ div_le_div_of_nonneg_right ha.1 (by norm_num : (0:ℝ) ≤ 8))
  · have hh := div_le_div_of_nonneg_right ha.2 (by norm_num : (0:ℝ) ≤ 8)
    rw [heqhi] at hh
    exact hh.trans (one_div_le_one_div_of_le (mul_pos (by norm_num) hpad)
      (mul_le_mul_of_nonneg_left hlower (by norm_num)))

end MinCostFlow.IPM.Machine
