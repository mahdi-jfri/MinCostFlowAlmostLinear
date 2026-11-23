module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Logarithm series on a normalized input

For `1 ≤ x ≤ 2`, the change of variable `t=(x-1)/(x+1)` gives
`0 ≤ t ≤ 1/3`. The odd-power series for the logarithm then has a geometric
tail. These bounds concern exact real arithmetic. A machine implementation must
also bound the errors from computing the change of variable and the series.
-/

@[expose] public section
namespace MinCostFlow.Num
open Finset

/-- The logarithm's odd-power series, truncated after `n` terms. -/
noncomputable def logSeries (x : ℝ) (n : ℕ) : ℝ :=
  2*∑ i∈range n, ((x-1)/(x+1))^(2*i+1)/(2*i+1)

/-- Normalizing the input confines the series argument to `[0,1/3]`. -/
theorem log_series_argument {x : ℝ} (hlo : 1≤x) (hhi : x≤2) :
    0≤(x-1)/(x+1) ∧ (x-1)/(x+1)≤1/3 := by
  have hp : 0<x+1 := by linarith
  constructor
  · exact div_nonneg (by linarith) (le_of_lt hp)
  · apply (div_le_iff₀ hp).mpr
    linarith

/-- The exact logarithm series on `[1,2]` has a geometric remainder. -/
theorem log_series_remainder {x : ℝ} (hlo : 1≤x) (hhi : x≤2) (n : ℕ) :
    |Real.log x-logSeries x n|≤3*(1/2:ℝ)^(2*n+1) := by
  let t := (x-1)/(x+1)
  obtain ⟨ht0,ht1⟩ := log_series_argument hlo hhi
  change 0≤t at ht0
  change t≤1/3 at ht1
  have ht : |t|<1 := by rw [abs_of_nonneg ht0]; linarith
  have he : (1+t)/(1-t)=x := by
    dsimp [t]
    field_simp
    ring
  have hb := Real.sum_range_sub_log_div_le ht n
  rw [he,abs_of_nonneg ht0] at hb
  have hd : (2/3:ℝ)≤1-t^2 := by nlinarith only [ht0,ht1]
  have hdpos : 0<1-t^2 := by linarith
  have hpow : t^(2*n+1)≤(1/2:ℝ)^(2*n+1) :=
    pow_le_pow_left₀ ht0 (by linarith) _
  have hrem : t^(2*n+1)/(1-t^2)≤(3/2:ℝ)*(1/2:ℝ)^(2*n+1) := by
    apply (div_le_iff₀ hdpos).mpr
    have hm := mul_le_mul_of_nonneg_left hd (show 0≤(3/2:ℝ)*(1/2:ℝ)^(2*n+1) by positivity)
    nlinarith only [hm,hpow]
  have heabs : |Real.log x-logSeries x n|=
      2*|1/2*Real.log x-∑ i∈range n,t^(2*i+1)/(2*i+1)| := by
    rw [← abs_of_nonneg (show (0:ℝ)≤2 by norm_num),← abs_mul]
    congr 1
    dsimp [logSeries,t]
    ring_nf
  rw [heabs]
  have hb' := le_trans hb hrem
  linarith

/-- `q+2` terms suffice for exact-real absolute error at most `2⁻q`. -/
theorem log_series_error {x : ℝ} (hlo : 1≤x) (hhi : x≤2) (q : ℕ) :
    |Real.log x-logSeries x (q+2)|≤1/(2:ℝ)^q := by
  have hb := log_series_remainder hlo hhi (q+2)
  have hp : (1/2:ℝ)^(2*(q+2)+1)≤(1/2:ℝ)^(q+2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hq : (1/2:ℝ)^q=1/(2:ℝ)^q := by rw [div_pow,one_pow]
  have he : 3*(1/2:ℝ)^(q+2)≤1/(2:ℝ)^q := by
    rw [pow_add,hq]
    norm_num
    nlinarith only [inv_nonneg.mpr (show (0:ℝ)≤(2:ℝ)^q by positivity)]
  exact le_trans hb (le_trans (mul_le_mul_of_nonneg_left hp (by norm_num)) he)

end MinCostFlow.Num
