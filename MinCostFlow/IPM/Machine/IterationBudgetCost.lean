module

public import MinCostFlow.IPM.Machine.IterationBudget
import MinCostFlow.Num.IPM.AlphaFacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The iteration budget has the paper's nearly linear shape

Rounding the logarithm up to binary input lengths and alpha down to a
power of two changes the iteration count by only a constant factor.
The resulting count is bounded by an explicit constant times
`m log³(mU) kappa⁻²` for dyadic quality `kappa=2^-k`, as required by
Theorem 4.6 (page 15). This bounds the count itself, independently of the
cost of the data-structure operations and the numerical work per step.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- The integer iteration budget is linear in the edge count, quadratic
in inverse quality, and cubic in the binary input-length bound. -/
theorem dyadicIterationBudget_bit_bound (m U k : ℕ) (hsize : 2≤m*U) :
    (dyadicIterationBudget m (m.size+U.size) k (Num.IPM.alphaExponent m U):ℝ)≤
      3276800000000000*(m:ℝ)*(m.size+U.size:ℕ)^3*((2:ℝ)^k)^2 := by
  have hm : 0<m := Nat.pos_of_ne_zero (by intro he; simp only [he,zero_mul] at hsize; omega)
  have hb : 0<m.size+U.size := by have hh := Nat.size_pos.mpr hm; omega
  have hscale : 1<Num.IPM.alphaScale m U := by
    unfold Num.IPM.alphaScale
    omega
  have hpNat := (Num.IPM.pow_alphaExponent_lt hscale).le
  have hp : (2:ℝ)^(Num.IPM.alphaExponent m U)≤2000*(m.size+U.size:ℕ) := by
    have hh : (2:ℝ)^(Num.IPM.alphaExponent m U)≤(2*(Num.IPM.alphaScale m U):ℕ) := by
      exact_mod_cast hpNat
    simpa only [Num.IPM.alphaScale,Nat.cast_mul,Nat.cast_ofNat,← mul_assoc,show (2:ℝ)*1000=2000 by norm_num] using hh
  have hp2 := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2^(Num.IPM.alphaExponent m U)) hp 2
  calc
    (dyadicIterationBudget m (m.size+U.size) k (Num.IPM.alphaExponent m U):ℝ)=
        819200000*(m:ℝ)*(m.size+U.size:ℕ)*((2:ℝ)^k)^2*((2:ℝ)^(Num.IPM.alphaExponent m U))^2 := by
      simp only [dyadicIterationBudget,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,
        show 2*(k+Num.IPM.alphaExponent m U+5)=(k+Num.IPM.alphaExponent m U+5)*2 by omega,
        pow_mul,pow_add]
      norm_num
      ring
    _≤819200000*(m:ℝ)*(m.size+U.size:ℕ)*((2:ℝ)^k)^2*
        (2000*(m.size+U.size:ℕ))^2 := mul_le_mul_of_nonneg_left hp2 (by positivity)
    _=3276800000000000*(m:ℝ)*(m.size+U.size:ℕ)^3*((2:ℝ)^k)^2 := by ring

/-- The explicit integer limit has the `Õ(m kappa⁻²)` iteration-count
shape of Theorem 4.6 (page 15), with `kappa=2^-k` and a cubic logarithm. -/
theorem dyadicIterationBudget_log_bound (m U k : ℕ) (hsize : 2≤m*U) :
    (dyadicIterationBudget m (m.size+U.size) k (Num.IPM.alphaExponent m U):ℝ)≤
      409600000000000000*(m:ℝ)*(Real.log ((m*U:ℕ):ℝ))^3*((2:ℝ)^k)^2 := by
  have hbits := (Num.IPM.alpha_bit_length_bounds hsize).2
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (m.size+U.size) : (0:ℝ)≤(m.size+U.size:ℕ)) hbits 3
  calc
    (dyadicIterationBudget m (m.size+U.size) k (Num.IPM.alphaExponent m U):ℝ)≤
        3276800000000000*(m:ℝ)*(m.size+U.size:ℕ)^3*((2:ℝ)^k)^2 :=
      dyadicIterationBudget_bit_bound m U k hsize
    _≤3276800000000000*(m:ℝ)*(5*Real.log ((m*U:ℕ):ℝ))^3*((2:ℝ)^k)^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _=409600000000000000*(m:ℝ)*(Real.log ((m*U:ℕ):ℝ))^3*((2:ℝ)^k)^2 := by ring

end MinCostFlow.IPM.Machine
