module

public import MinCostFlow.IPM.Definitions
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# A representable barrier exponent

The computational model on page 7 stores fixed-point numbers. The analytic
barrier exponent is `1/(1000 log(mU))`. Replace it by the inverse of the least
power of two above `1000*(bits(m)+bits(U))`, with `Nat.size` as bit length.
The replacement lies between one tenth of the analytic exponent and that
exponent when `mU≥2`.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM

/-- Integer threshold for the dyadic barrier exponent. Bit length is zero
at zero, and otherwise counts the ordinary binary digits. -/
def alphaScale (m U : ℕ) : ℕ := 1000*(m.size+U.size)

/-- Least exponent whose power of two reaches the threshold. -/
def alphaExponent (m U : ℕ) : ℕ := Nat.clog 2 (alphaScale m U)

/-- The dyadic exponent stored by the IPM, as a real number. -/
noncomputable def alphaPrime (m U : ℕ) : ℝ := 1/(2:ℝ)^(alphaExponent m U)

/-- The chosen exponent is exactly the least one reaching the threshold. -/
theorem alphaExponent_le_iff (m U j : ℕ) :
    alphaExponent m U≤j ↔ alphaScale m U≤2^j := Nat.clog_le_iff_le_pow (by decide)

/-- The chosen exponent reaches the threshold. -/
theorem alphaScale_le_pow (m U : ℕ) : alphaScale m U≤2^(alphaExponent m U) :=
  Nat.le_pow_clog (by decide) _

/-- Ceiling to a power of two increases a threshold greater than one by less
than a factor of two. -/
theorem pow_alphaExponent_lt {m U : ℕ} (hs : 1<alphaScale m U) :
    2^(alphaExponent m U)<2*alphaScale m U := by
  have hk : 0<alphaExponent m U := Nat.clog_pos (by decide) hs
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1<2) hs
  change 2^(alphaExponent m U-1)<alphaScale m U at hp
  have he : alphaExponent m U=alphaExponent m U-1+1 := by omega
  rw [he,pow_succ]
  change 2^(alphaExponent m U-1)*2<2*alphaScale m U
  omega

/-- Binary input lengths bound the natural logarithm from above and are at
most five times that logarithm when the product is at least two. -/
theorem alpha_bit_length_bounds {m U : ℕ} (h2 : 2≤m*U) :
    Real.log ((m*U:ℕ):ℝ)≤((m.size+U.size:ℕ):ℝ) ∧
    ((m.size+U.size:ℕ):ℝ)≤5*Real.log ((m*U:ℕ):ℝ) := by
  have hm : 0<m := Nat.pos_of_ne_zero (by intro he; simp only [he,zero_mul] at h2; omega)
  have hU : 0<U := Nat.pos_of_ne_zero (by intro he; simp only [he,mul_zero] at h2; omega)
  have hbm := Nat.size_pos.mpr hm
  have hbU := Nat.size_pos.mpr hU
  have hmlo : 2^(m.size-1)≤m := Nat.lt_size.mp (by omega)
  have hUlo : 2^(U.size-1)≤U := Nat.lt_size.mp (by omega)
  have hpLo : 2^((m.size-1)+(U.size-1))≤m*U := by
    rw [pow_add]
    exact Nat.mul_le_mul hmlo hUlo
  have hpHi : m*U<2^(m.size+U.size) := by
    rw [pow_add]
    exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self m) hU)
      (Nat.mul_le_mul_left _ (le_of_lt (Nat.lt_size_self U)))
  have hlo : (((m.size-1)+(U.size-1):ℕ):ℝ)*Real.log 2≤Real.log ((m*U:ℕ):ℝ) := by
    have hh := Real.log_le_log (show (0:ℝ)<(2:ℝ)^((m.size-1)+(U.size-1)) by positivity)
      (show (2:ℝ)^((m.size-1)+(U.size-1))≤((m*U:ℕ):ℝ) by exact_mod_cast hpLo)
    rwa [Real.log_pow] at hh
  have hhi : Real.log ((m*U:ℕ):ℝ)≤((m.size+U.size:ℕ):ℝ)*Real.log 2 := by
    have hh := Real.log_le_log (show (0:ℝ)<((m*U:ℕ):ℝ) by exact_mod_cast (show 0<m*U by omega))
      (show ((m*U:ℕ):ℝ)≤(2:ℝ)^(m.size+U.size) by exact_mod_cast le_of_lt hpHi)
    rwa [Real.log_pow] at hh
  have hlog2 : Real.log 2≤Real.log ((m*U:ℕ):ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast h2)
  have hlogLo : (3/5:ℝ)≤Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlogHi : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [hh]
  have hbits0 : (0:ℝ)≤((m.size+U.size:ℕ):ℝ) := Nat.cast_nonneg _
  have heNat : (m.size-1)+(U.size-1)+2=m.size+U.size := by omega
  have he : (((m.size-1)+(U.size-1):ℕ):ℝ)=((m.size+U.size:ℕ):ℝ)-2 := by
    have hh : (((m.size-1)+(U.size-1):ℕ):ℝ)+2=((m.size+U.size:ℕ):ℝ) := by exact_mod_cast heNat
    linarith only [hh]
  rw [he] at hlo
  constructor
  · have hh := mul_le_mul_of_nonneg_left hlogHi hbits0
    nlinarith only [hhi,hh]
  · have hh := mul_le_mul_of_nonneg_left hlogLo hbits0
    nlinarith only [hlo,hlog2,hh]

/-- The representable barrier exponent is within the required constant factor
of the analytic exponent in Section 4 of Chen et al. -/
theorem alphaPrime_bounds (I : Instance) (U : ℕ) (h2 : 2≤I.m*U) :
    MinCostFlow.IPM.alpha I (U:ℝ)/10≤alphaPrime I.m U ∧
    alphaPrime I.m U≤MinCostFlow.IPM.alpha I (U:ℝ) := by
  obtain ⟨hlog,hbits⟩ := alpha_bit_length_bounds h2
  have hm : 0<I.m := Nat.pos_of_ne_zero (by intro he; simp only [he,zero_mul] at h2; omega)
  have hbm := Nat.size_pos.mpr hm
  have hs : 1<alphaScale I.m U := by unfold alphaScale; omega
  have hpow := pow_alphaExponent_lt hs
  have hscale := alphaScale_le_pow I.m U
  have hlogpos : 0<Real.log ((I.m*U:ℕ):ℝ) := Real.log_pos (by exact_mod_cast (show 1<I.m*U by omega))
  have hupper : 1000*Real.log ((I.m*U:ℕ):ℝ)≤(2:ℝ)^(alphaExponent I.m U) := by
    have hh : (1000:ℝ)*((I.m.size+U.size:ℕ):ℝ)≤(2:ℝ)^(alphaExponent I.m U) := by
      exact_mod_cast hscale
    linarith only [hlog,hh]
  have hlower : (2:ℝ)^(alphaExponent I.m U)≤10000*Real.log ((I.m*U:ℕ):ℝ) := by
    have hh : (2:ℝ)^(alphaExponent I.m U)<2000*((I.m.size+U.size:ℕ):ℝ) := by
      have hhNat : 2^(alphaExponent I.m U)<2000*(I.m.size+U.size) := by
        simpa only [alphaScale,← Nat.mul_assoc,show 2*1000=2000 by decide] using hpow
      exact_mod_cast hhNat
    linarith only [hh,hbits]
  have hsame : MinCostFlow.IPM.alpha I (U:ℝ)=1/(1000*Real.log ((I.m*U:ℕ):ℝ)) := by
    simp only [MinCostFlow.IPM.alpha,Nat.cast_mul]
  rw [hsame]
  unfold alphaPrime
  constructor
  · rw [div_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith only [hlower]
  · exact one_div_le_one_div_of_le (by positivity) hupper

end MinCostFlow.Num.IPM
