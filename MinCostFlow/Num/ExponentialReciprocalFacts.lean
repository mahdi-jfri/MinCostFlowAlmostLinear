module

public import MinCostFlow.Num.Encoding
public import MinCostFlow.Num.PositiveExponentialFacts
import MinCostFlow.Num.LogarithmRangeFacts
import Mathlib.Tactic

/-!
# Reciprocal error and magnitude decoding for exponential evaluation

A positive exponential approximation with relative error `ε/8`, followed by
a reciprocal with relative error `ε/8`, gives relative error at most `ε`
for the inverse exponential. This file also checks that unsigned magnitude
conversion decodes as a nonnegative signed value when its magnitude fits.
-/

public section
namespace MinCostFlow.Num

/-- Relative error is preserved, with a constant guard, when an underestimate
of a positive number is inverted and the reciprocal is rounded. -/
theorem reciprocal_relative_compose {A T z ε : ℝ}
    (hA : 0<A) (hT : 0<T) (hAT : A≤T) (hε0 : 0≤ε) (hε1 : ε≤1)
    (happrox : |A-T|≤(ε/8)*T) (hrecip : |z-1/A|≤(ε/8)/A) :
    |z-1/T|≤ε/T := by
  have herr := (abs_le.mp happrox).1
  have hmul := mul_le_mul_of_nonneg_right hε1 (le_of_lt hT)
  have hhalf : T≤2*A := by nlinarith only [herr,hmul,hT]
  have hscale : (ε/8)/A≤(ε/4)/T := by
    apply (div_le_div_iff₀ hA hT).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf hε0
    nlinarith only [hh]
  have hinv : |1/A-1/T|≤(ε/4)/T := by
    have he : 1/A-1/T=(T-A)/(A*T) := by field_simp
    rw [he,abs_of_nonneg (div_nonneg (sub_nonneg.mpr hAT) (le_of_lt (mul_pos hA hT)))]
    calc
      _ ≤ ((ε/8)*T)/(A*T) := div_le_div_of_nonneg_right (by linarith only [herr]) (le_of_lt (mul_pos hA hT))
      _ = (ε/8)/A := by field_simp
      _ ≤ (ε/4)/T := hscale
  have hh := le_trans (abs_sub_le z (1/A) (1/T)) (add_le_add (le_trans hrecip hscale) hinv)
  have hu : 0≤ε/T := div_nonneg hε0 (le_of_lt hT)
  simp only [div_eq_mul_inv] at hh hu ⊢
  linarith only [hh,hu]

/-- A stored unsigned magnitude has its intended nonnegative signed value
whenever that magnitude fits the signed block range. -/
theorem magnitude_intVal {mem : ℕ→ℕ} {a h L : ℕ} {N : ℤ}
    (hu : unsignedVal mem a h L=N.natAbs) (hf : Fits h L |N|) :
    intVal mem a h L=|N| := by
  have hbound : ¬capacity h L≤2*N.natAbs := by
    have he : (N.natAbs:ℤ)=|N| := Int.natCast_natAbs _
    obtain ⟨_,hhi⟩ := hf
    omega
  simp only [intVal,hu,signedVal,ite_eq_right hbound,sub_zero,Int.natCast_natAbs]

/-- A fixed-point input bounded by `B` has magnitude numerator at most
`2^(2B)` scale units. -/
theorem exponential_magnitude_bound {P B : ℕ} {N : ℤ}
    (hN : |(N:ℝ)/(2:ℝ)^P|≤B) : |N|≤(2:ℤ)^(2*B)*(2:ℤ)^P := by
  have hp : (0:ℝ)<(2:ℝ)^P := by positivity
  rw [abs_div,abs_of_pos hp] at hN
  have hh := (div_le_iff₀ hp).mp hN
  have hB : (B:ℝ)≤(2:ℝ)^(2*B) := by
    have he : (B:ℝ)+1≤(2:ℝ)^B := by exact_mod_cast log_range_linear_bound B
    have he' : (2:ℝ)^B≤(2:ℝ)^(2*B) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith only [he,he']
  have hh' := le_trans hh (mul_le_mul_of_nonneg_right hB (le_of_lt hp))
  exact_mod_cast hh'

end MinCostFlow.Num
