module

public import MinCostFlow.Num.LogarithmRangeFacts
import Mathlib.Tactic

/-!
# Error from logarithm range reduction

On values at least one, the logarithm changes by at most the change in its
argument. Thus rounding a halved argument costs at most one last-place unit.
Together with the stored approximation to `log 2`, this gives a linear error
bound in the number of range-reduction steps.
-/

public section
namespace MinCostFlow.Num

private theorem log_difference_le {x y : ℝ} (hx : 1≤x) (hxy : x≤y) :
    Real.log y-Real.log x≤y-x := by
  have hxp : 0<x := by linarith
  have hyp : 0<y := lt_of_lt_of_le hxp hxy
  have hh := Real.log_le_sub_one_of_pos (div_pos hyp hxp)
  rw [Real.log_div (ne_of_gt hyp) (ne_of_gt hxp)] at hh
  have hquot : y/x-1=(y-x)/x := by field_simp
  rw [hquot] at hh
  have hb : (y-x)/x≤y-x := by
    apply (div_le_iff₀ hxp).mpr
    have hm := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hxy)
    simpa only [mul_one] using hm
  exact le_trans hh hb

/-- Above one, the logarithm is Lipschitz with constant one. -/
theorem log_error_above_one {x y : ℝ} (hx : 1≤x) (hy : 1≤y) :
    |Real.log x-Real.log y|≤|x-y| := by
  rcases le_total x y with hxy | hyx
  · have hp : 0<x := by linarith
    have hl := Real.log_le_log hp hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hl),abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hh := log_difference_le hx hxy
    linarith only [hh]
  · have hp : 0<y := by linarith
    have hl := Real.log_le_log hp hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hl),abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact log_difference_le hy hyx

/-- The integer output of normalized evaluation has error at most seventeen
last-place units when its series length is `P+4`. -/
theorem normalizedLogInt_error {P : ℕ} {N : ℤ}
    (hN0 : (2:ℤ)^P≤N) (hN1 : N≤2*(2:ℤ)^P) :
    |(normalizedLogInt P N (P+4):ℝ)/(2:ℝ)^P-Real.log ((N:ℝ)/(2:ℝ)^P)|≤
      17/(2:ℝ)^P := by
  rw [normalizedLogInt_value hN0]
  have hp : (0:ℝ)<(2:ℝ)^P := by positivity
  apply normalized_log_precision_error ?_ ?_ P
  · apply (le_div_iff₀ hp).mpr
    simpa only [one_mul] using (show (2:ℝ)^P≤(N:ℝ) by exact_mod_cast hN0)
  · apply (div_le_iff₀ hp).mpr
    exact_mod_cast hN1

/-- Rounding an argument above two down while halving it costs at most one
last-place unit in the reconstructed logarithm. -/
theorem logarithm_half_error {P : ℕ} {N : ℤ} (hN : 2*(2:ℤ)^P<N) :
    |(Real.log (((N/2:ℤ):ℝ)/(2:ℝ)^P)+Real.log 2)-
      Real.log ((N:ℝ)/(2:ℝ)^P)|≤1/(2:ℝ)^P := by
  have hp : (0:ℝ)<(2:ℝ)^P := by positivity
  have hhalf : (2:ℤ)^P≤N/2 := by omega
  have hy : 1≤((N/2:ℤ):ℝ)/(2:ℝ)^P := by
    apply (le_div_iff₀ hp).mpr
    simpa only [one_mul] using (show (2:ℝ)^P≤((N/2:ℤ):ℝ) by exact_mod_cast hhalf)
  have hx : 1≤((N:ℝ)/(2:ℝ)^P)/2 := by
    have hh : 2*(2:ℝ)^P≤(N:ℝ) := by exact_mod_cast (le_of_lt hN)
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (le_div_iff₀ hp).mpr
    linarith only [hh]
  have hb := log_error_above_one hy hx
  have hround : |((N/2:ℤ):ℝ)/(2:ℝ)^P-((N:ℝ)/(2:ℝ)^P)/2|≤1/(2:ℝ)^P := by
    have hh := floor_scaled_error (((N:ℝ)/(2:ℝ)^P)/2) P
    have he : ((N:ℝ)/(2:ℝ)^P)/2*(2:ℝ)^P=(N:ℝ)/2 := by field_simp
    rw [he,show (2:ℝ)=((2:ℤ):ℝ) by norm_num,
      Int.floor_div_cast_of_nonneg (by decide : (0:ℤ)≤2),Int.floor_intCast] at hh
    exact hh
  have hnp : (0:ℝ)<(N:ℝ)/(2:ℝ)^P := by linarith only [hx]
  rw [Real.log_div (ne_of_gt hnp) (by norm_num)] at hb
  have he : Real.log (((N/2:ℤ):ℝ)/(2:ℝ)^P)+Real.log 2-Real.log ((N:ℝ)/(2:ℝ)^P)=
      Real.log (((N/2:ℤ):ℝ)/(2:ℝ)^P)-(Real.log ((N:ℝ)/(2:ℝ)^P)-Real.log 2) := by ring
  rw [he]
  exact le_trans hb hround

/-- `E` reduction steps give absolute error at most `(18E+17)2⁻ᴾ`.
The constant block approximates `log 2` to seventeen last-place units. -/
theorem rangeLogInt_error {P : ℕ} {C : ℤ}
    (hC : |(C:ℝ)/(2:ℝ)^P-Real.log 2|≤17/(2:ℝ)^P) (E : ℕ) (N : ℤ)
    (hlo : (2:ℤ)^P≤(2:ℤ)^E*N) (hhi : N≤(2:ℤ)^(E+1)*(2:ℤ)^P) :
    |(rangeLogInt P C E N:ℝ)/(2:ℝ)^P-Real.log ((N:ℝ)/(2:ℝ)^P)|≤
      (18*(E:ℝ)+17)*(1/(2:ℝ)^P) := by
  have hu : (0:ℝ)≤1/(2:ℝ)^P := by positivity
  induction E generalizing N with
  | zero =>
    have hN0 : (2:ℤ)^P≤N := by simpa only [pow_zero,one_mul] using hlo
    have hN1 : N≤2*(2:ℤ)^P := by simpa only [zero_add,pow_one] using hhi
    have hh := normalizedLogInt_error hN0 hN1
    simpa only [rangeLogInt,Nat.cast_zero,mul_zero,zero_add,div_eq_mul_inv,one_mul] using hh
  | succ E ih =>
    have hscale : (0:ℤ)<(2:ℤ)^P := by positivity
    have hNpos : 0<N := by
      by_contra hn
      have hm := mul_nonpos_of_nonneg_of_nonpos
        (show (0:ℤ)≤(2:ℤ)^(E+1) by positivity) (show N≤0 by omega)
      omega
    have hxpos : (0:ℝ)<(N:ℝ)/(2:ℝ)^P := div_pos (by exact_mod_cast hNpos) (by positivity)
    rw [rangeLogInt]
    split_ifs with hsmall hlarge
    · obtain ⟨hlo',hhi'⟩ := log_range_double hlo hsmall
      have hr := ih (2*N) hlo' hhi'
      have hlog : Real.log (((2*N:ℤ):ℝ)/(2:ℝ)^P)=Real.log 2+Real.log ((N:ℝ)/(2:ℝ)^P) := by
        rw [Int.cast_mul,Int.cast_ofNat,mul_div_assoc,Real.log_mul (by norm_num) (ne_of_gt hxpos)]
      have he : ((rangeLogInt P C E (2*N)-C:ℤ):ℝ)/(2:ℝ)^P-Real.log ((N:ℝ)/(2:ℝ)^P)=
          ((rangeLogInt P C E (2*N):ℝ)/(2:ℝ)^P-Real.log (((2*N:ℤ):ℝ)/(2:ℝ)^P))-
          ((C:ℝ)/(2:ℝ)^P-Real.log 2) := by rw [hlog]; push_cast; ring
      rw [he]
      have htri := abs_sub_le
        ((rangeLogInt P C E (2*N):ℝ)/(2:ℝ)^P-Real.log (((2*N:ℤ):ℝ)/(2:ℝ)^P)) 0
        ((C:ℝ)/(2:ℝ)^P-Real.log 2)
      simp only [sub_zero,zero_sub,abs_neg] at htri
      have hb := le_trans htri (add_le_add hr hC)
      push_cast at hb ⊢
      simp only [div_eq_mul_inv] at hb hu ⊢
      nlinarith only [hb,hu]
    · obtain ⟨hlo',hhi'⟩ := log_range_half hhi hlarge
      have hr := ih (N/2) hlo' hhi'
      have hh := logarithm_half_error hlarge
      have he : ((rangeLogInt P C E (N/2)+C:ℤ):ℝ)/(2:ℝ)^P-Real.log ((N:ℝ)/(2:ℝ)^P)=
          ((rangeLogInt P C E (N/2):ℝ)/(2:ℝ)^P-Real.log (((N/2:ℤ):ℝ)/(2:ℝ)^P))+
          ((C:ℝ)/(2:ℝ)^P-Real.log 2)+
          (Real.log (((N/2:ℤ):ℝ)/(2:ℝ)^P)+Real.log 2-Real.log ((N:ℝ)/(2:ℝ)^P)) := by
        push_cast
        ring
      rw [he]
      have htri := abs_add_le
        (((rangeLogInt P C E (N/2):ℝ)/(2:ℝ)^P-Real.log (((N/2:ℤ):ℝ)/(2:ℝ)^P))+
          ((C:ℝ)/(2:ℝ)^P-Real.log 2))
        (Real.log (((N/2:ℤ):ℝ)/(2:ℝ)^P)+Real.log 2-Real.log ((N:ℝ)/(2:ℝ)^P))
      have htri' := abs_add_le
        ((rangeLogInt P C E (N/2):ℝ)/(2:ℝ)^P-Real.log (((N/2:ℤ):ℝ)/(2:ℝ)^P))
        ((C:ℝ)/(2:ℝ)^P-Real.log 2)
      have hb := le_trans htri (add_le_add (le_trans htri' (add_le_add hr hC)) hh)
      push_cast at hb ⊢
      simp only [div_eq_mul_inv] at hb hu ⊢
      nlinarith only [hb,hu]
    · have hN0 : (2:ℤ)^P≤N := by omega
      have hN1 : N≤2*(2:ℤ)^P := by omega
      have hb := normalizedLogInt_error hN0 hN1
      have hE0 : (0:ℝ)≤E := Nat.cast_nonneg E
      push_cast at hb ⊢
      simp only [div_eq_mul_inv] at hb hu ⊢
      nlinarith only [hb,hu,hE0,mul_nonneg hE0 hu]

/-- Precision `q+E+10` covers all errors in `E` range-reduction steps. -/
theorem log_range_error_budget {P E q : ℕ} (hP : q+E+10≤P) :
    (18*(E:ℝ)+17)*(1/(2:ℝ)^P)≤1/(2:ℝ)^q := by
  have he : (E:ℝ)+1≤(2:ℝ)^E := by exact_mod_cast log_range_linear_bound E
  have he' : 18*(E:ℝ)+17≤(2:ℝ)^E*1024 := by
    have hp : (0:ℝ)<(2:ℝ)^E := by positivity
    linarith only [he,hp]
  have hp : (2:ℝ)^(q+E+10)≤(2:ℝ)^P := pow_le_pow_right₀ (by norm_num) hP
  have hprod : (18*(E:ℝ)+17)*(2:ℝ)^q≤(2:ℝ)^P := by
    have hh := mul_le_mul_of_nonneg_left he' (show (0:ℝ)≤(2:ℝ)^q by positivity)
    rw [pow_add,pow_add,show (2:ℝ)^10=1024 by norm_num] at hp
    nlinarith only [hh,hp]
  rw [mul_one_div]
  apply (div_le_div_iff₀ (show (0:ℝ)<(2:ℝ)^P by positivity)
    (show (0:ℝ)<(2:ℝ)^q by positivity)).mpr
  simpa only [one_mul] using hprod

end MinCostFlow.Num
