module

public import MinCostFlow.Num.NormalizedLogarithmIntegerFacts
import MinCostFlow.Num.WordBounds
import Mathlib.Tactic

/-!
# Range reduction for the fixed-point logarithm

Double an input below one, or halve an input above two. In the latter case,
the integer numerator is rounded down. After at most `E` steps, an input in
`[2⁻ᴱ,2ᴱ⁺¹]` lies in `[1,2]`. Each doubling subtracts the stored logarithm
of two from the answer, and each halving adds it.
-/

@[expose] public section
namespace MinCostFlow.Num

/-- Integer calculation for logarithm range reduction. The parameter `C`
is the numerator of the stored approximation to `log 2`. -/
def rangeLogInt (P : ℕ) (C : ℤ) : ℕ→ℤ→ℤ
  | 0,N => normalizedLogInt P N (P+4)
  | E+1,N => if N<(2:ℤ)^P then rangeLogInt P C E (2*N)-C
      else if 2*(2:ℤ)^P<N then rangeLogInt P C E (N/2)+C
      else normalizedLogInt P N (P+4)

/-- Doubling a value below the scale reduces the exponent range by one. -/
theorem log_range_double {P E : ℕ} {N : ℤ}
    (hlo : (2:ℤ)^P≤(2:ℤ)^(E+1)*N) (hsmall : N<(2:ℤ)^P) :
    (2:ℤ)^P≤(2:ℤ)^E*(2*N) ∧ 2*N≤(2:ℤ)^(E+1)*(2:ℤ)^P := by
  have hp : (0:ℤ)<(2:ℤ)^P := pow_pos (by decide) _
  have he : (1:ℤ)≤(2:ℤ)^E := one_le_pow₀ (by decide)
  constructor
  · simpa only [pow_succ,mul_assoc,mul_left_comm,mul_comm] using hlo
  · have hh := mul_le_mul_of_nonneg_right he (le_of_lt hp)
    rw [pow_succ]
    nlinarith only [hh,hsmall]

/-- Halving a value above twice the scale reduces the exponent range by one,
even after integer rounding. -/
theorem log_range_half {P E : ℕ} {N : ℤ}
    (hhi : N≤(2:ℤ)^(E+1+1)*(2:ℤ)^P) (hlarge : 2*(2:ℤ)^P<N) :
    (2:ℤ)^P≤(2:ℤ)^E*(N/2) ∧ N/2≤(2:ℤ)^(E+1)*(2:ℤ)^P := by
  have hp : (0:ℤ)<(2:ℤ)^P := pow_pos (by decide) _
  have he : (1:ℤ)≤(2:ℤ)^E := one_le_pow₀ (by decide)
  have hhalf : (2:ℤ)^P≤N/2 := by omega
  constructor
  · have hh := mul_le_mul_of_nonneg_right he (show (0:ℤ)≤N/2 by omega)
    simp only [one_mul] at hh
    exact le_trans hhalf hh
  · rw [pow_succ] at hhi
    have hh : N≤2*((2:ℤ)^(E+1)*(2:ℤ)^P) := by nlinarith only [hhi]
    omega

/-- The range-reduced integer logarithm has magnitude at most two scale
units per reduction step, plus two for the normalized result. -/
theorem rangeLogInt_bounds {P : ℕ} {C : ℤ}
    (hC0 : 0≤C) (hC1 : C≤2*(2:ℤ)^P) (E : ℕ) (N : ℤ)
    (hlo : (2:ℤ)^P≤(2:ℤ)^E*N) (hhi : N≤(2:ℤ)^(E+1)*(2:ℤ)^P) :
    |rangeLogInt P C E N|≤2*(E+1:ℕ)*(2:ℤ)^P := by
  induction E generalizing N with
  | zero =>
    have hN0 : (2:ℤ)^P≤N := by simpa only [pow_zero,one_mul] using hlo
    have hN1 : N≤2*(2:ℤ)^P := by simpa only [zero_add,pow_one] using hhi
    obtain ⟨_,_,hZ0,hZ1⟩ := normalizedLogInt_bounds hN0 hN1 (P+4)
    simpa only [rangeLogInt,abs_of_nonneg hZ0,zero_add,Nat.cast_one,mul_one] using hZ1
  | succ E ih =>
    rw [rangeLogInt]
    split_ifs with hsmall hlarge
    · obtain ⟨hlo',hhi'⟩ := log_range_double hlo hsmall
      have hr := ih (2*N) hlo' hhi'
      have htri : |rangeLogInt P C E (2*N)-C|≤|rangeLogInt P C E (2*N)|+|C| := by
        simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (rangeLogInt P C E (2*N)) 0 C
      have hb := le_trans htri
        (add_le_add hr (show |C|≤2*(2:ℤ)^P by rwa [abs_of_nonneg hC0]))
      simp only [sub_zero,zero_sub,abs_neg,Nat.cast_add,Nat.cast_one] at hb ⊢
      nlinarith only [hb]
    · obtain ⟨hlo',hhi'⟩ := log_range_half hhi hlarge
      have hr := ih (N/2) hlo' hhi'
      have hb := le_trans (abs_add_le (rangeLogInt P C E (N/2)) C)
        (add_le_add hr (show |C|≤2*(2:ℤ)^P by rwa [abs_of_nonneg hC0]))
      simp only [Nat.cast_add,Nat.cast_one] at hb ⊢
      nlinarith only [hb]
    · have hN0 : (2:ℤ)^P≤N := by omega
      have hN1 : N≤2*(2:ℤ)^P := by omega
      obtain ⟨_,_,hZ0,hZ1⟩ := normalizedLogInt_bounds hN0 hN1 (P+4)
      rw [abs_of_nonneg hZ0]
      have hp0 : (0:ℤ)≤(2:ℤ)^P := by positivity
      have hE0 : (0:ℤ)≤E := Int.natCast_nonneg E
      push_cast
      nlinarith only [hZ1,hp0,hE0,mul_nonneg hE0 hp0]

/-- A linear factor in the number of reductions is bounded by its dyadic
scale. -/
theorem log_range_linear_bound (E : ℕ) : E+1≤2^E := by
  induction E with
  | zero => decide
  | succ E ih =>
    rw [pow_succ]
    omega

/-- The series denominator bounds hold when the precision has ten guard bits. -/
theorem log_series_denominator_bound {P : ℕ} (hP : 10≤P) : 2*(P+4)+1≤2^P := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hP
  clear hP
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 10+(k+1)=(10+k)+1 by omega,pow_succ]
    omega

/-- The signed logarithm range fits with four spare bits beyond precision
and the reduction exponent. -/
theorem fits_log_range {h L P E : ℕ} {v : ℤ}
    (hwidth : P+E+4≤h*L) (hv : |v|≤2*(E+1:ℕ)*(2:ℤ)^P) : Fits h L v := by
  have he : (E+1:ℕ)≤(2:ℤ)^E := by exact_mod_cast log_range_linear_bound E
  have hp : (0:ℤ)<(2:ℤ)^P := by positivity
  have he0 : (0:ℤ)<(2:ℤ)^E := by positivity
  have hb : |v|≤2*(2:ℤ)^E*(2:ℤ)^P := by
    have hm := mul_le_mul_of_nonneg_right he (le_of_lt hp)
    nlinarith only [hv,hm]
  have hc : (2:ℤ)^(P+E+4)≤(capacity h L:ℤ) := by
    rw [MinCostFlow.Num.capacity_eq_two_pow]
    push_cast
    exact pow_le_pow_right₀ (by decide) hwidth
  simp only [pow_add,show (2:ℤ)^4=16 by decide] at hc
  have hlo := neg_abs_le v
  have hhi := le_abs_self v
  have hmul := mul_pos hp he0
  constructor <;> nlinarith only [hb,hc,hlo,hhi,hmul]

end MinCostFlow.Num
