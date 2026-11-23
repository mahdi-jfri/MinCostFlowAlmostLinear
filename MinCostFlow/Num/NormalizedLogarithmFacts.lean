module

public import MinCostFlow.Num.RoundedLogarithmFacts
import Mathlib.Tactic

/-!
# Complete rounding bound for a normalized logarithm

First round `(x-1)/(x+1)`, then its square. Evaluate the rounded Horner
recurrence, round the final product, and double it exactly. For inputs in
`[1,2]`, all these roundings together cost at most sixteen last-place units.
-/

@[expose] public section
namespace MinCostFlow.Num

/-- The normalized logarithm calculation, including each fixed-point rounding. -/
noncomputable def normalizedLogRounded (P : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  let t := dyadicFloor P ((x-1)/(x+1))
  let s := dyadicFloor P (t^2)
  2*dyadicFloor P (t*roundedLogHorner P s 0 n)

/-- The argument and its rounded square remain nonnegative and small. -/
theorem normalized_log_rounding_bounds {x : ℝ} (hx0 : 1≤x) (hx1 : x≤2) (P : ℕ) :
    0≤dyadicFloor P ((x-1)/(x+1)) ∧ dyadicFloor P ((x-1)/(x+1))≤1/3 ∧
    0≤dyadicFloor P ((dyadicFloor P ((x-1)/(x+1)))^2) ∧
    dyadicFloor P ((dyadicFloor P ((x-1)/(x+1)))^2)≤1/2 := by
  obtain ⟨hr0,hr1⟩ := log_series_argument hx0 hx1
  have ht0 := dyadicFloor_nonneg (P:=P) hr0
  have ht1 := le_trans (dyadicFloor_le P _) hr1
  exact ⟨ht0,ht1,dyadicFloor_nonneg (sq_nonneg _),
    le_trans (dyadicFloor_le P _) (by nlinarith only [ht0,ht1])⟩

/-- Every rounding in the normalized logarithm contributes at most sixteen
last-place units in total. This bound is uniform in the number of terms. -/
theorem normalized_log_rounding_error {x : ℝ} (hx0 : 1≤x) (hx1 : x≤2) (P n : ℕ) :
    |normalizedLogRounded P x n-logSeries x n|≤16/(2:ℝ)^P := by
  let r := (x-1)/(x+1)
  let t := dyadicFloor P r
  let s := dyadicFloor P (t^2)
  let u := 1/(2:ℝ)^P
  have hu : 0≤u := by dsimp [u]; positivity
  obtain ⟨hr0,hr1⟩ := log_series_argument hx0 hx1
  change 0≤r at hr0
  change r≤1/3 at hr1
  obtain ⟨ht0,ht1,hs0,hs1⟩ := normalized_log_rounding_bounds hx0 hx1 P
  change 0≤t at ht0
  change t≤1/3 at ht1
  change 0≤s at hs0
  change s≤1/2 at hs1
  have htr : |t-r|≤u := dyadicFloor_error P r
  have hsq : |s-t^2|≤u := dyadicFloor_error P (t^2)
  have ht2 : t^2≤1/2 := by nlinarith only [ht0,ht1]
  have hr2 : r^2≤1/2 := by nlinarith only [hr0,hr1]
  have hsqdiff : |t^2-r^2|≤u := by
    have he : t^2-r^2=(t-r)*(t+r) := by ring
    rw [he,abs_mul,abs_of_nonneg (add_nonneg ht0 hr0)]
    have hb := mul_le_mul htr (show t+r≤1 by linarith) (add_nonneg ht0 hr0) hu
    simpa only [mul_one] using hb
  have hround := roundedLogHorner_error hs0 hs1 (sq_nonneg t) ht2 hsq 0 n
  have harg := logHorner_argument_error (sq_nonneg t) ht2 (sq_nonneg r) hr2 hu hsqdiff 0 n
  have hH : |roundedLogHorner P s 0 n-logHorner (r^2) 0 n|≤12*u := by
    have hb := le_trans (abs_sub_le (roundedLogHorner P s 0 n)
      (logHorner (t^2) 0 n) (logHorner (r^2) 0 n)) (add_le_add hround harg)
    dsimp only [u] at hb ⊢
    simp only [div_eq_mul_inv] at hb ⊢
    linarith only [hb]
  obtain ⟨hH0,hH2⟩ := logHorner_bounds (sq_nonneg r) hr2 0 n
  have hprod : |t*roundedLogHorner P s 0 n-r*logHorner (r^2) 0 n|≤6*u := by
    have he : t*roundedLogHorner P s 0 n-r*logHorner (r^2) 0 n=
        t*(roundedLogHorner P s 0 n-logHorner (r^2) 0 n)+(t-r)*logHorner (r^2) 0 n := by ring
    rw [he]
    calc
      _ ≤ |t*(roundedLogHorner P s 0 n-logHorner (r^2) 0 n)|+
          |(t-r)*logHorner (r^2) 0 n| := abs_add_le _ _
      _ = t*|roundedLogHorner P s 0 n-logHorner (r^2) 0 n|+
          |t-r| * logHorner (r^2) 0 n := by
        rw [abs_mul,abs_mul,abs_of_nonneg ht0,abs_of_nonneg hH0]
      _ ≤ (1/3:ℝ)*(12*u)+u*2 := add_le_add
        (mul_le_mul ht1 hH (abs_nonneg _) (by norm_num)) (mul_le_mul htr hH2 hH0 hu)
      _ = 6*u := by ring
  have hfinal := le_trans (abs_sub_le
    (dyadicFloor P (t*roundedLogHorner P s 0 n))
    (t*roundedLogHorner P s 0 n) (r*logHorner (r^2) 0 n))
    (add_le_add (dyadicFloor_error P _) hprod)
  have he : normalizedLogRounded P x n-logSeries x n=
      2*(dyadicFloor P (t*roundedLogHorner P s 0 n)-r*logHorner (r^2) 0 n) := by
    rw [← logHorner_series]
    dsimp [normalizedLogRounded,r,t,s]
    ring
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  change 2*|dyadicFloor P (t*roundedLogHorner P s 0 n)-r*logHorner (r^2) 0 n|≤16/(2:ℝ)^P
  change |dyadicFloor P (t*roundedLogHorner P s 0 n)-r*logHorner (r^2) 0 n|≤u+6*u at hfinal
  dsimp only [u] at hfinal hu
  simp only [div_eq_mul_inv] at hfinal hu ⊢
  linarith only [hfinal,hu]

/-- Ten guard bits and `q+4` terms suffice for absolute error `2⁻q`
after all arithmetic roundings on a normalized input. -/
theorem normalized_log_error {x : ℝ} {P q : ℕ}
    (hx0 : 1≤x) (hx1 : x≤2) (hP : q+10≤P) :
    |normalizedLogRounded P x (q+4)-Real.log x|≤1/(2:ℝ)^q := by
  have hround := normalized_log_rounding_error hx0 hx1 P (q+4)
  have htail := log_series_error hx0 hx1 (q+2)
  have hp : (2:ℝ)^(q+10)≤(2:ℝ)^P := pow_le_pow_right₀ (by norm_num) hP
  have hp' : 1/(2:ℝ)^P≤1/((2:ℝ)^q*1024) := by
    have hh := one_div_le_one_div_of_le (show (0:ℝ)<(2:ℝ)^(q+10) by positivity) hp
    simpa only [pow_add,show (2:ℝ)^10=1024 by norm_num] using hh
  have htail' : |logSeries x (q+4)-Real.log x|≤(1/(2:ℝ)^q)/4 := by
    rw [abs_sub_comm]
    convert htail using 1 <;> norm_num [pow_add,div_eq_mul_inv] <;> ring
  have htotal := le_trans (abs_sub_le (normalizedLogRounded P x (q+4))
    (logSeries x (q+4)) (Real.log x)) (add_le_add hround htail')
  have hround' : 16/(2:ℝ)^P≤(1/(2:ℝ)^q)/64 := by
    have hh := mul_le_mul_of_nonneg_left hp' (by norm_num : (0:ℝ)≤16)
    convert hh using 1 <;> field_simp <;> ring
  have hb := le_trans htotal (add_le_add hround' (le_refl _))
  have hu : (0:ℝ)≤1/(2:ℝ)^q := by positivity
  linarith

/-- Taking `P+4` terms makes the truncation smaller than one last-place
unit, leaving a bound of seventeen units after every rounding. -/
theorem normalized_log_precision_error {x : ℝ} (hx0 : 1≤x) (hx1 : x≤2) (P : ℕ) :
    |normalizedLogRounded P x (P+4)-Real.log x|≤17/(2:ℝ)^P := by
  have hround := normalized_log_rounding_error hx0 hx1 P (P+4)
  have htail := log_series_error hx0 hx1 (P+2)
  have ht : |logSeries x (P+4)-Real.log x|≤(1/(2:ℝ)^P)/4 := by
    rw [abs_sub_comm]
    convert htail using 1 <;> norm_num [pow_add,div_eq_mul_inv] <;> ring
  have hb := le_trans (abs_sub_le (normalizedLogRounded P x (P+4))
    (logSeries x (P+4)) (Real.log x)) (add_le_add hround ht)
  have hu : (0:ℝ)≤1/(2:ℝ)^P := by positivity
  simp only [div_eq_mul_inv] at hb hu ⊢
  linarith only [hb,hu]

end MinCostFlow.Num
