module

public import MinCostFlow.Num.DyadicRoundingFacts
public import MinCostFlow.Num.ExponentialFacts
import Mathlib.Tactic

/-!
# Rounded exponential series for a nonnegative reduced argument

Evaluate the Taylor polynomial by Horner's rule. Each step multiplies by the
argument, rounds, divides by the next coefficient index, rounds, and adds one.
For arguments at most one half, the recurrence contracts errors. Its total
rounding error is at most four last-place units, independent of its length.
-/

@[expose] public section
namespace MinCostFlow.Num

/-- Exponential Taylor polynomial in Horner form, starting at index `i`. -/
noncomputable def expHorner (x : ℝ) (i : ℕ) : ℕ→ℝ
  | 0 => 1
  | n+1 => 1+(x*expHorner x (i+1) n)/((i+1:ℕ):ℝ)

/-- Fixed-point Horner evaluation with both product and division rounded. -/
noncomputable def roundedExpHorner (P : ℕ) (x : ℝ) (i : ℕ) : ℕ→ℝ
  | 0 => 1
  | n+1 => 1+dyadicFloor P ((dyadicFloor P (x*roundedExpHorner P x (i+1) n))/((i+1:ℕ):ℝ))

/-- Completing a Horner tail gives the corresponding exponential polynomial. -/
theorem expHorner_expNear (x : ℝ) (i n : ℕ) :
    Real.expNear i x (expHorner x i n)=expSeries x (i+n+1) := by
  induction n generalizing i with
  | zero =>
    simp only [expHorner,Real.expNear,expSeries,add_zero,Finset.sum_range_succ,mul_one]
  | succ n ih =>
    rw [expHorner]
    have he : 1+x*expHorner x (i+1) n/((i+1:ℕ):ℝ)=
        1+x/((i:ℝ)+1)*expHorner x (i+1) n := by push_cast; ring
    rw [he,← Real.expNear_succ,ih]
    congr 1
    omega

/-- At index zero, the Horner recurrence is the first `n+1` Taylor terms. -/
theorem expHorner_series (x : ℝ) (n : ℕ) :
    expHorner x 0 n=expSeries x (n+1) := by
  simpa only [Real.expNear_zero,zero_add] using expHorner_expNear x 0 n

/-- Both exact and rounded Horner values stay between one and two on the
reduced nonnegative interval. The rounded values never exceed the exact ones. -/
theorem expHorner_bounds {x : ℝ} (hx0 : 0≤x) (hx1 : x≤1/2) (P i n : ℕ) :
    1≤roundedExpHorner P x i n ∧ roundedExpHorner P x i n≤expHorner x i n ∧
    expHorner x i n≤2 := by
  induction n generalizing i with
  | zero => simp [roundedExpHorner,expHorner]
  | succ n ih =>
    obtain ⟨hr0,hr1,he1⟩ := ih (i+1)
    have hd : (1:ℝ)≤((i+1:ℕ):ℝ) := by exact_mod_cast (show 1≤ i+1 by omega)
    have hdpos : (0:ℝ)<((i+1:ℕ):ℝ) := by linarith
    have hp0 : 0≤x*roundedExpHorner P x (i+1) n := mul_nonneg hx0 (by linarith)
    have hround0 := dyadicFloor_nonneg (P:=P) hp0
    have hquot0 := dyadicFloor_nonneg (P:=P) (div_nonneg hround0 (le_of_lt hdpos))
    have hround1 := dyadicFloor_le P (x*roundedExpHorner P x (i+1) n)
    have hprod := mul_le_mul_of_nonneg_left hr1 hx0
    have hquot1 := le_trans (dyadicFloor_le P _)
      (div_le_div_of_nonneg_right (le_trans hround1 hprod) (le_of_lt hdpos))
    have hprod1 : x*expHorner x (i+1) n≤1 := by
      have hh := mul_le_mul hx1 he1 (by linarith : 0≤expHorner x (i+1) n) (by norm_num : (0:ℝ)≤1/2)
      linarith only [hh]
    have hquot2 : x*expHorner x (i+1) n/((i+1:ℕ):ℝ)≤1 :=
      (div_le_one hdpos).mpr (le_trans hprod1 hd)
    simp only [roundedExpHorner,expHorner]
    exact ⟨by linarith only [hquot0],by linarith only [hquot1],by linarith only [hquot2]⟩

/-- The two roundings per Horner step contribute at most four units in total. -/
theorem roundedExpHorner_error {x : ℝ} (hx0 : 0≤x) (hx1 : x≤1/2) (P i n : ℕ) :
    |roundedExpHorner P x i n-expHorner x i n|≤4/(2:ℝ)^P := by
  have hu : (0:ℝ)≤1/(2:ℝ)^P := by positivity
  induction n generalizing i with
  | zero => simp [roundedExpHorner,expHorner]; positivity
  | succ n ih =>
    have hd : (1:ℝ)≤((i+1:ℕ):ℝ) := by exact_mod_cast (show 1≤ i+1 by omega)
    have hdpos : (0:ℝ)<((i+1:ℕ):ℝ) := by linarith
    have he : x*roundedExpHorner P x (i+1) n-x*expHorner x (i+1) n=
        x*(roundedExpHorner P x (i+1) n-expHorner x (i+1) n) := by ring
    have hprod : |x*roundedExpHorner P x (i+1) n-x*expHorner x (i+1) n|≤2/(2:ℝ)^P := by
      rw [he,abs_mul,abs_of_nonneg hx0]
      have hh := mul_le_mul hx1 (ih (i+1)) (abs_nonneg _) (by norm_num : (0:ℝ)≤1/2)
      convert hh using 1 <;> ring
    have hround := le_trans (abs_sub_le
      (dyadicFloor P (x*roundedExpHorner P x (i+1) n))
      (x*roundedExpHorner P x (i+1) n) (x*expHorner x (i+1) n))
      (add_le_add (dyadicFloor_error P _) hprod)
    have hquot : |dyadicFloor P (x*roundedExpHorner P x (i+1) n)/((i+1:ℕ):ℝ)-
        (x*expHorner x (i+1) n)/((i+1:ℕ):ℝ)|≤3/(2:ℝ)^P := by
      rw [← sub_div,abs_div,abs_of_pos hdpos]
      apply (div_le_iff₀ hdpos).mpr
      have hm := mul_le_mul_of_nonneg_left hd (show (0:ℝ)≤3/(2:ℝ)^P by positivity)
      simp only [div_eq_mul_inv] at hround hm ⊢
      linarith only [hround,hm]
    have hfinal := le_trans (abs_sub_le
      (dyadicFloor P (dyadicFloor P (x*roundedExpHorner P x (i+1) n)/((i+1:ℕ):ℝ)))
      (dyadicFloor P (x*roundedExpHorner P x (i+1) n)/((i+1:ℕ):ℝ))
      (x*expHorner x (i+1) n/((i+1:ℕ):ℝ)))
      (add_le_add (dyadicFloor_error P _) hquot)
    have he' : roundedExpHorner P x i (n+1)-expHorner x i (n+1)=
        dyadicFloor P (dyadicFloor P (x*roundedExpHorner P x (i+1) n)/((i+1:ℕ):ℝ))-
          x*expHorner x (i+1) n/((i+1:ℕ):ℝ) := by
      simp only [roundedExpHorner,expHorner]
      ring
    rw [he']
    simp only [div_eq_mul_inv] at hfinal ⊢
    linarith only [hfinal]

/-- At least `P+4` Horner steps give a nonnegative underestimate of the
exponential with absolute error at most five last-place units. -/
theorem roundedExpHorner_exp_error {x : ℝ} (hx0 : 0≤x) (hx1 : x≤1/2) (P : ℕ) :
    1≤roundedExpHorner P x 0 (P+4) ∧
    roundedExpHorner P x 0 (P+4)≤Real.exp x ∧
    |roundedExpHorner P x 0 (P+4)-Real.exp x|≤5/(2:ℝ)^P := by
  obtain ⟨hlo,hmid,_⟩ := expHorner_bounds hx0 hx1 P 0 (P+4)
  have hseries := Real.sum_le_exp_of_nonneg hx0 (P+4+1)
  have htail := exp_series_relative (show |x|≤1/2 by rwa [abs_of_nonneg hx0]) (P+3)
  have hexp : Real.exp x≤2 := by
    have hh := Real.abs_exp_sub_one_le (show |x|≤1 by rw [abs_of_nonneg hx0]; linarith)
    rw [abs_of_nonneg hx0] at hh
    have hh' := (abs_le.mp hh).2
    linarith only [hh',hx1]
  have htail' : |expHorner x 0 (P+4)-Real.exp x|≤1/(2:ℝ)^P := by
    rw [expHorner_series]
    have he : P+4+1=P+3+2 := by omega
    rw [he]
    have hh := le_trans htail (mul_le_mul_of_nonneg_left hexp (by positivity : (0:ℝ)≤1/(2:ℝ)^(P+3)))
    have hu : (0:ℝ)≤1/(2:ℝ)^P := by positivity
    simp only [pow_add] at hh
    norm_num only [show (2:ℝ)^3=8 by norm_num] at hh
    simp only [div_eq_mul_inv,mul_inv_rev] at hh hu ⊢
    nlinarith only [hh,hu]
  refine ⟨hlo,?_,?_⟩
  · change expSeries x (P+4+1)≤Real.exp x at hseries
    rw [← expHorner_series] at hseries
    exact le_trans hmid hseries
  · have hh := le_trans (abs_sub_le (roundedExpHorner P x 0 (P+4))
      (expHorner x 0 (P+4)) (Real.exp x))
      (add_le_add (roundedExpHorner_error hx0 hx1 P 0 (P+4)) htail')
    simp only [div_eq_mul_inv] at hh ⊢
    linarith only [hh]

end MinCostFlow.Num
