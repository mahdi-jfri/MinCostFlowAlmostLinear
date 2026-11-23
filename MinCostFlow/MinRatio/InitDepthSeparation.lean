module

public import Mathlib.Algebra.Polynomial.SumIteratedDerivative
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Size
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Separating logarithms from integer depth cutoffs

An exponential integral with integer endpoint coefficients bounds the
distance from an integer cutoff to the logarithm of a positive integer.
-/

public section
namespace MinCostFlow.MinRatio
open scoped Function

/-- A factorial bound for the integrand used to separate the logarithm
from integer thresholds. -/
theorem initDepthThreshold_factorial_bound (n : ℕ) :
    (n ^ 2) ^ (2 * n ^ 4) ≤ (2 * n ^ 4).factorial := by
  exact calc
    (n ^ 2) ^ (2 * n ^ 4) = (n ^ 4) ^ (n ^ 4) := by
      rw [pow_mul (n ^ 2) 2, ← pow_mul n 2 2]
    _ ≤ (n ^ 4).factorial * (n ^ 4 + 1) ^ (n ^ 4) :=
      (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.le_mul_of_pos_left _ (Nat.factorial_pos (n ^ 4)))
    _ ≤ (2 * n ^ 4).factorial := by
      rw [two_mul]
      exact Nat.factorial_mul_pow_le_factorial

/-- Completing the square bounds the polynomial factor in the exponential
integral for an integer threshold. -/
theorem initDepthThreshold_integrand_bound {n : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hxn : x ≤ n) :
    (x * ((n : ℝ) - x)) ^ (2 * n ^ 4) / ((2 * n ^ 4).factorial : ℝ) ≤
      1 / (4 : ℝ) ^ (2 * n ^ 4) := by
  have hquad : x * ((n : ℝ) - x) ≤ (n : ℝ) ^ 2 / 4 := by
    nlinarith [sq_nonneg (x - (n : ℝ) / 2)]
  have hpow := pow_le_pow_left₀ (mul_nonneg hx (sub_nonneg.mpr hxn)) hquad (2 * n ^ 4)
  have hfac : ((n : ℝ) ^ 2) ^ (2 * n ^ 4) ≤ ((2 * n ^ 4).factorial : ℝ) := by
    exact_mod_cast initDepthThreshold_factorial_bound n
  have hpos : (0 : ℝ) < ((2 * n ^ 4).factorial : ℝ) := by positivity
  rw [div_pow] at hpow
  apply (div_le_iff₀ hpos).2
  rw [one_div_mul_eq_div]
  exact hpow.trans (div_le_div_of_nonneg_right hfac (by positivity))

/-- The exponential integral for an integer threshold is bounded by the
interval length times the pointwise bound. -/
theorem initDepthThreshold_integral_le (n : ℕ) :
    (∫ x in (0 : ℝ)..(n : ℝ), Real.exp ((n : ℝ) - x) *
        ((x * ((n : ℝ) - x)) ^ (2 * n ^ 4) / ((2 * n ^ 4).factorial : ℝ))) ≤
      (n : ℝ) * (Real.exp n / (4 : ℝ) ^ (2 * n ^ 4)) := by
  let f : ℝ → ℝ := fun x => Real.exp ((n : ℝ) - x) *
    ((x * ((n : ℝ) - x)) ^ (2 * n ^ 4) / ((2 * n ^ 4).factorial : ℝ))
  let c : ℝ := Real.exp n / (4 : ℝ) ^ (2 * n ^ 4)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hg : Continuous (fun _ : ℝ => c) := continuous_const
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (Nat.cast_nonneg n)
    (hf.intervalIntegrable 0 n) (hg.intervalIntegrable 0 n) (fun x hx => show f x ≤ c from by
      have he : Real.exp ((n : ℝ) - x) ≤ Real.exp n :=
        Real.exp_le_exp.mpr (sub_le_self _ hx.1)
      unfold f c
      rw [div_eq_mul_inv (Real.exp n)]
      exact mul_le_mul he (by simpa only [one_div] using
        initDepthThreshold_integrand_bound hx.1 hx.2)
        (div_nonneg (pow_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) _) (by positivity)) (Real.exp_pos _).le)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h

private theorem initDepthThreshold_exp_le_four_pow (n : ℕ) :
    Real.exp (n : ℝ) ≤ (4 : ℝ) ^ n := by
  rw [show Real.exp (n : ℝ) = Real.exp 1 ^ n by
    simpa only [mul_one] using Real.exp_nat_mul 1 n]
  exact pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_one_lt_three.le.trans (by norm_num)) _

private theorem initDepthThreshold_upper_le_half {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * (Real.exp n / (4 : ℝ) ^ (2 * n ^ 4)) ≤ 1 / 2 := by
  have hnexp : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)) (n := n)).le
  have hdouble : 2 * (n : ℝ) ≤ (4 : ℝ) ^ n := by
    calc
      2 * (n : ℝ) ≤ 2 * (2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left hnexp (by norm_num)
      _ = (2 : ℝ) ^ (n + 1) := by rw [pow_succ, mul_comm]
      _ ≤ (2 : ℝ) ^ (2 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = (4 : ℝ) ^ n := by rw [pow_mul]; norm_num
  have hprod : 2 * ((n : ℝ) * Real.exp n) ≤ (4 : ℝ) ^ (2 * n ^ 4) := by
    calc
      2 * ((n : ℝ) * Real.exp n) = (2 * (n : ℝ)) * Real.exp n := by rw [mul_assoc]
      _ ≤ (4 : ℝ) ^ n * (4 : ℝ) ^ n :=
        mul_le_mul hdouble (initDepthThreshold_exp_le_four_pow n) (Real.exp_pos _).le (by positivity)
      _ = (4 : ℝ) ^ (2 * n) := by rw [two_mul, pow_add]
      _ ≤ (4 : ℝ) ^ (2 * n ^ 4) := pow_le_pow_right₀ (by norm_num)
        (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) _))
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  linarith only [hprod]

private theorem initDepthThreshold_upper_lt_one (n : ℕ) :
    (n : ℝ) * (Real.exp n / (4 : ℝ) ^ (2 * n ^ 4)) < 1 := by
  cases n with
  | zero => norm_num
  | succ n => exact (initDepthThreshold_upper_le_half n.succ_pos).trans_lt (by norm_num)

/-- The exponential integral is less than one. -/
theorem initDepthThreshold_integral_lt_one (n : ℕ) :
    (∫ x in (0 : ℝ)..(n : ℝ), Real.exp ((n : ℝ) - x) *
        ((x * ((n : ℝ) - x)) ^ (2 * n ^ 4) / ((2 * n ^ 4).factorial : ℝ))) < 1 :=
  (initDepthThreshold_integral_le n).trans_lt (initDepthThreshold_upper_lt_one n)

/-- On the interval from one quarter to one half of the threshold, both
polynomial factors are bounded away from zero. -/
theorem initDepthThreshold_integral_lower {n : ℕ} (hn : 0 < n) :
    (n : ℝ) / 4 * ((1 / 8 : ℝ) ^ (2 * n ^ 4) / ((2 * n ^ 4).factorial : ℝ)) ≤
      ∫ x in (0 : ℝ)..(n : ℝ), Real.exp ((n : ℝ) - x) *
        ((x * ((n : ℝ) - x)) ^ (2 * n ^ 4) / ((2 * n ^ 4).factorial : ℝ)) := by
  let f : ℝ → ℝ := fun x => Real.exp ((n : ℝ) - x) *
    ((x * ((n : ℝ) - x)) ^ (2 * n ^ 4) / ((2 * n ^ 4).factorial : ℝ))
  let c : ℝ := (1 / 8 : ℝ) ^ (2 * n ^ 4) / ((2 * n ^ 4).factorial : ℝ)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : (0 : ℝ) ≤ n / 4 := by positivity
  have hab : (n : ℝ) / 4 ≤ n / 2 := by linarith
  have hb : (n : ℝ) / 2 ≤ n := by linarith
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hg : Continuous (fun _ : ℝ => c) := continuous_const
  have hsub := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
    (hg.intervalIntegrable _ _) (hf.intervalIntegrable _ _) (fun x hx => show c ≤ f x from by
      have hx₁ : (1 : ℝ) / 4 ≤ x := (by linarith : (1 : ℝ) / 4 ≤ n / 4).trans hx.1
      have hx₂ : (1 : ℝ) / 2 ≤ n - x := by linarith [hx.2]
      have hbase : (1 / 8 : ℝ) ≤ x * ((n : ℝ) - x) := by
        simpa only [show (1 : ℝ) / 4 * (1 / 2) = 1 / 8 by norm_num] using
          mul_le_mul hx₁ hx₂ (by norm_num) (by linarith)
      have he : 1 ≤ Real.exp ((n : ℝ) - x) := Real.one_le_exp_iff.mpr (by linarith)
      unfold c f
      calc
        _ ≤ (x * ((n : ℝ) - x)) ^ (2 * n ^ 4) / ((2 * n ^ 4).factorial : ℝ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hbase _) (by positivity)
        _ ≤ _ := le_mul_of_one_le_left (by
          exact div_nonneg (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1 / 8).trans hbase) _) (by positivity)) he)
  have hfull := intervalIntegral.integral_mono_interval (μ := MeasureTheory.volume) ha hab hb
    (Filter.Eventually.of_forall fun x => show 0 ≤ f x from by
      unfold f
      rw [pow_mul]
      positivity) (hf.intervalIntegrable 0 n)
  rw [intervalIntegral.integral_const, smul_eq_mul,
    show (n : ℝ) / 2 - n / 4 = n / 4 by ring] at hsub
  exact hsub.trans hfull

/-- Adding successive derivatives of a polynomial gives the polynomial
factor of its exponential antiderivative. Integer coefficients are preserved. -/
private theorem initDepthThreshold_primitive (p : Polynomial ℤ) :
    Polynomial.sumIDeriv p - (Polynomial.sumIDeriv p).derivative = p := by
  nth_rw 1 [Polynomial.sumIDeriv_eq_self_add p]
  exact add_sub_cancel_right _ _

/-- A root of order at least `k` makes `k!` divide the value at that
root of the sum of the polynomial's successive derivatives. -/
theorem initDepthThreshold_endpoint_dvd (p : Polynomial ℤ) (k : ℕ) (z : ℤ)
    (hz : (Polynomial.X - Polynomial.C z) ^ k ∣ p) :
    (k.factorial : ℤ) ∣ (Polynomial.sumIDeriv p).eval z := by
  obtain ⟨q, _, hq⟩ := Polynomial.aeval_sumIDeriv ℤ p k
  have hm : (Polynomial.X - Polynomial.C z) ^ k ∣ p.map (algebraMap ℤ ℤ) := by
    simpa using hz
  refine ⟨q.eval z, ?_⟩
  simpa only [← Polynomial.eval_map_algebraMap, Polynomial.map_id, Algebra.algebraMap_self, nsmul_eq_mul] using hq z hm

/-- A coefficient bound controls the integral's endpoint coefficient at
zero. Each successive derivative contributes its constant term times
the corresponding factorial. -/
theorem initDepthThreshold_endpoint_zero_bound (p : Polynomial ℤ) {d : ℕ} {B : ℝ}
    (hd : p.natDegree ≤ d) (hB : ∀ i ≤ d, |(p.coeff i : ℝ)| ≤ B) :
    |(((Polynomial.sumIDeriv p).eval 0 : ℤ) : ℝ)| ≤ (d + 1 : ℝ) * d.factorial * B := by
  classical
  rw [Polynomial.sumIDeriv_apply_of_le hd, Polynomial.eval_finsetSum, Int.cast_sum]
  have hterm (i : ℕ) (hi : i ∈ Finset.range (d + 1)) :
      |(((Polynomial.derivative^[i] p).eval 0 : ℤ) : ℝ)| ≤ (d.factorial : ℝ) * B := by
    have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, zero_add,
      Nat.descFactorial_self, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul (by exact_mod_cast Nat.factorial_le hid) (hB i hid)
      (abs_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ i ∈ Finset.range (d + 1), |(((Polynomial.derivative^[i] p).eval 0 : ℤ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (d + 1), (d.factorial : ℝ) * B :=
      Finset.sum_le_sum hterm
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                            Nat.cast_add, Nat.cast_one]; ring

/-- Multiplying by `C n - X` increases a uniform coefficient bound
by at most `n + 1`. -/
theorem initDepthThreshold_linear_coeff_bound (n k i : ℕ) :
    |((((Polynomial.C (n : ℤ) - Polynomial.X) ^ k).coeff i : ℤ) : ℝ)| ≤
      ((n : ℝ) + 1) ^ k := by
  induction k generalizing i with
  | zero =>
    simp only [pow_zero, Polynomial.coeff_one]
    split <;> norm_num
  | succ k ih =>
    rw [pow_succ', sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Int.cast_sub, Int.cast_mul, Int.cast_natCast, pow_succ]
    have hshift :
        |(((Polynomial.X * (Polynomial.C (n : ℤ) - Polynomial.X) ^ k).coeff i : ℤ) : ℝ)|
          ≤ ((n : ℝ) + 1) ^ k := by
      cases i with
      | zero => simp only [Polynomial.coeff_X_mul_zero, Int.cast_zero, abs_zero]; positivity
      | succ i => rw [Polynomial.coeff_X_mul]; exact ih i
    refine (abs_sub_le _ 0 _).trans ?_
    rw [sub_zero, zero_sub, abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      _ ≤ (n : ℝ) * ((n : ℝ) + 1) ^ k + ((n : ℝ) + 1) ^ k :=
        add_le_add (mul_le_mul_of_nonneg_left (ih i) (Nat.cast_nonneg _)) hshift
      _ = _ := by ring

/-- Integration gives a difference of integer multiples of the threshold
exponential and of one. -/
theorem initDepthThreshold_integral_endpoints (n : ℕ) (p : Polynomial ℤ) :
    (∫ x in (0 : ℝ)..(n : ℝ),
      Real.exp ((n : ℝ) - x) * (p.map (Int.castRingHom ℝ)).eval x) =
        ((Polynomial.sumIDeriv p).eval 0 : ℤ) * Real.exp n -
          ((Polynomial.sumIDeriv p).eval n : ℤ) := by
  let q := Polynomial.sumIDeriv p
  have hq := initDepthThreshold_primitive p
  let f := Int.castRingHom ℝ
  have hqR : q.map f - (q.map f).derivative = p.map f := by
    rw [Polynomial.derivative_map, ← Polynomial.map_sub, hq]
  have hd (x : ℝ) : HasDerivAt
      (fun y => -(Real.exp ((n : ℝ) - y) * (q.map f).eval y))
      (Real.exp ((n : ℝ) - x) * (p.map f).eval x) x := by
    have he := ((hasDerivAt_const x (n : ℝ)).sub (hasDerivAt_id x)).exp
    have hprod := (he.mul ((q.map f).hasDerivAt x)).neg
    convert hprod using 1
    · rfl
    have hx := congrArg (Polynomial.eval x) hqR
    simp only [Polynomial.eval_sub] at hx
    rw [← hx]
    simp only [Pi.sub_apply, id_eq]
    ring
  have hc : Continuous (fun x : ℝ => Real.exp ((n : ℝ) - x) * (p.map f).eval x) := by
    exact (Real.continuous_exp.comp (continuous_const.sub continuous_id)).mul
      (continuous_iff_continuousAt.mpr fun x => ((p.map f).hasDerivAt x).continuousAt)
  change _ = (q.eval 0 : ℤ) * Real.exp n - (q.eval n : ℤ)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hc.intervalIntegrable _ _), sub_self, Real.exp_zero, one_mul, sub_zero]
  have hEval (z : ℤ) : (q.map f).eval (z : ℝ) = ((q.eval z : ℤ) : ℝ) := by
    exact (Polynomial.eval_map_apply (p := q) f z).trans rfl
  rw [show (n : ℝ) = ((n : ℤ) : ℝ) by simp, hEval, show (0 : ℝ) = ((0 : ℤ) : ℝ) by simp, hEval]
  push_cast
  ring

/-- Dividing the threshold integrand by its factorial still gives an
integer linear combination of the threshold exponential and one. -/
theorem initDepthThreshold_integral_normalized (n : ℕ) :
    ∃ a b : ℤ,
      (∫ x in (0 : ℝ)..(n : ℝ), Real.exp ((n : ℝ) - x) *
        ((x * ((n : ℝ) - x)) ^ (2 * n ^ 4) / ((2 * n ^ 4).factorial : ℝ))) =
        (a : ℝ) * Real.exp n - b ∧
      |(a : ℝ)| ≤ ((4 * n ^ 4 : ℕ) + 1 : ℝ) * ((4 * n ^ 4).factorial : ℝ) *
        ((n : ℝ) + 1) ^ (2 * n ^ 4) := by
  let k := 2 * n ^ 4
  let p : Polynomial ℤ := (Polynomial.X * (Polynomial.C (n : ℤ) - Polynomial.X)) ^ k
  obtain ⟨a, ha⟩ := initDepthThreshold_endpoint_dvd p k 0 (by
    simp only [Polynomial.C_0, sub_zero, p, mul_pow]
    exact dvd_mul_right _ _)
  obtain ⟨b, hb⟩ := initDepthThreshold_endpoint_dvd p k n (by
    unfold p
    rw [show Polynomial.C (n : ℤ) - Polynomial.X =
      -(Polynomial.X - Polynomial.C (n : ℤ)) by abel, mul_pow, neg_pow]
    exact (dvd_mul_left _ _).trans (dvd_mul_left _ _))
  have hp (x : ℝ) : (p.map (Int.castRingHom ℝ)).eval x = (x * ((n : ℝ) - x)) ^ k := by
    simp [p]
  have h := initDepthThreshold_integral_endpoints n p
  simp_rw [hp] at h
  refine ⟨a, b, ?_, ?_⟩
  · change (∫ x in (0 : ℝ)..(n : ℝ), Real.exp ((n : ℝ) - x) *
      ((x * ((n : ℝ) - x)) ^ k / (k.factorial : ℝ))) = _
    simp_rw [← mul_div_assoc]
    rw [intervalIntegral.integral_div, h, ha, hb]
    push_cast
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  · have hdegree : p.natDegree ≤ 2 * k := by
      have hlin : (Polynomial.C (n : ℤ) - Polynomial.X).natDegree ≤ 1 :=
        (Polynomial.natDegree_sub_le _ _).trans (by simp)
      have hmul : (Polynomial.X * (Polynomial.C (n : ℤ) - Polynomial.X)).natDegree ≤ 2 :=
        Polynomial.natDegree_mul_le.trans (by
          rw [Polynomial.natDegree_X]
          exact Nat.add_le_add_left hlin 1)
      unfold p
      exact Polynomial.natDegree_pow_le.trans ((Nat.mul_le_mul_left k hmul).trans_eq (Nat.mul_comm k 2))
    have hcoeff (i : ℕ) :
        |((p.coeff i : ℤ) : ℝ)| ≤ ((n : ℝ) + 1) ^ k := by
      rw [show p = Polynomial.X ^ k * (Polynomial.C (n : ℤ) - Polynomial.X) ^ k by
        exact mul_pow _ _ _, Polynomial.coeff_X_pow_mul']
      split
      · exact initDepthThreshold_linear_coeff_bound n k _
      · simp only [Int.cast_zero, abs_zero]; positivity
    have hbound := initDepthThreshold_endpoint_zero_bound p hdegree (fun i _ => hcoeff i)
    rw [ha, Int.cast_mul, Int.cast_natCast, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)] at hbound
    have hk : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
    have h := (le_mul_of_one_le_left (abs_nonneg (a : ℝ)) hk).trans hbound
    simpa only [k, ← Nat.mul_assoc] using h

/-- The integer endpoint identity separates the exponential of a positive
integer threshold from every integer. The coefficient bound makes the
separation uniform in the integer being compared. -/
theorem initDepthThreshold_exp_separation {n : ℕ} (hn : 0 < n) (z : ℤ) :
      min ((n : ℝ) / 4 * ((1 / 8 : ℝ) ^ (2 * n ^ 4) / ((2 * n ^ 4).factorial : ℝ)))
          (1 - (n : ℝ) * (Real.exp n / (4 : ℝ) ^ (2 * n ^ 4))) ≤
        (((4 * n ^ 4 : ℕ) + 1 : ℝ) * ((4 * n ^ 4).factorial : ℝ) *
          ((n : ℝ) + 1) ^ (2 * n ^ 4)) * |Real.exp n - z| := by
  obtain ⟨a, b, heq, ha⟩ := initDepthThreshold_integral_normalized n
  have hlo := initDepthThreshold_integral_lower hn
  have hhi := initDepthThreshold_integral_le n
  rw [heq] at hlo hhi
  refine le_trans ?_ (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
  rw [← abs_mul, mul_sub]
  by_cases hz : a * z ≤ b
  · have hz' : (a : ℝ) * (z : ℝ) ≤ b := by exact_mod_cast hz
    exact (min_le_left _ _).trans (hlo.trans ((sub_le_sub_left hz' _).trans (le_abs_self _)))
  · have hzInt : b + 1 ≤ a * z := by omega
    have hz' : (b : ℝ) + 1 ≤ (a : ℝ) * (z : ℝ) := by exact_mod_cast hzInt
    exact (min_le_right _ _).trans (show _ ≤ _ from
      (show _ ≤ -((a : ℝ) * Real.exp n - (a : ℝ) * (z : ℝ)) by linarith).trans
        (neg_le_abs _))

private theorem initDepthThreshold_exp_sub_le (x y : ℝ) :
    Real.exp y - Real.exp x ≤ Real.exp y * (y - x) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x - y))
    (Real.exp_pos y).le
  rw [← Real.exp_add, show y + (x - y) = x by ring] at h
  linarith only [h, show Real.exp y * (x - y + 1) =
    Real.exp y - Real.exp y * (y - x) by ring]

/-- The upper of the two exponentials bounds the rate at which their
difference grows with the difference of their arguments. -/
theorem initDepthThreshold_abs_exp_sub_le (x y : ℝ) :
    |Real.exp x - Real.exp y| ≤ max (Real.exp x) (Real.exp y) * |x - y| := by
  rcases le_total x y with h | h
  · have he := Real.exp_le_exp.mpr h
    rw [max_eq_right he, abs_of_nonpos (sub_nonpos.mpr he),
      abs_of_nonpos (sub_nonpos.mpr h), neg_sub, neg_sub]
    exact initDepthThreshold_exp_sub_le x y
  · have he := Real.exp_le_exp.mpr h
    rw [max_eq_left he, abs_of_nonneg (sub_nonneg.mpr he),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact initDepthThreshold_exp_sub_le y x

/-- The exponential separation bound gives a logarithm separation bound
after multiplying the denominator by the larger exponential. -/
theorem initDepthThreshold_log_separation {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    min ((n : ℝ) / 4 * ((1 / 8 : ℝ) ^ (2 * n ^ 4) / ((2 * n ^ 4).factorial : ℝ)))
        (1 - (n : ℝ) * (Real.exp n / (4 : ℝ) ^ (2 * n ^ 4))) ≤
      (((4 * n ^ 4 : ℕ) + 1 : ℝ) * ((4 * n ^ 4).factorial : ℝ) *
        ((n : ℝ) + 1) ^ (2 * n ^ 4)) *
      (max (Real.exp n) (m : ℝ) * |(n : ℝ) - Real.log m|) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have he := initDepthThreshold_exp_separation hn (m : ℤ)
  simp only [Int.cast_natCast] at he
  have hlog := initDepthThreshold_abs_exp_sub_le (n : ℝ) (Real.log m)
  rw [Real.exp_log hm'] at hlog
  exact he.trans (mul_le_mul_of_nonneg_left hlog (by positivity))

/-- The numerator of the separation estimate is at least an explicit
dyadic value. The factorial is bounded by a power of two using its
number of factors and an upper bound on each factor. -/
theorem initDepthThreshold_dyadic_numerator {n : ℕ} (hn : 0 < n) :
    1 / (2 : ℝ) ^ (2 + 3 * (2 * n ^ 4) + (2 * n ^ 4) ^ 2) ≤
      min ((n : ℝ) / 4 * ((1 / 8 : ℝ) ^ (2 * n ^ 4) / ((2 * n ^ 4).factorial : ℝ)))
        (1 - (n : ℝ) * (Real.exp n / (4 : ℝ) ^ (2 * n ^ 4))) := by
  let k := 2 * n ^ 4
  have hk : (k.factorial : ℝ) ≤ (2 : ℝ) ^ (k ^ 2) := by
    have h : k.factorial ≤ (2 : ℕ) ^ (k ^ 2) := by
      rw [pow_two k, pow_mul]
      exact (Nat.factorial_le_pow _).trans
        (Nat.pow_le_pow_left (Nat.lt_pow_self (by decide : 1 < (2 : ℕ))).le _)
    exact_mod_cast h
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply le_min
  · change 1 / (2 : ℝ) ^ (2 + 3 * k + k ^ 2) ≤ (n : ℝ) / 4 * ((1 / 8 : ℝ) ^ k / k.factorial)
    rw [pow_add, pow_add, pow_mul (2 : ℝ) 3, div_pow, one_pow]
    norm_num
    have hf : (0 : ℝ) < k.factorial := by positivity
    have h8 : (0 : ℝ) < (8 : ℝ) ^ k := by positivity
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (k ^ 2) := by positivity
    field_simp
    have hprod : (k.factorial : ℝ) ≤ (n : ℝ) * 2 ^ (k ^ 2) :=
      hk.trans (le_mul_of_one_le_left h2.le hn')
    simpa only [mul_comm (n : ℝ)] using hprod
  · have hhalf := initDepthThreshold_upper_le_half hn
    have hexp : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (2 + 3 * k + k ^ 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h : 1 / (2 : ℝ) ^ (2 + 3 * k + k ^ 2) ≤ 1 / 2 := by
      simpa only [pow_one] using one_div_le_one_div_of_le (by positivity) hexp
    have hmargin : (1 / 2 : ℝ) ≤ 1 - (n : ℝ) * (Real.exp n / (4 : ℝ) ^ (2 * n ^ 4)) := by
      linarith only [hhalf]
    exact h.trans hmargin

/-- A polynomial in the integer cutoff and the bit length bounds the
number of bits needed to separate the logarithm from that cutoff. -/
theorem initDepthThreshold_dyadic_log_gap {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    let k := 2 * n ^ 4
    let d := 4 * n ^ 4
    1 / (2 : ℝ) ^ (2 + 3 * k + k ^ 2 + (d + d ^ 2 + n * k + (2 * n + m.size))) ≤
      |(n : ℝ) - Real.log m| := by
  let k := 2 * n ^ 4
  let d := 4 * n ^ 4
  have hsucc (j : ℕ) : (j : ℝ) + 1 ≤ (2 : ℝ) ^ j := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)) (n := j))
  have hfac : (d.factorial : ℝ) ≤ (2 : ℝ) ^ (d ^ 2) := by
    have h : d.factorial ≤ (2 : ℕ) ^ (d ^ 2) := by
      rw [pow_two d, pow_mul]
      exact (Nat.factorial_le_pow _).trans
        (Nat.pow_le_pow_left (Nat.lt_pow_self (by decide : 1 < (2 : ℕ))).le _)
    exact_mod_cast h
  have hp : ((n : ℝ) + 1) ^ k ≤ (2 : ℝ) ^ (n * k) := by
    rw [pow_mul (2 : ℝ) n k]
    exact pow_le_pow_left₀ (by positivity) (hsucc n) _
  have hmax : max (Real.exp n) (m : ℝ) ≤ (2 : ℝ) ^ (2 * n + m.size) := by
    apply max_le
    · have he : Real.exp n ≤ (2 : ℝ) ^ (2 * n) := by
        rw [pow_mul]
        norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
        exact initDepthThreshold_exp_le_four_pow n
      exact he.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _))
    · have hm' : (m : ℝ) ≤ (2 : ℝ) ^ m.size := by exact_mod_cast (Nat.lt_size_self m).le
      exact hm'.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_add_left _ _))
  have hcoef : ((d : ℝ) + 1) * d.factorial * ((n : ℝ) + 1) ^ k ≤
      (2 : ℝ) ^ (d + d ^ 2 + n * k) := by
    rw [pow_add, pow_add]
    exact mul_le_mul (mul_le_mul (hsucc d) hfac (by positivity) (by positivity))
      hp (by positivity) (by positivity)
  have h := (initDepthThreshold_dyadic_numerator hn).trans
    (initDepthThreshold_log_separation hn hm)
  change 1 / (2 : ℝ) ^ (2 + 3 * k + k ^ 2) ≤
    (((d : ℝ) + 1) * d.factorial * ((n : ℝ) + 1) ^ k) *
      (max (Real.exp n) (m : ℝ) * |(n : ℝ) - Real.log m|) at h
  rw [← mul_assoc (((d : ℝ) + 1) * d.factorial * ((n : ℝ) + 1) ^ k)] at h
  have hbound := mul_le_mul hcoef hmax (by positivity) (by positivity)
  have hmul := h.trans (mul_le_mul_of_nonneg_right hbound (abs_nonneg _))
  change 1 / (2 : ℝ) ^ (2 + 3 * k + k ^ 2 + (d + d ^ 2 + n * k + (2 * n + m.size))) ≤ _
  rw [pow_add, ← div_div, div_le_iff₀ (by positivity),
    pow_add (2 : ℝ) (d + d ^ 2 + n * k), mul_comm |(n : ℝ) - Real.log m|]
  exact hmul

/-- A positive integer threshold cannot equal the logarithm of a positive
integer input. -/
theorem initDepthThreshold_log_ne {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    Real.log (m : ℝ) ≠ n := by
  intro heq
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have he : Real.exp (n : ℝ) = m := by rw [← heq, Real.exp_log hm']
  have hs := initDepthThreshold_exp_separation hn (m : ℤ)
  push_cast at hs
  rw [he, sub_self, abs_zero, mul_zero] at hs
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlo : (0 : ℝ) <
      (n : ℝ) / 4 * ((1 / 8 : ℝ) ^ (2 * n ^ 4) / ((2 * n ^ 4).factorial : ℝ)) := by
    positivity
  have hhi := sub_pos.mpr (initDepthThreshold_upper_lt_one n)
  rw [← he] at hs
  exact (lt_min hlo hhi).not_ge hs

/-- A dyadic enclosure can separate the logarithm from both of its
integer cutoffs. -/
theorem initDepthThreshold_exists_accuracy {m lower upper : ℕ} (hm : 0 < m)
    (hu : 0 < upper) (hlo : (lower : ℝ) < Real.log (m : ℝ))
    (hhi : Real.log (m : ℝ) ≤ upper) :
    ∃ accuracy : ℕ,
      (lower : ℝ) + 2 / (2 : ℝ) ^ accuracy < Real.log (m : ℝ) ∧
      Real.log (m : ℝ) + 2 / (2 : ℝ) ^ accuracy ≤ upper := by
  have hstrict := lt_of_le_of_ne hhi (initDepthThreshold_log_ne hu hm)
  have hgap : 0 < min (Real.log (m : ℝ) - lower) ((upper : ℝ) - Real.log (m : ℝ)) :=
    lt_min (sub_pos.mpr hlo) (sub_pos.mpr hstrict)
  obtain ⟨accuracy, ha⟩ := exists_pow_lt_of_lt_one (half_pos hgap)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have herror : 2 / (2 : ℝ) ^ accuracy <
      min (Real.log (m : ℝ) - lower) ((upper : ℝ) - Real.log (m : ℝ)) := by
    rw [div_pow, one_pow] at ha
    rw [div_eq_mul_one_div]
    linarith
  exact ⟨accuracy, by linarith [herror.trans_le (min_le_left _ _)],
    by linarith [herror.trans_le (min_le_right _ _)]⟩

/-- A single accuracy separates both positive integer cutoffs. It suffices
to use the exponent for the larger cutoff plus two guard bits. -/
theorem initDepthThreshold_gaps_of_accuracy {m lower upper accuracy : ℕ}
    (hm : 0 < m) (hl : 0 < lower) (hlu : lower ≤ upper)
    (hlo : (lower : ℝ) < Real.log (m : ℝ)) (hhi : Real.log (m : ℝ) ≤ upper)
    (hacc : let k := 2 * upper ^ 4
      let d := 4 * upper ^ 4
      2 + 3 * k + k ^ 2 + (d + d ^ 2 + upper * k + (2 * upper + m.size)) + 2 ≤ accuracy) :
    (lower : ℝ) + 2 / (2 : ℝ) ^ accuracy < Real.log (m : ℝ) ∧
      Real.log (m : ℝ) + 2 / (2 : ℝ) ^ accuracy ≤ upper := by
  let bits (n : ℕ) := 2 + 3 * (2 * n ^ 4) + (2 * n ^ 4) ^ 2 +
    (4 * n ^ 4 + (4 * n ^ 4) ^ 2 + n * (2 * n ^ 4) + (2 * n + m.size))
  have hb : bits lower ≤ bits upper := by
    dsimp [bits]
    gcongr
  have herr {n : ℕ} (hbits : bits n ≤ bits upper) :
      2 / (2 : ℝ) ^ accuracy < 1 / (2 : ℝ) ^ bits n := by
    have ha : bits n + 2 ≤ accuracy := Nat.add_le_add_right hbits 2 |>.trans hacc
    have hp : (2 : ℝ) ^ (bits n + 2) ≤ (2 : ℝ) ^ accuracy :=
      pow_le_pow_right₀ (by norm_num) ha
    refine (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (by positivity) hp).trans_lt ?_
    rw [pow_add]
    norm_num
    have hpos : (0 : ℝ) < (2 : ℝ) ^ bits n := by positivity
    field_simp
    linarith
  have hlow := initDepthThreshold_dyadic_log_gap hl hm
  have hu : 0 < upper := hl.trans_le hlu
  have hupp := initDepthThreshold_dyadic_log_gap hu hm
  rw [abs_of_nonpos (sub_nonpos.mpr hlo.le)] at hlow
  rw [abs_of_nonneg (sub_nonneg.mpr hhi)] at hupp
  exact ⟨by linarith only [(herr hb).trans_le hlow],
    by linarith only [(herr le_rfl).trans_le hupp]⟩

/-- Any bound on the upper cutoff gives a simple precision bound for
both comparisons. -/
theorem initDepthThreshold_gaps_of_cutoff_bound {m lower upper bound accuracy : ℕ}
    (hm : 0 < m) (hl : 0 < lower) (hlu : lower ≤ upper) (hub : upper ≤ bound)
    (hlo : (lower : ℝ) < Real.log (m : ℝ)) (hhi : Real.log (m : ℝ) ≤ upper)
    (hacc : 38 * bound ^ 8 + m.size ≤ accuracy) :
    (lower : ℝ) + 2 / (2 : ℝ) ^ accuracy < Real.log (m : ℝ) ∧
      Real.log (m : ℝ) + 2 / (2 : ℝ) ^ accuracy ≤ upper := by
  apply initDepthThreshold_gaps_of_accuracy hm hl hlu hlo hhi
  dsimp only
  have hb : 1 ≤ bound := hl.trans_le (hlu.trans hub)
  have hpow {e : ℕ} (he : e ≤ 8) : upper ^ e ≤ bound ^ 8 :=
    (Nat.pow_le_pow_left hub e).trans (Nat.pow_le_pow_right hb he)
  have h₀ : 1 ≤ bound ^ 8 := Nat.one_le_pow _ _ hb
  have h₁ : upper ≤ bound ^ 8 := by simpa only [pow_one] using hpow (e := 1) (by decide)
  have h₄ := hpow (e := 4) (by decide)
  have h₅ := hpow (e := 5) (by decide)
  have h₈ := hpow (e := 8) le_rfl
  calc
    _ = 4 + 10 * upper ^ 4 + 20 * upper ^ 8 + 2 * upper ^ 5 + 2 * upper + m.size := by ring
    _ ≤ 38 * bound ^ 8 + m.size := by omega
    _ ≤ accuracy := hacc

end MinCostFlow.MinRatio
