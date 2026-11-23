module

public import MinCostFlow.Final.TimeExponent
import Mathlib.Tactic

/-!
# Absorbing products into the subpolynomial time factor

The time bound uses shifted edge counts and binary ceiling logarithms.
The lemmas here bound those expressions using the same exponential
factor as Theorem 5.1, with explicit coefficients.
-/

public noncomputable section
namespace MinCostFlow.Final
open Chain

/-- The exponent in the Theorem 5.1 time factor, before multiplying by its constant. -/
def scalingLogShape (m : ℕ) : ℝ :=
  (Real.log ((m:ℝ)+2))^(47/48:ℝ) * Real.log (Real.log ((m:ℝ)+2)+2)

theorem scalingLogShape_nonneg (m : ℕ) : 0 ≤ scalingLogShape m := by
  unfold scalingLogShape
  have h := Real.log_nonneg (show (1:ℝ) ≤ (m:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) m])
  exact mul_nonneg (Real.rpow_nonneg h _) (Real.log_nonneg (by linarith))

theorem scalingTimeFactor_eq (B : ℝ) (m : ℕ) :
    alg2TimeFactor B (47/48) m = Real.exp (B*scalingLogShape m) := by
  unfold alg2TimeFactor scalingLogShape
  rw [mul_assoc]

theorem scalingTimeFactor_one_le {B : ℝ} (hB : 0 ≤ B) (m : ℕ) :
    1 ≤ alg2TimeFactor B (47/48) m := by
  rw [scalingTimeFactor_eq, ←Real.exp_zero]
  exact Real.exp_le_exp.mpr (mul_nonneg hB (scalingLogShape_nonneg m))

theorem scalingTimeFactor_mono {B B' : ℝ} (hB : B ≤ B') (m : ℕ) :
    alg2TimeFactor B (47/48) m ≤ alg2TimeFactor B' (47/48) m := by
  rw [scalingTimeFactor_eq, scalingTimeFactor_eq, Real.exp_le_exp]
  exact mul_le_mul_of_nonneg_right hB (scalingLogShape_nonneg m)

theorem scalingTimeFactor_pow (B : ℝ) (q m : ℕ) :
    alg2TimeFactor B (47/48) m ^ q = alg2TimeFactor (q*B) (47/48) m := by
  rw [scalingTimeFactor_eq, scalingTimeFactor_eq, ←Real.exp_nat_mul, mul_assoc]

/-- A power of the padded logarithm is absorbed by increasing the exponent constant. -/
theorem paddedLog_pow_le_timeFactor (q m : ℕ) :
    (Real.log ((m:ℝ)+2)+2)^q ≤
      alg2TimeFactor (q / (Real.log 2)^(47/48:ℝ)) (47/48) m := by
  let x := Real.log ((m:ℝ)+2)
  have hx : Real.log 2 ≤ x := Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) m])
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (Real.log 2)^(47/48:ℝ) ≤ x^(47/48:ℝ) :=
    Real.rpow_le_rpow hlog.le hx (by norm_num)
  have hd : 0 < (Real.log 2)^(47/48:ℝ) := Real.rpow_pos_of_pos hlog _
  have hxp : 0 < x+2 := by linarith
  have hl : 0 ≤ Real.log (x+2) := Real.log_nonneg (by linarith)
  have hc : (q:ℝ) ≤ (q:ℝ) / (Real.log 2)^(47/48:ℝ) * x^(47/48:ℝ) := by
    have hratio : 1 ≤ x^(47/48:ℝ) / (Real.log 2)^(47/48:ℝ) := (le_div_iff₀ hd).mpr (by simpa using hpow)
    calc
      _ ≤ (q:ℝ) * (x^(47/48:ℝ) / (Real.log 2)^(47/48:ℝ)) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg q)
      _ = _ := by ring
  rw [alg2TimeFactor, ←Real.exp_log hxp, ←Real.exp_nat_mul, Real.exp_le_exp]
  simpa only [Real.log_exp] using mul_le_mul_of_nonneg_right hc hl

/-- A logarithm ratio used to bound a constant rescaling of the edge count. -/
def logScale (A : ℝ) : ℝ := 1 + Real.log A / Real.log 2

theorem logScale_one_le {A : ℝ} (hA : 1 ≤ A) : 1 ≤ logScale A :=
  le_add_of_nonneg_right (div_nonneg (Real.log_nonneg hA) (Real.log_nonneg (by norm_num)))

/-- The shifted logarithm of a smaller input is at most a constant times
the shifted logarithm of the original edge count. -/
theorem log_le_scaled {A : ℝ} (hA : 1 ≤ A) {x y : ℝ} (hx : 2 ≤ x) (hy : 0 < y)
    (hxy : y ≤ A*x) : Real.log y ≤ logScale A*Real.log x := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (show (0:ℝ)<2 by norm_num) hx
  have hmul := mul_le_mul_of_nonneg_left hlog (div_nonneg (Real.log_nonneg hA) hl.le)
  calc
    _ ≤ Real.log (A*x) := Real.log_le_log hy hxy
    _ = Real.log A + Real.log x := Real.log_mul (by linarith) (by linarith)
    _ ≤ _ := by
      unfold logScale
      rw [add_mul, one_mul]
      rw [div_mul_cancel₀ _ hl.ne'] at hmul
      linarith

/-- Rescaling the edge count only changes the constant in the
subpolynomial time factor. -/
theorem scalingTimeFactor_rescale {A B : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (m i : ℕ)
    (hi : (i:ℝ)+2 ≤ A*((m:ℝ)+2)) :
    alg2TimeFactor B (47/48) i ≤
      alg2TimeFactor (B*(logScale A)^(47/48:ℝ)*logScale (logScale A)) (47/48) m := by
  let x := Real.log ((m:ℝ)+2)
  let y := Real.log ((i:ℝ)+2)
  let a := logScale A
  have ha : 1 ≤ a := logScale_one_le hA
  have hx : 0 ≤ x := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) m])
  have hy : 0 ≤ y := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) i])
  have hyx : y ≤ a*x := log_le_scaled hA
    (by linarith [Nat.cast_nonneg (α:=ℝ) m]) (by positivity) hi
  have hy2 : y+2 ≤ a*(x+2) := by rw [mul_add]; linarith
  have hLog : Real.log (y+2) ≤ logScale a * Real.log (x+2) :=
    log_le_scaled ha (by linarith) (by linarith) hy2
  have hPow : y^(47/48:ℝ) ≤ a^(47/48:ℝ)*x^(47/48:ℝ) := by
    rw [←Real.mul_rpow (by linarith : 0≤a) hx]
    exact Real.rpow_le_rpow hy hyx (by norm_num)
  rw [alg2TimeFactor, alg2TimeFactor, Real.exp_le_exp]
  calc
    B*y^(47/48:ℝ)*Real.log (y+2) ≤
        (B*(a^(47/48:ℝ)*x^(47/48:ℝ)))*(logScale a * Real.log (x+2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hPow hB) hLog
        (Real.log_nonneg (by linarith)) (by positivity)
    _ = _ := by ring

end MinCostFlow.Final
