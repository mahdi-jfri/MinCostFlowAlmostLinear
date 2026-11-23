module

public import MinCostFlow.Num.RoundedExponentialFacts
public import MinCostFlow.Num.SquaringFacts
import MinCostFlow.Num.LogarithmRangeFacts
import Mathlib.Tactic

/-!
# Positive exponential by halving and squaring

Reduce a nonnegative argument bounded by `B` by `B+2` binary shifts. Evaluate
the rounded Taylor series there, then square `B+2` times. The result remains
between one and the true exponential. Including argument rounding, its relative
error is at most `8*2^(B+2-P)`.
-/

@[expose] public section
namespace MinCostFlow.Num

/-- Complete rounded real calculation for a nonnegative argument. -/
noncomputable def positiveExpRounded (P B : ℕ) (y : ℝ) : ℝ :=
  roundedSquares P (roundedExpHorner P (dyadicFloor P (y/(2:ℝ)^(B+2))) 0 (P+4)) (B+2)

/-- Halving `B+2` times reduces every argument in `[0,B]` to `[0,1/2]`. -/
theorem positive_exp_reduced_bounds {y : ℝ} {B : ℕ} (hy0 : 0≤y) (hyB : y≤B) (P : ℕ) :
    0≤y/(2:ℝ)^(B+2) ∧ y/(2:ℝ)^(B+2)≤1/2 ∧
    0≤dyadicFloor P (y/(2:ℝ)^(B+2)) ∧ dyadicFloor P (y/(2:ℝ)^(B+2))≤1/2 := by
  have h0 : 0≤y/(2:ℝ)^(B+2) := div_nonneg hy0 (by positivity)
  have he : (B:ℝ)+1≤(2:ℝ)^B := by exact_mod_cast log_range_linear_bound B
  have h1 : y/(2:ℝ)^(B+2)≤1/2 := by
    apply (div_le_iff₀ (show (0:ℝ)<(2:ℝ)^(B+2) by positivity)).mpr
    rw [pow_add]
    norm_num only [show (2:ℝ)^2=4 by norm_num]
    nlinarith only [he,hyB,hy0]
  exact ⟨h0,h1,dyadicFloor_nonneg h0,le_trans (dyadicFloor_le P _) h1⟩

/-- Undoing the exact argument halving by squaring recovers `exp y`. -/
theorem exp_halving_power (y : ℝ) (k : ℕ) :
    (Real.exp (y/(2:ℝ)^k))^(2^k)=Real.exp y := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- The rounded positive exponential is always an underestimate at least one. -/
theorem positiveExpRounded_bounds {y : ℝ} {B : ℕ} (hy0 : 0≤y) (hyB : y≤B) (P : ℕ) :
    1≤positiveExpRounded P B y ∧ positiveExpRounded P B y≤Real.exp y := by
  obtain ⟨hv0,_,hr0,hr1⟩ := positive_exp_reduced_bounds hy0 hyB P
  obtain ⟨ha0,ha1,_⟩ := roundedExpHorner_exp_error hr0 hr1 P
  have hT : Real.exp (dyadicFloor P (y/(2:ℝ)^(B+2)))≤Real.exp (y/(2:ℝ)^(B+2)) :=
    Real.exp_le_exp.mpr (dyadicFloor_le P _)
  have hb := roundedSquares_bounds ha0 (le_trans ha1 hT) P (B+2)
  rw [exp_halving_power] at hb
  exact hb

/-- Every rounding in positive exponential evaluation, including the initial
argument shift, contributes at most `8*2^(B+2)/2^P` relative error. -/
theorem positiveExpRounded_error {y : ℝ} {B : ℕ} (hy0 : 0≤y) (hyB : y≤B) (P : ℕ) :
    |positiveExpRounded P B y-Real.exp y|≤
      (8*(2:ℝ)^(B+2)/(2:ℝ)^P)*Real.exp y := by
  let v := y/(2:ℝ)^(B+2)
  let r := dyadicFloor P v
  let a := roundedExpHorner P r 0 (P+4)
  let u := 1/(2:ℝ)^P
  have hu : 0≤u := by dsimp [u]; positivity
  have hu1 : u≤1 := by
    dsimp [u]
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  obtain ⟨hv0,_,hr0,hr1⟩ := positive_exp_reduced_bounds hy0 hyB P
  obtain ⟨ha0,ha1,haerr⟩ := roundedExpHorner_exp_error hr0 hr1 P
  change 1≤a at ha0
  change a≤Real.exp r at ha1
  change |a-Real.exp r|≤5/(2:ℝ)^P at haerr
  have hT1 : 1≤Real.exp v := Real.one_le_exp_iff.mpr hv0
  have hT : Real.exp r≤Real.exp v := Real.exp_le_exp.mpr (dyadicFloor_le P v)
  have harg := exp_argument_error hu1 (dyadicFloor_error P v)
  have herr : Real.exp v-a≤(7*u)*Real.exp v := by
    have hh := le_trans (abs_sub_le a (Real.exp r) (Real.exp v)) (add_le_add haerr harg)
    have hm := mul_le_mul_of_nonneg_left hT1 (show 0≤5*u by positivity)
    have hh' := (abs_le.mp hh).1
    dsimp only [u] at hh' hm ⊢
    simp only [div_eq_mul_inv] at hh' hm ⊢
    nlinarith only [hh',hm]
  have hsq := roundedSquares_error ha0 (le_trans ha1 hT) herr P (B+2)
  rw [exp_halving_power] at hsq
  obtain ⟨_,hupper⟩ := positiveExpRounded_bounds hy0 hyB P
  rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
  change -(roundedSquares P a (B+2)-Real.exp y)≤_
  have hnonneg := mul_nonneg hu (le_of_lt (Real.exp_pos y))
  dsimp only [u] at hsq hnonneg
  simp only [div_eq_mul_inv] at hsq hnonneg ⊢
  nlinarith only [hsq,hnonneg]

/-- Guard precision `q+B+5` gives relative error `2⁻q` for the positive
exponential calculation. -/
theorem positiveExpRounded_relative {y : ℝ} {P B q : ℕ}
    (hy0 : 0≤y) (hyB : y≤B) (hP : q+B+5≤P) :
    |positiveExpRounded P B y-Real.exp y|≤(1/(2:ℝ)^q)*Real.exp y := by
  have hb := positiveExpRounded_error hy0 hyB P
  have hp : (2:ℝ)^(q+B+5)≤(2:ℝ)^P := pow_le_pow_right₀ (by norm_num) hP
  have he : (2:ℝ)^(q+B+5)=(2:ℝ)^q*(8*(2:ℝ)^(B+2)) := by
    rw [show q+B+5=q+(B+2)+3 by omega,pow_add,pow_add]
    norm_num
    ring
  rw [he] at hp
  have hcoeff : 8*(2:ℝ)^(B+2)/(2:ℝ)^P≤1/(2:ℝ)^q := by
    apply (div_le_div_iff₀ (show (0:ℝ)<(2:ℝ)^P by positivity)
      (show (0:ℝ)<(2:ℝ)^q by positivity)).mpr
    simpa only [one_mul,mul_comm] using hp
  exact le_trans hb (mul_le_mul_of_nonneg_right hcoeff (le_of_lt (Real.exp_pos y)))

/-- A nonnegative exponential with argument at most `B` is at most `2^(2B)`. -/
theorem exp_le_two_pow_twice {y : ℝ} {B : ℕ} (hyB : y≤B) :
    Real.exp y≤(2:ℝ)^(2*B) := by
  have he1 : Real.exp 1≤4 := by
    have hh := Real.abs_exp_sub_one_le (x:=1) (by norm_num)
    norm_num only [abs_one,mul_one] at hh
    have hh' := (abs_le.mp hh).2
    linarith only [hh']
  calc
    Real.exp y ≤ Real.exp (B:ℝ) := Real.exp_le_exp.mpr hyB
    _ = Real.exp 1^B := by simpa only [mul_one] using Real.exp_nat_mul 1 B
    _ ≤ (4:ℝ)^B := pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he1 B
    _ = (2:ℝ)^(2*B) := by rw [pow_mul]; norm_num

end MinCostFlow.Num
