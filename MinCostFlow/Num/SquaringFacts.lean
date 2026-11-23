module

public import MinCostFlow.Num.DyadicRoundingFacts
import Mathlib.Tactic

/-!
# Relative error in repeated rounded squaring

All inputs here are at least one. Rounded squares stay at least one and remain
below the exact squares. Their relative error at most doubles per step, plus
one last-place unit. The resulting geometric error bound includes every
rounding in the squaring loop.
-/

@[expose] public section
namespace MinCostFlow.Num

/-- Repeated squaring with one fixed-point floor per step. -/
noncomputable def roundedSquares (P : ℕ) (a : ℝ) : ℕ→ℝ
  | 0 => a
  | n+1 => dyadicFloor P ((roundedSquares P a n)^2)

/-- A rounded square stays between one and the exact square of any upper bound. -/
theorem dyadic_square_bounds {a T : ℝ} (ha : 1≤a) (hT : a≤T) (P : ℕ) :
    1≤dyadicFloor P (a^2) ∧ dyadicFloor P (a^2)≤T^2 := by
  have ha0 : 0≤a := by linarith
  have ht0 : 0≤T := le_trans ha0 hT
  constructor
  · rw [← dyadicFloor_one P]
    exact dyadicFloor_mono P (by nlinarith only [ha])
  · exact le_trans (dyadicFloor_le P _) (pow_le_pow_left₀ ha0 hT 2)

/-- One rounded square doubles relative error and adds at most one last-place
unit to it, because the exact square is at least one. -/
theorem dyadic_square_error {a T δ : ℝ} (ha : 1≤a) (haT : a≤T)
    (herr : T-a≤δ*T) (P : ℕ) :
    T^2-dyadicFloor P (a^2)≤(2*δ+1/(2:ℝ)^P)*T^2 := by
  have ha0 : 0≤a := by linarith
  have hT0 : 0<T := by linarith
  have hδ : 0≤δ := by
    have hh : 0≤δ*T := le_trans (sub_nonneg.mpr haT) herr
    exact (mul_nonneg_iff_of_pos_right hT0).mp hh
  have hsum : T+a≤2*T := by linarith only [haT]
  have hprod := mul_le_mul herr hsum (by linarith only [ha,haT] : 0≤T+a)
    (mul_nonneg hδ (le_of_lt hT0))
  have hsquare : T^2-a^2≤2*δ*T^2 := by nlinarith only [hprod]
  have hround := (abs_le.mp (dyadicFloor_error P (a^2))).1
  have hu : (0:ℝ)≤1/(2:ℝ)^P := by positivity
  have hT1 : 1≤T^2 := by nlinarith only [ha,haT]
  have hunit := mul_le_mul_of_nonneg_left hT1 hu
  nlinarith only [hsquare,hround,hunit]

/-- All rounded iterates stay in the corresponding exact power interval. -/
theorem roundedSquares_bounds {a T : ℝ} (ha : 1≤a) (hT : a≤T) (P n : ℕ) :
    1≤roundedSquares P a n ∧ roundedSquares P a n≤T^(2^n) := by
  induction n with
  | zero => simpa only [roundedSquares,pow_zero,pow_one] using And.intro ha hT
  | succ n ih =>
    obtain ⟨hlo,hhi⟩ := dyadic_square_bounds ih.1 ih.2 P
    change 1≤dyadicFloor P ((roundedSquares P a n)^2) ∧
      dyadicFloor P ((roundedSquares P a n)^2)≤T^(2^(n+1))
    rw [pow_succ,← pow_mul] at hhi
    exact ⟨hlo,hhi⟩

/-- After `n` squarings, the relative error is at most
`2^n*(δ+2⁻ᴾ)-2⁻ᴾ`. -/
theorem roundedSquares_error {a T δ : ℝ} (ha : 1≤a) (haT : a≤T)
    (herr : T-a≤δ*T) (P n : ℕ) :
    T^(2^n)-roundedSquares P a n≤
      ((2:ℝ)^n*(δ+1/(2:ℝ)^P)-1/(2:ℝ)^P)*T^(2^n) := by
  induction n with
  | zero => simpa only [pow_zero,pow_one,roundedSquares,one_mul,add_sub_cancel_right] using herr
  | succ n ih =>
    obtain ⟨hlo,hhi⟩ := roundedSquares_bounds ha haT P n
    have hh := dyadic_square_error hlo hhi ih P
    have he : (T^(2^n))^2=T^(2^(n+1)) := by rw [← pow_mul,pow_succ]
    rw [he] at hh
    change T^(2^(n+1))-dyadicFloor P ((roundedSquares P a n)^2)≤_
    convert hh using 1 <;> rw [pow_succ] <;> ring

end MinCostFlow.Num
