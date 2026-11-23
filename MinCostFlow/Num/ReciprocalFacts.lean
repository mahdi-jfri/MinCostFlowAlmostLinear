module

public import MinCostFlow.Num.ApproximationFacts
import MinCostFlow.Num.ShiftRightFacts
import MinCostFlow.Num.ShiftFacts
import MinCostFlow.Num.WordBounds
import Mathlib.Tactic

/-!
# Range and rounding for reciprocals

An input at least `2⁻ᴱ` has reciprocal at most `2ᴱ`. Two spare bits
beyond precision plus `E` therefore suffice for the signed output. The only
rounding is the final floor performed by fixed-point division.
-/

public section
namespace MinCostFlow.Num

/-- Two spare bits cover the scaled reciprocal in the signed output range. -/
theorem reciprocal_floor_fits {x : ℝ} {h L P E : ℕ}
    (hx : 1/(2:ℝ)^E ≤ x) (hwidth : P+E+2≤h*L) :
    Fits h L ⌊(1/x)*(2:ℝ)^P⌋ := by
  have hxp : 0<x := lt_of_lt_of_le (by positivity) hx
  have hi : 1/x≤(2:ℝ)^E := (div_le_iff₀ hxp).mpr (by
    have hh := (div_le_iff₀ (show (0:ℝ)<(2:ℝ)^E by positivity)).mp hx
    nlinarith only [hh])
  have hf0 : (0:ℤ)≤⌊(1/x)*(2:ℝ)^P⌋ := Int.floor_nonneg.mpr (by positivity)
  have hf := Int.floor_le ((1/x)*(2:ℝ)^P)
  have hu : (⌊(1/x)*(2:ℝ)^P⌋ : ℝ) ≤ (2:ℝ)^(P+E) := by
    calc
      _ ≤ (1/x)*(2:ℝ)^P := hf
      _ ≤ (2:ℝ)^E*(2:ℝ)^P := mul_le_mul_of_nonneg_right hi (by positivity)
      _ = (2:ℝ)^(P+E) := by rw [pow_add]; ring
  have hc : (2:ℝ)^(P+E+2) ≤ (capacity h L : ℝ) := by
    rw [capacity_eq_two_pow]
    push_cast
    exact pow_le_pow_right₀ (by norm_num) hwidth
  have ht : 2*(⌊(1/x)*(2:ℝ)^P⌋ : ℝ)<(capacity h L : ℝ) := by
    rw [pow_add] at hc
    norm_num only [pow_two] at hc
    have hp : (0:ℝ)<(2:ℝ)^(P+E) := by positivity
    nlinarith only [hu,hc,hp]
  have ht' : 2*⌊(1/x)*(2:ℝ)^P⌋ < (capacity h L : ℤ) := by exact_mod_cast ht
  exact ⟨by have hc0 : (0:ℤ)≤capacity h L := Int.natCast_nonneg _; omega, ht'⟩

/-- Exact integer division of a stored one by the input equals rounding the
real reciprocal at the output precision. -/
theorem reciprocal_floorDiv {mem : ℕ→ℕ} {one a h L P : ℕ}
    (hone : intVal mem one h L=(2:ℤ)^P) :
    floorDiv (intVal mem one h L*(2:ℤ)^P) (intVal mem a h L)=
      ⌊(1/fixVal mem a h L P)*(2:ℝ)^P⌋ := by
  rw [floorDiv_eq_floor,hone]
  congr 1
  simp only [fixVal,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  field_simp

end MinCostFlow.Num
