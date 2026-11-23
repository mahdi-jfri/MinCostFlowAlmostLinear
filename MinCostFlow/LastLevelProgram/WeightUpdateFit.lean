module

public import MinCostFlow.LastLevelProgram.WeightUpdateCall
import MinCostFlow.Num.MultiplyFacts
import MinCostFlow.Num.FixedDivideFacts
import MinCostFlow.Num.ShiftRightFacts
import Mathlib.Tactic

/-!
# Working width for the weight update

The stored weight and stretch can each fit in a narrow block while
their product needs more limbs. Two operand widths and one extra
limb suffice for the entire signed update of Lemma 5.5 (page 18).
-/

public section

namespace MinCostFlow.LastLevelProgram

open Num

private theorem fits_add_extra {h M : ℕ} {x y : ℤ} (hh : 0 < h)
    (hx : Fits h M x) (hy : Fits h M y) : Fits h (M + 1) (x + y) := by
  have hb : 2 ≤ base h := by
    unfold base
    exact Nat.le_self_pow (by omega) _
  have hcap : 2 * (capacity h M : ℤ) ≤ (capacity h (M + 1) : ℤ) := by
    rw [capacity_succ, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hb) (Int.natCast_nonneg _)
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  exact ⟨by omega, by omega⟩

/-- A width of `2 * L + 1` holds the input blocks, exact product,
integer quotient, and final weight. The denominator here is the
already-scaled positive integer used by the divide call. -/
theorem weightUpdate_workingFit {h L : ℕ} {a b d : ℤ}
    (hh : 0 < h) (ha : Fits h L a) (hb : Fits h L b) (hd : Fits h L d) (hd₀ : 0 < d) :
    let W := 2 * L + 1
    Fits h W a ∧ Fits h W b ∧ Fits h W d ∧
      Fits h W (a * b) ∧ Fits h W (a * b / d) ∧ Fits h W (a + a * b / d) := by
  have hp := fits_mul_double ha hb
  have hq := fits_ediv hp hd₀
  have hle : L ≤ 2 * L := by omega
  have hle' : L ≤ 2 * L + 1 := by omega
  refine ⟨fits_of_length_le hle' ha, fits_of_length_le hle' hb, fits_of_length_le hle' hd,
    fits_of_length_le (Nat.le_succ _) hp, fits_of_length_le (Nat.le_succ _) hq, ?_⟩
  exact fits_add_extra hh (fits_of_length_le hle ha) hq

end MinCostFlow.LastLevelProgram
