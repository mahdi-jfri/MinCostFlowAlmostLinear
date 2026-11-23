module

public import MinCostFlow.Num.ShiftLeft
public import MinCostFlow.LastLevelProgram.SelectFormat
import Mathlib.Tactic

/-!
# Scaling fixed-point blocks for the last-level rebuild

The weight update divides by the integer scale times the grid
denominator. The same left-shift procedure can raise a stored
weight to the common precision required by the LSST query.
-/

public section

namespace MinCostFlow.LastLevelProgram

open Num WordRAM

/-- A positive integer scale can be shifted into the selected format
under a bound on its scaled numerator. -/
theorem scaledDenominator_fits {h L P : ℕ} {scale : ℤ}
    (hpos : 0 < scale)
    (hwidth : 2 * (scale : ℝ) * (2 : ℝ)^P < capacity h L) :
    Fits h L (scale * (2 : ℤ)^P) := by
  have hnonneg : 0 ≤ scale * (2 : ℤ)^P := mul_nonneg hpos.le (by positivity)
  refine ⟨by have hc := Int.natCast_nonneg (capacity h L); omega, ?_⟩
  have hb : (2 : ℝ) * ((scale * (2 : ℤ)^P : ℤ) : ℝ) < capacity h L := by
    push_cast
    simpa only [mul_assoc] using hwidth
  exact_mod_cast hb

/-- Shift a valid block left with exact signed semantics whenever
the shifted integer fits its width. -/
theorem scaleBlock_runs {w h i : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2 * h + 2 ≤ w) (hp : p.HasAt i (shiftLeftModule i h))
    (a L bits heap pos : ℕ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hwords : ∀ x ∈ [a,L,bits,heap], x < 2 ^ w)
    (ha : a + L ≤ heap) (hv : Valid mem a h L)
    (hz : ZeroFrom mem heap) (hroom : heap + L < 2 ^ w)
    (hfit : Fits h L (intVal mem a h L * (2 : ℤ)^bits)) :
    ∃ body, p.procs[i]? = some body ∧ ∃ o st cost,
      Runs w p ω body (startState [a,L,bits,heap] mem pos) o st cost ∧
      o.value = heap + L ∧ Valid st.mem heap h L ∧
      intVal st.mem heap h L = intVal mem a h L * (2 : ℤ)^bits ∧
      (∀ x < heap, st.mem x = mem x) ∧ ZeroFrom st.mem o.value ∧
      cost ≤ 35 * L + 35 := by
  obtain ⟨body, hb, o, st, cost, hr, hpost, hc⟩ :=
    shiftLeft_meetsContract hh hw hp [a,L,bits,heap] mem pos ω hwords
      ⟨⟨a,L,bits,heap,rfl,ha,hv⟩,hz,hroom⟩
  obtain ⟨hout, _, _, hframe, hzero, hv', hval⟩ := hpost
  change intVal st.mem heap h L = wrap h L (intVal mem a h L * (2 : ℤ)^bits) at hval
  rw [wrap_of_fits hfit] at hval
  exact ⟨body, hb, o, st, cost, hr, hout, hv', hval, hframe, hzero, hc⟩

/-- A left shift by the difference between two grid precisions preserves
the decoded real value at the finer precision. -/
theorem fixVal_of_shift {mem out : ℕ → ℕ} {a b h L P Q : ℕ} (hPQ : P ≤ Q)
    (hval : intVal out b h L = intVal mem a h L * (2 : ℤ)^(Q-P)) :
    fixVal out b h L Q = fixVal mem a h L P := by
  have hpow : (2 : ℝ)^Q = (2 : ℝ)^P * (2 : ℝ)^(Q-P) := by
    rw [← pow_add, Nat.add_sub_of_le hPQ]
  rw [fixVal, hval, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, hpow, fixVal]
  field_simp

/-- If the source block stores a value at precision `P`, the integer
produced by shifting to `Q` is the canonical numerator at `Q`. -/
theorem queryNumerator_of_shift {mem : ℕ → ℕ} {a h L P Q : ℕ} (hPQ : P ≤ Q) :
    queryNumerator Q (fixVal mem a h L P) =
      intVal mem a h L * (2 : ℤ)^(Q-P) := by
  have hpow : (2 : ℝ)^Q = (2 : ℝ)^P * (2 : ℝ)^(Q-P) := by
    rw [← pow_add, Nat.add_sub_of_le hPQ]
  have hval : fixVal mem a h L P =
      ((intVal mem a h L * (2 : ℤ)^(Q-P) : ℤ) : ℝ) / (2 : ℝ)^Q := by
    rw [fixVal, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, hpow]
    field_simp
  rw [hval, queryNumerator_grid]

end MinCostFlow.LastLevelProgram
