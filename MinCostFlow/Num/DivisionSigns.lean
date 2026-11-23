module

public import MinCostFlow.Num.Encoding
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import MinCostFlow.Num.SignFacts
import MinCostFlow.Num.ShiftRightFacts
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Signs and floor division

The division procedure computes magnitudes with natural division, then restores signs.
For differing signs a nonzero remainder requires one further negative unit. `floorDiv`
uses a positive denominator, so it is mathematical floor division even when the original
denominator is negative. It agrees with the floor of the real quotient.
-/

@[expose] public section
namespace MinCostFlow.Num

/-- Signed floor division, normalizing a negative denominator before integer division. -/
def floorDiv (x y : ℤ) : ℤ := if y < 0 then (-x) / (-y) else x / y

/-- The signed quotient convention is the floor of the real quotient. -/
theorem floorDiv_eq_floor (x y : ℤ) : floorDiv x y = ⌊(x : ℝ) / (y : ℝ)⌋ := by
  unfold floorDiv
  split_ifs with hy
  · rw [show (x : ℝ) / (y : ℝ) = ((-x : ℤ) : ℝ) / ((-y : ℤ) : ℝ) by simp only [Int.cast_neg, neg_div_neg_eq],
      Int.floor_div_cast_of_nonneg (show (0 : ℤ) ≤ -y by omega), Int.floor_intCast]
  · rw [Int.floor_div_cast_of_nonneg (show (0 : ℤ) ≤ y by omega), Int.floor_intCast]

private theorem negative_nat_quotient (A D : ℕ) (hD : 0 < D) :
    (-(A : ℤ)) / (D : ℤ) = -((A / D : ℕ) : ℤ) - if A % D = 0 then 0 else 1 := by
  have hp : (0 : ℤ) < D := by exact_mod_cast hD
  have hm : (A % D : ℕ) + (D : ℤ) * (A / D : ℕ) = (A : ℤ) := by exact_mod_cast Nat.mod_add_div A D
  have hr : (A % D : ℕ) < (D : ℤ) := by exact_mod_cast Nat.mod_lt A hD
  have hr0 : (0 : ℤ) ≤ (A % D : ℕ) := Int.natCast_nonneg _
  split_ifs with he
  · have hz : (A % D : ℕ) = (0 : ℤ) := by exact_mod_cast he
    apply (Int.ediv_eq_iff_of_pos hp).mpr
    constructor <;> nlinarith only [hm, hz, hp]
  · have hpos : (0 : ℤ) < (A % D : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero he
    apply (Int.ediv_eq_iff_of_pos hp).mpr
    constructor <;> nlinarith only [hm, hpos, hr]

/-- Magnitude division and a remainder test determine the signed floor quotient. -/
theorem floorDiv_abs (x y : ℤ) (hy : y ≠ 0) :
    floorDiv x y = if (x < 0 ↔ y < 0) then ((x.natAbs / y.natAbs : ℕ) : ℤ) else
      -((x.natAbs / y.natAbs : ℕ) : ℤ) - if x.natAbs % y.natAbs = 0 then 0 else 1 := by
  have hD : 0 < y.natAbs := Int.natAbs_pos.mpr hy
  by_cases hx : x < 0 <;> by_cases hy' : y < 0
  · have hxa : (x.natAbs : ℤ) = -x := by rw [Int.natCast_natAbs, abs_of_neg hx]
    have hya : (y.natAbs : ℤ) = -y := by rw [Int.natCast_natAbs, abs_of_neg hy']
    simp [floorDiv, hx, hy', Int.natCast_ediv, hxa, hya]
  · have hxa : (x.natAbs : ℤ) = -x := by rw [Int.natCast_natAbs, abs_of_neg hx]
    have hya : (y.natAbs : ℤ) = y := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
    simpa [floorDiv, hx, hy', hxa, hya] using negative_nat_quotient x.natAbs y.natAbs hD
  · have hxa : (x.natAbs : ℤ) = x := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
    have hya : (y.natAbs : ℤ) = -y := by rw [Int.natCast_natAbs, abs_of_neg hy']
    simpa [floorDiv, hx, hy', hxa, hya] using negative_nat_quotient x.natAbs y.natAbs hD
  · have hxa : (x.natAbs : ℤ) = x := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
    have hya : (y.natAbs : ℤ) = y := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
    simp [floorDiv, hx, hy', Int.natCast_ediv, hxa, hya]

/-- Every signed block has absolute value strictly below its unsigned capacity. -/
theorem intVal_natAbs_lt {mem : ℕ → ℕ} {a h L : ℕ} (hv : Valid mem a h L) :
    (intVal mem a h L).natAbs < capacity h L := by
  obtain ⟨hlo, hhi⟩ := intVal_fits hv
  have hp : (0 : ℤ) < capacity h L := by exact_mod_cast capacity_pos h L
  have he : |intVal mem a h L| < (capacity h L : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  rw [← Int.natCast_natAbs] at he
  exact_mod_cast he

/-- A nonnegative signed source has its ordinary magnitude as unsigned value. -/
theorem unsignedVal_nonnegative_abs {mem : ℕ → ℕ} {a h L : ℕ}
    (hv : Valid mem a h L) (hn : ¬ intVal mem a h L < 0) :
    unsignedVal mem a h L = (intVal mem a h L).natAbs := by
  have he := intVal_eq_unsigned_sub_sign hv
  rw [ite_eq_right hn, sub_zero] at he
  have ha : ((intVal mem a h L).natAbs : ℤ) = intVal mem a h L := by
    rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
  exact_mod_cast he.symm.trans ha.symm

/-- Negating a negative source gives its unsigned absolute value, including the signed minimum. -/
theorem negated_unsigned_abs {mem mem' : ℕ → ℕ} {a out h L : ℕ}
    (hv : Valid mem a h L) (hn : intVal mem a h L < 0)
    (hl : WordRAM.ListAt mem' out (digits h L (capacity h L - 1 - unsignedVal mem a h L + 1))) :
    unsignedVal mem' out h L = (intVal mem a h L).natAbs := by
  have hu := unsignedVal_lt hv
  have hp := capacity_pos h L
  have hsign := (intVal_neg_iff hv).mp hn
  have hupos : 0 < unsignedVal mem a h L := by omega
  have hnval := intVal_eq_unsigned_sub_sign hv
  rw [ite_eq_left hn] at hnval
  have ha : ((intVal mem a h L).natAbs : ℤ) = -intVal mem a h L := by
    rw [Int.natCast_natAbs, abs_of_neg hn]
  have he : capacity h L - unsignedVal mem a h L = (intVal mem a h L).natAbs := by
    have he' : ((capacity h L - unsignedVal mem a h L : ℕ) : ℤ) =
        ((intVal mem a h L).natAbs : ℤ) := by
      rw [Int.natCast_sub (Nat.le_of_lt hu), ha, hnval]
      ring
    exact_mod_cast he'
  have hout := unsignedVal_listAt (h := h) hl
  rw [digits_length, listVal_digits,
    show capacity h L - 1 - unsignedVal mem a h L + 1 = capacity h L - unsignedVal mem a h L by omega,
    Nat.mod_eq_of_lt (by omega), he] at hout
  exact hout

end MinCostFlow.Num
