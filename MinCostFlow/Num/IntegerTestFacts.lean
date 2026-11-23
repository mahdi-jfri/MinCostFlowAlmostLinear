module

public import MinCostFlow.Num.DivisionSigns
import MinCostFlow.Num.ShiftFacts
import MinCostFlow.Num.SignFacts
import MinCostFlow.Num.WordBounds
import Mathlib.Tactic

/-!
# Integer fixed-point values and zero low limbs

A fixed-point value is an integer exactly when its numerator is divisible by the
precision scale. For precision in whole limbs, this is equivalent to zero in the low
precision limbs, capped at the block length.
-/

public section
namespace MinCostFlow.Num

/-- The fixed-point real is an integer exactly when the scale divides the numerator. -/
theorem fixVal_isInteger_iff (mem : ℕ→ℕ) (a h L P : ℕ) :
    (∃ z:ℤ,fixVal mem a h L P=(z:ℝ)) ↔ (2:ℤ)^P∣intVal mem a h L := by
  have ht : (2:ℝ)^P≠0 := ne_of_gt (pow_pos (by norm_num) _)
  constructor
  · rintro ⟨z,hz⟩
    have he : (intVal mem a h L : ℝ)=(2:ℝ)^P*(z:ℝ) := by
      rw [fixVal,div_eq_iff ht] at hz
      simpa only [mul_comm] using hz
    have hei : intVal mem a h L=(2:ℤ)^P*z := by exact_mod_cast he
    exact ⟨z,hei⟩
  · rintro ⟨z,hz⟩
    refine ⟨z,?_⟩
    rw [fixVal,hz]
    push_cast
    exact mul_div_cancel_left₀ (z:ℝ) ht

/-- Zero low whole limbs characterize divisibility by their capacity. -/
theorem intVal_dvd_capacity_iff {mem : ℕ→ℕ} {a h L q : ℕ}
    (hv : Valid mem a h L) (hq : q≤L) :
    (capacity h q : ℤ)∣intVal mem a h L ↔ unsignedVal mem a h q=0 := by
  have hd : (capacity h q : ℤ)∣(capacity h L : ℤ) := by
    exact_mod_cast (show capacity h q∣capacity h L by unfold capacity; exact pow_dvd_pow (base h) hq)
  have he := Int.ModEq.of_dvd hd (signedVal_emod h L (unsignedVal mem a h L))
  change intVal mem a h L % (capacity h q:ℤ)=(unsignedVal mem a h L:ℤ)%(capacity h q:ℤ) at he
  rw [← Int.natCast_emod,unsignedVal_mod_prefix hv hq] at he
  rw [Int.dvd_iff_emod_eq_zero,he]
  exact Int.natCast_eq_zero

/-- A whole-limb precision uses at most all stored limbs in the integer test. -/
theorem intVal_dvd_scale_iff {mem : ℕ→ℕ} {a h L P : ℕ}
    (_hh : 0<h) (hP : h∣P) (hv : Valid mem a h L) :
    (2:ℤ)^P∣intVal mem a h L ↔ unsignedVal mem a h (min (P/h) L)=0 := by
  have he : capacity h (P/h)=2^P := by
    rw [capacity_eq_two_pow,Nat.mul_div_cancel' hP]
  have hei : (capacity h (P/h):ℤ)=(2:ℤ)^P := by exact_mod_cast he
  by_cases hq : P/h≤L
  · rw [min_eq_left hq,← hei]
    exact intVal_dvd_capacity_iff hv hq
  · have hLq : L≤P/h := by omega
    rw [min_eq_right hLq]
    have hle : capacity h L≤2^P := by
      rw [← he]
      unfold capacity
      exact Nat.pow_le_pow_right (base_pos h) hLq
    have hlt : (intVal mem a h L).natAbs<((2:ℤ)^P).natAbs := by
      have hnat : ((2:ℤ)^P).natAbs=2^P := by simp
      rw [hnat]
      exact lt_of_lt_of_le (intVal_natAbs_lt hv) hle
    rw [← intVal_eq_zero_iff hv]
    constructor
    · intro hd; exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hlt
    · intro hz; rw [hz]; exact dvd_zero _

end MinCostFlow.Num
