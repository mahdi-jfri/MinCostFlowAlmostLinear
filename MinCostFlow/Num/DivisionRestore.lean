module

public import MinCostFlow.Num.NegateCarry
import Mathlib.Tactic

/-!
# Restoring a negative quotient

Complementing an unsigned quotient with carry one gives its negative. Carry zero
subtracts one more, as required when a negative real quotient has nonzero remainder.
The result is explicitly wrapped to the output width.
-/

public section
namespace MinCostFlow.Num
open WordRAM

/-- Complementing unsigned digits restores a negative quotient, with a possible extra unit. -/
theorem negateCarry_unsigned_value {mem mem' : ℕ → ℕ} {a out h L c : ℕ}
    (hv : Valid mem a h L) (_hc : c ≤ 1)
    (hl : ListAt mem' out (digits h L (capacity h L - 1 - unsignedVal mem a h L + c))) :
    Valid mem' out h L ∧
      intVal mem' out h L = wrap h L (-(unsignedVal mem a h L : ℤ) - 1 + (c : ℤ)) := by
  have hu := unsignedVal_lt hv
  have hn : capacity h L - 1 - unsignedVal mem a h L + c =
      capacity h L - (unsignedVal mem a h L + 1) + c := by omega
  have he : ((capacity h L - 1 - unsignedVal mem a h L + c : ℕ) : ℤ) =
      (-(unsignedVal mem a h L : ℤ) - 1 + (c : ℤ)) + (capacity h L : ℤ) := by
    rw [hn, Nat.cast_add, Int.natCast_sub (by omega), Nat.cast_add, Nat.cast_one]
    ring
  have hout := unsignedVal_listAt (h := h) hl
  rw [digits_length,listVal_digits] at hout
  refine ⟨by simpa using valid_listAt hl (digits_lt h L _), ?_⟩
  rw [intVal,hout,← wrap_natCast]
  apply wrap_congr
  rw [he,Int.add_emod_right]

end MinCostFlow.Num
