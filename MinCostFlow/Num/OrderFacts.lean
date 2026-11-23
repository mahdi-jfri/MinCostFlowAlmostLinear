module

public import MinCostFlow.Num.Representation
import MinCostFlow.Num.SignFacts
import Mathlib.Tactic

/-!
# Ordering limb blocks

A different highest limb decides unsigned order because all lower limbs together are
smaller than one unit of the highest limb. Equal highest limbs can be dropped.
For signed blocks of the same sign, unsigned and signed order agree.
-/

public section
namespace MinCostFlow.Num

/-- A valid prefix is below its capacity. -/
private theorem prefix_lt {mem : ℕ → ℕ} {a h L : ℕ} (hv : Valid mem a h (L + 1)) :
    unsignedVal mem a h L < capacity h L :=
  unsignedVal_lt (fun i hi => hv i (by omega))

/-- A smaller highest limb gives a smaller unsigned value. -/
theorem unsignedVal_lt_of_top_lt {mem : ℕ → ℕ} {a d h L : ℕ}
    (ha : Valid mem a h (L + 1)) (_hd : Valid mem d h (L + 1))
    (ht : mem (a + L) < mem (d + L)) :
    unsignedVal mem a h (L + 1) < unsignedVal mem d h (L + 1) := by
  have hlow := prefix_lt ha
  have hm := Nat.mul_le_mul_left (capacity h L) (Nat.succ_le_of_lt ht)
  rw [unsignedVal_snoc, unsignedVal_snoc]
  nlinarith

/-- Equal highest limbs leave precisely the order of the prefixes. -/
theorem unsignedVal_lt_iff_of_top_eq {mem : ℕ → ℕ} {a d h L : ℕ}
    (ht : mem (a + L) = mem (d + L)) :
    unsignedVal mem a h (L + 1) < unsignedVal mem d h (L + 1) ↔
      unsignedVal mem a h L < unsignedVal mem d h L := by
  rw [unsignedVal_snoc, unsignedVal_snoc, ht]
  omega

/-- Within one sign, signed and unsigned order agree. -/
theorem intVal_lt_iff_of_same_sign {mem : ℕ → ℕ} {a d h L : ℕ}
    (ha : Valid mem a h L) (hd : Valid mem d h L)
    (hs : intVal mem a h L < 0 ↔ intVal mem d h L < 0) :
    intVal mem a h L < intVal mem d h L ↔
      unsignedVal mem a h L < unsignedVal mem d h L := by
  have hu := unsignedVal_lt ha
  have hv := unsignedVal_lt hd
  dsimp only [intVal, signedVal] at hs ⊢
  split_ifs at hs ⊢ <;> omega

end MinCostFlow.Num
