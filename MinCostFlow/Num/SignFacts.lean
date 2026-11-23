module

public import MinCostFlow.Num.Representation
import Mathlib.Tactic

/-!
# Reading the sign bit

The highest limb contains the sign bit. The lower limbs contribute strictly less than
one unit of that limb, so they cannot change the sign. These facts let the machine
read the sign in constant time even when the block spans many words.
-/

public section
namespace MinCostFlow.Num

/-- Split off the highest limb of a block. -/
theorem unsignedVal_snoc (mem : ℕ → ℕ) (a h L : ℕ) :
    unsignedVal mem a h (L + 1) = unsignedVal mem a h L + capacity h L * mem (a + L) := by
  induction L generalizing a with
  | zero => simp [unsignedVal, capacity]
  | succ L ih =>
    have ht := ih (a + 1)
    simp only [unsignedVal] at ht ⊢
    rw [ht, capacity_succ]
    have he : a + 1 + L = a + (L + 1) := by omega
    rw [he]
    ring

/-- The top-half test is exactly negativity of signed decoding. -/
theorem intVal_neg_iff {mem : ℕ → ℕ} {a h L : ℕ} (hv : Valid mem a h L) :
    intVal mem a h L < 0 ↔ capacity h L ≤ 2 * unsignedVal mem a h L := by
  have hu := unsignedVal_lt hv
  dsimp only [intVal, signedVal]
  split_ifs <;> omega

/-- A positive limb width gives an even base. -/
theorem base_eq_two_mul_half {h : ℕ} (hh : 0 < h) :
    base h = 2 * (base h / 2) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
  simp [base, pow_succ']

/-- A nonempty valid block is negative exactly when its top limb has its sign bit set. -/
theorem intVal_neg_iff_top {mem : ℕ → ℕ} {a h L : ℕ}
    (hh : 0 < h) (hv : Valid mem a h (L + 1)) :
    intVal mem a h (L + 1) < 0 ↔ base h / 2 ≤ mem (a + L) := by
  have hlow : unsignedVal mem a h L < capacity h L := by
    apply unsignedVal_lt
    intro i hi
    exact hv i (by omega)
  have hc := capacity_pos h L
  have hb := base_eq_two_mul_half hh
  rw [intVal_neg_iff hv, unsignedVal_snoc, capacity_succ]
  constructor
  · intro hn
    by_contra ht
    have ht' : mem (a + L) + 1 ≤ base h / 2 := by omega
    have hm := Nat.mul_le_mul_left (capacity h L) ht'
    nlinarith
  · intro ht
    have hm := Nat.mul_le_mul_left (capacity h L) ht
    nlinarith

end MinCostFlow.Num
