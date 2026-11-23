module

public import MinCostFlow.Num.Representation
import Mathlib.Tactic

/-!
# Room for limb arithmetic

The representation condition `2*h+2 ≤ w` leaves two spare bits above a product of
two limbs. Thus a product plus two limb-sized carries fits in a machine word. These
bounds account for the machine's checked arithmetic, including its intermediate results.
-/

public section
namespace MinCostFlow.Num

/-- The capacity is a power of two with one bit position per stored limb bit. -/
theorem capacity_eq_two_pow (h L : ℕ) : capacity h L = 2 ^ (h * L) := by
  exact (pow_mul 2 h L).symm

/-- The limb base is a word whenever products have the required slack. -/
theorem base_lt_word {h w : ℕ} (hf : 2 * h + 2 ≤ w) : base h < 2 ^ w := by
  apply Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ))
  omega

/-- Multiplication of two limbs followed by two carries does not overflow a word. -/
theorem limb_mul_add_lt_word {h w x y c d : ℕ}
    (hf : 2 * h + 2 ≤ w) (hx : x < base h) (hy : y < base h)
    (hc : c < base h) (hd : d < base h) : x * y + c + d < 2 ^ w := by
  have hb := base_pos h
  have hxy : x * y ≤ (base h - 1) * (base h - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  calc
    x * y + c + d < 4 * base h ^ 2 := by
      have hh : base h - 1 + 1 = base h := by omega
      nlinarith
    _ = 2 ^ (2 * h + 2) := by
      rw [base, ← pow_mul, pow_add, Nat.mul_comm 2 h]
      ring
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hf

/-- Adding two limbs and one carry also fits in a word. -/
theorem limb_add_lt_word {h w x y c : ℕ}
    (hf : 2 * h + 2 ≤ w) (hx : x < base h) (hy : y < base h)
    (hc : c < base h) : x + y + c < 2 ^ w := by
  have hb := base_pos h
  have htwo : 2 * base h ≤ 4 * base h ^ 2 := by nlinarith
  calc
    x + y + c < 4 * base h ^ 2 := by nlinarith
    _ = 2 ^ (2 * h + 2) := by
      rw [base, ← pow_mul, pow_add, Nat.mul_comm 2 h]
      ring
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hf

end MinCostFlow.Num
