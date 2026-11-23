module

public import MinCostFlow.Num.Encoding
import MinCostFlow.Num.ShiftFacts
import MinCostFlow.Num.ShiftRightFacts
import Mathlib.Tactic

/-!
# Values in one long-division step

The old remainder is smaller than the divisor. Appending one limb keeps the new
numerator below the divisor times the base. Estimated products fit one extra limb.
After correcting the digit, subtraction gives a nonnegative remainder that fits the
signed extra-limb block. The lemmas here connect those facts to the limb procedures.
-/

public section
namespace MinCostFlow.Num

/-- Removing only zero high limbs preserves the unsigned value. -/
theorem unsignedVal_eq_prefix_of_zeros {mem : ℕ → ℕ} {a h K n : ℕ} (hn : n ≤ K)
    (hz : ∀ i, n ≤ i → i < K → mem (a + i) = 0) :
    unsignedVal mem a h K = unsignedVal mem a h n := by
  have ht : unsignedVal mem (a + n) h (K - n) = 0 := by
    apply unsignedVal_zero
    intro i hi
    simpa only [Nat.add_assoc] using hz (n + i) (by omega) (by omega)
  conv_lhs => rw [show K = n + (K - n) by omega, unsignedVal_split, ht, mul_zero, add_zero]

/-- A block whose value fits a shorter unsigned prefix has exactly that prefix value. -/
theorem unsignedVal_prefix_of_lt {mem : ℕ → ℕ} {a h K n : ℕ}
    (hv : Valid mem a h K) (hn : n ≤ K) (hu : unsignedVal mem a h K < capacity h n) :
    unsignedVal mem a h n = unsignedVal mem a h K := by
  rw [← unsignedVal_mod_prefix hv hn, Nat.mod_eq_of_lt hu]

/-- Appending one digit to a smaller remainder gives a numerator below divisor times base. -/
theorem remainder_append_lt {B R V digit : ℕ} (hR : R < V) (hx : digit < B) :
    R * B + digit < V * B := by
  have hm := Nat.mul_le_mul_right B (Nat.succ_le_of_lt hR)
  nlinarith only [hm, hx]

/-- Multiplying a value below the old capacity by one limb fits the extra-limb capacity. -/
theorem limb_product_lt_next_capacity {h K V q : ℕ}
    (hV : V < capacity h K) (hq : q < base h) : q * V < capacity h (K + 1) := by
  have hm := Nat.mul_le_mul_right (capacity h K) (Nat.succ_le_of_lt hq)
  have hv' := Nat.mul_le_mul_left q (Nat.le_of_lt hV)
  rw [capacity_succ]
  nlinarith [capacity_pos h K]

/-- Conservation below capacity forces the final carry to be zero. -/
theorem row_exact_of_lt_capacity {value out C carry : ℕ}
    (hmass : out + C * carry = value) (hvalue : value < C) : out = value := by
  have hc : carry = 0 := by
    by_contra hn
    have hm := Nat.mul_le_mul_left C (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn))
    omega
  simpa only [hc, mul_zero, add_zero] using hmass

/-- A nonnegative remainder below the old capacity fits the signed extra-limb block. -/
theorem fits_nat_extra_limb {h K R : ℕ} (hh : 0 < h) (hR : R < capacity h K) :
    Fits h (K + 1) (R : ℤ) := by
  have hB : 2 ≤ base h := Nat.succ_le_of_lt (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide))
  have hc := capacity_pos h K
  have hm := Nat.mul_le_mul_right (capacity h K) hB
  change -(capacity h (K + 1) : ℤ) ≤ 2 * (R : ℤ) ∧ 2 * (R : ℤ) < (capacity h (K + 1) : ℤ)
  rw [capacity_succ]
  have hi : 2 * R < base h * capacity h K := by omega
  constructor
  · have hc0 : (0 : ℤ) ≤ (base h * capacity h K : ℕ) := Int.natCast_nonneg _
    have hr0 : (0 : ℤ) ≤ (R : ℤ) := Int.natCast_nonneg _
    exact le_trans (neg_nonpos.mpr hc0) (mul_nonneg (by decide) hr0)
  · exact_mod_cast hi

/-- Signed subtraction and unsigned subtraction have the same residue. -/
theorem wrap_signedVal_sub (h K u v : ℕ) :
    wrap h K (signedVal h K u - signedVal h K v) = wrap h K ((u : ℤ) - (v : ℤ)) := by
  apply wrap_congr
  rw [Int.sub_emod, signedVal_emod, signedVal_emod, ← Int.sub_emod]

/-- A wrapped subtraction of unsigned values recovers their nonnegative difference when it fits. -/
theorem wrapped_unsigned_difference {h K x y : ℕ} (hy : y ≤ x)
    (hf : Fits h K ((x - y : ℕ) : ℤ)) :
    wrap h K (signedVal h K x - signedVal h K y) = (x - y : ℕ) := by
  rw [wrap_signedVal_sub, ← Int.natCast_sub hy, wrap_of_fits hf]

/-- Reading a nonnegative signed value recovers its unsigned numerator. -/
theorem unsignedVal_of_intVal_nonneg {mem : ℕ → ℕ} {a h K R : ℕ}
    (hv : Valid mem a h K) (he : intVal mem a h K = (R : ℤ)) :
    unsignedVal mem a h K = R := by
  have hn := intVal_eq_unsigned_sub_sign hv
  rw [he, ite_eq_right (by exact_mod_cast Nat.not_lt_zero R), sub_zero] at hn
  exact_mod_cast hn.symm

end MinCostFlow.Num
