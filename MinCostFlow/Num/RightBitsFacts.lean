module

public import MinCostFlow.Num.Encoding
import Mathlib.Tactic

/-!
# Dividing adjacent limbs by a factor of the base

A remaining-bit right shift divides by a positive factor of the limb base. Each output
limb combines the quotient of its current limb with the remainder of the next one.
An extra source limb supplies the high bits at the boundary.
-/

public section
namespace MinCostFlow.Num

/-- Division by a factor of the base splits into adjacent output limbs. -/
theorem div_limb_pair {B t x V : ℕ} (hB : 0 < B) (ht : 0 < t)
    (hd : t ∣ B) (hx : x < B) :
    ((x + B * V) / t) % B = x / t + (B / t) * (V % t) ∧
    ((x + B * V) / t) / B = V / t ∧
    x / t + (B / t) * (V % t) < B := by
  have hk : 0 < B / t := Nat.div_pos (Nat.le_of_dvd hB hd) ht
  have he : B / t * t = B := Nat.div_mul_cancel hd
  have hxq : x / t < B / t := by
    apply (Nat.div_lt_iff_lt_mul ht).mpr
    rwa [he]
  have hquot : (x + B * V) / t = x / t + (B / t) * V := by
    have heq : x + B * V = x + t * ((B / t) * V) := by
      conv_lhs => rw [← he]
      ring
    rw [heq, Nat.add_mul_div_left _ _ ht]
  have hmod : ((x + B * V) / t) % B = x / t + (B / t) * (V % t) := by
    rw [hquot]
    conv_lhs => arg 2; rw [← he]
    rw [Nat.mod_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hxq,
      Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hxq, zero_add]
  refine ⟨hmod, ?_, ?_⟩
  · rw [Nat.div_div_eq_div_mul, Nat.mul_comm t B, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hx, zero_add]
  · rw [← hmod]
    exact Nat.mod_lt _ hB

/-- A multiple of the base contributes zero remainder modulo a factor of that base. -/
theorem mod_factor_of_base {B t x V : ℕ} (hd : t ∣ B) :
    (x + B * V) % t = x % t := by
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hd, zero_mul,
    Nat.zero_mod, add_zero, Nat.mod_mod]

/-- The shifted digit list uses the next source limb and then recurses on the tail. -/
theorem digits_unsigned_right_bits {mem : ℕ → ℕ} {a h L t : ℕ}
    (ht : 0 < t) (hd : t ∣ base h) (hv : Valid mem a h (L + 2)) :
    digits h (L + 1) (unsignedVal mem a h (L + 2) / t) =
      (mem a / t + (base h / t) * (mem (a + 1) % t)) ::
        digits h L (unsignedVal mem (a + 1) h (L + 1) / t) := by
  have hh : mem a < base h := (valid_succ.mp hv).1
  have hp := div_limb_pair (base_pos h) ht hd hh (V := unsignedVal mem (a + 1) h (L + 1))
  have hm : unsignedVal mem (a + 1) h (L + 1) % t = mem (a + 1) % t := by
    rw [unsignedVal]
    exact mod_factor_of_base hd
  rw [show unsignedVal mem a h (L + 2) = mem a + base h * unsignedVal mem (a + 1) h (L + 1) by rfl,
    digits, hp.1, hp.2.1, hm]

end MinCostFlow.Num
