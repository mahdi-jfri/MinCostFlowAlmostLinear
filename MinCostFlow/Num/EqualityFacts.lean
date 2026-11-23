module

public import MinCostFlow.Num.Representation
import Mathlib.Tactic

/-!
# Uniqueness of signed limb encodings

Signed decoding is injective within one unsigned capacity. The base expansion is also
unique when every digit is below the base. Together these facts justify comparing limb
blocks directly, without reconstructing a potentially many-word integer on the machine.
-/

public section
namespace MinCostFlow.Num

/-- Signed decoding is injective on the unsigned range of a fixed block length. -/
theorem signedVal_injective {h L u v : ℕ} (hu : u < capacity h L)
    (hv : v < capacity h L) : signedVal h L u = signedVal h L v ↔ u = v := by
  dsimp only [signedVal]
  split_ifs <;> omega

/-- Equality of signed values is equality of unsigned values for valid blocks. -/
theorem intVal_eq_iff_unsigned {mem mem' : ℕ → ℕ} {a d h L : ℕ}
    (ha : Valid mem a h L) (hd : Valid mem' d h L) :
    intVal mem a h L = intVal mem' d h L ↔
      unsignedVal mem a h L = unsignedVal mem' d h L :=
  signedVal_injective (unsignedVal_lt ha) (unsignedVal_lt hd)

/-- Equal base expansions have equal low limbs and equal tails. -/
theorem unsignedVal_eq_succ_iff {mem mem' : ℕ → ℕ} {a d h L : ℕ}
    (ha : mem a < base h) (hd : mem' d < base h) :
    unsignedVal mem a h (L + 1) = unsignedVal mem' d h (L + 1) ↔
      mem a = mem' d ∧ unsignedVal mem (a + 1) h L = unsignedVal mem' (d + 1) h L := by
  constructor
  · intro he
    have hmod := congrArg (fun n => n % base h) he
    simp only [unsignedVal, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hd] at hmod
    refine ⟨hmod, ?_⟩
    have hb := base_pos h
    simp only [unsignedVal, hmod] at he
    nlinarith
  · rintro ⟨hh, ht⟩
    simp only [unsignedVal, hh, ht]

/-- Testing equality can inspect one limb and then recurse on the tails. -/
theorem intVal_eq_succ_iff {mem mem' : ℕ → ℕ} {a d h L : ℕ}
    (ha : Valid mem a h (L + 1)) (hd : Valid mem' d h (L + 1)) :
    intVal mem a h (L + 1) = intVal mem' d h (L + 1) ↔
      mem a = mem' d ∧ intVal mem (a + 1) h L = intVal mem' (d + 1) h L := by
  rw [intVal_eq_iff_unsigned ha hd,
    unsignedVal_eq_succ_iff (valid_succ.mp ha).1 (valid_succ.mp hd).1,
    intVal_eq_iff_unsigned (valid_succ.mp ha).2 (valid_succ.mp hd).2]

/-- A shared fixed-point precision preserves and reflects equality. -/
theorem fixVal_eq_iff {mem mem' : ℕ → ℕ} {a d h L P : ℕ} :
    fixVal mem a h L P = fixVal mem' d h L P ↔ intVal mem a h L = intVal mem' d h L := by
  unfold fixVal
  rw [div_left_inj' (pow_ne_zero P (by norm_num : (2 : ℝ) ≠ 0))]
  exact Int.cast_inj

end MinCostFlow.Num
