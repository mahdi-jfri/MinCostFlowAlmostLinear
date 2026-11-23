module

public import MinCostFlow.Num.Encoding
import MinCostFlow.Num.WordBounds
import Mathlib.Tactic

/-!
# Splitting shifts into whole limbs and remaining bits

The low limbs are a remainder modulo their capacity. This lets a whole-limb shift be
combined with a one-limb scaling operation. The identities below also relate the
unsigned output to wrapped signed multiplication by a power of two.
-/

public section
namespace MinCostFlow.Num

/-- The capacities multiply when two blocks are concatenated. -/
theorem capacity_add (h k L : ℕ) : capacity h (k + L) = capacity h k * capacity h L :=
  pow_add _ _ _

/-- Split a block after its first `k` limbs. -/
theorem unsignedVal_split (mem : ℕ → ℕ) (a h k L : ℕ) :
    unsignedVal mem a h (k + L) = unsignedVal mem a h k +
      capacity h k * unsignedVal mem (a + k) h L := by
  induction k generalizing a with
  | zero => simp [unsignedVal, capacity]
  | succ k ih =>
    rw [show (k + 1) + L = (k + L) + 1 by omega, unsignedVal, ih,
      unsignedVal, capacity_succ]
    rw [show a + 1 + k = a + (k + 1) by omega]
    ring

/-- The low `k` limbs are the unsigned value modulo their capacity. -/
theorem unsignedVal_mod_prefix {mem : ℕ → ℕ} {a h L k : ℕ}
    (hv : Valid mem a h L) (hk : k ≤ L) :
    unsignedVal mem a h L % capacity h k = unsignedVal mem a h k := by
  have hp : unsignedVal mem a h k < capacity h k :=
    unsignedVal_lt (fun i hi => hv i (lt_of_lt_of_le hi hk))
  rw [show L = k + (L - k) by omega, unsignedVal_split,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]

/-- A bit shift is a whole-limb shift followed by a power of two below the base. -/
theorem two_pow_shift_split (h s : ℕ) :
    2 ^ s = capacity h (s / h) * 2 ^ (s % h) := by
  rw [capacity_eq_two_pow, ← pow_add]
  congr 1
  have he := Nat.mod_add_div s h
  omega

/-- A block with `q` zero low limbs followed by scaled source digits has the shifted value. -/
theorem unsignedVal_left_shift {mem mem' : ℕ → ℕ} {a heap h L q k : ℕ}
    (hv : Valid mem a h L) (hq : q ≤ L)
    (hz : ∀ i < q, mem' (heap + i) = 0)
    (hl : WordRAM.ListAt mem' (heap + q)
      (digits h (L - q) (unsignedVal mem a h (L - q) * k))) :
    unsignedVal mem' heap h L =
      (unsignedVal mem a h L * (capacity h q * k)) % capacity h L := by
  have ho := unsignedVal_listAt (h := h) hl
  rw [digits_length, listVal_digits] at ho
  have he : unsignedVal mem a h L % capacity h (L - q) =
      unsignedVal mem a h (L - q) := unsignedVal_mod_prefix hv (Nat.sub_le _ _)
  have hm : (unsignedVal mem a h L * k) % capacity h (L - q) =
      (unsignedVal mem a h (L - q) * k) % capacity h (L - q) := by
    conv_lhs => rw [Nat.mul_mod, he]
    conv_rhs => rw [Nat.mul_mod, Nat.mod_eq_of_lt
      (unsignedVal_lt (fun i hi => hv i (lt_of_lt_of_le hi (Nat.sub_le _ _))))]
  have hout : unsignedVal mem' heap h L = capacity h q *
      ((unsignedVal mem a h (L - q) * k) % capacity h (L - q)) := by
    conv_lhs => rw [show L = q + (L - q) by omega, unsignedVal_split]
    rw [unsignedVal_zero hz, zero_add, ho]
  rw [hout]
  have hc : capacity h L = capacity h q * capacity h (L - q) := by
    rw [← capacity_add]
    congr 1
    omega
  rw [hc, show unsignedVal mem a h L * (capacity h q * k) =
    capacity h q * (unsignedVal mem a h L * k) by ring, Nat.mul_mod_mul_left, hm]

/-- Multiplication of a signed decoding preserves unsigned residues. -/
theorem residue_signedVal_mul (h L u k : ℕ) :
    residue h L (signedVal h L u * (k : ℤ)) = (u * k) % capacity h L := by
  have he : (signedVal h L u * (k : ℤ)) % (capacity h L : ℤ) =
      ((u : ℤ) * k) % (capacity h L : ℤ) := by
    rw [Int.mul_emod, signedVal_emod, ← Int.mul_emod]
  rw [residue, he, ← Int.natCast_mul, ← Int.natCast_emod, Int.toNat_natCast]

/-- An unsigned modular product decodes as the wrapped signed product. -/
theorem signedVal_mul_mod (h L u k : ℕ) :
    signedVal h L ((u * k) % capacity h L) = wrap h L (signedVal h L u * (k : ℤ)) := by
  rw [wrap, residue_signedVal_mul]

/-- A low prefix is the wrapped signed value of the full block at the smaller width. -/
theorem intVal_prefix_wrap {mem : ℕ → ℕ} {a h K L : ℕ}
    (hv : Valid mem a h K) (hLK : L ≤ K) :
    intVal mem a h L = wrap h L (intVal mem a h K) := by
  have hcap : capacity h K = capacity h L * capacity h (K - L) := by
    rw [← capacity_add, show L + (K - L) = K by omega]
  have hd : capacity h L ∣ capacity h K := ⟨capacity h (K - L), hcap⟩
  have hcmod : (capacity h K : ℤ) % (capacity h L : ℤ) = 0 := by
    rw [← Int.natCast_emod, Nat.mod_eq_zero_of_dvd hd]
    rfl
  have he : intVal mem a h K % (capacity h L : ℤ) =
      (unsignedVal mem a h K : ℤ) % (capacity h L : ℤ) := by
    dsimp only [intVal, signedVal]
    split_ifs
    · rw [Int.sub_emod, hcmod, sub_zero, Int.emod_emod]
    · rw [sub_zero]
  have hr : residue h L (intVal mem a h K) = unsignedVal mem a h L := by
    rw [residue, he, ← Int.natCast_emod, Int.toNat_natCast, unsignedVal_mod_prefix hv hLK]
  rw [wrap, hr, intVal]

end MinCostFlow.Num
