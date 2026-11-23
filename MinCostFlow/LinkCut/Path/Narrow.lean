module

public import MinCostFlow.Num.Encoding

/-!
# Reading a wide block in fewer limbs

The tree keeps numbers in `K` limbs, the interface in `L ≤ K` limbs. The low `L` limbs of a
`K`-limb block, read as an `L`-limb block, give the number modulo the smaller capacity
(`intVal_low`). So a number that fits in `L` limbs is read exactly from its low limbs
(`intVal_low_of_fits`), and the read-out is a plain copy.
-/

@[expose] public section

namespace MinCostFlow.Num

theorem capacity_add (h L M : ℕ) : capacity h (L + M) = capacity h L * capacity h M := by
  simp only [capacity, pow_add]

/-- A block splits into its low `L` limbs and the rest. -/
theorem unsignedVal_add (mem : ℕ → ℕ) (h : ℕ) :
    ∀ (L M a : ℕ), unsignedVal mem a h (L + M) =
      unsignedVal mem a h L + capacity h L * unsignedVal mem (a + L) h M
  | 0, M, a => by simp [unsignedVal]
  | L + 1, M, a => by
    rw [show L + 1 + M = (L + M) + 1 by omega, unsignedVal, unsignedVal,
      unsignedVal_add mem h L M (a + 1), capacity_succ,
      show a + 1 + L = a + (L + 1) by omega]
    ring

/-- The low `L` limbs of a `K`-limb block hold the number modulo `capacity h L`. -/
theorem intVal_low {mem : ℕ → ℕ} {a h L K : ℕ} (hLK : L ≤ K) (hv : Valid mem a h K) :
    intVal mem a h L = wrap h L (intVal mem a h K) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hLK
  have hvL : Valid mem a h L := fun i hi => hv i (by omega)
  have huL := unsignedVal_lt hvL
  have hcL := capacity_pos h L
  have hsplit := unsignedVal_add mem h L M a
  rw [intVal, wrap]
  congr 1
  have hcK : (capacity h (L + M) : ℤ) = capacity h L * capacity h M := by
    rw [capacity_add]; push_cast; ring
  have hmod : intVal mem a h (L + M) % (capacity h L : ℤ) =
      (unsignedVal mem a h L : ℤ) := by
    rw [intVal, signedVal, hsplit]
    push_cast
    rw [hcK]
    have hlt : (unsignedVal mem a h L : ℤ) % capacity h L = unsignedVal mem a h L :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast huL)
    split_ifs
    · rw [show (unsignedVal mem a h L : ℤ) + capacity h L * unsignedVal mem (a + L) h M -
          capacity h L * capacity h M = unsignedVal mem a h L +
          capacity h L * (unsignedVal mem (a + L) h M - capacity h M) by ring,
        Int.add_mul_emod_self_left, hlt]
    · rw [sub_zero, Int.add_mul_emod_self_left, hlt]
  simp only [residue, hmod, Int.toNat_natCast]

/-- A number that fits in `L` limbs is read exactly from the low `L` limbs of its block. -/
theorem intVal_low_of_fits {mem : ℕ → ℕ} {a h L K : ℕ} (hLK : L ≤ K) (hv : Valid mem a h K)
    (hf : Fits h L (intVal mem a h K)) : intVal mem a h L = intVal mem a h K := by
  rw [intVal_low hLK hv, wrap_of_fits hf]

end MinCostFlow.Num
