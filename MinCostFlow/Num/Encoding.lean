module

public import MinCostFlow.Num.Representation
import WordRAM.Entry
import Mathlib.Tactic

/-!
# Encoding integers as limb lists

Successive division by the limb base gives a list of exactly `L` digits. Its unsigned
value is the input modulo the block capacity. Taking the nonnegative residue of a signed
integer gives its two's-complement encoding. Decoding recovers every integer in the signed
range. These lemmas supply actual encodings, rather than assuming that a valid block exists.
-/

@[expose] public section
namespace MinCostFlow.Num

/-- Exactly `L` low limbs of `n`, least significant first. -/
def digits (h : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | L + 1, n => n % base h :: digits h L (n / base h)

@[simp] theorem digits_length (h L n : ℕ) : (digits h L n).length = L := by
  induction L generalizing n with
  | zero => rfl
  | succ L ih => simp [digits, ih]

/-- Every generated digit is below the limb base. -/
theorem digits_lt (h L n : ℕ) : ∀ x ∈ digits h L n, x < base h := by
  induction L generalizing n with
  | zero => simp [digits]
  | succ L ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.mod_lt _ (base_pos h)
    · exact ih _ _ hx

/-- Truncating a digit list is reduction modulo the capacity. -/
theorem listVal_digits (h L n : ℕ) : listVal h (digits h L n) = n % capacity h L := by
  induction L generalizing n with
  | zero => exact (Nat.mod_one n).symm
  | succ L ih =>
    simp only [digits, listVal, ih, capacity_succ]
    exact Nat.mod_mul.symm

/-- The doubled form of the signed range also applies to empty blocks. -/
def Fits (h L : ℕ) (n : ℤ) : Prop :=
  -(capacity h L : ℤ) ≤ 2 * n ∧ 2 * n < (capacity h L : ℤ)

/-- Decoding a valid block is in the signed range. -/
theorem intVal_fits {mem : ℕ → ℕ} {a h L : ℕ} (hv : Valid mem a h L) :
    Fits h L (intVal mem a h L) := by
  have hu := unsignedVal_lt hv
  have hc := capacity_pos h L
  dsimp only [Fits, intVal, signedVal]
  split_ifs <;> omega

/-- The nonnegative residue used for a two's-complement encoding. -/
def residue (h L : ℕ) (n : ℤ) : ℕ := (n % (capacity h L : ℤ)).toNat

 theorem residue_lt (h L : ℕ) (n : ℤ) : residue h L n < capacity h L := by
  have hp : (0 : ℤ) < capacity h L := by exact_mod_cast capacity_pos h L
  exact (Int.toNat_lt (Int.emod_nonneg n (ne_of_gt hp))).mpr (Int.emod_lt_of_pos n hp)

/-- A list encoding of any integer, with wrap-around outside the signed range. -/
def encodeLimbs (h L : ℕ) (n : ℤ) : List ℕ := digits h L (residue h L n)

@[simp] theorem encodeLimbs_length (h L : ℕ) (n : ℤ) :
    (encodeLimbs h L n).length = L := digits_length _ _ _

 theorem encodeLimbs_lt (h L : ℕ) (n : ℤ) :
    ∀ x ∈ encodeLimbs h L n, x < base h := digits_lt _ _ _

/-- The unsigned value of an encoded signed integer is its nonnegative residue. -/
theorem listVal_encodeLimbs (h L : ℕ) (n : ℤ) :
    listVal h (encodeLimbs h L n) = residue h L n := by
  rw [encodeLimbs, listVal_digits, Nat.mod_eq_of_lt (residue_lt h L n)]

/-- Signed decoding inverts the residue operation in the signed range. -/
theorem signedVal_residue {h L : ℕ} {n : ℤ} (hn : Fits h L n) :
    signedVal h L (residue h L n) = n := by
  have hp : (0 : ℤ) < capacity h L := by exact_mod_cast capacity_pos h L
  have hc : ((residue h L n : ℕ) : ℤ) = n % (capacity h L : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg n (ne_of_gt hp))
  obtain ⟨hlo, hhi⟩ := hn
  by_cases hneg : n < 0
  · have hm : n % (capacity h L : ℤ) = n + capacity h L := by
      rw [← Int.add_emod_right n (capacity h L : ℤ)]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    have ht : capacity h L ≤ 2 * residue h L n := by omega
    simp only [signedVal, ite_eq_left ht]
    omega
  · have hm : n % (capacity h L : ℤ) = n :=
      Int.emod_eq_of_lt (by omega) (by omega)
    have ht : ¬ capacity h L ≤ 2 * residue h L n := by omega
    simp only [signedVal, ite_eq_right ht, sub_zero]
    omega

/-- Storing the encoding of an integer in range recovers that integer. -/
theorem intVal_encodeLimbs {mem : ℕ → ℕ} {a h L : ℕ} {n : ℤ}
    (hx : WordRAM.ListAt mem a (encodeLimbs h L n)) (hn : Fits h L n) :
    intVal mem a h L = n := by
  have hu := unsignedVal_listAt (h := h) hx
  rw [encodeLimbs_length, listVal_encodeLimbs] at hu
  rw [intVal, hu, signedVal_residue hn]

/-- Any stored encoding is valid, whether or not the integer fits. -/
theorem valid_encodeLimbs {mem : ℕ → ℕ} {a h L : ℕ} {n : ℤ}
    (hx : WordRAM.ListAt mem a (encodeLimbs h L n)) : Valid mem a h L := by
  have hv := valid_listAt hx (encodeLimbs_lt h L n)
  simpa only [encodeLimbs_length] using hv

/-- The signed integer obtained by reducing an arbitrary integer to an `L`-limb block. -/
def wrap (h L : ℕ) (n : ℤ) : ℤ := signedVal h L (residue h L n)

 theorem wrap_of_fits {h L : ℕ} {n : ℤ} (hn : Fits h L n) : wrap h L n = n :=
  signedVal_residue hn

/-- Signed decoding changes the unsigned integer only by a multiple of the capacity. -/
theorem signedVal_emod (h L u : ℕ) :
    signedVal h L u % (capacity h L : ℤ) = (u : ℤ) % (capacity h L : ℤ) := by
  unfold signedVal
  split_ifs
  · exact Int.sub_emod_right _ _
  · simp only [sub_zero]

/-- Adding signed decodings has the same residue as adding their unsigned values. -/
theorem residue_signedVal_add (h L u v c : ℕ) :
    residue h L (signedVal h L u + signedVal h L v + (c : ℤ)) =
      (u + v + c) % capacity h L := by
  have he : (signedVal h L u + signedVal h L v + (c : ℤ)) % (capacity h L : ℤ) =
      ((u : ℤ) + (v : ℤ) + (c : ℤ)) % (capacity h L : ℤ) := by
    rw [Int.add_emod, Int.add_emod (signedVal h L u) (signedVal h L v),
      signedVal_emod, signedVal_emod]
    rw [Int.add_emod ((u : ℤ) + v) c, Int.add_emod (u : ℤ) v]
  unfold residue
  rw [he, ← Int.natCast_add, ← Int.natCast_add, ← Int.natCast_emod, Int.toNat_natCast]

/-- Negating a signed decoding negates its unsigned residue modulo capacity. -/
theorem residue_signedVal_neg {h L u : ℕ} (hu : u < capacity h L) :
    residue h L (-signedVal h L u) = (capacity h L - u) % capacity h L := by
  have he : (-signedVal h L u) % (capacity h L : ℤ) =
      ((capacity h L - u : ℕ) : ℤ) % (capacity h L : ℤ) := by
    rw [Int.natCast_sub (Nat.le_of_lt hu)]
    unfold signedVal
    split_ifs
    · congr 1
      omega
    · simp only [sub_zero]
      rw [show (capacity h L : ℤ) - u = -(u : ℤ) + capacity h L by ring,
        Int.add_emod_right]
  unfold residue
  rw [he, ← Int.natCast_emod, Int.toNat_natCast]

/-- Every integer in range has a valid memory representation. -/
theorem exists_encoding (h L : ℕ) (n : ℤ) (hn : Fits h L n) :
    ∃ mem : ℕ → ℕ, Valid mem 0 h L ∧ intVal mem 0 h L = n := by
  have hx := WordRAM.listAt_initMem (encodeLimbs h L n)
  exact ⟨_, valid_encodeLimbs hx, intVal_encodeLimbs hx hn⟩

/-- Wrapping preserves the residue of an integer. -/
theorem wrap_emod (h L : ℕ) (n : ℤ) :
    wrap h L n % (capacity h L : ℤ) = n % (capacity h L : ℤ) := by
  rw [wrap, signedVal_emod]
  have hp : (0 : ℤ) < capacity h L := by exact_mod_cast capacity_pos h L
  have hr : ((residue h L n : ℕ) : ℤ) = n % (capacity h L : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg n (ne_of_gt hp))
  rw [hr, Int.emod_emod]

/-- Equal residues give the same wrapped integer. -/
theorem wrap_congr {h L : ℕ} {x y : ℤ}
    (he : x % (capacity h L : ℤ) = y % (capacity h L : ℤ)) : wrap h L x = wrap h L y := by
  simp only [wrap, residue, he]

/-- An already wrapped summand can be used without changing the final wrapped sum. -/
theorem wrap_add_wrap (h L : ℕ) (x y : ℤ) :
    wrap h L (x + wrap h L y) = wrap h L (x + y) := by
  apply wrap_congr
  rw [Int.add_emod, wrap_emod, ← Int.add_emod]

/-- A nonnegative integer has the usual natural remainder as its residue. -/
theorem residue_natCast (h L n : ℕ) : residue h L (n : ℤ) = n % capacity h L := by
  simp only [residue, ← Int.natCast_emod, Int.toNat_natCast]

/-- Loading the low natural digits gives the wrapped signed integer. -/
theorem wrap_natCast (h L n : ℕ) :
    wrap h L (n : ℤ) = signedVal h L (n % capacity h L) := by
  rw [wrap, residue_natCast]

/-- Negating an already wrapped integer preserves the final wrapped negative. -/
theorem wrap_neg_wrap (h L : ℕ) (n : ℤ) :
    wrap h L (-wrap h L n) = wrap h L (-n) := by
  apply wrap_congr
  exact Int.ModEq.neg (wrap_emod h L n)

end MinCostFlow.Num
