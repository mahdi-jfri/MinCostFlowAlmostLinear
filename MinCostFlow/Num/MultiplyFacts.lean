module

public import MinCostFlow.Num.Encoding
public import MinCostFlow.Num.ExtendCopy
import MinCostFlow.Num.ExtendFacts
import MinCostFlow.Num.ShiftFacts
import MinCostFlow.Num.ShiftRightFacts
import Mathlib.Tactic

/-!
# Signed schoolbook multiplication

Sign extension preserves the source integer modulo the larger capacity. Thus a
schoolbook product of extended unsigned encodings decodes as the wrapped signed
product. The product of two `L`-limb signed integers always fits in `2L` limbs.
-/

public section
namespace MinCostFlow.Num

/-- A sign-extended block has the original signed residue at its new capacity. -/
theorem extended_residue {mem mem' : ℕ → ℕ} {a out h L K : ℕ}
    (hv : Valid mem a h L) (hLK : L ≤ K)
    (hl : WordRAM.ListAt mem' out
      (extendedLimbs mem a (if intVal mem a h L < 0 then base h - 1 else 0) L K)) :
    (unsignedVal mem' out h K : ℤ) % (capacity h K : ℤ) =
      intVal mem a h L % (capacity h K : ℤ) := by
  have hu := unsignedVal_listAt (h := h) hl
  rw [extendedLimbs_length] at hu
  have hn := intVal_eq_unsigned_sub_sign hv
  by_cases hneg : intVal mem a h L < 0
  · rw [ite_eq_left hneg] at hu hn
    have he := listVal_extended_max (mem := mem) (a := a) (h := h) hLK
    rw [← hu] at he
    have he' : (unsignedVal mem' out h K : ℤ) + (capacity h L : ℤ) =
        (unsignedVal mem a h L : ℤ) + (capacity h K : ℤ) := by exact_mod_cast he
    have hv' : (unsignedVal mem' out h K : ℤ) = intVal mem a h L + capacity h K := by omega
    rw [hv', Int.add_emod_right]
  · rw [ite_eq_right hneg, listVal_extended_zero hLK] at hu
    rw [ite_eq_right hneg, sub_zero] at hn
    rw [hu, ← hn]

/-- Products of signed values in an `L`-limb range fit the doubled range. -/
theorem fits_mul_double {h L : ℕ} {x y : ℤ} (hx : Fits h L x) (hy : Fits h L y) :
    Fits h (2 * L) (x * y) := by
  have hc : (0 : ℤ) < capacity h L := by exact_mod_cast capacity_pos h L
  obtain ⟨hxl, hxu⟩ := hx
  obtain ⟨hyl, hyu⟩ := hy
  have hxprod := mul_nonneg (show (0 : ℤ) ≤ (capacity h L : ℤ) + 2 * x by omega)
    (show (0 : ℤ) ≤ (capacity h L : ℤ) - 2 * x by omega)
  have hyprod := mul_nonneg (show (0 : ℤ) ≤ (capacity h L : ℤ) + 2 * y by omega)
    (show (0 : ℤ) ≤ (capacity h L : ℤ) - 2 * y by omega)
  have hx2 : 4 * x ^ 2 ≤ (capacity h L : ℤ) ^ 2 := by nlinarith only [hxprod]
  have hy2 : 4 * y ^ 2 ≤ (capacity h L : ℤ) ^ 2 := by nlinarith only [hyprod]
  have hmhi : 4 * x * y ≤ (capacity h L : ℤ) ^ 2 := by nlinarith only [hx2, hy2, sq_nonneg (x - y)]
  have hmlo : -(capacity h L : ℤ) ^ 2 ≤ 4 * x * y := by nlinarith only [hx2, hy2, sq_nonneg (x + y)]
  have hc2 : (0 : ℤ) < (capacity h L : ℤ) ^ 2 := sq_pos_of_pos hc
  have he : capacity h (2 * L) = capacity h L * capacity h L := by
    rw [show 2 * L = L + L by omega, capacity_add]
  change -(capacity h (2 * L) : ℤ) ≤ 2 * (x * y) ∧ 2 * (x * y) < (capacity h (2 * L) : ℤ)
  rw [he]
  push_cast
  constructor <;> nlinarith only [hmhi, hmlo, hc2]

/-- An unsigned modular product decodes as the signed product determined by its source residues. -/
theorem intVal_product_of_residues {mem : ℕ → ℕ} {out h K u v : ℕ} {x y : ℤ}
    (hx : (u : ℤ) % (capacity h K : ℤ) = x % (capacity h K : ℤ))
    (hy : (v : ℤ) % (capacity h K : ℤ) = y % (capacity h K : ℤ))
    (ho : unsignedVal mem out h K = (u * v) % capacity h K) :
    intVal mem out h K = wrap h K (x * y) := by
  have hm : ((u : ℤ) * v) % (capacity h K : ℤ) = (x * y) % (capacity h K : ℤ) :=
    Int.ModEq.mul hx hy
  have hr : residue h K (x * y) = (u * v) % capacity h K := by
    rw [residue, ← hm, ← Int.natCast_mul, ← Int.natCast_emod, Int.toNat_natCast]
  rw [intVal, ho, wrap, hr]

end MinCostFlow.Num
