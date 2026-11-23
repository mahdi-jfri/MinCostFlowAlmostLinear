module

public import MinCostFlow.Num.ExtendFacts
import MinCostFlow.Num.SignFacts
import MinCostFlow.Num.ShiftFacts
import Mathlib.Tactic

/-!
# Signed values in arithmetic right shifts

Dropping low limbs is integer division by their capacity. Filling high limbs with the
sign limb preserves this quotient as a signed integer. One extra sign limb contributes
a multiple of the output capacity even after division by the remaining-bit factor.
-/

public section
namespace MinCostFlow.Num

/-- Signed decoding subtracts the capacity exactly for a negative block. -/
theorem intVal_eq_unsigned_sub_sign {mem : ℕ → ℕ} {a h L : ℕ} (hv : Valid mem a h L) :
    intVal mem a h L = (unsignedVal mem a h L : ℤ) -
      if intVal mem a h L < 0 then (capacity h L : ℤ) else 0 := by
  simp only [intVal_neg_iff hv]
  rfl

/-- Dropping a low prefix gives the signed quotient by that prefix's capacity. -/
theorem intVal_tail_div {mem : ℕ → ℕ} {a h L q : ℕ}
    (hv : Valid mem a h L) (hq : q ≤ L) :
    intVal mem a h L / (capacity h q : ℤ) =
      (unsignedVal mem (a + q) h (L - q) : ℤ) -
        if intVal mem a h L < 0 then (capacity h (L - q) : ℤ) else 0 := by
  have hlo : unsignedVal mem a h q < capacity h q :=
    unsignedVal_lt (fun i hi => hv i (lt_of_lt_of_le hi hq))
  have hc : capacity h L = capacity h q * capacity h (L - q) := by
    rw [← capacity_add, show q + (L - q) = L by omega]
  have hu : unsignedVal mem a h L = unsignedVal mem a h q +
      capacity h q * unsignedVal mem (a + q) h (L - q) := by
    conv_lhs => rw [show L = q + (L - q) by omega, unsignedVal_split]
  have hp : (0 : ℤ) < capacity h q := by exact_mod_cast capacity_pos h q
  have he : intVal mem a h L = (unsignedVal mem a h q : ℤ) +
      (capacity h q : ℤ) * ((unsignedVal mem (a + q) h (L - q) : ℤ) -
        if intVal mem a h L < 0 then (capacity h (L - q) : ℤ) else 0) := by
    conv_lhs => rw [intVal_eq_unsigned_sub_sign hv]
    rw [hu, hc]
    push_cast
    split_ifs <;> ring
  conv_lhs => rw [he, Int.add_mul_ediv_left _ _ (ne_of_gt hp),
    Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hlo), zero_add]

/-- Dividing a sign-extension capacity leaves a multiple of the output capacity. -/
theorem wrap_ediv_add_capacity {h L t : ℕ} (ht : 0 < t) (hd : t ∣ base h) (n : ℤ) :
    wrap h L ((n + (capacity h (L + 1) : ℤ)) / (t : ℤ)) = wrap h L (n / (t : ℤ)) := by
  have he : capacity h (L + 1) = t * ((base h / t) * capacity h L) := by
    calc
      capacity h (L + 1) = base h * capacity h L := capacity_succ _ _
      _ = (base h / t * t) * capacity h L := by rw [Nat.div_mul_cancel hd]
      _ = t * ((base h / t) * capacity h L) := by ring
  have hp : (0 : ℤ) < t := by exact_mod_cast ht
  have he' : (capacity h (L + 1) : ℤ) = (t : ℤ) * ((base h / t : ℕ) * (capacity h L : ℤ)) := by
    exact_mod_cast he
  rw [he', Int.add_mul_ediv_left _ _ (ne_of_gt hp)]
  apply wrap_congr
  exact Int.add_mul_emod_self_right _ _ _

private theorem ediv_of_bounded {n C D : ℤ} (hC : 0 < C) (hD : C ≤ D)
    (hn : -C ≤ n ∧ n < C) : n / D = if n < 0 then -1 else 0 := by
  have hp : 0 < D := lt_of_lt_of_le hC hD
  split_ifs with hneg
  · apply (Int.ediv_eq_iff_of_pos hp).mpr
    constructor <;> omega
  · exact Int.ediv_eq_zero_of_lt (by omega) (by omega)

/-- A divisor at least the capacity leaves only the sign of a signed block. -/
theorem intVal_div_large {mem : ℕ → ℕ} {a h L : ℕ} {D : ℤ}
    (hv : Valid mem a h L) (hD : (capacity h L : ℤ) ≤ D) :
    intVal mem a h L / D = if intVal mem a h L < 0 then -1 else 0 := by
  exact ediv_of_bounded (by exact_mod_cast capacity_pos h L) hD (intVal_bounds hv)

/-- The unsigned value of the sign-extended scratch block differs from the signed
whole-limb quotient only by its own capacity. -/
theorem extended_scratch_value {mem scratch : ℕ → ℕ} {a h L q heap : ℕ}
    (hv : Valid mem a h L) (hq : q ≤ L)
    (hl : WordRAM.ListAt scratch heap
      (extendedLimbs mem (a + q) (if intVal mem a h L < 0 then base h - 1 else 0)
        (L - q) (L + 1))) :
    (unsignedVal scratch heap h (L + 1) : ℤ) =
      intVal mem a h L / (capacity h q : ℤ) +
        if intVal mem a h L < 0 then (capacity h (L + 1) : ℤ) else 0 := by
  have hu := unsignedVal_listAt (h := h) hl
  rw [extendedLimbs_length] at hu
  rw [intVal_tail_div hv hq]
  split_ifs with hn
  · rw [ite_eq_left hn] at hu
    have he := listVal_extended_max (mem := mem) (a := a + q) (h := h)
      (M := L - q) (K := L + 1) (by omega)
    rw [← hu] at he
    have he' : (unsignedVal scratch heap h (L + 1) : ℤ) + (capacity h (L - q) : ℤ) =
        (unsignedVal mem (a + q) h (L - q) : ℤ) + (capacity h (L + 1) : ℤ) := by
      exact_mod_cast he
    omega
  · rw [ite_eq_right hn, listVal_extended_zero (by omega)] at hu
    simp only [hu, sub_zero, add_zero]

/-- The selected prefix length handles both ordinary and saturating whole-limb shifts. -/
theorem dropped_division {mem : ℕ → ℕ} {a h L q t : ℕ}
    (hv : Valid mem a h L) (ht : 0 < t) :
    (intVal mem a h L / (capacity h (L - (L - q)) : ℤ)) / (t : ℤ) =
      intVal mem a h L / ((capacity h q : ℤ) * (t : ℤ)) := by
  by_cases hq : q ≤ L
  · rw [show L - (L - q) = q by omega, Int.ediv_ediv_of_nonneg (Int.natCast_nonneg _)]
  · have hq' : L ≤ q := by omega
    have hc : capacity h L ≤ capacity h q := Nat.pow_le_pow_right (base_pos h) hq'
    have htp : (1 : ℤ) ≤ t := by exact_mod_cast ht
    have hcp : (0 : ℤ) < capacity h q := by exact_mod_cast capacity_pos h q
    have hm : (capacity h L : ℤ) ≤ (capacity h q : ℤ) * (t : ℤ) := by
      have hc' : (capacity h L : ℤ) ≤ capacity h q := by exact_mod_cast hc
      nlinarith
    rw [show L - (L - q) = L by omega, intVal_div_large hv le_rfl, intVal_div_large hv hm]
    split_ifs with hn
    · apply (Int.ediv_eq_iff_of_pos (by exact_mod_cast ht)).mpr
      constructor <;> omega
    · simp

/-- A right-bit quotient of the sign-extended scratch block has the desired signed residue. -/
theorem scratch_right_shift_value {mem scratch : ℕ → ℕ} {a h L s heap : ℕ}
    (hh : 0 < h) (hv : Valid mem a h L)
    (hl : WordRAM.ListAt scratch heap
      (extendedLimbs mem (a + (L - (L - s / h)))
        (if intVal mem a h L < 0 then base h - 1 else 0)
        (L - (L - (L - s / h))) (L + 1))) :
    wrap h L ((unsignedVal scratch heap h (L + 1) : ℤ) / (2 : ℤ) ^ (s % h)) =
      wrap h L (intVal mem a h L / (2 : ℤ) ^ s) := by
  have ht : 0 < 2 ^ (s % h) := pow_pos (by decide) _
  have hd : 2 ^ (s % h) ∣ base h := Nat.pow_dvd_pow 2 (Nat.le_of_lt (Nat.mod_lt _ hh))
  have he := extended_scratch_value hv (Nat.sub_le _ _) hl
  rw [he]
  have hpow : ((2 ^ (s % h) : ℕ) : ℤ) = (2 : ℤ) ^ (s % h) := by norm_cast
  have hdrop := dropped_division (q := s / h) hv ht
  rw [hpow] at hdrop
  have hden : (capacity h (s / h) : ℤ) * (2 : ℤ) ^ (s % h) = (2 : ℤ) ^ s := by
    exact_mod_cast (two_pow_shift_split h s).symm
  rw [hden] at hdrop
  split_ifs
  · rw [← hpow, wrap_ediv_add_capacity ht hd, hpow, hdrop]
  · rw [add_zero, hdrop]

/-- Dividing by a positive integer keeps a signed value in the same representable range. -/
theorem fits_ediv {h L : ℕ} {n t : ℤ} (hn : Fits h L n) (ht : 0 < t) :
    Fits h L (n / t) := by
  have hc : (0 : ℤ) < capacity h L := by exact_mod_cast capacity_pos h L
  obtain ⟨hlo, hhi⟩ := hn
  change -(capacity h L : ℤ) ≤ 2 * (n / t) ∧ 2 * (n / t) < (capacity h L : ℤ)
  by_cases hnonneg : 0 ≤ n
  · have hqnonneg := Int.ediv_nonneg hnonneg (le_of_lt ht)
    have hqle := Int.ediv_le_self t hnonneg
    constructor <;> omega
  · have hneg : n < 0 := by omega
    have hm : n * t ≤ n := by
      have hmul := mul_nonneg (neg_nonneg.mpr (le_of_lt hneg))
        (sub_nonneg.mpr (show (1 : ℤ) ≤ t by omega))
      nlinarith
    have hqlo := Int.le_ediv_of_mul_le ht hm
    have hqhi : n / t < 0 := (Int.ediv_lt_iff_lt_mul ht).mpr (by simpa using hneg)
    constructor <;> omega

end MinCostFlow.Num
