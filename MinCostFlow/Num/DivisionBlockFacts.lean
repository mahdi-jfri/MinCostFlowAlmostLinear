module

public import MinCostFlow.Num.Encoding
import MinCostFlow.Num.ShiftFacts
import MinCostFlow.Num.SignFacts
import MinCostFlow.Num.DivisionStepFacts
import Mathlib.Tactic

/-!
# Effective lengths from unsigned values

An unsigned block below a prefix capacity has only zero limbs above that prefix.
Its highest prefix limb is nonzero when the value reaches the preceding capacity.
These facts let long division use a zero-extended divisor without another scan.
-/

public section
namespace MinCostFlow.Num

/-- A value below the prefix capacity has zero high limbs. -/
theorem unsignedVal_high_zero_of_lt {mem : ℕ → ℕ} {a h K n : ℕ}
    (hv : Valid mem a h K) (hn : n ≤ K)
    (hu : unsignedVal mem a h K < capacity h n) :
    ∀ i, n ≤ i → i < K → mem (a + i) = 0 := by
  have he := unsignedVal_prefix_of_lt hv hn hu
  have hs := unsignedVal_split mem a h n (K - n)
  rw [show n + (K - n) = K by omega, ← he] at hs
  have ht : unsignedVal mem (a + n) h (K - n) = 0 := by
    have hc := capacity_pos h n
    nlinarith only [hs, hc]
  have hz := (unsignedVal_eq_zero_iff).mp ht
  intro i hni hi
  have hx := hz (i - n) (by omega)
  simpa only [show a + n + (i - n) = a + i by omega] using hx

/-- A nonzero highest limb puts the value above the preceding capacity. -/
theorem capacity_le_unsignedVal_of_top_pos {mem : ℕ → ℕ} {a h n : ℕ}
    (hn : 0 < n) (ht : 0 < mem (a + (n - 1))) :
    capacity h (n - 1) ≤ unsignedVal mem a h n := by
  have hs := unsignedVal_snoc mem a h (n - 1)
  rw [Nat.sub_add_cancel hn] at hs
  have hm := Nat.mul_le_mul_left (capacity h (n - 1)) ht
  omega

/-- Reaching the preceding capacity forces a nonzero highest prefix limb. -/
theorem top_pos_of_capacity_le_unsignedVal {mem : ℕ → ℕ} {a h K n : ℕ}
    (hv : Valid mem a h K) (hn : 0 < n) (hnK : n ≤ K)
    (hlo : capacity h (n - 1) ≤ unsignedVal mem a h K)
    (hhi : unsignedVal mem a h K < capacity h n) :
    0 < mem (a + (n - 1)) := by
  have he := unsignedVal_prefix_of_lt hv hnK hhi
  have hs := unsignedVal_snoc mem a h (n - 1)
  rw [Nat.sub_add_cancel hn, he] at hs
  have hb := unsignedVal_lt (h := h) (L := n - 1)
    (fun i hi => hv i (by omega))
  by_contra ht
  have hz : mem (a + (n - 1)) = 0 := by omega
  rw [hz, mul_zero, add_zero] at hs
  omega

end MinCostFlow.Num
