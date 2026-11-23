module

public import MinCostFlow.Num.ExtendCopy
import MinCostFlow.Num.ShiftFacts
import Mathlib.Tactic

/-!
# Values of extended limb lists

Zero high limbs preserve the unsigned value. High limbs equal to the largest limb
add exactly the difference between the new and old capacities. These identities
account for sign extension in an arithmetic right shift.
-/

public section
namespace MinCostFlow.Num

private theorem listVal_extended_empty_zero (mem : ℕ → ℕ) (a h K : ℕ) :
    listVal h (extendedLimbs mem a 0 0 K) = 0 := by
  induction K with
  | zero => rfl
  | succ K ih => simp only [extendedLimbs, listVal, ih, mul_zero, zero_add]

private theorem listVal_extended_empty_max (mem : ℕ → ℕ) (a h K : ℕ) :
    listVal h (extendedLimbs mem a (base h - 1) 0 K) + 1 = capacity h K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    have hb := base_pos h
    have hm := congrArg (fun n => base h * n) ih
    rw [extendedLimbs, listVal, capacity_succ]
    nlinarith [Nat.sub_add_cancel (Nat.succ_le_of_lt hb)]

/-- Appending zero high limbs leaves the unsigned value unchanged. -/
theorem listVal_extended_zero {mem : ℕ → ℕ} {a h M K : ℕ} (hk : M ≤ K) :
    listVal h (extendedLimbs mem a 0 M K) = unsignedVal mem a h M := by
  induction M generalizing a K with
  | zero => simpa only [unsignedVal] using listVal_extended_empty_zero mem a h K
  | succ M ih =>
    cases K with
    | zero => omega
    | succ K =>
      rw [extendedLimbs, listVal, unsignedVal, ih (by omega)]

/-- Maximal high limbs add the difference in capacities. -/
theorem listVal_extended_max {mem : ℕ → ℕ} {a h M K : ℕ} (hk : M ≤ K) :
    listVal h (extendedLimbs mem a (base h - 1) M K) + capacity h M =
      unsignedVal mem a h M + capacity h K := by
  induction M generalizing a K with
  | zero => simpa only [unsignedVal, capacity_zero, zero_add] using
      listVal_extended_empty_max mem a h K
  | succ M ih =>
    cases K with
    | zero => omega
    | succ K =>
      have ht := ih (a := a + 1) (K := K) (by omega)
      have hm := congrArg (fun n => base h * n) ht
      rw [extendedLimbs, listVal, unsignedVal, capacity_succ, capacity_succ]
      nlinarith

/-- An unsigned value divided by the low-prefix capacity is precisely its tail. -/
theorem unsignedVal_tail_div {mem : ℕ → ℕ} {a h L q : ℕ}
    (hv : Valid mem a h L) (hq : q ≤ L) :
    unsignedVal mem a h L / capacity h q = unsignedVal mem (a + q) h (L - q) := by
  have hlo : unsignedVal mem a h q < capacity h q :=
    unsignedVal_lt (fun i hi => hv i (lt_of_lt_of_le hi hq))
  conv_lhs => rw [show L = q + (L - q) by omega, unsignedVal_split]
  rw [Nat.add_mul_div_left _ _ (capacity_pos h q), Nat.div_eq_of_lt hlo, zero_add]

end MinCostFlow.Num
