module

public import MinCostFlow.Num.Encoding
import MinCostFlow.Num.ShiftFacts
import Mathlib.Tactic

/-!
# The value change of a schoolbook row

A row updates the high suffix of the accumulator and leaves its low prefix alone.
The exact carry equation, multiplied by the prefix capacity, gives the row's full
value modulo the accumulator capacity. Truncated high source limbs contribute only
multiples of that capacity.
-/

public section
namespace MinCostFlow.Num

/-- A suffix row adds its shifted multiple to the whole accumulator modulo capacity. -/
theorem mul_row_value {mem mem' : ℕ → ℕ} {a out h K i x carry : ℕ}
    (hi : i ≤ K) (hv : Valid mem out h K)
    (hvalid : Valid mem' (out + i) h (K - i))
    (hframe : ∀ z, z < out + i ∨ out + i + (K - i) ≤ z → mem' z = mem z)
    (hmass : unsignedVal mem' (out + i) h (K - i) + capacity h (K - i) * carry =
      unsignedVal mem (out + i) h (K - i) + x * unsignedVal mem a h (K - i)) :
    Valid mem' out h K ∧ unsignedVal mem' out h K =
      (unsignedVal mem out h K + capacity h i * x * unsignedVal mem a h K) % capacity h K := by
  have hv' : Valid mem' out h K := by
    intro j hj
    by_cases hji : j < i
    · rw [hframe (out + j) (Or.inl (by omega))]
      exact hv j hj
    · have he : out + i + (j - i) = out + j := by omega
      rw [← he]
      exact hvalid (j - i) (by omega)
  refine ⟨hv', ?_⟩
  have hlow : unsignedVal mem' out h i = unsignedVal mem out h i := by
    apply unsignedVal_congr
    intro j hj
    exact hframe (out + j) (Or.inl (by omega))
  have hbefore : unsignedVal mem out h K = unsignedVal mem out h i +
      capacity h i * unsignedVal mem (out + i) h (K - i) := by
    conv_lhs => rw [show K = i + (K - i) by omega, unsignedVal_split]
  have hafter : unsignedVal mem' out h K = unsignedVal mem out h i +
      capacity h i * unsignedVal mem' (out + i) h (K - i) := by
    conv_lhs => rw [show K = i + (K - i) by omega, unsignedVal_split, hlow]
  have hc : capacity h K = capacity h i * capacity h (K - i) := by
    rw [← capacity_add, show i + (K - i) = K by omega]
  have hs : unsignedVal mem a h K = unsignedVal mem a h (K - i) +
      capacity h (K - i) * unsignedVal mem (a + (K - i)) h i := by
    conv_lhs => rw [show K = (K - i) + i by omega, unsignedVal_split]
  have he : unsignedVal mem out h K + capacity h i * x * unsignedVal mem a h K =
      unsignedVal mem' out h K + capacity h K *
        (carry + x * unsignedVal mem (a + (K - i)) h i) := by
    calc
      _ = unsignedVal mem out h i + capacity h i *
          (unsignedVal mem (out + i) h (K - i) + x * unsignedVal mem a h (K - i)) +
          capacity h K * (x * unsignedVal mem (a + (K - i)) h i) := by
        rw [hbefore, hs, hc]
        ring
      _ = unsignedVal mem out h i + capacity h i *
          (unsignedVal mem' (out + i) h (K - i) + capacity h (K - i) * carry) +
          capacity h K * (x * unsignedVal mem (a + (K - i)) h i) := by rw [hmass]
      _ = _ := by rw [hafter, hc]; ring
  rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (unsignedVal_lt hv')]

/-- Consecutive shifted rows combine into one product of the remaining source suffix. -/
theorem mul_rows_split (mem : ℕ → ℕ) (a d h K i : ℕ) (hi : i < K) :
    capacity h i * mem (a + i) * unsignedVal mem d h K +
      capacity h (i + 1) * unsignedVal mem (a + (i + 1)) h (K - (i + 1)) * unsignedVal mem d h K =
    capacity h i * unsignedVal mem (a + i) h (K - i) * unsignedVal mem d h K := by
  rw [show K - i = (K - (i + 1)) + 1 by omega, unsignedVal, capacity_succ]
  rw [show a + i + 1 = a + (i + 1) by omega]
  ring

end MinCostFlow.Num
