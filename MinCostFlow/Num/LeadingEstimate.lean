module

public import MinCostFlow.Num.DivisionEstimate
import MinCostFlow.Num.ShiftFacts
import Mathlib.Tactic

/-!
# Reading the leading limbs for a quotient estimate

The effective divisor length is at least two. Splitting at two fewer limbs leaves
its leading pair and the numerator's leading triple. The low parts are each below
the split capacity, so the numerical quotient-estimate lemma applies directly.
-/

@[expose] public section
namespace MinCostFlow.Num

/-- The two highest divisor limbs, for an effective length of at least two. -/
def leadingPair (mem : ℕ → ℕ) (a h n : ℕ) : ℕ :=
  mem (a + (n - 1)) * base h + mem (a + (n - 2))

/-- Three numerator limbs aligned with a divisor of effective length `n`. -/
def leadingTriple (mem : ℕ → ℕ) (a h n : ℕ) : ℕ :=
  (mem (a + n) * base h + mem (a + (n - 1))) * base h + mem (a + (n - 2))

/-- The leading pair and the low prefix decompose the divisor. -/
theorem unsignedVal_leadingPair (mem : ℕ → ℕ) (a h M : ℕ) :
    unsignedVal mem a h (M + 2) = leadingPair mem a h (M + 2) * capacity h M + unsignedVal mem a h M := by
  rw [show M + 2 = M + 2 by rfl, unsignedVal_split]
  simp only [unsignedVal, leadingPair, show M + 2 - 1 = M + 1 by omega,
    Nat.add_sub_cancel, mul_zero, add_zero]
  rw [show a + M + 1 = a + (M + 1) by omega]
  ring

/-- The aligned leading triple and low prefix decompose the numerator. -/
theorem unsignedVal_leadingTriple (mem : ℕ → ℕ) (a h M : ℕ) :
    unsignedVal mem a h (M + 3) = leadingTriple mem a h (M + 2) * capacity h M + unsignedVal mem a h M := by
  rw [show M + 3 = M + 3 by rfl, unsignedVal_split]
  simp only [unsignedVal, leadingTriple, show M + 2 - 1 = M + 1 by omega,
    Nat.add_sub_cancel, mul_zero, add_zero]
  rw [show a + M + 1 = a + (M + 1) by omega,
    show a + (M + 1) + 1 = a + (M + 2) by omega]
  ring

/-- A nonzero highest divisor limb makes its leading pair at least the base. -/
theorem base_le_leadingPair {mem : ℕ → ℕ} {a h n : ℕ}
    (htop : 0 < mem (a + (n - 1))) : base h ≤ leadingPair mem a h n := by
  have hm := Nat.mul_le_mul_right (base h) (Nat.succ_le_of_lt htop)
  dsimp only [leadingPair]
  omega

/-- Leading limb estimates bracket the true quotient digit by one. -/
theorem leading_estimate_bounds {mem : ℕ → ℕ} {a d h n : ℕ}
    (hh : 0 < h) (hn : 2 ≤ n) (ha : Valid mem a h (n + 1)) (hd : Valid mem d h n)
    (htop : 0 < mem (d + (n - 1)))
    (hX : unsignedVal mem a h (n + 1) < unsignedVal mem d h n * base h) :
    unsignedVal mem a h (n + 1) / unsignedVal mem d h n ≤
        min (base h - 1) (leadingTriple mem a h n / leadingPair mem d h n) ∧
      min (base h - 1) (leadingTriple mem a h n / leadingPair mem d h n) ≤
        unsignedVal mem a h (n + 1) / unsignedVal mem d h n + 1 := by
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 2 := ⟨n - 2, by omega⟩
  have hlowA : unsignedVal mem a h M < capacity h M :=
    unsignedVal_lt (fun i hi => ha i (by omega))
  have hlowD : unsignedVal mem d h M < capacity h M :=
    unsignedVal_lt (fun i hi => hd i (by omega))
  exact quotient_digit_estimate
    (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) (capacity_pos h M)
    (base_le_leadingPair htop) (unsignedVal_leadingPair mem d h M) hlowD
    (by simpa only [show M + 2 + 1 = M + 3 by omega] using unsignedVal_leadingTriple mem a h M)
    hlowA hX

end MinCostFlow.Num
