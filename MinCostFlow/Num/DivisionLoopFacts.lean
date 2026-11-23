module

public import MinCostFlow.Num.DivisionStep
import MinCostFlow.Num.SignFacts
import Mathlib.Tactic

/-!
# The long-division recurrence

A partial numerator is the current remainder followed by the remaining input limbs.
Processing its highest pending limb separates one quotient digit at the matching
place value. Its remainder is exactly the remainder of the smaller recursive problem.
-/

@[expose] public section
namespace MinCostFlow.Num

/-- The current remainder followed by the pending low input limbs. -/
def loopNumerator (mem : ℕ → ℕ) (a r h K i : ℕ) : ℕ :=
  unsignedVal mem r h (K + 1) * capacity h i + unsignedVal mem a h i

/-- The highest pending limb is the next digit appended to the remainder. -/
theorem loopNumerator_step (mem : ℕ → ℕ) (a r h K S : ℕ) :
    loopNumerator mem a r h K (S + 1) =
      stepNumerator mem r h K (mem (a + S)) * capacity h S + unsignedVal mem a h S := by
  unfold loopNumerator stepNumerator
  rw [capacity_succ h S, unsignedVal_snoc mem a h S]
  ring

/-- Processing one quotient digit gives both the quotient and remainder recurrence. -/
theorem long_division_recurrence (X C low V : ℕ) (hV : 0 < V) :
    (X * C + low) / V = (X % V * C + low) / V + C * (X / V) ∧
    (X * C + low) % V = (X % V * C + low) % V := by
  have he : X * C + low = (X % V * C + low) + V * (C * (X / V)) := by
    conv_lhs => rw [← Nat.mod_add_div X V]
    ring
  rw [he, Nat.add_mul_div_left _ _ hV, Nat.add_mul_mod_self_left]
  exact ⟨rfl, rfl⟩

end MinCostFlow.Num
