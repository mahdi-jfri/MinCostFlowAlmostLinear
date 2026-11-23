module

public import MinCostFlow.Scaling.CoefficientRounding
import Mathlib.Tactic.Ring

/-!
# The numerical capacity-rounding loss

In Lemma C.12 used by Lemma C.9 of Chen et al., arXiv:2203.00671v2,
Appendix C, the total loss is at most the capacity unit times `m^12`.
For every `m >= 2`, this is at most `B/11` whenever the unit exceeds one.
The exact unit-one case is handled separately, avoiding the source's
incorrect split at `2*m^20` and its unstated large-m qualification.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Eleven times the coefficient-rounding loss is at most `B` for `m >= 2`. -/
theorem capacityUnit_loss_bound (m B : ℕ) (hm : 2 ≤ m) (hq : 1 < capacityUnit m B) :
    11 * (capacityUnit m B * m ^ 12) ≤ B := by
  have hh := capacityUnit_mul_lt_twice m B hq
  have hp : 22 ≤ m ^ 8 := le_trans (by decide : 22 ≤ 2 ^ 8) (Nat.pow_le_pow_left hm 8)
  have hmul := Nat.mul_le_mul_left (capacityUnit m B * m ^ 12) hp
  have he1 : capacityUnit m B * m ^ 12 * 22 = 22 * (capacityUnit m B * m ^ 12) := by ring
  have he2 : capacityUnit m B * m ^ 12 * m ^ 8 = capacityUnit m B * m ^ 20 := by
    rw [Nat.mul_assoc, ← Nat.pow_add]
  rw [he1, he2] at hmul
  omega

end MinCostFlow.Scaling
