module

public import MinCostFlow.Scaling.Circulation
import Mathlib.Tactic.NormNum

/-!
# Integer capacity rounding

Definition C.11 in Appendix C of Chen et al., arXiv:2203.00671v2, rounds
capacities to multiples of the ceiling of `B / m^20`, and clips large
capacities. Here `B` is a positive integer, as it is when obtained from an
integral approximate circulation. The clipping threshold is itself rounded
down to a multiple of the unit. This repairs the source's threshold, which
need not be a multiple and therefore does not always scale to an integer.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Ceiling of `B / m^20` for positive integer `B`. -/
def capacityUnit (m B : ℕ) : ℕ := (B - 1) / m ^ 20 + 1

/-- The scaled rounded capacity, including the clipping in Definition C.11. -/
def scaledCapacity (m B u : ℕ) : ℕ :=
  min (u / capacityUnit m B) (B * m ^ 20 / capacityUnit m B)

/-- The capacity before scaling back down to the polynomial-capacity instance. -/
def roundedCapacity (m B u : ℕ) : ℕ := capacityUnit m B * scaledCapacity m B u

/-- The unit is nonzero, so scaling is well defined. -/
theorem capacityUnit_pos (m B : ℕ) : 0 < capacityUnit m B := by
  exact Nat.zero_lt_succ _

/-- The unit rounds upward: its product with the denominator covers `B`. -/
theorem le_capacityUnit_mul (m B : ℕ) (hm : 0 < m) (hB : 0 < B) :
    B ≤ capacityUnit m B * m ^ 20 := by
  have hd : 0 < m ^ 20 := Nat.pow_pos hm
  have hrem := Nat.mod_lt (B - 1) hd
  have hdiv := Nat.div_add_mod (B - 1) (m ^ 20)
  unfold capacityUnit
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm ((B - 1) / m ^ 20)]
  omega

/-- The scaled capacities obey the `m^40` bound for every positive `m`,
including `m = 1`. This is the bound claimed after Definition C.11. -/
theorem scaledCapacity_le (m B u : ℕ) (hm : 0 < m) (hB : 0 < B) :
    scaledCapacity m B u ≤ m ^ 40 := by
  apply le_trans (min_le_right _ _)
  apply Nat.div_le_of_le_mul
  have h := Nat.mul_le_mul_right (m ^ 20) (le_capacityUnit_mul m B hm hB)
  calc
    B * m ^ 20 ≤ capacityUnit m B * m ^ 20 * m ^ 20 := h
    _ = capacityUnit m B * m ^ 40 := by
      rw [Nat.mul_assoc, ← Nat.pow_add]

/-- Rounded flows never exceed the original capacity. -/
theorem roundedCapacity_le (m B u : ℕ) : roundedCapacity m B u ≤ u := by
  calc
    roundedCapacity m B u ≤ capacityUnit m B * (u / capacityUnit m B) :=
      Nat.mul_le_mul_left _ (min_le_left _ _)
    _ ≤ u := Nat.mul_div_le _ _

/-- The rounded capacity is an exact integral multiple of its unit. -/
theorem roundedCapacity_div (m B u : ℕ) :
    roundedCapacity m B u / capacityUnit m B = scaledCapacity m B u := by
  exact Nat.mul_div_cancel_left _ (capacityUnit_pos m B)

/-- The corrected Definition C.11 instance, retaining the original edge slots. -/
def Circulation.capacityRounded (I : Circulation) (B : ℕ) : Circulation :=
  { I with capacity := fun e => roundedCapacity I.m B (I.capacity e) }

/-- Every feasible flow on the rounded instance is feasible on the original.
This is the first step of the proof of Lemma C.12. -/
theorem Circulation.capacityRounded_feasible (I : Circulation) (B : ℕ)
    (f : Fin I.m → ℝ) (hf : (I.capacityRounded B).Feasible f) : I.Feasible f := by
  refine ⟨hf.1, fun e => ⟨(hf.2 e).1, ?_⟩⟩
  apply le_trans (hf.2 e).2
  exact_mod_cast roundedCapacity_le I.m B (I.capacity e)

/-- The source's unrounded clipping threshold need not be a multiple of the
rounding unit: `m = 2`, `B = 2*m^20 + 2` gives unit three and remainder one. -/
theorem source_clipping_not_multiple :
    let B := 2 * 2 ^ 20 + 2
    capacityUnit 2 B = 3 ∧ (B * 2 ^ 20) % capacityUnit 2 B = 1 := by
  norm_num [capacityUnit]

end MinCostFlow.Scaling
