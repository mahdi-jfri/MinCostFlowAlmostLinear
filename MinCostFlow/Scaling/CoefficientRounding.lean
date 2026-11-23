module

public import MinCostFlow.Scaling.CapacityRounding
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rounding cycle coefficients to the capacity unit

The proof of Lemma C.12 used by capacity scaling in Appendix C of Chen et al.,
arXiv:2203.00671v2, rounds each real cycle coefficient down to a multiple of
the known integer capacity unit. These are mathematical witnesses, not real
numbers computed by the program. Each coefficient loses less than one unit.
When the unit exceeds one, its product with `m^20` is below `2*B`, repairing
the source's inaccurate small-B split.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- The integer multiple below a nonnegative real cycle coefficient. -/
noncomputable def roundCoefficient (q : ℕ) (a : ℝ) : ℕ := q * ⌊a / (q : ℝ)⌋₊

/-- Rounded coefficients do not increase and lose less than one unit. -/
theorem roundCoefficient_bounds (q : ℕ) (hq : 0 < q) (a : ℝ) (ha : 0 ≤ a) :
    (roundCoefficient q a : ℝ) ≤ a ∧ a < (roundCoefficient q a : ℝ) + q := by
  have hqreal : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hlo := Nat.floor_le (div_nonneg ha hqreal.le)
  have hup := Nat.lt_floor_add_one (a / (q : ℝ))
  have hlo' := (le_div_iff₀ hqreal).mp hlo
  have hup' := (div_lt_iff₀ hqreal).mp hup
  simp only [roundCoefficient, Nat.cast_mul]
  constructor
  · simpa only [mul_comm] using hlo'
  · linarith only [hup']

/-- Every rounded coefficient is an integral multiple of the unit. -/
theorem roundCoefficient_dvd (q : ℕ) (a : ℝ) : q ∣ roundCoefficient q a :=
  ⟨⌊a / (q : ℝ)⌋₊, rfl⟩

/-- Whenever rounding actually has a unit above one, that unit is less than
`2*B/m^20`. This covers the source's intermediate-B gap directly. -/
theorem capacityUnit_mul_lt_twice (m B : ℕ) (hq : 1 < capacityUnit m B) :
    capacityUnit m B * m ^ 20 < 2 * B := by
  have hB : 0 < B := by
    by_contra hn
    have he : B = 0 := by omega
    subst B
    simp only [capacityUnit, Nat.zero_sub, Nat.zero_div] at hq
    omega
  let k := (B - 1) / m ^ 20
  have hk : 1 ≤ k := by unfold capacityUnit at hq; change 1 < k + 1 at hq; omega
  have hdiv : k * m ^ 20 ≤ B - 1 := Nat.div_mul_le_self _ _
  have hmul := Nat.mul_le_mul_right (m ^ 20) hk
  simp only [Nat.one_mul] at hmul
  unfold capacityUnit
  change (k + 1) * m ^ 20 < _
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- With unit one, the corrected rounded capacity is simply the clipped capacity. -/
theorem roundedCapacity_of_unit_one (m B u : ℕ) (hq : capacityUnit m B = 1) :
    roundedCapacity m B u = min u (B * m ^ 20) := by
  simp only [roundedCapacity, scaledCapacity, hq, Nat.div_one, Nat.one_mul]

end MinCostFlow.Scaling
