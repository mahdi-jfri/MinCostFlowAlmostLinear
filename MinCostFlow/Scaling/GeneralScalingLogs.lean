module

public import MinCostFlow.Scaling.DemandBoundCheck
public import MinCostFlow.Scaling.GeneralScalingWork
import Mathlib.Tactic.Ring

/-!
# The logarithmic bounds for arbitrary demands

The composition in Lemma C.1 of Chen et al., arXiv:2203.00671v2, increases
intermediate edge counts and capacities by polynomial factors in `m`. Their
logarithms are bounded here explicitly. Padding all logarithms handles zero
costs, zero capacities, and the one-edge case without asymptotic exceptions.
-/

@[expose] public section
namespace MinCostFlow.Scaling.FlowReduction

/-- The artificial-capacity budget after demand rejection is polynomial in
`m` times `U`, so its logarithm has the required size. -/
theorem arbitrary_capacity_log (I : Instance) (U : ℕ) :
    Nat.clog 2 (scalingCapacityBudget I ((I.m + 1) * U) + 1) ≤
      2 + 2 * Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) := by
  have hm := Nat.le_pow_clog (by decide : 1 < 2) (I.m + 1)
  have hu := Nat.le_pow_clog (by decide : 1 < 2) (U + 1)
  have hp := Nat.mul_le_mul (Nat.mul_le_mul hm hm) hu
  have hsmall : scalingCapacityBudget I ((I.m + 1) * U) + 1 ≤
      4 * ((I.m + 1) * (I.m + 1) * (U + 1)) := by
    unfold scalingCapacityBudget
    have hpos : 1 ≤ (I.m + 1) * (I.m + 1) := Nat.mul_pos (by omega) (by omega)
    have he : 4 * ((I.m + 1) * (I.m + 1) * (U + 1)) =
      4 * ((I.m + 1) * (I.m + 1) * U) + 4 * ((I.m + 1) * (I.m + 1)) := by ring
    rw [he]
    simp only [Nat.mul_assoc] at hpos ⊢
    omega
  apply Nat.clog_le_of_le_pow
  calc
    _ ≤ 4 * ((I.m + 1) * (I.m + 1) * (U + 1)) := hsmall
    _ ≤ 4 * (2 ^ Nat.clog 2 (I.m + 1) * 2 ^ Nat.clog 2 (I.m + 1) *
        2 ^ Nat.clog 2 (U + 1)) := Nat.mul_le_mul_left 4 hp
    _ = 2 ^ (2 + 2 * Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1)) := by
      rw [Nat.pow_add, Nat.pow_add, two_mul, Nat.pow_add]
      ring

/-- Uniform padded factors dominate all intermediate logarithmic factors. -/
theorem general_scaling_log_factors (I : Instance) (C U : ℕ) :
    Nat.clog 2 (3 * I.m + 1) + 1 ≤ 3 * (Nat.clog 2 (I.m + 1) + 1) ∧
    Nat.clog 2 (3 * I.m + 1) +
        Nat.clog 2 (scalingCapacityBudget I ((I.m + 1) * U) + 1) + 1 ≤
      5 * (Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1) ∧
    Nat.clog 2 (max C 1 + 2) ≤ 2 * Nat.clog 2 (C + 2) := by
  have he := clog_two_le_of_le_pow_mul (3 * I.m + 1) (I.m + 1) 2 (by omega)
  have hu := arbitrary_capacity_log I U
  have hc := clog_two_le_of_le_pow_mul (max C 1 + 2) (C + 2) 1 (by simp; omega)
  have hl : 1 ≤ Nat.clog 2 (C + 2) := by
    have hh := Nat.le_pow_clog (by decide : 1 < 2) (C + 2)
    by_contra hn
    have hz : Nat.clog 2 (C + 2) = 0 := by omega
    rw [hz] at hh
    omega
  omega

/-- The full arbitrary-demand model makes at most an explicit constant
 times `log m * log(mU) * log C` primitive calls, with padded logarithms. -/
theorem arbitraryDemandScalingModel_calls (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) (C U : ℕ) :
    (arbitraryDemandScalingModel solve I hv C U).calls.length ≤
      345600 * (Nat.clog 2 (I.m + 1) + 1) *
        (Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1) * Nat.clog 2 (C + 2) := by
  unfold arbitraryDemandScalingModel
  split
  · dsimp only
    have hh := generalScalingModel_calls solve I hv C ((I.m + 1) * U)
    obtain ⟨h1, h2, h3⟩ := general_scaling_log_factors I C U
    have hp := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul_left 11520 h1) h2) h3
    have he (a b c : ℕ) : 11520 * (3 * a) * (5 * b) * (2 * c) = 345600 * a * b * c := by ring
    rw [he] at hp
    exact le_trans hh hp
  · simp

/-- All non-solver work has the same three logarithmic factors and an additive
scan of the original vertices. This counts the preliminary demand scan too. -/
theorem arbitraryDemandScalingModel_work (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) (C U : ℕ) (hm : 0 < I.m) :
    (arbitraryDemandScalingModel solve I hv C U).work ≤
      210000000000 * I.m * (Nat.clog 2 (I.m + 1) + 1) *
        (Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1) * Nat.clog 2 (C + 2) + 85 * I.n := by
  unfold arbitraryDemandScalingModel
  split
  · dsimp only
    have hh := generalScalingModel_work solve I hv C ((I.m + 1) * U) hm
    obtain ⟨h1, h2, h3⟩ := general_scaling_log_factors I C U
    have hp := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul_left (7000000000 * I.m) h1) h2) h3
    have he (m a b c : ℕ) : 7000000000 * m * (3 * a) * (5 * b) * (2 * c) =
      210000000000 * m * a * b * c := by ring
    rw [he] at hp
    omega
  · dsimp only
    omega

end MinCostFlow.Scaling.FlowReduction
