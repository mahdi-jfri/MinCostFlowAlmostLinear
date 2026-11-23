module

public import MinCostFlow.Scaling.CostStateInterpretation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The encoded update matches the physical cost-scaling update

Algorithm CostScaling in Appendix C of Chen et al., arXiv:2203.00671v2,
adds the primal augmentation and dual potential and halves epsilon. The
integer model doubles its denominator and potential numerator together.
These identities show that its interpreted state performs exactly that
physical update, including the rounding-unit scale on the integer dual.
-/

@[expose] public section
namespace MinCostFlow.Scaling.CostState
variable {I : Circulation}

/-- Doubling the stored denominator halves the represented epsilon. -/
theorem step_epsilon (solve : (J : Circulation) → Fin J.m → ℤ) (C : ℕ) (s : CostState I) :
    (s.step solve C).value.epsilon C = s.epsilon C / 2 := by
  simp only [epsilon, step, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The rounding unit halves along with epsilon. -/
theorem step_roundingUnit (solve : (J : Circulation) → Fin J.m → ℤ) (C : ℕ) (s : CostState I) :
    (s.step solve C).value.roundingUnit C = s.roundingUnit C / 2 := by
  simp only [roundingUnit, step, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The interpreted potential adds the computed dual in physical cost units. -/
theorem step_realPotential (solve : (J : Circulation) → Fin J.m → ℤ) (C : ℕ)
    (s : CostState I) (v : Fin I.n) :
    realPotential (I := I) C (s.step solve C).value v = realPotential (I := I) C s v +
      s.roundingUnit C * (((s.roundedInstance C).extractDualModel solve
        (Circulation.solveWithZeroCapacities solve (s.roundedInstance C))).value v : ℝ) := by
  unfold realPotential
  rw [s.step_roundingUnit solve C]
  simp only [step, Int.cast_mul, Int.cast_add, Int.cast_ofNat]
  ring

/-- The interpreted primal state adds exactly the projected residual augmentation. -/
theorem step_flow_cast (solve : (J : Circulation) → Fin J.m → ℤ) (C : ℕ) (s : CostState I) :
    (fun e => ((s.step solve C).value.flow e : ℝ)) =
      I.augment s.flow (fun e => (Circulation.solveWithZeroCapacities solve (s.roundedInstance C) e : ℝ)) := by
  funext e
  simp only [step, Circulation.augment, Circulation.project, Int.cast_add, Int.cast_sub]
  ring

/-- Initial encoded epsilon is the strict initialization `C+1`. -/
theorem initial_epsilon (I : Circulation) (C : ℕ) :
    (initial I).epsilon C = (C : ℝ) + 1 := by
  simp only [epsilon, initial, Nat.cast_one, div_one, Nat.cast_add]

/-- The initial integer potential represents the zero potential. -/
theorem initial_realPotential (I : Circulation) (C : ℕ) :
    realPotential (I := I) C (initial I) = fun _ => 0 := by
  funext v
  simp only [realPotential, initial, Int.cast_zero, mul_zero]

end MinCostFlow.Scaling.CostState
