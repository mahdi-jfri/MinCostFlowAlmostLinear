module

public import MinCostFlow.Scaling.DualExtractionCorrectness
import Mathlib.Tactic.Linarith

/-!
# Integer slacks from a residual potential

The last step of Lemma C.8 of Chen et al., arXiv:2203.00671v2, Appendix C,
forms nonnegative dual slacks from the reduced costs of a feasible integral
flow. For an integral residual potential, both slacks are integers. The
residual inequalities imply equality of primal and dual objectives, so this
construction supplies the dual output without another solver call.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Lower slack, computed entirely with integer subtraction and maximum. -/
def integerLowerSlack (I : Circulation) (y : Fin I.n → ℤ) (e : Fin I.m) : ℤ :=
  max (I.cost e - (y (I.tail e) - y (I.head e))) 0

/-- Upper slack, computed entirely with integer subtraction and maximum. -/
def integerUpperSlack (I : Circulation) (y : Fin I.n → ℤ) (e : Fin I.m) : ℤ :=
  max (-(I.cost e - (y (I.tail e) - y (I.head e)))) 0

/-- The computed integer slacks agree with the real dual-certificate slacks. -/
theorem integerSlacks_cast (I : Circulation) (y : Fin I.n → ℤ) :
    (fun e => (I.integerLowerSlack y e : ℝ)) = I.lowerSlack (fun v => (y v : ℝ)) ∧
    (fun e => (I.integerUpperSlack y e : ℝ)) = I.upperSlack (fun v => (y v : ℝ)) := by
  constructor <;> funext e <;> simp only [integerLowerSlack, integerUpperSlack,
    Int.cast_max, Int.cast_sub, Int.cast_neg, Int.cast_zero, lowerSlack, upperSlack,
    reducedCost, potentialDifference]

/-- A feasible integral flow and integral residual potential yield a feasible
integral dual with the same objective. -/
theorem integerSlacks_certificate (I : Circulation) (f : Fin I.m → ℤ)
    (hf : I.Feasible (fun e => (f e : ℝ))) (y : Fin I.n → ℤ)
    (hy : ∀ e, 0 < (I.residual f).capacity e →
      y ((I.residual f).tail e) - y ((I.residual f).head e) ≤ (I.residual f).cost e) :
    I.DualFeasible (fun v => (y v : ℝ))
      (fun e => (I.integerLowerSlack y e : ℝ)) (fun e => (I.integerUpperSlack y e : ℝ)) ∧
    I.objective (fun e => (f e : ℝ)) =
      I.dualObjective (fun e => (I.integerUpperSlack y e : ℝ)) := by
  have hforward : ∀ e, (f e : ℝ) < I.capacity e →
      0 ≤ I.reducedCost (fun v => (y v : ℝ)) e := by
    intro e he
    have hi : f e < (I.capacity e : ℤ) := by exact_mod_cast he
    have ha : 0 < (I.residual f).capacity (Fin.castAdd I.m e) := by
      simp only [Fin.addCases_left]
      exact Int.lt_toNat.mpr (sub_pos.mpr hi)
    have h := (Int.cast_le (R := ℝ)).mpr (hy (Fin.castAdd I.m e) ha)
    simp only [Fin.addCases_left, Int.cast_sub] at h
    exact sub_nonneg.mpr h
  have hreverse : ∀ e, 0 < (f e : ℝ) →
      I.reducedCost (fun v => (y v : ℝ)) e ≤ 0 := by
    intro e he
    have hi : 0 < f e := Int.cast_pos.mp he
    have ha : 0 < (I.residual f).capacity (Fin.natAdd I.m e) := by
      simp only [Fin.addCases_right]
      exact Int.lt_toNat.mpr hi
    have h := (Int.cast_le (R := ℝ)).mpr (hy (Fin.natAdd I.m e) ha)
    simp only [Fin.addCases_right, Int.cast_sub, Int.cast_neg] at h
    dsimp only [reducedCost, potentialDifference]
    linarith only [h]
  rw [(I.integerSlacks_cast y).1, (I.integerSlacks_cast y).2]
  exact ⟨I.slacks_dualFeasible _,
    I.dual_equality_of_residual_potential _ hf _ hforward hreverse⟩

end MinCostFlow.Scaling.Circulation
