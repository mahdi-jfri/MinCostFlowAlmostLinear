module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Circulations and their dual

Appendix C of Chen et al., arXiv:2203.00671v2, starts with the minimum-cost
circulation problem and its dual. Capacities and costs below are integers.
Real flows are used for the comparison defining an exact optimum. The incidence
sign agrees with `Instance`: positive at the tail and negative at the head.
The dual therefore uses the same sign, including for vertex potentials.

This file proves weak duality and the equality certificate for an optimum.
It does not assume strong duality.
-/

@[expose] public section

namespace MinCostFlow.Scaling

/-- The data of the minimum-cost circulation problem in Appendix C, equations
`MinCostCirculation` and `MinCostCirculationDual`. Zero capacities are allowed
so that rounded instances can retain edges of capacity zero. -/
structure Circulation where
  n : ℕ
  m : ℕ
  tail : Fin m → Fin n
  head : Fin m → Fin n
  capacity : Fin m → ℕ
  cost : Fin m → ℤ

namespace Circulation

/-- The edge-vertex incidence coefficient, with the sign of `Instance`. -/
def incidence (I : Circulation) (e : Fin I.m) (v : Fin I.n) : ℝ :=
  (if v = I.tail e then 1 else 0) - (if v = I.head e then 1 else 0)

/-- Net flow at a vertex. -/
def balance (I : Circulation) (f : Fin I.m → ℝ) (v : Fin I.n) : ℝ :=
  ∑ e, I.incidence e v * f e

/-- The zero-demand equation of the circulation problem. -/
def Conserves (I : Circulation) (f : Fin I.m → ℝ) : Prop :=
  ∀ v, I.balance f v = 0

/-- The primal constraints of Appendix C. -/
def Feasible (I : Circulation) (f : Fin I.m → ℝ) : Prop :=
  I.Conserves f ∧ ∀ e, 0 ≤ f e ∧ f e ≤ I.capacity e

/-- The primal objective. -/
def objective (I : Circulation) (f : Fin I.m → ℝ) : ℝ :=
  ∑ e, (I.cost e : ℝ) * f e

/-- Optimality is against every feasible real flow, including fractional flows. -/
def Optimal (I : Circulation) (f : Fin I.m → ℝ) : Prop :=
  I.Feasible f ∧ ∀ g, I.Feasible g → I.objective f ≤ I.objective g

/-- Applying the incidence matrix to a potential. -/
def potentialDifference (I : Circulation) (y : Fin I.n → ℝ) (e : Fin I.m) : ℝ :=
  y (I.tail e) - y (I.head e)

/-- Reduced costs from the paragraph before Definition C.4. -/
def reducedCost (I : Circulation) (y : Fin I.n → ℝ) (e : Fin I.m) : ℝ :=
  I.cost e - I.potentialDifference y e

/-- The constraints of the dual problem in Appendix C. -/
def DualFeasible (I : Circulation) (y : Fin I.n → ℝ)
    (lower upper : Fin I.m → ℝ) : Prop :=
  (∀ e, 0 ≤ lower e ∧ 0 ≤ upper e) ∧
  ∀ e, I.potentialDifference y e + lower e - upper e = I.cost e

/-- The dual objective of Appendix C. -/
def dualObjective (I : Circulation) (upper : Fin I.m → ℝ) : ℝ :=
  -(∑ e, upper e * (I.capacity e : ℝ))

/-- Every circulation instance has a feasible zero flow. -/
theorem zero_feasible (I : Circulation) : I.Feasible (fun _ => 0) := by
  constructor
  · intro v
    simp [balance]
  · intro e
    exact ⟨le_rfl, Nat.cast_nonneg _⟩

/-- The incidence pairing can be summed first over edges or first over vertices. -/
theorem potential_pairing (I : Circulation) (f : Fin I.m → ℝ)
    (y : Fin I.n → ℝ) :
    (∑ e, I.potentialDifference y e * f e) = ∑ v, y v * I.balance f v := by
  classical
  simp only [balance, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [incidence, potentialDifference, sub_mul, mul_sub, Finset.sum_sub_distrib,
    mul_ite, ite_mul]

/-- Potentials do not change the cost of a circulation, as used before
Definition C.4 in Appendix C. -/
theorem reducedCost_objective (I : Circulation) (f : Fin I.m → ℝ)
    (hf : I.Conserves f) (y : Fin I.n → ℝ) :
    (∑ e, I.reducedCost y e * f e) = I.objective f := by
  simp only [reducedCost, sub_mul, Finset.sum_sub_distrib]
  rw [potential_pairing]
  have hz : ∀ v, I.balance f v = 0 := hf
  simp [hz, objective]

/-- Weak duality for the primal and dual equations of Appendix C. -/
theorem weak_duality (I : Circulation) (f : Fin I.m → ℝ)
    (y : Fin I.n → ℝ) (lower upper : Fin I.m → ℝ)
    (hf : I.Feasible f) (hd : I.DualFeasible y lower upper) :
    I.dualObjective upper ≤ I.objective f := by
  have hp : (∑ e, I.potentialDifference y e * f e) = 0 := by
    rw [potential_pairing]
    have hz : ∀ v, I.balance f v = 0 := hf.1
    simp [hz]
  have he : ∀ e, -upper e * (I.capacity e : ℝ) ≤
      (I.cost e : ℝ) * f e - I.potentialDifference y e * f e := by
    intro e
    have hl := mul_nonneg (hd.1 e).1 (hf.2 e).1
    have hu := mul_nonneg (hd.1 e).2 (sub_nonneg.mpr (hf.2 e).2)
    have hc := hd.2 e
    rw [← hc]
    nlinarith only [hl, hu]
  have hs := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => he e)
  simpa [Finset.sum_sub_distrib, Finset.sum_neg_distrib, hp, dualObjective,
    objective] using hs

/-- Equality of feasible primal and dual objectives certifies exact optimality.
This is the final certification step used in Lemma C.8. -/
theorem optimal_of_dual_equality (I : Circulation) (f : Fin I.m → ℝ)
    (y : Fin I.n → ℝ) (lower upper : Fin I.m → ℝ)
    (hf : I.Feasible f) (hd : I.DualFeasible y lower upper)
    (heq : I.objective f = I.dualObjective upper) : I.Optimal f := by
  refine ⟨hf, fun g hg => ?_⟩
  rw [heq]
  exact I.weak_duality g y lower upper hg hd

end Circulation
end MinCostFlow.Scaling
