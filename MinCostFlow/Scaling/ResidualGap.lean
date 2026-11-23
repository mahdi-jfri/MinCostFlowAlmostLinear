module

public import MinCostFlow.Scaling.ResidualReduction
import Mathlib.Tactic.Linarith

/-!
# The optimum residual objective is the remaining gap

The proof of Lemma C.9 of Chen et al., arXiv:2203.00671v2, Appendix C,
compares the current feasible flow to an optimum. Their difference lifts
to a feasible residual circulation, and its objective is the difference of
the original objectives. Every other residual circulation augments to a
feasible original flow. Thus the lifted difference is residual optimal,
with value exactly the remaining objective gap.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The signed difference between two feasible flows lifts to a residual
circulation with the exact difference of their costs. -/
theorem differenceLift_objective (I : Circulation) (f : Fin I.m → ℤ) (g : Fin I.m → ℝ) :
    (I.residual f).objective (I.differenceLift f g) =
      I.objective g - I.objective (fun e => (f e : ℝ)) := by
  rw [I.residual_objective, I.project_differenceLift]
  simp only [objective, mul_sub, Finset.sum_sub_distrib]

/-- Lifting an optimum into the residual graph gives a residual optimum. -/
theorem differenceLift_optimal (I : Circulation) (f : Fin I.m → ℤ)
    (hf : I.Feasible (fun e => (f e : ℝ))) (g : Fin I.m → ℝ) (hg : I.Optimal g) :
    (I.residual f).Optimal (I.differenceLift f g) := by
  have hlift := I.differenceLift_feasible f g hf.2 hg.1.2
    (fun v => (hg.1.1 v).trans (hf.1 v).symm)
  refine ⟨hlift, ?_⟩
  intro h hh
  have hfeas := I.augment_feasible f hf h hh
  have hcompare := hg.2 _ hfeas
  rw [I.augment_objective] at hcompare
  rw [I.differenceLift_objective]
  linarith only [hcompare]

/-- A zero residual optimum certifies optimality of the current flow. -/
theorem optimal_of_zero_residual_optimum (I : Circulation) (f : Fin I.m → ℤ)
    (hf : I.Feasible (fun e => (f e : ℝ)))
    (hzero : (I.residual f).Optimal (fun _ => 0)) : I.Optimal (fun e => (f e : ℝ)) := by
  refine ⟨hf, ?_⟩
  intro g hg
  have hfeas := I.differenceLift_feasible f g hf.2 hg.2
    (fun v => (hg.1 v).trans (hf.1 v).symm)
  have hcmp := hzero.2 _ hfeas
  rw [I.differenceLift_objective] at hcmp
  have hz : (I.residual f).objective (fun _ => 0) = 0 := by simp only [objective, mul_zero, Finset.sum_const_zero]
  rw [hz] at hcmp
  linarith only [hcmp]

end MinCostFlow.Scaling.Circulation
