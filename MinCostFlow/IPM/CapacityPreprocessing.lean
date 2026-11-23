module

public import MinCostFlow.IPM.Definitions
import Mathlib.Tactic.Linarith

/-!
# Capacity checks before midpoint initialization

Appendix B.1 (page 92) of Chen et al., arXiv:2203.00671v2, starts each original
edge at the midpoint of its capacities. A reversed interval makes the
instance infeasible. An interval with equal ends forces a known flow and
must be removed before using a barrier. These facts apply to the real
flows of equation (8), without any integrality theorem.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

/-- Appendix B.1 (page 92)'s midpoint on each original edge. -/
@[expose] def midpointFlow (I : Instance) (e : Fin I.m) : ℝ :=
  (((I.edge e).lower : ℝ) + (I.edge e).upper) / 2

/-- A reversed capacity interval is a certificate of infeasibility. -/
theorem infeasible_of_reversed_capacity (I : Instance) (e : Fin I.m)
    (he : ((I.edge e).upper : ℝ) < (I.edge e).lower) :
    ¬ ∃ f, I.IsFeasible f := by
  rintro ⟨f, hf⟩
  exact (not_le_of_gt he) ((hf.2 e).1.trans (hf.2 e).2)

/-- An edge with equal capacities has a forced value in every feasible flow.
Deleting it therefore subtracts this fixed routing contribution from the
remaining demands and adds a fixed constant to the objective. -/
theorem flow_eq_of_fixed_capacity (I : Instance) (e : Fin I.m)
    (he : (I.edge e).lower = (I.edge e).upper)
    (f : Fin I.m → ℝ) (hf : I.IsFeasible f) : f e = (I.edge e).lower := by
  have hu := (hf.2 e).2
  rw [← he] at hu
  exact le_antisymm hu (hf.2 e).1

/-- The midpoint is strictly inside the interval exactly when its ends
are distinct and in increasing order. This is the missing domain check
in Appendix B.1 (page 92). -/
theorem midpoint_inside_iff (I : Instance) :
    StrictlyInside I (midpointFlow I) ↔
      ∀ e : Fin I.m, ((I.edge e).lower : ℝ) < (I.edge e).upper := by
  constructor
  · intro h e
    exact (h e).1.trans (h e).2
  · intro h e
    have he := h e
    constructor <;> dsimp only [midpointFlow] <;> linarith only [he]

end MinCostFlow.IPM
