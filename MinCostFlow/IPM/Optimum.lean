module

public import MinCostFlow.IPM.Definitions
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field

/-!
# An optimal real flow exists

Equation (8) of Section 4 of Chen et al., arXiv:2203.00671v2, minimizes
linear cost on a closed capacity box intersected with the routing equations.
This set is compact. Thus a feasible instance has a minimum, even when some
capacities coincide. No integrality theorem is needed for this fact.
-/

public section

namespace MinCostFlow.IPM

/-- The cost in equation (8) is continuous on real flow vectors. -/
theorem continuous_cost (I : Instance) : Continuous I.cost := by
  unfold Instance.cost
  exact continuous_finsetSum _ fun e _ => continuous_const.mul (continuous_apply e)

/-- The routing equations define a closed set. -/
theorem isClosed_routes (I : Instance) : IsClosed {f | I.Routes f} := by
  have heq : {f | I.Routes f} =
      ⋂ v : Fin I.n, {f : Fin I.m → ℝ | ∑ e, (I.edge e).b v * f e = (I.d v : ℝ)} := by
    ext f
    simp only [Set.mem_ofPred, Set.mem_iInter, Instance.Routes]
  rw [heq]
  apply isClosed_iInter
  intro v
  exact isClosed_eq (continuous_finsetSum _ fun e _ =>
    continuous_const.mul (continuous_apply e)) continuous_const

/-- The feasible set in equation (8) is compact, including when it is empty. -/
theorem isCompact_feasible (I : Instance) : IsCompact {f | I.IsFeasible f} := by
  let lower : Fin I.m → ℝ := fun e => (I.edge e).lower
  let upper : Fin I.m → ℝ := fun e => (I.edge e).upper
  have heq : {f | I.IsFeasible f} = {f | I.Routes f} ∩ Set.Icc lower upper := by
    ext f
    change (I.Routes f ∧ ∀ e, lower e ≤ f e ∧ f e ≤ upper e) ↔
      I.Routes f ∧ (lower ≤ f ∧ f ≤ upper)
    constructor
    · rintro ⟨hr, hf⟩
      exact ⟨hr, fun e => (hf e).1, fun e => (hf e).2⟩
    · rintro ⟨hr, hl, hu⟩
      exact ⟨hr, fun e => ⟨hl e, hu e⟩⟩
  rw [heq, Set.inter_comm]
  exact isCompact_Icc.inter_right (isClosed_routes I)

/-- Equation (8): whenever a feasible real flow exists, a minimum-cost real
flow exists. This justifies the optimal flow used throughout Section 4. -/
theorem exists_minCostFlow (I : Instance) (hf : ∃ f, I.IsFeasible f) :
    ∃ f, I.IsMinCostFlow f := by
  obtain ⟨f, hfeas, hmin⟩ := (isCompact_feasible I).exists_isMinOn hf
    (continuous_cost I).continuousOn
  exact ⟨f, hfeas, hmin⟩

end MinCostFlow.IPM
