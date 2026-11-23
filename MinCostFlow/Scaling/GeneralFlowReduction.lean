module

public import MinCostFlow.Scaling.FlowReduction
public import MinCostFlow.Scaling.DemandReduction
public import MinCostFlow.Scaling.ResidualReduction
import Mathlib.Tactic.Linarith

/-!
# General flow reduces to two circulation problems

The proof of Lemma C.1 of Chen et al., arXiv:2203.00671v2, uses the equivalence
between general minimum-cost flow and minimum-cost circulation. First subtract
lower capacities. A circulation feasibility phase either finds a flow routing
the shifted demands or proves that none exists. Then optimize a circulation in
the residual graph of the feasible integral flow. These statements compare with
all feasible real flows and include the infeasible-answer case.
-/

@[expose] public section
namespace MinCostFlow.Scaling.FlowReduction

/-- The first circulation problem in the reduction of a general flow instance. -/
abbrev feasibilityInstance (I : Instance) (hv : I.IsValid) : Circulation :=
  (shiftedGraph I hv).demandInstance (shiftedDemand I)

/-- Subtracting lower capacities converts any feasible input flow into a bounded
flow routing precisely the shifted demands. -/
theorem shifted_feasible (I : Instance) (hv : I.IsValid)
    (hcap : ∀ e, (I.edge e).lower ≤ (I.edge e).upper)
    (f : Fin I.m → ℝ) (hf : I.IsFeasible f) :
    (∀ v, (shiftedGraph I hv).balance (shift I f) v = (shiftedDemand I v : ℝ)) ∧
      ∀ e, 0 ≤ shift I f e ∧ shift I f e ≤ (shiftedGraph I hv).capacity e := by
  apply (feasible_restore_iff I hv hcap (shift I f)).mp
  simpa only [restore_shift] using hf

/-- The optimum of the first circulation decides feasibility of the original
instance, including arbitrary lower capacities and demands. -/
theorem feasible_iff_phase_value (I : Instance) (hv : I.IsValid)
    (hcap : ∀ e, (I.edge e).lower ≤ (I.edge e).upper)
    (g : Fin (I.m + (I.n + I.n)) → ℝ)
    (hg : (feasibilityInstance I hv).Optimal g) :
    (∃ f, I.IsFeasible f) ↔
      (feasibilityInstance I hv).objective g =
        -((shiftedGraph I hv).demandMass (shiftedDemand I) : ℝ) := by
  rw [← (shiftedGraph I hv).demand_feasible_iff_optimal_value (shiftedDemand I) g hg]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨shift I f, shifted_feasible I hv hcap f hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨restore I f, (feasible_restore_iff I hv hcap f).mpr hf⟩

/-- If the first circulation's optimum misses its saturation target, no real
flow is feasible in the original instance. -/
theorem infeasible_of_phase_value (I : Instance) (hv : I.IsValid)
    (hcap : ∀ e, (I.edge e).lower ≤ (I.edge e).upper)
    (g : Fin (I.m + (I.n + I.n)) → ℝ)
    (hg : (feasibilityInstance I hv).Optimal g)
    (hbad : (feasibilityInstance I hv).objective g ≠
      -((shiftedGraph I hv).demandMass (shiftedDemand I) : ℝ)) :
    ∀ f, ¬ I.IsFeasible f := by
  intro f hf
  exact hbad ((feasible_iff_phase_value I hv hcap g hg).mp ⟨f, hf⟩)

/-- Restrict a successful integral feasibility-phase flow and reinsert lower
capacities. All operations on the returned vector are integer operations. -/
def phaseFlow (I : Instance) (g : Fin (I.m + (I.n + I.n)) → ℤ) : Fin I.m → ℤ :=
  fun e => (I.edge e).lower + g (Fin.castAdd (I.n + I.n) e)

/-- A successful integral feasibility phase returns a feasible integral flow
for the original problem. -/
theorem phaseFlow_feasible (I : Instance) (hv : I.IsValid)
    (hcap : ∀ e, (I.edge e).lower ≤ (I.edge e).upper)
    (g : Fin (I.m + (I.n + I.n)) → ℤ)
    (hg : (feasibilityInstance I hv).Feasible (fun e => (g e : ℝ)))
    (heq : (feasibilityInstance I hv).objective (fun e => (g e : ℝ)) =
      -((shiftedGraph I hv).demandMass (shiftedDemand I) : ℝ)) :
    I.IsFeasible (fun e => (phaseFlow I g e : ℝ)) := by
  have h := (shiftedGraph I hv).demandRestrict_routes (shiftedDemand I)
    (fun e => (g e : ℝ)) hg heq
  have hf := (feasible_restore_iff I hv hcap _).mpr h
  have he : restore I ((shiftedGraph I hv).demandRestrict (fun e => (g e : ℝ))) =
      (fun e => (phaseFlow I g e : ℝ)) := by
    funext e
    simp only [restore, Circulation.demandRestrict, phaseFlow, Int.cast_add]
  rw [← he]
  exact hf

/-- Optimize the residual problem after any feasible integral shifted flow.
Restoring lower capacities then gives an exact minimum-cost flow in `Instance`. -/
theorem minCostFlow_of_residual_optimal (I : Instance) (hv : I.IsValid)
    (hcap : ∀ e, (I.edge e).lower ≤ (I.edge e).upper)
    (f : Fin I.m → ℤ)
    (hf : I.IsFeasible (restore I (fun e => (f e : ℝ))))
    (g : Fin (I.m + I.m) → ℝ)
    (hg : ((shiftedGraph I hv).residual f).Optimal g) :
    I.IsMinCostFlow (restore I ((shiftedGraph I hv).augment f g)) := by
  have hs := (feasible_restore_iff I hv hcap _).mp hf
  have ho := (shiftedGraph I hv).augment_optimal_with_demands f hs.2 g hg
  constructor
  · apply (feasible_restore_iff I hv hcap _).mpr
    exact ⟨fun v => (ho.1 v).trans (hs.1 v), ho.2.1⟩
  · intro h hh
    have ht := shifted_feasible I hv hcap h hh
    have hc := ho.2.2 (shift I h) (fun v => (ht.1 v).trans (hs.1 v).symm) ht.2
    have heq : I.cost h = I.cost (fun e => ((I.edge e).lower : ℝ)) +
        (shiftedGraph I hv).objective (shift I h) := by
      have he := cost_restore I hv (shift I h)
      simpa only [restore_shift] using he
    rw [cost_restore I hv _, heq]
    exact add_le_add le_rfl hc

end MinCostFlow.Scaling.FlowReduction
