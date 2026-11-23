module

public import MinCostFlow.Scaling.GeneralFlowReduction
public import MinCostFlow.Scaling.VertexCompression
public import MinCostFlow.Scaling.FeasibilitySize
import Mathlib.Tactic.Ring

/-!
# Rejecting nonzero demands on isolated vertices

The reduction behind Lemma C.1 of Chen et al., arXiv:2203.00671v2, must not
send an unbounded number of artificial arcs to the circulation solver when
most input vertices are isolated. The endpoint-label table identifies isolated
vertices. A nonzero demand there proves infeasibility. If the check passes,
all nonzero shifted demands occur among the at most `2*m` encountered vertices.
-/

@[expose] public section
namespace MinCostFlow.Scaling.FlowReduction

private theorem endpoint_ne_of_unlabeled (I : Instance) (hv : I.IsValid)
    (v : Fin I.n) (hz : (shiftedGraph I hv).endpointLabels.table v = 0)
    (e : Fin I.m) : v.val ≠ (I.edge e).tail ∧ v.val ≠ (I.edge e).head := by
  constructor
  · intro he
    have hve : v = (shiftedGraph I hv).tail e := Fin.ext he
    have hp := (shiftedGraph I hv).tail_label_pos e
    rw [← hve, hz] at hp
    exact Nat.lt_irrefl 0 hp
  · intro he
    have hve : v = (shiftedGraph I hv).head e := Fin.ext he
    have hp := (shiftedGraph I hv).head_label_pos e
    rw [← hve, hz] at hp
    exact Nat.lt_irrefl 0 hp

/-- Lower-capacity subtraction leaves an isolated vertex's demand unchanged. -/
theorem shiftedDemand_of_unlabeled (I : Instance) (hv : I.IsValid)
    (v : Fin I.n) (hz : (shiftedGraph I hv).endpointLabels.table v = 0) :
    shiftedDemand I v = I.d v := by
  have h : ∀ e, coefficient I e v * (I.edge e).lower = 0 := by
    intro e
    obtain ⟨ht, hh⟩ := endpoint_ne_of_unlabeled I hv v hz e
    simp [coefficient, ht, hh]
  simp only [shiftedDemand, h, Finset.sum_const_zero, sub_zero]

/-- An isolated vertex of a feasible flow must have demand zero. -/
theorem demand_zero_of_unlabeled_feasible (I : Instance) (hv : I.IsValid)
    (f : Fin I.m → ℝ) (hf : I.IsFeasible f) (v : Fin I.n)
    (hz : (shiftedGraph I hv).endpointLabels.table v = 0) : I.d v = 0 := by
  have hs : (∑ e, (I.edge e).b v * f e) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    obtain ⟨ht, hh⟩ := endpoint_ne_of_unlabeled I hv v hz e
    simp [Edge.b, ht, hh]
  have hr := hf.1 v
  rw [hs] at hr
  apply (Int.cast_inj (α := ℝ)).mp
  simpa only [Int.cast_zero] using hr.symm

/-- Scan all vertices for a nonzero demand at a vertex absent from the endpoint
table. This is an initial scan, performed once before any scaling loops. -/
def isolatedCheck (I : Instance) (hv : I.IsValid) : Bool :=
  let labels := (shiftedGraph I hv).endpointLabels
  (List.finRange I.n).all (fun v =>
    decide (0 < labels.table v) || decide (I.d v = 0))

/-- The Boolean scan states exactly the isolated-demand condition. -/
theorem isolatedCheck_iff (I : Instance) (hv : I.IsValid) :
    isolatedCheck I hv = true ↔
      ∀ v : Fin I.n, 0 < (shiftedGraph I hv).endpointLabels.table v ∨ I.d v = 0 := by
  simp [isolatedCheck]

/-- Every feasible input passes the isolated-demand check. -/
theorem isolatedCheck_of_feasible (I : Instance) (hv : I.IsValid)
    (f : Fin I.m → ℝ) (hf : I.IsFeasible f) : isolatedCheck I hv = true := by
  apply (isolatedCheck_iff I hv).mpr
  intro v
  by_cases h : 0 < (shiftedGraph I hv).endpointLabels.table v
  · exact Or.inl h
  · have hz : (shiftedGraph I hv).endpointLabels.table v = 0 := by omega
    exact Or.inr (demand_zero_of_unlabeled_feasible I hv f hf v hz)

/-- A failing check is a proof that no feasible real flow exists. -/
theorem infeasible_of_isolatedCheck (I : Instance) (hv : I.IsValid)
    (h : isolatedCheck I hv = false) : ∀ f, ¬ I.IsFeasible f := by
  intro f hf
  have hp := isolatedCheck_of_feasible I hv f hf
  rw [h] at hp
  exact Bool.noConfusion hp

/-- Passing the check gives precisely the support bound required for the
`3*m` positive-edge bound of the feasibility instance. -/
theorem shiftedDemand_support (I : Instance) (hv : I.IsValid)
    (h : isolatedCheck I hv = true) :
    ∀ v : Fin I.n, shiftedDemand I v ≠ 0 →
      0 < (shiftedGraph I hv).endpointLabels.table v := by
  intro v hd
  rcases (isolatedCheck_iff I hv).mp h v with hp | hz
  · exact hp
  · by_contra hneg
    have ht : (shiftedGraph I hv).endpointLabels.table v = 0 := by omega
    exact hd ((shiftedDemand_of_unlabeled I hv v ht).trans hz)

/-- After the isolated-demand check, the pruned feasibility solver input has
at most `3*m` positive-capacity edge slots, independent of `n`. -/
theorem feasibilityInstance_positiveEdges_le_three (I : Instance) (hv : I.IsValid)
    (h : isolatedCheck I hv = true) :
    (feasibilityInstance I hv).withoutZeroEdges.m ≤ 3 * I.m :=
  (shiftedGraph I hv).demandInstance_positiveEdges_le_three (shiftedDemand I)
    (shiftedDemand_support I hv h)

end MinCostFlow.Scaling.FlowReduction
