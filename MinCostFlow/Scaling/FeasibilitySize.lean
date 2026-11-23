module

public import MinCostFlow.Scaling.DemandReduction
public import MinCostFlow.Scaling.PositiveEdges
public import MinCostFlow.Scaling.VertexCompression
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.SplitIfs

/-!
# Bounding the positive arcs in the feasibility reduction

The reduction used in Lemma C.1 of Chen et al., arXiv:2203.00671v2, reserves
two artificial arc slots per vertex. Only one can have positive capacity for
each nonzero demand. If isolated vertices have zero demand, the number of
nonzero demands is at most the number of encountered endpoints, hence at most
`2*m`. Removing zero-capacity slots then leaves at most `3*m` arcs, even when
the original graph has many isolated vertices.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The number of retained edges is the sum of their positive-capacity indicators. -/
theorem positiveEdges_length_eq_sum (I : Circulation) :
    I.positiveEdges.length = ∑ e, if 0 < I.capacity e then 1 else 0 := by
  classical
  have he : I.positiveEdges.toFinset = Finset.univ.filter (fun e => 0 < I.capacity e) := by
    ext e
    simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_positiveEdges_iff]
  rw [← List.toFinset_card_of_nodup I.positiveEdges_nodup, he, Finset.card_filter]

/-- A nonzero integer demand activates exactly one of its two artificial arcs. -/
private theorem demand_indicator (d : ℤ) :
    (if 0 < d.toNat then 1 else 0 : ℕ) + (if 0 < (-d).toNat then 1 else 0) =
      if d ≠ 0 then 1 else 0 := by
  simp only [Int.lt_toNat, Int.natCast_zero]
  split_ifs <;> omega

/-- The positive edge count in a feasibility instance is the original positive
edge count plus one for each nonzero prescribed demand. -/
theorem demandInstance_positiveEdges_length (I : Circulation) (d : Fin I.n → ℤ) :
    (I.demandInstance d).positiveEdges.length = I.positiveEdges.length +
      ∑ v, if d v ≠ 0 then 1 else 0 := by
  classical
  rw [positiveEdges_length_eq_sum, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [← Finset.sum_add_distrib, positiveEdges_length_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  exact demand_indicator (d v)

/-- Distinct vertices of nonzero demand get distinct consecutive labels.
Thus there can be at most `2*m` nonzero demands after isolated-vertex checks. -/
theorem nonzero_demands_le_endpoints (I : Circulation) (d : Fin I.n → ℤ)
    (hd : ∀ v, d v ≠ 0 → 0 < I.endpointLabels.table v) :
    (∑ v, if d v ≠ 0 then 1 else 0 : ℕ) ≤ 2 * I.m := by
  classical
  let f : {v : Fin I.n // d v ≠ 0} → Fin I.endpointLabels.count :=
    fun v => I.encodeVertex v.val (hd v.val v.property)
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    exact (I.encodeVertex_eq_iff v.val w.val _ _).mp h
  have hc := Fintype.card_le_of_injective f hf
  have hsum : Fintype.card {v : Fin I.n // d v ≠ 0} =
      ∑ v, if d v ≠ 0 then 1 else 0 := by
    rw [Fintype.card_subtype, Finset.card_filter]
  rw [hsum, Fintype.card_fin] at hc
  exact le_trans hc I.endpointLabels_count_le

/-- The feasibility solver sees at most `3*m` positive-capacity edges once
isolated vertices of nonzero demand are rejected. -/
theorem demandInstance_positiveEdges_le_three (I : Circulation) (d : Fin I.n → ℤ)
    (hd : ∀ v, d v ≠ 0 → 0 < I.endpointLabels.table v) :
    (I.demandInstance d).withoutZeroEdges.m ≤ 3 * I.m := by
  change (I.demandInstance d).positiveEdges.length ≤ 3 * I.m
  rw [demandInstance_positiveEdges_length]
  have he := I.positiveEdges_length_le
  have hv := I.nonzero_demands_le_endpoints d hd
  omega

/-- The demand-support condition is satisfiable for every circulation graph:
the zero-demand instance satisfies it. -/
theorem zero_demand_support (I : Circulation) :
    ∀ v : Fin I.n, (0 : ℤ) ≠ 0 → 0 < I.endpointLabels.table v := by
  intro v h
  exact False.elim (h rfl)

end MinCostFlow.Scaling.Circulation
