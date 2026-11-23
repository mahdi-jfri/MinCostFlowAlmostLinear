module

public import MinCostFlow.Scaling.ShortestRoutingLayout

/-!
# Solver-domain and word bounds for the routing residual

The routing graph's capacities are at most `n+1`. Its residual graph has
`2*(m+n)` slots, so its capacities satisfy the bounded solver's polynomial
limit whenever a slot exists. Costs retain the original magnitudes.
These bounds justify calling the existing zero-capacity solver adapter
on the circulation prepared by the machine program.
-/

public section
namespace MinCostFlow.Scaling.Machine

/-- Every routing residual capacity satisfies its own-edge-count
fortieth-power bound, including graphs with empty edge sets. -/
theorem routingResidual_capacity_bound (J : Circulation) :
    ∀ e, (J.shortestRoutingGraph.residual J.shortestRoutingStart).capacity e ≤
      (J.shortestRoutingGraph.residual J.shortestRoutingStart).m^40 := by
  have hcap := J.shortestRoutingGraph.residual_capacities_le J.shortestRoutingStart
    J.shortestRoutingStart_bounds (J.n+1) J.shortestRoutingGraph_capacities
  intro e
  have he : e.val < (J.m+J.n)+(J.m+J.n) := e.isLt
  have hbase : 1 ≤ (J.m+J.n)+(J.m+J.n) := by omega
  have hp := Nat.pow_le_pow_right hbase (by decide : 1 ≤ 40)
  simp only [pow_one] at hp
  exact (hcap e).trans ((show J.n+1 ≤ (J.m+J.n)+(J.m+J.n) by omega).trans hp)

/-- Original polynomial cost bounds imply the routing residual's own
polynomial cost bound. Source arcs have zero cost and reversal negates costs. -/
theorem routingResidual_cost_bound (J : Circulation) (hc : J.CostsBounded (J.m^10)) :
    (J.shortestRoutingGraph.residual J.shortestRoutingStart).CostsBounded
      ((J.shortestRoutingGraph.residual J.shortestRoutingStart).m^10) := by
  have h := J.shortestRoutingGraph.residual_costsBounded J.shortestRoutingStart (J.m^10)
    (J.shortestRoutingGraph_costsBounded (J.m^10) hc)
  intro e
  apply (h e).trans
  apply Nat.pow_le_pow_left
  change J.m ≤ (J.m+J.n)+(J.m+J.n)
  omega

private theorem solverWords_fit_of_fields (J : Circulation) (w : ℕ)
    (hn : J.n < 2^w) (hm : J.m < 2^w) (hone : 1 < 2^w)
    (hu : ∀ e,J.capacity e < 2^w) (hc : ∀ e,(J.cost e).natAbs < 2^w) :
    ∀ x ∈ J.solverWords,x < 2^w := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hn
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hm
  obtain ⟨e,_,hx⟩ := List.mem_flatMap.mp hx
  simp only [Circulation.solverEdgeWords,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact (J.tail e).isLt.trans hn
  · exact (J.head e).isLt.trans hn
  · exact hu e
  · split <;> omega
  · exact hc e

/-- The routing residual's encoded fields fit when the original input,
new vertex count, and doubled routing edge count fit. -/
theorem routingResidual_words_fit (J : Circulation) (w : ℕ)
    (hinput : ∀ x ∈ J.solverWords,x < 2^w) (hn : J.n+1 < 2^w)
    (hm : (J.m+J.n)+(J.m+J.n) < 2^w) (hone : 1 < 2^w) :
    ∀ x ∈ (J.shortestRoutingGraph.residual J.shortestRoutingStart).solverWords,x < 2^w := by
  have hSinput := shortestRouting_words_fit J w hinput hn (by omega)
  have hcap := J.shortestRoutingGraph.residual_capacities_le J.shortestRoutingStart
    J.shortestRoutingStart_bounds (J.n+1) J.shortestRoutingGraph_capacities
  apply solverWords_fit_of_fields _ w hn hm hone
  · intro e
    exact (hcap e).trans_lt hn
  · intro e
    refine Fin.addCases (fun e => ?_) (fun e => ?_) e
    · simpa only [Fin.addCases_left] using hSinput _
        (J.shortestRoutingGraph.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
    · simpa only [Fin.addCases_right,Int.natAbs_neg] using hSinput _
        (J.shortestRoutingGraph.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))

end MinCostFlow.Scaling.Machine
