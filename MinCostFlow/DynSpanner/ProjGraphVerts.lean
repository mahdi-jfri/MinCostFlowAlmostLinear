module

public import MinCostFlow.DynSpanner.StepInv

/-!
# The vertices of the projected graph `J`

In a step at level `0 < j` of Algorithm 6 (lines 70-77), the graph `J` has one edge for each
affected edge `e`, between the first and the last vertex of `S_{j-1}` on the walk of `e`. This
file proves that these vertices are vertices of the current graph `G'` (`projGraph_V_subset`):
the walk of `e` lies in `H_{<j}`, whose vertices are those of `G'`.
-/

namespace MinCostFlow.DynSpanner

public section

/-- The vertices of the projected graph `J` of a step at level `0 < j` are vertices of `G'`. -/
theorem projGraph_V_subset {G_r H_lt_r H_lt : MGraph} {delta : List Update}
    {pi_r piLt_mid : Embedding} {S_prev : Finset ℕ}
    (hVG_r : G_r.IsValid) (hBV_d : G_r.BatchIsValid delta)
    (hds_d : ∀ u ∈ delta, isDelOrSplit u)
    (hSub_lt_r : G_r.IsSubgraph H_lt_r)
    (hEmb_lt_r : Embedding.IsEmbedding pi_r G_r H_lt_r)
    (hHLtV : H_lt.V = (G_r.applyBatch delta).V)
    (hHLtE : H_lt.E = H_lt_r.E ∩ (G_r.applyBatch delta).E)
    (hHLt_tail : H_lt.tail = (G_r.applyBatch delta).tail)
    (hHLt_head : H_lt.head = (G_r.applyBatch delta).head)
    (hSub_lt : (G_r.applyBatch delta).IsSubgraph H_lt)
    (hTouch : allTouched G_r delta ⊆ S_prev)
    (hpi_eq : ∀ e ∈ (G_r.applyBatch delta).E, piLt_mid e = pi_r e) :
    let G' := G_r.applyBatch delta
    let E_aff := affectedEdges G' H_lt piLt_mid S_prev
    (buildProjGraph G' H_lt piLt_mid S_prev E_aff).V ⊆ G'.V := by
  intro G' E_aff v hv
  have hInvG := batch_delOrSplit_invariants delta G_r hVG_r hBV_d hds_d
  rcases hInvG with ⟨hVG', hEG'_sub, _, _, _, _, hAncEnds⟩
  have hEnds_lt : ∀ e ∈ H_lt_r.E, H_lt.tail e = G'.tail e ∧ H_lt.head e = G'.head e :=
    fun _ _ => ⟨congrFun hHLt_tail _, congrFun hHLt_head _⟩
  simp only [buildProjGraph, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with ⟨e, heAff, rfl | rfl⟩
  · have heG' := (Finset.mem_filter.mp heAff).1
    have hhit : ∃ z ∈ H_lt.walkVertices (G'.tail e) (pi_r e), z ∈ S_prev := by
      simpa [E_aff, affectedEdges, decide_eq_true_eq, hpi_eq e heG'] using
        (Finset.mem_filter.mp heAff).2
    have hw_r := hEmb_lt_r.2 e (hEG'_sub heG')
    have hp := (prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r hSub_lt hHLtV hHLtE hEnds_lt hTouch
      (pi_r e) (G_r.tail e) (G_r.head e) (G'.tail e)
      (hVG_r e (hEG'_sub heG')).1 (hVG_r e (hEG'_sub heG')).2 hw_r
      (hVG' e heG').1 (hAncEnds e (hEG'_sub heG')).1).2 hhit
    simpa [proj, hpi_eq e heG'] using hp.2.1
  · have heG' := (Finset.mem_filter.mp heAff).1
    have hhit1 : ∃ z ∈ H_lt.walkVertices (G'.tail e) (pi_r e), z ∈ S_prev := by
      simpa [E_aff, affectedEdges, decide_eq_true_eq, hpi_eq e heG'] using
        (Finset.mem_filter.mp heAff).2
    have hw_r := hEmb_lt_r.2 e (hEG'_sub heG')
    have hVw := walkVertices_subset_V_of_batch hVG_r hBV_d hds_d hSub_lt_r hEnds_lt
      (IsWalk.mem_edge hw_r) (hVG' e heG').1
    have h1 := (exists_mem_walkVertices_iff_anc hVG_r hBV_d hds_d hSub_lt_r hEnds_lt hTouch
      (IsWalk.mem_edge hw_r) (hVG' e heG').1 (hAncEnds e (hEG'_sub heG')).1 hVw).mp hhit1
    have h2 : ∃ z₀ ∈ H_lt_r.walkVertices (G_r.head e) (walkRev (pi_r e)), z₀ ∈ S_prev := by
      obtain ⟨z₀, hz₀, hz₀S⟩ := h1
      exact ⟨z₀, (mem_walkVertices_walkRev hw_r z₀).mpr hz₀, hz₀S⟩
    have hVwr := walkVertices_subset_V_of_batch hVG_r hBV_d hds_d hSub_lt_r hEnds_lt
      (IsWalk.mem_edge (isWalk_walkRev hw_r)) (hVG' e heG').2
    have hhit2 := (exists_mem_walkVertices_iff_anc hVG_r hBV_d hds_d hSub_lt_r hEnds_lt hTouch
      (IsWalk.mem_edge (isWalk_walkRev hw_r)) (hVG' e heG').2
      (hAncEnds e (hEG'_sub heG')).2 hVwr).mpr h2
    have hp := (prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r hSub_lt hHLtV hHLtE hEnds_lt hTouch
      (walkRev (pi_r e)) (G_r.head e) (G_r.tail e) (G'.head e)
      (hVG_r e (hEG'_sub heG')).2 (hVG_r e (hEG'_sub heG')).1 (isWalk_walkRev hw_r)
      (hVG' e heG').2 (hAncEnds e (hEG'_sub heG')).2).2 hhit2
    simpa [proj, hpi_eq e heG'] using hp.2.1

end

end MinCostFlow.DynSpanner
