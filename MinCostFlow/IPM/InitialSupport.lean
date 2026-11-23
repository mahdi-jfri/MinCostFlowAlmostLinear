module

public import MinCostFlow.IPM.InitialConstruction
public import MinCostFlow.IPM.InitialSize
public import MinCostFlow.IPM.RecoverySupport
import Mathlib.Tactic.Linarith

/-!
# The small support vertex set in the augmented instance

For the real-flow recovery argument in Appendix B.1 (page 92) of Chen et al.,
arXiv:2203.00671v2, only original edge endpoints and the added vertex
can lie on residual arcs. This set has at most `2m+1` vertices after the
isolated-demand check. Thus a simple residual return route has length
bounded by the original edge count even if there are many isolated vertices.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM

/-- Original edge endpoints together with the newly added vertex. -/
def initialSupportVertices (I : Instance) : Finset (Fin (I.n+1)) :=
  Finset.univ.filter fun v => (v : ℕ) ∈ insert I.n (endpointVertices I)

/-- At most `2m+1` vertices are incident to augmented edges. -/
theorem initialSupportVertices_card_le (I : Instance) : (initialSupportVertices I).card ≤ 2*I.m+1 := by
  have hs : Finset.image Fin.val (initialSupportVertices I) ⊆ insert I.n (endpointVertices I) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hw).2
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hc
  have hi := Finset.card_insert_le I.n (endpointVertices I)
  have he := endpointVertices_card_le I
  omega

/-- Both endpoints of every augmented array edge belong to this small set. -/
theorem initialEdgeArray_endpoints (I : Instance) (K : ℤ) (hi : IsolatedDemandsZero I)
    (e : Fin ((freeEdges I).card+(deficitVertices I).card)) :
    (initialEdgeArray I K e).tail ∈ insert I.n (endpointVertices I) ∧
      (initialEdgeArray I K e).head ∈ insert I.n (endpointVertices I) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) e
  · simp only [initialEdgeArray, Fin.addCases_left]
    constructor
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(freeIndex I j).1, Finset.mem_univ _, rfl⟩)
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(freeIndex I j).1, Finset.mem_univ _, rfl⟩)
  · simp only [initialEdgeArray, Fin.addCases_right]
    have hv := deficit_vertex_is_endpoint I hi (deficitIndex I j).1 (deficitIndex I j).2
    have hvin : ((deficitIndex I j).1 : ℕ) ∈ insert I.n (endpointVertices I) := Finset.mem_insert_of_mem hv
    have hnew : I.n ∈ insert I.n (endpointVertices I) := Finset.mem_insert_self _ _
    unfold starEdge
    split_ifs
    · exact ⟨hvin, hnew⟩
    · exact ⟨hnew, hvin⟩

/-- Both endpoints of every actual augmented edge belong to the same set. -/
theorem initialInstance_endpoints (I : Instance) (K : ℤ) (hi : IsolatedDemandsZero I)
    (e : Fin (initialInstance I K).m) :
    ((initialInstance I K).edge e).tail ∈ insert I.n (endpointVertices I) ∧
      ((initialInstance I K).edge e).head ∈ insert I.n (endpointVertices I) := by
  have he : (initialInstance I K).edge e =
      initialEdgeArray I K (arrayIndex (initialEdgeArray I K) (initialDemands I) e) :=
    instanceOfArrays_edge (initialEdgeArray I K) (initialDemands I) e
  rw [he]
  exact initialEdgeArray_endpoints I K hi _

/-- Every directed residual support arc is contained in the small vertex set. -/
theorem initial_residualSupport_vertices (I : Instance) (K : ℤ)
    (hi : IsolatedDemandsZero I) (hJ : (initialInstance I K).IsValid)
    (d : Fin (initialInstance I K).m → ℝ) (u v : Fin (initialInstance I K).n)
    (huv : residualSupport (initialInstance I K) hJ d u v) :
    u ∈ initialSupportVertices I ∧ v ∈ initialSupportVertices I := by
  obtain ⟨e, he⟩ := huv
  have hend := initialInstance_endpoints I K hi e
  have ht : tailVertex (initialInstance I K) hJ e ∈ initialSupportVertices I :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hend.1⟩
  have hh : headVertex (initialInstance I K) hJ e ∈ initialSupportVertices I :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hend.2⟩
  rcases he with ⟨_, htail, hhead⟩ | ⟨_, hhead, htail⟩
  · exact ⟨htail ▸ ht, hhead ▸ hh⟩
  · exact ⟨hhead ▸ hh, htail ▸ ht⟩

end MinCostFlow.IPM
