module

public import MinCostFlow.IPM.InitialConstruction
import Mathlib.Tactic.Linarith

/-!
# Size of the auxiliary-vertex instance

Appendix B.1 (page 92) of Chen et al., arXiv:2203.00671v2, adds an edge only at
a nonzero deficit. An isolated vertex with nonzero demand certifies
infeasibility. Once that case is rejected, every deficit vertex is an
endpoint of an original edge. There are at most `2m` such vertices, so
the augmented instance has at most `3m` edges without an assumption
relating the total number of vertices to the number of edges.
-/

@[expose] public section
namespace MinCostFlow.IPM

/-- Original edge endpoints, including vertices with zero midpoint deficit. -/
def endpointVertices (I : Instance) : Finset ℕ :=
  (Finset.univ.image fun e : Fin I.m => (I.edge e).tail) ∪
    (Finset.univ.image fun e : Fin I.m => (I.edge e).head)

/-- Isolated vertices must have zero demand for a feasible flow to exist. -/
def IsolatedDemandsZero (I : Instance) : Prop :=
  ∀ v : Fin I.n, (v : ℕ) ∉ endpointVertices I → I.d v = 0

/-- At a vertex outside the endpoint set every incidence coefficient is zero. -/
theorem incidence_zero_of_not_endpoint (I : Instance) (v : Fin I.n)
    (hv : (v : ℕ) ∉ endpointVertices I) (e : Fin I.m) : (I.edge e).b v = 0 := by
  have ht : (v : ℕ) ≠ (I.edge e).tail := by
    intro he
    apply hv
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, Finset.mem_univ e, he.symm⟩)
  have hh : (v : ℕ) ≠ (I.edge e).head := by
    intro he
    apply hv
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, Finset.mem_univ e, he.symm⟩)
  simp only [Edge.b, ht, hh, ↓reduceIte, sub_self]

/-- A feasible instance passes the isolated-demand check. -/
theorem isolatedDemandsZero_of_feasible (I : Instance) (f : Fin I.m → ℝ)
    (hf : I.IsFeasible f) : IsolatedDemandsZero I := by
  intro v hv
  have hr := hf.1 v
  simp only [incidence_zero_of_not_endpoint I v hv, zero_mul, Finset.sum_const_zero] at hr
  exact_mod_cast hr.symm

/-- Failure of the isolated-demand check is a certificate of infeasibility. -/
theorem infeasible_of_isolated_demand (I : Instance) (hi : ¬ IsolatedDemandsZero I) :
    ¬ ∃ f, I.IsFeasible f := by
  rintro ⟨f, hf⟩
  exact hi (isolatedDemandsZero_of_feasible I f hf)

/-- A nonzero midpoint deficit is incident to an original edge once the
isolated-demand check passes. -/
theorem deficit_vertex_is_endpoint (I : Instance) (hi : IsolatedDemandsZero I)
    (v : Fin I.n) (hv : v ∈ deficitVertices I) : (v : ℕ) ∈ endpointVertices I := by
  by_contra hn
  have hd : I.d v = 0 := hi v hn
  have hb : ∀ e, incidenceInt (I.edge e) v = 0 := by
    intro e
    have h := incidence_zero_of_not_endpoint I v hn e
    rw [← incidenceInt_cast] at h
    exact_mod_cast h
  have hz : twiceDeficit I v = 0 := by
    simp only [twiceDeficit, hd, hb, mul_zero, zero_mul, Finset.sum_const_zero, sub_zero]
  exact (Finset.mem_filter.mp hv).2 hz

/-- There are at most `2m` distinct original edge endpoints. -/
theorem endpointVertices_card_le (I : Instance) : (endpointVertices I).card ≤ 2*I.m := by
  have ht := Finset.card_image_le (s := Finset.univ) (f := fun e : Fin I.m => (I.edge e).tail)
  have hh := Finset.card_image_le (s := Finset.univ) (f := fun e : Fin I.m => (I.edge e).head)
  have hu := Finset.card_union_le
    (Finset.univ.image fun e : Fin I.m => (I.edge e).tail)
    (Finset.univ.image fun e : Fin I.m => (I.edge e).head)
  simp only [Finset.card_univ, Fintype.card_fin] at ht hh
  dsimp only [endpointVertices]
  omega

/-- At most `2m` auxiliary edges are added after the isolated-demand check. -/
theorem deficitVertices_card_le (I : Instance) (hi : IsolatedDemandsZero I) :
    (deficitVertices I).card ≤ 2*I.m := by
  have hsub : Finset.image Fin.val (deficitVertices I) ⊆ endpointVertices I := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact deficit_vertex_is_endpoint I hi w hw
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hc
  exact hc.trans (endpointVertices_card_le I)

/-- The auxiliary instance has at most `3m` edges, allowing arbitrary
numbers of isolated zero-demand vertices in the input. -/
theorem initialInstance_m_le (I : Instance) (K : ℤ) (hi : IsolatedDemandsZero I) :
    (initialInstance I K).m ≤ 3*I.m := by
  rw [initialInstance_m]
  have hf : (freeEdges I).card ≤ I.m := by
    have h := Finset.card_le_card (Finset.filter_subset
      (fun e : Fin I.m => (I.edge e).lower < (I.edge e).upper) Finset.univ)
    simpa only [freeEdges, Finset.card_univ, Fintype.card_fin] using h
  have hd := deficitVertices_card_le I hi
  omega

end MinCostFlow.IPM
