module

public import MinCostFlow.SparseCore.LastLevel
import Mathlib.Data.Prod.Lex

/-!
# Deterministic representatives for the last level

Definition 5.8 (pages 19–20) uses spanning forests of the last graph.
Pick the smallest vertex in each component and keep a shortest edge
for each unordered pair, resolving ties by the edge name.
-/

open MinCostFlow.LSF MinCostFlow.SparseCore

public section

namespace MinCostFlow.LastLevelProgram

/-- The least vertex of a nonempty vertex set, with zero as the empty default. -/
@[expose] def firstVertex (V : Finset ℕ) : ℕ :=
  if h : V.Nonempty then V.min' h else 0

/-- A nonempty vertex set contains its chosen vertex. -/
theorem firstVertex_mem {V : Finset ℕ} (h : V.Nonempty) : firstVertex V ∈ V := by
  simp [firstVertex, h, Finset.min'_mem]

/-- Choose the smallest vertex name in each component. -/
@[expose] noncomputable def componentRoots (G : MGraph) : Finset ℕ :=
  G.V.image fun v => firstVertex (compOf G v)

/-- Each chosen root belongs to the input graph. -/
theorem componentRoots_subset (G : MGraph) : componentRoots G ⊆ G.V := by
  intro r hr
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
  exact (mem_compOf_iff.mp (firstVertex_mem ⟨u, self_mem_compOf hu⟩)).1

/-- Every graph vertex reaches a chosen root. -/
theorem componentRoots_connected {G : MGraph} {v : ℕ} (hv : v ∈ G.V) :
    ∃ r ∈ componentRoots G, G.Connected v r := by
  refine ⟨_, Finset.mem_image_of_mem _ hv, ?_⟩
  exact (mem_compOf_iff.mp (firstVertex_mem ⟨v, self_mem_compOf hv⟩)).2

/-- Two chosen roots in one component coincide. -/
theorem componentRoots_unique {G : MGraph} {r s : ℕ}
    (hr : r ∈ componentRoots G) (hs : s ∈ componentRoots G) (hconn : G.Connected r s) : r = s := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
  have hru := (mem_compOf_iff.mp (firstVertex_mem ⟨u, self_mem_compOf hu⟩)).2
  have hsv := (mem_compOf_iff.mp (firstVertex_mem ⟨v, self_mem_compOf hv⟩)).2
  rw [compOf_eq_of_connected (MGraph.connected_trans hru
    (MGraph.connected_trans hconn (MGraph.connected_symm hsv)))]

private noncomputable def edgeKeys (G : MGraph) (ℓ : ℕ → ℝ) (p : ℕ × ℕ) :
    Finset (ℝ ×ₗ ℕ) :=
  ((nonLoopEdges G).filter fun e => edgePairKey G e = p).image fun e => toLex (ℓ e, e)

/-- Pick a shortest edge with the given endpoints, breaking a tie by the edge name. -/
noncomputable def shortestEdge (G : MGraph) (ℓ : ℕ → ℝ) (p : ℕ × ℕ) : ℕ :=
  open Classical in
  if h : (edgeKeys G ℓ p).Nonempty then (ofLex ((edgeKeys G ℓ p).min' h)).2 else 0

/-- A chosen edge has the requested endpoints and minimizes the ordered pair
of length and edge name among the edges with those endpoints. -/
theorem shortestEdge_spec {G : MGraph} {ℓ : ℕ → ℝ} {e : ℕ} (he : e ∈ nonLoopEdges G) :
    let p := edgePairKey G e
    let f := shortestEdge G ℓ p
    f ∈ nonLoopEdges G ∧ edgePairKey G f = p ∧
      (ℓ f < ℓ e ∨ ℓ f = ℓ e ∧ f ≤ e) := by
  classical
  dsimp only
  let p := edgePairKey G e
  have hkey : toLex (ℓ e, e) ∈ edgeKeys G ℓ p :=
    Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨he, rfl⟩)
  have hnonempty : (edgeKeys G ℓ p).Nonempty := ⟨_, hkey⟩
  have hmin := Finset.min'_mem (edgeKeys G ℓ p) hnonempty
  have hle := Finset.min'_le (edgeKeys G ℓ p) _ hkey
  obtain ⟨f, hf, hfmin⟩ := Finset.mem_image.mp hmin
  have hp := Finset.mem_filter.mp hf
  rw [← hfmin] at hle
  change shortestEdge G ℓ p ∈ nonLoopEdges G ∧ edgePairKey G (shortestEdge G ℓ p) = p ∧
    (ℓ (shortestEdge G ℓ p) < ℓ e ∨ ℓ (shortestEdge G ℓ p) = ℓ e ∧ shortestEdge G ℓ p ≤ e)
  simp only [shortestEdge, hnonempty, ↓reduceDIte, ← hfmin]
  exact ⟨hp.1, hp.2, Prod.Lex.le_iff.mp hle⟩

end MinCostFlow.LastLevelProgram
