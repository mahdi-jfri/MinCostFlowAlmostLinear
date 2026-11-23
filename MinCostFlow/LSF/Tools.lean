module

public import MinCostFlow.Basic.Forest
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Static low-stretch spanning tree interface (Theorem 2.2)

This file states the specification of the static low-stretch spanning tree algorithm of Theorem 2.2
(page 7 of the paper): given a graph `G = (V, E)` with positive lengths `ℓ ∈ ℝ^E_{>0}` and
positive weights `v ∈ ℝ^E_{>0}`, it returns a tree `T` spanning `V` such that
`∑_{e ∈ E} v_e str^{T,ℓ}_e ≤ γ_LSST ‖v‖₁` with `γ_LSST = O(log² n)`.

The model of Lemma 5.4 (`MinCostFlow.LSF.Model`) takes any function satisfying this specification
as a parameter; `MinCostFlow.LSF.Theorem22` derives such a function from
`Cited.LowStretchSpanningTree`.
-/

@[expose] public section

namespace MinCostFlow.LSF

/-- A spanning tree `T` on `G.V` is a `(γ)`-low-stretch tree for `(G, ℓ, v)` (Theorem 2.2, page 7)
if `T` is a spanning tree on `G.V`, edges of `T` that belong to `G` have the same endpoints as in
`G`, the tree path `T[u, v]` for every edge `(u, v)` of `G` uses only edges in `G.E`, and
`∑_{e ∈ E} v_e str^{T,ℓ}_e ≤ γ ‖v‖₁`.

When `G` is connected, `T` can be chosen as a subgraph of `G`; when `G` is disconnected, `T` uses
bridge edges outside `G.E` between components while keeping every `G`-edge's path inside `G.E`. -/
def IsLSST (G : MGraph) (ℓ v : ℕ → ℝ) (γ : ℝ) (T : MGraph) : Prop :=
  T.IsSpanningTreeOn G.V ∧
  (∀ e ∈ T.E, e ∈ G.E → T.tail e = G.tail e ∧ T.head e = G.head e) ∧
  (∀ e ∈ G.E, ∀ f ∈ walkEdges (T.forestPath (G.tail e) (G.head e)), f ∈ G.E) ∧
  ∑ e ∈ G.E, v e * treeStretch G T ℓ e ≤ γ * G.norm1 v

/-- Specification of a static LSST algorithm with `γ_LSST = C * log²(n + 2)` (Theorem 2.2, page 7,
where the paper uses `γ_LSST = O(log² n)` with `log(n + 2)` so the factor is positive for all
`n ≥ 1`). -/
def HasLSSTSpec (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) : Prop :=
  ∀ (G : MGraph) (ℓ v : ℕ → ℝ), G.IsValid → G.V.Nonempty →
    (∀ e ∈ G.E, 0 < ℓ e) → (∀ e ∈ G.E, 0 < v e) →
    IsLSST G ℓ v (C * (Real.log ((G.n : ℝ) + 2)) ^ 2) (oracle G ℓ v)

end MinCostFlow.LSF
