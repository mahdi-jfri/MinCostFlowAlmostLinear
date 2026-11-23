module

public import MinCostFlow.Basic.Graph

/-!
# Forests, rooted spanning forests and stretch (Sections 2 and 5.1)

Section 2 (page 6):

> For a forest `F`, we use `F[u, v]` to denote the unique simple path from `u` to `v` along edges
> in the forest `F`; we ensure that `u, v` are in the same connected component of `F` whenever
> this notation is used. Additionally, we let `p(F[u, v]) ∈ ℝ^{E(G)}` denote the flow vector
> which routes one unit from `u` to `v` along the path in `F`. […]
>
> The *stretch* of `e = (u, v)` with respect to a tree `T` and lengths `ℓ ∈ ℝ^E_{>0}` is defined
> as `str^{T,ℓ}_e = 1 + ⟨ℓ, |p(T[u, v])|⟩/ℓ_e = 1 + (∑_{e' ∈ T[u, v]} ℓ_{e'})/ℓ_e`.

Definition 5.2 (rooted spanning forest, page 17):

> A *rooted spanning forest* of a graph `G = (V, E)` is a forest `F` on `V` such that each
> connected component of `F` has a unique distinguished vertex known as the *root*. We denote the
> root of the connected component of a vertex `v ∈ V` as `root^F_v`.

Definition 5.3 (stretches of `F`, page 17):

> Given a rooted spanning forest `F` of a graph `G = (V, E)` with lengths `ℓ ∈ ℝ^E_{>0}`, the
> stretch of an edge `e = (u, v) ∈ E` is given by
> `str^{F,ℓ}_e = 1 + ⟨ℓ, |p(F[u, v])|⟩/ℓ_e` if `root^F_u = root^F_v`, and
> `str^{F,ℓ}_e = 1 + ⟨ℓ, |p(F[u, root^F_u])| + |p(F[v, root^F_v])|⟩/ℓ_e` if
> `root^F_u ≠ root^F_v`.

How the definitions read it:

* A forest is itself a graph (`MGraph`) with no cycle. Its edges need not be edges of `G`: the
  tree `T` of Lemma 5.4 is static while `G` changes, and Definition 5.6 allows `T` to be "neither
  a spanning tree nor a subgraph of `G`".
* A rooted forest is a forest with a set `R` of roots, one in each connected component. A rooted
  spanning forest of `G` is a subgraph of `G`.
* `F[u, v]` (`forestPath`) is a path from `u` to `v` in `F` (the unique one, when `F` is a forest
  and `u, v` are connected; uniqueness is a lemma). When there is none it is the empty list; the
  paper never uses `F[u, v]` then.
* The lengths of the two paths to the roots in the second case are added; they use different
  edges, so `⟨ℓ, |p(P₁)| + |p(P₂)|⟩ = ⟨ℓ, |p(P₁)|⟩ + ⟨ℓ, |p(P₂)|⟩`.
-/

@[expose] public section

namespace MinCostFlow

namespace MGraph

variable (G : MGraph)

/-- `u` and `v` are in the same connected component of `G`: some walk joins them. -/
def Connected (u v : ℕ) : Prop :=
  ∃ P, G.IsWalk u v P

/-- `G` is a forest: a well-formed graph with no cycle. -/
def IsForest : Prop :=
  G.IsValid ∧ ∀ P, ¬ G.IsCycle P

/-- `T` is a spanning tree of the vertex set `V`: a forest on `V` in which every two vertices are
connected. -/
def IsSpanningTreeOn (V : Finset ℕ) : Prop :=
  G.IsForest ∧ G.V = V ∧ ∀ u ∈ V, ∀ v ∈ V, G.Connected u v

/-- `F[u, v]`: a path from `u` to `v` in `F`, or the empty list if there is none. -/
noncomputable def forestPath (F : MGraph) (u v : ℕ) : List (ℕ × Bool) :=
  open Classical in
  if h : ∃ P, F.IsPath u v P then Classical.choose h else []

end MGraph

/-- A rooted forest: a forest `F` with a set `R` of roots (Definition 5.2, page 17). -/
structure RootedForest where
  /-- The forest. -/
  F : MGraph
  /-- The roots. -/
  R : Finset ℕ

namespace RootedForest

variable (RF : RootedForest)

/-- `RF` is a rooted spanning forest of `G` (Definition 5.2): a forest on `V(G)` in which every
vertex is connected to exactly one root, whose edges are edges of `G` with the same ends.

The last condition is how [chen2022maximum, Appendix B.3] uses the words "spanning forest of `G`":
"every spanning tree/forest of `G_v` is also a spanning tree/forest of `G`" (proof of their Lemma
6.5), and the core graph `𝒞(G, F)` contracts edges of `G` (Definition 5.6). -/
def IsRootedSpanningForestOf (G : MGraph) : Prop :=
  RF.F.IsForest ∧ RF.F.V = G.V ∧ RF.R ⊆ G.V ∧ (∀ v ∈ G.V, ∃! r, r ∈ RF.R ∧ RF.F.Connected v r) ∧
    G.IsSubgraph RF.F

/-- `root^F_v`: the root connected to `v` (or `v` itself if there is none). -/
noncomputable def root (v : ℕ) : ℕ :=
  open Classical in
  if h : ∃ r, r ∈ RF.R ∧ RF.F.Connected v r then Classical.choose h else v

/-- The stretch `str^{F,ℓ}_e` of the edge `e = (u, v)` of `G` (Definition 5.3, page 17). -/
noncomputable def stretch (G : MGraph) (ℓ : ℕ → ℝ) (e : ℕ) : ℝ :=
  let u := G.tail e
  let v := G.head e
  if RF.root u = RF.root v then
    1 + walkLength ℓ (MGraph.forestPath RF.F u v) / ℓ e
  else
    1 + (walkLength ℓ (MGraph.forestPath RF.F u (RF.root u)) +
      walkLength ℓ (MGraph.forestPath RF.F v (RF.root v))) / ℓ e

end RootedForest

/-- The stretch `str^{T,ℓ}_e = 1 + ⟨ℓ, |p(T[u, v])|⟩/ℓ_e` of the edge `e = (u, v)` of `G` with
respect to a tree `T` (Section 2, page 6). -/
noncomputable def treeStretch (G T : MGraph) (ℓ : ℕ → ℝ) (e : ℕ) : ℝ :=
  1 + walkLength ℓ (MGraph.forestPath T (G.tail e) (G.head e)) / ℓ e

end MinCostFlow
