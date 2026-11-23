module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Graphs, flows and walks (Section 2)

This file fixes the graphs, flows and walks of Sections 2, 4, 5 and 6 of the paper, as Section 2
(page 5) defines them:

> We consider multi-graphs `G` with edge set `E(G)` and vertex set `V(G)`. […] We assume that each
> edge `e ∈ E` has an implicit direction and overload the notation slightly by writing
> `e = (u, v)` where `u` and `v` are the tail and head of `e` respectively […]. We let `rev(e)` be
> the edge `e` reversed.
>
> A *flow vector* is a vector `f ∈ ℝ^E`. If `f_e ≥ 0`, this means that `f_e` units flow in the
> implicit direction of the edge `e` chosen, and if `f_e ≤ 0`, then `|f_e|` units flow in the
> opposite direction. […] For an edge `e = (u, v) ∈ G` we let `b_e ∈ ℝ^V` denote the demand
> vector of routing one unit from `u` to `v`, i.e., `b_e` has a `1` at `u`, `-1` at `v`, and `0`
> elsewhere. Define the edge-vertex incidence matrix `B ∈ ℝ^{E × V}` as the matrix whose rows are
> `b_e`. We say that a flow `f` routes a demand `d` if `Bᵀ f = d`.
>
> We denote by `deg_G(v)` the combinatorial degree of `v` in `G`, i.e., the number of incident
> edges. […] We define the volume of a set `S ⊆ V` as `vol_G(S) = ∑_{v ∈ S} deg_G(v)`.

How the definitions read it:

* Vertices and edges are named by natural numbers: a graph is a finite set `V` of vertex names, a
  finite set `E` of edge names, and the tail and head of each edge. The names stay fixed while the
  graph changes (edge insertions and deletions, vertex splits; `MinCostFlow/Basic/Dynamic.lean`),
  and different graphs of the paper share them: the core graph `𝒞(G, F)` has the edges of `G`
  (Definition 5.6), and a sparsified core graph is a subgraph of it (Definition 5.7).
* Vectors on edges and on vertices are functions `ℕ → ℝ`; only their values on `E` (or `V`)
  matter. The tail and head functions are total; only their values on `E` matter.
* An edge from a vertex to itself is allowed (contracting a forest creates such edges); then
  `b_e = 0`, and it counts twice in the degree of its vertex.
* A walk is a list of *oriented edges* `(e, true)` (along `e`, from its tail to its head) and
  `(e, false)` (along `rev(e)`). Its flow vector `p(P)` adds `+1` on `e` for each use of
  `(e, true)` and `-1` for each use of `(e, false)`; a walk from `u` to `v` routes one unit from
  `u` to `v` (`walkFlow`, `demand_walkFlow` is proved by the tracks that need it).
-/

@[expose] public section

namespace MinCostFlow

/-- A directed multigraph whose vertices and edges are named by natural numbers: the vertex set
`V`, the edge set `E`, and the tail and head of each edge (Section 2, page 5). -/
structure MGraph where
  /-- The vertices. -/
  V : Finset ℕ
  /-- The edges. -/
  E : Finset ℕ
  /-- The tail `u` of `e = (u, v)`. -/
  tail : ℕ → ℕ
  /-- The head `v` of `e = (u, v)`. -/
  head : ℕ → ℕ

namespace MGraph

variable (G : MGraph)

/-- The graph is well formed: both ends of every edge are vertices. -/
def IsValid : Prop :=
  ∀ e ∈ G.E, G.tail e ∈ G.V ∧ G.head e ∈ G.V

/-- `m = |E|`. -/
def m : ℕ :=
  G.E.card

/-- `n = |V|`. -/
def n : ℕ :=
  G.V.card

/-- The entry of `b_e` at vertex `v`: `1` at the tail, `-1` at the head, `0` elsewhere (and `0`
everywhere for an edge from a vertex to itself). -/
def b (e v : ℕ) : ℝ :=
  (if v = G.tail e then 1 else 0) - (if v = G.head e then 1 else 0)

/-- The demand routed by the flow `f`, `(Bᵀ f)_v = ∑_{e ∈ E} (b_e)_v f_e`. -/
def demand (f : ℕ → ℝ) (v : ℕ) : ℝ :=
  ∑ e ∈ G.E, G.b e v * f e

/-- The flow `f` routes the demand `d`: `Bᵀ f = d` on the vertices. -/
def Routes (f d : ℕ → ℝ) : Prop :=
  ∀ v ∈ G.V, G.demand f v = d v

/-- `f` is a circulation: `Bᵀ f = 0`. -/
def IsCirculation (f : ℕ → ℝ) : Prop :=
  ∀ v ∈ G.V, G.demand f v = 0

/-- `⟨x, y⟩ = ∑_{e ∈ E} x_e y_e` for vectors on the edges. -/
def inner (x y : ℕ → ℝ) : ℝ :=
  ∑ e ∈ G.E, x e * y e

/-- `‖diag(ℓ) f‖₁ = ∑_{e ∈ E} ℓ_e |f_e|`; for positive `ℓ` this is `⟨ℓ, |f|⟩`. -/
def lnorm (ℓ f : ℕ → ℝ) : ℝ :=
  ∑ e ∈ G.E, ℓ e * |f e|

/-- `‖x‖₁ = ∑_{e ∈ E} |x_e|`. -/
def norm1 (x : ℕ → ℝ) : ℝ :=
  ∑ e ∈ G.E, |x e|

/-- The degree `deg_G(v)`: the number of ends at `v` of edges of `G` (a loop at `v` counts
twice). -/
def deg (v : ℕ) : ℕ :=
  (G.E.filter fun e => G.tail e = v).card + (G.E.filter fun e => G.head e = v).card

/-- The volume `vol_G(S) = ∑_{v ∈ S} deg_G(v)`. -/
def vol (S : Finset ℕ) : ℕ :=
  ∑ v ∈ S, G.deg v

/-- The maximum degree `Δ_max(G)` (`0` for a graph without vertices). -/
def maxDeg : ℕ :=
  G.V.sup G.deg

/-- `H` is a subgraph of `G`: its vertices and edges are vertices and edges of `G`, and its edges
have the same ends. -/
def IsSubgraph (H : MGraph) : Prop :=
  H.V ⊆ G.V ∧ H.E ⊆ G.E ∧ ∀ e ∈ H.E, H.tail e = G.tail e ∧ H.head e = G.head e

/-- The vertex where the oriented edge `x` starts: the tail of `x.1` if `x.2`, else its head. -/
def src (x : ℕ × Bool) : ℕ :=
  if x.2 then G.tail x.1 else G.head x.1

/-- The vertex where the oriented edge `x` ends. -/
def dst (x : ℕ × Bool) : ℕ :=
  if x.2 then G.head x.1 else G.tail x.1

/-- `P` is a walk from `u` to `v` in `G`: a list of oriented edges of `G`, each starting where
the previous one ends. -/
inductive IsWalk : ℕ → ℕ → List (ℕ × Bool) → Prop
  | nil (u : ℕ) : IsWalk u u []
  | cons {u v : ℕ} {x : ℕ × Bool} {P : List (ℕ × Bool)} :
      x.1 ∈ G.E → G.src x = u → IsWalk (G.dst x) v P → IsWalk u v (x :: P)

/-- The vertices of the walk `P` started at `u`, in order: `u`, then the end of each step. -/
def walkVertices (u : ℕ) (P : List (ℕ × Bool)) : List ℕ :=
  u :: P.map G.dst

/-- `P` is a path from `u` to `v`: a walk whose vertices are distinct. A path uses each edge at
most once. -/
def IsPath (u v : ℕ) (P : List (ℕ × Bool)) : Prop :=
  G.IsWalk u v P ∧ (G.walkVertices u P).Nodup

/-- `P` is a cycle: a nonempty closed walk that uses no edge twice. -/
def IsCycle (P : List (ℕ × Bool)) : Prop :=
  P ≠ [] ∧ (P.map Prod.fst).Nodup ∧ ∃ u, G.IsWalk u u P

end MGraph

/-- The flow vector `p(P)` of a list of oriented edges: on edge `e`, the number of steps
`(e, true)` minus the number of steps `(e, false)` (Section 2, page 6: "`p(F[u, v])` … the flow
vector which routes one unit from `u` to `v` along the path"). -/
def walkFlow (P : List (ℕ × Bool)) (e : ℕ) : ℝ :=
  (P.map fun x => if x.1 = e then (if x.2 then (1 : ℝ) else -1) else 0).sum

/-- The edges that `P` uses. -/
def walkEdges (P : List (ℕ × Bool)) : Finset ℕ :=
  (P.map Prod.fst).toFinset

/-- `⟨x, p(P)⟩`, the inner product of a vector on edges with the flow vector of `P`. -/
def walkInner (x : ℕ → ℝ) (P : List (ℕ × Bool)) : ℝ :=
  ∑ e ∈ walkEdges P, x e * walkFlow P e

/-- `⟨ℓ, |p(P)|⟩`, the length of `P` for lengths `ℓ`. -/
def walkLength (ℓ : ℕ → ℝ) (P : List (ℕ × Bool)) : ℝ :=
  ∑ e ∈ walkEdges P, ℓ e * |walkFlow P e|

/-- The reversed walk: the steps in the opposite order, each along the opposite orientation. -/
def walkRev (P : List (ℕ × Bool)) : List (ℕ × Bool) :=
  (P.map fun x => (x.1, !x.2)).reverse

/-- The ratio `⟨g, Δ⟩ / ‖diag(ℓ) Δ‖₁` of the min-ratio cycle problem (Definition 4.2, page 14). -/
noncomputable def ratio (G : MGraph) (g ℓ Δ : ℕ → ℝ) : ℝ :=
  G.inner g Δ / G.lnorm ℓ Δ

end MinCostFlow
