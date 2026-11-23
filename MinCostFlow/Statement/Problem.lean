module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic

/-!
# The minimum-cost flow problem

This file defines the problem of Theorem 1.1 of the paper (J. van den Brand, L. Chen, R. Kyng,
Y. P. Liu, R. Peng, M. Probst Gutenberg, S. Sachdeva, A. Sidford, *A Deterministic Almost-Linear
Time Algorithm for Minimum-Cost Flow*, arXiv:2309.16629v1, page 2):

> **Theorem 1.1 (Min-cost flow).** There is a deterministic algorithm that given a `m`-edge graph
> with integral vertex demands and edge capacities bounded by `U` in absolute value, and integral
> edge costs bounded by `C` in absolute value, computes an (exact) minimum-cost flow in time
> `m^{1+o(1)} log U log C`.

Its conventions are those of Section 2 (page 5):

> We consider multi-graphs `G` with edge set `E(G)` and vertex set `V(G)`. […] We assume that
> each edge `e ∈ E` has an implicit direction and overload the notation slightly by writing
> `e = (u, v)` where `u` and `v` are the tail and head of `e` respectively […].
>
> A *flow vector* is a vector `f ∈ ℝ^E`. If `f_e ≥ 0`, this means that `f_e` units flow in the
> implicit direction of the edge `e` chosen, and if `f_e ≤ 0`, then `|f_e|` units flow in the
> opposite direction. A *demand vector* is a vector `d ∈ ℝ^V` with `∑_{v ∈ V} d_v = 0`. For an
> edge `e = (u, v) ∈ G` we let `b_e ∈ ℝ^V` denote the demand vector of routing one unit from `u`
> to `v`, i.e., `b_e` has a `1` at `u`, `-1` at `v`, and `0` elsewhere. Define the edge-vertex
> incidence matrix `B ∈ ℝ^{E × V}` as the matrix whose rows are `b_e`. We say that a flow `f`
> routes a demand `d` if `Bᵀ f = d`.

The paper does not write out the minimum-cost flow problem. It takes it from the framework it
builds on, [chen2022maximum] (L. Chen, R. Kyng, Y. P. Liu, R. Peng, M. Probst Gutenberg,
S. Sachdeva, *Maximum Flow and Minimum-Cost Flow in Almost-Linear Time*, arXiv:2203.00671v2),
which it cites for Theorem 4.6 (page 15). There, Section 4, equation (8), an instance is a graph
with demands `d ∈ ℤ^V`, lower and upper capacities `u⁻, u⁺ ∈ ℤ^E` and costs `c ∈ ℤ^E`, and the
problem is to minimize `cᵀ f` over the flows with `Bᵀ f = d` and `u⁻_e ≤ f_e ≤ u⁺_e` for every
edge. This is why Theorem 1.1 bounds the capacities "in absolute value". The capacities
`0 ≤ f_e ≤ u_e` of the introduction (page 1) are the case `u⁻ = 0`. Lemma 4.12 of
[chen2022maximum] either computes an optimal flow or concludes that the instance admits no
feasible flow.

How the definitions read the paper:

* An instance has vertices `0, …, n - 1`, a list of edges, and a demand for each vertex. Edge
  number `j` is `edges[j]`. It has a tail, a head, a lower and an upper capacity and a cost, all
  integers. Several edges may join the same two vertices. An edge may also join a vertex to
  itself: then `b_e = 0`, and such an edge only adds its cost.
* A flow gives each edge number a real number. It is *feasible* if it routes the demands and lies
  between the capacities on every edge. A *minimum-cost flow* is a feasible flow whose cost is at
  most the cost of every feasible flow.
* The demands of a demand vector add up to `0`. The definitions do not ask this of an instance.
  When the demands do not add up to `0`, no flow routes them (summing `Bᵀ f = d` over all
  vertices gives `0 = ∑ d_v`), and the only correct answer is that there is no feasible flow.
* "Computes an (exact) minimum-cost flow": the answer is an integral minimum-cost flow, or, when
  there is no feasible flow, the statement that there is none. The flow is compared with every
  feasible real flow, as in the paper's Section 4 (page 13), where the rounding of Lemma 4.1
  turns a fractional flow into an integral one of no larger cost.

The file also fixes how instances and answers are written as lists of words for the machine of
`WordRAM/Model.lean`.
-/

@[expose] public section

namespace MinCostFlow

/-- An edge of an instance: its tail, its head, its lower and upper capacities, and its cost per
unit of flow. -/
structure Edge where
  /-- The tail `u` of `e = (u, v)`. -/
  tail : ℕ
  /-- The head `v` of `e = (u, v)`. -/
  head : ℕ
  /-- The lower capacity `u⁻_e`. -/
  lower : ℤ
  /-- The upper capacity `u⁺_e`. -/
  upper : ℤ
  /-- The cost `c_e` of one unit of flow. -/
  cost : ℤ

namespace Edge

/-- The vector `b_e` at vertex `v`: `1` at the tail, `-1` at the head, and `0` elsewhere (Section
2, page 5). For an edge from a vertex to itself the two entries cancel, and `b_e = 0`. -/
def b (e : Edge) (v : ℕ) : ℝ :=
  (if v = e.tail then 1 else 0) - (if v = e.head then 1 else 0)

end Edge

/-- An instance of the minimum-cost flow problem: `n` vertices `0, …, n - 1`, the edges, and the
demand of each vertex. -/
structure Instance where
  /-- The number of vertices. -/
  n : ℕ
  /-- The edges. Edge number `j` is `edges[j]`. -/
  edges : List Edge
  /-- The demands: vertex `v` has demand `demand[v]`. -/
  demand : List ℤ

namespace Instance

/-- The number of edges. -/
def m (I : Instance) : ℕ :=
  I.edges.length

/-- Edge number `j`. -/
def edge (I : Instance) (j : Fin I.m) : Edge :=
  I.edges[j.1]'j.2

/-- The demand `d_v` of vertex `v`. -/
def d (I : Instance) (v : ℕ) : ℤ :=
  I.demand.getD v 0

/-- The instance is well formed: the ends of every edge are vertices, and every vertex has a
demand. -/
def IsValid (I : Instance) : Prop :=
  (∀ e ∈ I.edges, e.tail < I.n ∧ e.head < I.n) ∧ I.demand.length = I.n

/-- The flow `f` routes the demands: `Bᵀ f = d`, that is, `∑_e (b_e)_v f_e = d_v` at every
vertex `v` (Section 2, page 5). -/
def Routes (I : Instance) (f : Fin I.m → ℝ) : Prop :=
  ∀ v : Fin I.n, ∑ j, (I.edge j).b v * f j = I.d v

/-- The flow `f` is feasible: it routes the demands, and `u⁻_e ≤ f_e ≤ u⁺_e` on every edge. -/
def IsFeasible (I : Instance) (f : Fin I.m → ℝ) : Prop :=
  I.Routes f ∧ ∀ j, ((I.edge j).lower : ℝ) ≤ f j ∧ f j ≤ (I.edge j).upper

/-- The cost `cᵀ f = ∑_e c_e f_e` of the flow `f`. -/
def cost (I : Instance) (f : Fin I.m → ℝ) : ℝ :=
  ∑ j, ((I.edge j).cost : ℝ) * f j

/-- `f` is a minimum-cost flow: it is feasible, and its cost is at most the cost of every
feasible flow. -/
def IsMinCostFlow (I : Instance) (f : Fin I.m → ℝ) : Prop :=
  I.IsFeasible f ∧ ∀ g, I.IsFeasible g → I.cost f ≤ I.cost g

/-- The bound `U` of Theorem 1.1: the largest absolute value of a demand or a capacity (`0` if
there is none). -/
def maxCapacity (I : Instance) : ℕ :=
  ((I.edges.map fun e => max e.lower.natAbs e.upper.natAbs) ++ I.demand.map Int.natAbs).foldr
    max 0

/-- The bound `C` of Theorem 1.1: the largest absolute value of a cost (`0` if there is no
edge). -/
def maxCost (I : Instance) : ℕ :=
  (I.edges.map fun e => e.cost.natAbs).foldr max 0

end Instance

/-! ## Words -/

/-- An integer written as two words: `1` if it is negative and `0` otherwise, then its absolute
value. -/
def encodeInt (z : ℤ) : List ℕ :=
  [if z < 0 then 1 else 0, z.natAbs]

/-- An edge written as words: its tail, its head, then its lower capacity, its upper capacity and
its cost as integers. -/
def Edge.encode (e : Edge) : List ℕ :=
  e.tail :: e.head :: (encodeInt e.lower ++ encodeInt e.upper ++ encodeInt e.cost)

namespace Instance

/-- The instance written as a list of words: `n`, `m`, the edges in order, then the demands in
order. -/
def encode (I : Instance) : List ℕ :=
  I.n :: I.m :: (I.edges.flatMap Edge.encode ++ I.demand.flatMap encodeInt)

/-- `out` is a correct answer for `I`. Either `out = [0]` and no flow is feasible, or `out` is `1`
followed by the values `f_0, …, f_{m-1}` of an integral minimum-cost flow `f`, each written as an
integer. -/
def IsCorrectAnswer (I : Instance) (out : List ℕ) : Prop :=
  (out = [0] ∧ ∀ f, ¬ I.IsFeasible f) ∨
  ∃ f : Fin I.m → ℤ, I.IsMinCostFlow (fun j => (f j : ℝ)) ∧
    out = 1 :: (List.finRange I.m).flatMap fun j => encodeInt (f j)

end Instance

end MinCostFlow
