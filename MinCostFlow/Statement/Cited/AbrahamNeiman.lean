module

public import WordRAM.Model
public import MinCostFlow.Statement.Cited.Graphs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Low-stretch spanning trees (Abraham and Neiman)

This file states Theorem 1 of

> I. Abraham and O. Neiman, *Using Petal-Decompositions to Build a Low Stretch Spanning Tree*,
> SIAM Journal on Computing 48(2), 227–248, 2019.

The paper cites it as [AN19] for its Theorem 2.2 (page 7), and uses it through Lemma 6.5 of
[chen2022maximum], whose proof our Lemma 5.4 modifies.

The source (abstract, page 227; Theorem 1 and the remark after it, page 228; Section 2, page
233):

> We prove that any weighted graph `G = (V, E, w)` with `n` points and `m` edges has a spanning
> tree `T` such that `∑_{{u,v} ∈ E} d_T(u,v)/w(u,v) = O(m log n log log n)`. Moreover, such a tree
> can be found in time `O(m log n log log n)`.
>
> Given a spanning tree `T`, let `avg-stretch_T(G) = (1/|E|) ∑_{{u,v} ∈ E} d_T(u,v)/w(u,v)`. Let
> `avg-stretch(n) = max_{G=(V,E,w) : |V|=n} min_T {avg-stretch_T(G)}`.
>
> **Theorem 1.** `avg-stretch(n) = O(log n log log n)`. Moreover, such a tree can be found in
> `O(m log n log log n)` time.
>
> Since our result holds for multigraphs, […]
>
> Let `G = (V, E, w)` be a weighted undirected graph; we shall assume throughout the paper that
> `w(e) ≥ 1` for all edges `e ∈ E`.

How the statement reads it:

* The graph is a connected multigraph without loops, with weights that are integers at least `1`.
  A spanning tree exists only for a connected graph. Integer weights are what the machine reads;
  the source's weights are reals at least `1`.
* "Such a tree can be found": a program `P` that, for every sequence of random bits, halts with a
  spanning tree whose total stretch is `O(m log n log log n)`, within `O(m log n log log n)` steps.
  The paper's algorithm uses no randomness, and the statement asks nothing of the random bits.
* The tree is the list of the numbers of its edges.
* `O(m log n log log n)` is `K·m·log(n+2)·log(log(n+2))`, and the time also has `m + 1` for `m`.
  This changes the bound by at most a constant factor when `n ≥ 3`, keeps it positive for every
  `n ≥ 1`, and lets a program read its input when `m = 0`.
* The source's time is analysed with unit-cost operations on real weights, including rounding a
  weight to a power of `2` (Section 6). On the word RAM, where a weight `W` is a word, such a
  rounding costs `O(log log W)` steps, and the algorithm does it for each edge at each of its
  `O(log n)` levels. The time therefore also allows `K·(m+1)·log(n+2)·log(log(W+2)+2)` for the
  largest weight `W`, which only weakens the statement.
-/

@[expose] public section

namespace MinCostFlow.Cited

open WordRAM

/-- A weighted undirected graph on the vertices `0, …, n - 1`. Edge number `j` is
`edges[j] = (u, v, w)`: it joins `u` and `v` and has weight `w`. -/
structure WGraph where
  /-- The number of vertices. -/
  n : ℕ
  /-- The edges, with their weights. -/
  edges : List (ℕ × ℕ × ℕ)

namespace WGraph

/-- The number of edges. -/
def m (G : WGraph) : ℕ :=
  G.edges.length

/-- The unweighted graph of `G`. -/
def graph (G : WGraph) : Graph :=
  ⟨G.n, G.edges.map fun e => (e.1, e.2.1)⟩

/-- Edge number `j`. -/
def edge (G : WGraph) (j : Fin G.m) : ℕ × ℕ × ℕ :=
  G.edges[j.1]'j.2

/-- `es` is a walk from `u` to `v` along the edges of `G` whose numbers are in `T`, listed by
their numbers. -/
inductive IsWalkIn (G : WGraph) (T : List ℕ) : ℕ → ℕ → List ℕ → Prop
  | nil (u : ℕ) : IsWalkIn G T u u []
  | cons {u x v j : ℕ} {es : List ℕ} (hj : j ∈ T) (h : j < G.m)
      (hend : (G.edges[j]'h).1 = u ∧ (G.edges[j]'h).2.1 = x ∨
        (G.edges[j]'h).1 = x ∧ (G.edges[j]'h).2.1 = u) :
      IsWalkIn G T x v es → IsWalkIn G T u v (j :: es)

/-- The weight of a list of edge numbers. -/
def weightOf (G : WGraph) (es : List ℕ) : ℕ :=
  (es.map fun j => (G.edges.getD j (0, 0, 0)).2.2).sum

/-- `d_T(u, v)`: the least weight of a walk from `u` to `v` along the edges of `T`. In a tree it is
the weight of the unique path. -/
noncomputable def treeDist (G : WGraph) (T : List ℕ) (u v : ℕ) : ℕ :=
  sInf {d | ∃ es, G.IsWalkIn T u v es ∧ d = G.weightOf es}

/-- `G` is connected: it has a vertex, and every two vertices are joined by a walk. -/
def IsConnected (G : WGraph) : Prop :=
  0 < G.n ∧ ∀ u < G.n, ∀ v < G.n, ∃ es, G.IsWalkIn (List.range G.m) u v es

/-- `T` is a spanning tree of `G`: `n - 1` different edge numbers of `G` whose edges join every
two vertices. A connected graph on `n` vertices with `n - 1` edges is a tree. -/
def IsSpanningTree (G : WGraph) (T : List ℕ) : Prop :=
  T.Nodup ∧ (∀ j ∈ T, j < G.m) ∧ T.length = G.n - 1 ∧
    ∀ u < G.n, ∀ v < G.n, ∃ es, G.IsWalkIn T u v es

/-- The total stretch `∑_{{u,v} ∈ E} d_T(u,v)/w(u,v)` of the edges of `G` in `T`. -/
noncomputable def totalStretch (G : WGraph) (T : List ℕ) : ℝ :=
  ∑ j : Fin G.m, (G.treeDist T (G.edge j).1 (G.edge j).2.1 : ℝ) / (G.edge j).2.2

/-- The largest weight (`0` if there is no edge). -/
def maxWeight (G : WGraph) : ℕ :=
  (G.edges.map fun e => e.2.2).foldr max 0

/-- The graph written as a list of words: `n`, `m`, then the two ends and the weight of each
edge. -/
def encode (G : WGraph) : List ℕ :=
  G.n :: G.m :: G.edges.flatMap fun e => [e.1, e.2.1, e.2.2]

end WGraph

/-- `log(n+2)·log(log(n+2))`, the factor `log n log log n` of the source. -/
noncomputable def logLogFactor (n : ℕ) : ℝ :=
  Real.log ((n : ℝ) + 2) * Real.log (Real.log ((n : ℝ) + 2))

/-- `log(n+2)·log(log(W+2)+2)`, the cost of rounding weights at most `W` at `O(log n)` levels. -/
noncomputable def weightFactor (n W : ℕ) : ℝ :=
  Real.log ((n : ℝ) + 2) * Real.log (Real.log ((W : ℝ) + 2) + 2)

/-- **[AN19], Theorem 1** (SIAM J. Comput. 48(2), 2019, page 228): there are a program `P`, a
word size constant `c` and a constant `K` such that on every connected loopless multigraph with
integer weights at least `1`, for every sequence of random bits, `P` halts with a spanning tree
`T` with `∑_{{u,v} ∈ E} d_T(u,v)/w(u,v) ≤ K·m·log(n+2)·log(log(n+2))`, within
`K·(m+1)·(log(n+2)·log(log(n+2)) + log(n+2)·log(log(W+2)+2))` steps, where `W` is the largest
weight. It is proved as `MinCostFlow.LowStretch.lowStretchSpanningTree_lsst`
(`MinCostFlow/LowStretch/ProgClusterSetupLs.lean`). -/
def LowStretchSpanningTree : Prop :=
  ∃ (P : Program) (c : ℕ) (K : ℝ),
    ∀ G : WGraph, G.graph.IsValid → G.graph.IsLoopless → G.IsConnected →
      (∀ e ∈ G.edges, 1 ≤ e.2.2) → ∀ ω, ∃ out cost,
        RunsTo (wordSize c G.encode) P G.encode ω out cost ∧ G.IsSpanningTree out ∧
        G.totalStretch out ≤ K * G.m * logLogFactor G.n ∧
        (cost : ℝ) ≤ K * (G.m + 1) * (logLogFactor G.n + weightFactor G.n G.maxWeight)

end MinCostFlow.Cited
