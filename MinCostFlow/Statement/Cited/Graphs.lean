module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Sym.Sym2

/-!
# Graphs in the cited results

The cited results stated in `MinCostFlow/Statement/Cited/` are about undirected graphs. This file fixes the common objects, each stated as the sources define it.

A graph has vertices `0, …, n - 1` and a list of edges; edge number `j` joins `edges[j].1` and
`edges[j].2`. Several edges may join the same two vertices, so a graph is a multigraph. Each source
says which graphs it allows (loopless, or simple); the statements state these conditions.

For a set `X` of vertices, the graph `G[X]` has the vertices of `X` and the edges with both ends
in `X`. Inside `G[X]`, the degree of a vertex counts the ends of edges at it (`degIn`), the volume
of a set is the sum of the degrees of its vertices (`volIn`), and the cut of a set `S ⊆ X` is the
number of edges with exactly one end in `S` (`cutIn`). The whole graph is `X = {0, …, n - 1}`
(`verts`).

The expansion conditions are written with a product instead of a quotient,
`φ · min(vol(S), vol(X \ S)) ≤ cut(S)`. The sources write the quotient. The two agree when the
minimum is positive; when it is `0` the product form holds and the quotient is `0/0`, which the
sources do not use.
-/

@[expose] public section

namespace MinCostFlow.Cited

/-- An undirected graph on the vertices `0, …, n - 1`. Edge number `j` joins `edges[j].1` and
`edges[j].2`. -/
structure Graph where
  /-- The number of vertices. -/
  n : ℕ
  /-- The edges. -/
  edges : List (ℕ × ℕ)

namespace Graph

/-- The number of edges. -/
def m (G : Graph) : ℕ :=
  G.edges.length

/-- The set of vertices `{0, …, n - 1}`. -/
def verts (G : Graph) : Finset ℕ :=
  Finset.range G.n

/-- The ends of every edge are vertices. -/
def IsValid (G : Graph) : Prop :=
  ∀ e ∈ G.edges, e.1 < G.n ∧ e.2 < G.n

/-- No edge joins a vertex to itself. -/
def IsLoopless (G : Graph) : Prop :=
  ∀ e ∈ G.edges, e.1 ≠ e.2

/-- The graph is simple: no loop, and no two edges join the same two vertices. -/
def IsSimple (G : Graph) : Prop :=
  G.IsLoopless ∧ G.edges.Pairwise fun e f => s(e.1, e.2) ≠ s(f.1, f.2)

/-- The edges of `G[X]`: those with both ends in `X`. -/
def inside (G : Graph) (X : Finset ℕ) : List (ℕ × ℕ) :=
  G.edges.filter fun e => decide (e.1 ∈ X) && decide (e.2 ∈ X)

/-- The degree of `v` in `G[X]`: the number of ends at `v` of edges of `G[X]` (a loop at `v`
counts twice). -/
def degIn (G : Graph) (X : Finset ℕ) (v : ℕ) : ℕ :=
  ((G.inside X).filter fun e => e.1 = v).length + ((G.inside X).filter fun e => e.2 = v).length

/-- The volume of `S` in `G[X]`: the sum of the degrees in `G[X]` of the vertices of `S`. -/
def volIn (G : Graph) (X S : Finset ℕ) : ℕ :=
  ∑ v ∈ S, G.degIn X v

/-- The cut of `S` in `G[X]`: the number of edges of `G[X]` with exactly one end in `S`. -/
def cutIn (G : Graph) (X S : Finset ℕ) : ℕ :=
  ((G.inside X).filter fun e => decide (e.1 ∈ S) != decide (e.2 ∈ S)).length

/-- The degree of `v` in `G`. -/
def deg (G : Graph) (v : ℕ) : ℕ :=
  G.degIn G.verts v

/-- The volume of `S` in `G`. -/
def vol (G : Graph) (S : Finset ℕ) : ℕ :=
  G.volIn G.verts S

/-- The cut of `S` in `G`, written `δ_G(S)` or `|E_G(S, V \ S)|`. -/
def cut (G : Graph) (S : Finset ℕ) : ℕ :=
  G.cutIn G.verts S

/-- `G[X]` has conductance at least `φ`: every `S ⊆ X` with `S ≠ ∅` and `S ≠ X` has
`φ · min(vol(S), vol(X \ S)) ≤ cut(S)` in `G[X]`. -/
def IsConductanceExpanderOn (G : Graph) (X : Finset ℕ) (φ : ℝ) : Prop :=
  ∀ S ⊆ X, S.Nonempty → S ≠ X →
    φ * min (G.volIn X S : ℝ) (G.volIn X (X \ S)) ≤ G.cutIn X S

/-- `G[X]` has expansion at least `ψ`: every `S ⊆ X` with `S ≠ ∅` and `S ≠ X` has
`ψ · min(|S|, |X \ S|) ≤ cut(S)` in `G[X]`. -/
def IsExpansionExpanderOn (G : Graph) (X : Finset ℕ) (ψ : ℝ) : Prop :=
  ∀ S ⊆ X, S.Nonempty → S ≠ X →
    ψ * min (S.card : ℝ) (X \ S).card ≤ G.cutIn X S

/-- The graph written as a list of words: `n`, `m`, then the two ends of each edge in order. -/
def encode (G : Graph) : List ℕ :=
  G.n :: G.m :: G.edges.flatMap fun e => [e.1, e.2]

end Graph

/-- `P` is a path from `u` to `v` along the edges `E`: a list of vertices that starts at `u`, ends
at `v`, and in which consecutive vertices are joined by an edge of `E`. It is simple when no vertex
repeats. Its length is its number of edges, `P.length - 1`. -/
def IsPathAlong (E : List (ℕ × ℕ)) (u v : ℕ) (P : List ℕ) : Prop :=
  P.head? = some u ∧ P.getLast? = some v ∧
    P.IsChain fun x y => (x, y) ∈ E ∨ (y, x) ∈ E

end MinCostFlow.Cited
