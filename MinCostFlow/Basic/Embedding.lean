module

public import MinCostFlow.Basic.Graph

/-!
# Graph embeddings (Section 2)

Section 2 (page 7):

> Given weighted graphs `G` and `H` with `V(G) ⊆ V(H)`, we say that `Π_{G→H}` is a
> *graph-embedding* from `G` into `H` if it maps each edge `e^G = (u, v) ∈ E(G)` to a `u`-`v` path
> `Π_{G→H}(e^G)` in `H`. Let `w_G` be the weight function of `G` and `w_H` be the weight function
> of `H`. We define the *congestion* of an edge `e^H` by
> `econg(Π_{G→H}, e^H) = (∑_{e^G ∈ E(G) with e^H ∈ Π_{G→H}(e^G)} w_G(e^G)) / w_H(e^H)` and the
> congestion of the embedding by `econg(Π_{G→H}) = max_{e^H ∈ E(H)} econg(Π_{G→H}, e^H)`.
> Analogously, the congestion of a vertex `v^H ∈ V(H)` is defined by
> `vcong(Π_{G→H}, v^H) = ∑_{e^G ∈ E(G) with v^H ∈ Π_{G→H}(e^G)} w_G(e^G)` and the
> vertex-congestion of the graph-embedding by `vcong(Π_{G→H}) = max_{v^H ∈ V(H)} vcong(Π_{G→H}, v^H)`.
> We define the length of the embedding by `length(Π_{G→H}) = max_{e^G ∈ E(G)} |Π_{G→H}(e^G)|`.
>
> Given graphs `A, B, C` and graph-embeddings `Π_{B→C}` from `B` into `C` and `Π_{A→B}` from `A`
> to `B`. We denote by `Π_{B→C} ∘ Π_{A→B}` the graph embedding of `A` into `C` obtained by
> mapping each edge `e^A = (u, v) ∈ E(A)` with path `Π_{A→B}(e^A) = e^B_1 ⊕ e^B_2 ⊕ … ⊕ e^B_k`
> in `B` to the path `Π_{B→C}(e^B_1) ⊕ Π_{B→C}(e^B_2) ⊕ … ⊕ Π_{B→C}(e^B_k)`.

How the definitions read it:

* An embedding maps each edge name to a list of oriented edges (`MinCostFlow/Basic/Graph.lean`).
  A "`u`-`v` path" is read as a walk from `u` to `v`: the composition of two embeddings
  concatenates paths, which can repeat vertices, and the paper still calls the result a path.
* In the composition, a step of `Π_{A→B}(e^A)` that goes along `e^B` backwards is replaced by
  `Π_{B→C}(e^B)` reversed, so that the result is again a walk.
* `e^H ∈ Π(e^G)` and `v^H ∈ Π(e^G)` mean that the walk uses the edge, or visits the vertex; a
  walk that uses an edge twice counts it once.
* The maxima are over the edges of `H` (vertices of `H`, edges of `G`), and are `0` over an empty
  set.
-/

@[expose] public section

namespace MinCostFlow

/-- A map from the edges of one graph to walks in another. -/
abbrev Embedding :=
  ℕ → List (ℕ × Bool)

namespace Embedding

/-- `emb` is a graph-embedding from `G` into `H`: `V(G) ⊆ V(H)`, and each edge `(u, v)` of `G` goes
to a walk from `u` to `v` in `H`. -/
def IsEmbedding (emb : Embedding) (G H : MGraph) : Prop :=
  G.V ⊆ H.V ∧ ∀ e ∈ G.E, H.IsWalk (G.tail e) (G.head e) (emb e)

/-- `econg(Π, e^H)`: the total weight of the edges of `G` whose walk uses `e^H`, divided by the
weight of `e^H`. -/
noncomputable def econgAt (emb : Embedding) (G : MGraph) (wG wH : ℕ → ℝ) (eH : ℕ) : ℝ :=
  (∑ e ∈ G.E with eH ∈ walkEdges (emb e), wG e) / wH eH

/-- `vcong(Π, v^H)`: the total weight of the edges `e^G` of `G` whose walk in `H` visits `v^H`
(its first vertex is the tail of `e^G`). -/
noncomputable def vcongAt (emb : Embedding) (G H : MGraph) (wG : ℕ → ℝ) (vH : ℕ) : ℝ :=
  ∑ e ∈ G.E with vH ∈ H.walkVertices (G.tail e) (emb e), wG e

/-- `econg(Π) = max_{e^H ∈ E(H)} econg(Π, e^H)` (`0` if `H` has no edge). -/
noncomputable def econg (emb : Embedding) (G H : MGraph) (wG wH : ℕ → ℝ) : ℝ :=
  if h : H.E.Nonempty then H.E.sup' h (econgAt emb G wG wH) else 0

/-- `vcong(Π) = max_{v^H ∈ V(H)} vcong(Π, v^H)` (`0` if `H` has no vertex). -/
noncomputable def vcong (emb : Embedding) (G H : MGraph) (wG : ℕ → ℝ) : ℝ :=
  if h : H.V.Nonempty then H.V.sup' h (vcongAt emb G H wG) else 0

/-- `length(Π) = max_{e^G ∈ E(G)} |Π(e^G)|`, the largest number of steps of a walk. -/
def length (emb : Embedding) (G : MGraph) : ℕ :=
  G.E.sup fun e => (emb e).length

/-- `Π_{B→C} ∘ Π_{A→B}`: each step of `Π_{A→B}(e^A)` along `e^B` is replaced by `Π_{B→C}(e^B)`,
and each step against `e^B` by `Π_{B→C}(e^B)` reversed. -/
def comp (embBC embAB : Embedding) : Embedding :=
  fun e => (embAB e).flatMap fun x => if x.2 then embBC x.1 else walkRev (embBC x.1)

end Embedding

end MinCostFlow
