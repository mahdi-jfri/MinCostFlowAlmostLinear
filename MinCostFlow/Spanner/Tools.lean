module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Spanner.Embedding
public import Mathlib.Data.Nat.Log

/-!
# Expander tool specifications for Algorithm 4

This file specifies the three tools used by Algorithm 4 (`Sparsify`, page 42):

1. `IsExpander` (**Definition 8.3**, page 40): conductance expansion on `Cited.Graph`.
2. `ConstructExpanderTool` (**Theorem 8.4**, page 40): deterministic expander construction
   `ConstructExpander(n, w)` with `w ≤ deg_W ≤ c_deg · w` (`c_deg = 18` in the paper).
3. `DecomposeTool` (**Theorem 8.5**, page 41): deterministic expander decomposition `Decompose(G)`
   partitioning a loopless multigraph into `G_0, …, G_ℓ` (`ℓ = O(log m)`).
4. `PathDSTool` (**Theorem 8.6**, page 41): dynamic short-path data structure on a decremental
   expander, maintaining `V̂`, `deleted`, `Delete`, and `GetPath`.

The numeric parameters (`φ_Const`, `c_deg`, `c_ℓ`, `φ_dec`, `φ_out`, `γ_ExpPath`, `γ_del`) are
kept as fields of the tool specifications rather than hardcoded asymptotic expressions.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-- **Definition 8.3** (Expander, `spanner.tex`, page 40):
An unweighted, undirected graph `G` is a `φ`-expander (`φ ∈ (0, 1]`) if for every nonempty proper
subset `S ⊊ V(G)`, `|E_G(S, V \ S)| ≥ φ · min{vol_G(S), vol_G(V \ S)}`. -/
def IsExpander (G : Graph) (φ : ℝ) : Prop :=
  0 < φ ∧ φ ≤ 1 ∧ G.IsConductanceExpanderOn G.verts φ

/-- **Theorem 8.4** (`spanner.tex`, page 40):
Given an integer `n > 1` and a weight vector `w ∈ ℝ_{≥ 1}`, `ConstructExpander(n, w)` constructs an
unweighted `φ_Const`-expander `W` on `n` vertices with `w ≤ Deg_W ≤ c_deg · w` (`c_deg = 18` in
the paper). The constructed graph `W` is valid and may contain self-loops or parallel edges. -/
structure ConstructExpanderTool where
  /-- Expansion parameter `φ_Const ∈ (0, 1]`. -/
  φ_Const : ℝ
  /-- Degree upper multiplier `c_deg` (`18` in Theorem 8.4). -/
  c_deg : ℝ
  /-- `ConstructExpander(n, w)`. -/
  construct : ℕ → (ℕ → ℝ) → Graph
  hφ_pos : 0 < φ_Const
  hφ_le : φ_Const ≤ 1
  hc_deg : 1 ≤ c_deg
  construct_spec : ∀ (n : ℕ) (w : ℕ → ℝ), 1 < n → (∀ v < n, 1 ≤ w v) →
    let W := construct n w
    W.n = n ∧ W.IsValid ∧ W.IsConductanceExpanderOn W.verts φ_Const ∧
      ∀ v < n, w v ≤ (W.deg v : ℝ) ∧ (W.deg v : ℝ) ≤ c_deg * w v

/-- Bounded variant of `ConstructExpanderTool`, restricted to vertex counts `n ≤ N_max` and total
weight `∑_{v < n} w v ≤ W_max` (used for constructing witness instances on finite graphs). -/
structure BoundedConstructExpanderTool (N_max : ℕ) (W_max : ℝ) where
  φ_Const : ℝ
  c_deg : ℝ
  construct : ℕ → (ℕ → ℝ) → Graph
  hφ_pos : 0 < φ_Const
  hφ_le : φ_Const ≤ 1
  hc_deg : 1 ≤ c_deg
  construct_spec : ∀ (n : ℕ) (w : ℕ → ℝ), 1 < n → n ≤ N_max →
    (∀ v < n, 1 ≤ w v) → (∑ v ∈ Finset.range n, w v) ≤ W_max →
    let W := construct n w
    W.n = n ∧ W.IsValid ∧ W.IsConductanceExpanderOn W.verts φ_Const ∧
      ∀ v < n, w v ≤ (W.deg v : ℝ) ∧ (W.deg v : ℝ) ≤ c_deg * w v

/-- Any global `ConstructExpanderTool` restricts to a bounded one. -/
def ConstructExpanderTool.toBounded (t : ConstructExpanderTool) (N_max : ℕ) (W_max : ℝ) :
    BoundedConstructExpanderTool N_max W_max where
  φ_Const := t.φ_Const
  c_deg := t.c_deg
  construct := t.construct
  hφ_pos := t.hφ_pos
  hφ_le := t.hφ_le
  hc_deg := t.hc_deg
  construct_spec n w hn _ hw _ := t.construct_spec n w hn hw

/-- Output of `Decompose(G)` (**Theorem 8.5**, page 41): the level bound `ℓ`, edge-level map
`level`, and the list `comps i` of nontrivial connected components of `G_i` for `0 < i ≤ ℓ`. -/
structure DecomposeOutput where
  /-- Maximum level `ℓ`. -/
  ℓ : ℕ
  /-- Level `0 ≤ level j ≤ ℓ` assigned to edge index `j < G.m`. -/
  level : ℕ → ℕ
  /-- List of nontrivial connected components `X ⊆ V(G)` of `G_i` for `0 < i ≤ ℓ`. -/
  comps : ℕ → List (Finset ℕ)

namespace DecomposeOutput

/-- The original edge indices of `G` assigned to level `i`. -/
def edgesAt (G : Graph) (d : DecomposeOutput) (i : ℕ) : List ℕ :=
  (List.range G.m).filter fun j => decide (d.level j = i)

/-- The subgraph `G_i` of `G` consisting of edges assigned to level `i`. -/
def graphAt (G : Graph) (d : DecomposeOutput) (i : ℕ) : Graph :=
  ⟨G.n, (d.edgesAt G i).map fun j => G.edges.getD j (0, 0)⟩

end DecomposeOutput

/-- **Theorem 8.5** (`spanner.tex`, page 41):
Given a valid loopless multigraph `G`, `Decompose(G)` computes an edge-disjoint partition
`G_0, G_1, …, G_ℓ` with `ℓ ≤ c_ℓ · (log₂(m + 2) + 1)` such that `|E(G_i)| ≤ 2^i · n` for all
`0 ≤ i ≤ ℓ`, and for each `0 < i ≤ ℓ` and nontrivial connected component `X` of `G_i`, `G_i[X]`
is a `φ_dec(G)`-expander with `deg_{G_i[X]}(x) ≥ φ_dec(G) · 2^i` for every `x ∈ X`. -/
structure DecomposeTool where
  /-- Constant `c_ℓ ≥ 1` in `ℓ ≤ c_ℓ · (log₂(m + 2) + 1)`. -/
  c_ℓ : ℝ
  /-- Conductance guarantee `φ` on `G`. -/
  φ_dec : Graph → ℝ
  /-- `Decompose(G)`. -/
  decompose : Graph → DecomposeOutput
  hc_ℓ : 1 ≤ c_ℓ
  hφ_pos : ∀ G : Graph, G.IsValid → G.IsLoopless → 0 < φ_dec G
  hφ_le : ∀ G : Graph, G.IsValid → G.IsLoopless → φ_dec G ≤ 1
  decompose_spec : ∀ G : Graph, G.IsValid → G.IsLoopless →
    let d := decompose G
    (d.ℓ : ℝ) ≤ c_ℓ * ((Nat.log 2 (G.m + 2) : ℝ) + 1) ∧
    (∀ j < G.m, d.level j ≤ d.ℓ) ∧
    (∀ i ≤ d.ℓ, (d.graphAt G i).m ≤ 2 ^ i * G.n) ∧
    (∀ i, 0 < i → i ≤ d.ℓ →
      (d.comps i).Pairwise Disjoint ∧
      (∀ X ∈ d.comps i, X ⊆ G.verts ∧ 2 ≤ X.card ∧
        (d.graphAt G i).IsConductanceExpanderOn X (φ_dec G) ∧
        (∀ x ∈ X, φ_dec G * (2 ^ i : ℝ) ≤ ((d.graphAt G i).degIn X x : ℝ)) ∧
        (∀ e ∈ (d.graphAt G i).edges, e.1 ∈ X ↔ e.2 ∈ X)) ∧
      (∀ e ∈ (d.graphAt G i).edges, ∃ X ∈ d.comps i, e.1 ∈ X ∧ e.2 ∈ X))

/-- **Theorem 8.6** (`spanner.tex`, page 41):
Dynamic short-path data structure on a decremental `φ_in`-expander `G` (a valid multigraph with
`1 ≤ G.m ≤ M` and no isolated vertices, possibly with self-loops or parallel edges).
Maintains a monotonically increasing pruned vertex set `V̂ ⊆ V(G)` under `Delete(e)` and answers
`GetPath(u, v)` queries for `u, v ∈ V(G) \ V̂` with simple walks of at most `γ_ExpPath` edges in
`G[V(G) \ V̂] \ deleted`, ensuring `vol_{G^{(0)}}(V̂) ≤ γ_del · t / φ_out` after `t` deletions. -/
structure PathDSTool where
  /-- Abstract state type of the data structure. -/
  State : Type
  /-- Effective conductance parameter `φ_out` in `vol_{G^{(0)}}(V̂) ≤ γ_del · t / φ_out`. -/
  φ_out : ℝ → ℕ → ℝ
  /-- Path length bound `γ_ExpPath`. -/
  γ_ExpPath : ℝ → ℕ → ℝ
  /-- Query and fallback-update runtime overhead `γ_query ≥ γ_ExpPath`.
  Equals `γ_ExpPath` when `[CS21]` covers all regimes; in concrete fallback mode
  (`FallbackPruning`), absorbs `fbCostBound d` for both `Delete` and `GetPath`. -/
  γ_query : ℝ → ℕ → ℝ
  /-- Volume deletion constant `γ_del`. -/
  γ_del : ℝ → ℕ → ℝ
  /-- Initialize on `(φ_in, M, G)`. -/
  init : ℝ → ℕ → Graph → State
  /-- The maintained pruned vertex subset `V̂`. -/
  Vhat : State → Finset ℕ
  /-- The set of deleted edge indices. -/
  deleted : State → Finset ℕ
  /-- `Delete(e)`: removes edge `e` and returns `(newState, V̂_new \ V̂_old)`. -/
  delete : State → ℕ → State × Finset ℕ
  /-- `GetPath(u, v)`: returns a simple `u`-`v` walk in `G[V \ V̂] \ deleted`. -/
  getPath : State → ℕ → ℕ → Walk
  /-- Invariant relating a state to `(φ_in, M, G)`. -/
  Inv : ℝ → ℕ → Graph → State → Prop
  hφ_pos : ∀ φ_in M, 0 < φ_in → 0 < φ_out φ_in M
  hφ_le : ∀ φ_in M, 0 < φ_in → φ_out φ_in M ≤ φ_in
  hφ_half : ∀ φ_in M, 0 < φ_in → φ_out φ_in M ≤ 1 / 2
  hγ_ExpPath_ge : ∀ φ_in M, 0 < φ_in → 1 / φ_out φ_in M ≤ γ_ExpPath φ_in M
  hγ_query_ge : ∀ φ_in M, 0 < φ_in → γ_ExpPath φ_in M ≤ γ_query φ_in M
  hγ_del_ge : ∀ φ_in M, 0 < φ_in → 1 ≤ γ_del φ_in M
  init_inv : ∀ (φ_in : ℝ) (M : ℕ) (G : Graph),
    0 < φ_in → φ_in ≤ 1 → G.IsValid → 1 ≤ G.m → G.m ≤ M →
    (∀ v < G.n, 1 ≤ G.deg v) → G.IsConductanceExpanderOn G.verts φ_in →
    Inv φ_in M G (init φ_in M G)
  init_Vhat : ∀ (φ_in : ℝ) (M : ℕ) (G : Graph),
    0 < φ_in → φ_in ≤ 1 → G.IsValid → 1 ≤ G.m → G.m ≤ M →
    (∀ v < G.n, 1 ≤ G.deg v) → G.IsConductanceExpanderOn G.verts φ_in →
    Vhat (init φ_in M G) = ∅
  init_deleted : ∀ (φ_in : ℝ) (M : ℕ) (G : Graph),
    0 < φ_in → φ_in ≤ 1 → G.IsValid → 1 ≤ G.m → G.m ≤ M →
    (∀ v < G.n, 1 ≤ G.deg v) → G.IsConductanceExpanderOn G.verts φ_in →
    deleted (init φ_in M G) = ∅
  delete_spec : ∀ (φ_in : ℝ) (M : ℕ) (G : Graph) (s : State) (e : ℕ),
    0 < φ_in → φ_in ≤ 1 → G.IsValid → 1 ≤ G.m → G.m ≤ M →
    (∀ v < G.n, 1 ≤ G.deg v) → G.IsConductanceExpanderOn G.verts φ_in →
    Inv φ_in M G s → e < G.m → e ∉ deleted s →
    let res := delete s e
    Inv φ_in M G res.1 ∧
    deleted res.1 = insert e (deleted s) ∧
    Vhat s ⊆ Vhat res.1 ∧
    Vhat res.1 ⊆ G.verts ∧
    res.2 = Vhat res.1 \ Vhat s ∧
    (G.vol (Vhat res.1) : ℝ) ≤ γ_del φ_in M * ((deleted res.1).card : ℝ) / φ_out φ_in M
  getPath_spec : ∀ (φ_in : ℝ) (M : ℕ) (G : Graph) (s : State) (u v : ℕ),
    0 < φ_in → φ_in ≤ 1 → G.IsValid → 1 ≤ G.m → G.m ≤ M →
    (∀ v < G.n, 1 ≤ G.deg v) → G.IsConductanceExpanderOn G.verts φ_in →
    Inv φ_in M G s → u ∈ G.verts \ Vhat s → v ∈ G.verts \ Vhat s →
    let P := getPath s u v
    P.IsWalk G u v ∧ P.verts.Nodup ∧ (∀ e ∈ P.edges, e ∉ deleted s) ∧
      (∀ x ∈ P.verts, x ∉ Vhat s) ∧ (P.edges.length : ℝ) ≤ γ_ExpPath φ_in M

/-- The bundle of the three expander tools used by Algorithm 4 (`Sparsify`). -/
structure SpannerTools where
  constructExpander : ConstructExpanderTool
  decompose : DecomposeTool
  pathDS : PathDSTool

/-- Bounded version of `SpannerTools` for a specific vertex/weight bound `(N_max, W_max)`. -/
structure LocalSpannerTools (N_max : ℕ) (W_max : ℝ) where
  constructExpander : BoundedConstructExpanderTool N_max W_max
  decompose : DecomposeTool
  pathDS : PathDSTool

/-- Restrict global `SpannerTools` to `LocalSpannerTools N_max W_max`. -/
def SpannerTools.toLocal (tools : SpannerTools) (N_max : ℕ) (W_max : ℝ) :
    LocalSpannerTools N_max W_max where
  constructExpander := tools.constructExpander.toBounded N_max W_max
  decompose := tools.decompose
  pathDS := tools.pathDS

end MinCostFlow.Spanner
