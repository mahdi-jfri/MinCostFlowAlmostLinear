module

public import WordRAM.DataStructure
public import MinCostFlow.Statement.Cited.Graphs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Short paths in decremental expanders (Chuzhoy and Saranurak)

This file states Theorem 3.9 of

> J. Chuzhoy and T. Saranurak, *Deterministic Algorithms for Decremental Shortest Paths via
> Layered Core Decomposition*, SODA 2021, arXiv:2009.08479v1.

The paper cites it as [CS21] ("see Theorem 3.9 in arXiv v1") for its Theorem 8.6 (page 41).
The proof of `MinCostFlow.theorem_1_1` does not use it: the static sparsifier of Theorem 8.1
is proved directly from our deterministic hierarchy of embedded matchings
(`MinCostFlow.HierPaths.hierPathDSExistsFrom` and
`MinCostFlow.HierPaths.theorem_8_1_concrete_unconditional` in `MinCostFlow/HierPaths/BuildFinal.lean`).

The source (Sections 2 and 3.3):

> All graphs considered in this paper are undirected and simple, so they do not have parallel
> edges or self loops. […] We say that `G` is a `φ`-expander iff `Φ(G) ≥ φ`. Suppose we are given
> a graph `G` and a sub-graph `G' ⊆ G`. We say that `G'` is a strong `φ`-expander with respect to
> `G` iff for every partition `(S, S̄)` of `V(G')` into non-empty subsets,
> `δ_{G'}(S)/min{vol_G(S), vol_G(S̄)} ≥ φ`.
>
> […] `φ = 1/(c·γ)`, where `c` is a large enough constant. […] Throughout, we use an additional
> parameter `γ(n) = exp(O(log^{3/4} n))`.
>
> **Theorem 3.9.** There is a deterministic algorithm that, given an `m`-edge `n`-vertex
> `φ`-expander `G` undergoing a sequence at most `φ|E(G)|/10` edge deletions, and a parameter
> `q > 1`, maintains an incremental vertex set `S ⊆ V(G)`, such that, if we denote by `G^{(0)}`
> the graph `G` before any edge deletions, then, for every `t > 0`, after `t` edges are deleted
> from `G`, `vol_{G^{(0)}}(S) ≤ O(t/φ)` holds and `G \ S` is a strong `φ/6`-expander with respect
> to `G^{(0)}`. The algorithm also supports the following query: given a pair of vertices
> `u, v ∈ V(G) \ S`, return a simple `u`-`v` path `P` in `G \ S` of length at most
> `(γ(m))^{O(q)}`, with query time `(γ(m))^{O(q)}`. The total update time of the algorithm is
> `O(m^{1+1/q}(γ(n))^{O(q)})`.

The proof of the theorem fixes `φ = 1/(c·γ(m))` ("Throughout the algorithm, `m` denotes the number
of edges in the original `φ`-expander graph `G`, and the parameter `φ = 1/(cγ(m))` remains
unchanged").

How the statement reads it, as a data structure (`WordRAM/DataStructure.lean`):

* The abstract state (`PrunedExpander`) is the graph `G^{(0)}`, the parameter `q`, the numbers of
  the deleted edges in order, and the set `S`.
* The initialization takes `[a, q, h]`, with `G^{(0)}` written at address `a` as `Graph.encode`.
  It may be called when `G^{(0)}` is simple, has an edge and no isolated vertex, is a `φ`-expander
  for `φ = 1/(c·γ(m))`, `q ≥ 2` is an integer, and words have at least `c_w·log(n+m+2)` bits. An
  expander in the source's quotient form has no isolated vertex once it has an edge (the cut of
  an isolated vertex is `0/0`); asking for no isolated vertex keeps `n ≤ 2m`.
* Operation `0` deletes edge number `e`, with arguments `[handle, e, h]`, as long as at most
  `φ·m/10` edges are deleted in all. The new set `S'` contains `S`, satisfies the two conditions
  of the theorem, and the call writes the vertices of `S' \ S` at `h` as a length-prefixed list:
  this is how the incremental set is maintained for the user.
* Operation `1` is the query, with arguments `[handle, u, v, h]` for `u, v ∉ S`. It writes a
  simple `u`-`v` path in `G \ S` at `h` as a length-prefixed list of vertices, with at most
  `γ(m)^{K q}` edges, and does not change the state.
* "The total update time is `O(m^{1+1/q}γ(n)^{O(q)})`": the initialization's amortized bound is
  `K·(m^{1+1/q}·γ(n)^{K q} + 1)` and each deletion's is `K`, so all updates together cost at most
  the former plus `K` per deletion. Queries have the amortized bound `K·(γ(m)^{K q} + 1)`, which is
  weaker than the source's worst-case query time. Space: each call uses at most as many new cells
  as the total update bound, or the query bound for a query.
* `γ(x) = 2^{K_γ·(⌊(log₂ x + 1)^{3/4}⌋ + 1)}` with an integer `K_γ > 0`, which is
  `exp(Θ(log^{3/4} x))`. The source fixes `γ` only up to the constant in its exponent. An integer
  `γ` makes `φ = 1/(c·γ(m))` a rational number that a program can compute exactly; the algorithm
  uses `φ` in its thresholds.
* "Where `c` is a large enough constant": the statement holds for every integer `c ≥ c₀`, for some
  `c₀ > 0`, with the other constants allowed to depend on `c`.
* The `O` constants are a common `K`. The `+ 1` terms keep the bounds positive for small graphs.
  Every call may assume that words have at least `c_w·log(n+m+2)` bits.
* "A deterministic algorithm": every call ends as specified for every sequence of random bits.
-/

@[expose] public section

namespace MinCostFlow.Cited

open WordRAM

/-- The graph written at address `a` of `mem` in the form of `Graph.encode`. -/
def readGraph (mem : ℕ → ℕ) (a : ℕ) : Graph :=
  ⟨mem a, (List.range (mem (a + 1))).map fun j => (mem (a + 2 + 2 * j), mem (a + 3 + 2 * j))⟩

/-- The state of the data structure of [CS21] Theorem 3.9: the graph `G^{(0)}`, the parameter
`q`, the numbers of the deleted edges in order, and the maintained set `S`. -/
structure PrunedExpander where
  /-- The graph before any edge deletion, `G^{(0)}`. -/
  G : Graph
  /-- The parameter `q`. -/
  q : ℕ
  /-- The numbers of the deleted edges, in the order of deletion. -/
  deleted : List ℕ
  /-- The maintained set `S`. -/
  S : Finset ℕ

namespace PrunedExpander

/-- The edges not deleted yet. -/
def currentEdges (s : PrunedExpander) : List (ℕ × ℕ) :=
  ((List.range s.G.m).filter fun j => j ∉ s.deleted).map fun j => s.G.edges.getD j (0, 0)

/-- The current graph `G`, after the deletions. -/
def current (s : PrunedExpander) : Graph :=
  ⟨s.G.n, s.currentEdges⟩

/-- The vertices of `G \ S`. -/
def outside (s : PrunedExpander) : Finset ℕ :=
  s.G.verts \ s.S

/-- `G \ S` is a strong `ψ`-expander with respect to `G^{(0)}`: for every partition `(A, B)` of
`V(G) \ S` into nonempty sets, `ψ·min(vol_{G^{(0)}}(A), vol_{G^{(0)}}(B)) ≤ δ_{G \ S}(A)`. -/
def IsStrongExpander (s : PrunedExpander) (ψ : ℝ) : Prop :=
  ∀ A ⊆ s.outside, A.Nonempty → A ≠ s.outside →
    ψ * min (s.G.vol A : ℝ) (s.G.vol (s.outside \ A)) ≤ s.current.cutIn s.outside A

/-- The guarantees of Theorem 3.9 after `t` deletions, for the constant `K` of `O(t/φ)`:
`S` is a set of vertices, `vol_{G^{(0)}}(S) ≤ K·t/φ`, and `G \ S` is a strong `φ/6`-expander
with respect to `G^{(0)}`. -/
def Good (K φ : ℝ) (s : PrunedExpander) : Prop :=
  s.S ⊆ s.G.verts ∧ (s.G.vol s.S : ℝ) ≤ K * s.deleted.length / φ ∧ s.IsStrongExpander (φ / 6)

end PrunedExpander

/-- `γ(x) = 2^{K_γ·(⌊(log₂ x + 1)^{3/4}⌋ + 1)}`, which is `exp(Θ(log^{3/4} x))`. -/
def csGamma (Kγ x : ℕ) : ℕ :=
  2 ^ (Kγ * (Nat.sqrt (Nat.sqrt ((Nat.log 2 x + 1) ^ 3)) + 1))

/-- `φ = 1/(c·γ(m))`. -/
noncomputable def csPhi (Kγ c m : ℕ) : ℝ :=
  1 / ((c : ℝ) * csGamma Kγ m)

/-- The total update bound `K·(m^{1+1/q}·γ(n)^{K q} + 1)` of a graph with `n` vertices and `m`
edges. -/
noncomputable def csTotal (Kγ : ℕ) (K : ℝ) (n m q : ℕ) : ℕ :=
  ⌈K * ((m : ℝ) ^ (1 + 1 / (q : ℝ)) * (csGamma Kγ n : ℝ) ^ (K * q) + 1)⌉₊

/-- The query bound `K·(γ(m)^{K q} + 1)`. -/
noncomputable def csQuery (Kγ : ℕ) (K : ℝ) (m q : ℕ) : ℕ :=
  ⌈K * ((csGamma Kγ m : ℝ) ^ (K * q) + 1)⌉₊

/-- The specification of the data structure of [CS21] Theorem 3.9 at word size `w`, for the
constants `K_γ` (of `γ`), `c` (of `φ = 1/(c·γ(m))`), `K` (of the `O`s) and `c_w` (of the word
size). The initialization reads `G^{(0)}` from address `args[0]` and `q` from `args[1]`;
operation `0` deletes an edge and operation `1` answers a path query. -/
noncomputable def prunedExpanderDS (Kγ c : ℕ) (K : ℝ) (cw w : ℕ) :
    DataStructure PrunedExpander where
  initPre args mem :=
    let G := readGraph mem (args.getD 0 0)
    let q := args.getD 1 0
    args.length = 3 ∧ G.IsValid ∧ G.IsSimple ∧ 1 ≤ G.m ∧ (∀ v < G.n, 1 ≤ G.deg v) ∧
      G.IsConductanceExpanderOn G.verts (csPhi Kγ c G.m) ∧ 2 ≤ q ∧
      cw * (Nat.log 2 (G.n + G.m + 2) + 1) ≤ w
  initPost args mem s _ :=
    s.G = readGraph mem (args.getD 0 0) ∧ s.q = args.getD 1 0 ∧ s.deleted = [] ∧
      PrunedExpander.Good K (csPhi Kγ c s.G.m) s
  initCost args mem :=
    let G := readGraph mem (args.getD 0 0)
    csTotal Kγ K G.n G.m (args.getD 1 0)
  initSpace args mem :=
    let G := readGraph mem (args.getD 0 0)
    csTotal Kγ K G.n G.m (args.getD 1 0)
  pre i s args _ :=
    match i with
    | 0 =>
      let e := args.getD 1 0
      args.length = 3 ∧ cw * (Nat.log 2 (s.G.n + s.G.m + 2) + 1) ≤ w ∧ e < s.G.m ∧
        e ∉ s.deleted ∧ ((s.deleted.length + 1 : ℕ) : ℝ) ≤ csPhi Kγ c s.G.m * s.G.m / 10
    | 1 =>
      let u := args.getD 1 0
      let v := args.getD 2 0
      args.length = 4 ∧ cw * (Nat.log 2 (s.G.n + s.G.m + 2) + 1) ≤ w ∧ u < s.G.n ∧ v < s.G.n ∧
        u ∉ s.S ∧ v ∉ s.S
    | _ => False
  post i s args _ s' mem' :=
    match i with
    | 0 =>
      s'.G = s.G ∧ s'.q = s.q ∧ s'.deleted = s.deleted ++ [args.getD 1 0] ∧ s.S ⊆ s'.S ∧
        PrunedExpander.Good K (csPhi Kγ c s.G.m) s' ∧
        ∃ L, SeqAt mem' (heapArg args) L ∧ L.Nodup ∧ L.toFinset = s'.S \ s.S
    | 1 =>
      s' = s ∧ ∃ P, SeqAt mem' (heapArg args) P ∧ P.Nodup ∧ (∀ x ∈ P, x ∉ s.S) ∧
        IsPathAlong s.currentEdges (args.getD 1 0) (args.getD 2 0) P ∧
        ((P.length : ℝ) - 1 ≤ (csGamma Kγ s.G.m : ℝ) ^ (K * s.q))
    | _ => False
  cost i s _ _ :=
    match i with
    | 0 => ⌈K⌉₊
    | _ => csQuery Kγ K s.G.m s.q
  space i s _ _ :=
    match i with
    | 0 => csTotal Kγ K s.G.n s.G.m s.q
    | _ => csQuery Kγ K s.G.m s.q

/-- **[CS21], Theorem 3.9** (arXiv:2009.08479v1, page 17): there are integers `K_γ > 0` and
`c₀ > 0` such that for every integer `c ≥ c₀` there are constants `K` and `c_w`, procedure bodies
`mk b` (written for the base index `b`) and a representation `R` such that, in every program that
has the bodies `mk b` at indices `b, b+1, …`, procedure `b` (the initialization) and procedures
`b + 1` (deletion) and `b + 2` (query) implement `prunedExpanderDS` with `R`, at every word size
`w`. -/
def DecrementalExpanderPaths : Prop :=
  ∃ (Kγ c₀ : ℕ), 0 < Kγ ∧ 0 < c₀ ∧ ∀ c : ℕ, c₀ ≤ c →
    ∃ (K : ℝ) (cw : ℕ) (mk : ℕ → List Stmt) (R : DSRep PrunedExpander),
      ∀ (w b : ℕ) (p : Program), p.HasAt b (mk b) →
        R.Implements w p b (fun i => b + 1 + i) (prunedExpanderDS Kγ c K cw w)

end MinCostFlow.Cited
