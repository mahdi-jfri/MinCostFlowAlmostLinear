module

public import WordRAM.Model
public import MinCostFlow.Statement.Cited.Graphs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit expanders and expander decomposition (Chuzhoy, Gao, Li, Nanongkai, Peng, Saranurak)

This file states Theorem 2.4 and Corollary 6.1 of

> J. Chuzhoy, Y. Gao, J. Li, D. Nanongkai, R. Peng, T. Saranurak, *A Deterministic Algorithm for
> Balanced Cut with Applications to Dynamic Connectivity, Flows, and Beyond*, FOCS 2020,
> arXiv:1910.08025v2.

The paper cites it as [CGLNPS21] for its Theorem 8.4 (page 40), Theorem 8.5 (page 41) and
Theorem B.1 (page 49). Theorem 8.5 points to "Corollary 6.2 in arXiv v2"; in arXiv v2, Corollary
6.2 is the dynamic minimum spanning forest, and the expander decomposition is Corollary 6.1.

The conventions of the source (Section 2):

> All graphs considered in this paper are unweighted and undirected, and they may have parallel
> edges but no self-loops. […] The conductance of a cut `S` is
> `Φ_G(S) = δ_G(S)/min{vol_G(S), vol_G(S̄)}`. […] The conductance of a graph `G` […] is the
> smallest conductance of any cut in `G`: `Φ(G) = min_{∅ ≠ S ⊊ V} Φ_G(S)`. The sparsity of a cut
> `S` is `Ψ_G(S) = δ_G(S)/min{|S|, |S̄|}`, and the expansion of a graph `G` is
> `Ψ(G) = min_{∅ ≠ S ⊊ V} Ψ_G(S)`. […] We say that a graph `G` is a `ψ`-expander iff
> `Ψ(G) ≥ ψ`.

> **Theorem 2.4.** There is a constant `α₀ > 0` and a deterministic algorithm, that we call
> ConstructExpander, that, given an integer `n > 1`, in time `O(n)` constructs a graph `H_n` with
> `|V(H_n)| = n`, such that `H_n` is an `α₀`-expander, and every vertex in `H_n` has degree at
> most `9`.

> An `(ε, φ)`-expander decomposition of a graph `G = (V, E)` is a partition
> `P = {V_1, …, V_k}` of the set `V` of vertices, such that for all `1 ≤ i ≤ k`, the conductance
> of graph `G[V_i]` is at least `φ`, and `∑_{i=1}^k δ_G(V_i) ≤ ε Vol(G)`.
>
> **Corollary 6.1.** There is a deterministic algorithm that, given a graph `G = (V, E)` with `m`
> edges, and parameters `ε ∈ (0, 1]` and `1 ≤ r ≤ O(log m)`, computes a `(ε, φ)`-expander
> decomposition of `G` with `φ = Ω(ε/(log m)^{O(r²)})`, in time
> `O(m^{1+O(1/r)} · (log m)^{O(r²)}/ε²)`.

How the statements read them:

* Graphs are loopless multigraphs (`Graph.IsLoopless`), as in the source.
* "A deterministic algorithm that […] in time `T`": a program that, for every sequence of random
  bits, halts with a correct answer within `T` steps. The statement asks nothing of the random
  bits.
* Theorem 2.4: the input is `[n]`; the output is `H_n` written as `Graph.encode`. The constant
  `α₀` must be positive, as in the source.
* Corollary 6.1: the input is the graph, then `a`, `b` and `r`, with `ε = a/b`, `1 ≤ a ≤ b` and
  `r ≥ 1` integers (the machine reads integers). The output gives each vertex the label of its
  part. "`r ≤ O(log m)`" is `r ≤ c_r · log m` for a constant `c_r > 0`.
* The `O` and `Ω` of Corollary 6.1 have constants `K > 0`, with `log(m+2)` and `m + 2` in place
  of `log m` and `m`; this only lowers the promised conductance and raises the time, and keeps
  both meaningful for small `m`. The time also has a term `K·n`: the output has a label for each
  of the `n` vertices, so no program meets a bound in `m` alone when `n` is much larger than `m`.
-/

@[expose] public section

namespace MinCostFlow.Cited

open WordRAM

/-- **[CGLNPS21], Theorem 2.4** (arXiv:1910.08025v2, page 15): there are a constant `α₀ > 0`, a
program `P`, a word size constant `c` and a constant `K` such that for every integer `n > 1`, for
every sequence of random bits, `P` halts on `[n]` within `K·n` steps with the encoding of a
loopless graph on `n` vertices of expansion at least `α₀` and maximum degree at most `9`.
It is proved as `MinCostFlow.ExplicitExpander.explicitExpander`. -/
def ExplicitExpander : Prop :=
  ∃ (α₀ : ℝ) (P : Program) (c : ℕ) (K : ℝ), 0 < α₀ ∧
    ∀ n : ℕ, 1 < n → ∀ ω, ∃ out cost, RunsTo (wordSize c [n]) P [n] ω out cost ∧
      (∃ H : Graph, out = H.encode ∧ H.n = n ∧ H.IsValid ∧ H.IsLoopless ∧
        H.IsExpansionExpanderOn H.verts α₀ ∧ ∀ v < n, H.deg v ≤ 9) ∧
      (cost : ℝ) ≤ K * n

/-- The parts of the partition given by the labels `label`: for each label `ℓ` of a vertex, the
set of vertices labelled `ℓ`. -/
def partsOf (G : Graph) (label : List ℕ) : Finset (Finset ℕ) :=
  G.verts.image fun v => G.verts.filter fun x => label.getD x 0 = label.getD v 0

/-- `label` gives an `(ε, φ)`-expander decomposition of `G`: it has a label for each vertex, the
graph `G[X]` of each part `X` has conductance at least `φ`, and `∑_X δ_G(X) ≤ ε·Vol(G)`. -/
def IsExpanderDecomposition (G : Graph) (ε φ : ℝ) (label : List ℕ) : Prop :=
  label.length = G.n ∧ (∀ X ∈ partsOf G label, G.IsConductanceExpanderOn X φ) ∧
    (∑ X ∈ partsOf G label, (G.cut X : ℝ)) ≤ ε * G.vol G.verts

/-- **[CGLNPS21], Corollary 6.1** (arXiv:1910.08025v2, page 43): there are constants `K > 0` and
`c_r > 0`, a program `P` and a word size constant `c` such that on every loopless graph `G` with
`m` edges, every `ε = a/b ∈ (0, 1]` and every integer `r` with `1 ≤ r ≤ c_r · log m`, for every
sequence of random bits, `P` halts with an `(ε, φ)`-expander decomposition of `G` for
`φ = ε/(K·log(m+2)^{K r²})`, within `K·(n + (m+2)^{1+K/r}·log(m+2)^{K r²}/ε²)` steps. The case
that the paper uses (`ε = 1/200` and a fixed `r` for each `m`,
`MinCostFlow.ExpanderDecomp.ExpanderDecompositionUsed`) is proved as
`MinCostFlow.ExpanderDecomp.expanderDecompositionUsed_holds`
(`MinCostFlow/ExpanderDecomp/UsedProved.lean`). -/
def ExpanderDecomposition : Prop :=
  ∃ (K cr : ℝ) (P : Program) (c : ℕ), 0 < K ∧ 0 < cr ∧
    ∀ (G : Graph) (a b r : ℕ), G.IsValid → G.IsLoopless → 1 ≤ a → a ≤ b → 1 ≤ r →
      (r : ℝ) ≤ cr * Real.log G.m → ∀ ω, ∃ out cost,
        RunsTo (wordSize c (G.encode ++ [a, b, r])) P (G.encode ++ [a, b, r]) ω out cost ∧
        IsExpanderDecomposition G (a / b)
          ((a / b) / (K * Real.log ((G.m : ℝ) + 2) ^ (K * (r : ℝ) ^ 2))) out ∧
        (cost : ℝ) ≤ K * (G.n + ((G.m : ℝ) + 2) ^ (1 + K / r) *
          Real.log ((G.m : ℝ) + 2) ^ (K * (r : ℝ) ^ 2) / ((a : ℝ) / b) ^ 2)

end MinCostFlow.Cited
