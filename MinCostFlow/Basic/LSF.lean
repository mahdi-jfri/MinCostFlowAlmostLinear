module

public import MinCostFlow.Basic.Forest

/-!
# Low-stretch forests (Lemma 5.4)

Lemma 5.4 (page 17) maintains a triple `(T, F, wstr)`:

> […] initializes a tree `T` spanning `V`, and a rooted spanning forest `F ⊆ T`, an edge-disjoint
> partition `𝒲` of `F` into `O(m/k)` sub trees and stretch overestimates `wstr_e`. […]
> 2. `str^{F,ℓ}_e ≤ wstr_e ≤ O(k log^6 n)` for all `e ∈ E` at all times, including inserted edges
>    `e`.
> […] We refer to the triple `(T, F, wstr)` as a Low-Stretch Forest (LSF) of `G`.

Definition 5.6 (core graph, page 18) uses such a triple: "Consider a tree `T` and a rooted spanning
forest `E(F) ⊆ E(T)` on a graph `G` equipped with stretch overestimates `wstr_e` satisfying the
guarantees of Lemma 5.4."

How the definitions read it:

* `LSF` is the triple. `LSF.Holds G ℓ σ` is the part of the guarantees of Lemma 5.4 that speaks of
  one moment: `T` is a forest (a tree when it is built; Section 5.3 notes that `T` stays fixed
  while `G` changes, so later it need not span `G`, and Appendix A.1 adds new isolated vertices to
  it), `F` is a rooted spanning forest of `G` and a subgraph of `T`, and item 2 with the bound
  `σ` for `O(k log^6 n)`.
* The other items of Lemma 5.4 speak of a sequence of updates. The files in `MinCostFlow/LSF/`
  state them (`MinCostFlow/LSF/Lemma54.lean`).
-/

@[expose] public section

namespace MinCostFlow

/-- A low-stretch forest `(T, F, wstr)` (Lemma 5.4, page 17): a tree `T`, a rooted forest
`F ⊆ T`, and stretch overestimates `wstr`. -/
structure LSF where
  /-- The tree `T`. -/
  T : MGraph
  /-- The rooted spanning forest `F ⊆ T`. -/
  F : RootedForest
  /-- The stretch overestimates `wstr_e`. -/
  wstr : ℕ → ℝ

namespace LSF

/-- The guarantees of Lemma 5.4 at one moment, for the graph `G` with lengths `ℓ`: `T` is a forest,
`F` is a rooted spanning forest of `G` contained in `T`, and `str^{F,ℓ}_e ≤ wstr_e ≤ σ` for every
edge `e` of `G` (item 2, with `σ` for `O(k log^6 n)`). -/
def Holds (L : LSF) (G : MGraph) (ℓ : ℕ → ℝ) (σ : ℝ) : Prop :=
  L.T.IsForest ∧ L.F.IsRootedSpanningForestOf G ∧ L.T.IsSubgraph L.F.F ∧
    ∀ e ∈ G.E, L.F.stretch G ℓ e ≤ L.wstr e ∧ L.wstr e ≤ σ

end LSF

end MinCostFlow
