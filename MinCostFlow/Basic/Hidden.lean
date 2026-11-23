module

public import MinCostFlow.Basic.Dynamic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Valid pairs and hidden stability (Definitions 4.3 and 4.4)

Definition 4.3 (valid pair, page 14):

> For a graph `G = (V, E)` with lengths `ℓ ∈ ℝ^E_{>0}`, we say that `c, w ∈ ℝ^E` are a *valid
> pair* if `c` is a circulation and `|ℓ_e c_e| ≤ w_e` for all `e ∈ E`.

Definition 4.4 (hidden stable `α`-flow updates, page 14):

> We say that a dynamic min-ratio cycle instance described by a dynamic graph `G^{(t)}`, gradients
> `g^{(t)}`, and lengths `ℓ^{(t)}` satisfies the *hidden stable `α`-flow chasing* property if there
> are hidden dynamic circulations `c^{(t)}` and hidden dynamic upper bounds `w^{(t)}` such that the
> following holds at all stages `t`:
> 1. `c^{(t)}` is a circulation, i.e., `B_{G^{(t)}}ᵀ c^{(t)} = 0`.
> 2. `c^{(t)}` and `w^{(t)}` are a valid pair with respect to `G^{(t)}`.
> 3. `c^{(t)}` has sufficiently negative objective value relative to `w^{(t)}`, i.e.,
>    `⟨g^{(t)}, c^{(t)}⟩ / ‖w^{(t)}‖₁ ≤ -α`.
> 4. For any edge `e` in the current graph `G^{(t)}`, and any stage `t' ≤ t`, if the edge `e` was
>    not explicitly inserted after stage `t'`, then `w^{(t)}_e ≤ 2 w^{(t')}_e`. However, between
>    stage `t'` and `t`, endpoints of edge `e` might change due to vertex splits.
> 5. Each entry of `w^{(t)}` and `ℓ^{(t)}` is quasipolynomially lower and upper-bounded:
>    `log w^{(t)}_e ∈ [-log^{O(1)} m, log^{O(1)} m]` and
>    `log ℓ^{(t)}_e ∈ [-log^{O(1)} m, log^{O(1)} m]` for all `e ∈ E(G^{(t)})`.

How the definitions read it:

* A dynamic instance is the sequence of graphs `G^{(t)}`, of batches `U^{(t)}`, of gradients and
  of lengths, for the stages `t = 0, 1, …, T`; `G^{(t)}` is `G^{(t-1)}` after the batch `U^{(t)}`
  (`DynamicInstance.IsValid`). The conditions are asked at every stage `0 ≤ t ≤ T`.
* "Not explicitly inserted after stage `t'`": no batch `U^{(s)}` with `t' < s ≤ t` inserts `e`.
* The bound `log^{O(1)} m` of item 5 is a parameter `Ψ`: `|log w^{(t)}_e| ≤ Ψ` and
  `|log ℓ^{(t)}_e| ≤ Ψ`, with `w^{(t)}_e, ℓ^{(t)}_e > 0` (the logarithms are of positive numbers).
  The theorems that use this definition say how `Ψ` depends on `m`.
-/

@[expose] public section

namespace MinCostFlow

/-- `c, w` are a valid pair for `G` with lengths `ℓ` (Definition 4.3, page 14): `c` is a
circulation and `|ℓ_e c_e| ≤ w_e` for every edge. -/
def IsValidPair (G : MGraph) (ℓ c w : ℕ → ℝ) : Prop :=
  G.IsCirculation c ∧ ∀ e ∈ G.E, |ℓ e * c e| ≤ w e

/-- A dynamic min-ratio cycle instance (Section 4, page 14): graphs `G^{(t)}`, batches `U^{(t)}`
(`U^{(t)}` turns `G^{(t-1)}` into `G^{(t)}`), gradients `g^{(t)}` and lengths `ℓ^{(t)}`. -/
structure DynamicInstance where
  /-- The graph `G^{(t)}` at stage `t`. -/
  G : ℕ → MGraph
  /-- The batch `U^{(t)}` of stage `t ≥ 1`. -/
  U : ℕ → List Update
  /-- The gradients `g^{(t)}`. -/
  g : ℕ → ℕ → ℝ
  /-- The lengths `ℓ^{(t)}`. -/
  ℓ : ℕ → ℕ → ℝ

namespace DynamicInstance

variable (D : DynamicInstance)

/-- Up to stage `T`, each batch applies to the graph before it and gives the graph after it. -/
def IsValid (T : ℕ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ T →
    (D.G (t - 1)).BatchIsValid (D.U t) ∧ D.G t = (D.G (t - 1)).applyBatch (D.U t)

/-- No batch `U^{(s)}` with `t' < s ≤ t` inserts the edge `e`. -/
def NotInsertedBetween (e t' t : ℕ) : Prop :=
  ∀ s, t' < s → s ≤ t → ∀ u ∈ D.U s, ¬ u.Inserts e

/-- The five conditions of Definition 4.4 at stage `t`, for hidden circulations `c` and upper
bounds `w`. -/
def HiddenStableAt (α Ψ : ℝ) (c w : ℕ → ℕ → ℝ) (t : ℕ) : Prop :=
  (D.G t).IsCirculation (c t) ∧
  IsValidPair (D.G t) (D.ℓ t) (c t) (w t) ∧
  (D.G t).inner (D.g t) (c t) / (D.G t).norm1 (w t) ≤ -α ∧
  (∀ e ∈ (D.G t).E, ∀ t' ≤ t, D.NotInsertedBetween e t' t → w t e ≤ 2 * w t' e) ∧
  (∀ e ∈ (D.G t).E, 0 < w t e ∧ |Real.log (w t e)| ≤ Ψ ∧ 0 < D.ℓ t e ∧ |Real.log (D.ℓ t e)| ≤ Ψ)

/-- The instance has the hidden stable `α`-flow chasing property up to stage `T`, with the bound
`Ψ` of item 5 (Definition 4.4, page 14). -/
def HiddenStable (T : ℕ) (α Ψ : ℝ) : Prop :=
  ∃ c w : ℕ → ℕ → ℝ, ∀ t ≤ T, D.HiddenStableAt α Ψ c w t

end DynamicInstance

end MinCostFlow
