module

public import MinCostFlow.Chain.Ordered.Algorithm1
public import MinCostFlow.Chain.Algorithm1BudgetHelpers

/-!
# Budgets and chain actions of Algorithm 1 with orders

The repaired Lemma 5.17 charges the time of a level `Õ(m k² γ_r)` instead of `Õ(m k γ_r)`: its
cumulative cost carries a factor `k + 1` (`SparseCoreRestartTool.IsSpecOrdRestart`). The recourse
does not change. So the running time of Lemma 5.11 gains the factor `k`, and its bound
`k · m^{1/d} Õ(γ_ℓ γ_r)^{O(d)} (m + Σ_i (s_i + r_i) m^{1-i/d})` is
`m^{2/d} Õ(γ_ℓ γ_r)^{O(d)} (⋯)` for `k ≈ m^{1/d}`.

This file multiplies the runtime budgets of `Chain/Algorithm1BudgetHelpers.lean` by `k + 1`
(`opRuntimeBudget`, `activeRestartCap`, `ChainBudgetInv`, `ChainBudgetInvWith`). The tree-update
budgets do not change. `lemma511TimeFactor` is the factor of the runtime bound of Lemma 5.11 with
`M₀^{2/d}` in place of `M₀^{1/d}`: since `k ≤ 2 M₀^{1/d}` and `1 ≤ M₀^{1/d}`, the factor `k + 1`
is at most `3 M₀^{1/d}`.

It also defines the chain actions and their validity, as in `Chain/Lemma5_11.lean`. An update of
level `0` must consist of edge insertions and deletions: level `0` gets its ends sorted by edge
name, which is ordered with split bound `0` exactly for such updates.
The updates of the IPM are of this kind (paper Definition 4.6, page 15).
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section BudgetDefinitions

/-- Runtime budget retired by one invocation of `Rebuild(i₀)` or `Shift(i₀)`: the budget of
`Chain/Algorithm1BudgetHelpers.lean` times `k + 1`. -/
noncomputable def opRuntimeBudget (TP : SparseCoreParams) (LP : LastLevelParams)
    (P : ChainParams) (n i₀ : ℕ) : ℝ :=
  ((P.k : ℝ) + 1) * Chain.opRuntimeBudget TP LP P n i₀

/-- Cumulative active restart runtime allowance across levels `< P.d`, times `k + 1`. -/
noncomputable def activeRestartCap (TP : SparseCoreParams) (P : ChainParams) (n : ℕ)
    (curRestarts : ℕ → ℕ) : ℝ :=
  ((P.k : ℝ) + 1) * Chain.activeRestartCap TP P n curRestarts

/-- Amortized budget invariant maintained alongside `ChainInv`, with the runtime budgets of this
file. -/
def ChainBudgetInv {T : SparseCoreRestartTool} {P : ChainParams}
    (TP : SparseCoreParams) (LP : LastLevelParams) (N₀ : ℕ) (st : ChainState T P) : Prop :=
  (st.closedRuntime : ℝ) + activeRestartCap TP P N₀ st.curRestarts ≤
    ∑ i ∈ Finset.range (P.d + 1),
      ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) *
        opRuntimeBudget TP LP P N₀ i ∧
  (st.closedTreeUpdates : ℝ) ≤
    diffTreeCap TP P 0 +
    ∑ i ∈ Finset.range (P.d + 1),
      ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) *
        opTreeBudget TP P i

/-- Amortized budget invariant with an explicit extra runtime allowance `overflow` (for external
batches of length exceeding `P.M₀`). -/
def ChainBudgetInvWith {T : SparseCoreRestartTool} {P : ChainParams}
    (TP : SparseCoreParams) (LP : LastLevelParams) (N₀ : ℕ) (st : ChainState T P)
    (overflow : ℝ) : Prop :=
  (st.closedRuntime : ℝ) + activeRestartCap TP P N₀ st.curRestarts ≤
    ∑ i ∈ Finset.range (P.d + 1),
      ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) *
        opRuntimeBudget TP LP P N₀ i + overflow ∧
  (st.closedTreeUpdates : ℝ) ≤
    diffTreeCap TP P 0 +
    ∑ i ∈ Finset.range (P.d + 1),
      ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) *
        opTreeBudget TP P i

lemma ChainBudgetInv.toWith {T : SparseCoreRestartTool} {P : ChainParams}
    {TP : SparseCoreParams} {LP : LastLevelParams} {N₀ : ℕ} {st : ChainState T P}
    (hB : ChainBudgetInv TP LP N₀ st) : ChainBudgetInvWith TP LP N₀ st 0 :=
  ⟨by simpa using hB.1, hB.2⟩

lemma ChainBudgetInvWith.toZero {T : SparseCoreRestartTool} {P : ChainParams}
    {TP : SparseCoreParams} {LP : LastLevelParams} {N₀ : ℕ} {st : ChainState T P}
    (hB : ChainBudgetInvWith TP LP N₀ st 0) : ChainBudgetInv TP LP N₀ st :=
  ⟨by simpa using hB.1, hB.2⟩

/-- The factor of the runtime bound of Lemma 5.11 for the chain with orders: the factor of
`Chain.lemma_5_11` times `3`, with `M₀^{2/d}` in place of `M₀^{1/d}`. -/
noncomputable def lemma511TimeFactor (TP : SparseCoreParams) (LP : LastLevelParams)
    (P : ChainParams) (N₀ : ℕ) : ℝ :=
  3 * ((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) *
    (P.M₀ : ℝ) ^ (2 / (P.d : ℝ)) *
    (TP.γ_r (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ (3 * P.d + 2)) *
    (2 * logFactor P N₀) ^ (max TP.p_T LP.p_last + 1)

end BudgetDefinitions

section ChainActions

/-- Valid external operations on Algorithm 1 with orders (Lemma 5.11, page 20; `Rebuild` is only
invoked internally through `Update`). -/
inductive ChainAction where
  | update (U : List Update) (g' ℓ' : ℕ → ℝ)
  | shift (i₀ : ℕ)

/-- Sequential execution of `ChainAction`s starting from `st`, returning the final state and the
list of `TreeChange` batches emitted at each step for updating `T^𝒢`. -/
noncomputable def execChainActions (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) :
    ChainState T P → List ChainAction → ChainState T P × List (List TreeChange)
  | st, [] => (st, [])
  | st, act :: rest =>
    let (st1, ch) := match act with
      | .update U g' ℓ' => algorithm1_update T L TP P N₀ st U g' ℓ'
      | .shift i₀ => algorithm1_shift T L P st i₀
    let (st2, chs) := execChainActions T L TP P N₀ st1 rest
    (st2, ch :: chs)

/-- Validity of a sequence of `ChainAction`s relative to the current top-level graph and lengths
`(G₀, ℓ)`, as in `Chain.ChainActionListValid`, where every update is an edge insertion or deletion
(`Bundle.IsEdgeUpdate`) and the new lengths lie in `[e^{-Λ}, e^Λ]` (`LenInRange`), as the
lengths of a hidden stable instance do (Definition 4.4, item 5, page 14). The number `c` is the
count `updCount 0` of updates since the last rebuild of level `0`. An update that passes the
threshold of level `0` rebuilds it and renames its edges to `0, …, |E| - 1` (`Ordered.updateLoop`),
so the later actions refer to the renamed graph. -/
def ChainActionListValid (P : ChainParams) (N₀ : ℕ) (Λ : ℝ) :
    ℕ → MGraph → (ℕ → ℝ) → List ChainAction → Prop
  | _, _, _, [] => True
  | c, G₀, ℓ, .update U _ ℓ' :: rest =>
    G₀.BatchIsValid U ∧
    NoBatchReinsert G₀ U ∧
    (∀ u ∈ U, IsEdgeUpdate u) ∧
    (G₀.applyBatch U).IsValid ∧
    (G₀.applyBatch U).m ≤ P.M₀ ∧
    (G₀.applyBatch U).n ≤ N₀ ∧
    U.length ≤ P.M₀ ∧
    LenInRange Λ (G₀.applyBatch U) ℓ' ∧
    (∀ e ∈ (G₀.applyBatch U).E, e ∈ G₀.E → (∀ u ∈ U, ¬ u.Inserts e) → ℓ' e = ℓ e) ∧
    ChainActionListValid P N₀ Λ
      (if intRebuildThreshold P N₀ 0 < c + U.length then 0 else c + U.length)
      (if intRebuildThreshold P N₀ 0 < c + U.length then (G₀.applyBatch U).compact
        else G₀.applyBatch U)
      (if intRebuildThreshold P N₀ 0 < c + U.length then
        fun j => ℓ' (compactUnrank (G₀.applyBatch U).E j) else ℓ')
      rest
  | c, G₀, ℓ, .shift i₀ :: rest =>
    i₀ ≤ P.d ∧ ChainActionListValid P N₀ Λ c G₀ ℓ rest

end ChainActions

end MinCostFlow.Chain.Ordered
