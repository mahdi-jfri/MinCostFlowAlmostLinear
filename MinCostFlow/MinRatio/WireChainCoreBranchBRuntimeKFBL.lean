module

public import MinCostFlow.MinRatio.WireChainCoreAlgebra
import WordRAM.Tactic

/-!
# The runtime of the model after the update loop of Branch B (`WireChainCoreBranchBRuntimeKFBL`)

The cost bound `costTotalBranchB` pays the plain steps and the rebuilds of Branch B from the
growth of `totalRuntime` of the chain. The loop of Branch B (`wireBranchBLoopKFBL_runs`) ends at a
level `i₀` with a chain `chE`, and the model after the update is the rest of
`Chain.Ordered.updateLoop` from `chE` at `i₀`. This file bounds the growth of `totalRuntime` over
that rest:
* `branchBRuntime_int`: when the test fires at `i₀ < d`, the rest is a rebuild from `i₀`, which
  adds the tool costs of the rebuilt levels and the cost of the last level
  (`rebuild_totalRuntime_sub`), and keeps the levels below `i₀`;
* `branchBRuntime_term`: at `i₀ = d`, the rest adds the cost of the last level when the batch
  that reaches it is not empty, and keeps the levels below `d`.

The growth over the plain steps is the last part of the post of `wireBranchBLoopKFBL_runs`.
-/

public section

namespace MinCostFlow.MinRatio

open Chain Chain.Ordered

/-- When the test fires at `i₀ < d`, the rest of the update loop from `chE` adds at least the tool
costs of the levels `i₀ ≤ j < d` and the cost of the last level to `totalRuntime`, and keeps the
graphs and the tool states of the levels below `i₀`. -/
theorem branchBRuntime_int (T : SparseCoreRestartTool) (L : LastLevelTool) (TP : SparseCoreParams)
    (P : ChainParams) (N0 : ℕ) (ℓ' g' : ℕ → ℝ) {i₀ : ℕ} (hi : i₀ < P.d)
    (chE : ChainState T P) (curGE : MGraph) (curUE : List Update) (curEncE : ℕ)
    (hFire : intRebuildThreshold P N0 i₀ < chE.updCount i₀ + curUE.length) :
    let X := (Chain.Ordered.updateLoop T L TP P N0 ℓ' g' (P.d - i₀) i₀ chE curGE curUE curEncE).1
    chE.totalRuntime + (Finset.Ico i₀ P.d).sum (fun j => T.cost (X.scState j)) +
        L.cost (X.G P.d) ≤ X.totalRuntime ∧
      ∀ m < i₀, X.scState m = chE.scState m ∧ X.G m = chE.G m := by
  intro X
  obtain ⟨rem, hrem⟩ : ∃ rem, P.d - i₀ = rem + 1 := ⟨P.d - i₀ - 1, by omega⟩
  set stLG : ChainState T P :=
    { chE with ℓ := rebuildStartFn i₀ curGE ℓ', g := rebuildStartFn i₀ curGE g' }
  have hX : X = (Chain.Ordered.algorithm1_rebuild T L P stLG i₀ (rebuildStartGraph i₀ curGE) curEncE).1 := by
    simp only [X, hrem, Chain.Ordered.updateLoop, hFire, ↓reduceIte]
    rfl
  have hRt : stLG.totalRuntime = chE.totalRuntime := rfl
  have hSub := rebuild_totalRuntime_sub T L P stLG hi (rebuildStartGraph i₀ curGE) curEncE
  have hLe := algorithm1_rebuild_totalRuntime_le T L P stLG hi (rebuildStartGraph i₀ curGE) curEncE
  have hEx := ordAlgorithm1_rebuild_exact T L P stLG hi (rebuildStartGraph i₀ curGE) curEncE
  dsimp only at hSub hEx
  rw [← hX] at hSub hLe hEx
  rw [hRt] at hSub hLe
  refine ⟨by omega, fun m hm => ⟨(hEx.1 m hm).2.1, (hEx.1 m hm).1⟩⟩

/-- At `i₀ = d`, the rest of the update loop from `chE` adds the cost of the last level to
`totalRuntime` when the batch that reaches it is not empty, and keeps the tool states of the
levels below `d`. The graph of the last level is then the graph `curGE`. -/
theorem branchBRuntime_term (T : SparseCoreRestartTool) (L : LastLevelTool) (TP : SparseCoreParams)
    (P : ChainParams) (N0 : ℕ) (ℓ' g' : ℕ → ℝ)
    (chE : ChainState T P) (curGE : MGraph) (curUE : List Update) (curEncE : ℕ) :
    let X := (Chain.Ordered.updateLoop T L TP P N0 ℓ' g' 0 P.d chE curGE curUE curEncE).1
    chE.totalRuntime + (if curUE = [] then 0 else L.cost (X.G P.d)) ≤ X.totalRuntime ∧
      X.G P.d = curGE ∧ ∀ m < P.d, X.scState m = chE.scState m := by
  intro X
  by_cases hU : curUE = []
  · have hX : X = { chE with G := fun j => if j = P.d then curGE else chE.G j, ℓ := ℓ', g := g' } :=
      by simp only [X, Chain.Ordered.updateLoop, hU, ↓reduceIte]
    rw [if_pos hU, hX]
    exact ⟨le_of_eq (by simp [ChainState.totalRuntime]), by simp, fun _ _ => rfl⟩
  · rw [if_neg hU]
    have hG : X.G P.d = curGE := by simp only [X, Chain.Ordered.updateLoop, hU, ↓reduceIte]
    have hSc : ∀ m < P.d, X.scState m = chE.scState m := fun m _ => by
      simp only [X, Chain.Ordered.updateLoop, hU, ↓reduceIte]
    have hRt : X.totalRuntime = chE.totalRuntime + L.cost curGE := by
      simp only [X, Chain.Ordered.updateLoop, hU, ↓reduceIte, ChainState.totalRuntime]
      omega
    rw [hG, hRt]
    exact ⟨le_rfl, rfl, hSc⟩

/-- The runtime premise of case 1 of `costTotalBranchB`: the loop raised `totalRuntime` from `ch0`
to `chE` by the changes of tool cost of the plain levels (`hLoop`, from the post of
`wireBranchBLoopKFBL_runs`), and the test fired at `i₀ < d`. Then the changes of tool cost below
`i₀`, the tool costs of the rebuilt levels and the cost of the last level are at most the growth
of `totalRuntime` from `ch0` to the model `X` after the update. -/
theorem branchBRuntime_case_int (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N0 : ℕ) (ℓ' g' : ℕ → ℝ) {i₀ : ℕ} (hi : i₀ < P.d)
    (ch0 chE : ChainState T P) (curGE : MGraph) (curUE : List Update) (curEncE : ℕ)
    (hFire : intRebuildThreshold P N0 i₀ < chE.updCount i₀ + curUE.length)
    (hLoop : ch0.totalRuntime + (Finset.Ico 0 i₀).sum
      (fun j => T.cost (chE.scState j) - T.cost (ch0.scState j)) ≤ chE.totalRuntime) :
    let X := (Chain.Ordered.updateLoop T L TP P N0 ℓ' g' (P.d - i₀) i₀ chE curGE curUE curEncE).1
    (Finset.range i₀).sum (fun j => T.cost (X.scState j) - T.cost (ch0.scState j)) +
        (Finset.Ico i₀ P.d).sum (fun j => T.cost (X.scState j)) + L.cost (X.G P.d) ≤
      X.totalRuntime - ch0.totalRuntime := by
  intro X
  obtain ⟨hRt, hPre⟩ := branchBRuntime_int T L TP P N0 ℓ' g' hi chE curGE curUE curEncE hFire
  have hEq : (Finset.range i₀).sum (fun j => T.cost (X.scState j) - T.cost (ch0.scState j)) =
      (Finset.Ico 0 i₀).sum (fun j => T.cost (chE.scState j) - T.cost (ch0.scState j)) := by
    rw [Finset.range_eq_Ico]
    exact Finset.sum_congr rfl fun j hj => by rw [(hPre j (Finset.mem_Ico.mp hj).2).1]
  rw [hEq]
  dsimp only [X] at hRt ⊢
  omega

/-- The runtime premise of cases 2 and 3 of `costTotalBranchB`: the loop ran all `d` plain
levels from `ch0` to `chE` (`hLoop`). Then the changes of tool cost of the plain levels and the
cost of the last level (when its batch is not empty) are at most the growth of `totalRuntime`
from `ch0` to the model `X` after the update. -/
theorem branchBRuntime_case_term (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N0 : ℕ) (ℓ' g' : ℕ → ℝ)
    (ch0 chE : ChainState T P) (curGE : MGraph) (curUE : List Update) (curEncE : ℕ)
    (hLoop : ch0.totalRuntime + (Finset.Ico 0 P.d).sum
      (fun j => T.cost (chE.scState j) - T.cost (ch0.scState j)) ≤ chE.totalRuntime) :
    let X := (Chain.Ordered.updateLoop T L TP P N0 ℓ' g' 0 P.d chE curGE curUE curEncE).1
    (Finset.range P.d).sum (fun j => T.cost (X.scState j) - T.cost (ch0.scState j)) +
        (if curUE = [] then 0 else L.cost (X.G P.d)) ≤
      X.totalRuntime - ch0.totalRuntime := by
  intro X
  obtain ⟨hRt, _, hPre⟩ := branchBRuntime_term T L TP P N0 ℓ' g' chE curGE curUE curEncE
  have hEq : (Finset.range P.d).sum (fun j => T.cost (X.scState j) - T.cost (ch0.scState j)) =
      (Finset.Ico 0 P.d).sum (fun j => T.cost (chE.scState j) - T.cost (ch0.scState j)) := by
    rw [Finset.range_eq_Ico]
    exact Finset.sum_congr rfl fun j hj => by rw [hPre j (Finset.mem_Ico.mp hj).2]
  rw [hEq]
  dsimp only [X] at hRt ⊢
  omega

end MinCostFlow.MinRatio
