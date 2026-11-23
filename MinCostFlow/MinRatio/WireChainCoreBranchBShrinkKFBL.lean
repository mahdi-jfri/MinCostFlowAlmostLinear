module

public import MinCostFlow.MinRatio.WireSelectSplitPotModel
public import MinCostFlow.Chain.Ordered.ShiftLoopLevels

/-!
# The forests of the finished levels only shrink (`WireChainCoreBranchBShrinkKFBL`)

Sync 2a of Branch B cuts from the path tree the edges that leave the forest of each finished
level (`branchBSplit`). This removes all old edges that the level drops only when the new forest
of the level lies in the old one. The record of the change (`LSFChange.Exact`) gives only the
difference, and an abstract tool need not keep its forests inside the old ones. So `hB` takes
this as a fact on the tool, `BranchBForestShrinkKFBL`, in the same way as the tool step fact.

The tool of the program (`sparseCoreProgTool`) meets it: its forests only shrink on a batch
(`progTool_nonRebuilt_forest_subset`). `chainForestShrink_progTool` gives this.
-/

public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered
open MinCostFlow.SparseCore MinCostFlow.LSF MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- **Tool fact.** For a chain `st` that meets `ChainInv` and a chain `st'` that the levels
`0, …, i` reach from it on the batches `U` without a rebuild (`NonRebuiltBatches`), the forest
of each level `j ≤ i` of `st'` lies in that of `st`. -/
@[expose] def ChainForestShrink (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ) : Prop :=
  ∀ (st st' : ChainState T P) (U : ℕ → List Update) (i : ℕ),
    Ordered.ChainInv T L TP LP P N₀ st → NonRebuiltBatches T st st' U i →
    ∀ j ≤ i, (st'.toTreeChain.activeLSF j).F.F.E ⊆ (st.toTreeChain.activeLSF j).F.F.E

/-- The tool fact `ChainForestShrink` at the tools of a configuration. -/
@[expose] def BranchBForestShrinkKFBL (cfg : Alg2Config) : Prop :=
  ChainForestShrink cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀

/-- The tool of the program meets `ChainForestShrink` when its LSF init is valid for every
branch (`progTool_nonRebuilt_forest_subset`). -/
theorem chainForestShrink_progTool {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ} (hInit : ∀ b < P.k, IsValidLSFInitFor lsfInit C_lsst P.k b) :
    ChainForestShrink (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ :=
  fun _ _ _ _ hInv hNR => progTool_nonRebuilt_forest_subset hInv hInit hNR

/-- `BranchBForestShrinkKFBL` for a configuration whose tool is the tool of the program. -/
theorem branchBForestShrink_of_progTool {cfg : Alg2Config} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth : ℕ} {impl : SparsifyImpl}
    (hT : cfg.T = sparseCoreProgTool lsfInit C_lsst depth impl)
    (hInit : ∀ b < cfg.P.k, IsValidLSFInitFor lsfInit C_lsst cfg.P.k b) :
    BranchBForestShrinkKFBL cfg := by
  unfold BranchBForestShrinkKFBL
  rw [hT]
  exact chainForestShrink_progTool hInit

end MinCostFlow.MinRatio
