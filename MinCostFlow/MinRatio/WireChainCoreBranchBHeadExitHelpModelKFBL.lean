module

public import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitBaseKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBModelKFBL

/-!
# The model after the exit of the loop of Branch B (`WireChainCoreBranchBHeadExitHelpModelKFBL`)

The model after the update is the chain of `alg2PreResetState`, that is the update loop of
Algorithm 1 (page 21) from level `0` on the internal batch `Uint`. A run up to the exit of the
loop (`BranchBRunPreExitKFBL`) has done the plain steps of the levels below `i₀`, and its loop
facts say that the update loop from level `0` ends where the update loop from level `i₀` ends.
This file gives the model equation `X = (alg2PreResetState …).chain` of the exit goals in the
form that each exit needs.

* `modelEq_loop`: the chain of `alg2PreResetState` is the update loop from `i₀` at the state of
  the exit.
* `modelEq_int`: at the interior exit (`i₀ < d`) it is the rebuild from `i₀`
  (`branchBUpdateLoop_int`, with the test of the loop that fires at `i₀`).
* `modelEq_term`: at the terminal exits (`i₀ = d`) it is the update loop at `rem = 0`
  (`branchBUpdateLoop_term`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

namespace BranchBRunPreExitKFBL

variable {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
      canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
      collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {stepCap : ℕ → ℕ → ℕ}
    {root uIntBuf editsPtr editWords g l heap pos : ℕ} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}

variable (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)

/-- The chain of `alg2PreResetState` is the update loop of Algorithm 1 from level `i₀` at the
state of the exit. Algorithm 1 runs the update loop from level `0` at `st0` on `G1` and `Uint`
(the definitions of `alg2PreResetState` and `algorithm1_update`), and the loop facts of `H.loop`
say that this loop ends where the loop from `i₀` ends. -/
theorem modelEq_loop :
    (alg2PreResetState cfg model U H.gVec H.lVec).chain =
      (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g' (cfg.P.d - H.i₀) H.i₀
        H.chE H.curGE H.curUE H.curEncE).1 := by
  rw [← H.loop.2.2.2.2.2.2.2.1, H.st0_eq, H.G1_eq, H.Uint_eq, H.ℓ'_eq, H.g'_eq]
  rfl

/-- At the interior exit (`i₀ < d`), the chain of `alg2PreResetState` is the rebuild from `i₀`
(Algorithm 1, page 21): the test of the loop fires at `i₀` (the loop facts), so
`branchBUpdateLoop_int` applies, with `0 < i₀` from `i₀_pos`. -/
theorem modelEq_int (hi : H.i₀ < cfg.P.d) :
    (alg2PreResetState cfg model U H.gVec H.lVec).chain =
      (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P { H.chE with ℓ := H.ℓ', g := H.g' }
        H.i₀ H.curGE H.curEncE).1 := by
  rw [modelEq_loop H]
  exact branchBUpdateLoop_int hi (i₀_pos H) (H.loop.2.2.2.2.2.2.1 hi)

/-- At the terminal exits (`i₀ = d`), the chain of `alg2PreResetState` is the update loop at
level `d` with `rem = 0` (`modelEq_loop` and `branchBUpdateLoop_term`). -/
theorem modelEq_term (hi : H.i₀ = cfg.P.d) :
    (alg2PreResetState cfg model U H.gVec H.lVec).chain =
      (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g' 0 cfg.P.d H.chE
        H.curGE H.curUE H.curEncE).1 := by
  rw [modelEq_loop H, hi]
  exact branchBUpdateLoop_term

end BranchBRunPreExitKFBL

end MinCostFlow.MinRatio
