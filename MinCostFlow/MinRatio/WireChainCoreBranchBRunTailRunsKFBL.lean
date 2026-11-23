module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailPartGoalsKFBL
import WordRAM.Tactic

/-!
# The run of the whole core of Branch B from its parts (`WireChainCoreBranchBRunTailRunsKFBL`)

Branch B is the statement `wireBranchBKFBL`: the prefix, the front, the loop, a test of
`reg 96 < reg 75` that picks the interior exit or the terminal exit, and the suffix. A head of a
run holds the runs of the first three parts and of the exit. `core_runs` joins them with a run of
the suffix from the state `sX` after the exit (`runs_seq_iff`, `runs_cond_iff`) and turns the run
of Branch B into a run of the whole core (`dispatchRuns`). At the end of the loop, `reg 96` holds
the level `i₀` of the exit and `reg 75` holds `d` (the loop invariant at the top of the last pass,
and the loop facts on the registers), so the test picks the interior exit exactly when `i₀ < d`.
This proves `BranchBTailRunsGoalKFBL`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

namespace BranchBRunHeadKFBL

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

variable (Hd : BranchBRunHeadKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)

/-- **The run of the whole core from the parts of a run of Branch B.** A run of the suffix from the
state `sX` after the exit gives a run of the chain core from the start state, at the cost of the
parts plus `8` (one step for each of the four sequences of `wireBranchBKFBL` and four for the
test). -/
theorem core_runs (o : Outcome) (out : State) (cS : ℕ)
    (hSuf : Runs w p ω (wireBranchBSuffixKFBL emitCuts packEditsProc filterEdits (opTree 4)
      (opTree 1) (opTree 0) bind canonCopy isNeg pushInsProc) Hd.sX o out cS) :
    ∃ cost : ℕ, Runs w p ω (ordChainUpdateCoreBodyKFBL
        (wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg
          refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
          sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit rebuildOffReadyProc)
        (wireBranchBKFBL collectDel emitCuts packEditsProc filterEdits zeroIns
          refreshAccountsProc updateLen0Proc copyProc updLen slotProc pushInsProc bind canonCopy
          isNeg dgApply initCore coreLenProc lastInit opTree opCore))
      (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos) o out cost ∧
      cost ≤ Hd.c0 + Hd.cP + Hd.cF + Hd.cL + Hd.cX + cS + 12 := by
  have hLR := Hd.loop.2.2.2.2.2.2.2.2.2.1
  obtain ⟨_, _, _, _, _, _, _, _, r75, _, _, _, _, _, _, _, _, _, r96, _⟩ :=
    Hd.loop.2.2.2.2.1.regs
  have h96 : Hd.sL.regs 96 = Hd.i₀ := (hLR 96 (by omega) (by omega) (by omega) (by omega)).trans r96
  have h75 : Hd.sL.regs 75 = cfg.P.d :=
    (hLR 75 (by omega) (by omega) (by omega) (by omega)).trans r75
  have hw1 : 1 < 2 ^ w := by have := Hd.envA.w18; omega
  have hw0 : 0 < 2 ^ w := by omega
  -- the test and the exit
  have hCond : ∃ c, Runs w p ω (.cond (.bin .lt (.reg 96) (.reg 75))
      (wireBranchBIntKFBL dgApply initCore (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit)
      (wireBranchBTermKFBL (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit ;;
        collectTermForestStmt 81)) Hd.sL .normal Hd.sX c ∧ c = Hd.cX + 4 := by
    rcases Hd.exitCase with ⟨_, hi, _, _, _, _, hRun, _⟩ |
        ⟨hi, _, _, _, _, _, _, hRun, _⟩ | ⟨hi, _, _, _, _, _, _, _, _, hRun, _⟩
    · refine ⟨_, runs_cond_iff.mpr ⟨1, Hd.cX, ?_, ?_, rfl⟩, by simp [Expr.size]; omega⟩
      · simp [Expr.eval, BinOp.eval, h96, h75, hi, hw1]
      · simpa using hRun
    · refine ⟨_, runs_cond_iff.mpr ⟨0, Hd.cX, ?_, ?_, rfl⟩, by simp [Expr.size]; omega⟩
      · simp [Expr.eval, BinOp.eval, h96, h75, hi, hw0]
      · simpa using hRun
    · refine ⟨_, runs_cond_iff.mpr ⟨0, Hd.cX, ?_, ?_, rfl⟩, by simp [Expr.size]; omega⟩
      · simp [Expr.eval, BinOp.eval, h96, h75, hi, hw0]
      · simpa using hRun
  obtain ⟨cC, hC, hcC⟩ := hCond
  have hB : Runs w p ω (wireBranchBKFBL collectDel emitCuts packEditsProc filterEdits zeroIns
      refreshAccountsProc updateLen0Proc copyProc updLen slotProc pushInsProc bind canonCopy
      isNeg dgApply initCore coreLenProc lastInit opTree opCore) Hd.st o out
      (Hd.cP + (Hd.cF + (Hd.cL + (cC + cS + 1) + 1) + 1) + 1) := by
    unfold wireBranchBKFBL
    refine runs_seq_iff.mpr (Or.inr ⟨_, _, _, Hd.pre.1, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨_, _, _, Hd.front.1, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨_, _, _, Hd.loop.1, ?_, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, hC, hSuf, rfl⟩)
  refine ⟨_, Hd.dispatchRuns o out _ hB, ?_⟩
  omega

end BranchBRunHeadKFBL

/-- The run goal of the tail (`BranchBTailRunsGoalKFBL`) holds: `core_runs`. -/
theorem branchBTailRunsGoalKFBL_proved : BranchBTailRunsGoalKFBL :=
  fun Hd o out cS h => BranchBRunHeadKFBL.core_runs Hd o out cS h

end MinCostFlow.MinRatio

end
