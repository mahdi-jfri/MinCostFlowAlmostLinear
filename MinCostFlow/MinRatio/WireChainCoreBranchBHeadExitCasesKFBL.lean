module

public import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitKFBL

/-!
# The exit of the head of Branch B, one goal for each exit (`WireChainCoreBranchBHeadExitCasesKFBL`)

`BranchBHeadExitGoalKFBL` (`WireChainCoreBranchBHeadExitKFBL.lean`) gives the exit fields of the
head of a run of Branch B from a run up to the exit of the loop (`BranchBRunPreExitKFBL`). The
loop has three exits, by the level `H.i₀` where it stops and the batch `H.curUE` there. This file
states the same conclusion once for each exit, so that the three can be proved on their own:

* `BranchBHeadExitIntGoalKFBL`: the interior exit, `0 < H.i₀` and `H.i₀ < cfg.P.d`;
* `BranchBHeadExitTermGoalKFBL`: the terminal exit with a batch, `H.i₀ = cfg.P.d` and
  `H.curUE ≠ []`;
* `BranchBHeadExitEmptyGoalKFBL`: the terminal exit with an empty batch, `H.i₀ = cfg.P.d` and
  `H.curUE = []`.

`BranchBHeadExitGoalKFBL` follows from the three and from `0 < H.i₀ ≤ cfg.P.d`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- **The exit fields of the head at the interior exit** (`0 < i₀ < d`). -/
@[expose] def BranchBHeadExitIntGoalKFBL : Prop :=
  ∀ {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
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
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ},
    BranchBIntExitLayGoalKFBL → BranchBTermExitLayGoalKFBL →
    BranchBIntExitForestLocGoalKFBL → BranchBTermExitForestLocGoalKFBL →
    ∀ (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
        lastMul
        intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
        bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
        dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
        edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
        collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
        coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
        allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
        editsPtr editWords g l heap pos ω mem0 mem model tok U B R),
    0 < H.i₀ → H.i₀ < cfg.P.d →
    ∃ (sX : State) (cX fr vcL ecL termTokN hT : ℕ) (tokN : ℕ → Rcore.τ)
      (X : ChainState cfg.T cfg.P),
      (BranchBExitOutKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
        (capExp := capExp) H.A vcL ecL (heap + 1 + 12 * cfg.P.d)
        (heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1)) tok.intCap fr H.st0 H.chE X H.levelU H.D H.sE sX
            H.tokE tokN
        termTokN hT) ∧
      (BranchBExitCaseKFBL w L P vCap eCap capExp capLimit lastMul lastSpace dgApply
        initCore coreLenProc lastInit cfg Psc Rcore p opCore ω levelSpace levelCost tok H.A H.ℓ'
            H.g' H.i₀ H.sE
        H.sL H.chE H.curGE H.curUE H.curEncE H.bWE H.tokE sX cX fr vcL ecL termTokN hT tokN X) ∧
      (X = (alg2PreResetState cfg model U H.gVec H.lVec).chain) ∧
      (BranchBExitForestLocKFBL
        (RL := LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
          (model.chain.G cfg.P.d).E) H.A (heap + 1 + 12 * cfg.P.d)
        (heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1)) fr
        (if fr ≤ cfg.P.d then chainSuffixForests H.st0 fr else [])
        (if fr ≤ cfg.P.d then chainSuffixForests X fr else []) H.tokE tok.termTok sX) ∧
      (BranchBRebuiltOrdKFBL (solverLevelMetaAddr tok.table cfg.P.d) cfg.P.d (fr + 1)
        heap vCap eCap L sX.mem)

/-- **The exit fields of the head at the terminal exit with a batch** (`i₀ = d`,
`curUE ≠ []`). -/
@[expose] def BranchBHeadExitTermGoalKFBL : Prop :=
  ∀ {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
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
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ},
    BranchBIntExitLayGoalKFBL → BranchBTermExitLayGoalKFBL →
    BranchBIntExitForestLocGoalKFBL → BranchBTermExitForestLocGoalKFBL →
    ∀ (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
        lastMul
        intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
        bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
        dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
        edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
        collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
        coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
        allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
        editsPtr editWords g l heap pos ω mem0 mem model tok U B R),
    H.i₀ = cfg.P.d → H.curUE ≠ [] →
    ∃ (sX : State) (cX fr vcL ecL termTokN hT : ℕ) (tokN : ℕ → Rcore.τ)
      (X : ChainState cfg.T cfg.P),
      (BranchBExitOutKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
        (capExp := capExp) H.A vcL ecL (heap + 1 + 12 * cfg.P.d)
        (heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1)) tok.intCap fr H.st0 H.chE X H.levelU H.D H.sE sX
            H.tokE tokN
        termTokN hT) ∧
      (BranchBExitCaseKFBL w L P vCap eCap capExp capLimit lastMul lastSpace dgApply
        initCore coreLenProc lastInit cfg Psc Rcore p opCore ω levelSpace levelCost tok H.A H.ℓ'
            H.g' H.i₀ H.sE
        H.sL H.chE H.curGE H.curUE H.curEncE H.bWE H.tokE sX cX fr vcL ecL termTokN hT tokN X) ∧
      (X = (alg2PreResetState cfg model U H.gVec H.lVec).chain) ∧
      (BranchBExitForestLocKFBL
        (RL := LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
          (model.chain.G cfg.P.d).E) H.A (heap + 1 + 12 * cfg.P.d)
        (heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1)) fr
        (if fr ≤ cfg.P.d then chainSuffixForests H.st0 fr else [])
        (if fr ≤ cfg.P.d then chainSuffixForests X fr else []) H.tokE tok.termTok sX) ∧
      (BranchBRebuiltOrdKFBL (solverLevelMetaAddr tok.table cfg.P.d) cfg.P.d (fr + 1)
        heap vCap eCap L sX.mem)

/-- **The exit fields of the head at the terminal exit with an empty batch**
(`i₀ = d`, `curUE = []`). -/
@[expose] def BranchBHeadExitEmptyGoalKFBL : Prop :=
  ∀ {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
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
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ},
    BranchBIntExitLayGoalKFBL → BranchBTermExitLayGoalKFBL →
    BranchBIntExitForestLocGoalKFBL → BranchBTermExitForestLocGoalKFBL →
    ∀ (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
        lastMul
        intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
        bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
        dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
        edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
        collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
        coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
        allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
        editsPtr editWords g l heap pos ω mem0 mem model tok U B R),
    H.i₀ = cfg.P.d → H.curUE = [] →
    ∃ (sX : State) (cX fr vcL ecL termTokN hT : ℕ) (tokN : ℕ → Rcore.τ)
      (X : ChainState cfg.T cfg.P),
      (BranchBExitOutKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
        (capExp := capExp) H.A vcL ecL (heap + 1 + 12 * cfg.P.d)
        (heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1)) tok.intCap fr H.st0 H.chE X H.levelU H.D H.sE sX
            H.tokE tokN
        termTokN hT) ∧
      (BranchBExitCaseKFBL w L P vCap eCap capExp capLimit lastMul lastSpace dgApply
        initCore coreLenProc lastInit cfg Psc Rcore p opCore ω levelSpace levelCost tok H.A H.ℓ'
            H.g' H.i₀ H.sE
        H.sL H.chE H.curGE H.curUE H.curEncE H.bWE H.tokE sX cX fr vcL ecL termTokN hT tokN X) ∧
      (X = (alg2PreResetState cfg model U H.gVec H.lVec).chain) ∧
      (BranchBExitForestLocKFBL
        (RL := LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
          (model.chain.G cfg.P.d).E) H.A (heap + 1 + 12 * cfg.P.d)
        (heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1)) fr
        (if fr ≤ cfg.P.d then chainSuffixForests H.st0 fr else [])
        (if fr ≤ cfg.P.d then chainSuffixForests X fr else []) H.tokE tok.termTok sX) ∧
      (BranchBRebuiltOrdKFBL (solverLevelMetaAddr tok.table cfg.P.d) cfg.P.d (fr + 1)
        heap vCap eCap L sX.mem)

end MinCostFlow.MinRatio

end
