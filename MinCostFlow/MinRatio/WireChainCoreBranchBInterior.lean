module

public import MinCostFlow.MinRatio.WireChainCoreOps
public import MinCostFlow.MinRatio.WireChainCoreAlgebra
public import MinCostFlow.MinRatio.WireChainSpecs
public import MinCostFlow.MinRatio.WireRebuildSuffixLoopK
import MinCostFlow.MinRatio.WireShiftDeepPrep
import WordRAM.Tactic

/-!
# Branch B interior periodic rebuild step (`WireChainCoreBranchBInterior`)

Provides `wireBranchBInteriorRebuildStep` and `wireBranchBInteriorRebuildStep_runs` for an
interior periodic rebuild at `0 < idx < d` inside Branch B of `ordChainUpdateCoreBody`:
1. Applies `curBatch` (`reg 10`) to `levelGraphs[idx]` in place via `dgApplyBatch`.
2. Reads the output rotation order `OrdListAt` of level `idx - 1` (op `5`) into `reg 9`.
3. Increments `rebuildCount[idx]` via `incrementLevelCounter`.
4. Rebuilds chain levels `idx .. d` via `ordRebuildSuffixProgramKStore_runs`.
5. Zeroes `updCount[idx .. d - 1]` via `wireZeroUpdCountLoop_runs` and sets `reg 97 := 1`
   (`rebuiltFlag`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- Interior periodic rebuild at `0 < idx = reg 96 < d`: applies `curBatch` (`reg 10`) to
`levelGraphs[idx]`, reads `ord` from level `idx - 1` (op `5`), increments `rebuildCount[idx]`,
rebuilds suffix `idx .. d` via `ordRebuildSuffixProgramKStore`, zeroes `updCount[idx .. d - 1]`,
and sets `reg 97 := 1`. -/
@[expose] def wireBranchBInteriorRebuildStep
    (dgApply readOrd initCore readGraph readLSF coreLenProc lastInit : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 96))) ;;
  .call 15 dgApply [.reg 6, .reg 10, .const 1] ;;
  .assign 22 (.bin .sub (.reg 96) (.const 1)) ;;
  .assign 3 (.load (.bin .add (.reg 77) (.reg 22))) ;;
  .assign 2 (.load (.bin .add (.reg 78) (.reg 22))) ;;
  ordCoreReadOrdStmt readOrd ;;
  .assign 4 (.reg 5) ;;
  .assign 0 (.reg 86) ;;
  .assign 1 (.reg 96) ;;
  incrementLevelCounter ;;
  .assign 1 (.reg 76) ;;
  .assign 7 (.load (.bin .add (.reg 83) (.reg 96))) ;;
  .assign 8 (.reg 7) ;;
  .assign 20 (.reg 96) ;;
  .assign 21 (.reg 75) ;;
  .assign 51 (.bin .add (.reg 77) (.reg 96)) ;;
  .assign 52 (.bin .add (.reg 78) (.reg 96)) ;;
  .assign 56 (.load (.bin .add (.reg 73) (.const 10))) ;;
  .assign 57 (.reg 82) ;;
  .assign 58 (.reg 83) ;;
  .assign 67 (.reg 94) ;;
  .assign 68 (.reg 95) ;;
  ordRebuildSuffixProgramKStore initCore readGraph readLSF coreLenProc readOrd lastInit ;;
  .assign 20 (.reg 96) ;;
  wireZeroUpdCountLoop ;;
  .assign 97 (.const 1)

theorem wireBranchBInteriorRebuildStep_noRand
    (dgApply readOrd initCore readGraph readLSF coreLenProc lastInit : ℕ) :
    (wireBranchBInteriorRebuildStep dgApply readOrd initCore readGraph readLSF coreLenProc
      lastInit).NoRand := by
  simp [wireBranchBInteriorRebuildStep, ordCoreReadOrdStmt, incrementLevelCounter_noRand,
    ordRebuildSuffixProgramKStore_noRand, wireZeroUpdCountLoop_noRand, Stmt.NoRand]

set_option maxHeartbeats 800000 in
/-- Execute `wireBranchBInteriorRebuildStep` at `0 < idx < d`. -/
theorem wireBranchBInteriorRebuildStep_runs
    {w L P m capExp lastMul intCapMax forestEdgeCap drainUnit wordExp stretchPrec
      dgCap ecCap lastSpace termUpdSpace termUpdCost
      dgApply initCore coreLenProc edgeProc signExt mul intDiv copy lastInit
      idx coreHPrev gPtr lPtr vcIdx ecIdx vcPrev ecPrev curBatch curBatchWords curHeap
      handle handleBase branchBase lvlMTable levelMeta rebuildCountBase updCountBase : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {levelSpace levelCost updStepSpace updStepCost : ℕ → ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opCore opLast : ℕ → ℕ}
    {ω : ℕ → Bool} {st : State}
    (ch : ChainState cfg.T cfg.P) (curU : List Update) (ℓ' g' ℓi : ℕ → ℝ) (extraEnc : ℕ)
    (tokPrev0 : Rcore.τ)
    (hCoreLocal : Rcore.Local)
    (hFour : fmt.limbBits = 4) (hPrec : fmt.precision = P) (hWidth : P ≤ 4 * L)
    (hLWord : L < 2 ^ w) (hPWord : P < 2 ^ w)
    (hIdxPos : 0 < idx) (hIdxLt : idx < cfg.P.d)
    (hdW : cfg.P.d < 2 ^ w) (hkPos : 0 < cfg.P.k) (hkW : cfg.P.k < 2 ^ w) (hNW : ch.N₀ < 2 ^ w)
    (hw18 : 18 < 2 ^ w)
    (hInitOrdEq : ToolInitOrdEqOnE cfg.T) (hWordExpEq : Psc.wordExp = wordExp)
    (hDGApply : MeetsContract w p dgApply
      (dgApplyBatchContract w vcIdx ecIdx (ch.G idx) (ch.G idx) curU curBatchWords))
    (hCoreImplPrev : Rcore.Implements w p initCore opCore
      (sparseCoreOrdMachineContractK fmt L cfg.T (ch.G (idx - 1)) cfg.P.k (ch.lvlM (idx - 1))
        ch.N₀ vcPrev ecPrev capExp Psc (allocation (idx - 1))))
    (hCoreImpl : ∀ j, idx ≤ j → j < cfg.P.d → ∀ (G : MGraph) (M vc ec : ℕ),
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractK fmt L cfg.T G cfg.P.k M ch.N₀ vc ec capExp Psc (allocation j)))
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hLastImpl : ∀ (G : MGraph) (vc ec : ℕ),
      (LastLevelProgram.lastLevelRepresentation vc ec 4 L fmt.precision G.E).Implements
        w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L cfg.L G vc ec lastMul stretchPrec lastAlloc))
    (hOps : UpdateCoreOpsHyp (w := w) (L := L) (P := P) (m := m) (capExp := capExp)
      (lastMul := lastMul) (intCapMax := intCapMax) (forestEdgeCap := forestEdgeCap)
      (drainUnit := drainUnit) (coreSpace := coreSpace) (coreFixed := coreFixed)
      (toolMul := toolMul) (fmt := fmt) (cfg := cfg) (Psc := Psc)
      (allocation := allocation) (lastAlloc := lastAlloc)
      Rcore dgCap ecCap levelSpace levelCost updStepSpace updStepCost lastSpace termUpdSpace
      termUpdCost)
    (hRebInv : UpdateRebuildModelInv w L P wordExp stretchPrec ch idx
      ((ch.G idx).applyBatch curU) ℓ' g' extraEnc)
    (hLenIEq : ∀ e ∈ ((ch.G idx).applyBatch curU).E,
      let stLG : ChainState cfg.T cfg.P := { ch with ℓ := ℓ', g := g' }
      let next := (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stLG idx
        ((ch.G idx).applyBatch curU) extraEnc).1
      ℓi e = next.toTreeChain.chainLen next.ℓ idx e)
    (hRegs :
      st.regs 4 = curHeap ∧ st.regs 10 = curBatch ∧ st.regs 73 = handle ∧
      st.regs 75 = cfg.P.d ∧ st.regs 76 = cfg.P.k ∧ st.regs 77 = handleBase ∧
      st.regs 78 = branchBase ∧ st.regs 82 = lvlMTable ∧ st.regs 83 = levelMeta ∧
      st.regs 85 = updCountBase ∧ st.regs 86 = rebuildCountBase ∧
      st.regs 94 = L ∧ st.regs 95 = P ∧ st.regs 96 = idx)
    (hCells :
      st.mem (handle + 10) = ch.N₀ ∧
      st.mem (handleBase + (idx - 1)) = coreHPrev ∧
      st.mem (branchBase + (idx - 1)) = ch.bran (idx - 1) ∧
      st.mem (levelMeta + cfg.P.d + idx) = gPtr ∧
      st.mem (levelMeta + idx) = lPtr ∧
      st.mem (rebuildCountBase + idx) = ch.rebuildCount idx ∧
      (∀ j, idx ≤ j → j < cfg.P.d → st.mem (lvlMTable + j) = ch.lvlM j))
    (hBrPrevLt : ch.bran (idx - 1) < cfg.P.k) (hCoreHPrevW : coreHPrev < 2 ^ w)
    (hRepPrev : Rcore.rep coreHPrev (chainLevelOrdAbs ch (idx - 1)) tokPrev0 st.mem)
    (hInPrev : SparseCoreOrdInput cfg.T cfg.P.k (ch.lvlM (idx - 1)) ch.N₀
      (ch.scState (idx - 1)) (ch.G (idx - 1)) (ch.levelOrd (idx - 1)) (ch.updCount (idx - 1)))
    (hFootPrev : ∀ a, Rcore.foot coreHPrev tokPrev0 a → a < curHeap)
    (hGAt : DynGraphAt st.mem gPtr vcIdx ecIdx (ch.G idx))
    (hLenAt : EdgeValuesAt st.mem lPtr 4 L P ((ch.G idx).applyBatch curU).E ℓi)
    (hSmall : SmallBatchAt st.mem curBatch (ch.G idx) curU curBatchWords)
    (hBatchValid : (ch.G idx).BatchIsValid curU)
    (hBatchCaps : BatchWithinCaps vcIdx ecIdx curU)
    (hBatchW : ∀ j < curBatchWords, st.mem (curBatch + j) < 2 ^ w)
    (hBounds :
      handle + 18 ≤ curHeap ∧ handleBase + cfg.P.d < curHeap ∧ branchBase + cfg.P.d < curHeap ∧
      lvlMTable + cfg.P.d ≤ curHeap ∧ levelMeta + 2 * cfg.P.d ≤ curHeap ∧
      rebuildCountBase + cfg.P.d < curHeap ∧ updCountBase + cfg.P.d ≤ curHeap ∧
      gPtr + dynGraphSize vcIdx ecIdx ≤ curHeap ∧ lPtr + ecIdx * L ≤ curHeap ∧
      curBatch + curBatchWords ≤ curHeap)
    (hSep :
      let d := cfg.P.d
      (handleBase + d < branchBase ∨ branchBase + d < handleBase) ∧
      (handleBase + d < lvlMTable ∨ lvlMTable + d ≤ handleBase) ∧
      (branchBase + d < lvlMTable ∨ lvlMTable + d ≤ branchBase) ∧
      (handleBase + d < levelMeta ∨ levelMeta + 2 * d ≤ handleBase) ∧
      (branchBase + d < levelMeta ∨ levelMeta + 2 * d ≤ branchBase) ∧
      (lvlMTable + d ≤ levelMeta ∨ levelMeta + 2 * d ≤ lvlMTable) ∧
      (rebuildCountBase + d < handle ∨ handle + 18 ≤ rebuildCountBase) ∧
      (rebuildCountBase + d < lvlMTable ∨ lvlMTable + d ≤ rebuildCountBase) ∧
      (rebuildCountBase + d < handleBase ∨ handleBase + d < rebuildCountBase) ∧
      (rebuildCountBase + d < branchBase ∨ branchBase + d < rebuildCountBase) ∧
      (rebuildCountBase + d < levelMeta ∨ levelMeta + 2 * d ≤ rebuildCountBase) ∧
      (rebuildCountBase + d < updCountBase ∨ updCountBase + d ≤ rebuildCountBase) ∧
      (updCountBase + d ≤ handleBase ∨ handleBase + d < updCountBase) ∧
      (updCountBase + d ≤ branchBase ∨ branchBase + d < updCountBase) ∧
      (updCountBase + d ≤ levelMeta ∨ levelMeta + 2 * d ≤ updCountBase) ∧
      (∀ a, gPtr ≤ a → a < gPtr + dynGraphSize vcIdx ecIdx →
        ¬ Rcore.foot coreHPrev tokPrev0 a ∧
        (a < curBatch ∨ curBatch + curBatchWords ≤ a) ∧
        (a < handle ∨ handle + 18 ≤ a) ∧
        (a < handleBase ∨ handleBase + d < a) ∧
        (a < branchBase ∨ branchBase + d < a) ∧
        (a < lvlMTable ∨ lvlMTable + d ≤ a) ∧
        (a < levelMeta ∨ levelMeta + 2 * d ≤ a) ∧
        (a < rebuildCountBase ∨ rebuildCountBase + d < a) ∧
        (a < updCountBase ∨ updCountBase + d ≤ a) ∧
        (a < lPtr ∨ lPtr + ecIdx * L ≤ a)) ∧
      (∀ a, lPtr ≤ a → a < lPtr + ecIdx * L →
        ¬ Rcore.foot coreHPrev tokPrev0 a ∧
        (a < handleBase ∨ handleBase + d < a) ∧
        (a < branchBase ∨ branchBase + d < a) ∧
        (a < levelMeta ∨ levelMeta + 2 * d ≤ a) ∧
        (a < rebuildCountBase ∨ rebuildCountBase + d < a) ∧
        (a < updCountBase ∨ updCountBase + d ≤ a)) ∧
      ¬ Rcore.foot coreHPrev tokPrev0 (handle + 10) ∧
      (∀ j, idx ≤ j → j < d → ¬ Rcore.foot coreHPrev tokPrev0 (lvlMTable + j)) ∧
      ¬ Rcore.foot coreHPrev tokPrev0 (rebuildCountBase + idx) ∧
      (∀ j, idx ≤ j → j ≤ d →
        ¬ Rcore.foot coreHPrev tokPrev0 (handleBase + j) ∧
        ¬ Rcore.foot coreHPrev tokPrev0 (branchBase + j)) ∧
      (∀ j, idx ≤ j → j < d →
        ¬ Rcore.foot coreHPrev tokPrev0 (levelMeta + j) ∧
        ¬ Rcore.foot coreHPrev tokPrev0 (levelMeta + d + j) ∧
        ¬ Rcore.foot coreHPrev tokPrev0 (updCountBase + j)))
    (hz : ZeroFrom st.mem curHeap)
    (hRoom : curHeap + (1 + ordRotWords (chainLevelOrdAbs ch (idx - 1)) (ch.bran (idx - 1))) +
      (Finset.Ico idx cfg.P.d).sum levelSpace + lastSpace < 2 ^ w) :
    let d := cfg.P.d
    let curG := (ch.G idx).applyBatch curU
    let stLG : ChainState cfg.T cfg.P := { ch with ℓ := ℓ', g := g' }
    let next := (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stLG idx curG extraEnc).1
    ∃ (out : State) (cost vcLast ecLast termTok : ℕ) (tokPrev' : Rcore.τ)
      (coreTok : ℕ → Rcore.τ),
      Runs w p ω
        (wireBranchBInteriorRebuildStep dgApply (opCore 5) initCore (opCore 3) (opCore 2)
          coreLenProc lastInit)
        st .normal out cost ∧
      curHeap ≤ out.regs 4 ∧
      out.regs 4 ≤ curHeap + (1 + ordRotWords (chainLevelOrdAbs ch (idx - 1)) (ch.bran (idx - 1))) +
        (Finset.Ico idx d).sum levelSpace + lastSpace ∧
      ZeroFrom out.mem (out.regs 4) ∧
      out.regs 97 = 1 ∧ out.regs 96 = idx ∧ (∀ r, 70 ≤ r → r ≠ 97 → out.regs r = st.regs r) ∧
      Rcore.rep coreHPrev (chainLevelOrdAbs next (idx - 1)) tokPrev' out.mem ∧
      (∀ a, Rcore.foot coreHPrev tokPrev' a →
        Rcore.foot coreHPrev tokPrev0 a ∨ (curHeap ≤ a ∧ a < out.regs 4)) ∧
      (∀ j, idx ≤ j → j < d →
        out.mem (branchBase + j) = next.bran j ∧
        curHeap ≤ out.mem (handleBase + j) ∧ out.mem (handleBase + j) ≤ out.regs 4 ∧
        Rcore.rep (out.mem (handleBase + j)) (chainLevelOrdAbs next j) (coreTok j) out.mem ∧
        (∀ a, Rcore.foot (out.mem (handleBase + j)) (coreTok j) a →
          curHeap ≤ a ∧ a < out.regs 4 ∧ ¬ Rcore.foot coreHPrev tokPrev' a)) ∧
      (∀ j₁ j₂, idx ≤ j₁ → j₁ < d → idx ≤ j₂ → j₂ < d → j₁ ≠ j₂ →
        ∀ a, Rcore.foot (out.mem (handleBase + j₁)) (coreTok j₁) a →
          ¬ Rcore.foot (out.mem (handleBase + j₂)) (coreTok j₂) a) ∧
      DynGraphAt out.mem gPtr vcIdx ecIdx (next.G idx) ∧
      EdgeValuesAt out.mem lPtr 4 L P (next.G idx).E (next.toTreeChain.chainLen next.ℓ idx) ∧
      (∀ j, idx + 1 ≤ j → j < d →
        ∃ vc ec,
          DynGraphAt out.mem (out.mem (levelMeta + d + j)) vc ec (next.G j) ∧
          curHeap ≤ out.mem (levelMeta + d + j) ∧
          out.mem (levelMeta + d + j) + dynGraphSize vc ec ≤ out.regs 4 ∧
          EdgeValuesAt out.mem (out.mem (levelMeta + j)) 4 L P (next.G j).E
            (next.toTreeChain.chainLen next.ℓ j) ∧
          curHeap ≤ out.mem (levelMeta + j) ∧
          out.mem (levelMeta + j) + ec * L ≤ out.regs 4 ∧
          (∀ a, out.mem (levelMeta + j) ≤ a → a < out.mem (levelMeta + j) + ec * L →
            ¬ Rcore.foot coreHPrev tokPrev' a ∧
            (∀ r, idx ≤ r → r < d → ¬ Rcore.foot (out.mem (handleBase + r)) (coreTok r) a) ∧
            ¬ (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (next.G d).E).foot
              (out.mem (handleBase + d)) termTok a) ∧
          (∀ a, out.mem (levelMeta + d + j) ≤ a →
            a < out.mem (levelMeta + d + j) + dynGraphSize vc ec →
            ¬ Rcore.foot coreHPrev tokPrev' a ∧
            (∀ r, idx ≤ r → r < d → ¬ Rcore.foot (out.mem (handleBase + r)) (coreTok r) a) ∧
            ¬ (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (next.G d).E).foot
              (out.mem (handleBase + d)) termTok a)) ∧
      out.mem (branchBase + d) = next.lastBran ∧
      curHeap ≤ out.mem (handleBase + d) ∧
      (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (next.G d).E).rep
        (out.mem (handleBase + d)) (next.lastK, next.lastLSFs) termTok out.mem ∧
      (∀ a, (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (next.G d).E).foot
          (out.mem (handleBase + d)) termTok a →
        curHeap ≤ a ∧ a < out.regs 4 ∧ ¬ Rcore.foot coreHPrev tokPrev' a ∧
        ∀ j, idx ≤ j → j < d → ¬ Rcore.foot (out.mem (handleBase + j)) (coreTok j) a) ∧
      out.mem (rebuildCountBase + idx) = ch.rebuildCount idx + 1 ∧
      (∀ j, idx ≤ j → j < d → out.mem (updCountBase + j) = 0) ∧
      (∀ a < curHeap,
        ¬ Rcore.foot coreHPrev tokPrev0 a →
        (a < gPtr ∨ gPtr + dynGraphSize vcIdx ecIdx ≤ a) →
        a ≠ rebuildCountBase + idx →
        (a < handleBase + idx ∨ handleBase + d < a) →
        (a < branchBase + idx ∨ branchBase + d < a) →
        ((a < levelMeta + (idx + 1) ∨ levelMeta + d ≤ a) ∧
         (a < levelMeta + d + (idx + 1) ∨ levelMeta + 2 * d ≤ a)) →
        (a < updCountBase + idx ∨ updCountBase + d ≤ a) →
        out.mem a = st.mem a) ∧
      cost + Rcore.phi coreHPrev tokPrev' out.mem +
          (Finset.Ico idx d).sum (fun j => Rcore.phi (out.mem (handleBase + j)) (coreTok j) out.mem) ≤
        updStepCost idx +
          (Finset.Ico idx d).sum (fun j => levelCost j + 9) +
          lastMul * (cfg.L.cost (next.G d) + 1) + 20 * d + 150 +
          Rcore.phi coreHPrev tokPrev0 st.mem := by
  dsimp only
  let d := cfg.P.d
  set curG := (ch.G idx).applyBatch curU
  let stLG : ChainState cfg.T cfg.P := { ch with ℓ := ℓ', g := g' }
  let next := (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stLG idx curG extraEnc).1
  obtain ⟨hr4, hr10, hr73, hr75, hr76, hr77, hr78, hr82, hr83, hr85, hr86, hr94, hr95, hr96⟩ := hRegs
  obtain ⟨hH10, hHPrev, hBPrev, hGCell, hLCell, hRCCell, hLvlM⟩ := hCells
  obtain ⟨hHLe, hHBLe, hBBLe, hMLe, hLMLe, hRCLe, hUCLe, hGLe, hLLe, hBLe⟩ := hBounds
  obtain ⟨hSepHB, hSepHM, hSepBM, hSepHL, hSepBL, hSepML, hRCH, hRCM, hRCHB, hRCBB, hRCLM, hRCUC,
    hUCHB, hUCBB, hUCLM, hDisjG, hDisjL, hFootH10, hFootLvlM, hFootRC, hFootHB, hFootLMUC⟩ := hSep
  obtain ⟨hRCNext, _, hRebLvls, hLastAgree, hLastPos, hLastStr⟩ := hRebInv
  obtain ⟨hExPre, hExGIdx, hExLvls, hExLast, hExLastBr, _, hExEll, _, hExLvlM, hExN0, _⟩ :=
    ordAlgorithm1_rebuild_exact cfg.T cfg.L cfg.P stLG hIdxLt curG extraEnc
  have hNextN0 : next.N₀ = ch.N₀ := hExN0
  have hNextLvlM : ∀ j, next.lvlM j = ch.lvlM j := fun j => congrFun hExLvlM j
  have hPrevAbsEq : chainLevelOrdAbs next (idx - 1) = chainLevelOrdAbs ch (idx - 1) := by
    have hp := hExPre (idx - 1) (by omega)
    have hOrdPrev : next.levelOrd (idx - 1) = ch.levelOrd (idx - 1) := by
      unfold ChainState.levelOrd Chain.Ordered.chainLevelOrd
      split_ifs with h0
      · dsimp only [next, stLG]; rw [(hExPre 0 hIdxPos).1]
      · have hp2 := hExPre (idx - 1 - 1) (by omega)
        dsimp only [next, stLG]; rw [hp2.2.1, hp2.2.2.1]
    dsimp only [chainLevelOrdAbs, next, stLG] at hOrdPrev ⊢
    rw [hp.1, hp.2.1, hp.2.2.2.1, hOrdPrev]
  have hNextOrdIdx : next.levelOrd idx = cfg.T.rot (ch.scState (idx - 1)) (ch.bran (idx - 1)) := by
    have hne0 : idx ≠ 0 := by omega
    have hp := hExPre (idx - 1) (by omega)
    simp only [ChainState.levelOrd, Chain.Ordered.chainLevelOrd, hne0, ↓reduceIte]
    dsimp only [next, stLG]
    rw [hp.2.1, hp.2.2.1]
  -- Step 1: load `gPtr`, run `dgApplyBatch`
  let s1 := { st with regs := Function.update st.regs 6 gPtr }
  have r1 : Runs w p ω (.assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 96))))
      st .normal s1 7 :=
    runs_assign_iff.mpr ⟨gPtr, by simp [Expr.eval, BinOp.eval, hr83, hr75, hr96,
      show levelMeta + cfg.P.d < 2 ^ w by omega, show levelMeta + cfg.P.d + idx < 2 ^ w by omega, hGCell], rfl, rfl, rfl⟩
  obtain ⟨bodyDG, hBodyDG, oDG, outDG, cDG, rDGBody, hPostDG, hcDG⟩ :=
    hDGApply [gPtr, curBatch, 1] s1.mem s1.pos ω
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl <;> omega)
      ⟨gPtr, curBatch, 1, rfl, by omega, by omega, by omega,
        fun i hi => by
          by_contra h
          rcases (hDisjG (curBatch + i) (by omega) (by omega)).2.1 with h' | h' <;> omega,
        hBatchW, hSmall.1, hBatchValid, hBatchCaps, hGAt, Or.inl ⟨by decide, rfl⟩⟩
  obtain ⟨_, _, _, hEqDG, _, hDGAfter, hDGFr⟩ := hPostDG
  simp only [List.cons.injEq, and_true] at hEqDG
  obtain ⟨rfl, rfl, rfl⟩ := hEqDG
  have hFold1 : curU.foldl (dgBatchTarget 1) (ch.G idx) = curG := by
    have hfun : dgBatchTarget 1 = MGraph.applyUpdate := by funext H u; simp [dgBatchTarget]
    rw [hfun]; rfl
  have hDGCur : DynGraphAt outDG.mem gPtr vcIdx ecIdx curG := hFold1 ▸ hDGAfter
  let s2 : State := { regs := Function.update s1.regs 15 oDG.value, mem := outDG.mem, pos := outDG.pos }
  have r2 : Runs w p ω (.call 15 dgApply [.reg 6, .reg 10, .const 1]) s1 .normal s2 (3 + cDG + 1) :=
    runs_call_iff.mpr ⟨[gPtr, curBatch, 1], bodyDG, oDG, outDG, cDG,
      by simp [evalArgs, Expr.eval, s1, hr10, show 1 < 2 ^ w by omega],
      hBodyDG, rDGBody, rfl, rfl, by simp [argsSize, Expr.size]⟩
  have hLocPrev2 := hCoreLocal coreHPrev (chainLevelOrdAbs ch (idx - 1)) tokPrev0 st.mem s2.mem
    (fun a ha => (hDGFr a (by by_contra h; exact (hDisjG a (by omega) (by omega)).1 ha)).symm)
  -- Step 2: op `5` (`ordCoreReadOrdK_runs`) on level `idx - 1`
  let s3 := { s2 with regs := Function.update s2.regs 22 (idx - 1) }
  let s4 := { s3 with regs := Function.update s3.regs 3 coreHPrev }
  let s5 := { s4 with regs := Function.update s4.regs 2 (ch.bran (idx - 1)) }
  have hHPrev2 : outDG.mem (handleBase + (idx - 1)) = coreHPrev :=
    (hDGFr _ (by by_contra h; rcases (hDisjG (handleBase + (idx - 1)) (by omega) (by omega)).2.2.2.1 with h' | h' <;> omega)).trans hHPrev
  have hBPrev2 : outDG.mem (branchBase + (idx - 1)) = ch.bran (idx - 1) :=
    (hDGFr _ (by by_contra h; rcases (hDisjG (branchBase + (idx - 1)) (by omega) (by omega)).2.2.2.2.1 with h' | h' <;> omega)).trans hBPrev
  have r3 : Runs w p ω (.assign 22 (.bin .sub (.reg 96) (.const 1))) s2 .normal s3 4 :=
    runs_assign_iff.mpr ⟨idx - 1, by simp [Expr.eval, BinOp.eval, s2, s1, hr96, show 1 < 2 ^ w by omega,
      show idx - 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 77) (.reg 22)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨coreHPrev, by simp [Expr.eval, BinOp.eval, s3, s2, s1, hr77, show handleBase + (idx - 1) < 2 ^ w by omega, hHPrev2], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 78) (.reg 22)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨ch.bran (idx - 1), by simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, hr78, show branchBase + (idx - 1) < 2 ^ w by omega, hBPrev2], rfl, rfl, rfl⟩
  have hz5 : ZeroFrom s5.mem curHeap := fun a ha => (hDGFr a (Or.inr (by omega))).trans (hz a ha)
  obtain ⟨s6, h1, ordW, cOrd, tokPrev1, r6, hs6_5, hs6_9, hRep6, hOrd6, hOrdWLe6, hResp6, hc6, hs6_regs⟩ :=
    ordCoreReadOrdK_runs (w := w) (L := L) (k := cfg.P.k) (M := ch.lvlM (idx - 1)) (N := ch.N₀)
      (vCap := vcPrev) (eCap := ecPrev) (capExp := capExp) (init := initCore)
      (branch := ch.bran (idx - 1)) (handle := coreHPrev) (heap := curHeap)
      (st := s5) (ω := ω) hCoreImplPrev
      (by simp [s5]) (by simp [s5, s4]) (by simp [s5, s4, s3, s2, s1, hr4])
      hBrPrevLt hkW hCoreHPrevW (hLocPrev2.1 hRepPrev) hInPrev hFootPrev hz5 (by omega)
  have hh1Lo : curHeap ≤ h1 := hResp6.1
  have hh1Hi : h1 ≤ curHeap + (1 + ordRotWords (chainLevelOrdAbs ch (idx - 1)) (ch.bran (idx - 1))) := hResp6.2.1
  obtain ⟨hOrdLo6, hOrdEnd6, hOrdWords6⟩ :=
    hOps.op5Placement _ s6.mem (s6.regs 9) ordW curHeap h1 hOrd6 hResp6.2.2.1 hh1Lo
  let s7 := { s6 with regs := Function.update s6.regs 4 h1 }
  have r7 : Runs w p ω (.assign 4 (.reg 5)) s6 .normal s7 2 :=
    runs_assign_iff.mpr ⟨h1, by simp [Expr.eval, hs6_5], rfl, rfl, rfl⟩
  have hs7_eq_st (a : ℕ) (ha : a < curHeap) (hnf : ¬ Rcore.foot coreHPrev tokPrev0 a)
      (hng : a < gPtr ∨ gPtr + dynGraphSize vcIdx ecIdx ≤ a) : s7.mem a = st.mem a :=
    (hResp6.2.2.2.1 a ha hnf).trans (hDGFr a hng)
  have hRC7 : s7.mem (rebuildCountBase + idx) = ch.rebuildCount idx :=
    (hs7_eq_st _ (by omega) hFootRC
      (by by_contra h; rcases (hDisjG (rebuildCountBase + idx) (by omega) (by omega)).2.2.2.2.2.2.2.1 with h' | h' <;> omega)).trans hRCCell
  -- Step 3: increment `rebuildCount[idx]`
  let s8 := { s7 with regs := Function.update s7.regs 0 rebuildCountBase }
  let s9 := { s8 with regs := Function.update s8.regs 1 idx }
  have r8 : Runs w p ω (.assign 0 (.reg 86)) s7 .normal s8 2 :=
    runs_assign_iff.mpr ⟨rebuildCountBase, by simp [Expr.eval, s7, hs6_regs 86 (by decide) (by decide), s5, s4, s3, s2, s1, hr86], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 1 (.reg 96)) s8 .normal s9 2 :=
    runs_assign_iff.mpr ⟨idx, by simp [Expr.eval, s8, s7, hs6_regs 96 (by decide) (by decide), s5, s4, s3, s2, s1, hr96], rfl, rfl, rfl⟩
  obtain ⟨s10, r10, hs10Mem, hs10Regs, _⟩ :=
    incrementLevelCounter_runs (w := w) (base := rebuildCountBase) (level := idx)
      (count := ch.rebuildCount idx) (p := p) (st := s9) (ω := ω)
      (by simp [s9, s8]) (by simp [s9]) hRC7 (by omega) hRCNext
  have hs10_eq7 (a : ℕ) (hne : a ≠ rebuildCountBase + idx) : s10.mem a = s7.mem a := by
    rw [hs10Mem]; simp [s9, s8, Function.update_of_ne hne]
  have hs10_rc : s10.mem (rebuildCountBase + idx) = ch.rebuildCount idx + 1 := by
    rw [hs10Mem]; simp
  have hs10_r (r : ℕ) (h0 : r ≠ 0) (h1' : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4)
      (h5 : r ≠ 5) (h6 : r ≠ 6) (h9 : r ≠ 9) (h15 : r ≠ 15) (h22 : r ≠ 22) :
      s10.regs r = st.regs r := by
    rw [hs10Regs]; simp only [s9, s8, s7, Function.update_of_ne h1', Function.update_of_ne h0,
      Function.update_of_ne h4]
    rw [hs6_regs r h5 h9]
    simp [s5, s4, s3, s2, s1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h22, Function.update_of_ne h15, Function.update_of_ne h6]
  have hs10_4 : s10.regs 4 = h1 := by rw [hs10Regs]; simp [s9, s8, s7]
  have hs10_6 : s10.regs 6 = gPtr := by
    rw [hs10Regs]; simp [s9, s8, s7, hs6_regs 6 (by decide) (by decide), s5, s4, s3, s2, s1]
  have hs10_9 : s10.regs 9 = s6.regs 9 := by rw [hs10Regs]; simp [s9, s8, s7]
  -- Step 4: set up suffix-rebuild regs and run `ordRebuildSuffixProgramKStore` on `[idx, d]`
  let regs11 : ℕ → ℕ :=
    Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update s10.regs
      1 cfg.P.k) 7 lPtr) 8 lPtr) 20 idx) 21 d) 51 (handleBase + idx)) 52 (branchBase + idx))
      56 ch.N₀) 57 lvlMTable) 58 levelMeta) 67 L) 68 P
  let s11 : State := { s10 with regs := regs11 }
  have hs11_ge70 (r : ℕ) (hr : 70 ≤ r) : s11.regs r = st.regs r := by
    have hne : ∀ k < 70, r ≠ k := fun k hk => by omega
    simp only [s11, regs11, Function.update_of_ne (hne 68 (by decide)),
      Function.update_of_ne (hne 67 (by decide)), Function.update_of_ne (hne 58 (by decide)),
      Function.update_of_ne (hne 57 (by decide)), Function.update_of_ne (hne 56 (by decide)),
      Function.update_of_ne (hne 52 (by decide)), Function.update_of_ne (hne 51 (by decide)),
      Function.update_of_ne (hne 21 (by decide)), Function.update_of_ne (hne 20 (by decide)),
      Function.update_of_ne (hne 8 (by decide)), Function.update_of_ne (hne 7 (by decide)),
      Function.update_of_ne (hne 1 (by decide))]
    exact hs10_r r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hs11_4 : s11.regs 4 = h1 := by simp [s11, regs11, hs10_4]
  have hs11_6 : s11.regs 6 = gPtr := by simp [s11, regs11, hs10_6]
  have hs11_7 : s11.regs 7 = lPtr := by simp [s11, regs11]
  have hs11_9 : s11.regs 9 = s6.regs 9 := by simp [s11, regs11, hs10_9]
  have hModelLevel : ∀ j, idx ≤ j → j < d →
      let Gj := next.G j
      let ℓj := next.toTreeChain.chainLen next.ℓ j
      next.scState j = cfg.T.initOrd cfg.P.k (next.lvlM j) next.N₀ Gj
        (fun e => if e ∈ Gj.E then ℓj e else 0)
        (fun e => if e ∈ Gj.E then ℓj e else 0)
        (next.levelOrd j) ∧
      next.G (j + 1) = cfg.T.S (next.scState j) 0 ∧
      next.bran j = 0 ∧ next.updCount j = 0 ∧
      (next.G j).m ≤ next.lvlM j ∧ (next.G j).n ≤ next.N₀ ∧
      next.lvlM j < 2 ^ w ∧ (next.lvlM j + next.N₀ + 2) ^ Psc.wordExp * (L + 1) < 2 ^ w ∧
      IsRotationOrder (next.G j) (next.levelOrd j) ∧
      (∀ e ∈ (next.G j).E, 0 < ℓj e) ∧
      (next.G (j + 1)).E ⊆ (next.G j).E ∧
      (∀ e ∈ (next.G (j + 1)).E,
        ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ fmt.precision =
          next.toTreeChain.chainLen next.ℓ (j + 1) e) := by
    intro j hj1 hj2
    obtain ⟨hScJ, hGJ1, hBrJ, hUpdJ⟩ := hExLvls j hj1 hj2
    obtain ⟨hmLe, hnLe, hMW, hWordE, hRot, hPos, hSub, hFits⟩ := hRebLvls j hj1 hj2
    refine ⟨?_, hGJ1, hBrJ, hUpdJ, hmLe, hnLe, hMW, hWordExpEq ▸ hWordE, hRot, hPos, hSub,
      hPrec ▸ hFits⟩
    rw [hScJ, hNextLvlM j, hNextN0, hExEll]
    exact hInitOrdEq cfg.P.k (ch.lvlM j) ch.N₀ (next.G j) _ _ _ _ (next.levelOrd j)
      (fun e he => by simp [he, stLG, next])
  obtain ⟨s12, cReb, vcLast, ecLast, termTok, coreTok12, rReb, hs12_lo, hs12_hi, hz12, hCores12,
      hCoreDisj12, hMeta12, hTermB12, hTermHLo12, hTermRep12, hTermFoot12, hTermDisj12,
      hs12_frame, hcReb⟩ :=
    ordRebuildSuffixProgramKStore_runs (w := w) (L := L) (capExp := capExp) (init := initCore)
      (coreLenProc := coreLenProc) (edgeProc := edgeProc) (signExt := signExt) (mul := mul)
      (intDiv := intDiv) (copy := copy) (lastInit := lastInit) (first := idx)
      (handleBase := handleBase) (branchBase := branchBase) (lvlMTable := lvlMTable)
      (levelLens := levelMeta) (heapFloor := h1) (lastMul := lastMul)
      (stretchPrec := stretchPrec) (vc0 := vcIdx) (ec0 := ecIdx) (ordWords0 := ordW)
      (fmt := fmt) (T := cfg.T) (LT := cfg.L) (CP := cfg.P) (P := Psc) (allocation := allocation)
      (lastAlloc := lastAlloc) (Rcore := Rcore) (p := p) (op := opCore) (opLast := opLast)
      (st := s11) (ω := ω) next levelSpace levelCost lastSpace (le_of_lt hIdxLt) hCoreLocal
      hFour (hPrec ▸ hWidth) hLWord (hPrec ▸ hPWord) hdW hkPos hkW (hNextN0.symm ▸ hNW) (by omega)
      (by simp [s11, regs11]) (by rw [hs11_4]) (by simp [s11, regs11]) (by simp [s11, regs11, d])
      (by simp [s11, regs11]) (by simp [s11, regs11]) (by simp [s11, regs11, hNextN0])
      (by simp [s11, regs11]) (by simp [s11, regs11]) (by simp [s11, regs11]) (by simp [s11, regs11, hPrec])
      (by omega) (by omega) (by omega) (by omega)
      hSepHB hSepHM hSepBM hSepHL hSepBL hSepML
      (fun j hj1 hj2 => by
        rw [hs10_eq7 _ (by rcases hRCM with h | h <;> omega),
          hs7_eq_st _ (by omega) (hFootLvlM j hj1 hj2)
            (by by_contra h; rcases (hDisjG (lvlMTable + j) (by omega) (by omega)).2.2.2.2.2.1 with h' | h' <;> omega),
          hLvlM j hj1 hj2, hNextLvlM j])
      (by rw [hs11_6, hExGIdx]
          exact dynGraphAt_of_agree hDGCur (fun a ha1 ha2 =>
            (hs10_eq7 a (by rcases (hDisjG a ha1 ha2).2.2.2.2.2.2.2.1 with h | h <;> omega)).trans
              (hResp6.2.2.2.1 a (by omega) (hDisjG a ha1 ha2).1)))
      (by rw [hs11_7, hExGIdx, hPrec]
          have hL11 : EdgeValuesAt s11.mem lPtr 4 L P curG.E ℓi :=
            hLenAt.congr (fun e he t ht => by
              have heL : e * L + L ≤ ecIdx * L := by
                simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt (hDGCur.2.2.1 e he))
              exact (hs10_eq7 _ (by rcases (hDisjL (lPtr + e * L + t) (by omega) (by omega)).2.2.2.2.1 with h | h <;> omega)).trans
                (hs7_eq_st _ (by omega) (hDisjL (lPtr + e * L + t) (by omega) (by omega)).1
                  (by by_contra h; rcases (hDisjG (lPtr + e * L + t) (by omega) (by omega)).2.2.2.2.2.2.2.2.2 with h' | h' <;> omega)))
          exact fun e he => ⟨(hL11 e he).1, (hL11 e he).2.trans (hLenIEq e he)⟩)
      (by simp [s11, regs11])
      (fun _ => ⟨by rw [hs11_9, hNextOrdIdx]
                    exact MinCostFlow.MinRatio.ordListAt_of_agree hOrd6 (fun t ht => hs10_eq7 _ (by omega)),
        fun t ht => by rw [hs11_9, hs10_eq7 _ (by omega)]; exact hOrdWords6 t ht,
        by rw [hs11_9, hs11_4]; exact hOrdEnd6⟩)
      (by rw [hs11_6, hs11_4]; omega) (by rw [hs11_7, hs11_4]; omega)
      (fun a ha1 ha2 => by
        rw [hs11_6] at ha1 ha2
        exact ⟨by rcases (hDisjG a ha1 ha2).2.2.2.1 with h | h <;> omega,
          by rcases (hDisjG a ha1 ha2).2.2.2.2.1 with h | h <;> omega,
          by rcases (hDisjG a ha1 ha2).2.2.2.2.2.2.1 with h | h <;> omega⟩)
      (fun a ha1 ha2 => by
        rw [hs11_7] at ha1 ha2
        exact ⟨by rcases (hDisjL a ha1 ha2).2.1 with h | h <;> omega,
          by rcases (hDisjL a ha1 ha2).2.2.1 with h | h <;> omega,
          by rcases (hDisjL a ha1 ha2).2.2.2.1 with h | h <;> omega⟩)
      (fun a ha => by rw [hs11_4] at ha; exact (hs10_eq7 a (by omega)).trans (hResp6.2.2.1 a ha))
      (fun j hj1 hj2 vc ec => hNextN0.symm ▸ hCoreImpl j hj1 hj2 (next.G j) (next.lvlM j) vc ec)
      hCoreLenProc hEdgeProc hSign hMul hDiv hCopy (fun vc ec => hLastImpl (next.G d) vc ec)
      hModelLevel
      ⟨hExLast.trans (by rw [hExEll]), hExLastBr, hLastAgree, hLastPos, hLastStr⟩
      (fun j hj1 hj2 vc ec gB lB oB oW h _ _ _ _ _ _ hLe => by
        have hSpJ := hOps.levelSpaceDom next j gB lB oB h hj2
        have hSumLe : (Finset.Ico idx j).sum levelSpace + levelSpace j ≤ (Finset.Ico idx d).sum levelSpace := by
          have hIns : Finset.Ico idx (j + 1) = insert j (Finset.Ico idx j) := by
            ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
          have hSub : (Finset.Ico idx (j + 1)).sum levelSpace ≤ (Finset.Ico idx d).sum levelSpace :=
            Finset.sum_le_sum_of_subset (fun x hx => by simp only [Finset.mem_Ico] at hx ⊢; omega)
          rw [hIns, Finset.sum_insert (by simp)] at hSub
          exact le_trans (le_of_eq (Nat.add_comm _ _)) hSub
        have hJRoom : h + levelSpace j < 2 ^ w := by rw [hs11_4] at hLe; dsimp only [d] at hSumLe; omega
        dsimp only at hSpJ
        refine ⟨by clear hGAt hLenAt hOrd6 hModelLevel; omega, fun ret0 _ hret0Hi =>
          ⟨fun m1 h1' raw vcH ecH hDG hh1 hh2 => by
            obtain ⟨hE, hDgH, hEcH⟩ := hOps.op3Placement _ m1 ret0 h1' raw vcH ecH hDG hh1 hh2
            have hEcMul := Nat.mul_le_mul_right L hEcH
            clear hGAt hLenAt hOrd6 hModelLevel hDG
            exact ⟨hE, by omega, by omega⟩,
          fun m2 vcH ecH vcF ecF h2 h3 Lw hDGEx hLSF hLw _ hh2Hi hh2 hh3 => by
            obtain ⟨m1, rawG, hDG⟩ := hDGEx
            obtain ⟨_, hDgH, hEcH⟩ := hOps.op3Placement _ m1 h2 h2 rawG vcH ecH hDG le_rfl (by omega)
            obtain ⟨_, _, _, hS2, hSE, _⟩ := hOps.op2Placement (next.G j) 0 tokPrev0
              m2 h2 h3 vcF ecF Lw _ hLSF hh2 hh3
            have hSubJ := (hModelLevel j hj1 hj2).2.2.2.2.2.2.2.2.2.2.1
            have hMonoSp := wireCoreLenEdgeSpace_mono (max_le_max_left L hLw)
            have hMulSp := Nat.mul_le_mul_left (next.G (j + 1)).m hMonoSp
            have hEcMul := Nat.mul_le_mul_right L hEcH
            have hEndLe : h3 + ecH * L +
                (next.G (j + 1)).m * wireCoreLenEdgeSpace (max L Lw) +
                (1 + ordRotWords (chainLevelOrdAbs next j) 0) ≤ h + levelSpace j := by
              clear hGAt hLenAt hOrd6 hModelLevel hDG hLSF hSE hS2 hSubJ
              omega
            exact ⟨hS2, fun e he => (hSE e (hSubJ he)).1, fun e he => (hSE e (hSubJ he)).2,
              lt_of_le_of_lt hEndLe hJRoom⟩⟩⟩)
      (fun j hj1 hj2 m oPtr oW h hOrd _ hz' hGe => by
        obtain ⟨hLo, hEnd, hW⟩ := hOps.op5Placement _ m oPtr oW h1 h hOrd hz' hGe
        exact ⟨fun a ha1 _ => ⟨by omega, by omega⟩, hEnd, hW⟩)
      (fun j hj1 hj2 m gPtr' vcH ecH oW hDG _ hO2 => by
        obtain ⟨_, hDgH, _⟩ := hOps.op3Placement _ m 0 0 gPtr' vcH ecH hDG le_rfl (by omega)
        exact hOps.levelCostDom next idx j vcH ecH oW hj1 hj2 hDgH hO2)
      (fun vc ec gB lB h _ _ _ hLe => by
        have hLSp := hOps.lastSpaceDom gB lB h
        rw [hs11_4] at hLe
        exact ⟨by omega, hLSp⟩)
      tokPrev0
  rw [hs11_4] at hs12_lo hs12_hi
  have hs12_ge70 (r : ℕ) (hr : 70 ≤ r) : s12.regs r = st.regs r :=
    (ordRebuildSuffixProgramKStore_preserves_ge70 rReb r hr).trans (hs11_ge70 r hr)
  -- Step 5: zero `updCount[idx .. d - 1]` and set `reg 97 := 1`
  let s12a := { s12 with regs := Function.update s12.regs 20 idx }
  have r12a : Runs w p ω (.assign 20 (.reg 96)) s12 .normal s12a 2 :=
    runs_assign_iff.mpr ⟨idx, by simp [Expr.eval, hs12_ge70 96 (by decide), hr96], rfl, rfl, rfl⟩
  obtain ⟨s13, cZero, rZero, hcZero, hUCZero13, hUCFr13, hs13_regs⟩ :=
    wireZeroUpdCountLoop_runs (w := w) (first := idx) (d := d) (updCountBase := updCountBase)
      (p := p) (ω := ω) (st := s12a)
      (by simp [s12a]) (by simp [s12a, hs12_ge70 75 (by decide), hr75, d])
      (by simp [s12a, hs12_ge70 85 (by decide), hr85])
      (le_of_lt hIdxLt) (by omega) (by omega)
  let s14 := { s13 with regs := Function.update s13.regs 97 1 }
  have r14 : Runs w p ω (.assign 97 (.const 1)) s13 .normal s14 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, show 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hs14_r4 : s14.regs 4 = s12.regs 4 := by
    simp only [s14, Function.update_of_ne (by decide : (4 : ℕ) ≠ 97)]
    rw [hs13_regs 4 (by decide)]; simp [s12a]
  have hs14_eq12_ge (a : ℕ) (ha : h1 ≤ a) : s14.mem a = s12.mem a := hUCFr13 a (Or.inr (by omega))
  -- Compose all steps
  have rTail : Runs w p ω
      (ordRebuildSuffixProgramKStore initCore (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit ;;
       .assign 20 (.reg 96) ;; wireZeroUpdCountLoop ;; .assign 97 (.const 1))
      s11 .normal s14 (cReb + (2 + (cZero + 2 + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s12, cReb, _, rReb,
      runs_seq_iff.mpr (Or.inr ⟨s12a, 2, _, r12a,
        runs_seq_iff.mpr (Or.inr ⟨s13, cZero, 2, rZero, r14, rfl⟩), rfl⟩), rfl⟩)
  have goA {s : State} {r : ℕ} {e : Expr} {v : ℕ} {rest : Stmt} {sOut : State} {cRest : ℕ}
      (he : e.eval w s = some v)
      (hr : Runs w p ω rest { s with regs := Function.update s.regs r v } .normal sOut cRest) :
      Runs w p ω (.assign r e ;; rest) s .normal sOut (e.size + 1 + cRest + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨_, e.size + 1, cRest,
      runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hr, rfl⟩)
  have hH10_10 : s10.mem (handle + 10) = ch.N₀ :=
    (hs10_eq7 _ (by rcases hRCH with h | h <;> omega)).trans
      ((hs7_eq_st _ (by omega) hFootH10
        (by by_contra h; rcases (hDisjG (handle + 10) (by omega) (by omega)).2.2.1 with h' | h' <;> omega)).trans hH10)
  have hLCell10 : s10.mem (levelMeta + idx) = lPtr :=
    (hs10_eq7 _ (by rcases hRCLM with h | h <;> omega)).trans
      ((hs7_eq_st _ (by omega) (hFootLMUC idx le_rfl hIdxLt).1
        (by by_contra h; rcases (hDisjG (levelMeta + idx) (by omega) (by omega)).2.2.2.2.2.2.1 with h' | h' <;> omega)).trans hLCell)
  have rSetup : Runs w p ω
      (.assign 1 (.reg 76) ;; .assign 7 (.load (.bin .add (.reg 83) (.reg 96))) ;;
       .assign 8 (.reg 7) ;; .assign 20 (.reg 96) ;; .assign 21 (.reg 75) ;;
       .assign 51 (.bin .add (.reg 77) (.reg 96)) ;; .assign 52 (.bin .add (.reg 78) (.reg 96)) ;;
       .assign 56 (.load (.bin .add (.reg 73) (.const 10))) ;;
       .assign 57 (.reg 82) ;; .assign 58 (.reg 83) ;; .assign 67 (.reg 94) ;; .assign 68 (.reg 95) ;;
       ordRebuildSuffixProgramKStore initCore (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit ;;
       .assign 20 (.reg 96) ;; wireZeroUpdCountLoop ;; .assign 97 (.const 1))
      s10 .normal s14 _ :=
    goA (by simp [Expr.eval, hs10_r 76 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr76])
    (goA (by simp [Expr.eval, BinOp.eval,
      hs10_r 83 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hs10_r 96 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hr83, hr96, show levelMeta + idx < 2 ^ w by omega, hLCell10])
    (goA (by simp [Expr.eval])
    (goA (by simp [Expr.eval, hs10_r 96 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr96])
    (goA (by simp [Expr.eval, hs10_r 75 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr75, d])
    (goA (by simp [Expr.eval, BinOp.eval,
      hs10_r 77 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hs10_r 96 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hr77, hr96, show handleBase + idx < 2 ^ w by omega])
    (goA (by simp [Expr.eval, BinOp.eval,
      hs10_r 78 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hs10_r 96 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hr78, hr96, show branchBase + idx < 2 ^ w by omega])
    (goA (by simp [Expr.eval, BinOp.eval,
      hs10_r 73 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hr73, show 10 < 2 ^ w by omega, show handle + 10 < 2 ^ w by omega, hH10_10])
    (goA (by simp [Expr.eval, hs10_r 82 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr82])
    (goA (by simp [Expr.eval, hs10_r 83 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr83])
    (goA (by simp [Expr.eval, hs10_r 94 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr94])
    (goA (by simp [Expr.eval, hs10_r 95 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr95]) rTail)))))))))))
  have rAll := runs_seq_iff.mpr (Or.inr ⟨s1, 7, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 3 + cDG + 1, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 4, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 5, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, cOrd, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 2, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 2, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 2, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 10, _, r10, rSetup, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- Preserve `tokPrev1` across `r10`, `rReb`, `rZero`
  have hFootPrev1Lt (a : ℕ) (ha : Rcore.foot coreHPrev tokPrev1 a) : a < h1 := by
    rcases hResp6.2.2.2.2 a ha with h0 | ⟨_, hhi⟩
    · exact (hFootPrev a h0).trans_le hh1Lo
    · exact hhi
  have hLocPrev14 := hCoreLocal coreHPrev (chainLevelOrdAbs ch (idx - 1)) tokPrev1 s6.mem s14.mem
    (fun a ha => by
      have hlt1 := hFootPrev1Lt a ha
      have hneUC : a < updCountBase + idx ∨ updCountBase + d ≤ a := by
        rcases hResp6.2.2.2.2 a ha with h0 | ⟨hlo, _⟩
        · by_contra h; exact (hFootLMUC (a - updCountBase) (by omega) (by omega)).2.2 (by simpa [show updCountBase + (a - updCountBase) = a by omega] using h0)
        · exact Or.inr (by omega)
      have hneHB : a < handleBase + idx ∨ handleBase + d < a := by
        rcases hResp6.2.2.2.2 a ha with h0 | ⟨hlo, _⟩
        · by_contra h; exact (hFootHB (a - handleBase) (by omega) (by omega)).1 (by simpa [show handleBase + (a - handleBase) = a by omega] using h0)
        · exact Or.inr (by omega)
      have hneBB : a < branchBase + idx ∨ branchBase + d < a := by
        rcases hResp6.2.2.2.2 a ha with h0 | ⟨hlo, _⟩
        · by_contra h; exact (hFootHB (a - branchBase) (by omega) (by omega)).2 (by simpa [show branchBase + (a - branchBase) = a by omega] using h0)
        · exact Or.inr (by omega)
      have hneLM : (a < levelMeta + (idx + 1) ∨ levelMeta + d ≤ a) ∧
          (a < levelMeta + d + (idx + 1) ∨ levelMeta + 2 * d ≤ a) := by
        rcases hResp6.2.2.2.2 a ha with h0 | ⟨hlo, _⟩
        · refine ⟨?_, ?_⟩
          · by_contra h; exact (hFootLMUC (a - levelMeta) (by omega) (by omega)).1 (by simpa [show levelMeta + (a - levelMeta) = a by omega] using h0)
          · by_contra h; exact (hFootLMUC (a - (levelMeta + d)) (by omega) (by omega)).2.1 (by simpa [show levelMeta + cfg.P.d + (a - (levelMeta + d)) = a by omega] using h0)
        · exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
      have hneRC : a ≠ rebuildCountBase + idx := by
        rcases hResp6.2.2.2.2 a ha with h0 | ⟨hlo, _⟩
        · intro h; exact hFootRC (h ▸ h0)
        · omega
      exact ((hUCFr13 a hneUC).trans ((hs12_frame a hlt1 hneHB hneBB hneLM).trans (hs10_eq7 a hneRC))).symm)
  have hHandle14 (j : ℕ) (hj : j ≤ d) : s14.mem (handleBase + j) = s12.mem (handleBase + j) :=
    hUCFr13 _ (by rcases hUCHB with h | h <;> omega)
  have hBranch14 (j : ℕ) (hj : j ≤ d) : s14.mem (branchBase + j) = s12.mem (branchBase + j) :=
    hUCFr13 _ (by rcases hUCBB with h | h <;> omega)
  have hMeta14 (j : ℕ) (hj : j < 2 * d) : s14.mem (levelMeta + j) = s12.mem (levelMeta + j) :=
    hUCFr13 _ (by rcases hUCLM with h | h <;> omega)
  have hPhi14_sum :
      (Finset.Ico idx d).sum (fun j => Rcore.phi (s14.mem (handleBase + j)) (coreTok12 j) s14.mem) =
      (Finset.Ico idx d).sum (fun j => Rcore.phi (s12.mem (handleBase + j)) (coreTok12 j) s12.mem) :=
    Finset.sum_congr rfl (fun j hj => by
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      rw [hHandle14 j (le_of_lt hj2)]
      exact (hCoreLocal _ (chainLevelOrdAbs next j) (coreTok12 j) s12.mem s14.mem
        (fun a ha => (hs14_eq12_ge a ((hCores12 j hj1 hj2).2.2.2.2 a ha).1).symm)).2.symm)
  have hPrepCost := hOps.interiorPrepCostDom idx curBatchWords
    (ordRotWords (chainLevelOrdAbs ch (idx - 1)) (ch.bran (idx - 1))) (ch.lvlM (idx - 1)) ch.N₀
    hIdxPos hIdxLt
  refine ⟨s14, _, vcLast, ecLast, termTok, tokPrev1, coreTok12, rAll,
    by rw [hs14_r4]; exact hh1Lo.trans hs12_lo, by rw [hs14_r4]; omega,
    fun a ha => by rw [hs14_r4] at ha; exact (hs14_eq12_ge a (hs12_lo.trans ha)).trans (hz12 a ha),
    by simp [s14], by simp [s14, hs13_regs 96 (by decide), s12a, hs12_ge70 96 (by decide), hr96],
    fun r hr hne => by
      simp only [s14, Function.update_of_ne hne]
      rw [hs13_regs r (by omega)]; simp [s12a, Function.update_of_ne (by omega : r ≠ 20), hs12_ge70 r hr],
    hPrevAbsEq.symm ▸ hLocPrev14.1 hRep6,
    fun a ha => by
      rcases hResp6.2.2.2.2 a ha with h0 | ⟨hlo, hhi⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hlo, hs14_r4.symm ▸ hhi.trans_le hs12_lo⟩,
    fun j hj1 hj2 => by
      rw [hBranch14 j (le_of_lt hj2), hHandle14 j (le_of_lt hj2), hs14_r4]
      obtain ⟨hBr, hHLo, hHHi, hRepJ, hFootJ⟩ := hCores12 j hj1 hj2
      have hlocJ := hCoreLocal _ (chainLevelOrdAbs next j) (coreTok12 j) s12.mem s14.mem
        (fun a ha => (hs14_eq12_ge a (hFootJ a ha).1).symm)
      exact ⟨hBr, hh1Lo.trans hHLo, hHHi, hlocJ.1 hRepJ,
        fun a ha => by have hF := hFootJ a ha; exact ⟨hh1Lo.trans hF.1, hF.2, fun hf => by have := hFootPrev1Lt a hf; omega⟩⟩,
    fun j₁ j₂ h1' h2' h3' h4' hne a ha1 ha2 => by
      rw [hHandle14 j₁ (le_of_lt h2')] at ha1; rw [hHandle14 j₂ (le_of_lt h4')] at ha2
      exact hCoreDisj12 j₁ j₂ h1' h2' h3' h4' hne a ha1 ha2,
    by rw [hExGIdx]
       exact dynGraphAt_of_agree hDGCur (fun a ha1 ha2 =>
         (hUCFr13 a (by rcases (hDisjG a ha1 ha2).2.2.2.2.2.2.2.2.1 with h | h <;> omega)).trans
           ((hs12_frame a (by omega)
             (by rcases (hDisjG a ha1 ha2).2.2.2.1 with h | h <;> omega)
             (by rcases (hDisjG a ha1 ha2).2.2.2.2.1 with h | h <;> omega)
             (by rcases (hDisjG a ha1 ha2).2.2.2.2.2.2.1 with h | h <;> [exact ⟨Or.inl (by omega), Or.inl (by omega)⟩; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩])).trans
             ((hs10_eq7 a (by rcases (hDisjG a ha1 ha2).2.2.2.2.2.2.2.1 with h | h <;> omega)).trans
               (hResp6.2.2.2.1 a (by omega) (hDisjG a ha1 ha2).1)))),
    by rw [hExGIdx]
       have hL14 : EdgeValuesAt s14.mem lPtr 4 L P curG.E ℓi :=
         hLenAt.congr (fun e he t ht => by
           have heL : e * L + L ≤ ecIdx * L := by
             simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt (hDGCur.2.2.1 e he))
           exact (hUCFr13 _ (by rcases (hDisjL (lPtr + e * L + t) (by omega) (by omega)).2.2.2.2.2 with h | h <;> omega)).trans
             ((hs12_frame _ (by omega)
               (by rcases (hDisjL (lPtr + e * L + t) (by omega) (by omega)).2.1 with h | h <;> omega)
               (by rcases (hDisjL (lPtr + e * L + t) (by omega) (by omega)).2.2.1 with h | h <;> omega)
               (by rcases (hDisjL (lPtr + e * L + t) (by omega) (by omega)).2.2.2.1 with h | h <;> [exact ⟨Or.inl (by omega), Or.inl (by omega)⟩; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩])).trans
               ((hs10_eq7 _ (by rcases (hDisjL (lPtr + e * L + t) (by omega) (by omega)).2.2.2.2.1 with h | h <;> omega)).trans
                 (hs7_eq_st _ (by omega) (hDisjL (lPtr + e * L + t) (by omega) (by omega)).1
                   (by by_contra h; rcases (hDisjG (lPtr + e * L + t) (by omega) (by omega)).2.2.2.2.2.2.2.2.2 with h' | h' <;> omega)))))
       exact fun e he => ⟨(hL14 e he).1, (hL14 e he).2.trans (hLenIEq e he)⟩,
    fun j hj1 hj2 => by
      obtain ⟨vc, ec, hDG, hGLo, hGHi, hLen, hLLo, hLHi, hDisjC, hDisjTL, hDisjTG⟩ := hMeta12 j hj1 hj2
      have hML := hMeta14 j (by omega)
      have hMG : s14.mem (levelMeta + d + j) = s12.mem (levelMeta + d + j) := by
        simpa [Nat.add_assoc] using hMeta14 (d + j) (by omega)
      dsimp only [d] at hMG hGLo hLLo
      refine ⟨vc, ec, ?_, by rw [hMG]; exact hh1Lo.trans hGLo, by rw [hMG, hs14_r4]; exact hGHi,
        ?_, by rw [hML]; exact hh1Lo.trans hLLo, by rw [hML, hs14_r4]; exact hLHi, ?_, ?_⟩
      · rw [hMG]; exact dynGraphAt_of_agree hDG (fun a ha1 _ => hs14_eq12_ge a (le_trans hGLo ha1))
      · rw [hML]; exact (hPrec ▸ hLen).congr (fun e he t ht => hs14_eq12_ge _ (by omega))
      · intro a ha1 ha2; rw [hML] at ha1 ha2
        exact ⟨fun hf => by have := hFootPrev1Lt a hf; omega,
          fun r hr1 hr2 => by rw [hHandle14 r (le_of_lt hr2)]; exact (hDisjC r hr1 hr2).1 a ha1 ha2,
          by rw [hHandle14 d le_rfl]; exact hPrec ▸ hDisjTL a ha1 ha2⟩
      · intro a ha1 ha2; rw [hMG] at ha1 ha2
        exact ⟨fun hf => by have := hFootPrev1Lt a hf; omega,
          fun r hr1 hr2 => by rw [hHandle14 r (le_of_lt hr2)]; exact (hDisjC r hr1 hr2).2 a ha1 ha2,
          by rw [hHandle14 d le_rfl]; exact hPrec ▸ hDisjTG a ha1 ha2⟩,
    by rw [hBranch14 d le_rfl]; exact hTermB12,
    by rw [hHandle14 d le_rfl]; exact hh1Lo.trans hTermHLo12,
    by rw [hHandle14 d le_rfl]
       exact (LastLevelProgram.lastLevelRepresentation_local vcLast ecLast 4 L P (next.G d).E
         _ (next.lastK, next.lastLSFs) termTok s12.mem s14.mem
         (fun a ha => (hs14_eq12_ge a (hTermFoot12 a (hPrec.symm ▸ ha)).1).symm)).1 (hPrec ▸ hTermRep12),
    fun a ha => by
      rw [hHandle14 d le_rfl] at ha
      have hF := hTermFoot12 a (hPrec.symm ▸ ha)
      refine ⟨hh1Lo.trans hF.1, hs14_r4.symm ▸ hF.2, fun hf => by have := hFootPrev1Lt a hf; omega,
        fun r hr1 hr2 => by rw [hHandle14 r (le_of_lt hr2)]; exact hTermDisj12 r hr1 hr2 a (hPrec.symm ▸ ha)⟩,
    by exact (hUCFr13 _ (by rcases hRCUC with h | h <;> omega)).trans
         ((hs12_frame _ (by omega) (by rcases hRCHB with h | h <;> omega) (by rcases hRCBB with h | h <;> omega)
           (by rcases hRCLM with h | h <;> [exact ⟨Or.inl (by omega), Or.inl (by omega)⟩; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩])).trans hs10_rc),
    fun j hj1 hj2 => hUCZero13 j hj1 hj2,
    fun a ha hnf hng hnrc hnh hnb hnm hnuc =>
      (hUCFr13 a hnuc).trans ((hs12_frame a (ha.trans_le hh1Lo) hnh hnb hnm).trans
        ((hs10_eq7 a hnrc).trans (hs7_eq_st a ha hnf hng))),
    ?_⟩
  rw [hPhi14_sum, hLocPrev14.2.symm]
  rw [hLocPrev2.2.symm] at hc6
  dsimp only [dgApplyBatchContract] at hcDG
  simp only [Expr.size]
  dsimp only [d, next, stLG] at hcReb hcZero hc6 hPrepCost ⊢
  clear rAll rSetup rTail rReb rZero r6 r2 hCores12 hMeta12 hTermRep12 hModelLevel
  omega

end MinCostFlow.MinRatio
