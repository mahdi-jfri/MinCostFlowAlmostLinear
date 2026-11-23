module

public import MinCostFlow.MinRatio.WireChainCoreOps
public import MinCostFlow.MinRatio.WireChainCoreLens
import MinCostFlow.MinRatio.WireRebuildSuffixLoopKBase
import MinCostFlow.SparseCore.Program.AssemblyReemb
import WordRAM.Tactic

/-!
# Branch B non-rebuild level-update step (`WireChainCoreBranchBStep`)

Provides `wireBranchBNoRebuildStep` and `wireBranchBNoRebuildStep_runs` for one non-rebuild
iteration of `Chain.Ordered.updateLoop` at `idx = reg 96 < d`:
1. Loads `(handle, branch, levelGraphs[idx], levelLens[idx])` and runs op `0` (`ordCoreUpdateK`)
   under `ToolUpdateOrdEqOnE`.
2. Updates `levelGraphs[idx]` in place via `dgApplyBatch`.
3. Increments `updCount[idx]` by `curU.length`.
4. Loads the active branch's child batch and order edits into `regs 10..13` via
   `ordLoadBranchOutStmt`.
5. When `idx + 1 < d`, reads the updated LSF (op `2`) and updates `levelLens[idx + 1]` in place
   via `wireUpdateCoreLenFromBatchBody`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

@[expose] def wireBranchBCondLenStmt (readLSF updateCoreLenProc : ℕ) : Stmt :=
  .cond (.bin .lt (.bin .add (.reg 96) (.const 1)) (.reg 75))
    (ordCoreReadLSFStmt readLSF ;;
     .assign 18 (.load (.bin .add (.reg 4) (.const 3))) ;;
     .assign 19 (.load (.bin .add (.reg 4) (.const 4))) ;;
     .assign 20 (.load (.bin .add (.reg 83) (.bin .add (.reg 96) (.const 1)))) ;;
     .call 4 updateCoreLenProc [.reg 10, .reg 18, .reg 7, .reg 20, .reg 94, .reg 19, .reg 5])
    .nop

/-- Execute one non-rebuild iteration of `Chain.Ordered.updateLoop` at `idx = reg 96 < d`. -/
@[expose] def wireBranchBNoRebuildStep
    (updCore readLSF dgApply updateCoreLenProc : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 77) (.reg 96))) ;;
  .assign 2 (.load (.bin .add (.reg 78) (.reg 96))) ;;
  .assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 96))) ;;
  .assign 7 (.load (.bin .add (.reg 83) (.reg 96))) ;;
  .assign 8 (.reg 7) ;;
  ordCoreUpdateStmt updCore ;;
  .call 15 dgApply [.reg 6, .reg 10, .const 1] ;;
  .assign 16 (.load (.reg 10)) ;;
  .assign 17 (.bin .add (.reg 85) (.reg 96)) ;;
  .store (.reg 17) (.bin .add (.load (.reg 17)) (.reg 16)) ;;
  ordLoadBranchOutStmt ;;
  .assign 4 (.reg 5) ;;
  wireBranchBCondLenStmt readLSF updateCoreLenProc

theorem wireBranchBNoRebuildStep_noRand (updCore readLSF dgApply updateCoreLenProc : ℕ) :
    (wireBranchBNoRebuildStep updCore readLSF dgApply updateCoreLenProc).NoRand := by
  simp [wireBranchBNoRebuildStep, wireBranchBCondLenStmt, ordCoreUpdateStmt, ordLoadBranchOutStmt,
    ordCoreReadLSFStmt, Stmt.NoRand]

set_option maxHeartbeats 800000 in
/-- Execute `wireBranchBNoRebuildStep` at `idx < d`, updating `coreTok idx`, `levelGraphs[idx]`,
`updCount[idx]`, `regs 10..13` (next batch and order edits), and (when `idx + 1 < d`)
`levelLens[idx + 1]`. -/
theorem wireBranchBNoRebuildStep_runs
    {w L P m capExp lastMul intCapMax forestEdgeCap drainUnit
      dgCap ecCap lastSpace termUpdSpace termUpdCost
      initCore dgApply updateCoreLenProc edgeProc signExt mul intDiv copy
      idx coreH gPtr lPtr nextLPtr curBatch curBatchWords curEdits curEditsWords curHeap
      handleBase branchBase levelMeta updCountBase vcIdx ecIdx ecNext : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {levelSpace levelCost updStepSpace updStepCost : ℕ → ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opCore : ℕ → ℕ}
    {ω : ℕ → Bool} {st : State}
    (ch : ChainState cfg.T cfg.P) (curU : List Update) (curEditsList : List OrdEdit)
    (oldOrd : ℕ → List End) (ℓi gi oldNextℓ : ℕ → ℝ) (coreTok0 : Rcore.τ)
    (hCoreLocal : Rcore.Local)
    (hFour : fmt.limbBits = 4) (hPrec : fmt.precision = P) (hw16 : 16 ≤ 2 ^ w)
    (hIdxLt : idx < cfg.P.d) (hdW : cfg.P.d < 2 ^ w) (hkW : cfg.P.k < 2 ^ w)
    (hUpdOrdEq : ToolUpdateOrdEqOnE cfg.T)
    (hCoreImpl : Rcore.Implements w p initCore opCore
      (sparseCoreOrdMachineContractK fmt L cfg.T (ch.G idx) cfg.P.k (ch.lvlM idx) ch.N₀
        vcIdx ecIdx capExp Psc (allocation idx)))
    (hDGApply : MeetsContract w p dgApply
      (dgApplyBatchContract w vcIdx ecIdx (ch.G idx) (ch.G idx) curU curBatchWords))
    (hUpdLenProc : p.procs[updateCoreLenProc]? = some (wireUpdateCoreLenFromBatchBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hOps : UpdateCoreOpsHyp (w := w) (L := L) (P := P) (m := m) (capExp := capExp)
      (lastMul := lastMul) (intCapMax := intCapMax) (forestEdgeCap := forestEdgeCap)
      (drainUnit := drainUnit) (coreSpace := coreSpace) (coreFixed := coreFixed)
      (toolMul := toolMul) (fmt := fmt) (cfg := cfg) (Psc := Psc)
      (allocation := allocation) (lastAlloc := lastAlloc)
      Rcore dgCap ecCap levelSpace levelCost updStepSpace updStepCost lastSpace termUpdSpace
      termUpdCost)
    (hRegs :
      st.regs 4 = curHeap ∧ st.regs 10 = curBatch ∧ st.regs 11 = curBatchWords ∧
      st.regs 12 = curEdits ∧ st.regs 13 = curEditsWords ∧
      st.regs 75 = cfg.P.d ∧ st.regs 77 = handleBase ∧ st.regs 78 = branchBase ∧
      st.regs 83 = levelMeta ∧ st.regs 85 = updCountBase ∧ st.regs 94 = L ∧ st.regs 96 = idx)
    (hHCell : st.mem (handleBase + idx) = coreH)
    (hBCell : st.mem (branchBase + idx) = ch.bran idx)
    (hBrLt : ch.bran idx < cfg.P.k)
    (hGCell : st.mem (levelMeta + cfg.P.d + idx) = gPtr)
    (hLCell : st.mem (levelMeta + idx) = lPtr)
    (hNLCell : idx + 1 < cfg.P.d → st.mem (levelMeta + (idx + 1)) = nextLPtr)
    (hUCCell : st.mem (updCountBase + idx) = ch.updCount idx)
    (hUCW : ch.updCount idx + curU.length < 2 ^ w)
    (hCoreH_W : coreH < 2 ^ w)
    (hRep : Rcore.rep coreH ⟨ch.scState idx, ch.G idx, oldOrd, ch.updCount idx⟩ coreTok0 st.mem)
    (hIn : SparseCoreOrdInput cfg.T cfg.P.k (ch.lvlM idx) ch.N₀ (ch.scState idx)
      (ch.G idx) oldOrd (ch.updCount idx))
    (hFoot : ∀ a, Rcore.foot coreH coreTok0 a → a < curHeap)
    (hGAt : DynGraphAt st.mem gPtr vcIdx ecIdx (ch.G idx))
    (hSmall : SmallBatchAt st.mem curBatch (ch.G idx) curU curBatchWords)
    (hDecode : (decodeBatch st.mem curBatch (ch.G idx)).1 = curU)
    (hBatchValid : (ch.G idx).BatchIsValid curU)
    (hBatchCaps : BatchWithinCaps vcIdx ecIdx curU)
    (hBatchW : ∀ j < curBatchWords, st.mem (curBatch + j) < 2 ^ w)
    (hEditsAt : OrdEditsAt st.mem curEdits curEditsList curEditsWords)
    (hEditsW : ∀ j < curEditsWords, st.mem (curEdits + j) < 2 ^ w)
    (hNewOrdEq :
      applyOrdEdits oldOrd curEditsList =
        chainLevelOrd cfg.T (fun j => if j = idx then (ch.G idx).applyBatch curU else ch.G j)
          ch.scState ch.bran idx)
    (hOrdBatch : OrderedBatch (ch.G idx) curU oldOrd (applyOrdEdits oldOrd curEditsList))
    (hUpdThresh : ((ch.updCount idx + curU.length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold cfg.P.k (ch.lvlM idx) ch.N₀)
    (hLenAt : EdgeValuesAt st.mem lPtr 4 L P ((ch.G idx).applyBatch curU).E ℓi)
    (hLenCap : ∀ e ∈ ((ch.G idx).applyBatch curU).E, e < ecIdx)
    (hLenPos : ∀ e ∈ ((ch.G idx).applyBatch curU).E, 0 < ℓi e)
    (hNextInv : idx + 1 < cfg.P.d →
      let curG := (ch.G idx).applyBatch curU
      let newOrd := chainLevelOrd cfg.T (fun j => if j = idx then curG else ch.G j)
        ch.scState ch.bran idx
      let upd := cfg.T.updateOrd (ch.scState idx) curU ℓi gi newOrd
      let sc' := upd.1
      let nextU := upd.2 (ch.bran idx)
      let nextG := cfg.T.S sc' (ch.bran idx)
      ch.G (idx + 1) = cfg.T.S (ch.scState idx) (ch.bran idx) ∧
      nextG = (ch.G (idx + 1)).applyBatch nextU ∧
      EdgeValuesAt st.mem nextLPtr 4 L P (ch.G (idx + 1)).E oldNextℓ ∧
      (∀ e ∈ (ch.G (idx + 1)).E, e < ecNext) ∧
      (∀ u ∈ nextU, match u with
        | .insert e _ _ => e ∈ curG.E ∧ e < ecIdx ∧ e < ecNext ∧
            ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P =
              coreLen (cfg.T.lsfs sc' (ch.bran idx)) ℓi e
        | _ => True) ∧
      (∀ e ∈ nextG.E, (∀ u ∈ nextU, ¬ Update.Inserts e u) →
        e ∈ (ch.G (idx + 1)).E ∧
        coreLen (cfg.T.lsfs sc' (ch.bran idx)) ℓi e = oldNextℓ e))
    (hBelow :
      handleBase + idx < curHeap ∧ branchBase + idx < curHeap ∧
      levelMeta + cfg.P.d + idx < curHeap ∧ updCountBase + idx < curHeap ∧
      gPtr + dynGraphSize vcIdx ecIdx ≤ curHeap ∧ lPtr + ecIdx * L ≤ curHeap ∧
      curBatch + curBatchWords ≤ curHeap ∧ curEdits + curEditsWords ≤ curHeap ∧
      (idx + 1 < cfg.P.d → nextLPtr + ecNext * L ≤ curHeap))
    (hDisj :
      (∀ a, gPtr ≤ a → a < gPtr + dynGraphSize vcIdx ecIdx →
        ¬ Rcore.foot coreH coreTok0 a ∧ a ≠ updCountBase + idx ∧
        (a < curBatch ∨ curBatch + curBatchWords ≤ a) ∧
        (a < lPtr ∨ lPtr + ecIdx * L ≤ a) ∧
        (idx + 1 < cfg.P.d → a < nextLPtr ∨ nextLPtr + ecNext * L ≤ a)) ∧
      ¬ Rcore.foot coreH coreTok0 (updCountBase + idx) ∧
      (updCountBase + idx < curBatch ∨ curBatch + curBatchWords ≤ updCountBase + idx) ∧
      (updCountBase + idx < lPtr ∨ lPtr + ecIdx * L ≤ updCountBase + idx) ∧
      (idx + 1 < cfg.P.d →
        (updCountBase + idx < nextLPtr ∨ nextLPtr + ecNext * L ≤ updCountBase + idx) ∧
        (lPtr + ecIdx * L ≤ nextLPtr ∨ nextLPtr + ecNext * L ≤ lPtr) ∧
        (∀ a, nextLPtr ≤ a → a < nextLPtr + ecNext * L → ¬ Rcore.foot coreH coreTok0 a) ∧
        ¬ Rcore.foot coreH coreTok0 (levelMeta + (idx + 1)) ∧
        (levelMeta + (idx + 1) < gPtr ∨ gPtr + dynGraphSize vcIdx ecIdx ≤ levelMeta + (idx + 1)) ∧
        levelMeta + (idx + 1) ≠ updCountBase + idx) ∧
      (∀ a, lPtr ≤ a → a < lPtr + ecIdx * L → ¬ Rcore.foot coreH coreTok0 a) ∧
      (∀ t < curBatchWords, ¬ Rcore.foot coreH coreTok0 (curBatch + t)))
    (hz : ZeroFrom st.mem curHeap)
    (hRoom : curHeap + updStepSpace idx < 2 ^ w) :
    let curG := (ch.G idx).applyBatch curU
    let newOrd := chainLevelOrd cfg.T (fun j => if j = idx then curG else ch.G j)
      ch.scState ch.bran idx
    let upd := cfg.T.updateOrd (ch.scState idx) curU ℓi gi newOrd
    let sc' := upd.1
    let nextU := upd.2 (ch.bran idx)
    let aNext : SparseCoreOrdAbs cfg.T := ⟨sc', curG, newOrd, ch.updCount idx + curU.length⟩
    ∃ (out : State) (cost : ℕ) (coreTok' : Rcore.τ) (nextEdits : List OrdEdit),
      Runs w p ω (wireBranchBNoRebuildStep (opCore 0) (opCore 2) dgApply updateCoreLenProc)
        st .normal out cost ∧
      curHeap ≤ out.regs 4 ∧ out.regs 4 ≤ curHeap + updStepSpace idx ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      Rcore.rep coreH aNext coreTok' out.mem ∧
      SparseCoreOrdInput cfg.T cfg.P.k (ch.lvlM idx) ch.N₀ sc' curG newOrd
        (ch.updCount idx + curU.length) ∧
      (∀ a, Rcore.foot coreH coreTok' a →
        Rcore.foot coreH coreTok0 a ∨ (curHeap ≤ a ∧ a < out.regs 4)) ∧
      DynGraphAt out.mem gPtr vcIdx ecIdx curG ∧
      out.mem (updCountBase + idx) = ch.updCount idx + curU.length ∧
      SmallBatchAt out.mem (out.regs 10) (cfg.T.S (ch.scState idx) (ch.bran idx)) nextU (out.regs 11) ∧
      (decodeBatch out.mem (out.regs 10) (cfg.T.S (ch.scState idx) (ch.bran idx))).1 = nextU ∧
      OrdEditsAt out.mem (out.regs 12) nextEdits (out.regs 13) ∧
      applyOrdEdits (cfg.T.rot (ch.scState idx) (ch.bran idx)) nextEdits =
        cfg.T.rot sc' (ch.bran idx) ∧
      curHeap ≤ out.regs 10 ∧ out.regs 10 + out.regs 11 ≤ out.regs 4 ∧
      curHeap ≤ out.regs 12 ∧ out.regs 12 + out.regs 13 ≤ out.regs 4 ∧
      (∀ t < out.regs 11, out.mem (out.regs 10 + t) < 2 ^ w ∧
        ¬ Rcore.foot coreH coreTok' (out.regs 10 + t)) ∧
      (∀ t < out.regs 13, out.mem (out.regs 12 + t) < 2 ^ w ∧
        ¬ Rcore.foot coreH coreTok' (out.regs 12 + t)) ∧
      (idx + 1 < cfg.P.d →
        EdgeValuesAt out.mem nextLPtr 4 L P ((ch.G (idx + 1)).applyBatch nextU).E
          (coreLen (cfg.T.lsfs sc' (ch.bran idx)) ℓi)) ∧
      (∀ a < curHeap,
        ¬ Rcore.foot coreH coreTok0 a →
        (a < gPtr ∨ gPtr + dynGraphSize vcIdx ecIdx ≤ a) →
        a ≠ updCountBase + idx →
        (idx + 1 < cfg.P.d → a < nextLPtr ∨ nextLPtr + ecNext * L ≤ a) →
        out.mem a = st.mem a) ∧
      cost + Rcore.phi coreH coreTok' out.mem ≤
        Psc.mul * (cfg.T.cost sc' - cfg.T.cost (ch.scState idx)) + updStepCost idx +
          Rcore.phi coreH coreTok0 st.mem := by
  dsimp only
  set d := cfg.P.d
  set curG := (ch.G idx).applyBatch curU
  set newOrd := chainLevelOrd cfg.T (fun j => if j = idx then curG else ch.G j) ch.scState ch.bran idx
  set upd := cfg.T.updateOrd (ch.scState idx) curU ℓi gi newOrd
  set sc' := upd.1
  set nextU := upd.2 (ch.bran idx)
  set aNext : SparseCoreOrdAbs cfg.T := ⟨sc', curG, newOrd, ch.updCount idx + curU.length⟩
  obtain ⟨hr4, hr10, hr11, hr12, hr13, hr75, hr77, hr78, hr83, hr85, hr94, hr96⟩ := hRegs
  obtain ⟨hHBLt, hBBLt, hLMLt, hUCLt, hGLe, hLLe, hBLe, hELe, hNLLe⟩ := hBelow
  obtain ⟨hDisjG, hUCFoot, hUCB, hUCL, hDisjNext, hDisjL, hDisjB⟩ := hDisj
  have hStepSp := hOps.updStepSpaceDom idx coreH gPtr curBatch curBatchWords curEdits curEditsWords
    lPtr curHeap nextU.length (ch.lvlM idx) ch.N₀ hIdxLt
  have hStepCost := hOps.updStepCostDom idx curBatchWords curEditsWords nextU.length
    (ch.lvlM idx) ch.N₀ hIdxLt
  dsimp only at hStepSp hStepCost
  -- Step 1: load regs `3, 2, 6, 7, 8`
  let s1 := { st with regs := Function.update st.regs 3 coreH }
  let s2 := { s1 with regs := Function.update s1.regs 2 (ch.bran idx) }
  let s3 := { s2 with regs := Function.update s2.regs 6 gPtr }
  let s4 := { s3 with regs := Function.update s3.regs 7 lPtr }
  let s5 := { s4 with regs := Function.update s4.regs 8 lPtr }
  have r1 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 77) (.reg 96)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨coreH, by simp [Expr.eval, BinOp.eval, hr77, hr96, show handleBase + idx < 2 ^ w by omega, hHCell], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 78) (.reg 96)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨ch.bran idx, by simp [Expr.eval, BinOp.eval, s1, hr78, hr96, show branchBase + idx < 2 ^ w by omega, hBCell], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 96)))) s2 .normal s3 7 :=
    runs_assign_iff.mpr ⟨gPtr, by simp [Expr.eval, BinOp.eval, s2, s1, hr83, hr75, hr96,
      show levelMeta + d < 2 ^ w by omega, show levelMeta + d + idx < 2 ^ w by omega, hGCell], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 83) (.reg 96)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨lPtr, by simp [Expr.eval, BinOp.eval, s3, s2, s1, hr83, hr96,
      show levelMeta + idx < 2 ^ w by omega, hLCell], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 8 (.reg 7)) s4 .normal s5 2 :=
    runs_assign_iff.mpr ⟨lPtr, by simp [Expr.eval, s4], rfl, rfl, rfl⟩
  -- Step 2: op `0` (`ordCoreUpdateK_runs`)
  set aPrev : SparseCoreOrdAbs cfg.T := ⟨ch.scState idx, ch.G idx, oldOrd, ch.updCount idx⟩
  let updArgs := [coreH, gPtr, curBatch, curBatchWords, curEdits, curEditsWords, lPtr, lPtr, curHeap]
  have hReadBatch : ordUpdateBatch aPrev updArgs s5.mem = curU := by
    unfold ordUpdateBatch
    simp only [updArgs, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, aPrev]
    exact hDecode
  have hReadEdits : readOrdEdits s5.mem curEdits = curEditsList := hEditsAt.1
  have hUpdOrdEq' : ordUpdateOrder aPrev updArgs s5.mem = newOrd := by
    unfold ordUpdateOrder
    simp only [updArgs, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, aPrev, hReadEdits]
    exact hNewOrdEq
  have hUpdModelEq : ordUpdateModel fmt L aPrev updArgs s5.mem = upd := by
    unfold ordUpdateModel
    rw [hReadBatch, hUpdOrdEq']
    exact hUpdOrdEq (ch.scState idx) curU _ ℓi _ gi newOrd
  have hANextEq : ordUpdateNext fmt L aPrev updArgs s5.mem = aNext := by
    unfold ordUpdateNext
    rw [hUpdModelEq, hReadBatch, hUpdOrdEq']
  have hPre0 : SparseCoreOrdUpdateAt fmt L cfg.T cfg.P.k (ch.lvlM idx) ch.N₀ vcIdx ecIdx
      aPrev updArgs s5.mem := by
    refine ⟨coreH, gPtr, curBatch, curBatchWords, curEdits, curEditsWords, lPtr, lPtr, curHeap, rfl,
      hIn, hGAt, ?_, ?_, ?_, ?_, ?_, ?_, hBatchW, hEditsW, hGLe, hBLe, hELe, hLLe, hLLe, ?_, ?_⟩
    · rw [hReadBatch]; exact hSmall
    · rw [hReadBatch]; exact hBatchValid
    · rw [hReadBatch]; exact hBatchCaps
    · rw [hReadEdits]; exact hEditsAt
    · rw [hReadBatch, hUpdOrdEq', ← hNewOrdEq]; exact hOrdBatch
    · rw [hReadBatch]; exact hUpdThresh
    · intro e he
      rw [hReadBatch] at he
      exact ⟨hLenCap e he, hFour.symm ▸ (hLenAt e he).1, hFour.symm ▸ (hLenAt e he).1⟩
    · intro e he
      rw [hReadBatch] at he ⊢
      have hv := (hLenAt e he).2
      simp only [readEdgeValues, he, ↓reduceIte, hFour, hPrec]
      rw [hv]; exact hLenPos e he
  obtain ⟨s6, h1, cUpd, tok1, r6, hs6_5, hRep6, hIn6, hBO6, hResp6, hc6, hs6_regs⟩ :=
    ordCoreUpdateK_runs (w := w) (L := L) (k := cfg.P.k) (M := ch.lvlM idx) (N := ch.N₀)
      (vCap := vcIdx) (eCap := ecIdx) (capExp := capExp) (init := initCore)
      (handle := coreH) (graph := gPtr) (batch := curBatch) (words := curBatchWords)
      (edits := curEdits) (editWords := curEditsWords) (lengths := lPtr) (gradient := lPtr)
      (heap := curHeap) (st := s5) (ω := ω) hCoreImpl
      (by simp [s5, s4, s3, s2, s1]) (by simp [s5, s4, s3]) (by simp [s5, s4, s3, s2, s1, hr10])
      (by simp [s5, s4, s3, s2, s1, hr11]) (by simp [s5, s4, s3, s2, s1, hr12])
      (by simp [s5, s4, s3, s2, s1, hr13]) (by simp [s5, s4]) (by simp [s5])
      (by simp [s5, s4, s3, s2, s1, hr4])
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      hRep hPre0 hFoot hz (by omega)
  rw [hANextEq] at hRep6 hIn6 hc6
  have hBatchesEq : (ordUpdateModel fmt L aPrev updArgs s5.mem).2 = upd.2 :=
    congrArg Prod.snd hUpdModelEq
  rw [hBatchesEq] at hBO6
  have hh1Lo : curHeap ≤ h1 := hResp6.1
  have hh1Hi : h1 ≤ curHeap + allocation idx 0 updArgs := hResp6.2.1
  have hFoot1 (a : ℕ) (ha : Rcore.foot coreH tok1 a) :
      Rcore.foot coreH coreTok0 a ∨ (curHeap ≤ a ∧ a < h1) := hResp6.2.2.2.2 a ha
  -- Step 3: `dgApplyBatch` on `levelGraphs[idx]` (`gPtr`)
  have hGAt6 : DynGraphAt s6.mem gPtr vcIdx ecIdx (ch.G idx) :=
    dynGraphAt_of_agree hGAt (fun a ha1 ha2 =>
      hResp6.2.2.2.1 a (by omega) (hDisjG a ha1 ha2).1)
  have hSmall6 : SmallBatchAt s6.mem curBatch (ch.G idx) curU curBatchWords :=
    smallBatchAt_of_agree hSmall (fun a ha1 ha2 =>
      hResp6.2.2.2.1 a (by omega) (by simpa [show curBatch + (a - curBatch) = a by omega] using hDisjB (a - curBatch) (by omega)))
  have hBatchW6 : ∀ t < curBatchWords, s6.mem (curBatch + t) < 2 ^ w := fun t ht => by
    rw [hResp6.2.2.2.1 (curBatch + t) (by omega) (hDisjB t ht)]; exact hBatchW t ht
  obtain ⟨bodyDG, hBodyDG, oDG, outDG, cDG, rDGBody, hPostDG, hcDG⟩ :=
    hDGApply [gPtr, curBatch, 1] s6.mem s6.pos ω
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl <;> omega)
      ⟨gPtr, curBatch, 1, rfl, hw16, by omega, by omega,
        fun i hi => by
          by_contra h
          rcases (hDisjG (curBatch + i) (by omega) (by omega)).2.2.1 with h' | h' <;> omega,
        hBatchW6, hSmall6.1, hBatchValid, hBatchCaps, hGAt6, Or.inl ⟨by decide, rfl⟩⟩
  obtain ⟨_, _, _, hEqDG, _, hDGAfter, hDGFr⟩ := hPostDG
  simp only [List.cons.injEq, and_true] at hEqDG
  obtain ⟨rfl, rfl, rfl⟩ := hEqDG
  have hFold1 : curU.foldl (dgBatchTarget 1) (ch.G idx) = curG := by
    have hfun : dgBatchTarget 1 = MGraph.applyUpdate := by funext H u; simp [dgBatchTarget]
    rw [hfun]; rfl
  have hDGCur : DynGraphAt outDG.mem gPtr vcIdx ecIdx curG := hFold1 ▸ hDGAfter
  let s7 : State := { regs := Function.update s6.regs 15 oDG.value, mem := outDG.mem, pos := outDG.pos }
  have r7 : Runs w p ω (.call 15 dgApply [.reg 6, .reg 10, .const 1]) s6 .normal s7 (3 + cDG + 1) :=
    runs_call_iff.mpr ⟨[gPtr, curBatch, 1], bodyDG, oDG, outDG, cDG,
      by simp [evalArgs, Expr.eval, hs6_regs 6 (by decide), hs6_regs 10 (by decide),
        s5, s4, s3, s2, s1, hr10, show 1 < 2 ^ w by omega],
      hBodyDG, rDGBody, rfl, rfl, by simp [argsSize, Expr.size]⟩
  -- Step 4: increment `updCount[idx]` by `curU.length`
  have hCurLen7 : outDG.mem curBatch = curU.length := by
    have h1' := hSmall6.1.1
    have hne : curBatch < gPtr ∨ gPtr + dynGraphSize vcIdx ecIdx ≤ curBatch := by
      by_contra h
      rcases (hDisjG curBatch (by omega) (by omega)).2.2.1 with h' | h' <;> omega
    exact (hDGFr curBatch hne).trans hSmall6.1.2.1
  have hUC7 : s7.mem (updCountBase + idx) = ch.updCount idx := by
    have hne : updCountBase + idx < gPtr ∨ gPtr + dynGraphSize vcIdx ecIdx ≤ updCountBase + idx := by
      by_contra h
      exact (hDisjG _ (by omega) (by omega)).2.1 rfl
    exact (hDGFr _ hne).trans ((hResp6.2.2.2.1 _ hUCLt hUCFoot).trans hUCCell)
  let s8 := { s7 with regs := Function.update s7.regs 16 curU.length }
  let s9 := { s8 with regs := Function.update s8.regs 17 (updCountBase + idx) }
  let s10 := { s9 with mem := Function.update s9.mem (updCountBase + idx) (ch.updCount idx + curU.length) }
  have r8 : Runs w p ω (.assign 16 (.load (.reg 10))) s7 .normal s8 3 :=
    runs_assign_iff.mpr ⟨curU.length, by
      simp [Expr.eval, s7, hs6_regs 10 (by decide), s5, s4, s3, s2, s1, hr10, hCurLen7], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 17 (.bin .add (.reg 85) (.reg 96))) s8 .normal s9 4 :=
    runs_assign_iff.mpr ⟨updCountBase + idx, by
      simp [Expr.eval, BinOp.eval, s8, s7, hs6_regs 85 (by decide), hs6_regs 96 (by decide),
        s5, s4, s3, s2, s1, hr85, hr96, show updCountBase + idx < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.store (.reg 17) (.bin .add (.load (.reg 17)) (.reg 16))) s9 .normal s10 6 :=
    runs_store_iff.mpr ⟨updCountBase + idx, ch.updCount idx + curU.length,
      by simp [Expr.eval, s9],
      by simp [Expr.eval, BinOp.eval, s9, s8, hUC7, hUCW], rfl, rfl, rfl⟩
  -- Preserve `BranchOutAt`, `Rcore.rep` at `s10`
  have hs10_eq6_ge (a : ℕ) (ha : curHeap ≤ a) : s10.mem a = s6.mem a := by
    change Function.update outDG.mem (updCountBase + idx) _ a = s6.mem a
    rw [Function.update_of_ne (by omega), hDGFr a (Or.inr (by omega))]
  have hBO6' : BranchOutAt s6.mem curHeap cfg.P.k (cfg.T.S (ch.scState idx)) upd.2
      (cfg.T.rot (ch.scState idx)) (cfg.T.rot sc') := by
    rw [hANextEq] at hBO6; exact hBO6
  have hBO10 : BranchOutAt s10.mem curHeap cfg.P.k (cfg.T.S (ch.scState idx)) upd.2
      (cfg.T.rot (ch.scState idx)) (cfg.T.rot sc') := by
    refine ⟨(hs10_eq6_ge curHeap le_rfl).trans hBO6'.1, fun j hj => ?_⟩
    obtain ⟨hSB, eds, hEd, hAp⟩ := hBO6'.2 j hj
    obtain ⟨_, hbLo, _, heLo, _, _, _, _, _, _⟩ := hOps.op0Placement coreH tok1 s6.mem curHeap h1 cfg.P.k j
      _ _ _ _ hBO6' hj
    have h0 := hs10_eq6_ge (curHeap + 1 + 4 * j) (by omega)
    have h1' := hs10_eq6_ge (curHeap + 2 + 4 * j) (by omega)
    have h2' := hs10_eq6_ge (curHeap + 3 + 4 * j) (by omega)
    have h3' := hs10_eq6_ge (curHeap + 4 + 4 * j) (by omega)
    rw [h0, h1', h2', h3']
    refine ⟨smallBatchAt_of_agree hSB (fun a ha1 _ => hs10_eq6_ge a (hbLo.trans ha1)),
      eds, ordEditsAt_of_agree hEd (fun a ha1 _ => hs10_eq6_ge a (heLo.trans (by
        rwa [show curHeap + 3 + 4 * j = curHeap + 1 + 4 * j + 2 by omega] at ha1))), hAp⟩
  have hLoc10 := hCoreLocal coreH aNext tok1 s6.mem s10.mem (fun a ha => by
    rcases hFoot1 a ha with h0 | ⟨hlo, _⟩
    · have hne1 : a ≠ updCountBase + idx := fun h => hUCFoot (h ▸ h0)
      have hne2 : a < gPtr ∨ gPtr + dynGraphSize vcIdx ecIdx ≤ a := by
        by_contra h; exact (hDisjG a (by omega) (by omega)).1 h0
      change s6.mem a = Function.update outDG.mem (updCountBase + idx) _ a
      rw [Function.update_of_ne hne1, hDGFr a hne2]
    · exact (hs10_eq6_ge a hlo).symm)
  have hRep10 : Rcore.rep coreH aNext tok1 s10.mem := hLoc10.1 hRep6
  have hPhi10 : Rcore.phi coreH tok1 s10.mem = Rcore.phi coreH tok1 s6.mem := hLoc10.2.symm
  -- Step 5: `ordLoadBranchOutStmt ;; .assign 4 (.reg 5)`
  have hBOPlacement := hOps.op0Placement coreH tok1 s6.mem curHeap h1 cfg.P.k (ch.bran idx)
    (cfg.T.S (ch.scState idx)) upd.2 (cfg.T.rot (ch.scState idx)) (cfg.T.rot sc') hBO6' hBrLt
  dsimp only at hBOPlacement
  obtain ⟨hBOEnd, hbPLo, hbPHi, hePLo, hePHi, hbPW, hePW, hbPFoot, hePFoot, hNextDec6⟩ := hBOPlacement
  dsimp only [updArgs] at hh1Hi
  obtain ⟨s11, r11, hs11Mem, _, hNextSB11, ⟨nextEdits, hNextOE11, hNextRot11⟩, hs11_regs⟩ :=
    ordLoadBranchOut_runs (w := w) (branchOutAddr := curHeap) (k := cfg.P.k) (j := ch.bran idx)
      (p := p) (st := s10) (ω := ω)
      (by simp [s10, s9, s8, s7, hs6_regs 2 (by decide), s5, s4, s3, s2])
      (by simp [s10, s9, s8, s7, hs6_regs 4 (by decide), s5, s4, s3, s2, s1, hr4])
      hBrLt hBO10 (by omega) (by omega)
  let s12 := { s11 with regs := Function.update s11.regs 4 h1 }
  have r12 : Runs w p ω (.assign 4 (.reg 5)) s11 .normal s12 2 :=
    runs_assign_iff.mpr ⟨h1, by
      simp [Expr.eval, hs11_regs 5 (by decide) (by decide) (by decide) (by decide) (by decide),
        s10, s9, s8, s7, hs6_5], rfl, rfl, rfl⟩
  set boBase := curHeap + 1 + 4 * ch.bran idx
  obtain ⟨hs11_10', hs11_11', hs11_12', hs11_13'⟩ :=
    ordLoadBranchOut_regs_eq (branchOutAddr := curHeap) (j := ch.bran idx) r11
      (by simp [s10, s9, s8, s7, hs6_regs 2 (by decide), s5, s4, s3, s2])
      (by simp [s10, s9, s8, s7, hs6_regs 4 (by decide), s5, s4, s3, s2, s1, hr4])
      (by omega) (by omega)
  have hs11_10 : s11.regs 10 = s6.mem boBase := hs11_10'.trans (hs10_eq6_ge boBase (by omega))
  have hs11_11 : s11.regs 11 = s6.mem (boBase + 1) := hs11_11'.trans (hs10_eq6_ge (boBase + 1) (by omega))
  have hs11_12 : s11.regs 12 = s6.mem (boBase + 2) := hs11_12'.trans (hs10_eq6_ge (boBase + 2) (by omega))
  have hs11_13 : s11.regs 13 = s6.mem (boBase + 3) := hs11_13'.trans (hs10_eq6_ge (boBase + 3) (by omega))
  -- Step 6: conditional LSF readout + `wireUpdateCoreLenFromBatchBody` when `idx + 1 < d`
  have hs12_eq10 : s12.mem = s10.mem := hs11Mem
  have hs12_regs_keep (r : ℕ) (h4 : r ≠ 4) (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12)
      (h13 : r ≠ 13) (h14 : r ≠ 14) (h15 : r ≠ 15) (h16 : r ≠ 16) (h17 : r ≠ 17)
      (h5 : r ≠ 5) : s12.regs r = s5.regs r := by
    simp only [s12, Function.update_of_ne h4]
    rw [hs11_regs r h10 h11 h12 h13 h14]
    simp only [s10, s9, s8, s7, Function.update_of_ne h17, Function.update_of_ne h16,
      Function.update_of_ne h15]
    exact hs6_regs r h5
  have hCondOut :
      ∃ (sEnd : State) (cCond : ℕ) (tokEnd : Rcore.τ),
        Runs w p ω (wireBranchBCondLenStmt (opCore 2) updateCoreLenProc) s12 .normal sEnd cCond ∧
        h1 ≤ sEnd.regs 4 ∧ sEnd.regs 4 ≤ curHeap + updStepSpace idx ∧
        ZeroFrom sEnd.mem (sEnd.regs 4) ∧
        (∀ r, 70 ≤ r → sEnd.regs r = st.regs r) ∧
        (∀ r ∈ ([10, 11, 12, 13] : List ℕ), sEnd.regs r = s12.regs r) ∧
        Rcore.rep coreH aNext tokEnd sEnd.mem ∧
        (∀ a, Rcore.foot coreH tokEnd a →
          Rcore.foot coreH tok1 a ∨ (h1 ≤ a ∧ a < sEnd.regs 4)) ∧
        (idx + 1 < d →
          EdgeValuesAt sEnd.mem nextLPtr 4 L P ((ch.G (idx + 1)).applyBatch nextU).E
            (coreLen (cfg.T.lsfs sc' (ch.bran idx)) ℓi)) ∧
        (∀ a < h1, ¬ Rcore.foot coreH tok1 a →
          (idx + 1 < d → a < nextLPtr ∨ nextLPtr + ecNext * L ≤ a) →
          sEnd.mem a = s12.mem a) ∧
        cCond + Rcore.phi coreH tokEnd sEnd.mem ≤
          Psc.readout +
            nextU.length * (wireCoreLenEdgeCost (max L (L + (capExp + sparseCoreReadout2LimbConst) *
              (Nat.log 2 (ch.lvlM idx + ch.N₀ + 2) + 1))) + 60) + 95 +
            Rcore.phi coreH tok1 s12.mem := by
    by_cases hlt : idx + 1 < d
    · obtain ⟨hGNextEq, hNextGEq, hNextLenAt0, hNextECap, hNextIns, hNextOld⟩ := hNextInv hlt
      obtain ⟨hUCNext, hLNextDisj, hNextFoot, hNLCellFoot, hNLCellG, hNLCellUC⟩ := hDisjNext hlt
      have hGCur12 : DynGraphAt s12.mem gPtr vcIdx ecIdx curG := by
        rw [hs12_eq10]
        exact dynGraphAt_of_agree hDGCur (fun a ha1 ha2 => by
          change Function.update outDG.mem (updCountBase + idx) _ a = outDG.mem a
          rw [Function.update_of_ne (hDisjG a ha1 ha2).2.1])
      have hFoot1Lt (a : ℕ) (ha : Rcore.foot coreH tok1 a) : a < h1 := by
        rcases hFoot1 a ha with h0 | ⟨_, hhi⟩
        · exact (hFoot a h0).trans_le hh1Lo
        · exact hhi
      have hz12 : ZeroFrom s12.mem h1 := fun a ha => by
        rw [hs12_eq10, hs10_eq6_ge a (hh1Lo.trans ha)]; exact hResp6.2.2.1 a ha
      obtain ⟨s13, h2, cLSF, tok2, r13, hs13_5, hRep13, hLw13, ⟨vcF, ecF, hLSF13⟩, hResp13, hc13, hs13_regs⟩ :=
        ordCoreReadLSFK_runs (w := w) (L := L) (k := cfg.P.k) (M := ch.lvlM idx) (N := ch.N₀)
          (vCap := vcIdx) (eCap := ecIdx) (capExp := capExp) (init := initCore)
          (branch := ch.bran idx) (handle := coreH) (graph := gPtr) (heap := h1)
          (st := s12) (ω := ω) hCoreImpl
          ((hs12_regs_keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [s5, s4, s3, s2]))
          ((hs12_regs_keep 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [s5, s4, s3, s2, s1]))
          ((hs12_regs_keep 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [s5, s4, s3]))
          (by simp [s12]) hBrLt hkW hCoreH_W hGCur12 (by omega) (hs12_eq10.symm ▸ hRep10) hIn6
          hFoot1Lt hz12 (by omega)
      set Lw := s13.mem (h1 + 4)
      set stretchDesc := s13.mem (h1 + 3)
      obtain ⟨_, _, _, hS2_13, hSE_13, hSOwn_13⟩ :=
        hOps.op2Placement curG coreH tok1 s13.mem h1 h2 vcF ecF Lw _ (hFour ▸ hLSF13) hResp13.1 hResp13.2.1
      have hNLCell13 : s13.mem (levelMeta + (idx + 1)) = nextLPtr := by
        have hnf1 : ¬ Rcore.foot coreH tok1 (levelMeta + (idx + 1)) := fun hf => by
          rcases hFoot1 _ hf with h0 | ⟨hlo, _⟩
          · exact hNLCellFoot h0
          · omega
        rw [hResp13.2.2.2.1 _ (by omega) hnf1, hs12_eq10]
        change Function.update outDG.mem (updCountBase + idx) _ _ = nextLPtr
        rw [Function.update_of_ne hNLCellUC, hDGFr _ hNLCellG,
          hResp6.2.2.2.1 _ (by omega) hNLCellFoot, hNLCell hlt]
      let s14 := { s13 with regs := Function.update s13.regs 18 stretchDesc }
      let s15 := { s14 with regs := Function.update s14.regs 19 Lw }
      let s16 := { s15 with regs := Function.update s15.regs 20 nextLPtr }
      have r14 : Runs w p ω (.assign 18 (.load (.bin .add (.reg 4) (.const 3)))) s13 .normal s14 5 :=
        runs_assign_iff.mpr ⟨stretchDesc, by
          simp [Expr.eval, BinOp.eval, hs13_regs 4 (by decide), s12, show 3 < 2 ^ w by omega,
            show h1 + 3 < 2 ^ w by omega, stretchDesc], rfl, rfl, rfl⟩
      have r15 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 4) (.const 4)))) s14 .normal s15 5 :=
        runs_assign_iff.mpr ⟨Lw, by
          simp [Expr.eval, BinOp.eval, s14, hs13_regs 4 (by decide), s12, show 4 < 2 ^ w by omega,
            show h1 + 4 < 2 ^ w by omega, Lw], rfl, rfl, rfl⟩
      have r16 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 83) (.bin .add (.reg 96) (.const 1))))) s15 .normal s16 7 :=
        runs_assign_iff.mpr ⟨nextLPtr, by
          simp [Expr.eval, BinOp.eval, s15, s14, hs13_regs 83 (by decide), hs13_regs 96 (by decide),
            hs12_regs_keep 83 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hs12_regs_keep 96 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            s5, s4, s3, s2, s1, hr83, hr96, show 1 < 2 ^ w by omega, show idx + 1 < 2 ^ w by omega,
            show levelMeta + (idx + 1) < 2 ^ w by omega, hNLCell13], rfl, rfl, rfl⟩
      have hNextSB13 : SmallBatchAt s13.mem (s11.regs 10) (ch.G (idx + 1)) nextU (s11.regs 11) := by
        rw [hGNextEq]
        refine smallBatchAt_of_agree (hs11Mem.symm ▸ hs12_eq10.symm ▸ hNextSB11) (fun a ha1 ha2 => ?_)
        rw [hs11_10] at ha1 ha2; rw [hs11_11] at ha2
        exact hResp13.2.2.2.1 a (by omega)
          (by simpa [show s6.mem boBase + (a - s6.mem boBase) = a by omega] using hbPFoot (a - s6.mem boBase) (by omega))
      have hNextBW13 : ∀ t < s11.regs 11, s13.mem (s11.regs 10 + t) < 2 ^ w := fun t ht => by
        rw [hs11_11] at ht; rw [hs11_10]
        rw [hResp13.2.2.2.1 _ (by omega) (hbPFoot t ht), hs12_eq10, hs10_eq6_ge _ (by omega)]
        exact hbPW t ht
      have hPrevLen13 : EdgeValuesAt s13.mem lPtr 4 L P curG.E ℓi :=
        hLenAt.congr (fun e he t ht => by
          have heL : e * L + L ≤ ecIdx * L := by
            simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt (hLenCap e he))
          have hnf1 : ¬ Rcore.foot coreH tok1 (lPtr + e * L + t) := fun hf => by
            rcases hFoot1 _ hf with h0 | ⟨hlo, _⟩
            · exact hDisjL _ (by omega) (by omega) h0
            · omega
          have hneG : lPtr + e * L + t < gPtr ∨ gPtr + dynGraphSize vcIdx ecIdx ≤ lPtr + e * L + t := by
            by_contra h
            rcases (hDisjG (lPtr + e * L + t) (by omega) (by omega)).2.2.2.1 with h' | h' <;> omega
          rw [hResp13.2.2.2.1 _ (by omega) hnf1, hs12_eq10]
          change Function.update outDG.mem (updCountBase + idx) _ _ = st.mem _
          rw [Function.update_of_ne (by rcases hUCL with h' | h' <;> omega), hDGFr _ hneG,
            hResp6.2.2.2.1 _ (by omega) (hDisjL _ (by omega) (by omega))])
      have hCurLen13 : EdgeValuesAt s13.mem nextLPtr 4 L P (ch.G (idx + 1)).E oldNextℓ :=
        hNextLenAt0.congr (fun e he t ht => by
          have heL : e * L + L ≤ ecNext * L := by
            simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt (hNextECap e he))
          have hnf1 : ¬ Rcore.foot coreH tok1 (nextLPtr + e * L + t) := fun hf => by
            rcases hFoot1 _ hf with h0 | ⟨hlo, _⟩
            · exact hNextFoot _ (by omega) (by omega) h0
            · omega
          have hneG : nextLPtr + e * L + t < gPtr ∨ gPtr + dynGraphSize vcIdx ecIdx ≤ nextLPtr + e * L + t := by
            by_contra h
            rcases (hDisjG (nextLPtr + e * L + t) (by omega) (by omega)).2.2.2.2 hlt with h' | h' <;> omega
          rw [hResp13.2.2.2.1 _ (by omega) hnf1, hs12_eq10]
          change Function.update outDG.mem (updCountBase + idx) _ _ = st.mem _
          rw [Function.update_of_ne (by rcases hUCNext with h' | h' <;> omega), hDGFr _ hneG,
            hResp6.2.2.2.1 _ (by omega) (hNextFoot _ (by omega) (by omega))])
      have hNFootNext (a : ℕ) (h1' : nextLPtr ≤ a) (h2' : a < nextLPtr + ecNext * L) :
          ¬ Rcore.foot coreH tok1 a := fun hf => by
        rcases hFoot1 a hf with h0 | ⟨hlo, _⟩
        · exact hNextFoot a h1' h2' h0
        · omega
      have hMonoSp := Nat.mul_le_mul_left nextU.length (wireCoreLenEdgeSpace_mono (max_le_max_left L hLw13))
      have hMonoCost := Nat.mul_le_mul_left nextU.length
        (Nat.add_le_add_right (wireCoreLenEdgeCost_mono (max_le_max_left L hLw13)) 60)
      have hh2Lo := hResp13.1
      have hh2Hi := hResp13.2.1
      have hNLHi := hNLLe hlt
      obtain ⟨h3, outLen, cLen, rLenBody, hh3Lo, hh3Hi, hcLen, hNextLen17, hz17, hFrLen17⟩ :=
        wireUpdateCoreLenFromBatchBody_runs (w := w) (edgeProc := edgeProc) (signExt := signExt)
          (mul := mul) (intDiv := intDiv) (copy := copy)
          (batchPtr := s11.regs 10) (stretchDesc := stretchDesc) (prevLenPtr := lPtr)
          (curLenPtr := nextLPtr) (L := L) (Lw := Lw) (P := P) (ecPrev := ecIdx) (ecCur := ecNext)
          (totalWords := s11.regs 11) (pos := s16.pos) (heap := h2) (p := p) (ω := ω) (mem := s16.mem)
          hEdgeProc hSign hMul hDiv hCopy hNextSB13 hNextBW13
          (hFour ▸ hPrec ▸ hLSF13.2.2.2) hPrevLen13 hCurLen13 hNextECap hNextIns
          (fun e he hno => by
            obtain ⟨hmem, heq⟩ := hNextOld e (hNextGEq.symm ▸ he) (fun u hu hins => hno ⟨u, hu, hins⟩)
            exact ⟨hmem, heq.symm⟩)
          (fun e _ ⟨u, hu, hins⟩ => by
            obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hu
            exact ⟨k, hk, hins⟩)
          (by rw [hs11_10, hs11_11]; exact hbPHi.trans hh2Lo)
          hS2_13 hSE_13 (by omega) (by omega)
          (Or.inr (by rw [hs11_10]; omega)) hLNextDisj
          (fun e he k hk => by
            dsimp only [s16, s15, s14, stretchDesc]
            have hOwn := (hSOwn_13 e he).2.1 (s13.mem (s13.mem (h1 + 3)) + e * Lw + k) (by omega) (by omega)
            by_contra hcon
            exact hOwn.elim (hNFootNext _ (by omega) (by omega)) (by omega))
          (fun e he k hk => by
            dsimp only [s16, s15, s14, stretchDesc]
            have hOwn := (hSOwn_13 e he).2.2.2 (s13.mem (s13.mem (h1 + 3) + 1) + e * Lw + k) (by omega) (by omega)
            by_contra hcon
            exact hOwn.elim (hNFootNext _ (by omega) (by omega)) (by omega))
          hResp13.2.2.1 (by omega) (by omega)
      let s17 : State := { regs := Function.update s16.regs 4 h3, mem := outLen.mem, pos := outLen.pos }
      have hs16_7 : s16.regs 7 = lPtr := by
        simp only [s16, s15, s14, Function.update_of_ne (by decide : (7 : ℕ) ≠ 20),
          Function.update_of_ne (by decide : (7 : ℕ) ≠ 19), Function.update_of_ne (by decide : (7 : ℕ) ≠ 18)]
        rw [hs13_regs 7 (by decide), hs12_regs_keep 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [s5, s4]
      have hs16_94 : s16.regs 94 = L := by
        simp only [s16, s15, s14, Function.update_of_ne (by decide : (94 : ℕ) ≠ 20),
          Function.update_of_ne (by decide : (94 : ℕ) ≠ 19), Function.update_of_ne (by decide : (94 : ℕ) ≠ 18)]
        rw [hs13_regs 94 (by decide), hs12_regs_keep 94 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [s5, s4, s3, s2, s1, hr94]
      have r17 : Runs w p ω
          (.call 4 updateCoreLenProc [.reg 10, .reg 18, .reg 7, .reg 20, .reg 94, .reg 19, .reg 5])
          s16 .normal s17 (7 + cLen + 1) :=
        runs_call_iff.mpr ⟨[s11.regs 10, stretchDesc, lPtr, nextLPtr, L, Lw, h2],
          wireUpdateCoreLenFromBatchBody edgeProc, .returned h3, outLen, cLen,
          by simp only [evalArgs, Expr.eval, hs16_7, hs16_94]
             simp [s16, s15, s14, hs13_regs 10 (by decide), hs13_5, s12],
          hUpdLenProc, rLenBody, rfl, rfl, by simp [argsSize, Expr.size]⟩
      have hFoot2Lt (a : ℕ) (ha : Rcore.foot coreH tok2 a) : a < h2 := by
        rcases hResp13.2.2.2.2 a ha with h1' | ⟨_, hhi⟩
        · exact (hFoot1Lt a h1').trans_le hh2Lo
        · exact hhi
      have hLoc17 := hCoreLocal coreH aNext tok2 s13.mem s17.mem (fun a ha =>
        (hFrLen17 a (hFoot2Lt a ha) (by
          by_contra h
          rcases hResp13.2.2.2.2 a ha with hf1 | ⟨hlo, _⟩
          · exact hNFootNext a (by omega) (by omega) hf1
          · omega)).symm)
      have rThen := runs_seq_iff.mpr (Or.inr ⟨s13, cLSF, _, r13,
        runs_seq_iff.mpr (Or.inr ⟨s14, 5, _, r14,
          runs_seq_iff.mpr (Or.inr ⟨s15, 5, _, r15,
            runs_seq_iff.mpr (Or.inr ⟨s16, 7, 7 + cLen + 1, r16, r17, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
      have rCond : Runs w p ω (wireBranchBCondLenStmt (opCore 2) updateCoreLenProc) s12 .normal s17 _ :=
        runs_cond_iff.mpr ⟨1, _,
          by simp [Expr.eval, BinOp.eval,
            hs12_regs_keep 96 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hs12_regs_keep 75 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            s5, s4, s3, s2, s1, hr96, hr75, show 1 < 2 ^ w by omega, show idx + 1 < 2 ^ w by omega, hlt],
          rThen, rfl⟩
      refine ⟨s17, _, tok2, rCond, by simp only [s17, Function.update_self]; exact hh2Lo.trans hh3Lo,
        by simp only [s17, Function.update_self]; omega, hz17,
        fun r hr => by simp [s17, s16, s15, s14, Function.update_of_ne (by omega : r ≠ 4),
          Function.update_of_ne (by omega : r ≠ 20), Function.update_of_ne (by omega : r ≠ 19),
          Function.update_of_ne (by omega : r ≠ 18), hs13_regs r (by omega),
          hs12_regs_keep r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          s5, s4, s3, s2, s1, Function.update_of_ne (by omega : r ≠ 8),
          Function.update_of_ne (by omega : r ≠ 7), Function.update_of_ne (by omega : r ≠ 6),
          Function.update_of_ne (by omega : r ≠ 2), Function.update_of_ne (by omega : r ≠ 3)],
        fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · simp [s17, s16, s15, s14, hs13_regs 10 (by decide)]
          · simp [s17, s16, s15, s14, hs13_regs 11 (by decide)]
          · simp [s17, s16, s15, s14, hs13_regs 12 (by decide)]
          · simp [s17, s16, s15, s14, hs13_regs 13 (by decide)],
        hLoc17.1 hRep13,
        fun a ha => by
          rcases hResp13.2.2.2.2 a ha with h1' | ⟨hlo, hhi⟩
          · exact Or.inl h1'
          · exact Or.inr ⟨hlo, hhi.trans_le hh3Lo⟩,
        fun _ => hNextLen17,
        fun a ha hnf hnn => (hFrLen17 a (ha.trans_le hResp13.1) (hnn hlt)).trans (hResp13.2.2.2.1 a ha hnf),
        ?_⟩
      have hPhiEq : Rcore.phi coreH tok2 s17.mem = Rcore.phi coreH tok2 s13.mem := hLoc17.2.symm
      rw [hPhiEq]; simp only [Expr.size]
      clear rCond rThen r17 r13 hNextSB13 hPrevLen13 hCurLen13 hNextLen17 hGCur12 hRep13 hLSF13
      omega
    · have rCond : Runs w p ω (wireBranchBCondLenStmt (opCore 2) updateCoreLenProc) s12 .normal s12 (1 + 5 + 1) :=
        runs_cond_iff.mpr ⟨0, 1,
          by simp [Expr.eval, BinOp.eval,
            hs12_regs_keep 96 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hs12_regs_keep 75 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            s5, s4, s3, s2, s1, hr96, hr75, show 1 < 2 ^ w by omega, show idx + 1 < 2 ^ w by omega, hlt],
          by simpa using (runs_nop_iff (w := w) (p := p) (ω := ω) (st := s12)).mpr ⟨rfl, rfl, rfl⟩, rfl⟩
      refine ⟨s12, 7, tok1, rCond, le_rfl, by simp [s12]; omega,
        fun a ha => by simp [s12] at ha; rw [hs12_eq10, hs10_eq6_ge a (hh1Lo.trans ha)]; exact hResp6.2.2.1 a ha,
        fun r hr => (hs12_regs_keep r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
          (by simp [s5, s4, s3, s2, s1, Function.update_of_ne (by omega : r ≠ 8),
            Function.update_of_ne (by omega : r ≠ 7), Function.update_of_ne (by omega : r ≠ 6),
            Function.update_of_ne (by omega : r ≠ 2), Function.update_of_ne (by omega : r ≠ 3)]),
        fun _ _ => rfl, hs12_eq10.symm ▸ hRep10, fun _ h => Or.inl h, fun h => absurd h hlt,
        fun _ _ _ _ => rfl, by omega⟩
  obtain ⟨sEnd, cCond, tokEnd, rCond, hsEnd_lo, hsEnd_hi, hzEnd, hsEnd_ge70, hsEnd_1013,
      hRepEnd, hFootEnd, hNextLenEnd, hFrEnd, hcCond⟩ := hCondOut
  have rAll := runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 7, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 2, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, cUpd, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 3 + cDG + 1, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 3, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 4, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 6, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, 30, _, r11,
    runs_seq_iff.mpr (Or.inr ⟨s12, 2, cCond, r12, rCond, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hr10End : sEnd.regs 10 = s6.mem boBase := (hsEnd_1013 10 (by simp)).trans (by simp [s12, hs11_10])
  have hr11End : sEnd.regs 11 = s6.mem (boBase + 1) := (hsEnd_1013 11 (by simp)).trans (by simp [s12, hs11_11])
  have hr12End : sEnd.regs 12 = s6.mem (boBase + 2) := (hsEnd_1013 12 (by simp)).trans (by simp [s12, hs11_12])
  have hr13End : sEnd.regs 13 = s6.mem (boBase + 3) := (hsEnd_1013 13 (by simp)).trans (by simp [s12, hs11_13])
  have hEndEq6 (a : ℕ) (h1' : curHeap ≤ a) (h2' : a < h1) (hnf : ¬ Rcore.foot coreH tok1 a) :
      sEnd.mem a = s6.mem a :=
    (hFrEnd a h2' hnf (fun hlt => Or.inr (by have := hNLLe hlt; omega))).trans
      (hs12_eq10.symm ▸ hs10_eq6_ge a h1')
  have hNextSB6 : SmallBatchAt s6.mem (s6.mem boBase) (cfg.T.S (ch.scState idx) (ch.bran idx))
      nextU (s6.mem (boBase + 1)) := by
    have h := (hBO6'.2 (ch.bran idx) hBrLt).1
    simpa only [boBase, Nat.add_assoc, show 1 + (4 * ch.bran idx + 1) = 2 + 4 * ch.bran idx by omega] using h
  refine ⟨sEnd, _, tokEnd, nextEdits, rAll, hh1Lo.trans hsEnd_lo, hsEnd_hi, hzEnd, hsEnd_ge70,
    hRepEnd, hIn6,
    fun a ha => by
      rcases hFootEnd a ha with h1' | ⟨hlo, hhi⟩
      · rcases hFoot1 a h1' with h0 | ⟨hlo, hhi⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hlo, hhi.trans_le hsEnd_lo⟩
      · exact Or.inr ⟨hh1Lo.trans hlo, hhi⟩,
    dynGraphAt_of_agree hDGCur (fun a ha1 ha2 => by
      have hnf1 : ¬ Rcore.foot coreH tok1 a := fun hf => by
        rcases hFoot1 a hf with h0 | ⟨hlo, _⟩
        · exact (hDisjG a ha1 ha2).1 h0
        · omega
      rw [hFrEnd a (by omega) hnf1 (fun hlt => (hDisjG a ha1 ha2).2.2.2.2 hlt), hs12_eq10]
      change Function.update outDG.mem (updCountBase + idx) _ a = outDG.mem a
      rw [Function.update_of_ne (hDisjG a ha1 ha2).2.1]),
    by
      have hnf1 : ¬ Rcore.foot coreH tok1 (updCountBase + idx) := fun hf => by
        rcases hFoot1 _ hf with h0 | ⟨hlo, _⟩
        · exact hUCFoot h0
        · omega
      rw [hFrEnd _ (by omega) hnf1 (fun hlt => (hDisjNext hlt).1), hs12_eq10]
      simp [s10],
    by
      rw [hr10End, hr11End]
      exact smallBatchAt_of_agree hNextSB6 (fun a ha1 ha2 =>
        hEndEq6 a (by omega) (by omega) (by simpa [show s6.mem boBase + (a - s6.mem boBase) = a by omega] using hbPFoot (a - s6.mem boBase) (by omega))),
    by
      rw [hr10End]
      exact decodeBatch_of_agree hNextSB6.1 hNextDec6 (fun t ht =>
        hEndEq6 _ (by omega) (by omega) (hbPFoot t ht)),
    by
      rw [hr12End, hr13End]
      refine ordEditsAt_of_agree (by simpa [hs11_12, hs11_13, hs11Mem, ← hs12_eq10] using hNextOE11)
        (fun a ha1 ha2 => hFrEnd a (by omega)
          (by simpa [show s6.mem (boBase + 2) + (a - s6.mem (boBase + 2)) = a by omega] using hePFoot (a - s6.mem (boBase + 2)) (by omega))
          (fun hlt => Or.inr (by have := hNLLe hlt; omega))),
    hNextRot11,
    by rw [hr10End]; exact hbPLo,
    by rw [hr10End, hr11End]; exact hbPHi.trans hsEnd_lo,
    by rw [hr12End]; exact hePLo,
    by rw [hr12End, hr13End]; exact hePHi.trans hsEnd_lo,
    fun t ht => by
      rw [hr11End] at ht; rw [hr10End]
      refine ⟨by rw [hEndEq6 _ (by omega) (by omega) (hbPFoot t ht)]; exact hbPW t ht, fun hf => ?_⟩
      rcases hFootEnd _ hf with h1' | ⟨hlo, _⟩
      · exact hbPFoot t ht h1'
      · omega,
    fun t ht => by
      rw [hr13End] at ht; rw [hr12End]
      refine ⟨by rw [hEndEq6 _ (by omega) (by omega) (hePFoot t ht)]; exact hePW t ht, fun hf => ?_⟩
      rcases hFootEnd _ hf with h1' | ⟨hlo, _⟩
      · exact hePFoot t ht h1'
      · omega,
    hNextLenEnd,
    fun a ha hnf hng hnu hnl => by
      have hnf1 : ¬ Rcore.foot coreH tok1 a := fun hf => by
        rcases hFoot1 a hf with h0 | ⟨hlo, _⟩
        · exact hnf h0
        · omega
      rw [hFrEnd a (ha.trans_le hh1Lo) hnf1 hnl, hs12_eq10]
      change Function.update outDG.mem (updCountBase + idx) _ a = st.mem a
      rw [Function.update_of_ne hnu, hDGFr a hng, hResp6.2.2.2.1 a ha hnf],
    ?_⟩
  rw [hs12_eq10, hPhi10] at hcCond
  dsimp only [aNext, aPrev] at hc6
  dsimp only [dgApplyBatchContract] at hcDG
  have hPhi5 : Rcore.phi coreH coreTok0 s5.mem = Rcore.phi coreH coreTok0 st.mem := rfl
  rw [hPhi5] at hc6
  have hMulDist :
      Psc.mul * (cfg.T.cost sc' - cfg.T.cost (ch.scState idx) +
        (cfg.P.k + 1) * (curBatchWords + curEditsWords + 1) *
          SparseCore.bundleLogFactor (ch.lvlM idx) ch.N₀) =
      Psc.mul * (cfg.T.cost sc' - cfg.T.cost (ch.scState idx)) +
        Psc.mul * ((cfg.P.k + 1) * (curBatchWords + curEditsWords + 1) *
          SparseCore.bundleLogFactor (ch.lvlM idx) ch.N₀) := Nat.mul_add _ _ _
  rw [hMulDist] at hc6
  clear rAll rCond r12 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 hBO6 hBO6' hBO10 hNextSB11 hNextOE11
    hNextLenEnd hRepEnd hRep10 hRep6 hDGCur hDGAfter hGAt6 hSmall6 hPre0 hNextInv hNextSB6 hMulDist
  omega

end MinCostFlow.MinRatio
