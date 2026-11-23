module

public import MinCostFlow.MinRatio.WireChainCoreReembPlaceKFBL
public import MinCostFlow.MinRatio.WireChainCoreOps
public import MinCostFlow.MinRatio.WireChainCoreSelOutLevelKFBL
import WordRAM.Tactic

/-!
# The first half of a Branch B level step under `KFRBL` (`WireChainCoreBranchBHeadKFBL`)

At a level `idx` that `Update` does not rebuild, the chain-update core calls op `0` of the sparse
core on the batch of the level, applies the batch to the level graph, adds the batch length to the
update counter, and loads the batch and the order edits that the active branch forwards to the next
level. This file gives that part of the step, `wireBranchBStepHeadKFBL`, and its run lemma
`wireBranchBStepHeadKFBL_runs`. It is the first half of `wireBranchBNoRebuildStep`
(`WireChainCoreBranchBStep.lean`), moved to the layout contract with re-embedding lists
(`sparseCoreOrdMachineContractKFRBL`) and to the output facts of op `0`
(`SparseCoreUpdateOutFootAt`, `SparseCoreReembPlaceAt`), through `ordCoreUpdateKFRBLPlace_runs`.

The step keeps in registers `23`, `24` and `25` the batch pointer, its length in words and the
heap pointer of the op-`0` call. Only the footprint of the core, the level graph and the update
counter change below that heap pointer, and the op-`0` output above it stays as op `0` left it. So
the change record and the re-embedding list of the active branch are still there at the end, and
the next part of the step copies them (`WireChainCoreBranchBCopyKFBL.lean`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- A change record that the memory keeps. -/
theorem lsfChangeAt_of_agree {mem₁ mem₂ : ℕ → ℕ} {a : ℕ} {c : Read.LSFChange}
    (h : Read.LSFChangeAt mem₁ a c) (hag : ∀ x, a ≤ x → x < a + c.words → mem₂ x = mem₁ x) :
    Read.LSFChangeAt mem₂ a c := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hw : c.words = 2 + c.roots.length + c.fDel.length := by
    simp only [Read.LSFChange.words, Read.LSFChange.size]; omega
  exact ⟨(hag a le_rfl (by omega)).trans h0,
    fun i hi => (hag _ (by omega) (by omega)).trans (h1 i hi),
    (hag _ (by omega) (by omega)).trans h2,
    fun i hi => (hag _ (by omega) (by omega)).trans (h3 i hi)⟩

/-- The change records of op `0` stay when the memory keeps the output region `[heap, ret)`. -/
theorem branchOutFChgAt_of_agree {w heap ret k : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    {oldLsf newLsf : ℕ → LSF} (h : BranchOutFChgAt w mem₁ heap ret k oldLsf newLsf)
    (hag : ∀ a, heap ≤ a → a < ret → mem₂ a = mem₁ a) :
    BranchOutFChgAt w mem₂ heap ret k oldLsf newLsf := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hp : mem₂ (heap + 1 + 6 * k) = mem₁ (heap + 1 + 6 * k) := hag _ (by omega) (by omega)
  refine ⟨h0, by rw [hp]; exact h1, by rw [hp]; exact h2, fun j hj => ?_⟩
  obtain ⟨c, hc, hex, hlo, hhi, hw⟩ := h3 j hj
  have hq : mem₂ (mem₁ (heap + 1 + 6 * k) + j) = mem₁ (mem₁ (heap + 1 + 6 * k) + j) :=
    hag _ (by omega) (by omega)
  refine ⟨c, ?_, hex, ?_, ?_, hw⟩
  · show Read.LSFChangeAt mem₂ (mem₂ (mem₂ (heap + 1 + 6 * k) + j)) c
    rw [hp, hq]
    exact lsfChangeAt_of_agree hc fun x hx1 hx2 => hag x (by omega) (by omega)
  · show heap ≤ mem₂ (mem₂ (heap + 1 + 6 * k) + j)
    rw [hp, hq]; exact hlo
  · show mem₂ (mem₂ (heap + 1 + 6 * k) + j) + c.words ≤ ret
    rw [hp, hq]; exact hhi

/-- The first half of a non-rebuild level step at `idx = reg 96`: load the handle, the branch, the
graph and the lengths of the level, keep the batch (`regs 10, 11`) and the heap pointer (`reg 4`) in
`regs 23, 24, 25`, call op `0`, apply the batch to the level graph, add the batch length to the
update counter, load the forwarded batch and order edits of the active branch into `regs 10..13`,
and move the heap pointer to the end of the op-`0` output. -/
@[expose] def wireBranchBStepHeadKFBL (updCore dgApply : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 77) (.reg 96))) ;;
  .assign 2 (.load (.bin .add (.reg 78) (.reg 96))) ;;
  .assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 96))) ;;
  .assign 7 (.load (.bin .add (.reg 83) (.reg 96))) ;;
  .assign 8 (.reg 7) ;;
  .assign 23 (.reg 10) ;;
  .assign 24 (.reg 11) ;;
  .assign 25 (.reg 4) ;;
  ordCoreUpdateStmt updCore ;;
  .call 15 dgApply [.reg 6, .reg 10, .const 1] ;;
  .assign 16 (.load (.reg 10)) ;;
  .assign 17 (.bin .add (.reg 85) (.reg 96)) ;;
  .store (.reg 17) (.bin .add (.load (.reg 17)) (.reg 16)) ;;
  ordLoadBranchOutStmt ;;
  .assign 4 (.reg 5)

theorem wireBranchBStepHeadKFBL_noRand (updCore dgApply : ℕ) :
    (wireBranchBStepHeadKFBL updCore dgApply).NoRand := by
  simp [wireBranchBStepHeadKFBL, ordCoreUpdateStmt, ordLoadBranchOutStmt, Stmt.NoRand]

set_option maxHeartbeats 1600000 in
/-- Run the first half of a non-rebuild level step. Op `0` turns the abstract state of the level into
`aNext` (the model step of `Chain.Ordered.updateLoop`), the level graph becomes `curG`, and the
update counter grows by the batch length. The forwarded batch and order edits of the active branch
`b` lie in the op-`0` output `[curHeap, h1)`, off the new footprint, and their pointers are in
`regs 10..13`. The change record of branch `b` and its re-embedding list are those of op `0`. Below
`curHeap`, only the footprint of the core, the level graph and the update counter change. -/
theorem wireBranchBStepHeadKFBL_runs
    {w L P depth M N vCap eCap capExp edMul initCore dgApply
      idx coreH gPtr lPtr curBatch curBatchWords curEdits curEditsWords curHeap
      handleBase branchBase levelMeta updCountBase : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc : ℕ → List ℕ → ℕ} {Ginit : MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opCore : ℕ → ℕ}
    {ω : ℕ → Bool} {st : State}
    (ch : ChainState cfg.T cfg.P) (curU : List Update) (curEditsList : List OrdEdit)
    (oldOrd : ℕ → List End) (ℓi gi : ℕ → ℝ) (coreTok0 : Rcore.τ)
    (hCoreLocal : Rcore.Local)
    (hFour : fmt.limbBits = 4) (hPrec : fmt.precision = P) (hw16 : 16 ≤ 2 ^ w)
    (hUpdOrdEq : ToolUpdateOrdEqOnE cfg.T)
    (hCoreImpl : Rcore.Implements w p initCore opCore
      (sparseCoreOrdMachineContractKFRBL fmt L depth cfg.T reembFn Ginit cfg.P.k M N vCap eCap
        capExp Psc alloc))
    (hOut : SparseCoreUpdateOutFootAt fmt L depth cfg.T Ginit cfg.P.k M N vCap eCap capExp Psc
      alloc edMul Rcore p opCore)
    (hPlace : SparseCoreReembPlaceAt fmt L depth cfg.T Ginit cfg.P.k M N vCap eCap capExp Psc
      alloc Rcore p opCore)
    (hDGApply : MeetsContract w p dgApply
      (dgApplyBatchContract w vCap eCap (ch.G idx) (ch.G idx) curU curBatchWords))
    (hRegs :
      st.regs 4 = curHeap ∧ st.regs 10 = curBatch ∧ st.regs 11 = curBatchWords ∧
      st.regs 12 = curEdits ∧ st.regs 13 = curEditsWords ∧
      st.regs 75 = cfg.P.d ∧ st.regs 77 = handleBase ∧ st.regs 78 = branchBase ∧
      st.regs 83 = levelMeta ∧ st.regs 85 = updCountBase ∧ st.regs 96 = idx)
    (hHCell : st.mem (handleBase + idx) = coreH)
    (hBCell : st.mem (branchBase + idx) = ch.bran idx)
    (hBrLt : ch.bran idx < cfg.P.k)
    (hGCell : st.mem (levelMeta + cfg.P.d + idx) = gPtr)
    (hLCell : st.mem (levelMeta + idx) = lPtr)
    (hUCCell : st.mem (updCountBase + idx) = ch.updCount idx)
    (hUCW : ch.updCount idx + curU.length < 2 ^ w)
    (hCoreH_W : coreH < 2 ^ w)
    (hRep : Rcore.rep coreH ⟨ch.scState idx, ch.G idx, oldOrd, ch.updCount idx⟩ coreTok0 st.mem)
    (hIn : SparseCoreOrdInput cfg.T cfg.P.k M N (ch.scState idx) (ch.G idx) oldOrd
      (ch.updCount idx))
    (hFoot : ∀ a, Rcore.foot coreH coreTok0 a → a < curHeap)
    (hGAt : DynGraphAt st.mem gPtr vCap eCap (ch.G idx))
    (hSmall : SmallBatchAt st.mem curBatch (ch.G idx) curU curBatchWords)
    (hDecode : (decodeBatch st.mem curBatch (ch.G idx)).1 = curU)
    (hBatchValid : (ch.G idx).BatchIsValid curU)
    (hBatchCaps : BatchWithinCaps vCap eCap curU)
    (hBatchW : ∀ j < curBatchWords, st.mem (curBatch + j) < 2 ^ w)
    (hEditsAt : OrdEditsAt st.mem curEdits curEditsList curEditsWords)
    (hEditsW : ∀ j < curEditsWords, st.mem (curEdits + j) < 2 ^ w)
    (hValid : OrdEditsValidFor vCap eCap oldOrd curEditsList)
    (hBlocks : OrdEditsForBatch (ch.G idx) curU curEditsList)
    (hNewOrdEq :
      applyOrdEdits oldOrd curEditsList =
        chainLevelOrd cfg.T (fun j => if j = idx then (ch.G idx).applyBatch curU else ch.G j)
          ch.scState ch.bran idx)
    (hOrdBatch : OrderedBatch (ch.G idx) curU oldOrd (applyOrdEdits oldOrd curEditsList))
    (hUpdThresh : ((ch.updCount idx + curU.length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold cfg.P.k M N)
    (hLenAt : EdgeValuesAt st.mem lPtr 4 L P ((ch.G idx).applyBatch curU).E ℓi)
    (hLenCap : ∀ e ∈ ((ch.G idx).applyBatch curU).E, e < eCap)
    (hLenPos : ∀ e ∈ ((ch.G idx).applyBatch curU).E, 0 < ℓi e)
    (hBelow :
      handleBase + idx < curHeap ∧ branchBase + idx < curHeap ∧
      levelMeta + cfg.P.d + idx < curHeap ∧ updCountBase + idx < curHeap ∧
      gPtr + dynGraphSize vCap eCap ≤ curHeap ∧ lPtr + eCap * L ≤ curHeap ∧
      curBatch + curBatchWords ≤ curHeap ∧ curEdits + curEditsWords ≤ curHeap)
    (hDisj :
      (∀ a, gPtr ≤ a → a < gPtr + dynGraphSize vCap eCap →
        ¬ Rcore.foot coreH coreTok0 a ∧ a ≠ updCountBase + idx ∧
        (a < curBatch ∨ curBatch + curBatchWords ≤ a)) ∧
      ¬ Rcore.foot coreH coreTok0 (updCountBase + idx) ∧
      (updCountBase + idx < curBatch ∨ curBatch + curBatchWords ≤ updCountBase + idx) ∧
      (∀ t < curBatchWords, ¬ Rcore.foot coreH coreTok0 (curBatch + t)))
    (hz : ZeroFrom st.mem curHeap)
    (hRoom : curHeap + alloc 0
      [coreH, gPtr, curBatch, curBatchWords, curEdits, curEditsWords, lPtr, lPtr, curHeap] <
        2 ^ w) :
    let curG := (ch.G idx).applyBatch curU
    let newOrd := chainLevelOrd cfg.T (fun j => if j = idx then curG else ch.G j)
      ch.scState ch.bran idx
    let upd := cfg.T.updateOrd (ch.scState idx) curU ℓi gi newOrd
    let sc' := upd.1
    let nextU := upd.2 (ch.bran idx)
    let aNext : SparseCoreOrdAbs cfg.T := ⟨sc', curG, newOrd, ch.updCount idx + curU.length⟩
    let args := [coreH, gPtr, curBatch, curBatchWords, curEdits, curEditsWords, lPtr, lPtr, curHeap]
    let k := cfg.P.k
    let b := ch.bran idx
    let base := curHeap + 1 + 4 * b
    ∃ (out : State) (cost h1 : ℕ) (tok1 : Rcore.τ),
      Runs w p ω (wireBranchBStepHeadKFBL (opCore 0) dgApply) st .normal out cost ∧
      out.regs 4 = h1 ∧ curHeap ≤ h1 ∧ h1 ≤ curHeap + alloc 0 args ∧
      out.regs 2 = b ∧ out.regs 3 = coreH ∧ out.regs 6 = gPtr ∧ out.regs 7 = lPtr ∧
      out.regs 23 = curBatch ∧ out.regs 24 = curBatchWords ∧ out.regs 25 = curHeap ∧
      out.regs 10 = out.mem base ∧ out.regs 11 = out.mem (base + 1) ∧
      out.regs 12 = out.mem (base + 2) ∧ out.regs 13 = out.mem (base + 3) ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      ZeroFrom out.mem h1 ∧
      Rcore.rep coreH aNext tok1 out.mem ∧
      SparseCoreOrdInput cfg.T k M N sc' curG newOrd (ch.updCount idx + curU.length) ∧
      (∀ a, Rcore.foot coreH tok1 a → Rcore.foot coreH coreTok0 a ∨ (curHeap ≤ a ∧ a < h1)) ∧
      DynGraphAt out.mem gPtr vCap eCap curG ∧
      out.mem (updCountBase + idx) = ch.updCount idx + curU.length ∧
      SmallBatchAt out.mem (out.mem base) (cfg.T.S (ch.scState idx) b) nextU
        (out.mem (base + 1)) ∧
      (decodeBatch out.mem (out.mem base) (cfg.T.S (ch.scState idx) b)).1 = nextU ∧
      (∃ nextEdits, OrdEditsAt out.mem (out.mem (base + 2)) nextEdits (out.mem (base + 3)) ∧
        applyOrdEdits (cfg.T.rot (ch.scState idx) b) nextEdits = cfg.T.rot sc' b ∧
        OrdEditsForBatch (cfg.T.S (ch.scState idx) b) nextU nextEdits ∧
        OrdEditsValidFor vCap eCap (cfg.T.rot (ch.scState idx) b) nextEdits) ∧
      base + 3 < h1 ∧
      curHeap ≤ out.mem base ∧ out.mem base + out.mem (base + 1) ≤ h1 ∧
      curHeap ≤ out.mem (base + 2) ∧ out.mem (base + 2) + out.mem (base + 3) ≤ h1 ∧
      (∀ t < out.mem (base + 1), out.mem (out.mem base + t) < 2 ^ w ∧
        ¬ Rcore.foot coreH tok1 (out.mem base + t)) ∧
      (∀ t < out.mem (base + 3), out.mem (out.mem (base + 2) + t) < 2 ^ w ∧
        ¬ Rcore.foot coreH tok1 (out.mem (base + 2) + t)) ∧
      out.mem (base + 3) ≤ edMul * (cfg.T.cost sc' - cfg.T.cost (ch.scState idx) +
        (curBatchWords + curEditsWords + 1) * SparseCore.bundleLogFactor M N) ∧
      BranchOutFChgAt w out.mem curHeap h1 k (cfg.T.lsfs (ch.scState idx)) (cfg.T.lsfs sc') ∧
      ReembListAt out.mem (out.mem (curHeap + 1 + 4 * k + 2 * b))
        (out.mem (curHeap + 2 + 4 * k + 2 * b)) (reembFn (ch.scState idx) curU newOrd b) ∧
      curHeap ≤ out.mem (curHeap + 1 + 4 * k + 2 * b) ∧
      out.mem (curHeap + 1 + 4 * k + 2 * b) + out.mem (curHeap + 2 + 4 * k + 2 * b) ≤ h1 ∧
      (∀ a < curHeap, ¬ Rcore.foot coreH coreTok0 a →
        (a < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ a) → a ≠ updCountBase + idx →
        out.mem a = st.mem a) ∧
      cost + Rcore.phi coreH tok1 out.mem ≤
        Psc.mul * (cfg.T.cost sc' - cfg.T.cost (ch.scState idx) +
          (k + 1) * (curBatchWords + curEditsWords + 1) * SparseCore.bundleLogFactor M N) +
        670 * curBatchWords + 200 + Rcore.phi coreH coreTok0 st.mem := by
  dsimp only
  set d := cfg.P.d
  set curG := (ch.G idx).applyBatch curU
  set newOrd := chainLevelOrd cfg.T (fun j => if j = idx then curG else ch.G j) ch.scState
    ch.bran idx
  set upd := cfg.T.updateOrd (ch.scState idx) curU ℓi gi newOrd
  set sc' := upd.1
  set nextU := upd.2 (ch.bran idx)
  set aNext : SparseCoreOrdAbs cfg.T := ⟨sc', curG, newOrd, ch.updCount idx + curU.length⟩
  obtain ⟨hr4, hr10, hr11, hr12, hr13, hr75, hr77, hr78, hr83, hr85, hr96⟩ := hRegs
  obtain ⟨hHBLt, hBBLt, hLMLt, hUCLt, hGLe, hLLe, hBLe, hELe⟩ := hBelow
  obtain ⟨hDisjG, hUCFoot, hUCB, hDisjB⟩ := hDisj
  -- Step 1: the loads and the three saved registers
  let s1 := { st with regs := Function.update st.regs 3 coreH }
  let s2 := { s1 with regs := Function.update s1.regs 2 (ch.bran idx) }
  let s3 := { s2 with regs := Function.update s2.regs 6 gPtr }
  let s4 := { s3 with regs := Function.update s3.regs 7 lPtr }
  let s5 := { s4 with regs := Function.update s4.regs 8 lPtr }
  let s5a := { s5 with regs := Function.update s5.regs 23 curBatch }
  let s5b := { s5a with regs := Function.update s5a.regs 24 curBatchWords }
  let s5c := { s5b with regs := Function.update s5b.regs 25 curHeap }
  have r1 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 77) (.reg 96)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨coreH, by simp [Expr.eval, BinOp.eval, hr77, hr96,
      show handleBase + idx < 2 ^ w by omega, hHCell], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 78) (.reg 96)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨ch.bran idx, by simp [Expr.eval, BinOp.eval, s1, hr78, hr96,
      show branchBase + idx < 2 ^ w by omega, hBCell], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 96))))
      s2 .normal s3 7 :=
    runs_assign_iff.mpr ⟨gPtr, by simp [Expr.eval, BinOp.eval, s2, s1, hr83, hr75, hr96,
      show levelMeta + d < 2 ^ w by omega, show levelMeta + d + idx < 2 ^ w by omega, hGCell],
      rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 83) (.reg 96)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨lPtr, by simp [Expr.eval, BinOp.eval, s3, s2, s1, hr83, hr96,
      show levelMeta + idx < 2 ^ w by omega, hLCell], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 8 (.reg 7)) s4 .normal s5 2 :=
    runs_assign_iff.mpr ⟨lPtr, by simp [Expr.eval, s4], rfl, rfl, rfl⟩
  have r5a : Runs w p ω (.assign 23 (.reg 10)) s5 .normal s5a 2 :=
    runs_assign_iff.mpr ⟨curBatch, by simp [Expr.eval, s5, s4, s3, s2, s1, hr10], rfl, rfl, rfl⟩
  have r5b : Runs w p ω (.assign 24 (.reg 11)) s5a .normal s5b 2 :=
    runs_assign_iff.mpr ⟨curBatchWords, by simp [Expr.eval, s5a, s5, s4, s3, s2, s1, hr11],
      rfl, rfl, rfl⟩
  have r5c : Runs w p ω (.assign 25 (.reg 4)) s5b .normal s5c 2 :=
    runs_assign_iff.mpr ⟨curHeap, by simp [Expr.eval, s5b, s5a, s5, s4, s3, s2, s1, hr4],
      rfl, rfl, rfl⟩
  have hs5c_regs (r : ℕ) (h3 : r ≠ 3) (h2 : r ≠ 2) (h6 : r ≠ 6) (h7 : r ≠ 7) (h8 : r ≠ 8)
      (h23 : r ≠ 23) (h24 : r ≠ 24) (h25 : r ≠ 25) : s5c.regs r = st.regs r := by
    simp [s5c, s5b, s5a, s5, s4, s3, s2, s1, Function.update_of_ne h3, Function.update_of_ne h2,
      Function.update_of_ne h6, Function.update_of_ne h7, Function.update_of_ne h8,
      Function.update_of_ne h23, Function.update_of_ne h24, Function.update_of_ne h25]
  -- Step 2: op `0`
  set aPrev : SparseCoreOrdAbs cfg.T := ⟨ch.scState idx, ch.G idx, oldOrd, ch.updCount idx⟩
  let updArgs := [coreH, gPtr, curBatch, curBatchWords, curEdits, curEditsWords, lPtr, lPtr,
    curHeap]
  have hReadBatch : ordUpdateBatch aPrev updArgs s5c.mem = curU := by
    unfold ordUpdateBatch
    simp only [updArgs, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, aPrev]
    exact hDecode
  have hReadEdits : readOrdEdits s5c.mem curEdits = curEditsList := hEditsAt.1
  have hUpdOrdEq' : ordUpdateOrder aPrev updArgs s5c.mem = newOrd := by
    unfold ordUpdateOrder
    simp only [updArgs, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, aPrev, hReadEdits]
    exact hNewOrdEq
  have hUpdModelEq : ordUpdateModel fmt L aPrev updArgs s5c.mem = upd := by
    unfold ordUpdateModel
    rw [hReadBatch, hUpdOrdEq']
    exact hUpdOrdEq (ch.scState idx) curU _ ℓi _ gi newOrd
  have hANextEq : ordUpdateNext fmt L aPrev updArgs s5c.mem = aNext := by
    unfold ordUpdateNext
    rw [hUpdModelEq, hReadBatch, hUpdOrdEq']
  have hPre0 : SparseCoreOrdUpdateAt fmt L cfg.T cfg.P.k M N vCap eCap aPrev updArgs s5c.mem := by
    refine ⟨coreH, gPtr, curBatch, curBatchWords, curEdits, curEditsWords, lPtr, lPtr, curHeap,
      rfl, hIn, hGAt, ?_, ?_, ?_, ?_, ?_, ?_, hBatchW, hEditsW, hGLe, hBLe, hELe, hLLe, hLLe, ?_,
      ?_⟩
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
  obtain ⟨s6, h1, cUpd, tok1, r6, hs6_5, hRep6, hIn6, hBO6, hFChg6, hReemb6, hPl6, hFor6, hVal6,
      hSlots6, hResp6, hc6, hs6_regs⟩ :=
    ordCoreUpdateKFRBLPlace_runs (w := w) (L := L) (depth := depth) (k := cfg.P.k) (M := M) (N := N)
      (vCap := vCap) (eCap := eCap) (capExp := capExp) (edMul := edMul) (init := initCore)
      (handle := coreH) (graph := gPtr) (batch := curBatch) (words := curBatchWords)
      (edits := curEdits) (editWords := curEditsWords) (lengths := lPtr) (gradient := lPtr)
      (heap := curHeap) (st := s5c) (ω := ω) hCoreImpl hOut hPlace
      (by simp [s5c, s5b, s5a, s5, s4, s3, s2, s1]) (by simp [s5c, s5b, s5a, s5, s4, s3])
      (by simp [s5c, s5b, s5a, s5, s4, s3, s2, s1, hr10])
      (by simp [s5c, s5b, s5a, s5, s4, s3, s2, s1, hr11])
      (by simp [s5c, s5b, s5a, s5, s4, s3, s2, s1, hr12])
      (by simp [s5c, s5b, s5a, s5, s4, s3, s2, s1, hr13]) (by simp [s5c, s5b, s5a, s5, s4])
      (by simp [s5c, s5b, s5a, s5]) (by simp [s5c, s5b, s5a, s5, s4, s3, s2, s1, hr4])
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      hRep hPre0 (by rw [hReadEdits]; exact hValid)
      (by rw [hReadBatch, hReadEdits]; exact hBlocks) hFoot hz (by omega)
  have hANextEq2 : ordUpdateNext fmt L aPrev [coreH, gPtr, curBatch, curBatchWords, curEdits,
      curEditsWords, lPtr, lPtr, curHeap] s5c.mem = aNext := hANextEq
  have hUpdModelEq2 : ordUpdateModel fmt L aPrev [coreH, gPtr, curBatch, curBatchWords, curEdits,
      curEditsWords, lPtr, lPtr, curHeap] s5c.mem = upd := hUpdModelEq
  have hReadBatch2 : ordUpdateBatch aPrev [coreH, gPtr, curBatch, curBatchWords, curEdits,
      curEditsWords, lPtr, lPtr, curHeap] s5c.mem = curU := hReadBatch
  have hUpdOrdEq2 : ordUpdateOrder aPrev [coreH, gPtr, curBatch, curBatchWords, curEdits,
      curEditsWords, lPtr, lPtr, curHeap] s5c.mem = newOrd := hUpdOrdEq'
  simp only [hANextEq2, hUpdModelEq2] at hRep6 hIn6 hBO6 hFChg6 hFor6 hVal6 hSlots6 hc6 hPl6
  simp only [hReadBatch2, hUpdOrdEq2] at hReemb6
  have hh1Lo : curHeap ≤ h1 := hResp6.1
  have hh1Hi : h1 ≤ curHeap + alloc 0 [coreH, gPtr, curBatch, curBatchWords, curEdits,
      curEditsWords, lPtr, lPtr, curHeap] := hResp6.2.1
  have hFoot1 (a : ℕ) (ha : Rcore.foot coreH tok1 a) :
      Rcore.foot coreH coreTok0 a ∨ (curHeap ≤ a ∧ a < h1) := hResp6.2.2.2.2 a ha
  -- Step 3: `dgApplyBatch` on `levelGraphs[idx]` (`gPtr`)
  have hGAt6 : DynGraphAt s6.mem gPtr vCap eCap (ch.G idx) :=
    dynGraphAt_of_agree hGAt (fun a ha1 ha2 =>
      hResp6.2.2.2.1 a (by omega) (hDisjG a ha1 ha2).1)
  have hDisjB' (a : ℕ) (ha1 : curBatch ≤ a) (ha2 : a < curBatch + curBatchWords) :
      ¬ Rcore.foot coreH coreTok0 a := by
    have h := hDisjB (a - curBatch) (by omega)
    rwa [show curBatch + (a - curBatch) = a by omega] at h
  have hSmall6 : SmallBatchAt s6.mem curBatch (ch.G idx) curU curBatchWords :=
    smallBatchAt_of_agree hSmall (fun a ha1 ha2 =>
      hResp6.2.2.2.1 a (by omega) (hDisjB' a ha1 ha2))
  have hBatchW6 : ∀ t < curBatchWords, s6.mem (curBatch + t) < 2 ^ w := fun t ht => by
    rw [hResp6.2.2.2.1 (curBatch + t) (by omega) (hDisjB t ht)]; exact hBatchW t ht
  obtain ⟨bodyDG, hBodyDG, oDG, outDG, cDG, rDGBody, hPostDG, hcDG⟩ :=
    hDGApply [gPtr, curBatch, 1] s6.mem s6.pos ω
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl <;> omega)
      ⟨gPtr, curBatch, 1, rfl, hw16, by omega, by omega,
        fun i hi => by
          by_contra h
          rcases (hDisjG (curBatch + i) (by omega) (by omega)).2.2 with h' | h' <;> omega,
        hBatchW6, hSmall6.1, hBatchValid, hBatchCaps, hGAt6, Or.inl ⟨by decide, rfl⟩⟩
  obtain ⟨_, _, _, hEqDG, _, hDGAfter, hDGFr⟩ := hPostDG
  simp only [List.cons.injEq, and_true] at hEqDG
  obtain ⟨rfl, rfl, rfl⟩ := hEqDG
  have hFold1 : curU.foldl (dgBatchTarget 1) (ch.G idx) = curG := by
    have hfun : dgBatchTarget 1 = MGraph.applyUpdate := by funext H u; simp [dgBatchTarget]
    rw [hfun]; rfl
  have hDGCur : DynGraphAt outDG.mem gPtr vCap eCap curG := hFold1 ▸ hDGAfter
  let s7 : State :=
    { regs := Function.update s6.regs 15 oDG.value, mem := outDG.mem, pos := outDG.pos }
  have r7 : Runs w p ω (.call 15 dgApply [.reg 6, .reg 10, .const 1]) s6 .normal s7
      (3 + cDG + 1) :=
    runs_call_iff.mpr ⟨[gPtr, curBatch, 1], bodyDG, oDG, outDG, cDG,
      by simp [evalArgs, Expr.eval, hs6_regs 6 (by decide), hs6_regs 10 (by decide),
        s5c, s5b, s5a, s5, s4, s3, s2, s1, hr10, show 1 < 2 ^ w by omega],
      hBodyDG, rDGBody, rfl, rfl, by simp [argsSize, Expr.size]⟩
  -- Step 4: add `curU.length` to `updCount[idx]`
  have hCurLen7 : outDG.mem curBatch = curU.length := by
    have := hSmall6.1.1
    have hne : curBatch < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ curBatch := by
      by_contra h
      rcases (hDisjG curBatch (by omega) (by omega)).2.2 with h' | h' <;> omega
    exact (hDGFr curBatch hne).trans hSmall6.1.2.1
  have hUC7 : s7.mem (updCountBase + idx) = ch.updCount idx := by
    have hne : updCountBase + idx < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ updCountBase + idx := by
      by_contra h
      exact (hDisjG _ (by omega) (by omega)).2.1 rfl
    exact (hDGFr _ hne).trans ((hResp6.2.2.2.1 _ hUCLt hUCFoot).trans hUCCell)
  let s8 := { s7 with regs := Function.update s7.regs 16 curU.length }
  let s9 := { s8 with regs := Function.update s8.regs 17 (updCountBase + idx) }
  let s10 := { s9 with
    mem := Function.update s9.mem (updCountBase + idx) (ch.updCount idx + curU.length) }
  have r8 : Runs w p ω (.assign 16 (.load (.reg 10))) s7 .normal s8 3 :=
    runs_assign_iff.mpr ⟨curU.length, by
      simp [Expr.eval, s7, hs6_regs 10 (by decide), s5c, s5b, s5a, s5, s4, s3, s2, s1, hr10,
        hCurLen7], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 17 (.bin .add (.reg 85) (.reg 96))) s8 .normal s9 4 :=
    runs_assign_iff.mpr ⟨updCountBase + idx, by
      simp [Expr.eval, BinOp.eval, s8, s7, hs6_regs 85 (by decide), hs6_regs 96 (by decide),
        s5c, s5b, s5a, s5, s4, s3, s2, s1, hr85, hr96, show updCountBase + idx < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.store (.reg 17) (.bin .add (.load (.reg 17)) (.reg 16))) s9 .normal s10
      6 :=
    runs_store_iff.mpr ⟨updCountBase + idx, ch.updCount idx + curU.length,
      by simp [Expr.eval, s9],
      by simp [Expr.eval, BinOp.eval, s9, s8, hUC7, hUCW], rfl, rfl, rfl⟩
  -- The memory from `curHeap` on is that of op `0`.
  have hs10_eq6_ge (a : ℕ) (ha : curHeap ≤ a) : s10.mem a = s6.mem a := by
    change Function.update outDG.mem (updCountBase + idx) _ a = s6.mem a
    rw [Function.update_of_ne (by omega), hDGFr a (Or.inr (by omega))]
  have hBO10 : BranchOutAt s10.mem curHeap cfg.P.k (cfg.T.S (ch.scState idx)) upd.2
      (cfg.T.rot (ch.scState idx)) (cfg.T.rot sc') := by
    refine ⟨(hs10_eq6_ge curHeap le_rfl).trans hBO6.1, fun j hj => ?_⟩
    obtain ⟨hSB, eds, hEd, hAp⟩ := hBO6.2 j hj
    obtain ⟨_, hbLo, _, heLo, _, _, _, _, _, _, _⟩ := hSlots6 j hj
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
      have hne2 : a < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ a := by
        by_contra h; exact (hDisjG a (by omega) (by omega)).1 h0
      change s6.mem a = Function.update outDG.mem (updCountBase + idx) _ a
      rw [Function.update_of_ne hne1, hDGFr a hne2]
    · exact (hs10_eq6_ge a hlo).symm)
  have hRep10 : Rcore.rep coreH aNext tok1 s10.mem := hLoc10.1 hRep6
  have hPhi10 : Rcore.phi coreH tok1 s10.mem = Rcore.phi coreH tok1 s6.mem := hLoc10.2.symm
  -- Step 5: `ordLoadBranchOutStmt ;; .assign 4 (.reg 5)`
  obtain ⟨hBOEnd, hbPLo, hbPHi, hePLo, hePHi, hbPW, hePW, hbPFoot, hePFoot, hNextDec6, hEWle⟩ :=
    hSlots6 (ch.bran idx) hBrLt
  obtain ⟨s11, r11, hs11Mem, _, hNextSB11, ⟨nextEdits, hNextOE11, hNextRot11⟩, hs11_regs⟩ :=
    ordLoadBranchOut_runs (w := w) (branchOutAddr := curHeap) (k := cfg.P.k) (j := ch.bran idx)
      (p := p) (st := s10) (ω := ω)
      (by simp [s10, s9, s8, s7, hs6_regs 2 (by decide), s5c, s5b, s5a, s5, s4, s3, s2])
      (by simp [s10, s9, s8, s7, hs6_regs 4 (by decide), s5c, s5b, s5a, s5, s4, s3, s2, s1, hr4])
      hBrLt hBO10 (by omega) (by omega)
  let s12 := { s11 with regs := Function.update s11.regs 4 h1 }
  have r12 : Runs w p ω (.assign 4 (.reg 5)) s11 .normal s12 2 :=
    runs_assign_iff.mpr ⟨h1, by
      simp [Expr.eval, hs11_regs 5 (by decide) (by decide) (by decide) (by decide) (by decide),
        s10, s9, s8, s7, hs6_5], rfl, rfl, rfl⟩
  set boBase := curHeap + 1 + 4 * ch.bran idx
  obtain ⟨hs11_10', hs11_11', hs11_12', hs11_13'⟩ :=
    ordLoadBranchOut_regs_eq (branchOutAddr := curHeap) (j := ch.bran idx) r11
      (by simp [s10, s9, s8, s7, hs6_regs 2 (by decide), s5c, s5b, s5a, s5, s4, s3, s2])
      (by simp [s10, s9, s8, s7, hs6_regs 4 (by decide), s5c, s5b, s5a, s5, s4, s3, s2, s1, hr4])
      (by omega) (by omega)
  have hs12_eq10 : s12.mem = s10.mem := hs11Mem
  have hs12_regs_keep (r : ℕ) (h4 : r ≠ 4) (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12)
      (h13 : r ≠ 13) (h14 : r ≠ 14) (h15 : r ≠ 15) (h16 : r ≠ 16) (h17 : r ≠ 17)
      (h5 : r ≠ 5) : s12.regs r = s5c.regs r := by
    simp only [s12, Function.update_of_ne h4]
    rw [hs11_regs r h10 h11 h12 h13 h14]
    simp only [s10, s9, s8, s7, Function.update_of_ne h17, Function.update_of_ne h16,
      Function.update_of_ne h15]
    exact hs6_regs r h5
  have rAll := runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 7, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 2, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s5a, 2, _, r5a,
    runs_seq_iff.mpr (Or.inr ⟨s5b, 2, _, r5b,
    runs_seq_iff.mpr (Or.inr ⟨s5c, 2, _, r5c,
    runs_seq_iff.mpr (Or.inr ⟨s6, cUpd, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 3 + cDG + 1, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 3, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 4, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 6, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, 30, 2, r11, r12, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- The facts at `s12`.
  have hBaseEq (i : ℕ) (hi : i < 4) : s12.mem (boBase + i) = s6.mem (boBase + i) := by
    rw [hs12_eq10]; exact hs10_eq6_ge _ (by omega)
  have hNextSB6 : SmallBatchAt s6.mem (s6.mem boBase) (cfg.T.S (ch.scState idx) (ch.bran idx))
      nextU (s6.mem (boBase + 1)) := by
    have h := (hBO6.2 (ch.bran idx) hBrLt).1
    simpa only [boBase, Nat.add_assoc, show 1 + (4 * ch.bran idx + 1) = 2 + 4 * ch.bran idx by
      omega] using h
  have hb0 := hBaseEq 0 (by omega)
  have hb1 := hBaseEq 1 (by omega)
  have hb2 := hBaseEq 2 (by omega)
  have hb3 := hBaseEq 3 (by omega)
  simp only [Nat.add_zero] at hb0
  have hag12 (a : ℕ) (ha : curHeap ≤ a) : s12.mem a = s6.mem a := by
    rw [hs12_eq10]; exact hs10_eq6_ge a ha
  have hOE6 : OrdEditsAt s6.mem (s6.mem (boBase + 2)) nextEdits (s6.mem (boBase + 3)) := by
    have h := hNextOE11
    rw [hs11_12', hs11_13'] at h
    rw [hs11Mem, ← hs12_eq10, hb2, hb3] at h
    exact ordEditsAt_of_agree h (fun a ha1 _ => (hag12 a (hePLo.trans ha1)).symm)
  have hEdEq : readOrdEdits s6.mem (s6.mem (boBase + 2)) = nextEdits := hOE6.1
  have hFor6b := hFor6 (ch.bran idx) hBrLt
  have hVal6b := hVal6 (ch.bran idx) hBrLt
  simp only [show curHeap + 3 + 4 * ch.bran idx = boBase + 2 by omega, hEdEq] at hFor6b hVal6b
  have hFrame12 (a : ℕ) (ha : a < curHeap) (hnf : ¬ Rcore.foot coreH coreTok0 a)
      (hng : a < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ a) (hnu : a ≠ updCountBase + idx) :
      s12.mem a = st.mem a := by
    rw [hs12_eq10]
    change Function.update outDG.mem (updCountBase + idx) _ a = st.mem a
    rw [Function.update_of_ne hnu, hDGFr a hng, hResp6.2.2.2.1 a ha hnf]
  have hKeep (r : ℕ) (hr : 70 ≤ r) : s12.regs r = st.regs r :=
    (hs12_regs_keep r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)).trans
      (hs5c_regs r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega))
  have hRj (r : ℕ) (hr : r ≠ 4) : s12.regs r = s11.regs r := by
    simp only [s12, Function.update_of_ne hr]
  have hR10 : s12.regs 10 = s12.mem boBase := by
    rw [hRj 10 (by decide), hs12_eq10]; exact hs11_10'
  have hR11 : s12.regs 11 = s12.mem (boBase + 1) := by
    rw [hRj 11 (by decide), hs12_eq10]; exact hs11_11'
  have hR12 : s12.regs 12 = s12.mem (boBase + 2) := by
    rw [hRj 12 (by decide), hs12_eq10]; exact hs11_12'
  have hR13 : s12.regs 13 = s12.mem (boBase + 3) := by
    rw [hRj 13 (by decide), hs12_eq10]; exact hs11_13'
  have hReembB := hReemb6 (ch.bran idx) hBrLt
  have hPlB := hPl6 (ch.bran idx) hBrLt
  have hChgEnd := hFChg6.1
  have hRp0 : s12.mem (curHeap + 1 + 4 * cfg.P.k + 2 * ch.bran idx) =
      s6.mem (curHeap + 1 + 4 * cfg.P.k + 2 * ch.bran idx) := hag12 _ (by omega)
  have hRp1 : s12.mem (curHeap + 2 + 4 * cfg.P.k + 2 * ch.bran idx) =
      s6.mem (curHeap + 2 + 4 * cfg.P.k + 2 * ch.bran idx) := hag12 _ (by omega)
  refine ⟨s12, _, h1, tok1, rAll, by simp [s12], hh1Lo, hh1Hi,
    (hs12_regs_keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans
      (by simp [s5c, s5b, s5a, s5, s4, s3, s2]),
    (hs12_regs_keep 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans
      (by simp [s5c, s5b, s5a, s5, s4, s3, s2, s1]),
    (hs12_regs_keep 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans (by simp [s5c, s5b, s5a, s5, s4, s3]),
    (hs12_regs_keep 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans (by simp [s5c, s5b, s5a, s5, s4]),
    (hs12_regs_keep 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans (by simp [s5c, s5b, s5a]),
    (hs12_regs_keep 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans (by simp [s5c, s5b]),
    (hs12_regs_keep 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans (by simp [s5c]),
    hR10, hR11, hR12, hR13, hKeep,
    fun a ha => by rw [hag12 a (by omega)]; exact hResp6.2.2.1 a ha,
    hs12_eq10 ▸ hRep10, hIn6, hFoot1,
    dynGraphAt_of_agree hDGCur (fun a ha1 ha2 => by
      rw [hs12_eq10]
      change Function.update outDG.mem (updCountBase + idx) _ a = outDG.mem a
      rw [Function.update_of_ne (hDisjG a ha1 ha2).2.1]),
    by rw [hs12_eq10]; simp [s10],
    by
      rw [hb0, hb1]
      exact smallBatchAt_of_agree hNextSB6 (fun a ha1 _ => hag12 a (by omega)),
    by
      rw [hb0]
      exact decodeBatch_of_agree hNextSB6.1 hNextDec6 (fun t _ => hag12 _ (by omega)),
    ⟨nextEdits, by
      rw [hb2, hb3]
      exact ordEditsAt_of_agree hOE6 (fun a ha1 _ => hag12 a (by omega)),
      hNextRot11, hFor6b, hVal6b⟩,
    hBOEnd, by rw [hb0]; exact hbPLo, by rw [hb0, hb1]; exact hbPHi,
    by rw [hb2]; exact hePLo, by rw [hb2, hb3]; exact hePHi,
    fun t ht => by
      rw [hb1] at ht
      rw [hb0, hag12 _ (by omega)]
      exact ⟨hbPW t ht, hbPFoot t ht⟩,
    fun t ht => by
      rw [hb3] at ht
      rw [hb2, hag12 _ (by omega)]
      exact ⟨hePW t ht, hePFoot t ht⟩,
    by rw [hb3]; exact hEWle,
    branchOutFChgAt_of_agree hFChg6 (fun a ha _ => hag12 a ha),
    by
      rw [hRp0, hRp1]
      exact ⟨hReembB.1, listAt_of_agree hReembB.2 fun t ht => hag12 _ (by omega)⟩,
    by rw [hRp0]; exact hPlB.1, by rw [hRp0, hRp1]; exact hPlB.2,
    hFrame12, ?_⟩
  have hcDG' : cDG ≤ 670 * curBatchWords + 30 := hcDG
  have hc6' : cUpd + Rcore.phi coreH tok1 s6.mem ≤
      Psc.mul * (cfg.T.cost sc' - cfg.T.cost (ch.scState idx) +
        (cfg.P.k + 1) * (curBatchWords + curEditsWords + 1) * SparseCore.bundleLogFactor M N) +
      Rcore.phi coreH coreTok0 st.mem + 10 := hc6
  have hPhi12 : Rcore.phi coreH tok1 s12.mem = Rcore.phi coreH tok1 s6.mem := by
    rw [hs12_eq10]; exact hPhi10
  clear hc6 hcDG rAll r12 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 hBO6 hBO10 hNextSB11 hNextOE11 hRep10 hRep6
    hDGCur hDGAfter hGAt6 hSmall6 hPre0 hNextSB6
  omega

end MinCostFlow.MinRatio
