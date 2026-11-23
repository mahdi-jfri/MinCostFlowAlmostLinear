module

public import MinCostFlow.MinRatio.SelectUpdateNonRebuilt
public import MinCostFlow.MinRatio.SelectUpdateModel
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Non-rebuilt prefix `F`, `φ`, and `len` update (`SelectUpdateFPhiLen`)

Runs the `op 4`-free part of non-rebuilt level maintenance (`dgApplyBatch`, `delEdgeList`,
`batchCopySplits`, `filterPres`, `coreLenFill`) across all non-rebuilt interior levels
`j = cur .. limit - 1` (`limit = min firstReb d ≤ d`).

Because this pass never invokes sparse-core readout `op 4`, it writes only inside `[B.base, B.endAddr)`
and `[scratch, scOut)`, leaving the entire solver footprint `Rrep.foot` and all stretch tables of
`UpdateCoreSelectOutAt` completely untouched across all levels.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore MinCostFlow.SparseCore.Program

/-- Space bound for one level of `selectUpdateFPhiLenLevelBody`. -/
def selectUpdateFPhiLenSpace (uGLen Lk Lw : ℕ) : ℕ :=
  uGLen + uGLen * selCoreLenEdgeSpace Lk Lw

/-- Cost bound for one level of `selectUpdateFPhiLenLevelBody`. -/
def selectUpdateFPhiLenCost (uWords uLen uGLen fDelLen Lk Lw : ℕ) : ℕ :=
  (670 * uWords + 30) +
  (fDelLen * 490 + 20) +
  (uLen * (18 * Lk + 130) + 40) +
  (40 * uGLen + 20) +
  (uGLen * (selCoreLenEdgeCost Lk Lw + 40) + 20) + 260

/-- Update `F j`, `φ j`, and `len j` for one non-rebuilt level `j < B.d` without calling `op 4`.
Arguments: `[metaBase, j, slot, prevLen, Lk, scratch]` (`reg 0..5`). Returns `scOut`. -/
def selectUpdateFPhiLenLevelBody (dgApplyBatch delEdgeList batchCopySplits filterPres
    coreLenFill : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 7 (.bin .add (.reg 6) (.const 1)) ;;
  .assign 8 (.bin .add (.reg 0) (.const smTableOff)) ;;
  .assign 9 (.load (.bin .add (.reg 8) (.reg 1))) ;;
  .assign 10 (.load (.bin .add (.bin .add (.reg 8) (.reg 7)) (.reg 1))) ;;
  .assign 11 (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 3) (.reg 7))) (.reg 1))) ;;
  .assign 12 (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 4) (.reg 7))) (.reg 1))) ;;
  .assign 13 (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 6) (.reg 7))) (.reg 1))) ;;
  .assign 14 (.bin .add (.bin .add (.reg 9) (.const 4)) (.bin .mul (.const 7) (.reg 10))) ;;
  .assign 15 (.load (.reg 2)) ;;
  .assign 16 (.load (.bin .add (.reg 2) (.const 1))) ;;
  .assign 17 (.load (.bin .add (.reg 2) (.const 2))) ;;
  .assign 18 (.load (.bin .add (.reg 2) (.const 3))) ;;
  .assign 19 (.load (.bin .add (.reg 2) (.const 8))) ;;
  .assign 20 (.load (.bin .add (.reg 2) (.const 9))) ;;
  .assign 21 (.load (.bin .add (.reg 2) (.const 10))) ;;
  .assign 22 (.load (.reg 19)) ;;
  .assign 23 (.load (.bin .add (.reg 19) (.const 1))) ;;
  .call 24 dgApplyBatch [.reg 13, .reg 21, .const 0] ;;
  .call 24 delEdgeList [.reg 13, .reg 17, .reg 18] ;;
  .call 24 batchCopySplits [.reg 21, .reg 11, .reg 4] ;;
  .call 25 filterPres [.reg 15, .reg 16, .reg 14, .reg 5] ;;
  .assign 26 (.bin .add (.reg 5) (.reg 16)) ;;
  .call 27 coreLenFill
    [.reg 3, .reg 22, .reg 23, .reg 12, .reg 5, .reg 25, .reg 4, .reg 20, .const 0, .reg 26] ;;
  .ret (.reg 27)

theorem selectUpdateFPhiLenLevelBody_noRand (dgApplyBatch delEdgeList batchCopySplits
    filterPres coreLenFill : ℕ) :
    (selectUpdateFPhiLenLevelBody dgApplyBatch delEdgeList batchCopySplits filterPres
      coreLenFill).NoRand := by
  simp [selectUpdateFPhiLenLevelBody, Stmt.NoRand]

/-- Recursive loop calling `selectUpdateFPhiLenLevelBody` for levels `cur .. limit - 1`.
Arguments: `[metaBase, cur, limit, lvlMeta, selOutBase, d, Lk, scratch]` (`reg 0..7`). -/
def selectUpdateFPhiLenLoopBody (self lvlProc : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 1) (.reg 2))
    (.assign 8 (.bin .add (.bin .add (.reg 4) (.const 1)) (.bin .mul (.const 12) (.reg 1))) ;;
     .cond (.reg 1)
       (.assign 9 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const smTableOff))
         (.bin .mul (.const 4) (.bin .add (.reg 5) (.const 1))))
         (.bin .sub (.reg 1) (.const 1)))))
       (.assign 9 (.load (.reg 3))) ;;
     .call 10 lvlProc [.reg 0, .reg 1, .reg 8, .reg 9, .reg 6, .reg 7] ;;
     .call 11 self [.reg 0, .bin .add (.reg 1) (.const 1), .reg 2, .reg 3, .reg 4, .reg 5,
       .reg 6, .reg 10] ;;
     .ret (.reg 11))
    (.ret (.reg 7))

theorem selectUpdateFPhiLenLoopBody_noRand (self lvlProc : ℕ) :
    (selectUpdateFPhiLenLoopBody self lvlProc).NoRand := by
  simp [selectUpdateFPhiLenLoopBody, Stmt.NoRand]

/-- Scratch space for `selectUpdateFPhiLenLoopBody` over levels `cur .. limit - 1`. -/
def selectUpdateFPhiLenLoopSpace (diffLists : ℕ → LevelDiffLists) (stLw : ℕ → ℕ)
    (cur limit Lk : ℕ) : ℕ :=
  (Finset.Ico cur limit).sum fun j =>
    selectUpdateFPhiLenSpace (diffLists j).uG.length Lk (stLw j)

/-- Step cost for `selectUpdateFPhiLenLoopBody` over levels `cur .. limit - 1`. -/
def selectUpdateFPhiLenLoopCost (levelU : ℕ → List Update) (uWords : ℕ → ℕ)
    (diffLists : ℕ → LevelDiffLists) (stLw : ℕ → ℕ) (cur limit Lk : ℕ) : ℕ :=
  (Finset.Ico cur limit).sum (fun j =>
    selectUpdateFPhiLenCost (uWords j) (levelU j).length (diffLists j).uG.length
      (diffLists j).fDel.length Lk (stLw j) + 70) + 10

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore MinCostFlow.SparseCore.Program

private lemma ent_end_fp {e eCap L : ℕ} (he : e < eCap) : e * L + L ≤ eCap * L := by
  have h := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
  rwa [Nat.succ_mul] at h

private lemma regBlk_le_end_fp {B : SelectBlocksLoc} {j a : ℕ} (hj : j ≤ B.d)
    (h : B.regBlk j a) : B.base ≤ a ∧ a < B.endAddr := by
  have h1 : B.base ≤ B.fPtr j := by unfold SelectBlocksLoc.fPtr; omega
  have h2 := B.blk_le_last hj
  have h3 : B.lastGPtr ≤ B.endAddr := by
    unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  unfold SelectBlocksLoc.regBlk at h
  omega

private lemma lenPtr_prev_le_fPtr_fp {B : SelectBlocksLoc} {j : ℕ} (hj : 0 < j) :
    B.lenPtr (j - 1) + B.eCap * B.Lk ≤ B.fPtr j := by
  have h1 : B.lenPtr (j - 1) + B.eCap * B.Lk ≤ B.fPtr (j - 1) + B.levelSize := by
    unfold SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr SelectBlocksLoc.levelSize
    omega
  have h2 : B.fPtr (j - 1) + B.levelSize = B.fPtr j := by
    unfold SelectBlocksLoc.fPtr
    cases j with
    | zero => omega
    | succ k => simp [Nat.succ_mul]; omega
  omega

private lemma runs_seq_call_c {w r f : ℕ} {args : List Expr} {s2 : Stmt}
    {p : Program} {ω : ℕ → Bool} {st st1 : State} {o1 : Outcome} {vs : List ℕ}
    {body : Stmt} {c1 k T : ℕ} {Q : Outcome → State → Prop}
    (hvs : evalArgs w st args = some vs) (hbody : p.procs[f]? = some body)
    (hr1 : Runs w p ω body (startState vs st.mem st.pos) o1 st1 c1)
    (h2 : ∃ o st2 c2, Runs w p ω s2 ⟨st1.mem, Function.update st.regs r o1.value, st1.pos⟩ o st2 c2 ∧
      Q o st2 ∧ (k + (argsSize args + c1 + 2)) + c2 ≤ T) :
    ∃ o st2 c, Runs w p ω (.seq (.call r f args) s2) st o st2 c ∧ Q o st2 ∧ k + c ≤ T := by
  obtain ⟨o, st2, c2, hr2, hq, hc⟩ := h2
  exact ⟨o, st2, (argsSize args + c1 + 1) + c2 + 1,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _,
      runs_call_iff.mpr ⟨vs, body, o1, st1, c1, hvs, hbody, hr1, rfl, rfl, rfl⟩, hr2, rfl⟩), hq, by omega⟩

set_option maxHeartbeats 1000000 in
/-- Verification of `selectUpdateFPhiLenLevelBody`: updates `F j`, `V j`, `φ j`, `E j`, and
`len j` in `SelBlocksDataAt` while preserving all memory `< scratch` outside `B.regBlk j`. -/
theorem selectUpdateFPhiLenLevel_runs
    {w P j pLast prevLen slot uPtr uWords stDesc stLw scratch pos : ℕ}
    {dgApplyBatch delEdgeList batchCopySplits filterPres coreLenFill coreLenEdge : ℕ}
    {oldG newG newF : MGraph} {wstr prevVal : ℕ → ℝ} {p : Program} {ω : ℕ → Bool}
    {B : SelectBlocksLoc} {metaBase : ℕ} {solverG : ℕ → ℕ} {D : SelBlocksData}
    {U : List Update} {L : LevelDiffLists} {mem : ℕ → ℕ}
    (hw16 : 16 < 2 ^ w) (hLkW : B.Lk < 2 ^ w) (hj : j < B.d) (hStLwW : stLw < 2 ^ w)
    (htab : SelectMetaTableAt mem (selectMlocOf B metaBase solverG pLast))
    (hblk : SelBlocksDataAt mem B P D pLast)
    (hMetaLe : metaBase + selectLevelMetaSize B.d ≤ scratch)
    (hBEnd : B.endAddr ≤ scratch)
    (hG : DynGraphAt mem (solverG j) B.vCap B.eCap newG)
    (hGLe : solverG j + dynGraphSize B.vCap B.eCap ≤ scratch)
    (hGOffBlk : solverG j + dynGraphSize B.vCap B.eCap ≤ B.fPtr j ∨
      B.fPtr j + B.levelSize ≤ solverG j)
    (hDiff : LevelDiffListsAt mem slot L)
    (hSlotMeta : mem (slot + 8) = stDesc ∧ mem (slot + 9) = stLw ∧ mem (slot + 10) = uPtr)
    (hSlotLe : slot + 12 ≤ scratch)
    (hUGLe : mem (slot + 0) + L.uG.length ≤ scratch)
    (hUGOffBlk : mem (slot + 0) + L.uG.length ≤ B.fPtr j ∨ B.fPtr j + B.levelSize ≤ mem (slot + 0))
    (hFDelLe : mem (slot + 2) + L.fDel.length ≤ scratch)
    (hFDelOffBlk : mem (slot + 2) + L.fDel.length ≤ B.fPtr j ∨ B.fPtr j + B.levelSize ≤ mem (slot + 2))
    (hBatch : BatchAt mem uPtr oldG U uWords)
    (hBatchWords : ∀ i < uWords, mem (uPtr + i) < 2 ^ w)
    (hULe : uPtr + uWords ≤ scratch)
    (hUOffBlk : uPtr + uWords ≤ B.fPtr j ∨ B.fPtr j + B.levelSize ≤ uPtr)
    (hStDescLe : stDesc + 2 ≤ scratch)
    (hStBaseW : mem stDesc < 2 ^ w ∧ mem (stDesc + 1) < 2 ^ w)
    (hStretch : StretchValuesAt mem stDesc 4 stLw P newG.E wstr)
    (hNumBound : ∀ e ∈ newG.E, mem stDesc + e * stLw + stLw ≤ scratch ∧
      (mem stDesc + e * stLw + stLw ≤ B.fPtr j ∨ B.fPtr j + B.levelSize ≤ mem stDesc + e * stLw))
    (hDenBound : ∀ e ∈ newG.E, mem (stDesc + 1) + e * stLw + stLw ≤ scratch ∧
      (mem (stDesc + 1) + e * stLw + stLw ≤ B.fPtr j ∨ B.fPtr j + B.levelSize ≤ mem (stDesc + 1) + e * stLw))
    (hPrevLe : prevLen + B.eCap * B.Lk ≤ scratch)
    (hPrevOffBlk : prevLen + B.eCap * B.Lk ≤ B.fPtr j ∨ B.fPtr j + B.levelSize ≤ prevLen)
    (hPrevVal : EdgeValuesAt mem prevLen 4 B.Lk P newG.E prevVal)
    (hOldV : D.V j = oldG.V)
    (hNewG : newG = oldG.applyBatch U)
    (hBV : oldG.BatchIsValid U)
    (hCapsU : BatchWithinCaps B.vCap B.eCap U)
    (hOldFSub : oldG.IsSubgraph (D.F j))
    (hOldFV : (D.F j).V = oldG.V)
    (hNewFSub : newG.IsSubgraph newF)
    (hNewFV : newF.V = newG.V)
    (hNewFSubOld : newF.E ⊆ (D.F j).E)
    (hNewFNoDel : ∀ e ∈ newF.E, Update.delete e ∉ U)
    (hFDelEq : L.fDel.toFinset = (D.F j).E \ newF.E)
    (hListCaps : (∀ e ∈ L.uG, e < B.eCap) ∧ (∀ e ∈ L.fDel, e < B.eCap))
    (hLenUnchanged : ∀ e ∈ newG.E, e ∉ L.uG → e ∈ D.E j ∧ wstr e * prevVal e = D.len j e)
    (hLenFit : ∀ e ∈ newG.E,
      ∃ q : ℤ, Num.Fits 4 B.Lk q ∧ (q : ℝ) / (2 : ℝ) ^ P = wstr e * prevVal e)
    (hDgBatch : MeetsContract w p dgApplyBatch
      (dgApplyBatchContract w B.vCap B.eCap oldG (D.F j) U uWords))
    (hDelList : MeetsContract w p delEdgeList
      (dgDeleteEdgeListContract w B.vCap B.eCap (U.foldl (dgBatchTarget 0) (D.F j)) L.fDel))
    (hSplits : MeetsContract w p batchCopySplits
      (selBatchCopySplitsContract w B.vCap P oldG U uWords (D.φ j)))
    (hFilterPres : MeetsContract w p filterPres (selFilterPresentContract w L.uG))
    (hpCoreLen : p.procs[coreLenFill]? = some (selCoreLenFillBody coreLenEdge))
    (hCoreLenEdge : MeetsContract w p coreLenEdge (selCoreLenEdgeContract w P))
    (hz : ZeroFrom mem scratch)
    (hroom : scratch + selectUpdateFPhiLenSpace L.uG.length B.Lk stLw < 2 ^ w) :
    ∃ scOut cost out,
      Runs w p ω
        (selectUpdateFPhiLenLevelBody dgApplyBatch delEdgeList batchCopySplits filterPres coreLenFill)
        (startState [metaBase, j, slot, prevLen, B.Lk, scratch] mem pos)
        (.returned scOut) out cost ∧
      scratch ≤ scOut ∧
      scOut ≤ scratch + selectUpdateFPhiLenSpace L.uG.length B.Lk stLw ∧
      SelBlocksDataAt out.mem B P
        { D with
          F := Function.update D.F j newF
          V := Function.update D.V j newG.V
          φ := Function.update D.φ j (splitPot (D.φ j) (batchSplits U))
          E := Function.update D.E j newG.E
          len := Function.update D.len j (fun e => wstr e * prevVal e) } pLast ∧
      ZeroFrom out.mem scOut ∧
      (∀ a < scratch, ¬ B.regBlk j a → out.mem a = mem a) ∧
      cost ≤ selectUpdateFPhiLenCost uWords U.length L.uG.length L.fDel.length B.Lk stLw := by
  have hjLe : j ≤ B.d := Nat.le_of_lt hj
  have hBEndBlk : B.fPtr j + B.levelSize ≤ B.endAddr := by
    have h1 := B.blk_le_last hjLe
    have h2 : B.lastGPtr ≤ B.endAddr := by unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
    omega
  have hBaseLeF : B.base ≤ B.fPtr j := by unfold SelectBlocksLoc.fPtr; omega
  have hFEnd : B.fPtr j + dynGraphSize B.vCap B.eCap ≤ B.fPtr j + B.levelSize := by
    unfold SelectBlocksLoc.levelSize; omega
  have hPhiGe : B.fPtr j + dynGraphSize B.vCap B.eCap = B.phiPtr j := rfl
  have hPhiEnd : B.phiPtr j + B.vCap * B.Lk = B.lenPtr j := rfl
  have hLenEnd : B.lenPtr j + B.eCap * B.Lk = B.embPtr j := rfl
  have hEmbEnd : B.embPtr j + B.eCap + B.eCap * B.slot = B.fPtr j + B.levelSize :=
    (B.blkEnd_eq j).symm
  set uGPtr := mem (slot + 0)
  set fDelPtr := mem (slot + 2)
  set numBase := mem stDesc
  set denBase := mem (stDesc + 1)
  have hUGAt : ListAt mem uGPtr L.uG := hDiff.2.1
  have hFDelAt : ListAt mem fDelPtr L.fDel := hDiff.2.2.2.1
  have hrow := htab.2.2 j hjLe
  have hdM : mem (metaBase + 1) = B.d := by simpa [smDOff, selectMlocOf] using htab.2.1
  have hgPtrM : mem (smEntryAddr metaBase B.d 0 j) = solverG j := by
    simpa [selectMlocOf, hj] using hrow.1
  have hvCapM : mem (smEntryAddr metaBase B.d 1 j) = B.vCap := by
    simpa [selectMlocOf] using hrow.2.1
  have hphiM : mem (smEntryAddr metaBase B.d 3 j) = B.phiPtr j := by
    simpa [selectMlocOf] using hrow.2.2.2.1
  have hlenM : mem (smEntryAddr metaBase B.d 4 j) = B.lenPtr j := by
    simpa [selectMlocOf] using hrow.2.2.2.2.1
  have hfM : mem (smEntryAddr metaBase B.d 6 j) = B.fPtr j := by
    simpa [selectMlocOf] using hrow.2.2.2.2.2.2.1
  have hMetaSize : selectLevelMetaSize B.d = 2 + 8 * (B.d + 1) := rfl
  have hDgSz : dynGraphSize B.vCap B.eCap = 4 + 7 * B.vCap + 9 * B.eCap := rfl
  -- Step 1: `dgApplyBatch [B.fPtr j, uPtr, 0]`
  obtain ⟨b1, hb1, o1, st1, c1, hr1, hp1, hc1⟩ :=
    hDgBatch [B.fPtr j, uPtr, 0] mem pos ω (by wram_words)
      ⟨B.fPtr j, uPtr, 0, rfl, by omega, by omega, by omega,
        fun i hi => by rcases hUOffBlk with h | h <;> [left; right] <;> omega,
        hBatchWords, hBatch, hBV, hCapsU, hblk.1 j hjLe, Or.inr ⟨rfl, hOldFSub, hOldFV⟩⟩
  obtain ⟨_, _, _, hargs1, _, hFmid1, hfr1⟩ := hp1
  simp only [List.cons.injEq] at hargs1
  obtain ⟨rfl, rfl, rfl, -⟩ := hargs1
  -- Step 2: `delEdgeList [B.fPtr j, fDelPtr, L.fDel.length]`
  have hFDelAt1 : ListAt st1.mem fDelPtr L.fDel := fun i hi =>
    (hfr1 _ (by rcases hFDelOffBlk with h | h <;> [left; right] <;> omega)).trans (hFDelAt i hi)
  obtain ⟨b2, hb2, o2, st2, c2, hr2, hp2, hc2⟩ :=
    hDelList [B.fPtr j, fDelPtr, L.fDel.length] st1.mem st1.pos ω (by wram_words)
      ⟨B.fPtr j, fDelPtr, rfl, by omega, by omega, by omega,
        by rcases hFDelOffBlk with h | h <;> [left; right] <;> omega,
        hFDelAt1, fun e he => by have := hListCaps.2 e he; omega, hFmid1⟩
  obtain ⟨_, _, hargs2, _, hFout2, hfr2⟩ := hp2
  simp only [List.cons.injEq] at hargs2
  obtain ⟨rfl, rfl, -⟩ := hargs2
  have hNewF2 : DynGraphAt st2.mem (B.fPtr j) B.vCap B.eCap newF :=
    dgApplyBatch_allowZero_and_deleteList_eq hBV hOldFSub hOldFV (hNewG ▸ hNewFSub)
      (hNewG ▸ hNewFV) hNewFSubOld hNewFNoDel hFDelEq hFout2
  have hfr12 : ∀ a, ¬ B.regF j a → st2.mem a = mem a := fun a ha => by
    unfold SelectBlocksLoc.regF at ha
    rw [hfr2 a (by omega), hfr1 a (by omega)]
  have hblk2 : SelBlocksDataAt st2.mem B P { D with F := Function.update D.F j newF } pLast :=
    hblk.setF hjLe hfr12 hNewF2
  -- Step 3: `batchCopySplits [uPtr, B.phiPtr j, B.Lk]`
  have hBatch2 : BatchAt st2.mem uPtr oldG U uWords :=
    hBatch.of_agree fun i hi => hfr12 _ (by
      unfold SelectBlocksLoc.regF; rcases hUOffBlk with h | h <;> omega)
  have hPhi2 := hblk2.2.1 j hjLe
  obtain ⟨b3, hb3, o3, st3, c3, hr3, hp3, hc3⟩ :=
    hSplits [uPtr, B.phiPtr j, B.Lk] st2.mem st2.pos ω (by wram_words)
      ⟨uPtr, B.phiPtr j, B.Lk, rfl, hw16, by omega, by omega, by omega,
        by rcases hUOffBlk with h | h <;> [left; right] <;> omega,
        hBatch2, hBV, fun u hu => by
          have hc := hCapsU u hu
          cases u with | insert _ _ _ => trivial | delete _ => trivial | split _ _ _ _ => exact hc,
        hOldV ▸ hPhi2.1, hOldV ▸ hPhi2.2⟩
  have hp3' := hp3
  obtain ⟨_, _, _, hargs3, _, _, _, hfr3⟩ := hp3
  simp only [List.cons.injEq] at hargs3
  obtain ⟨rfl, rfl, rfl, -⟩ := hargs3
  have hblk3 : SelBlocksDataAt st3.mem B P
      { D with
        F := Function.update D.F j newF
        V := Function.update D.V j newG.V
        φ := Function.update D.φ j (splitPot (D.φ j) (batchSplits U)) } pLast := by
    simpa only [← hNewG] using selBatchCopySplits_setPhi hjLe hblk2 hp3'
  have hfr13 : ∀ a, ¬ B.regBlk j a → st3.mem a = mem a := fun a ha => by
    unfold SelectBlocksLoc.regBlk at ha
    rw [hfr3 a (by omega), hfr12 a (by unfold SelectBlocksLoc.regF; omega)]
  -- Step 4: `filterPres [uGPtr, L.uG.length, dgEPresBase (solverG j) B.vCap, scratch]`
  have hG3 : DynGraphAt st3.mem (solverG j) B.vCap B.eCap newG :=
    hG.of_agree fun a _ _ => hfr13 a (by unfold SelectBlocksLoc.regBlk; rcases hGOffBlk with h | h <;> omega)
  have hUGAt3 : ListAt st3.mem uGPtr L.uG := fun i hi =>
    (hfr13 _ (by unfold SelectBlocksLoc.regBlk; rcases hUGOffBlk with h | h <;> omega)).trans (hUGAt i hi)
  obtain ⟨b4, hb4, o4, st4, c4, hr4, hp4, hc4⟩ :=
    hFilterPres [uGPtr, L.uG.length, dgEPresBase (solverG j) B.vCap, scratch] st3.mem st3.pos ω
      (by unfold dgEPresBase; wram_words)
      ⟨uGPtr, dgEPresBase (solverG j) B.vCap, scratch, rfl, hw16, by omega,
        by unfold selectUpdateFPhiLenSpace at hroom; omega,
        Or.inl hUGLe, hUGAt3, fun e he => by
          have heCap := hListCaps.1 e he
          have hbit := hG3.2.2.2.2.2.2.2.2.2.2.2.1 e heCap
          refine ⟨by omega, by unfold dgEPresBase; omega, ?_, Or.inl (by unfold dgEPresBase; omega)⟩
          by_cases hE : e ∈ newG.E <;> simp [hE] at hbit <;> omega⟩
  obtain ⟨_, _, _, hargs4, hcnt4, hSurvAt4, hfr4⟩ := hp4
  simp only [List.cons.injEq] at hargs4
  obtain ⟨rfl, -, rfl, rfl, -⟩ := hargs4
  set survUG := selPresent st3.mem (dgEPresBase (solverG j) B.vCap) L.uG
  have hSurvLenLe : survUG.length ≤ L.uG.length := selPresent_length_le _ _ _
  have hSurvMem : ∀ e, e ∈ survUG ↔ e ∈ L.uG ∧ e ∈ newG.E := fun e =>
    mem_selPresent_iff hG3 hListCaps.1 e
  have hblk4 : SelBlocksDataAt st4.mem B P
      { D with
        F := Function.update D.F j newF
        V := Function.update D.V j newG.V
        φ := Function.update D.φ j (splitPot (D.φ j) (batchSplits U)) } pLast :=
    hblk3.of_agree fun a _ ha2 => hfr4 a (Or.inl (by omega))
  have hz4 : ZeroFrom st4.mem (scratch + L.uG.length) := fun a ha =>
    (hfr4 a (Or.inr ha)).trans ((hfr13 a (by unfold SelectBlocksLoc.regBlk; omega)).trans (hz a (by omega)))
  have hSt4Ag : ∀ a < scratch, ¬ B.regBlk j a → st4.mem a = mem a := fun a ha hnb =>
    (hfr4 a (Or.inl ha)).trans (hfr13 a hnb)
  -- Step 5: `selCoreLenFill` on `survUG` at `shift = 0`
  have hSurvOk : ∀ e ∈ survUG,
      SelCoreLenEntryOk P 0 B.Lk stLw st4.mem prevLen numBase denBase e := by
    intro e he
    have heG := ((hSurvMem e).mp he).2
    have heCap := hG.2.2.1 e heG
    have hpAg : ∀ t < B.Lk, st4.mem (prevLen + e * B.Lk + t) = mem (prevLen + e * B.Lk + t) := fun t ht => by
      have hent := ent_end_fp (L := B.Lk) heCap
      exact hSt4Ag _ (by omega) (by unfold SelectBlocksLoc.regBlk; rcases hPrevOffBlk with h | h <;> omega)
    have hnAg : ∀ t < stLw, st4.mem (numBase + e * stLw + t) = mem (numBase + e * stLw + t) := fun t ht =>
      hSt4Ag _ (by have := (hNumBound e heG).1; omega)
        (by unfold SelectBlocksLoc.regBlk; rcases (hNumBound e heG).2 with h | h <;> omega)
    have hdAg : ∀ t < stLw, st4.mem (denBase + e * stLw + t) = mem (denBase + e * stLw + t) := fun t ht =>
      hSt4Ag _ (by have := (hDenBound e heG).1; omega)
        (by unfold SelectBlocksLoc.regBlk; rcases (hDenBound e heG).2 with h | h <;> omega)
    have hPv := hPrevVal e heG
    have hSv := hStretch e heG
    have hv1 : Num.Valid st4.mem (prevLen + e * B.Lk) 4 B.Lk := fun t ht => hpAg t ht ▸ hPv.1 t ht
    have hv2 : Num.Valid st4.mem (numBase + e * stLw) 4 stLw := fun t ht => hnAg t ht ▸ hSv.1 t ht
    have hv3 : Num.Valid st4.mem (denBase + e * stLw) 4 stLw := fun t ht => hdAg t ht ▸ hSv.2.1 t ht
    have hpFix : Num.fixVal st4.mem (prevLen + e * B.Lk) 4 B.Lk P = prevVal e := by
      unfold Num.fixVal; rw [Num.intVal_congr hpAg]; exact hPv.2
    have hnFix : Num.fixVal st4.mem (numBase + e * stLw) 4 stLw P =
        Num.fixVal mem (numBase + e * stLw) 4 stLw P := by
      unfold Num.fixVal; rw [Num.intVal_congr hnAg]
    have hdFix : Num.fixVal st4.mem (denBase + e * stLw) 4 stLw P =
        Num.fixVal mem (denBase + e * stLw) 4 stLw P := by
      unfold Num.fixVal; rw [Num.intVal_congr hdAg]
    obtain ⟨q, hqFit, hqVal⟩ := hLenFit e heG
    refine ⟨hv1, hv2, hv3, by rw [hdFix]; exact hSv.2.2.1,
      by simpa [pow_zero, mul_one] using Num.intVal_fits hv1, q, hqFit, ?_⟩
    unfold selCoreLenVal
    rw [hpFix, hnFix, hdFix, hSv.2.2.2]
    simpa [add_zero] using hqVal
  have hsc1Room : (scratch + L.uG.length) + survUG.length * selCoreLenEdgeSpace B.Lk stLw < 2 ^ w := by
    have := Nat.mul_le_mul_right (selCoreLenEdgeSpace B.Lk stLw) hSurvLenLe
    unfold selectUpdateFPhiLenSpace at hroom; omega
  obtain ⟨st5, c5, hr5, hc5, hLen5, hz5, hfr5, hkeep5⟩ :=
    selCoreLenFill_runs_perEdge (L_list := survUG) (dst := B.lenPtr j)
      (listPtr := scratch) (shift := 0) (heap := scratch + L.uG.length)
      (eCap := B.eCap) (pos := st4.pos) (ω := ω)
      hCoreLenEdge hw16 hLkW hStLwW (by omega) (by omega) (by omega) (by omega)
      (Or.inr (by omega)) hSurvAt4 (fun e he => hListCaps.1 e ((hSurvMem e).mp he).1)
      (fun e he => by
        have hent := ent_end_fp (L := B.Lk) (hListCaps.1 e ((hSurvMem e).mp he).1)
        exact ⟨by omega, by rcases hPrevOffBlk with h | h <;> [left; right] <;> omega⟩)
      (fun e he => by
        have h1 := hNumBound e ((hSurvMem e).mp he).2
        exact ⟨by omega, by rcases h1.2 with h | h <;> [left; right] <;> omega⟩)
      (fun e he => by
        have h1 := hDenBound e ((hSurvMem e).mp he).2
        exact ⟨by omega, by rcases h1.2 with h | h <;> [left; right] <;> omega⟩)
      hSurvOk hz4 hsc1Room
  set scOut := (scratch + L.uG.length) + survUG.length * selCoreLenEdgeSpace B.Lk stLw
  have hscOutLo : scratch ≤ scOut := by dsimp only [scOut]; omega
  have hscOutHi : scOut ≤ scratch + selectUpdateFPhiLenSpace L.uG.length B.Lk stLw := by
    have := Nat.mul_le_mul_right (selCoreLenEdgeSpace B.Lk stLw) hSurvLenLe
    unfold selectUpdateFPhiLenSpace; dsimp only [scOut]; omega
  have hPrecEq : coreLenPrec B.d P pLast j = P := by unfold coreLenPrec; simp [hj]
  have hblk5 : SelBlocksDataAt st5.mem B P
      { D with
        F := Function.update D.F j newF
        V := Function.update D.V j newG.V
        φ := Function.update D.φ j (splitPot (D.φ j) (batchSplits U))
        E := Function.update D.E j newG.E
        len := Function.update D.len j (fun e => wstr e * prevVal e) } pLast := by
    let m5b : ℕ → ℕ := fun a => if a < scratch then st5.mem a else st4.mem a
    have hLen5Part : SelPartLen m5b B P j newG.E (fun e => wstr e * prevVal e) pLast := by
      refine ⟨fun e he => hG.2.2.1 e he, fun e he => ?_⟩
      have heCap := hG.2.2.1 e he
      have hent := ent_end_fp (L := B.Lk) heCap
      have hm5Ag : ∀ t < B.Lk, m5b (B.lenPtr j + e * B.Lk + t) = st5.mem (B.lenPtr j + e * B.Lk + t) :=
        fun t ht => by simp [m5b, show B.lenPtr j + e * B.Lk + t < scratch by omega]
      by_cases heUG : e ∈ L.uG
      · have heS : e ∈ survUG := (hSurvMem e).mpr ⟨heUG, he⟩
        obtain ⟨hv, hfx⟩ := hLen5 e heS
        have hpAg : ∀ t < B.Lk, st4.mem (prevLen + e * B.Lk + t) = mem (prevLen + e * B.Lk + t) := fun t ht =>
          hSt4Ag _ (by omega) (by unfold SelectBlocksLoc.regBlk; rcases hPrevOffBlk with h | h <;> omega)
        have hnAg : ∀ t < stLw, st4.mem (numBase + e * stLw + t) = mem (numBase + e * stLw + t) := fun t ht =>
          hSt4Ag _ (by have := (hNumBound e he).1; omega)
            (by unfold SelectBlocksLoc.regBlk; rcases (hNumBound e he).2 with h | h <;> omega)
        have hdAg : ∀ t < stLw, st4.mem (denBase + e * stLw + t) = mem (denBase + e * stLw + t) := fun t ht =>
          hSt4Ag _ (by have := (hDenBound e he).1; omega)
            (by unfold SelectBlocksLoc.regBlk; rcases (hDenBound e he).2 with h | h <;> omega)
        refine ⟨fun t ht => hm5Ag t ht ▸ hv t ht, ?_⟩
        rw [hPrecEq]; unfold Num.fixVal; rw [Num.intVal_congr hm5Ag]
        have hfx0 : Num.fixVal st5.mem (B.lenPtr j + e * B.Lk) 4 B.Lk P =
            selCoreLenVal st4.mem P prevLen numBase denBase B.Lk stLw e := by
          simpa only [Nat.add_zero] using hfx
        change Num.fixVal st5.mem (B.lenPtr j + e * B.Lk) 4 B.Lk P = wstr e * prevVal e
        rw [hfx0]; unfold selCoreLenVal
        have hpF : Num.fixVal st4.mem (prevLen + e * B.Lk) 4 B.Lk P = prevVal e := by
          unfold Num.fixVal; rw [Num.intVal_congr hpAg]; exact (hPrevVal e he).2
        have hnF : Num.fixVal st4.mem (numBase + e * stLw) 4 stLw P =
            Num.fixVal mem (numBase + e * stLw) 4 stLw P := by
          unfold Num.fixVal; rw [Num.intVal_congr hnAg]
        have hdF : Num.fixVal st4.mem (denBase + e * stLw) 4 stLw P =
            Num.fixVal mem (denBase + e * stLw) 4 stLw P := by
          unfold Num.fixVal; rw [Num.intVal_congr hdAg]
        rw [hpF, hnF, hdF, (hStretch e he).2.2.2]
      · have hnotS : e ∉ survUG := fun hs => heUG ((hSurvMem e).mp hs).1
        obtain ⟨heOld, hlenEq⟩ := hLenUnchanged e he heUG
        have hold := (hblk4.2.2.1 j hjLe).2 e heOld
        have hkp : ∀ t < B.Lk, m5b (B.lenPtr j + e * B.Lk + t) = st4.mem (B.lenPtr j + e * B.Lk + t) :=
          fun t ht => (hm5Ag t ht).trans (hkeep5 e heCap hnotS t ht)
        refine ⟨fun t ht => hkp t ht ▸ hold.1 t ht, ?_⟩
        unfold Num.fixVal; rw [Num.intVal_congr hkp]
        change _ = wstr e * prevVal e; rw [hlenEq]; exact hold.2
    have hblk5b := hblk4.setLen hjLe (fun a ha => by
      dsimp only [m5b]; split_ifs with hlt
      · exact hfr5 a (by omega) (by unfold SelectBlocksLoc.regLen at ha; omega)
      · rfl) hLen5Part
    exact hblk5b.of_agree fun a _ ha2 => by simp [m5b, show a < scratch by omega]
  have hSt5Ag : ∀ a < scratch, ¬ B.regBlk j a → st5.mem a = mem a := fun a ha hnb =>
    (hfr5 a (by omega) (by unfold SelectBlocksLoc.regBlk at hnb; omega)).trans (hSt4Ag a ha hnb)
  -- Stitch the 18 setup assignments + 5 calls + ret via `runs_start_le`
  suffices hMain : ∃ o stF cost,
      Runs w p ω
        (selectUpdateFPhiLenLevelBody dgApplyBatch delEdgeList batchCopySplits filterPres coreLenFill)
        (startState [metaBase, j, slot, prevLen, B.Lk, scratch] mem pos) o stF cost ∧
      (o = .returned scOut ∧ stF.mem = st5.mem) ∧
      cost ≤ selectUpdateFPhiLenCost uWords U.length L.uG.length L.fDel.length B.Lk stLw by
    obtain ⟨_, stF, cost, hrun, ⟨rfl, hmemEq⟩, hcost⟩ := hMain
    exact ⟨scOut, cost, stF, hrun, hscOutLo, hscOutHi, hmemEq ▸ hblk5, hmemEq ▸ hz5,
      fun a ha hnb => hmemEq ▸ hSt5Ag a ha hnb, hcost⟩
  apply runs_start_le
  unfold selectUpdateFPhiLenLevelBody
  have hEntryLt : ∀ blk ≤ 6, smEntryAddr metaBase B.d blk j < 2 ^ w := fun blk hblk => by
    have hm := Nat.mul_le_mul_right (B.d + 1) hblk
    unfold smEntryAddr smTableOff; omega
  refine runs_seq_assign_flat (v := B.d)
    (by simp [Expr.eval, BinOp.eval, startState, hdM, show 1 < 2 ^ w by omega,
          show metaBase + 1 < 2 ^ w by omega, show B.d < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := B.d + 1)
    (by simp [Expr.eval, BinOp.eval, Function.update, show 1 < 2 ^ w by omega,
          show B.d + 1 < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := metaBase + smTableOff)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState,
          show smTableOff < 2 ^ w by unfold smTableOff; omega,
          show metaBase + smTableOff < 2 ^ w by unfold smTableOff; omega]) ?_
  refine runs_seq_assign_flat (v := solverG j)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState,
          show metaBase + smTableOff + j = smEntryAddr metaBase B.d 0 j by unfold smEntryAddr; omega,
          hEntryLt 0 (by omega), hgPtrM, show solverG j < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := B.vCap)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState,
          show metaBase + smTableOff + (B.d + 1) + j = smEntryAddr metaBase B.d 1 j by
            unfold smEntryAddr; omega,
          show metaBase + smTableOff + (B.d + 1) < 2 ^ w by unfold smTableOff; omega,
          hEntryLt 1 (by omega), hvCapM, show B.vCap < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := B.phiPtr j)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState,
          show 3 < 2 ^ w by omega, show 3 * (B.d + 1) < 2 ^ w by omega,
          show metaBase + smTableOff + 3 * (B.d + 1) < 2 ^ w by unfold smTableOff; omega,
          show metaBase + smTableOff + 3 * (B.d + 1) + j = smEntryAddr metaBase B.d 3 j by
            unfold smEntryAddr; omega,
          hEntryLt 3 (by omega), hphiM, show B.phiPtr j < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := B.lenPtr j)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState,
          show 4 < 2 ^ w by omega, show 4 * (B.d + 1) < 2 ^ w by omega,
          show metaBase + smTableOff + 4 * (B.d + 1) < 2 ^ w by unfold smTableOff; omega,
          show metaBase + smTableOff + 4 * (B.d + 1) + j = smEntryAddr metaBase B.d 4 j by
            unfold smEntryAddr; omega,
          hEntryLt 4 (by omega), hlenM, show B.lenPtr j < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := B.fPtr j)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState,
          show 6 < 2 ^ w by omega, show 6 * (B.d + 1) < 2 ^ w by omega,
          show metaBase + smTableOff + 6 * (B.d + 1) < 2 ^ w by unfold smTableOff; omega,
          show metaBase + smTableOff + 6 * (B.d + 1) + j = smEntryAddr metaBase B.d 6 j by
            unfold smEntryAddr; omega,
          hEntryLt 6 (by omega), hfM, show B.fPtr j < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := dgEPresBase (solverG j) B.vCap)
    (by simp [Expr.eval, BinOp.eval, Function.update, show 4 < 2 ^ w by omega,
          show 7 < 2 ^ w by omega, show solverG j + 4 < 2 ^ w by omega,
          show 7 * B.vCap < 2 ^ w by omega,
          show solverG j + 4 + 7 * B.vCap = dgEPresBase (solverG j) B.vCap from rfl,
          show dgEPresBase (solverG j) B.vCap < 2 ^ w by unfold dgEPresBase; omega]) ?_
  refine runs_seq_assign_flat (v := uGPtr)
    (by simp [Expr.eval, Function.update, startState, show slot < 2 ^ w by omega,
          show uGPtr < 2 ^ w by omega, uGPtr]) ?_
  refine runs_seq_assign_flat (v := L.uG.length)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState, show 1 < 2 ^ w by omega,
          show slot + 1 < 2 ^ w by omega, hDiff.1, show L.uG.length < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := fDelPtr)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState, show 2 < 2 ^ w by omega,
          show slot + 2 < 2 ^ w by omega, show fDelPtr < 2 ^ w by omega, fDelPtr]) ?_
  refine runs_seq_assign_flat (v := L.fDel.length)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState, show 3 < 2 ^ w by omega,
          show slot + 3 < 2 ^ w by omega, hDiff.2.2.1, show L.fDel.length < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := stDesc)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState, show 8 < 2 ^ w by omega,
          show slot + 8 < 2 ^ w by omega, hSlotMeta.1, show stDesc < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := stLw)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState, show 9 < 2 ^ w by omega,
          show slot + 9 < 2 ^ w by omega, hSlotMeta.2.1, hStLwW]) ?_
  refine runs_seq_assign_flat (v := uPtr)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState, show 10 < 2 ^ w by omega,
          show slot + 10 < 2 ^ w by omega, hSlotMeta.2.2, show uPtr < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := numBase)
    (by simp [Expr.eval, Function.update, show stDesc < 2 ^ w by omega, hStBaseW.1, numBase]) ?_
  refine runs_seq_assign_flat (v := denBase)
    (by simp [Expr.eval, BinOp.eval, Function.update, show 1 < 2 ^ w by omega,
          show stDesc + 1 < 2 ^ w by omega, hStBaseW.2, denBase]) ?_
  -- Call 1: `dgApplyBatch`
  refine runs_seq_call_c
    (by simp [evalArgs, Expr.eval, Function.update, show 0 < 2 ^ w by omega]) hb1 hr1 ?_
  -- Call 2: `delEdgeList`
  refine runs_seq_call_c (by simp [evalArgs, Expr.eval, Function.update, fDelPtr]) hb2 hr2 ?_
  -- Call 3: `batchCopySplits`
  refine runs_seq_call_c (by simp [evalArgs, Expr.eval, Function.update, startState]) hb3 hr3 ?_
  -- Call 4: `filterPres`
  refine runs_seq_call_c (by simp [evalArgs, Expr.eval, Function.update, startState, uGPtr]) hb4 hr4 ?_
  -- `reg 26 := scratch + L.uG.length`
  refine runs_seq_assign_flat (v := scratch + L.uG.length)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState,
          show scratch + L.uG.length < 2 ^ w by unfold selectUpdateFPhiLenSpace at hroom; omega]) ?_
  -- Call 5: `coreLenFill`
  refine runs_seq_call_c
    (by simp [evalArgs, Expr.eval, Function.update, startState, hcnt4, numBase, denBase,
          show 0 < 2 ^ w by omega])
    hpCoreLen hr5 ?_
  -- `ret (reg 27)`
  refine ⟨.returned scOut, _, _,
    runs_ret_iff.mpr ⟨scOut, by simp [Expr.eval, Function.update, Outcome.value], rfl, rfl, rfl⟩,
    ⟨rfl, rfl⟩, ?_⟩
  simp only [dgApplyBatchContract, dgDeleteEdgeListContract, selBatchCopySplitsContract,
    selFilterPresentContract, selectUpdateFPhiLenCost, List.getD_cons_zero, List.getD_cons_succ,
    Expr.size, argsSize] at hc1 hc2 hc3 hc4 hc5 ⊢
  have hmul : survUG.length * (selCoreLenEdgeCost B.Lk stLw + 40) ≤
      L.uG.length * (selCoreLenEdgeCost B.Lk stLw + 40) :=
    Nat.mul_le_mul_right _ hSurvLenLe
  omega

end MinCostFlow.MinRatio
