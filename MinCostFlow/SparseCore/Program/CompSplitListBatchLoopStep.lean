module

public import MinCostFlow.SparseCore.Program.CompSplitListBatchLoopBase
import WordRAM.Tactic

/-!
# Single-Update Step of Batch Loop with Canonical Split Lists (`CompSplitListBatchLoopStep`)

Verifies one iteration (`compBatchWithSplitsBodyStmt`) of `compBatchWithSplitsLoopStmt`: copies
`cntBase → oldCntBase`, captures `(tag, delE, x0, y0)` (via `compEdgeEndsProc` for `.delete`),
dispatches the update via `compBatchLoopStep_runs`, emits every branch's `canonStepSplits` via
`compEmitAllBranches_runs`, and increments `r10`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Single-iteration body of `compBatchWithSplitsLoopStmt`. -/
def compBatchWithSplitsBodyStmt (bIns bDel bSplit bEnds bEmit : ℕ) : Stmt :=
  .assign 17 (.bin .add (.reg 8) (.reg 6)) ;;
  .assign 18 (.bin .add (.reg 17) (.bin .mul (.const 4) (.bin .mul (.reg 3) (.reg 4)))) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 3)) ;;
  .assign 20 (.bin .add (.reg 19) (.reg 3)) ;;
  .assign 21 (.bin .add (.reg 20) (.const 2)) ;;
  compCopySliceStmt 7 19 3 22 23 ;;
  .assign 13 (.load (.reg 11)) ;;
  .store (.reg 21) (.reg 13) ;;
  .cond (.bin .eq (.reg 13) (.const 1))
    (.assign 14 (.load (.bin .add (.reg 11) (.const 1))) ;;
     .store (.bin .add (.reg 21) (.const 1)) (.reg 14) ;;
     .call 22 bEnds [.reg 0, .reg 14, .reg 20])
    (.cond (.bin .lt (.const 1) (.reg 13))
      (.store (.reg 20) (.load (.bin .add (.reg 11) (.const 1))) ;;
       .store (.bin .add (.reg 20) (.const 1)) (.load (.bin .add (.reg 11) (.const 2))))
      (.assign 14 (.const 0))) ;;
  compBatchDispStmt bIns bDel bSplit ;;
  .assign 17 (.bin .add (.reg 8) (.reg 6)) ;;
  .assign 18 (.bin .add (.reg 17) (.bin .mul (.const 4) (.bin .mul (.reg 3) (.reg 4)))) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 3)) ;;
  .assign 21 (.bin .add (.reg 19) (.reg 3)) ;;
  .assign 20 (.bin .add (.reg 21) (.const 2)) ;;
  .assign 13 (.load (.reg 20)) ;;
  .assign 14 (.load (.bin .add (.reg 20) (.const 1))) ;;
  .assign 15 (.load (.reg 21)) ;;
  .assign 16 (.load (.bin .add (.reg 21) (.const 1))) ;;
  .store (.reg 20) (.const 0) ;;
  .store (.bin .add (.reg 20) (.const 1)) (.const 0) ;;
  .store (.reg 21) (.const 0) ;;
  .store (.bin .add (.reg 21) (.const 1)) (.const 0) ;;
  .assign 21 (.const 0) ;;
  compEmitAllBranchesStmt bEmit ;;
  .assign 10 (.bin .add (.reg 10) (.const 1))

lemma compBatchWithSplitsLoopStmt_eq (bIns bDel bSplit bEnds bEmit : ℕ) :
    compBatchWithSplitsLoopStmt bIns bDel bSplit bEnds bEmit =
      .loop (.bin .lt (.reg 10) (.reg 6))
        (compBatchWithSplitsBodyStmt bIns bDel bSplit bEnds bEmit) := rfl

private lemma sp1_toFinset_eq (u : Update) :
    (match u with | .split _ v' _ _ => [v'] | _ => []).toFinset =
      match u with | .split _ v' _ _ => {v'} | _ => ∅ := by
  cases u <;> simp

set_option maxHeartbeats 1200000 in
open Classical in
/-- Verification of one full iteration (`compBatchWithSplitsBodyStmt`) of the batch loop with
canonical split emission. -/
theorem compBatchWithSplitsStep_runs {W : LSFWindowImpl}
    {w k b bZero bLogAdd bPreLog bLsf bCons bErase bApp bMark bDisp bIns bDel bSplit
      bSort bRootVal bEnds bEndRoots bUFInitFind bUFPairUnion bUFClean bEmit
      heap numU cntBase splitBase spBufBase spCntBase oldCntBase endsTmp ufBase updBuf
      idx uPtr nSp uLen : ℕ}
    {p : Program} {mem0 : ℕ → ℕ} {ω : ℕ → Bool}
    {S : CompLSFFamily k} {x : CompLSFMeta k} {touched : List ℕ}
    {cnts spCnts : Fin k → ℕ} {u : Update} {st : State}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hpLogAdd : p.procs[bLogAdd]? = some (compLogAddOrigRootProc
      (lsfBaseBat W.Q_AN bLsf + 0) (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge) (lsfBaseBat W.Q_AN bLsf + 1)))
    (hpPreLog : p.procs[bPreLog]? = some (compPreLogProc bLogAdd))
    (hpLsf : p.HasAt bLsf (lsfModuleProcs W.Q_AN W.c_AN W.K_AN bLsf W.h))
    (hpCons : p.procs[bCons]? = some ghostConsProc)
    (hpErase : p.procs[bErase]? = some ghostEraseProc)
    (hpApp : p.procs[bApp]? = some ghostAppendProc)
    (hpMark : p.procs[bMark]? = some compMarkTouchProc)
    (hpDisp : p.procs[bDisp]? = some (compDispatchOneProc bZero bPreLog (bLsf + lsfIdxBatch)))
    (hpIns : p.procs[bIns]? = some (compStepInsertProc bCons bMark bDisp))
    (hpDel : p.procs[bDel]? = some (compStepDeleteProc bErase bMark bDisp))
    (hpSplit : p.procs[bSplit]? = some (compStepSplitProc bApp bMark bDisp))
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hpRootVal : p.procs[bRootVal]? = some compRootValProc)
    (hpEnds : p.procs[bEnds]? = some compEdgeEndsProc)
    (hpEndRoots : p.procs[bEndRoots]? = some compEdgeEndRootsProc)
    (hpInitFind : p.procs[bUFInitFind]? = some compUFInitFindProc)
    (hpPairUnion : p.procs[bUFPairUnion]? = some compUFPairUnionProc)
    (hpClean : p.procs[bUFClean]? = some compUFCleanProc)
    (hpEmit : p.procs[bEmit]? = some (compEmitBranchSplitProc bZero (bSort + sortIdxMergeSort)
      bRootVal bEndRoots bUFInitFind bUFPairUnion bUFClean))
    (hw16 : 16 ≤ 2 ^ w)
    (hrep : CompLSFRepDirty W k b S x touched st.mem)
    (hnd : touched.Nodup) (hlt : ∀ c ∈ touched, c < x.numComps)
    (hidx_lt : idx < numU) (hlen_le : touched.length ≤ 2 * idx) (hnsp_le : nSp ≤ idx)
    (hu_at : UpdateAt st.mem uPtr (S ⟨0, hrep.1⟩).G u uLen)
    (hu_mem_ag : ∀ i < uLen, st.mem (uPtr + i) = mem0 (uPtr + i))
    (hu_words : ∀ i < uLen, st.mem (uPtr + i) < 2 ^ w)
    (hu_out : ∀ i < uLen, (uPtr + i < b ∨ x.endAddr ≤ uPtr + i) ∧ uPtr + i < heap)
    (huLen_eq : dgUpdateMemLen mem0 uPtr = uLen) (huLen_ge2 : 2 ≤ uLen)
    (hu_val : (S ⟨0, hrep.1⟩).G.UpdateIsValid u)
    (hCaps1 : UpdateWithinCaps x.vCap x.eCap u)
    (hr0 : st.regs 0 = b) (hr2 : st.regs 2 = heap) (hr3 : st.regs 3 = k) (hr4 : st.regs 4 = x.vCap)
    (hr6 : st.regs 6 = numU) (hr7 : st.regs 7 = cntBase) (hr8 : st.regs 8 = splitBase)
    (hr9 : st.regs 9 = updBuf) (hr10 : st.regs 10 = idx) (hr11 : st.regs 11 = uPtr) (hr12 : st.regs 12 = nSp)
    (hend_h : x.endAddr ≤ heap)
    (hheap_cnt : heap + 1 + 2 * numU ≤ cntBase)
    (hcnt_sp : cntBase + k + 2 * (k * x.vCap) ≤ splitBase)
    (hspBuf_def : spBufBase = splitBase + numU)
    (hspCnt_def : spCntBase = spBufBase + 4 * (k * x.vCap))
    (holdCnt_def : oldCntBase = spCntBase + k)
    (hends_def : endsTmp = oldCntBase + k)
    (huf_def : ufBase = endsTmp + 2)
    (huf_le : ufBase + ufEmitScratchSize x.vCap ≤ updBuf)
    (hbuf_w : updBuf + 5 + uLen + 2 * x.eCap < 2 ^ w)
    (hu_w : uPtr + uLen < 2 ^ w)
    (hz : ZeroFrom st.mem endsTmp)
    (hhp : st.mem heap = touched.length) (hls : ListAt st.mem (heap + 1) touched)
    (hcnts_m : ∀ j : Fin k, st.mem (cntBase + j.1) = cnts j)
    (hcnts_le : ∀ j : Fin k, cnts j ≤ (S j).RF.R.card)
    (hspCnts_m : ∀ j : Fin k, st.mem (spCntBase + j.1) = spCnts j)
    (hspCnts_le : ∀ j : Fin k, spCnts j ≤ (S j).RF.R.card) :
    let cs0 := S ⟨0, hrep.1⟩
    let S1 : CompLSFFamily k := fun j => compLSFStepSingle (S j) u
    let rootsBase := cntBase + k
    let fDelBase := cntBase + k + k * x.vCap
    ∃ st2 cBody, ∃ (x1 : CompLSFMeta k) (touched1 : List ℕ)
        (cuts1 : Fin k → List (ℕ × ℕ)) (sp1 : List ℕ),
      Runs w p ω (compBatchWithSplitsBodyStmt bIns bDel bSplit bEnds bEmit) st .normal st2 cBody ∧
      (∀ r < 10, st2.regs r = st.regs r) ∧
      st2.regs 10 = idx + 1 ∧ st2.regs 11 = uPtr + uLen ∧ st2.regs 12 = nSp + sp1.length ∧
      sp1.length ≤ 1 ∧
      x1.vCap = x.vCap ∧ x1.eCap = x.eCap ∧ x1.L_w = x.L_w ∧
      x1.numComps = x.numComps ∧ x1.numEdgeful = x.numEdgeful ∧
      x1.m0Total = x.m0Total ∧ x1.endAddr = x.endAddr ∧ HEq x1.compOf x.compOf ∧
      CompLSFRepDirty W k b S1 x1 touched1 st2.mem ∧
      touched1.Nodup ∧ (∀ c ∈ touched1, c < x.numComps) ∧
      touched1.length ≤ touched.length + 2 ∧
      touched.length ≤ touched1.length ∧
      st2.mem heap = touched1.length ∧
      ListAt st2.mem (heap + 1) touched1 ∧
      (∀ i (hi : i < sp1.length), st2.mem (splitBase + (nSp + i)) = sp1[i]) ∧
      (∀ j : Fin k,
        st2.mem (cntBase + j.1) = cnts j + (cuts1 j).length ∧
        (∀ i (hi : i < (cuts1 j).length),
          st2.mem (rootsBase + j.1 * x.vCap + (cnts j + i)) = (cuts1 j)[i].2 ∧
          st2.mem (fDelBase + j.1 * x.vCap + (cnts j + i)) = (cuts1 j)[i].1) ∧
        cnts j + (cuts1 j).length ≤ (S1 j).RF.R.card) ∧
      (∀ j : Fin k,
        let step := canonStepSplits (S j) u
        st2.mem (spCntBase + j.1) = spCnts j + step.length ∧
        spCnts j + step.length ≤ (S1 j).RF.R.card ∧
        (∀ i (hi : i < step.length),
          st2.mem (spBufBase + 4 * (j.1 * x.vCap) + 4 * (spCnts j + i)) =
            (if step[i].isRelease then 1 else 0) ∧
          st2.mem (spBufBase + 4 * (j.1 * x.vCap) + 4 * (spCnts j + i) + 1) = step[i].edge ∧
          st2.mem (spBufBase + 4 * (j.1 * x.vCap) + 4 * (spCnts j + i) + 2) = step[i].kept ∧
          st2.mem (spBufBase + 4 * (j.1 * x.vCap) + 4 * (spCnts j + i) + 3) = step[i].fresh)) ∧
      (∀ (cuts2 : Fin k → List (ℕ × ℕ)) (sp2 : List ℕ) (S2 : CompLSFFamily k),
        (∀ j : Fin k,
          CompForestCutsValid x.vCap (S1 j).RF (cuts2 j) ∧
          ((cuts2 j).map Prod.fst).Nodup ∧
          ((cuts2 j).map Prod.fst).toFinset = (S1 j).RF.F.E \ (S2 j).RF.F.E ∧
          (S2 j).RF.F.E ⊆ (S1 j).RF.F.E ∧
          ((cuts2 j).map Prod.snd).Nodup ∧
          sp2.Nodup ∧
          (∀ r ∈ (cuts2 j).map Prod.snd, r ∉ sp2) ∧
          ((cuts2 j).map Prod.snd).toFinset ∪ sp2.toFinset = (S2 j).RF.R \ (S1 j).RF.R ∧
          (S1 j).RF.R ⊆ (S2 j).RF.R) →
        ∀ j : Fin k,
          let cuts := cuts1 j ++ cuts2 j
          let sp := sp1 ++ sp2
          CompForestCutsValid x.vCap (S j).RF cuts ∧
          (cuts.map Prod.fst).Nodup ∧
          (cuts.map Prod.fst).toFinset = (S j).RF.F.E \ (S2 j).RF.F.E ∧
          (S2 j).RF.F.E ⊆ (S j).RF.F.E ∧
          (cuts.map Prod.snd).Nodup ∧
          sp.Nodup ∧
          (∀ r ∈ cuts.map Prod.snd, r ∉ sp) ∧
          (cuts.map Prod.snd).toFinset ∪ sp.toFinset = (S2 j).RF.R \ (S j).RF.R ∧
          (S j).RF.R ⊆ (S2 j).RF.R) ∧
      (∀ a,
        (a < b ∨ x.endAddr ≤ a) →
        a ≠ heap → (a < heap + 1 + touched.length ∨ heap + 1 + touched.length + 2 ≤ a) →
        (a < splitBase + nSp ∨ splitBase + nSp + sp1.length ≤ a) →
        (∀ j : Fin k, a ≠ cntBase + j.1) →
        (∀ j : Fin k, a < rootsBase + j.1 * x.vCap + cnts j ∨
          rootsBase + j.1 * x.vCap + cnts j + (cuts1 j).length ≤ a) →
        (∀ j : Fin k, a < fDelBase + j.1 * x.vCap + cnts j ∨
          fDelBase + j.1 * x.vCap + cnts j + (cuts1 j).length ≤ a) →
        (∀ j : Fin k, a < spBufBase + 4 * (j.1 * x.vCap) + 4 * spCnts j ∨
          spBufBase + 4 * (j.1 * x.vCap) + 4 * (spCnts j + (canonStepSplits (S j) u).length) ≤ a) →
        (∀ j : Fin k, a ≠ spCntBase + j.1) →
        (a < oldCntBase ∨ oldCntBase + k ≤ a) →
        a < endsTmp → st2.mem a = st.mem a) ∧
      ZeroFrom st2.mem endsTmp ∧
      cBody + 120 * (∑ j : Fin k, (cuts1 j).length) +
          180 * (∑ j : Fin k, (canonStepSplits (S j) u).length) +
          compPhiFull k b x1 st2.mem ≤
        compPhiFull k b x st.mem + 2640 * k +
          k * ((touchedComps cs0 u).filter fun C => 1 ≤ (compGraph cs0.G₀ C).m).sum (fun C =>
            lsfBatchCostFactor * ((1 + projUpdWords mem0 cs0 C uPtr u) * x.L_w + 1) +
            lsfBatchCostFactor * (projUpdWords mem0 cs0 C uPtr u * x.L_w)) := by
  intro cs0 S1 rootsBase fDelBase
  have hk : 1 ≤ k := hrep.1
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have huf_sz : ufEmitScratchSize x.vCap = 8 * x.vCap + 3 := rfl
  -- Step A: Compute scratch addresses + copy `cntBase → oldCntBase`
  let a1 : State := { st with regs := Function.update st.regs 17 spBufBase }
  let a2 : State := { a1 with regs := Function.update a1.regs 18 spCntBase }
  let a3 : State := { a2 with regs := Function.update a2.regs 19 oldCntBase }
  let a4 : State := { a3 with regs := Function.update a3.regs 20 endsTmp }
  let a5 : State := { a4 with regs := Function.update a4.regs 21 ufBase }
  have ha1 : Runs w p ω (.assign 17 (.bin .add (.reg 8) (.reg 6))) st .normal a1 4 :=
    runs_assign_iff.mpr ⟨spBufBase, by
      simp [Expr.eval, BinOp.eval, hr8, hr6, ← hspBuf_def, show spBufBase < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have ha2 : Runs w p ω (.assign 18 (.bin .add (.reg 17) (.bin .mul (.const 4) (.bin .mul (.reg 3) (.reg 4)))))
      a1 .normal a2 8 :=
    runs_assign_iff.mpr ⟨spCntBase, by
      simp [a1, Expr.eval, BinOp.eval, hr3, hr4, hw4, ← hspCnt_def,
        show k * x.vCap < 2 ^ w by omega, show 4 * (k * x.vCap) < 2 ^ w by omega,
        show spCntBase < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  have ha3 : Runs w p ω (.assign 19 (.bin .add (.reg 18) (.reg 3))) a2 .normal a3 4 :=
    runs_assign_iff.mpr ⟨oldCntBase, by
      simp [a2, a1, Expr.eval, BinOp.eval, hr3, ← holdCnt_def, show oldCntBase < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have ha4 : Runs w p ω (.assign 20 (.bin .add (.reg 19) (.reg 3))) a3 .normal a4 4 :=
    runs_assign_iff.mpr ⟨endsTmp, by
      simp [a3, a2, a1, Expr.eval, BinOp.eval, hr3, ← hends_def, show endsTmp < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have ha5 : Runs w p ω (.assign 21 (.bin .add (.reg 20) (.const 2))) a4 .normal a5 4 :=
    runs_assign_iff.mpr ⟨ufBase, by
      simp [a4, a3, a2, a1, Expr.eval, BinOp.eval, hw2, ← huf_def, show ufBase < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨aCp, cCp, haCp, hrCp, hcp_val, hcp_fr, hcCp⟩ :=
    compCopySlice_runs (w := w) (rSrc := 7) (rDst := 19) (rLen := 3) (rIdx := 22) (rTmp := 23)
      (src := cntBase) (dst := oldCntBase) (len := k) (p := p) (ω := ω) (st := a5)
      (by decide) hw16 (by omega) (by omega) (Or.inl (by omega))
      (by simp [a5, a4, a3, a2, a1, hr7]) (by simp [a5, a4, a3]) (by simp [a5, a4, a3, a2, a1, hr3])
  -- Step B: Load `tag`, store `tag` at `ufBase`, capture `(delE, x0, y0)`
  set tag := st.mem uPtr
  have htag_cp : aCp.mem uPtr = tag := hcp_fr uPtr (Or.inl (by have := hu_out 0 (by omega); omega))
  let b1 : State := { aCp with regs := Function.update aCp.regs 13 tag }
  let b2 : State := { b1 with mem := Function.update b1.mem ufBase tag }
  have hb1 : Runs w p ω (.assign 13 (.load (.reg 11))) aCp .normal b1 3 :=
    runs_assign_iff.mpr ⟨tag, Expr.eval_load_of_eq (by
      simp [Expr.eval, hrCp 11 (by decide), a5, a4, a3, a2, a1, hr11]) htag_cp,
      rfl, rfl, by simp [Expr.size]⟩
  have hb2 : Runs w p ω (.store (.reg 21) (.reg 13)) b1 .normal b2 3 :=
    runs_store_iff.mpr ⟨ufBase, tag,
      by simp [b1, Expr.eval, hrCp 21 (by decide), a5], by simp [b1, Expr.eval],
      rfl, rfl, by simp [Expr.size]⟩
  have htag_w : tag < 2 ^ w := by simpa [tag] using hu_words 0 (by omega)
  have hpre_meta : ∃ (b3 : State) (cMeta delE x0 y0 : ℕ),
      Runs w p ω
        (.cond (.bin .eq (.reg 13) (.const 1))
          (.assign 14 (.load (.bin .add (.reg 11) (.const 1))) ;;
           .store (.bin .add (.reg 21) (.const 1)) (.reg 14) ;;
           .call 22 bEnds [.reg 0, .reg 14, .reg 20])
          (.cond (.bin .lt (.const 1) (.reg 13))
            (.store (.reg 20) (.load (.bin .add (.reg 11) (.const 1))) ;;
             .store (.bin .add (.reg 20) (.const 1)) (.load (.bin .add (.reg 11) (.const 2))))
            (.assign 14 (.const 0)))) b2 .normal b3 cMeta ∧
      (∀ r < 14, b3.regs r = b2.regs r) ∧
      b3.mem ufBase = tag ∧ b3.mem (ufBase + 1) = delE ∧
      b3.mem endsTmp = x0 ∧ b3.mem (endsTmp + 1) = y0 ∧
      delE < 2 ^ w ∧ x0 < 2 ^ w ∧ y0 < 2 ^ w ∧
      (∀ a, a < endsTmp ∨ ufBase + 2 ≤ a → b3.mem a = aCp.mem a) ∧
      (∀ j : Fin k, match (generalizing := false) u with
        | .insert _ _ _ => tag = 0
        | .delete e => tag = 1 ∧ delE = e ∧
            (e ∈ (S j).RF.F.E → x0 = (S j).G.tail e ∧ y0 = (S j).G.head e)
        | .split v v' _ _ => 2 ≤ tag ∧ x0 = v ∧ y0 = v') ∧
      cMeta ≤ 210 := by
    cases u with
    | insert e aV bV =>
      rcases hu_at with ⟨_, hLA⟩
      have htag0 : tag = 0 := by simpa [tag] using hLA 0 (by simp)
      let b2' : State := { b2 with regs := Function.update b2.regs 14 0 }
      have hnoop : Runs w p ω (.assign 14 (.const 0)) b2 .normal b2' 2 :=
        runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
      have hc2 : Runs w p ω
          (.cond (.bin .lt (.const 1) (.reg 13))
            (.store (.reg 20) (.load (.bin .add (.reg 11) (.const 1))) ;;
             .store (.bin .add (.reg 20) (.const 1)) (.load (.bin .add (.reg 11) (.const 2))))
            (.assign 14 (.const 0))) b2 .normal b2' 6 :=
        runs_cond_iff.mpr ⟨0, 2, by simp [b2, b1, Expr.eval, BinOp.eval, htag0, hw1], by simpa using hnoop,
          by simp [Expr.size]⟩
      have hc1 : Runs w p ω
          (.cond (.bin .eq (.reg 13) (.const 1))
            (.assign 14 (.load (.bin .add (.reg 11) (.const 1))) ;;
             .store (.bin .add (.reg 21) (.const 1)) (.reg 14) ;;
             .call 22 bEnds [.reg 0, .reg 14, .reg 20])
            (.cond (.bin .lt (.const 1) (.reg 13))
              (.store (.reg 20) (.load (.bin .add (.reg 11) (.const 1))) ;;
               .store (.bin .add (.reg 20) (.const 1)) (.load (.bin .add (.reg 11) (.const 2))))
              (.assign 14 (.const 0)))) b2 .normal b2' 10 :=
        runs_cond_iff.mpr ⟨0, 6, by simp [b2, b1, Expr.eval, BinOp.eval, htag0, hw1], by simpa using hc2,
          by simp [Expr.size]⟩
      refine ⟨b2', 10, 0, 0, 0, hc1, fun r hr => by simp [b2', show r ≠ 14 by omega], by simp [b2', b2],
        by dsimp only [b2', b2, b1]; rw [Function.update_of_ne (by omega), hcp_fr _ (Or.inr (by omega))]; exact hz _ (by omega),
        by dsimp only [b2', b2, b1]; rw [Function.update_of_ne (by omega), hcp_fr _ (Or.inr (by omega))]; exact hz _ (le_refl _),
        by dsimp only [b2', b2, b1]; rw [Function.update_of_ne (by omega), hcp_fr _ (Or.inr (by omega))]; exact hz _ (by omega),
        hw0', hw0', hw0', fun a ha => by simp [b2', b2, b1, show a ≠ ufBase by omega], fun _ => htag0, by omega⟩
    | delete e =>
      rcases hu_at with ⟨_, hLA⟩
      have htag1 : tag = 1 := by simpa [tag] using hLA 0 (by simp)
      have he_m : st.mem (uPtr + 1) = e := by simpa using hLA 1 (by simp)
      have he_w : e < 2 ^ w := he_m ▸ hu_words 1 (by omega)
      have hu1_lt : uPtr + 1 < heap := (hu_out 1 (by omega)).2
      have he_b2 : b2.mem (uPtr + 1) = e := by
        dsimp only [b2, b1]; rw [Function.update_of_ne (by omega), hcp_fr _ (Or.inl (by omega))]; exact he_m
      let d1 : State := { b2 with regs := Function.update b2.regs 14 e }
      let d2 : State := { d1 with mem := Function.update d1.mem (ufBase + 1) e }
      have hd1 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 11) (.const 1)))) b2 .normal d1 5 :=
        runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq (by
          simp [b2, b1, Expr.eval, BinOp.eval, hrCp 11 (by decide), a5, a4, a3, a2, a1, hr11, hw1,
            show uPtr + 1 < 2 ^ w by omega]) he_b2, rfl, rfl, by simp [Expr.size]⟩
      have hd2 : Runs w p ω (.store (.bin .add (.reg 21) (.const 1)) (.reg 14)) d1 .normal d2 5 :=
        runs_store_iff.mpr ⟨ufBase + 1, e, by
          simp [d1, b2, b1, Expr.eval, BinOp.eval, hrCp 21 (by decide), a5, hw1,
            show ufBase + 1 < 2 ^ w by omega], by simp [d1, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
      have hrep_d2 : CompLSFRepDirty W k b S x touched d2.mem :=
        compLSFRepDirty_of_agree hrep (fun a ha1 ha2 => by
          dsimp only [d2, d1, b2, b1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            hcp_fr a (Or.inl (by omega))])
      obtain ⟨dE, cE, hrE, hE_ends, hE_lt1, hE_lt2, hE_fr, hcE⟩ :=
        compEdgeEnds_runs (W := W) (w := w) (k := k) (b := b) (e := e) (out2 := endsTmp)
          (S := S) (x := x) (touched := touched) (p := p) (mem := d2.mem) (pos := d2.pos) (ω := ω)
          hw16 hrep_d2 (by omega) (by omega) hu_val
      let d3 : State := { d2 with regs := Function.update d2.regs 22 0, mem := dE.mem, pos := dE.pos }
      have hd3 : Runs w p ω (.call 22 bEnds [.reg 0, .reg 14, .reg 20]) d2 .normal d3 (3 + cE + 1) :=
        runs_call_iff.mpr ⟨[b, e, endsTmp], compEdgeEndsProc, .returned 0, dE, cE,
          by simp [evalArgs, Expr.eval, d2, d1, b2, b1, hrCp 0 (by decide), hrCp 20 (by decide),
            a5, a4, a3, a2, a1, hr0], hpEnds, hrE, rfl, rfl, by simp [argsSize, Expr.size]⟩
      have hthen := runs_seq_iff.mpr (Or.inr ⟨d1, 5, _, hd1,
        runs_seq_iff.mpr (Or.inr ⟨d2, 5, _, hd2, hd3, rfl⟩), rfl⟩)
      have hc1 : Runs w p ω
          (.cond (.bin .eq (.reg 13) (.const 1))
            (.assign 14 (.load (.bin .add (.reg 11) (.const 1))) ;;
             .store (.bin .add (.reg 21) (.const 1)) (.reg 14) ;;
             .call 22 bEnds [.reg 0, .reg 14, .reg 20])
            (.cond (.bin .lt (.const 1) (.reg 13))
              (.store (.reg 20) (.load (.bin .add (.reg 11) (.const 1))) ;;
               .store (.bin .add (.reg 20) (.const 1)) (.load (.bin .add (.reg 11) (.const 2))))
              (.assign 14 (.const 0)))) b2 .normal d3 (5 + (5 + (3 + cE + 1) + 1) + 1 + 4) :=
        runs_cond_iff.mpr ⟨1, _, by simp [b2, b1, Expr.eval, BinOp.eval, htag1, hw1], by simpa using hthen,
          by simp [Expr.size]; omega⟩
      refine ⟨d3, _, e, d3.mem endsTmp, d3.mem (endsTmp + 1), hc1,
        fun r hr => by simp [d3, d2, d1, show r ≠ 22 by omega, show r ≠ 14 by omega],
        by dsimp only [d3]; rw [hE_fr ufBase (Or.inr (by omega))]; simp [d2, d1, b2],
        by dsimp only [d3]; rw [hE_fr (ufBase + 1) (Or.inr (by omega))]; simp [d2],
        rfl, rfl, he_w, hE_lt1, hE_lt2,
        fun a ha => by
          dsimp only [d3]; rw [hE_fr a (by omega)]
          dsimp only [d2, d1, b2, b1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
        fun j => ⟨htag1, rfl, fun heFj => by
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨ℓ₀, hBr⟩, _⟩ := hrep
          have hOrig := compLSF_F_edge_orig (hBr j).1 heFj
          have hnc : e ∉ (S ⟨0, hk⟩).crossEdges := (hBr j).2.2.2.2.1 ▸ hOrig.2.2.1
          have hni : e ∉ (S ⟨0, hk⟩).insertedGlobal := (hBr j).2.2.2.2.2.1 ▸ hOrig.2.1
          rw [(hBr j).2.2.1]; exact hE_ends hnc hni⟩, by omega⟩
    | split v v' St Sh =>
      have htag23 : (tag = 2 ∨ tag = 3) ∧ st.mem (uPtr + 1) = v ∧ st.mem (uPtr + 2) = v' ∧ 3 ≤ uLen := by
        rcases hu_at with ⟨_, _, _, _, _, _, hL, hLA⟩ | ⟨_, _, _, _, _, _, hL, hLA⟩
        · exact ⟨Or.inl (by simpa [tag] using hLA 0 (by simp)),
            by simpa using hLA 1 (by simp), by simpa using hLA 2 (by simp), by omega⟩
        · exact ⟨Or.inr (by simpa [tag] using hLA 0 (by simp)),
            by simpa using hLA 1 (by simp), by simpa using hLA 2 (by simp), by omega⟩
      have hu3 : 3 ≤ uLen := htag23.2.2.2
      have hv_w : v < 2 ^ w := htag23.2.1 ▸ hu_words 1 (by omega)
      have hv'_w : v' < 2 ^ w := htag23.2.2.1 ▸ hu_words 2 (by omega)
      have hu1_lt : uPtr + 1 < heap := (hu_out 1 (by omega)).2
      have hu2_lt : uPtr + 2 < heap := (hu_out 2 (by omega)).2
      have hv_b2 : b2.mem (uPtr + 1) = v := by
        dsimp only [b2, b1]; rw [Function.update_of_ne (by omega), hcp_fr _ (Or.inl (by omega))]; exact htag23.2.1
      have hv'_b2 : b2.mem (uPtr + 2) = v' := by
        dsimp only [b2, b1]; rw [Function.update_of_ne (by omega), hcp_fr _ (Or.inl (by omega))]; exact htag23.2.2.1
      let e1 : State := { b2 with mem := Function.update b2.mem endsTmp v }
      let e2 : State := { e1 with mem := Function.update e1.mem (endsTmp + 1) v' }
      have he1 : Runs w p ω (.store (.reg 20) (.load (.bin .add (.reg 11) (.const 1)))) b2 .normal e1 6 :=
        runs_store_iff.mpr ⟨endsTmp, v,
          by simp [b2, b1, Expr.eval, hrCp 20 (by decide), a5, a4],
          Expr.eval_load_of_eq (x := uPtr + 1) (by
            simp [b2, b1, Expr.eval, BinOp.eval, hrCp 11 (by decide), a5, a4, a3, a2, a1, hr11, hw1,
              show uPtr + 1 < 2 ^ w by omega]) hv_b2, rfl, rfl, by simp [Expr.size]⟩
      have he2 : Runs w p ω (.store (.bin .add (.reg 20) (.const 1))
          (.load (.bin .add (.reg 11) (.const 2)))) e1 .normal e2 8 :=
        runs_store_iff.mpr ⟨endsTmp + 1, v',
          by simp [e1, b2, b1, Expr.eval, BinOp.eval, hrCp 20 (by decide), a5, a4, hw1,
            show endsTmp + 1 < 2 ^ w by omega],
          Expr.eval_load_of_eq (x := uPtr + 2) (by
            simp [e1, b2, b1, Expr.eval, BinOp.eval, hrCp 11 (by decide), a5, a4, a3, a2, a1, hr11, hw2,
              show uPtr + 2 < 2 ^ w by omega]) (by dsimp only [e1]; rw [Function.update_of_ne (by omega)]; exact hv'_b2),
          rfl, rfl, by simp [Expr.size]⟩
      have hseq := runs_seq_iff.mpr (Or.inr ⟨e1, 6, 8, he1, he2, rfl⟩)
      have hc2 : Runs w p ω
          (.cond (.bin .lt (.const 1) (.reg 13))
            (.store (.reg 20) (.load (.bin .add (.reg 11) (.const 1))) ;;
             .store (.bin .add (.reg 20) (.const 1)) (.load (.bin .add (.reg 11) (.const 2))))
            (.assign 14 (.const 0))) b2 .normal e2 19 :=
        runs_cond_iff.mpr ⟨1, 15, by
          simp [b2, b1, Expr.eval, BinOp.eval, hw1, show 1 < tag by rcases htag23.1 with h | h <;> omega],
          by simpa using hseq, by simp [Expr.size]⟩
      have hc1 : Runs w p ω
          (.cond (.bin .eq (.reg 13) (.const 1))
            (.assign 14 (.load (.bin .add (.reg 11) (.const 1))) ;;
             .store (.bin .add (.reg 21) (.const 1)) (.reg 14) ;;
             .call 22 bEnds [.reg 0, .reg 14, .reg 20])
            (.cond (.bin .lt (.const 1) (.reg 13))
              (.store (.reg 20) (.load (.bin .add (.reg 11) (.const 1))) ;;
               .store (.bin .add (.reg 20) (.const 1)) (.load (.bin .add (.reg 11) (.const 2))))
              (.assign 14 (.const 0)))) b2 .normal e2 23 :=
        runs_cond_iff.mpr ⟨0, 19, by
          simp [b2, b1, Expr.eval, BinOp.eval, hw1, show tag ≠ 1 by rcases htag23.1 with h | h <;> omega],
          by simpa using hc2, by simp [Expr.size]⟩
      refine ⟨e2, 23, 0, v, v', hc1, fun _ _ => rfl,
        by dsimp only [e2, e1, b2]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
        by dsimp only [e2, e1, b2, b1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), hcp_fr _ (Or.inr (by omega))]; exact hz _ (by omega),
        by dsimp only [e2, e1]; rw [Function.update_of_ne (by omega), Function.update_self],
        by simp [e2], hw0', hv_w, hv'_w,
        fun a ha => by
          dsimp only [e2, e1, b2, b1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)],
        fun _ => ⟨by rcases htag23.1 with h | h <;> omega, rfl, rfl⟩, by omega⟩
  obtain ⟨b3, cMeta, delE, x0, y0, hrun_meta, hrb3, hb3_t, hb3_e, hb3_x, hb3_y,
    hdelE_w, hx0_w, hy0_w, hb3_fr, htag_spec, hcMeta⟩ := hpre_meta
  have hb3_lt_old : ∀ a < oldCntBase, b3.mem a = st.mem a := fun a ha =>
    (hb3_fr a (Or.inl (by omega))).trans (hcp_fr a (Or.inl ha))
  have hb3_old : ∀ j : Fin k, b3.mem (oldCntBase + j.1) = cnts j := fun j =>
    (hb3_fr _ (Or.inl (by have := j.2; omega))).trans ((hcp_val j.1 j.2).trans (hcnts_m j))
  have hb3_ge_uf2 : ∀ a, ufBase + 2 ≤ a → b3.mem a = 0 := fun a ha =>
    (hb3_fr a (Or.inr ha)).trans ((hcp_fr a (Or.inr (by omega))).trans (hz a (by omega)))
  have hrep_b3 : CompLSFRepDirty W k b S x touched b3.mem :=
    compLSFRepDirty_of_agree hrep (fun a ha1 ha2 => hb3_lt_old a (by omega))
  have hrb3_lt13 : ∀ r < 13, b3.regs r = st.regs r := fun r hr => by
    rw [hrb3 r (by omega)]; dsimp only [b2, b1]
    rw [Function.update_of_ne (by omega), hrCp r (by omega) (by omega)]
    simp [a5, a4, a3, a2, a1, show r ≠ 21 by omega, show r ≠ 20 by omega, show r ≠ 19 by omega,
      show r ≠ 18 by omega, show r ≠ 17 by omega]
  have hb3_r13 : b3.regs 13 = b3.mem uPtr := by
    rw [hrb3 13 (by omega), hb3_lt_old uPtr (by have := hu_out 0 (by omega); omega)]; simp [b2, b1, tag]
  -- Step C: Dispatch single update via `compBatchLoopStep_runs`
  have hb3_eq_tag : { b3 with regs := Function.update b3.regs 13 (b3.mem uPtr) } = b3 := by
    cases b3 with | mk regs mem pos =>
      simp only [State.mk.injEq, and_true, true_and]
      funext r; by_cases hr : r = 13
      · subst hr; rw [Function.update_self]; exact hb3_r13.symm
      · exact Function.update_of_ne hr _ _
  have hu_at_b3 : UpdateAt b3.mem uPtr cs0.G u uLen := by
    obtain ⟨l', _, hu_at', hrem'⟩ :=
      compBatchBodyAt_of_agree (U := [u]) (tw := uLen) ⟨uLen, le_refl uLen, hu_at, Nat.sub_self uLen⟩
        (fun i hi => hb3_lt_old (uPtr + i) (by have := (hu_out i hi).2; omega))
    have hl'eq : l' = uLen := by dsimp [BatchBodyAt] at hrem'; omega
    exact hl'eq ▸ hu_at'
  obtain ⟨st1, cStep, x1, touched1, cuts1, sp1, hrun_step0, hr1_lt11, hr1_11, hr1_12, hsp1_le, hsp1_eq,
    hx1_1, hx1_2, hx1_3, hx1_4, hx1_5, hx1_6, hx1_7, hx1_8, hrep1, hnd1, hlt1, hlen1, hlen_ge1,
    hhp1, hls1, hsp1_m, hbr1, hcomb, hfr1, hz1, hcost1⟩ :=
    compBatchLoopStep_runs (ω := ω) hpZero hpLogAdd hpPreLog hpLsf hpCons hpErase hpApp hpMark hpDisp
      hpIns hpDel hpSplit hw16 hrep_b3 hnd hlt hu_at_b3
      (fun i hi => (hb3_lt_old (uPtr + i) (by have := (hu_out i hi).2; omega)).trans (hu_mem_ag i hi))
      (fun i hi => (hb3_lt_old (uPtr + i) (by have := (hu_out i hi).2; omega)).symm ▸ hu_words i hi)
      hu_out huLen_eq huLen_ge2 hu_val hCaps1
      ((hrb3_lt13 0 (by omega)).trans hr0) ((hrb3_lt13 2 (by omega)).trans hr2)
      ((hrb3_lt13 7 (by omega)).trans hr7) ((hrb3_lt13 8 (by omega)).trans hr8)
      ((hrb3_lt13 9 (by omega)).trans hr9) ((hrb3_lt13 11 (by omega)).trans hr11)
      ((hrb3_lt13 12 (by omega)).trans hr12)
      hend_h (by omega) hcnt_sp (by omega) hbuf_w hu_w
      (fun a ha => hb3_ge_uf2 a (by omega))
      ((hb3_lt_old heap (by omega)).trans hhp)
      (fun i hi => (hb3_lt_old _ (by omega)).trans (hls i hi))
      (fun j => (hb3_lt_old _ (by have := j.2; omega)).trans (hcnts_m j))
      hcnts_le
  rw [hb3_eq_tag] at hrun_step0
  have hR1_le : ∀ j : Fin k, (S1 j).RF.R.card ≤ x1.vCap := fun j => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨ℓ₁, hBr1⟩, _, hT1, _⟩ := hrep1
    have hT1j := compEdgeTrack_of_same_graph hT1 (hBr1 j).2.1 (hBr1 j).2.2.1
      (hBr1 j).2.2.2.2.1 (hBr1 j).2.2.2.2.2.2
    exact (Finset.card_le_card fun r hr => Finset.mem_range.mpr
      (hT1j.hVlt r ((compLSF_RF_isRSF (hBr1 j).1).2.2.1 hr))).trans (by simp)
  have hst1_above_sp : ∀ a, spBufBase ≤ a → a < updBuf → st1.mem a = b3.mem a := fun a ha1 ha2 =>
    hfr1 a (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      (fun j => by have := j.2; omega)
      (fun j => Or.inr (by
        have hjv : j.1 * x.vCap + x.vCap ≤ k * x.vCap := by
          have := Nat.mul_le_mul_right x.vCap (show j.1 + 1 ≤ k by have := j.2; omega)
          rw [Nat.add_mul, Nat.one_mul] at this; exact this
        have := le_trans (hbr1 j).2.2 (hx1_1 ▸ hR1_le j); omega))
      (fun j => Or.inr (by
        have hjv : j.1 * x.vCap + x.vCap ≤ k * x.vCap := by
          have := Nat.mul_le_mul_right x.vCap (show j.1 + 1 ≤ k by have := j.2; omega)
          rw [Nat.add_mul, Nat.one_mul] at this; exact this
        have := le_trans (hbr1 j).2.2 (hx1_1 ▸ hR1_le j); omega)) ha2
  -- Step D: Reload `(tag, delE, x0, y0)`, zero `[endsTmp, ufBase + 2)`, set `r21 := 0`
  have hr1_eq : ∀ r < 11, st1.regs r = st.regs r := fun r hr =>
    (hr1_lt11 r hr).trans (hrb3_lt13 r (by omega))
  let p1 : State := { st1 with regs := Function.update st1.regs 17 spBufBase }
  let p2 : State := { p1 with regs := Function.update p1.regs 18 spCntBase }
  let p3 : State := { p2 with regs := Function.update p2.regs 19 oldCntBase }
  let p4 : State := { p3 with regs := Function.update p3.regs 21 endsTmp }
  let p5 : State := { p4 with regs := Function.update p4.regs 20 ufBase }
  let p6 : State := { p5 with regs := Function.update p5.regs 13 tag }
  let p7 : State := { p6 with regs := Function.update p6.regs 14 delE }
  let p8 : State := { p7 with regs := Function.update p7.regs 15 x0 }
  let p9 : State := { p8 with regs := Function.update p8.regs 16 y0 }
  let p10 : State := { p9 with mem := Function.update p9.mem ufBase 0 }
  let p11 : State := { p10 with mem := Function.update p10.mem (ufBase + 1) 0 }
  let p12 : State := { p11 with mem := Function.update p11.mem endsTmp 0 }
  let p13 : State := { p12 with mem := Function.update p12.mem (endsTmp + 1) 0 }
  let stPreE : State := { p13 with regs := Function.update p13.regs 21 0 }
  have hp1 : Runs w p ω (.assign 17 (.bin .add (.reg 8) (.reg 6))) st1 .normal p1 4 :=
    runs_assign_iff.mpr ⟨spBufBase, by
      simp [Expr.eval, BinOp.eval, hr1_eq 8 (by omega), hr8, hr1_eq 6 (by omega), hr6,
        ← hspBuf_def, show spBufBase < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  have hp2 : Runs w p ω (.assign 18 (.bin .add (.reg 17) (.bin .mul (.const 4) (.bin .mul (.reg 3) (.reg 4)))))
      p1 .normal p2 8 :=
    runs_assign_iff.mpr ⟨spCntBase, by
      simp [p1, Expr.eval, BinOp.eval, hr1_eq 3 (by omega), hr3, hr1_eq 4 (by omega), hr4, hw4,
        ← hspCnt_def, show k * x.vCap < 2 ^ w by omega, show 4 * (k * x.vCap) < 2 ^ w by omega,
        show spCntBase < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  have hp3 : Runs w p ω (.assign 19 (.bin .add (.reg 18) (.reg 3))) p2 .normal p3 4 :=
    runs_assign_iff.mpr ⟨oldCntBase, by
      simp [p2, p1, Expr.eval, BinOp.eval, hr1_eq 3 (by omega), hr3, ← holdCnt_def,
        show oldCntBase < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  have hp4 : Runs w p ω (.assign 21 (.bin .add (.reg 19) (.reg 3))) p3 .normal p4 4 :=
    runs_assign_iff.mpr ⟨endsTmp, by
      simp [p3, p2, p1, Expr.eval, BinOp.eval, hr1_eq 3 (by omega), hr3, ← hends_def,
        show endsTmp < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  have hp5 : Runs w p ω (.assign 20 (.bin .add (.reg 21) (.const 2))) p4 .normal p5 4 :=
    runs_assign_iff.mpr ⟨ufBase, by
      simp [p4, p3, p2, p1, Expr.eval, BinOp.eval, hw2, ← huf_def,
        show ufBase < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  have hp6 : Runs w p ω (.assign 13 (.load (.reg 20))) p5 .normal p6 3 :=
    runs_assign_iff.mpr ⟨tag, Expr.eval_load_of_eq (by simp [p5, Expr.eval])
      ((hst1_above_sp ufBase (by omega) (by omega)).trans hb3_t), rfl, rfl, by simp [Expr.size]⟩
  have hp7 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 20) (.const 1)))) p6 .normal p7 5 :=
    runs_assign_iff.mpr ⟨delE, Expr.eval_load_of_eq (by
      simp [p6, p5, Expr.eval, BinOp.eval, hw1, show ufBase + 1 < 2 ^ w by omega])
      ((hst1_above_sp (ufBase + 1) (by omega) (by omega)).trans hb3_e), rfl, rfl, by simp [Expr.size]⟩
  have hp8 : Runs w p ω (.assign 15 (.load (.reg 21))) p7 .normal p8 3 :=
    runs_assign_iff.mpr ⟨x0, Expr.eval_load_of_eq (by simp [p7, p6, p5, p4, Expr.eval])
      ((hst1_above_sp endsTmp (by omega) (by omega)).trans hb3_x), rfl, rfl, by simp [Expr.size]⟩
  have hp9 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 21) (.const 1)))) p8 .normal p9 5 :=
    runs_assign_iff.mpr ⟨y0, Expr.eval_load_of_eq (by
      simp [p8, p7, p6, p5, p4, Expr.eval, BinOp.eval, hw1, show endsTmp + 1 < 2 ^ w by omega])
      ((hst1_above_sp (endsTmp + 1) (by omega) (by omega)).trans hb3_y), rfl, rfl, by simp [Expr.size]⟩
  have hp10 : Runs w p ω (.store (.reg 20) (.const 0)) p9 .normal p10 3 :=
    runs_store_iff.mpr ⟨ufBase, 0, by simp [p9, p8, p7, p6, p5, Expr.eval],
      by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hp11 : Runs w p ω (.store (.bin .add (.reg 20) (.const 1)) (.const 0)) p10 .normal p11 5 :=
    runs_store_iff.mpr ⟨ufBase + 1, 0, by
      simp [p10, p9, p8, p7, p6, p5, Expr.eval, BinOp.eval, hw1, show ufBase + 1 < 2 ^ w by omega],
      by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hp12 : Runs w p ω (.store (.reg 21) (.const 0)) p11 .normal p12 3 :=
    runs_store_iff.mpr ⟨endsTmp, 0, by simp [p11, p10, p9, p8, p7, p6, p5, p4, Expr.eval],
      by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hp13 : Runs w p ω (.store (.bin .add (.reg 21) (.const 1)) (.const 0)) p12 .normal p13 5 :=
    runs_store_iff.mpr ⟨endsTmp + 1, 0, by
      simp [p12, p11, p10, p9, p8, p7, p6, p5, p4, Expr.eval, BinOp.eval, hw1,
        show endsTmp + 1 < 2 ^ w by omega], by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hp14 : Runs w p ω (.assign 21 (.const 0)) p13 .normal stPreE 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hpreE_lt : ∀ a < endsTmp, stPreE.mem a = st1.mem a := fun a ha => by
    dsimp only [stPreE, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hpreE_zero : ZeroFrom stPreE.mem endsTmp := fun a ha => by
    by_cases h1 : a = endsTmp + 1
    · rw [h1]; simp [stPreE, p13]
    · by_cases h2 : a = endsTmp
      · rw [h2]; dsimp only [stPreE, p13, p12]; rw [Function.update_of_ne (by omega), Function.update_self]
      · by_cases h3 : a = ufBase + 1
        · rw [h3]; dsimp only [stPreE, p13, p12, p11]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
        · by_cases h4 : a = ufBase
          · rw [h4]; dsimp only [stPreE, p13, p12, p11, p10]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_self]
          · dsimp only [stPreE, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]
            rw [Function.update_of_ne h1, Function.update_of_ne h2,
              Function.update_of_ne h3, Function.update_of_ne h4]
            by_cases hu : a < updBuf
            · exact (hst1_above_sp a (by omega) hu).trans (hb3_ge_uf2 a (by omega))
            · exact hz1 a (by omega)
  -- Step E: Emit canonical split entries for all branches via `compEmitAllBranches_runs`
  have hstep_comb := hcomb (fun _ => []) [] S1 (fun j =>
    ⟨trivial, List.nodup_nil, by simp [S1], Finset.Subset.rfl, List.nodup_nil,
      List.nodup_nil, fun _ h => by simp at h, by simp [S1], Finset.Subset.rfl⟩)
  have hspStep_le : ∀ j : Fin k, spCnts j + (canonStepSplits (S j) u).length ≤ (S1 j).RF.R.card := fun j => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨ℓ₀, hBr0⟩, _⟩ := hrep
    obtain ⟨_, hndE, hsE, _, hndR, _, hdisjR, hsR, hRsub⟩ := hstep_comb j
    simp only [List.append_nil] at hndE hsE hndR hdisjR hsR
    have hsp1_set : sp1.toFinset = match (generalizing := false) u with | .split _ v' _ _ => {v'} | _ => ∅ := by
      rw [hsp1_eq]; exact sp1_toFinset_eq u
    rw [hsp1_eq] at hdisjR; rw [hsp1_set] at hsR
    have hlen_eq := canonStepSplits_length_eq_card_sdiff (hBr0 j).1 ((hBr0 j).2.2.1.symm ▸ hu_val)
      hndE hsE hndR hdisjR hsR
    have hsdiff_card := Finset.card_sdiff_add_card_eq_card hRsub
    have := hspCnts_le j; dsimp only [S1] at *; omega
  have hrep1_preE : CompLSFRepDirty W k b S1 x1 touched1 stPreE.mem :=
    compLSFRepDirty_of_agree hrep1 (fun a ha1 ha2 => hpreE_lt a (by omega))
  obtain ⟨stE, cEmit, hrEmit, hrE_lt13, hE_br, hE_uf, hE_fr, hcEmit⟩ :=
    compEmitAllBranches_runs (W := W) (w := w) (k := k) (b := b)
      (cntBase := cntBase) (spBufBase := spBufBase) (spCntBase := spCntBase)
      (oldCntBase := oldCntBase) (ufBase := ufBase)
      (tag := tag) (delE := delE) (x0 := x0) (y0 := y0)
      (S := S) (x1 := x1) (touched1 := touched1) (u := u)
      (oldCnts := cnts) (spCnts := spCnts) (cuts1 := cuts1) (st := stPreE) (ω := ω)
      hpZero hpSort hpRootVal hpEndRoots hpInitFind hpPairUnion hpClean hpEmit hw16
      (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨ℓ₀, hBr0⟩, _⟩ := hrep; exact ⟨ℓ₀, fun j => (hBr0 j).1⟩)
      (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨ℓ₀, hBr0⟩, _⟩ := hrep; exact fun j => (hBr0 j).2.2.1.symm ▸ hu_val)
      hrep1_preE (by omega) (by rw [hx1_1]; omega) (by rw [hx1_1]; omega)
      (by omega) (by omega) (by rw [hx1_1]; omega) ⟨htag_w, hdelE_w, hx0_w, hy0_w⟩
      (by simp [stPreE, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hr1_eq 0 (by omega), hr0])
      (by simp [stPreE, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hr1_eq 3 (by omega), hr3])
      (by simp [stPreE, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hr1_eq 4 (by omega), hr4, hx1_1])
      (by simp [stPreE, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hr1_eq 7 (by omega), hr7])
      (by simp [stPreE, p13, p12, p11, p10, p9, p8, p7, p6])
      (by simp [stPreE, p13, p12, p11, p10, p9, p8, p7])
      (by simp [stPreE, p13, p12, p11, p10, p9, p8])
      (by simp [stPreE, p13, p12, p11, p10, p9])
      (by simp [stPreE, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1])
      (by simp [stPreE, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2])
      (by simp [stPreE, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3])
      (by simp [stPreE, p13, p12, p11, p10, p9, p8, p7, p6, p5])
      (by simp [stPreE])
      (fun j => (hpreE_lt _ (by have := j.2; omega)).trans ((hst1_above_sp _ (by omega) (by have := j.2; omega)).trans (hb3_old j)))
      (fun j => (hpreE_lt _ (by have := j.2; omega)).trans (hbr1 j).1)
      (fun j i hi => by
        have hjv : j.1 * x.vCap + x.vCap ≤ k * x.vCap := by
          have := Nat.mul_le_mul_right x.vCap (show j.1 + 1 ≤ k by have := j.2; omega)
          rw [Nat.add_mul, Nat.one_mul] at this; exact this
        have hbd := le_trans (hbr1 j).2.2 (hx1_1 ▸ hR1_le j)
        rw [hx1_1, hpreE_lt _ (by omega), hpreE_lt _ (by omega)]
        exact (hbr1 j).2.1 i hi)
      (fun j => le_trans (hbr1 j).2.2 (hR1_le j))
      (fun j => by
        obtain ⟨_, hndE, hsE, _, _, _, _, hsR, _⟩ := hstep_comb j
        simp only [List.append_nil] at hndE hsE hsR
        have hsp1_set : sp1.toFinset = match (generalizing := false) u with | .split _ v' _ _ => {v'} | _ => ∅ := by
          rw [hsp1_eq]; exact sp1_toFinset_eq u
        rw [hsp1_set] at hsR
        refine ⟨hndE, hsE, hsR, fun q hq => ?_⟩
        have hqR : q.2 ∈ (S1 j).RF.R := by
          have : q.2 ∈ (S1 j).RF.R \ (S j).RF.R := by
            rw [← hsR]; exact Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨q, hq, rfl⟩))
          exact (Finset.mem_sdiff.mp this).1
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨ℓ₁, hBr1⟩, _, hT1, _⟩ := hrep1
        have hT1j := compEdgeTrack_of_same_graph hT1 (hBr1 j).2.1 (hBr1 j).2.2.1
          (hBr1 j).2.2.2.2.1 (hBr1 j).2.2.2.2.2.2
        exact hT1j.hVlt q.2 ((compLSF_RF_isRSF (hBr1 j).1).2.2.1 hqR))
      htag_spec
      (fun j => (hpreE_lt _ (by have := j.2; omega)).trans ((hst1_above_sp _ (by omega) (by have := j.2; omega)).trans ((hb3_lt_old _ (by have := j.2; omega)).trans (hspCnts_m j))))
      (fun j => le_trans (hspStep_le j) (hR1_le j))
      (fun a ha1 _ => hpreE_zero a (by omega))
  -- Step F: Increment `r10 := idx + 1` and chain execution
  let st2 : State := { stE with regs := Function.update stE.regs 10 (idx + 1) }
  have hrun_inc : Runs w p ω (.assign 10 (.bin .add (.reg 10) (.const 1))) stE .normal st2 4 :=
    runs_assign_iff.mpr ⟨idx + 1, by
      simp [Expr.eval, BinOp.eval, hrE_lt13 10 (by omega), stPreE, p13, p12, p11, p10, p9, p8, p7, p6,
        p5, p4, p3, p2, p1, hr1_eq 10 (by omega), hr10, hw1, show idx + 1 < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hbody_run : Runs w p ω (compBatchWithSplitsBodyStmt bIns bDel bSplit bEnds bEmit)
      st .normal st2 (cCp + cMeta + cStep + cEmit + 117) := by
    unfold compBatchWithSplitsBodyStmt
    have s25 := runs_seq_iff.mpr (Or.inr ⟨stE, cEmit, 4, hrEmit, hrun_inc, rfl⟩)
    have s24 := runs_seq_iff.mpr (Or.inr ⟨stPreE, 2, _, hp14, s25, rfl⟩)
    have s23 := runs_seq_iff.mpr (Or.inr ⟨p13, 5, _, hp13, s24, rfl⟩)
    have s22 := runs_seq_iff.mpr (Or.inr ⟨p12, 3, _, hp12, s23, rfl⟩)
    have s21 := runs_seq_iff.mpr (Or.inr ⟨p11, 5, _, hp11, s22, rfl⟩)
    have s20 := runs_seq_iff.mpr (Or.inr ⟨p10, 3, _, hp10, s21, rfl⟩)
    have s19 := runs_seq_iff.mpr (Or.inr ⟨p9, 5, _, hp9, s20, rfl⟩)
    have s18 := runs_seq_iff.mpr (Or.inr ⟨p8, 3, _, hp8, s19, rfl⟩)
    have s17 := runs_seq_iff.mpr (Or.inr ⟨p7, 5, _, hp7, s18, rfl⟩)
    have s16 := runs_seq_iff.mpr (Or.inr ⟨p6, 3, _, hp6, s17, rfl⟩)
    have s15 := runs_seq_iff.mpr (Or.inr ⟨p5, 4, _, hp5, s16, rfl⟩)
    have s14 := runs_seq_iff.mpr (Or.inr ⟨p4, 4, _, hp4, s15, rfl⟩)
    have s13 := runs_seq_iff.mpr (Or.inr ⟨p3, 4, _, hp3, s14, rfl⟩)
    have s12 := runs_seq_iff.mpr (Or.inr ⟨p2, 8, _, hp2, s13, rfl⟩)
    have s11 := runs_seq_iff.mpr (Or.inr ⟨p1, 4, _, hp1, s12, rfl⟩)
    have s10 := runs_seq_iff.mpr (Or.inr ⟨st1, cStep, _, hrun_step0, s11, rfl⟩)
    have s9 := runs_seq_iff.mpr (Or.inr ⟨b3, cMeta, _, hrun_meta, s10, rfl⟩)
    have s8 := runs_seq_iff.mpr (Or.inr ⟨b2, 3, _, hb2, s9, rfl⟩)
    have s7 := runs_seq_iff.mpr (Or.inr ⟨b1, 3, _, hb1, s8, rfl⟩)
    have s6 := runs_seq_iff.mpr (Or.inr ⟨aCp, cCp, _, haCp, s7, rfl⟩)
    have s5 := runs_seq_iff.mpr (Or.inr ⟨a5, 4, _, ha5, s6, rfl⟩)
    have s4 := runs_seq_iff.mpr (Or.inr ⟨a4, 4, _, ha4, s5, rfl⟩)
    have s3 := runs_seq_iff.mpr (Or.inr ⟨a3, 4, _, ha3, s4, rfl⟩)
    have s2 := runs_seq_iff.mpr (Or.inr ⟨a2, 8, _, ha2, s3, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨a1, 4, _, ha1, s2, by omega⟩)
  have hst2_lt_sp : ∀ a < spBufBase, st2.mem a = st1.mem a := fun a ha =>
    (hE_fr a (fun _ => by omega) (fun _ => Or.inl (by omega)) (Or.inl (by omega))).trans (hpreE_lt a (by omega))
  have hrep1_st2 : CompLSFRepDirty W k b S1 x1 touched1 st2.mem :=
    compLSFRepDirty_of_agree hrep1 (fun a ha1 ha2 => hst2_lt_sp a (by omega))
  have hst2_zero : ZeroFrom st2.mem endsTmp := fun a ha => by
    by_cases huf_a : ufBase ≤ a ∧ a < ufBase + ufEmitScratchSize x1.vCap
    · exact hE_uf a huf_a.1 huf_a.2
    · rw [hE_fr a (fun j => by have := j.2; omega) (fun j => Or.inr (by
        have hjv : j.1 * x1.vCap + x1.vCap ≤ k * x1.vCap := by
          have := Nat.mul_le_mul_right x1.vCap (show j.1 + 1 ≤ k by have := j.2; omega)
          rw [Nat.add_mul, Nat.one_mul] at this; exact this
        have := le_trans (hspStep_le j) (hR1_le j); rw [hx1_1] at hjv ⊢; omega))
        (by rw [not_and_or, not_le, not_lt] at huf_a; exact huf_a)]
      exact hpreE_zero a ha
  -- Cost + potential bound
  have hcost_step : (cCp + cMeta + cStep + cEmit + 117) +
        120 * (∑ j : Fin k, (cuts1 j).length) +
        180 * (∑ j : Fin k, (canonStepSplits (S j) u).length) +
        compPhiFull k b x1 st2.mem ≤
      compPhiFull k b x st.mem + 2640 * k +
        k * ((touchedComps cs0 u).filter fun C => 1 ≤ (compGraph cs0.G₀ C).m).sum (fun C =>
          lsfBatchCostFactor * ((1 + projUpdWords mem0 cs0 C uPtr u) * x.L_w + 1) +
          lsfBatchCostFactor * (projUpdWords mem0 cs0 C uPtr u * x.L_w)) := by
    have hphi_b3 : compPhi b x b3.mem = compPhi b x st.mem :=
      (compLSFRep_local W k b S x st.mem b3.mem (fun a ha => (hb3_lt_old a (by have := ha.2; omega)).symm)).2.symm
    have hphi_st2 : compPhiFull k b x1 st2.mem = compPhiFull k b x1 st1.mem :=
      (compLSFRepFull_local W k b S1 x1 st1.mem st2.mem (fun a ha => (hst2_lt_sp a (by have := ha.2; omega)).symm)).2.symm
    have hsp_drop := compSplitPhi_step_drop hrep hrep1 hu_val hx1_6
    have hstep_sp_le : (∑ j : Fin k, (canonStepSplits (S j) u).length) ≤
        k + ∑ j : Fin k, ((forestAfterInput (S j).RF.F u).E \ (S1 j).RF.F.E).card := by
      calc (∑ j : Fin k, (canonStepSplits (S j) u).length)
          ≤ ∑ j : Fin k, (1 + ((forestAfterInput (S j).RF.F u).E \ (S1 j).RF.F.E).card) :=
            Finset.sum_le_sum fun j _ => canonStepSplits_length_le_succ_t (S j) u
        _ = k + ∑ j : Fin k, ((forestAfterInput (S j).RF.F u).E \ (S1 j).RF.F.E).card := by
            rw [Finset.sum_add_distrib]; simp
    set sumT := ∑ j : Fin k, ((forestAfterInput (S j).RF.F u).E \ (S1 j).RF.F.E).card
    set logM := Nat.log 2 (x.m0Total + 2) + 1
    have h180_le : 180 * sumT ≤ 500 * logM * sumT :=
      Nat.mul_le_mul_right sumT (by dsimp [logM]; omega)
    have hcEmit' : cEmit ≤ 1500 * logM * sumT + 1400 * k + 10 := by
      simpa [hx1_6, logM, sumT, S1] using hcEmit
    have hsp_drop' : 2000 * logM * sumT + compSplitPhi k b x1 st1.mem ≤ compSplitPhi k b x st.mem := by
      simpa [logM, sumT, S1] using hsp_drop
    have h1000 : 1000 ≤ 1000 * k := Nat.le_mul_of_pos_right 1000 hk
    have h2000 : 1500 * logM * sumT + 500 * logM * sumT = 2000 * logM * sumT := by ring
    rw [hphi_b3] at hcost1
    rw [hphi_st2]
    simp only [compPhiFull] at *
    dsimp only [S1, cs0] at hcost1 ⊢
    omega
  refine ⟨st2, cCp + cMeta + cStep + cEmit + 117, x1, touched1, cuts1, sp1, hbody_run,
    fun r hr => by
      simp only [st2, Function.update_of_ne (show r ≠ 10 by omega), hrE_lt13 r (by omega),
        stPreE, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1,
        Function.update_of_ne (show r ≠ 21 by omega), Function.update_of_ne (show r ≠ 16 by omega),
        Function.update_of_ne (show r ≠ 15 by omega), Function.update_of_ne (show r ≠ 14 by omega),
        Function.update_of_ne (show r ≠ 13 by omega), Function.update_of_ne (show r ≠ 20 by omega),
        Function.update_of_ne (show r ≠ 19 by omega), Function.update_of_ne (show r ≠ 18 by omega),
        Function.update_of_ne (show r ≠ 17 by omega)]
      exact hr1_eq r (by omega),
    by simp [st2],
    by simp [st2, hrE_lt13 11 (by omega), stPreE, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hr1_11],
    by simp [st2, hrE_lt13 12 (by omega), stPreE, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hr1_12],
    hsp1_le, hx1_1, hx1_2, hx1_3, hx1_4, hx1_5, hx1_6, hx1_7, hx1_8,
    hrep1_st2, hnd1, hlt1, hlen1, hlen_ge1,
    (hst2_lt_sp heap (by omega)).trans hhp1,
    fun i hi => (hst2_lt_sp _ (by omega)).trans (hls1 i hi),
    fun i hi => (hst2_lt_sp _ (by omega)).trans (hsp1_m i hi),
    fun j => ⟨(hst2_lt_sp _ (by have := j.2; omega)).trans (hbr1 j).1,
      fun i hi => by
        have hjv : j.1 * x.vCap + x.vCap ≤ k * x.vCap := by
          have := Nat.mul_le_mul_right x.vCap (show j.1 + 1 ≤ k by have := j.2; omega)
          rw [Nat.add_mul, Nat.one_mul] at this; exact this
        have hbd := le_trans (hbr1 j).2.2 (hx1_1 ▸ hR1_le j)
        rw [hst2_lt_sp _ (by dsimp only [rootsBase]; omega), hst2_lt_sp _ (by dsimp only [fDelBase]; omega)]
        exact (hbr1 j).2.1 i hi,
      (hbr1 j).2.2⟩,
    fun j => ⟨(hE_br j).1, hspStep_le j, by simpa [hx1_1] using (hE_br j).2⟩,
    hcomb,
    fun a ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9 ha10 ha11 =>
      (hE_fr a ha9 (fun j => by rw [hx1_1]; exact ha8 j) (Or.inl (by omega))).trans
      ((hpreE_lt a ha11).trans
      ((hfr1 a ha1 ha2 ha3 ha4 ha5 ha6 ha7 (by omega)).trans
      ((hb3_fr a (Or.inl ha11)).trans (hcp_fr a ha10)))),
    hst2_zero, hcost_step⟩

end

end MinCostFlow.SparseCore.Program
