module

public import MinCostFlow.SparseCore.Program.CompSplitListBatchBase
import WordRAM.Tactic

/-!
# Full `op 0` Verification with Canonical Split Lists (`CompSplitListBatch`)

Verifies `compBatchWithSplitsProc` (`compLSFDS_op0_withSplits`): establishes `CompLSFRepAt`,
`CompBatchPostFull` (both `Read.LSFChangeAt`/`CompForestCutsValid` AND `CompSplitListAt`),
`(compLSFRepFull W k).Respects`, and the exact amortized cost bound against `compPhiFull`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

set_option maxHeartbeats 1200000 in
open Classical in
/-- Full verification of `compBatchWithSplitsProc` (`op 0` of `compLSFDSFullWithSplits`) for an
explicitly pinned batch `U`. -/
theorem compLSFDS_op0_withSplits_for {W : LSFWindowImpl}
    {w k b batchPtr heap totalWords bZero bLogAdd bPreLog bLsf bCons bErase bApp bMark bDisp bIns bDel bSplit
      bSort bRootVal bEnds bEndRoots bUFInitFind bUFPairUnion bUFClean bEmit bPackChg bPackSp : ℕ}
    {G₀ : MGraph} {S : CompLSFFamily k} {x : CompLSFMeta k}
    {U : List Update} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool} {p : Program}
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
    (hpPackChg : p.procs[bPackChg]? = some (compPackChangesProc bZero))
    (hpPackSp : p.procs[bPackSp]? = some (compPackSplitsProc bZero))
    (hrep : CompLSFRepAt W k b S x mem)
    (hk : 1 ≤ k) (hw16 : 16 ≤ 2 ^ w)
    (hBAt : BatchAt mem batchPtr (S ⟨0, hk⟩).G U totalWords)
    (hBVal : (S ⟨0, hk⟩).G.BatchIsValid U)
    (hBCaps : BatchWithinCaps (mem (b + compOffVCap)) (mem (b + compOffECap)) U)
    (hBWords : ∀ i < totalWords, mem (batchPtr + i) < 2 ^ w)
    (hBHeap : batchPtr + totalWords ≤ heap)
    (hBOut : ∀ i < totalWords, batchPtr + i < b ∨ mem (b + compOffEndAddr) ≤ batchPtr + i)
    (hargs : ∀ a ∈ [b, batchPtr, heap], a < 2 ^ w)
    (hdisj : ∀ a, compFoot b x a → a < heap)
    (hz : ZeroFrom mem heap)
    (hsp : heap + (compLSFDSFullWithSplits W w k G₀).space 0 S [b, batchPtr, heap] mem < 2 ^ w) :
    ∃ o st' c,
      Runs w p ω (compBatchWithSplitsProc bZero bIns bDel bSplit bEnds bEmit bPackChg bPackSp)
        (startState [b, batchPtr, heap] mem pos) o st' c ∧
      ∃ S' x',
        CompLSFRepAt W k b S' x' st'.mem ∧
        (compLSFDSFullWithSplits W w k G₀).post 0 S [b, batchPtr, heap] mem S' st'.mem ∧
        (compLSFRepFull W k).Respects (compFoot b x) heap
          ((compLSFDSFullWithSplits W w k G₀).space 0 S [b, batchPtr, heap] mem) mem o.value b x' st'.mem ∧
        c + compPhiFull k b x' st'.mem ≤
          (compLSFDSFullWithSplits W w k G₀).cost 0 S [b, batchPtr, heap] mem + compPhiFull k b x mem ∧
        x'.vCap = x.vCap ∧ x'.eCap = x.eCap ∧ x'.L_w = x.L_w ∧
        CompBatchPostFullAt w k S [b, batchPtr, heap] mem o.value U S' st'.mem := by
  have hrep_orig := hrep
  obtain ⟨hk', _, _, _, hLw, _, heCap1, hnumC, _, hTE, hhdr, ⟨ℓ₀, hBr⟩, _, hT, _, _, _, _, _, _, _, _, _, _⟩ := hrep
  have hend_heap : x.endAddr ≤ heap := by
    have hb_lt_end : b < x.endAddr := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hTE; omega
    have hlt := hdisj (x.endAddr - 1) ⟨by omega, by omega⟩; omega
  have hmem_vCap : mem (b + compOffVCap) = x.vCap := hhdr.1
  have hmem_eCap : mem (b + compOffECap) = x.eCap := hhdr.2.1
  have hmem_k : mem (b + compOffK) = k := hhdr.2.2.1
  have hmem_Lw : mem (b + compOffLW) = x.L_w := hhdr.2.2.2.1
  have hmem_tmPtr : mem (b + compOffTouchMarkPtr) = compTouchMarkBase b x.vCap x.eCap :=
    hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmem_end : mem (b + compOffEndAddr) = x.endAddr :=
    hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hmem_vCap, hmem_eCap] at hBCaps
  rw [hmem_end] at hBOut
  have htw_eq : batchMemLen mem batchPtr = totalWords := batchMemLen_eq hBAt
  have hnumU_m : mem batchPtr = U.length := hBAt.2.1
  have htw_ge1 : 1 ≤ totalWords := by have := hBAt.1; omega
  have hsp_eq : (compLSFDSFullWithSplits W w k G₀).space 0 S [b, batchPtr, heap] mem =
      11 + 3 * U.length + totalWords + 2 * x.eCap + 8 * x.vCap + k * (8 + 12 * x.vCap) := by
    simp only [compLSFDSFullWithSplits, ↓reduceIte, compBatchSpaceFull, List.getD_cons_zero,
      List.getD_cons_succ, hmem_vCap, hmem_eCap, htw_eq, hnumU_m]
  have hsp_lt : heap + (11 + 3 * U.length + totalWords + 2 * x.eCap + 8 * x.vCap + k * (8 + 12 * x.vCap)) < 2 ^ w := by
    rwa [hsp_eq] at hsp
  set numU := U.length
  set tmBase := compTouchMarkBase b x.vCap x.eCap
  set cntBase := heap + 1 + 2 * numU + k * (5 + 6 * x.vCap)
  set splitBase := cntBase + k + 2 * (k * x.vCap)
  set spBufBase := splitBase + numU
  set spCntBase := spBufBase + 4 * (k * x.vCap)
  set oldCntBase := spCntBase + k
  set endsTmp := oldCntBase + k
  set ufBase := endsTmp + 2
  set updBuf := ufBase + (8 * x.vCap + 3)
  have hupd_eq : updBuf = heap + 6 + 3 * numU + 8 * x.vCap + k * (8 + 12 * x.vCap) := by
    dsimp only [updBuf, ufBase, endsTmp, oldCntBase, spCntBase, spBufBase, splitBase, cntBase]; ring
  have htm_le_end : tmBase + x.vCap ≤ x.endAddr := by
    have : tmBase + x.vCap ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [tmBase, compTablesEnd, compHandlesBase, compStaticSize, compTouchMarkBase,
        compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base,
        compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega
    omega
  have hb_hdr_lt : b + compHdrSize ≤ x.endAddr := by
    have : b + compHdrSize ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega
    omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  have hw6 : 6 < 2 ^ w := by omega
  have hw8 : 8 < 2 ^ w := by omega
  have hb_off_w : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w := fun off hoff => by
    dsimp only [compHdrSize] at hb_hdr_lt hoff; omega
  have hkv_lt : 4 * (k * x.vCap) < 2 ^ w := by
    have : 4 * (k * x.vCap) ≤ k * (8 + 12 * x.vCap) := by
      calc 4 * (k * x.vCap) = k * (4 * x.vCap) := by ring
        _ ≤ k * (8 + 12 * x.vCap) := Nat.mul_le_mul_left k (by omega)
    omega
  -- Step 1: Prefix (15 statements)
  set st0 := startState [b, batchPtr, heap] mem pos
  let r1 := Function.update st0.regs 3 k
  let r2 := Function.update r1 4 x.vCap
  let r3 := Function.update r2 5 tmBase
  let r4 := Function.update r3 6 numU
  let r5 := Function.update r4 7 cntBase
  let r6 := Function.update r5 8 splitBase
  let r7 := Function.update r6 17 spBufBase
  let r8 := Function.update r7 18 spCntBase
  let r9 := Function.update r8 19 oldCntBase
  let r10 := Function.update r9 20 endsTmp
  let r11 := Function.update r10 9 updBuf
  let r12 := Function.update r11 10 0
  let r13 := Function.update r12 11 (batchPtr + 1)
  let r14 := Function.update r13 12 0
  have hupd_mem_eq : Function.update mem heap 0 = mem := by
    funext a; by_cases ha : a = heap
    · subst ha; rw [Function.update_self, hz a (le_refl _)]
    · simp [ha]
  let stP : State := { st0 with regs := r14 }
  have hp1 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 0) (.const compOffK))))
      st0 .normal { st0 with regs := r1 } 5 :=
    runs_assign_iff.mpr ⟨k, Expr.eval_load_of_eq (by
      have := hb_off_w compOffK (by decide); simp [st0, startState, Expr.eval, BinOp.eval, this.1, this.2]) hmem_k,
      rfl, rfl, by simp [Expr.size]⟩
  have hp2 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const compOffVCap))))
      { st0 with regs := r1 } .normal { st0 with regs := r2 } 5 :=
    runs_assign_iff.mpr ⟨x.vCap, Expr.eval_load_of_eq (by
      have := hb_off_w compOffVCap (by decide); simp [r1, st0, startState, Expr.eval, BinOp.eval, this.1, this.2]) hmem_vCap,
      rfl, rfl, by simp [Expr.size]⟩
  have hp3 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const compOffTouchMarkPtr))))
      { st0 with regs := r2 } .normal { st0 with regs := r3 } 5 :=
    runs_assign_iff.mpr ⟨tmBase, Expr.eval_load_of_eq (by
      have := hb_off_w compOffTouchMarkPtr (by decide)
      simp [r2, r1, st0, startState, Expr.eval, BinOp.eval, this.1, this.2]) hmem_tmPtr,
      rfl, rfl, by simp [Expr.size]⟩
  have hp4 : Runs w p ω (.assign 6 (.load (.reg 1)))
      { st0 with regs := r3 } .normal { st0 with regs := r4 } 3 :=
    runs_assign_iff.mpr ⟨numU, Expr.eval_load_of_eq (by
      simp [r3, r2, r1, st0, startState, Expr.eval]) hnumU_m, rfl, rfl, by simp [Expr.size]⟩
  have hp5 : Runs w p ω (.assign 7 (.bin .add (.bin .add (.bin .add (.reg 2) (.const 1)) (.bin .mul (.const 2) (.reg 6)))
      (.bin .mul (.reg 3) (.bin .add (.const 5) (.bin .mul (.const 6) (.reg 4))))))
      { st0 with regs := r4 } .normal { st0 with regs := r5 } 16 :=
    runs_assign_iff.mpr ⟨cntBase, by
      have hkm : k * (5 + 6 * x.vCap) ≤ k * (8 + 12 * x.vCap) := Nat.mul_le_mul_left k (by omega)
      have h1k : 1 * (8 + 12 * x.vCap) ≤ k * (8 + 12 * x.vCap) := Nat.mul_le_mul_right _ hk
      simp [r4, r3, r2, r1, st0, startState, Expr.eval, BinOp.eval, hw1, hw2, hw5, hw6,
        show 6 * x.vCap < 2 ^ w by omega, show 5 + 6 * x.vCap < 2 ^ w by omega,
        show k * (5 + 6 * x.vCap) < 2 ^ w by omega, show heap + 1 < 2 ^ w by omega,
        show 2 * numU < 2 ^ w by omega, show heap + 1 + 2 * numU < 2 ^ w by omega,
        show cntBase < 2 ^ w by omega, cntBase], rfl, rfl, by simp [Expr.size]⟩
  have hp6 : Runs w p ω (.assign 8 (.bin .add (.bin .add (.reg 7) (.reg 3))
      (.bin .mul (.const 2) (.bin .mul (.reg 3) (.reg 4)))))
      { st0 with regs := r5 } .normal { st0 with regs := r6 } 10 :=
    runs_assign_iff.mpr ⟨splitBase, by
      simp [r5, r4, r3, r2, r1, st0, startState, Expr.eval, BinOp.eval, hw2,
        show k * x.vCap < 2 ^ w by omega, show 2 * (k * x.vCap) < 2 ^ w by omega,
        show cntBase + k < 2 ^ w by omega, show splitBase < 2 ^ w by omega, splitBase],
      rfl, rfl, by simp [Expr.size]⟩
  have hp7 : Runs w p ω (.assign 17 (.bin .add (.reg 8) (.reg 6)))
      { st0 with regs := r6 } .normal { st0 with regs := r7 } 4 :=
    runs_assign_iff.mpr ⟨spBufBase, by
      simp [r6, r5, r4, Expr.eval, BinOp.eval, show spBufBase < 2 ^ w by omega, spBufBase],
      rfl, rfl, by simp [Expr.size]⟩
  have hp8 : Runs w p ω (.assign 18 (.bin .add (.reg 17) (.bin .mul (.const 4) (.bin .mul (.reg 3) (.reg 4)))))
      { st0 with regs := r7 } .normal { st0 with regs := r8 } 8 :=
    runs_assign_iff.mpr ⟨spCntBase, by
      simp [r7, r6, r5, r4, r3, r2, r1, Expr.eval, BinOp.eval, hw4,
        show k * x.vCap < 2 ^ w by omega, hkv_lt, show spCntBase < 2 ^ w by omega, spCntBase],
      rfl, rfl, by simp [Expr.size]⟩
  have hp9 : Runs w p ω (.assign 19 (.bin .add (.reg 18) (.reg 3)))
      { st0 with regs := r8 } .normal { st0 with regs := r9 } 4 :=
    runs_assign_iff.mpr ⟨oldCntBase, by
      simp [r8, r7, r6, r5, r4, r3, r2, r1, Expr.eval, BinOp.eval, show oldCntBase < 2 ^ w by omega, oldCntBase],
      rfl, rfl, by simp [Expr.size]⟩
  have hp10 : Runs w p ω (.assign 20 (.bin .add (.reg 19) (.reg 3)))
      { st0 with regs := r9 } .normal { st0 with regs := r10 } 4 :=
    runs_assign_iff.mpr ⟨endsTmp, by
      simp [r9, r8, r7, r6, r5, r4, r3, r2, r1, Expr.eval, BinOp.eval, show endsTmp < 2 ^ w by omega, endsTmp],
      rfl, rfl, by simp [Expr.size]⟩
  have hp11 : Runs w p ω (.assign 9 (.bin .add (.bin .add (.reg 20) (.const 2))
      (.bin .add (.bin .mul (.const 8) (.reg 4)) (.const 3))))
      { st0 with regs := r10 } .normal { st0 with regs := r11 } 10 :=
    runs_assign_iff.mpr ⟨updBuf, by
      simp [r10, r9, r8, r7, r6, r5, r4, r3, r2, Expr.eval, BinOp.eval, hw2, hw3, hw8,
        show endsTmp + 2 < 2 ^ w by omega, show 8 * x.vCap < 2 ^ w by omega,
        show 8 * x.vCap + 3 < 2 ^ w by omega, show updBuf < 2 ^ w by omega, updBuf, ufBase],
      rfl, rfl, by simp [Expr.size]⟩
  have hp12 : Runs w p ω (.store (.reg 2) (.const 0))
      { st0 with regs := r11 } .normal { st0 with regs := r11 } 3 :=
    runs_store_iff.mpr ⟨heap, 0, by simp [r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState, Expr.eval],
      by simp [Expr.eval, hw0'], rfl, by simp [st0, startState, hupd_mem_eq], by simp [Expr.size]⟩
  have hp13 : Runs w p ω (.assign 10 (.const 0))
      { st0 with regs := r11 } .normal { st0 with regs := r12 } 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hp14 : Runs w p ω (.assign 11 (.bin .add (.reg 1) (.const 1)))
      { st0 with regs := r12 } .normal { st0 with regs := r13 } 4 :=
    runs_assign_iff.mpr ⟨batchPtr + 1, by
      simp [r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState, Expr.eval, BinOp.eval, hw1,
        show batchPtr + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  have hp15 : Runs w p ω (.assign 12 (.const 0))
      { st0 with regs := r13 } .normal stP 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  -- Step 2: Main batch loop with canonical split emission
  obtain ⟨stL, cL, xL, touched', cuts, sp, hrunL, hrL_lt10, hrL_12,
    hxL1, hxL2, hxL3, hxL4, hxL5, hxL6, hxL7, hxL8, hrepL, hndL, hltL, hlenL, hspL_le,
    hhpL, hlsL, hspL_m, hbrL, hspL_br, hfrL, hzL, hcostL⟩ :=
    compBatchWithSplitsLoop_runs (W := W) (w := w) (k := k) (b := b)
      (batchPtr := batchPtr) (heap := heap) (numU := numU)
      (cntBase := cntBase) (splitBase := splitBase) (spBufBase := spBufBase)
      (spCntBase := spCntBase) (oldCntBase := oldCntBase) (endsTmp := endsTmp)
      (ufBase := ufBase) (updBuf := updBuf) (totalWords := totalWords) (mem0 := mem) (ω := ω)
      hpZero hpLogAdd hpPreLog hpLsf hpCons hpErase hpApp hpMark hpDisp hpIns hpDel hpSplit
      hpSort hpRootVal hpEnds hpEndRoots hpInitFind hpPairUnion hpClean hpEmit
      hw16 hBWords hBHeap rfl rfl rfl rfl
      U 0 (batchPtr + 1) 0 (totalWords - 1) S x [] (fun _ => 0) (fun _ => 0) stP
      (by simp [numU]) (le_refl _) (by omega) hBOut (fun _ _ => rfl)
      (compLSFRepDirty_nil_iff.mpr hrep_orig) List.nodup_nil (fun _ h => by simp at h)
      (by simp) (le_refl 0)
      (by simp [stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState])
      (by simp [stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState])
      (by simp [stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1])
      (by simp [stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2])
      (by simp [stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4])
      (by simp [stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5])
      (by simp [stP, r14, r13, r12, r11, r10, r9, r8, r7, r6])
      (by simp [stP, r14, r13, r12, r11])
      (by simp [stP, r14, r13, r12]) (by simp [stP, r14, r13]) (by simp [stP, r14])
      hBAt.2.2 hBVal hBCaps hend_heap (by dsimp only [cntBase]; omega) (le_refl _) rfl
      (le_refl _) (by omega) (fun z hz' => hz z (by omega))
      (by simpa [stP, st0, startState] using hz heap (le_refl _)) (fun _ hi => by simp at hi)
      (fun j => hz (cntBase + j.1) (by omega)) (fun _ => Nat.zero_le _)
      (fun j => hz (spCntBase + j.1) (by omega)) (fun _ => Nat.zero_le _)
  -- Step 3: Load `numTouched`, unmark `touchMark`, zero gap `[heap + 1 + touched'.length, heap + 1 + 2 * numU)`
  let stU0 : State := { stL with regs := Function.update stL.regs 13 touched'.length }
  let stU1 : State := { stU0 with regs := Function.update stU0.regs 14 0 }
  have hrL_eq : ∀ r < 10, stL.regs r = stP.regs r := hrL_lt10
  have hu0 : Runs w p ω (.assign 13 (.load (.reg 2))) stL .normal stU0 3 :=
    runs_assign_iff.mpr ⟨touched'.length, Expr.eval_load_of_eq (by
      simp [Expr.eval, hrL_eq 2 (by omega), stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState]) hhpL, rfl, rfl, by simp [Expr.size]⟩
  have hu1 : Runs w p ω (.assign 14 (.const 0)) stU0 .normal stU1 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨stU, cU, hrunU, hrU_lt14, hU_zero, hU_fr, hcU⟩ :=
    compUnmarkLoop_runs (heap := heap) (tmBase := tmBase) (vCap := x.vCap) (touched := touched')
      (st := stU1) (ω := ω) hw16 (by omega) (by omega) (by omega)
      (fun c hc => lt_of_lt_of_le (hltL c hc) hnumC)
      (by simp [stU1, stU0, hrL_eq 2 (by omega), stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState])
      (by simp [stU1, stU0, hrL_eq 5 (by omega), stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3])
      (by simp [stU1, stU0]) (by simp [stU1]) hlsL
  have hU_ge_h : ∀ a, heap ≤ a → stU.mem a = stL.mem a := fun a ha =>
    hU_fr a fun c hc => by have := lt_of_lt_of_le (hltL c hc) hnumC; omega
  set ptrBase := heap + 1 + touched'.length
  set gapLen := 2 * numU - touched'.length
  obtain ⟨oZ, stZ0, cZ, hrunZ0, _, hZ_zero, hZ_fr, hcZ⟩ :=
    compBatchZeroRange_call (ptr := ptrBase) (len := gapLen) (mem := stU.mem) (pos := stU.pos) (ω := ω)
      hpZero hw16 (by omega)
  let stZ : State := { stU with regs := Function.update stU.regs 15 oZ.value, mem := stZ0.mem, pos := stZ0.pos }
  have hrZ_lt14 : ∀ r < 14, stZ.regs r = stU1.regs r := fun r hr => by
    simp only [stZ, Function.update_of_ne (show r ≠ 15 by omega)]; exact hrU_lt14 r hr
  have hrunZ : Runs w p ω (.call 15 bZero
      [.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 13),
       .bin .sub (.bin .mul (.const 2) (.reg 6)) (.reg 13)]) stU .normal stZ (cZ + 11) := by
    rw [runs_call_iff]
    refine ⟨[ptrBase, gapLen], compZeroRangeProc, oZ, stZ0, cZ, ?_, hpZero, hrunZ0, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
    have hr2_U : stU.regs 2 = heap := (hrU_lt14 2 (by omega)).trans (by simp [stU1, stU0, hrL_eq 2 (by omega), stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState])
    have hr6_U : stU.regs 6 = numU := (hrU_lt14 6 (by omega)).trans (by simp [stU1, stU0, hrL_eq 6 (by omega), stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4])
    have hr13_U : stU.regs 13 = touched'.length := (hrU_lt14 13 (by omega)).trans (by simp [stU1, stU0])
    simp [evalArgs, Expr.eval, BinOp.eval, hr2_U, hr6_U, hr13_U, hw1, hw2,
      show heap + 1 < 2 ^ w by omega, show ptrBase < 2 ^ w by omega,
      show 2 * numU < 2 ^ w by omega, show 2 * numU - touched'.length < 2 ^ w by omega, ptrBase, gapLen]
  -- Step 4: Pack `LSFChangeAt` records at `[ptrBase + k, midEnd)` via `compPackChanges_runs_gen`
  set S' := compLSFBatchFamily S U
  let splits : Fin k → List CompSplitEntry := fun j => canonSplitList (S j) U
  have hR'_le : ∀ j : Fin k, (S' j).RF.R.card ≤ x.vCap := fun j => by
    obtain ⟨ℓ₀', hBr'⟩ := hrepL.2.2.2.2.2.2.2.2.2.2.2.1
    have hT' := compEdgeTrack_of_same_graph hrepL.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (hBr' j).2.1 (hBr' j).2.2.1 (hBr' j).2.2.2.2.1 (hBr' j).2.2.2.2.2.2
    rw [← hxL1]
    exact (Finset.card_le_card fun r hr => Finset.mem_range.mpr
      (hT'.hVlt r ((compLSF_RF_isRSF (hBr' j).1).2.2.1 hr))).trans (by simp)
  have hcut_bd : ∀ j : Fin k, (cuts j).length + sp.length ≤ x.vCap := fun j => by
    obtain ⟨_, _, _, _, _, _, hndR, hndS, hdisjR, hsR, _⟩ := hbrL j
    have hcard_u : ((cuts j).map Prod.snd).toFinset.card + sp.toFinset.card =
        ((S' j).RF.R \ (S j).RF.R).card := by
      rw [← hsR, Finset.card_union_of_disjoint]
      exact Finset.disjoint_left.mpr fun r h1 h2 =>
        hdisjR r (List.mem_toFinset.mp h1) (List.mem_toFinset.mp h2)
    rw [List.toFinset_card_of_nodup hndR, List.length_map, List.toFinset_card_of_nodup hndS] at hcard_u
    have hsdiff_le : ((S' j).RF.R \ (S j).RF.R).card ≤ (S' j).RF.R.card :=
      Finset.card_le_card Finset.sdiff_subset
    have := hR'_le j; omega
  have hsp_bd : ∀ j : Fin k, (splits j).length ≤ x.vCap := fun j =>
    le_trans (by simpa [splits] using (hspL_br j).2.1) (hR'_le j)
  have hZ_hdr_ag : ∀ a, b ≤ a → a < b + compHdrSize → stZ.mem a = stL.mem a := fun a ha1 ha2 => by
    have hlt_tm : a < tmBase := by
      dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase,
        compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
        compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at ha2 ⊢; omega
    exact (hZ_fr a (Or.inl (by omega))).trans (hU_fr a fun c _ => by omega)
  have hZ_ge_cnt : ∀ a, cntBase ≤ a → stZ.mem a = stL.mem a := fun a ha =>
    (hZ_fr a (Or.inr (by omega))).trans (hU_ge_h a (by omega))
  have hZ_zero_ptr : ∀ a, ptrBase ≤ a → a < cntBase → stZ.mem a = 0 := fun a ha1 ha2 => by
    by_cases hgap : a < heap + 1 + 2 * numU
    · have h := hZ_zero (a - ptrBase) (by omega)
      rwa [show ptrBase + (a - ptrBase) = a by omega] at h
    · rw [hZ_fr a (Or.inr (by omega)), hU_ge_h a (by omega)]
      rw [hfrL a (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
        (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega))
        (fun _ => Or.inl (by omega)) (fun _ => by omega) (Or.inl (by omega)) (by omega)]
      exact hz a (by omega)
  have hZ_zero_roots : ∀ j : Fin k, ∀ i, (cuts j).length ≤ i → i < x.vCap →
      stZ.mem (cntBase + k + j.1 * x.vCap + i) = 0 ∧
      stZ.mem (cntBase + k + k * x.vCap + j.1 * x.vCap + i) = 0 := fun j i hi1 hi2 => by
    have hj_mul : j.1 * x.vCap + x.vCap ≤ k * x.vCap := by
      have := Nat.mul_le_mul_right x.vCap (show j.1 + 1 ≤ k by have := j.2; omega)
      rw [Nat.add_mul, Nat.one_mul] at this; exact this
    have hsep : ∀ (j0 : Fin k) (base : ℕ), base = cntBase + k ∨ base = cntBase + k + k * x.vCap →
        base + j.1 * x.vCap + i < base + j0.1 * x.vCap ∨
        base + j0.1 * x.vCap + (cuts j0).length ≤ base + j.1 * x.vCap + i := fun j0 base _ => by
      by_cases hjj : j0 = j
      · subst hjj; right; omega
      · have hne : j0.1 ≠ j.1 := fun h => hjj (Fin.ext h)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · right; have h := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ j.1 by omega)
          rw [Nat.add_mul, Nat.one_mul] at h; have := hcut_bd j0; omega
        · left; have h := Nat.mul_le_mul_right x.vCap (show j.1 + 1 ≤ j0.1 by omega)
          rw [Nat.add_mul, Nat.one_mul] at h; omega
    constructor
    · rw [hZ_ge_cnt _ (by omega), hfrL _ (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
        (fun j0 => by have := j0.2; omega) (fun j0 => by simpa using hsep j0 (cntBase + k) (Or.inl rfl))
        (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (fun _ => by omega) (Or.inl (by omega)) (by omega)]
      exact hz _ (by omega)
    · rw [hZ_ge_cnt _ (by omega), hfrL _ (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
        (fun j0 => by have := j0.2; omega)
        (fun j0 => Or.inr (by
          have h := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ k by have := j0.2; omega)
          rw [Nat.add_mul, Nat.one_mul] at h; have := hcut_bd j0; omega))
        (fun j0 => by simpa using hsep j0 (cntBase + k + k * x.vCap) (Or.inr rfl))
        (fun _ => Or.inl (by omega)) (fun _ => by omega) (Or.inl (by omega)) (by omega)]
      exact hz _ (by omega)
  obtain ⟨stP1, cPk1, hrPk1, hPk1_br, hmid_le_cnt, hzPk1, hPk1_ab, hPk1_bl, hcPk1⟩ :=
    compPackChanges_runs_gen (b := b) (heap := heap + k) (numTouched := touched'.length)
      (cntBase := cntBase) (splitBase := splitBase) (vCap := x.vCap)
      (cuts := cuts) (splitVerts := sp) (mem := stZ.mem) (pos := stZ.pos) (ω := ω)
      hpZero hw16 hk
      ((hZ_hdr_ag _ (by dsimp only [compOffK]; omega) (by dsimp only [compOffK, compHdrSize]; omega)).trans hrepL.2.2.2.2.2.2.2.2.2.2.1.2.2.1)
      ((hZ_hdr_ag _ (by dsimp only [compOffVCap]; omega) (by dsimp only [compOffVCap, compHdrSize]; omega)).trans (hxL1 ▸ hrepL.2.2.2.2.2.2.2.2.2.2.1.1))
      (by omega)
      (by
        have hmul_c : k + k + k * (2 + 2 * x.vCap) = k * (4 + 2 * x.vCap) := by ring
        have hle_c : k * (4 + 2 * x.vCap) ≤ k * (5 + 6 * x.vCap) := Nat.mul_le_mul_left k (by omega)
        dsimp only [cntBase]; omega)
      (le_refl _) (by omega) hcut_bd
      (fun j => (hZ_ge_cnt _ (by omega)).trans (by simpa using (hbrL j).1))
      (fun j i hi => by
        rw [hZ_ge_cnt _ (by omega), hZ_ge_cnt _ (by omega)]; simpa using (hbrL j).2.1 i hi)
      (fun i hi => (hZ_ge_cnt _ (by omega)).trans (by simpa using hspL_m i hi))
      (fun a ha1 ha2 => hZ_zero_ptr a (by dsimp only [ptrBase]; omega) ha2)
      hZ_zero_roots (fun a h1 h2 => by omega)
  set midEnd := heap + k + 1 + touched'.length + k + compPackedPrefixWords cuts sp k
  have hmid_eq : midEnd = ptrBase + 2 * k + compPackedPrefixWords cuts sp k := by
    dsimp only [midEnd, ptrBase]; omega
  let stPk1 : State := { stZ with regs := Function.update stZ.regs 15 midEnd, mem := stP1.mem, pos := stP1.pos }
  have hr0_Z : stZ.regs 0 = b := (hrZ_lt14 0 (by omega)).trans (by simp [stU1, stU0, hrL_eq 0 (by omega), stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState])
  have hr2_Z : stZ.regs 2 = heap := (hrZ_lt14 2 (by omega)).trans (by simp [stU1, stU0, hrL_eq 2 (by omega), stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState])
  have hr3_Z : stZ.regs 3 = k := (hrZ_lt14 3 (by omega)).trans (by simp [stU1, stU0, hrL_eq 3 (by omega), stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1])
  have hr4_Z : stZ.regs 4 = x.vCap := (hrZ_lt14 4 (by omega)).trans (by simp [stU1, stU0, hrL_eq 4 (by omega), stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2])
  have hr6_Z : stZ.regs 6 = numU := (hrZ_lt14 6 (by omega)).trans (by simp [stU1, stU0, hrL_eq 6 (by omega), stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4])
  have hr7_Z : stZ.regs 7 = cntBase := (hrZ_lt14 7 (by omega)).trans (by simp [stU1, stU0, hrL_eq 7 (by omega), stP, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5])
  have hr8_Z : stZ.regs 8 = splitBase := (hrZ_lt14 8 (by omega)).trans (by simp [stU1, stU0, hrL_eq 8 (by omega), stP, r14, r13, r12, r11, r10, r9, r8, r7, r6])
  have hr12_Z : stZ.regs 12 = sp.length := (hrZ_lt14 12 (by omega)).trans (by simpa [stU1, stU0] using hrL_12)
  have hr13_Z : stZ.regs 13 = touched'.length := (hrZ_lt14 13 (by omega)).trans (by simp [stU1, stU0])
  have hrunPk1 : Runs w p ω (.call 15 bPackChg [.reg 0, .bin .add (.reg 2) (.reg 3), .reg 13, .reg 7, .reg 8, .reg 12])
      stZ .normal stPk1 (cPk1 + 9) := by
    rw [runs_call_iff]
    refine ⟨[b, heap + k, touched'.length, cntBase, splitBase, sp.length], compPackChangesProc bZero,
      .returned midEnd, stP1, cPk1, ?_, hpPackChg, hrPk1, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    simp [evalArgs, Expr.eval, BinOp.eval, hr0_Z, hr2_Z, hr3_Z, hr7_Z, hr8_Z, hr12_Z, hr13_Z,
      show heap + k < 2 ^ w by omega]
  -- Step 5: Compute `[ptrBase, spBufBase, spCntBase, oldCntBase]` and pack splits via `compPackSplitsProc`
  let q1 : State := { stPk1 with regs := Function.update stPk1.regs 16 ptrBase }
  let q2 : State := { q1 with regs := Function.update q1.regs 17 spBufBase }
  let q3 : State := { q2 with regs := Function.update q2.regs 18 spCntBase }
  let q4 : State := { q3 with regs := Function.update q3.regs 19 oldCntBase }
  have hq1 : Runs w p ω (.assign 16 (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 13))) stPk1 .normal q1 6 :=
    runs_assign_iff.mpr ⟨ptrBase, by
      simp [stPk1, Expr.eval, BinOp.eval, hr2_Z, hr13_Z, hw1, show heap + 1 < 2 ^ w by omega,
        show ptrBase < 2 ^ w by omega, ptrBase], rfl, rfl, by simp [Expr.size]⟩
  have hq2 : Runs w p ω (.assign 17 (.bin .add (.reg 8) (.reg 6))) q1 .normal q2 4 :=
    runs_assign_iff.mpr ⟨spBufBase, by
      simp [q1, stPk1, Expr.eval, BinOp.eval, hr8_Z, hr6_Z, show spBufBase < 2 ^ w by omega, spBufBase],
      rfl, rfl, by simp [Expr.size]⟩
  have hq3 : Runs w p ω (.assign 18 (.bin .add (.reg 17) (.bin .mul (.const 4) (.bin .mul (.reg 3) (.reg 4))))) q2 .normal q3 8 :=
    runs_assign_iff.mpr ⟨spCntBase, by
      simp [q2, q1, stPk1, Expr.eval, BinOp.eval, hr3_Z, hr4_Z, hw4, show k * x.vCap < 2 ^ w by omega,
        hkv_lt, show spCntBase < 2 ^ w by omega, spCntBase], rfl, rfl, by simp [Expr.size]⟩
  have hq4 : Runs w p ω (.assign 19 (.bin .add (.reg 18) (.reg 3))) q3 .normal q4 4 :=
    runs_assign_iff.mpr ⟨oldCntBase, by
      simp [q3, q2, q1, stPk1, Expr.eval, BinOp.eval, hr3_Z, show oldCntBase < 2 ^ w by omega, oldCntBase],
      rfl, rfl, by simp [Expr.size]⟩
  have hPk1_ge_spB : ∀ a, spBufBase ≤ a → stP1.mem a = stL.mem a := fun a ha =>
    (hPk1_ab a (by omega)).trans (hZ_ge_cnt a (by omega))
  have hmid_le_buf : midEnd + k * (1 + 4 * x.vCap) ≤ spBufBase := by
    have h1 : compPackedPrefixWords cuts sp k ≤ k * (2 + 2 * x.vCap) := by
      unfold compPackedPrefixWords
      calc (Finset.range k).sum (fun i => if hi : i < k then (compBranchChange (cuts ⟨i, hi⟩) sp).words else 0)
          ≤ (Finset.range k).sum (fun _ => 2 + 2 * x.vCap) := Finset.sum_le_sum fun i hi => by
            have hilt := Finset.mem_range.mp hi
            simp only [hilt, ↓reduceDIte, Read.LSFChange.words, Read.LSFChange.size, compBranchChange,
              List.length_append, List.length_map]
            have := hcut_bd ⟨i, hilt⟩; omega
        _ = k * (2 + 2 * x.vCap) := by simp
    have hmul : 2 * k + k * (2 + 2 * x.vCap) + k * (1 + 4 * x.vCap) = k * (5 + 6 * x.vCap) := by ring
    dsimp only [spBufBase, splitBase, cntBase, ptrBase] at hmid_eq ⊢; omega
  have hPk1_zero_mid : ∀ a, midEnd ≤ a → a < spBufBase → stP1.mem a = 0 := fun a ha1 ha2 => by
    by_cases hlt : a < splitBase + sp.length
    · exact hzPk1 a ha1 hlt
    · rw [hPk1_ab a (by omega), hZ_ge_cnt a (by omega)]
      rw [hfrL a (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
        (fun j0 => by have := j0.2; omega)
        (fun j0 => Or.inr (by
          have h := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ k by have := j0.2; omega)
          rw [Nat.add_mul, Nat.one_mul] at h; have := hcut_bd j0; omega))
        (fun j0 => Or.inr (by
          have h := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ k by have := j0.2; omega)
          rw [Nat.add_mul, Nat.one_mul] at h; have := hcut_bd j0; omega))
        (fun _ => Or.inl (by omega)) (fun _ => by omega) (Or.inl (by omega)) (by omega)]
      exact hz a (by omega)
  have hPk1_buf_tail : ∀ j : Fin k, ∀ t, 4 * (splits j).length ≤ t → t < 4 * x.vCap →
      stP1.mem (spBufBase + 4 * (j.1 * x.vCap) + t) = 0 := fun j t ht1 ht2 => by
    have hjv : j.1 * x.vCap + x.vCap ≤ k * x.vCap := by
      have := Nat.mul_le_mul_right x.vCap (show j.1 + 1 ≤ k by have := j.2; omega)
      rw [Nat.add_mul, Nat.one_mul] at this; exact this
    rw [hPk1_ge_spB _ (by omega)]
    rw [hfrL _ (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      (fun j0 => by have := j0.2; omega)
      (fun j0 => Or.inr (by
        have h := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ k by have := j0.2; omega)
        rw [Nat.add_mul, Nat.one_mul] at h; have := hcut_bd j0; omega))
      (fun j0 => Or.inr (by
        have h := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ k by have := j0.2; omega)
        rw [Nat.add_mul, Nat.one_mul] at h; have := hcut_bd j0; omega))
      (fun j0 => by
        by_cases hjj : j0 = j
        · subst hjj; right; dsimp only [splits] at ht1; omega
        · have hne : j0.1 ≠ j.1 := fun h => hjj (Fin.ext h)
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · right; have h := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ j.1 by omega)
            rw [Nat.add_mul, Nat.one_mul] at h; have := hsp_bd j0; dsimp only [splits] at this; omega
          · left; have h := Nat.mul_le_mul_right x.vCap (show j.1 + 1 ≤ j0.1 by omega)
            rw [Nat.add_mul, Nat.one_mul] at h; omega)
      (fun _ => by omega) (Or.inl (by omega)) (by omega)]
    exact hz _ (by omega)
  obtain ⟨stP2, cPk2, hrPk2, hPk2_shift, hPk2_mid, hPk2_sp, hout_le_buf, hzPk2, hPk2_bl, hcPk2⟩ :=
    compPackSplits_runs (b := b) (ptrBase := ptrBase) (midEnd := midEnd)
      (spCntBase := spCntBase) (spBufBase := spBufBase) (oldCntBase := oldCntBase) (vCap := x.vCap)
      (splits := splits) (mem := stP1.mem) (pos := q4.pos) (ω := ω)
      hpZero hw16 hk
      ((hPk1_bl _ (by dsimp only [compOffK, compHdrSize] at hb_hdr_lt ⊢; omega)).trans ((hZ_hdr_ag _ (by dsimp only [compOffK]; omega) (by dsimp only [compOffK, compHdrSize]; omega)).trans hrepL.2.2.2.2.2.2.2.2.2.2.1.2.2.1))
      ((hPk1_bl _ (by dsimp only [compOffVCap, compHdrSize] at hb_hdr_lt ⊢; omega)).trans ((hZ_hdr_ag _ (by dsimp only [compOffVCap]; omega) (by dsimp only [compOffVCap, compHdrSize]; omega)).trans (hxL1 ▸ hrepL.2.2.2.2.2.2.2.2.2.2.1.1)))
      (by omega) (by omega) hmid_le_buf (le_refl _) (le_refl _) (by omega) hsp_bd
      (fun j => (hPk1_ge_spB _ (by omega)).trans (by simpa [splits] using (hspL_br j).1))
      (fun j i hi => by
        have h := (hspL_br j).2.2 i hi
        simp only [Nat.zero_add] at h
        have hjv : j.1 * x.vCap + x.vCap ≤ k * x.vCap := by
          have := Nat.mul_le_mul_right x.vCap (show j.1 + 1 ≤ k by have := j.2; omega)
          rw [Nat.add_mul, Nat.one_mul] at this; exact this
        exact ⟨(hPk1_ge_spB _ (by omega)).trans h.1, (hPk1_ge_spB _ (by omega)).trans h.2.1,
          (hPk1_ge_spB _ (by omega)).trans h.2.2.1, (hPk1_ge_spB _ (by omega)).trans h.2.2.2⟩)
      hPk1_zero_mid (fun a h1 h2 => by omega) hPk1_buf_tail (fun a h1 h2 => by omega)
      (fun a ha => (hPk1_ge_spB a (by omega)).trans (hzL a ha))
  set outEnd := midEnd + compSplitPrefixWords splits k
  let stPk2 : State := { q4 with regs := Function.update q4.regs 15 outEnd, mem := stP2.mem, pos := stP2.pos }
  have hrunPk2 : Runs w p ω (.call 15 bPackSp [.reg 0, .reg 16, .reg 15, .reg 18, .reg 17, .reg 19])
      q4 .normal stPk2 (cPk2 + 7) := by
    rw [runs_call_iff]
    refine ⟨[b, ptrBase, midEnd, spCntBase, spBufBase, oldCntBase], compPackSplitsProc bZero,
      .returned outEnd, stP2, cPk2, ?_, hpPackSp, hrPk2, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    simp [evalArgs, Expr.eval, q4, q3, q2, q1, stPk1, hr0_Z]
  have hrunRet : Runs w p ω (.ret (.reg 15)) stPk2 (.returned outEnd) stPk2 2 :=
    runs_ret_iff.mpr ⟨outEnd, by simp [stPk2, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  -- Chain full execution
  have hrun_full : Runs w p ω
      (compBatchWithSplitsProc bZero bIns bDel bSplit bEnds bEmit bPackChg bPackSp) st0
      (.returned outEnd) stPk2 (167 + cL + cU + cZ + cPk1 + cPk2) := by
    unfold compBatchWithSplitsProc
    have t24 := runs_seq_iff.mpr (Or.inr ⟨stPk2, cPk2 + 7, 2, hrunPk2, hrunRet, rfl⟩)
    have t23 := runs_seq_iff.mpr (Or.inr ⟨q4, 4, _, hq4, t24, rfl⟩)
    have t22 := runs_seq_iff.mpr (Or.inr ⟨q3, 8, _, hq3, t23, rfl⟩)
    have t21 := runs_seq_iff.mpr (Or.inr ⟨q2, 4, _, hq2, t22, rfl⟩)
    have t20 := runs_seq_iff.mpr (Or.inr ⟨q1, 6, _, hq1, t21, rfl⟩)
    have t19 := runs_seq_iff.mpr (Or.inr ⟨stPk1, cPk1 + 9, _, hrunPk1, t20, rfl⟩)
    have t18 := runs_seq_iff.mpr (Or.inr ⟨stZ, cZ + 11, _, hrunZ, t19, rfl⟩)
    have t17 := runs_seq_iff.mpr (Or.inr ⟨stU, cU, _, hrunU, t18, rfl⟩)
    have t16 := runs_seq_iff.mpr (Or.inr ⟨stU1, 2, _, hu1, t17, rfl⟩)
    have t15 := runs_seq_iff.mpr (Or.inr ⟨stU0, 3, _, hu0, t16, rfl⟩)
    have t14 := runs_seq_iff.mpr (Or.inr ⟨stL, cL, _, hrunL, t15, rfl⟩)
    have t13 := runs_seq_iff.mpr (Or.inr ⟨stP, 2, _, hp15, t14, rfl⟩)
    have t12 := runs_seq_iff.mpr (Or.inr ⟨_, 4, _, hp14, t13, rfl⟩)
    have t11 := runs_seq_iff.mpr (Or.inr ⟨_, 2, _, hp13, t12, rfl⟩)
    have t10 := runs_seq_iff.mpr (Or.inr ⟨_, 3, _, hp12, t11, rfl⟩)
    have t9 := runs_seq_iff.mpr (Or.inr ⟨_, 10, _, hp11, t10, rfl⟩)
    have t8 := runs_seq_iff.mpr (Or.inr ⟨_, 4, _, hp10, t9, rfl⟩)
    have t7 := runs_seq_iff.mpr (Or.inr ⟨_, 4, _, hp9, t8, rfl⟩)
    have t6 := runs_seq_iff.mpr (Or.inr ⟨_, 8, _, hp8, t7, rfl⟩)
    have t5 := runs_seq_iff.mpr (Or.inr ⟨_, 4, _, hp7, t6, rfl⟩)
    have t4 := runs_seq_iff.mpr (Or.inr ⟨_, 10, _, hp6, t5, rfl⟩)
    have t3 := runs_seq_iff.mpr (Or.inr ⟨_, 16, _, hp5, t4, rfl⟩)
    have t2 := runs_seq_iff.mpr (Or.inr ⟨_, 3, _, hp4, t3, rfl⟩)
    have t1 := runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hp3, t2, rfl⟩)
    have t0 := runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hp2, t1, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hp1, t0, by omega⟩)
  -- Restore `CompLSFRepAt` and `compPhiFull`
  have hPk2_lt_end : ∀ a < x.endAddr, stPk2.mem a = stU.mem a := fun a ha =>
    (hPk2_bl a (by omega)).trans ((hPk1_bl a (by omega)).trans (hZ_fr a (Or.inl (by omega))))
  have htm_eq_L : compTouchMarkBase b xL.vCap xL.eCap = tmBase := by rw [hxL1, hxL2]
  obtain ⟨hrep_final, hphi_eq⟩ := compLSFRepAt_of_unmarked hrepL
    (fun c hc => by rw [htm_eq_L, hPk2_lt_end _ (by have := lt_of_lt_of_le (hltL c hc) hnumC; omega)]; exact hU_zero c hc)
    (fun a ha hnt => (hPk2_lt_end a (hxL7 ▸ ha)).trans (hU_fr a fun c hc => by
      have := lt_of_lt_of_le (hltL c hc) hnumC; rw [htm_eq_L, hxL1] at hnt; omega))
    (fun c hc hnc => by
      rw [htm_eq_L, hPk2_lt_end _ (by rw [hxL1] at hc; omega)]
      exact hU_fr _ fun c' hc' heq => hnc ((Nat.add_left_cancel heq) ▸ hc'))
  -- Cost bound
  have hcost_final : (167 + cL + cU + cZ + cPk1 + cPk2) + compPhiFull k b xL stPk2.mem ≤
      (compLSFDSFullWithSplits W w k G₀).cost 0 S [b, batchPtr, heap] mem + compPhiFull k b x mem := by
    have hsubE : ∀ C ∈ components (S ⟨0, hk⟩).G₀, ((S ⟨0, hk⟩).compSt C).G.E ⊆ (S ⟨0, hk⟩).G.E := fun C hC =>
      (hBr ⟨0, hk⟩).1.hCE_sub C hC
    have hcost_ds : (compLSFDSFullWithSplits W w k G₀).cost 0 S [b, batchPtr, heap] mem =
        compBatchLsfMul * k * sumTouchedLsfBatchCost mem (S ⟨0, hk⟩) batchPtr x.L_w U +
        compBatchUpdMulFull * k * (U.length + 1) := by
      have h0 := compLSFDS_batchCost_eq (w := w) (b := b) (G₀ := G₀) (heap := heap) W hk hsubE hBAt
      simp only [compLSFDSFullWithSplits, ↓reduceIte, compLSFDSFull, show (0 : ℕ) ≠ 6 by decide,
        List.getD_cons_zero, List.getD_cons_succ, h0, hmem_Lw, hnumU_m, numU]
      dsimp only [compBatchUpdMulFull, compBatchUpdMul]; ring
    rw [hcost_ds, hphi_eq]
    have hsteps_le : compBatchStepsCost mem x.L_w (S ⟨0, hk⟩) (batchPtr + 1) U ≤
        3 * sumTouchedLsfBatchCost mem (S ⟨0, hk⟩) batchPtr x.L_w U :=
      compBatchStepsCost_le_three_mul hLw (hBr ⟨0, hk⟩).1 hBVal hBAt
    have hmul_steps : k * compBatchStepsCost mem x.L_w (S ⟨0, hk⟩) (batchPtr + 1) U ≤
        compBatchLsfMul * k * sumTouchedLsfBatchCost mem (S ⟨0, hk⟩) batchPtr x.L_w U := by
      calc k * compBatchStepsCost mem x.L_w (S ⟨0, hk⟩) (batchPtr + 1) U
          ≤ k * (3 * sumTouchedLsfBatchCost mem (S ⟨0, hk⟩) batchPtr x.L_w U) := Nat.mul_le_mul_left k hsteps_le
        _ = 3 * k * sumTouchedLsfBatchCost mem (S ⟨0, hk⟩) batchPtr x.L_w U := by ring
        _ ≤ compBatchLsfMul * k * sumTouchedLsfBatchCost mem (S ⟨0, hk⟩) batchPtr x.L_w U :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right k (by decide))
    have hgap_cancel : cU + cZ ≤ 52 * numU + 25 := by dsimp only [gapLen] at hcZ; omega
    have hnon_lsf : 167 + 2650 * k * numU + 10 + (52 * numU + 25) + 45 * k * sp.length + 260 * k +
        20 * sp.length + 90 + 150 * k + 80 ≤ compBatchUpdMulFull * k * (numU + 1) := by
      have h1 : 45 * k * sp.length ≤ 45 * k * numU := Nat.mul_le_mul_left _ hspL_le
      have h2 : 72 * numU ≤ 72 * (k * numU) := by
        calc 72 * numU = 1 * (72 * numU) := by ring
          _ ≤ k * (72 * numU) := Nat.mul_le_mul_right _ hk
          _ = 72 * (k * numU) := by ring
      have h3 : 375 ≤ 375 * k := Nat.le_mul_of_pos_right 375 hk
      have h4 : compBatchUpdMulFull * k * (numU + 1) = 3000 * (k * numU) + 3000 * k := by
        dsimp only [compBatchUpdMulFull]; ring
      have h5 : 2650 * k * numU = 2650 * (k * numU) := by ring
      have h6 : 45 * k * numU = 45 * (k * numU) := by ring
      omega
    dsimp only [numU] at hgap_cancel hnon_lsf
    have hsum_le : 100 * ∑ j, (cuts j).length ≤ 120 * ∑ j, (cuts j).length :=
      Nat.mul_le_mul_right _ (by decide)
    have hphi_stP : compPhiFull k b x stP.mem = compPhiFull k b x mem := rfl
    dsimp only [splits] at hcPk2
    omega
  -- Word bound `∀ a, ptrBase + k ≤ a → a < outEnd → stPk2.mem a < 2 ^ w`
  have hwords_lt : ∀ a, ptrBase + k ≤ a → a < outEnd → stPk2.mem a < 2 ^ w := fun a ha1 ha2 => by
    by_cases h1 : a < ptrBase + 2 * k
    · let jf : Fin k := ⟨a - (ptrBase + k), by omega⟩
      have hptr := (hPk2_sp jf).1
      rw [show ptrBase + k + jf.1 = a by dsimp [jf]; omega] at hptr
      have hle_out : midEnd + compSplitPrefixWords splits jf.1 ≤ outEnd := by
        dsimp only [outEnd]
        exact Nat.add_le_add_left (Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))) midEnd
      rw [hptr]; omega
    · by_cases h2 : a < midEnd
      · obtain ⟨jf, hlo, hhi⟩ := prefix_locate (k := k) (base := ptrBase + 2 * k) (a := a)
          (fun j => (compBranchChange (cuts j) sp).words) (by omega)
          (by dsimp only [compPackedPrefixWords] at hmid_eq; rw [← hmid_eq]; exact h2)
        obtain ⟨hptr_eq, hAt, _, _⟩ := hPk1_br jf
        have hpk_idx : heap + k + 1 + touched'.length = ptrBase + k := by dsimp only [ptrBase]; omega
        have hptr_eq' : stP1.mem (ptrBase + k + jf.1) = ptrBase + 2 * k + compPackedPrefixWords cuts sp jf.1 := by
          simpa [hpk_idx, show ptrBase + k + k = ptrBase + 2 * k by omega] using hptr_eq
        rw [hpk_idx, hptr_eq'] at hAt
        rw [hPk2_mid a (by omega) h2]
        set pJ := ptrBase + 2 * k + compPackedPrefixWords cuts sp jf.1
        set chg := compBranchChange (cuts jf) sp
        have hpJ_lo : pJ ≤ a := hlo
        have hpJ_hi : a < pJ + chg.words := hhi
        have hw_chg : chg.words = 2 + chg.roots.length + chg.fDel.length := by
          simp [Read.LSFChange.words, Read.LSFChange.size]; omega
        have hr_le : chg.roots.length ≤ x.vCap := by simp [chg, compBranchChange]; exact hcut_bd jf
        have hf_le : chg.fDel.length ≤ x.vCap := by simp [chg, compBranchChange]; have := hcut_bd jf; omega
        obtain ⟨hAt1, hAt2, hAt3, hAt4⟩ := hAt
        by_cases c0 : a = pJ
        · rw [c0, hAt1]; omega
        · by_cases c1 : a < pJ + 1 + chg.roots.length
          · have hr_m := hAt2 (a - (pJ + 1)) (by omega)
            rw [show pJ + 1 + (a - (pJ + 1)) = a by omega] at hr_m; rw [hr_m]
            have hrm : chg.roots[a - (pJ + 1)]'(by omega) ∈ (S' jf).RF.R := by
              have hmem := List.getElem_mem (l := chg.roots) (n := a - (pJ + 1)) (by omega)
              simp only [chg, compBranchChange, List.mem_append] at hmem
              have hsR := (hbrL jf).2.2.2.2.2.2.2.2.2.1
              have hmem_u : chg.roots[a - (pJ + 1)]'(by omega) ∈ ((cuts jf).map Prod.snd).toFinset ∪ sp.toFinset := by
                rcases hmem with h | h
                · exact Finset.mem_union_left _ (List.mem_toFinset.mpr h)
                · exact Finset.mem_union_right _ (List.mem_toFinset.mpr h)
              rw [hsR] at hmem_u; exact (Finset.mem_sdiff.mp hmem_u).1
            obtain ⟨ℓ₀', hBr'⟩ := hrepL.2.2.2.2.2.2.2.2.2.2.2.1
            have hT' := compEdgeTrack_of_same_graph hrepL.2.2.2.2.2.2.2.2.2.2.2.2.2.1
              (hBr' jf).2.1 (hBr' jf).2.2.1 (hBr' jf).2.2.2.2.1 (hBr' jf).2.2.2.2.2.2
            have hv_lt := hT'.hVlt _ ((compLSF_RF_isRSF (hBr' jf).1).2.2.1 hrm)
            rw [hxL1] at hv_lt; omega
          · by_cases c2 : a = pJ + 1 + chg.roots.length
            · rw [c2, hAt3]; omega
            · have hf_m := hAt4 (a - (pJ + 2 + chg.roots.length)) (by omega)
              rw [show pJ + 2 + chg.roots.length + (a - (pJ + 2 + chg.roots.length)) = a by omega] at hf_m
              rw [hf_m]
              have hfm : chg.fDel[a - (pJ + 2 + chg.roots.length)]'(by omega) ∈ (S jf).G.E := by
                have hmem := List.getElem_mem (l := chg.fDel) (n := a - (pJ + 2 + chg.roots.length)) (by omega)
                simp only [chg, compBranchChange] at hmem
                have hsE := (hbrL jf).2.2.2.2.1
                have h1 : chg.fDel[a - (pJ + 2 + chg.roots.length)]'(by omega) ∈ (S jf).RF.F.E \ (S' jf).RF.F.E := by
                  rw [← hsE]; exact List.mem_toFinset.mpr hmem
                exact (compLSF_RF_isRSF (hBr jf).1).2.2.2.2.2.1 (Finset.mem_sdiff.mp h1).1
              have hT0j := compEdgeTrack_of_same_graph hT (hBr jf).2.1 (hBr jf).2.2.1
                (hBr jf).2.2.2.2.1 (hBr jf).2.2.2.2.2.2
              have he_lt := hT0j.hElt _ hfm; omega
      · obtain ⟨jf, hlo, hhi⟩ := prefix_locate (k := k) (base := midEnd) (a := a)
          (fun j => splitEntriesWords (splits j)) (by omega) ha2
        obtain ⟨hptr_eq, ⟨hsp_len, hsp_ent⟩, _, _⟩ := hPk2_sp jf
        rw [hptr_eq] at hsp_len hsp_ent
        set pJ := midEnd + compSplitPrefixWords splits jf.1
        have hpJ_lo : pJ ≤ a := hlo
        have hpJ_hi : a < pJ + (1 + 4 * (splits jf).length) := hhi
        have hlen_le : (splits jf).length ≤ x.vCap := hsp_bd jf
        by_cases c0 : a = pJ
        · rw [c0, hsp_len]; omega
        · have hidx_lt : (a - (pJ + 1)) / 4 < (splits jf).length := by omega
          have hdm : 4 * ((a - (pJ + 1)) / 4) + (a - (pJ + 1)) % 4 = a - (pJ + 1) :=
            Nat.div_add_mod (a - (pJ + 1)) 4
          have hmod_lt : (a - (pJ + 1)) % 4 < 4 := Nat.mod_lt _ (by decide)
          have hent := hsp_ent ((a - (pJ + 1)) / 4) hidx_lt
          have hT0j := compEdgeTrack_of_same_graph hT (hBr jf).2.1 (hBr jf).2.2.1
            (hBr jf).2.2.2.2.1 (hBr jf).2.2.2.2.2.2
          have hvPos : 0 < x.vCap := by omega
          have hmem_s := List.getElem_mem (l := splits jf) (n := (a - (pJ + 1)) / 4) hidx_lt
          have hbd_s := canonSplitList_entries_lt hvPos (by omega : 0 < x.eCap) U (S jf)
            (hBr jf).1 ((hBr jf).2.2.1.symm ▸ hBVal) hBCaps hT0j.hVlt hT0j.hElt _ hmem_s
          have hcase : (a - (pJ + 1)) % 4 = 0 ∨ (a - (pJ + 1)) % 4 = 1 ∨
              (a - (pJ + 1)) % 4 = 2 ∨ (a - (pJ + 1)) % 4 = 3 := by omega
          rcases hcase with hr0 | hr1 | hr2 | hr3
          · have ha_eq : pJ + 1 + 4 * ((a - (pJ + 1)) / 4) = a := by omega
            rw [← ha_eq, hent.1]; split_ifs <;> omega
          · have ha_eq : pJ + 1 + 4 * ((a - (pJ + 1)) / 4) + 1 = a := by omega
            rw [← ha_eq, hent.2.1]; omega
          · have ha_eq : pJ + 1 + 4 * ((a - (pJ + 1)) / 4) + 2 = a := by omega
            rw [← ha_eq, hent.2.2.1]; omega
          · have ha_eq : pJ + 1 + 4 * ((a - (pJ + 1)) / 4) + 3 = a := by omega
            rw [← ha_eq, hent.2.2.2]; omega
  -- Assemble `CompBatchPostFull` and `Respects`
  have hheap_val : stPk2.mem heap = touched'.length :=
    (hPk2_bl heap (by omega)).trans ((hPk1_bl heap (by omega)).trans ((hZ_fr heap (Or.inl (by omega))).trans ((hU_ge_h heap (le_refl _)).trans hhpL)))
  have hbuf_le_sp : spBufBase ≤ heap + compBatchSpaceFull k [b, batchPtr, heap] mem := by
    simp only [compBatchSpaceFull, List.getD_cons_zero, List.getD_cons_succ, hmem_vCap, hmem_eCap, htw_eq, hnumU_m]
    have hmul : k * (5 + 6 * x.vCap) + k + 2 * (k * x.vCap) ≤ k * (8 + 12 * x.vCap) := by
      have : k * (5 + 6 * x.vCap) + k + 2 * (k * x.vCap) = k * (6 + 8 * x.vCap) := by ring
      rw [this]; exact Nat.mul_le_mul_left k (by omega)
    dsimp only [spBufBase, splitBase, cntBase, numU]; omega
  have hpost_at : CompBatchPostFullAt w k S [b, batchPtr, heap] mem outEnd U S' stPk2.mem := by
    refine ⟨hk, b, batchPtr, heap, totalWords, rfl, hBAt, rfl, hheap_val ▸ hlenL,
      by rw [hheap_val]; dsimp only [outEnd, ptrBase] at hmid_eq ⊢; omega,
      le_trans hout_le_buf hbuf_le_sp, hzPk2,
      ⟨fun j => compBranchChange (cuts j) sp, fun j => ?_⟩, ?_⟩
    · obtain ⟨hptr_eq, hAt, hge_p, hle_m⟩ := hPk1_br j
      obtain ⟨_, _, hval_j, hndE_j, hsE_j, hEsub_j, hndR_j, hndS_j, hdisj_j, hsR_j, _⟩ := hbrL j
      have hchg := compForestCuts_to_lsfChange hval_j hndE_j hsE_j hEsub_j hndR_j hndS_j hdisj_j hsR_j
      have hpk_idx : heap + k + 1 + touched'.length = ptrBase + k := by dsimp only [ptrBase]; omega
      rw [hpk_idx] at hptr_eq hAt hge_p hle_m
      have hptr_sh : stPk2.mem (ptrBase + j.1) = stP1.mem (ptrBase + k + j.1) := hPk2_shift j
      have hptr_eq' : stP1.mem (ptrBase + k + j.1) = ptrBase + 2 * k + compPackedPrefixWords cuts sp j.1 := by
        simpa [show ptrBase + k + k = ptrBase + 2 * k by omega] using hptr_eq
      have hAt2 : Read.LSFChangeAt stPk2.mem (stPk2.mem (ptrBase + j.1)) (compBranchChange (cuts j) sp) := by
        rw [hptr_sh]
        set pJ := stP1.mem (ptrBase + k + j.1)
        have hlo_pJ : ptrBase + 2 * k ≤ pJ := by rw [hptr_eq']; omega
        have hw_j : (compBranchChange (cuts j) sp).words =
            2 + (compBranchChange (cuts j) sp).roots.length + (compBranchChange (cuts j) sp).fDel.length := by
          simp [Read.LSFChange.words, Read.LSFChange.size]; omega
        refine ⟨(hPk2_mid pJ hlo_pJ (by omega)).trans hAt.1,
          fun i hi => (hPk2_mid _ (by omega) (by omega)).trans (hAt.2.1 i hi),
          (hPk2_mid _ (by omega) (by omega)).trans hAt.2.2.1,
          fun i hi => (hPk2_mid _ (by omega) (by omega)).trans (hAt.2.2.2 i hi)⟩
      rw [hheap_val, hmem_vCap]
      refine ⟨hAt2, hchg.1, hchg.2.1, hchg.2.2.2.1, hchg.2.2.2.2,
        by rw [hptr_sh, hptr_eq']; dsimp only [ptrBase]; omega,
        by rw [hptr_sh]; dsimp only [outEnd]; omega⟩
    · rw [hheap_val]
      refine ⟨by dsimp only [outEnd, ptrBase] at hmid_eq ⊢; omega, hwords_lt, fun j hj => ?_⟩
      obtain ⟨_, hAt, hge_p, hle_o⟩ := hPk2_sp ⟨j, hj⟩
      simp only [hj, ↓reduceDIte]
      have hge_p' : ptrBase + k + k ≤ stP2.mem (ptrBase + k + j) := by dsimp only at hge_p; omega
      exact ⟨hAt, hge_p', hle_o⟩
  refine ⟨.returned outEnd, stPk2, 167 + cL + cU + cZ + cPk1 + cPk2, hrun_full, S', xL, hrep_final,
    ?_, ?_, hcost_final, hxL1, hxL2, hxL3, hpost_at⟩
  · simp only [compLSFDSFullWithSplits, ↓reduceIte]
    rcases hpost_at with ⟨hk_, b_, bp_, hp_, tw_, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨hk_, b_, bp_, hp_, tw_, outEnd, U, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · refine ⟨by dsimp only [outEnd, Outcome.value, ptrBase] at hmid_eq ⊢; omega,
      le_trans hout_le_buf (by rw [hsp_eq]; simpa [compBatchSpaceFull, List.getD_cons_zero, List.getD_cons_succ, hmem_vCap, hmem_eCap, htw_eq, hnumU_m] using hbuf_le_sp),
      hzPk2, fun a ha hnf => ?_, fun a ha => Or.inl (by simpa [compLSFRepFull, compLSFRep, compFoot, hxL7] using ha)⟩
    have hout : a < b ∨ x.endAddr ≤ a := by
      simp only [compFoot, not_and, not_lt] at hnf
      by_cases h1 : a < b; exact Or.inl h1; exact Or.inr (hnf (le_of_not_gt h1))
    rw [hPk2_bl a (by omega), hPk1_bl a (by omega), hZ_fr a (Or.inl (by omega)), hU_fr a (fun c hc => by
      have : b ≤ tmBase + c := by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize,
        compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
        compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega
      have := lt_of_lt_of_le (hltL c hc) hnumC; rcases hout with h | h <;> omega)]
    exact hfrL a hout (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega))
      (fun _ => Or.inl (by omega)) (fun _ => by omega) (Or.inl (by omega)) (by omega)

end

end MinCostFlow.SparseCore.Program
