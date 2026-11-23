module

public import MinCostFlow.SparseCore.Program.CompSplitListBatchLoopStep
import WordRAM.Tactic

/-!
# Main Batch Loop with Canonical Split Lists (`CompSplitListBatchLoop`)

Verifies `compBatchWithSplitsLoopStmt`: processes every update in `U` sequentially via
`compBatchWithSplitsStep_runs`, maintaining `CompLSFRepDirty`, cut logs, split vertices, AND
per-branch canonical split entries `canonSplitList (S j) U` in `spBufBase` / `spCntBase`, with
amortized cost bounded against `compPhiFull`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

set_option maxHeartbeats 800000 in
open Classical in
/-- Verification of `compBatchWithSplitsLoopStmt`: processes every update in `U` sequentially,
maintaining `CompLSFRepDirty`, cut logs, split vertices, AND per-branch canonical split entries
`canonSplitList (S j) U` in `spBufBase` / `spCntBase`, while bounding `c + 120 * ∑ cuts +
180 * ∑ splits + compPhiFull`. -/
theorem compBatchWithSplitsLoop_runs {W : LSFWindowImpl}
    {w k b bZero bLogAdd bPreLog bLsf bCons bErase bApp bMark bDisp bIns bDel bSplit
      bSort bRootVal bEnds bEndRoots bUFInitFind bUFPairUnion bUFClean bEmit
      batchPtr heap numU cntBase splitBase spBufBase spCntBase oldCntBase endsTmp ufBase updBuf
      totalWords : ℕ}
    {p : Program} {mem0 : ℕ → ℕ} {ω : ℕ → Bool}
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
    (hbatch_words : ∀ i < totalWords, mem0 (batchPtr + i) < 2 ^ w)
    (hbatch_heap : batchPtr + totalWords ≤ heap)
    (hspBuf_def : spBufBase = splitBase + numU)
    (holdCnt_def : oldCntBase = spCntBase + k)
    (hends_def : endsTmp = oldCntBase + k)
    (huf_def : ufBase = endsTmp + 2) :
    ∀ (U : List Update) (idx uPtr nSp remWords : ℕ)
      (S : CompLSFFamily k) (x : CompLSFMeta k)
      (touched : List ℕ) (cnts spCnts : Fin k → ℕ) (st : State),
      idx + U.length = numU →
      batchPtr + 1 ≤ uPtr →
      uPtr + remWords ≤ batchPtr + totalWords →
      (∀ i < totalWords, batchPtr + i < b ∨ x.endAddr ≤ batchPtr + i) →
      (∀ i < totalWords, st.mem (batchPtr + i) = mem0 (batchPtr + i)) →
      (hrep : CompLSFRepDirty W k b S x touched st.mem) →
      touched.Nodup → (∀ c ∈ touched, c < x.numComps) →
      touched.length ≤ 2 * idx →
      nSp ≤ idx →
      st.regs 0 = b → st.regs 2 = heap → st.regs 3 = k → st.regs 4 = x.vCap →
      st.regs 6 = numU → st.regs 7 = cntBase → st.regs 8 = splitBase → st.regs 9 = updBuf →
      st.regs 10 = idx → st.regs 11 = uPtr → st.regs 12 = nSp →
      BatchBodyAt mem0 uPtr (S ⟨0, hrep.1⟩).G U remWords →
      (S ⟨0, hrep.1⟩).G.BatchIsValid U →
      BatchWithinCaps x.vCap x.eCap U →
      x.endAddr ≤ heap →
      heap + 1 + 2 * numU ≤ cntBase →
      cntBase + k + 2 * (k * x.vCap) ≤ splitBase →
      spCntBase = spBufBase + 4 * (k * x.vCap) →
      ufBase + ufEmitScratchSize x.vCap ≤ updBuf →
      updBuf + 5 + totalWords + 2 * x.eCap < 2 ^ w →
      ZeroFrom st.mem endsTmp →
      st.mem heap = touched.length →
      ListAt st.mem (heap + 1) touched →
      (∀ j : Fin k, st.mem (cntBase + j.1) = cnts j) →
      (∀ j : Fin k, cnts j ≤ (S j).RF.R.card) →
      (∀ j : Fin k, st.mem (spCntBase + j.1) = spCnts j) →
      (∀ j : Fin k, spCnts j ≤ (S j).RF.R.card) →
      let cs0 := S ⟨0, hrep.1⟩
      let S' := compLSFBatchFamily S U
      let rootsBase := cntBase + k
      let fDelBase := cntBase + k + k * x.vCap
      ∃ st' c, ∃ (x' : CompLSFMeta k) (touched' : List ℕ)
          (cuts : Fin k → List (ℕ × ℕ)) (sp : List ℕ),
        Runs w p ω (compBatchWithSplitsLoopStmt bIns bDel bSplit bEnds bEmit) st .normal st' c ∧
        (∀ r < 10, st'.regs r = st.regs r) ∧
        st'.regs 12 = nSp + sp.length ∧
        x'.vCap = x.vCap ∧ x'.eCap = x.eCap ∧ x'.L_w = x.L_w ∧
        x'.numComps = x.numComps ∧ x'.numEdgeful = x.numEdgeful ∧
        x'.m0Total = x.m0Total ∧ x'.endAddr = x.endAddr ∧ HEq x'.compOf x.compOf ∧
        CompLSFRepDirty W k b S' x' touched' st'.mem ∧
        touched'.Nodup ∧ (∀ c ∈ touched', c < x.numComps) ∧
        touched'.length ≤ 2 * numU ∧
        sp.length ≤ U.length ∧
        st'.mem heap = touched'.length ∧
        ListAt st'.mem (heap + 1) touched' ∧
        (∀ i (hi : i < sp.length), st'.mem (splitBase + (nSp + i)) = sp[i]) ∧
        (∀ j : Fin k,
          st'.mem (cntBase + j.1) = cnts j + (cuts j).length ∧
          (∀ i (hi : i < (cuts j).length),
            st'.mem (rootsBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].2 ∧
            st'.mem (fDelBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].1) ∧
          CompForestCutsValid x.vCap (S j).RF (cuts j) ∧
          ((cuts j).map Prod.fst).Nodup ∧
          ((cuts j).map Prod.fst).toFinset = (S j).RF.F.E \ (S' j).RF.F.E ∧
          (S' j).RF.F.E ⊆ (S j).RF.F.E ∧
          ((cuts j).map Prod.snd).Nodup ∧
          sp.Nodup ∧
          (∀ r ∈ (cuts j).map Prod.snd, r ∉ sp) ∧
          ((cuts j).map Prod.snd).toFinset ∪ sp.toFinset = (S' j).RF.R \ (S j).RF.R ∧
          (S j).RF.R ⊆ (S' j).RF.R) ∧
        (∀ j : Fin k,
          let spL := canonSplitList (S j) U
          st'.mem (spCntBase + j.1) = spCnts j + spL.length ∧
          spCnts j + spL.length ≤ (S' j).RF.R.card ∧
          (∀ i (hi : i < spL.length),
            st'.mem (spBufBase + 4 * (j.1 * x.vCap) + 4 * (spCnts j + i)) =
              (if spL[i].isRelease then 1 else 0) ∧
            st'.mem (spBufBase + 4 * (j.1 * x.vCap) + 4 * (spCnts j + i) + 1) = spL[i].edge ∧
            st'.mem (spBufBase + 4 * (j.1 * x.vCap) + 4 * (spCnts j + i) + 2) = spL[i].kept ∧
            st'.mem (spBufBase + 4 * (j.1 * x.vCap) + 4 * (spCnts j + i) + 3) = spL[i].fresh)) ∧
        (∀ a,
          (a < b ∨ x.endAddr ≤ a) →
          a ≠ heap → (a < heap + 1 + touched.length ∨ heap + 1 + 2 * numU ≤ a) →
          (a < splitBase + nSp ∨ splitBase + nSp + sp.length ≤ a) →
          (∀ j : Fin k, a ≠ cntBase + j.1) →
          (∀ j : Fin k, a < rootsBase + j.1 * x.vCap + cnts j ∨
            rootsBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
          (∀ j : Fin k, a < fDelBase + j.1 * x.vCap + cnts j ∨
            fDelBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
          (∀ j : Fin k, a < spBufBase + 4 * (j.1 * x.vCap) + 4 * spCnts j ∨
            spBufBase + 4 * (j.1 * x.vCap) + 4 * (spCnts j + (canonSplitList (S j) U).length) ≤ a) →
          (∀ j : Fin k, a ≠ spCntBase + j.1) →
          (a < oldCntBase ∨ oldCntBase + k ≤ a) →
          a < endsTmp → st'.mem a = st.mem a) ∧
        ZeroFrom st'.mem endsTmp ∧
        c + 120 * (∑ j : Fin k, (cuts j).length) +
            180 * (∑ j : Fin k, (canonSplitList (S j) U).length) +
            compPhiFull k b x' st'.mem ≤
          compPhiFull k b x st.mem + 2650 * k * U.length + 10 +
            k * compBatchStepsCost mem0 x.L_w cs0 uPtr U := by
  intro U
  induction U with
  | nil =>
    intro idx uPtr nSp remWords S x touched cnts spCnts st hidx _ _ _ _ hrep hnd hlt hlen hnsp
      _ _ _ _ hr6 _ _ _ hr10 _ hr12 _ _ _ _ _ _ _ _ _ hz hhp hls hcnts_m _ hspCnts_m hspCnts_le
    have hidx_eq : idx = numU := by simp at hidx; omega
    refine ⟨st, 4, x, touched, fun _ => [], [],
      runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr10, hr6, hidx_eq],
        rfl, rfl, by simp [Expr.size]⟩),
      fun _ _ => rfl, by simp [hr12], rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl,
      hrep, hnd, hlt, by omega, Nat.zero_le _, hhp, hls, fun _ h => by simp at h,
      fun j => ⟨by simpa using hcnts_m j, fun _ h => by simp at h, trivial,
        List.nodup_nil, by simp [compLSFBatchFamily, compLSFBatch], Finset.Subset.rfl, List.nodup_nil, List.nodup_nil,
        fun _ h => by simp at h, by simp [compLSFBatchFamily, compLSFBatch], Finset.Subset.rfl⟩,
      fun j => ⟨by simpa [canonSplitList] using hspCnts_m j,
        by simpa [canonSplitList, compLSFBatchFamily, compLSFBatch] using hspCnts_le j,
        fun _ h => by simp [canonSplitList] at h⟩,
      fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl, hz, by simp [canonSplitList]; omega⟩
  | cons u us ih =>
    intro idx uPtr nSp remWords S x touched cnts spCnts st hidx hu_ge hu_le hout_b hag_b
      hrep hnd hlt hlen hnsp hr0 hr2 hr3 hr4 hr6 hr7 hr8 hr9 hr10 hr11 hr12
      hBody hVal hCaps hend_h hheap_cnt hcnt_sp hspCnt_def huf_le hbuf_w hz hhp hls
      hcnts_m hcnts_le hspCnts_m hspCnts_le
    intro cs0 S' rootsBase fDelBase
    have hk : 1 ≤ k := hrep.1
    have hw1 : 1 < 2 ^ w := by omega
    have hidx_lt : idx < numU := by simp at hidx; omega
    obtain ⟨uLen, huLen_le, hu_at0, hBody2⟩ := hBody
    rcases hVal with ⟨hu_val, hVal2⟩
    have hCaps1 : UpdateWithinCaps x.vCap x.eCap u ∧ BatchWithinCaps x.vCap x.eCap us := by
      simpa [BatchWithinCaps] using hCaps
    have huLen_eq : dgUpdateMemLen mem0 uPtr = uLen := dgUpdateMemLen_eq hu_at0
    have huLen_ge2 : 2 ≤ uLen := updateAt_len_ge_two hu_at0
    have hu_mem_ag : ∀ i < uLen, st.mem (uPtr + i) = mem0 (uPtr + i) := fun i hi => by
      have h := hag_b (uPtr - batchPtr + i) (by omega)
      rwa [show batchPtr + (uPtr - batchPtr + i) = uPtr + i by omega] at h
    have hu_words : ∀ i < uLen, st.mem (uPtr + i) < 2 ^ w := fun i hi => by
      rw [hu_mem_ag i hi]
      have h := hbatch_words (uPtr - batchPtr + i) (by omega)
      rwa [show batchPtr + (uPtr - batchPtr + i) = uPtr + i by omega] at h
    have hu_out : ∀ i < uLen, (uPtr + i < b ∨ x.endAddr ≤ uPtr + i) ∧ uPtr + i < heap := fun i hi => by
      have h1 := hout_b (uPtr - batchPtr + i) (by omega)
      rw [show batchPtr + (uPtr - batchPtr + i) = uPtr + i by omega] at h1
      exact ⟨h1, by omega⟩
    have hu_at : UpdateAt st.mem uPtr cs0.G u uLen := by
      obtain ⟨l', _, hu_at', hrem'⟩ :=
        compBatchBodyAt_of_agree (U := [u]) (tw := uLen) ⟨uLen, le_refl uLen, hu_at0, Nat.sub_self uLen⟩ hu_mem_ag
      have hl'eq : l' = uLen := by dsimp [BatchBodyAt] at hrem'; omega
      exact hl'eq ▸ hu_at'
    let S1 : CompLSFFamily k := fun j => compLSFStepSingle (S j) u
    obtain ⟨st2, cBody, x1, touched1, cuts1, sp1, hrun_body, hr2_lt10, hr2_10, hr2_11, hr2_12, hsp1_le,
      hx1_1, hx1_2, hx1_3, hx1_4, hx1_5, hx1_6, hx1_7, hx1_8, hrep1, hnd1, hlt1, hlen1, hlen_ge1,
      hhp1, hls1, hsp1_m, hbr1, hsp1_br, hcomb, hfr1, hz1, hcost1⟩ :=
      compBatchWithSplitsStep_runs hpZero hpLogAdd hpPreLog hpLsf hpCons hpErase hpApp hpMark hpDisp
        hpIns hpDel hpSplit hpSort hpRootVal hpEnds hpEndRoots hpInitFind hpPairUnion hpClean hpEmit
        hw16 hrep hnd hlt hidx_lt hlen hnsp hu_at hu_mem_ag hu_words hu_out huLen_eq huLen_ge2
        hu_val hCaps1.1 hr0 hr2 hr3 hr4 hr6 hr7 hr8 hr9 hr10 hr11 hr12 hend_h hheap_cnt hcnt_sp
        hspBuf_def hspCnt_def holdCnt_def hends_def huf_def huf_le (by omega) (by omega) hz hhp hls
        hcnts_m hcnts_le hspCnts_m hspCnts_le
    have hst2_batch : ∀ i < totalWords, st2.mem (batchPtr + i) = mem0 (batchPtr + i) := fun i hi =>
      (hfr1 _ (hout_b i hi) (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (fun _ => by omega)
        (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega))
        (fun _ => by omega) (Or.inl (by omega)) (by omega)).trans (hag_b i hi)
    obtain ⟨st3, cRest, x2, touched2, cuts2, sp2, hrun_rest, hr3_lt10, hr3_12,
      hx2_1, hx2_2, hx2_3, hx2_4, hx2_5, hx2_6, hx2_7, hx2_8, hrep2, hnd2, hlt2, hlen2, hsp2_le,
      hhp2, hls2, hsp2_m, hbr2, hspL2, hfr2, hz2, hcost2⟩ :=
      ih (idx + 1) (uPtr + uLen) (nSp + sp1.length) (remWords - uLen) S1 x1 touched1
        (fun j => cnts j + (cuts1 j).length) (fun j => spCnts j + (canonStepSplits (S j) u).length) st2
        (by simp at hidx ⊢; omega) (by omega) (by omega) (by simpa [hx1_7] using hout_b) hst2_batch
        hrep1 hnd1 (by simpa [hx1_4] using hlt1) (by omega) (by omega)
        ((hr2_lt10 0 (by omega)).trans hr0) ((hr2_lt10 2 (by omega)).trans hr2)
        ((hr2_lt10 3 (by omega)).trans hr3) (by rw [hr2_lt10 4 (by omega), hr4, hx1_1])
        ((hr2_lt10 6 (by omega)).trans hr6) ((hr2_lt10 7 (by omega)).trans hr7)
        ((hr2_lt10 8 (by omega)).trans hr8) ((hr2_lt10 9 (by omega)).trans hr9)
        hr2_10 hr2_11 hr2_12
        (by simpa [S1, cs0, compLSFStepSingle] using hBody2)
        (by simpa [S1, cs0, compLSFStepSingle] using hVal2)
        (by simpa [hx1_1, hx1_2] using hCaps1.2)
        (by omega) hheap_cnt (by rw [hx1_1]; exact hcnt_sp) (by rw [hx1_1]; exact hspCnt_def)
        (by rw [hx1_1]; exact huf_le) (by rw [hx1_2]; exact hbuf_w) hz1
        hhp1 hls1 (fun j => (hbr1 j).1) (fun j => (hbr1 j).2.2)
        (fun j => (hsp1_br j).1) (fun j => (hsp1_br j).2.1)
    have hrun_full : Runs w p ω (compBatchWithSplitsLoopStmt bIns bDel bSplit bEnds bEmit)
        st .normal st3 (3 + cBody + cRest + 1) := by
      rw [compBatchWithSplitsLoopStmt_eq]
      exact runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st2, cBody, cRest,
        by simp [Expr.eval, BinOp.eval, hr10, hr6, hidx_lt, hw1], by decide, hrun_body, hrun_rest,
        by simp [Expr.size]⟩))
    have hS'_eq : S' = compLSFBatchFamily S1 us := by
      funext j; simp [S', S1, compLSFBatchFamily, compLSFBatch]
    have hcomb_fin := hcomb cuts2 sp2 S' (fun j => by simpa [hx1_1, hS'_eq] using (hbr2 j).2.2)
    have hsp_len_add : (sp1 ++ sp2).length = sp1.length + sp2.length := List.length_append
    have hR1_le : ∀ j : Fin k, (S1 j).RF.R.card ≤ x.vCap := fun j => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨ℓ₁, hBr1⟩, _, hT1, _⟩ := hrep1
      have hT1j := compEdgeTrack_of_same_graph hT1 (hBr1 j).2.1 (hBr1 j).2.2.1
        (hBr1 j).2.2.2.2.1 (hBr1 j).2.2.2.2.2.2
      rw [← hx1_1]
      exact (Finset.card_le_card fun r hr => Finset.mem_range.mpr
        (hT1j.hVlt r ((compLSF_RF_isRSF (hBr1 j).1).2.2.1 hr))).trans (by simp)
    have hR2_le : ∀ j : Fin k, (S' j).RF.R.card ≤ x.vCap := fun j => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨ℓ₂, hBr2⟩, _, hT2, _⟩ := hrep2
      have hT2j := compEdgeTrack_of_same_graph hT2 (hBr2 j).2.1 (hBr2 j).2.2.1
        (hBr2 j).2.2.2.2.1 (hBr2 j).2.2.2.2.2.2
      rw [hS'_eq, ← hx1_1, ← hx2_1]
      exact (Finset.card_le_card fun r hr => Finset.mem_range.mpr
        (hT2j.hVlt r ((compLSF_RF_isRSF (hBr2 j).1).2.2.1 hr))).trans (by simp)
    have hcut_tot_le : ∀ j0 : Fin k, cnts j0 + (cuts1 j0).length + (cuts2 j0).length ≤ x.vCap := fun j0 => by
      obtain ⟨_, _, _, _, _, _, hndR2, _, _, hsR2, hRsub2⟩ := hbr2 j0
      have hcard2 : (cuts2 j0).length ≤ ((compLSFBatchFamily S1 us j0).RF.R \ (S1 j0).RF.R).card := by
        rw [← List.length_map (f := Prod.snd), ← List.toFinset_card_of_nodup hndR2, ← hsR2]
        exact Finset.card_le_card Finset.subset_union_left
      have hsdiff := Finset.card_sdiff_add_card_eq_card hRsub2
      have hR2j : (compLSFBatchFamily S1 us j0).RF.R.card ≤ x.vCap := by rw [← hS'_eq]; exact hR2_le j0
      have := (hbr1 j0).2.2; dsimp only [S1] at *; omega
    have hcost_total : (3 + cBody + cRest + 1) +
          120 * (∑ j : Fin k, (cuts1 j ++ cuts2 j).length) +
          180 * (∑ j : Fin k, (canonSplitList (S j) (u :: us)).length) +
          compPhiFull k b x2 st3.mem ≤
        compPhiFull k b x st.mem + 2650 * k * (u :: us).length + 10 +
          k * compBatchStepsCost mem0 x.L_w cs0 uPtr (u :: us) := by
      have hsum_cuts : (∑ j : Fin k, (cuts1 j ++ cuts2 j).length) =
          (∑ j : Fin k, (cuts1 j).length) + (∑ j : Fin k, (cuts2 j).length) := by
        simp [List.length_append, Finset.sum_add_distrib]
      have hsum_sp : (∑ j : Fin k, (canonSplitList (S j) (u :: us)).length) =
          (∑ j : Fin k, (canonStepSplits (S j) u).length) +
          (∑ j : Fin k, (canonSplitList (S1 j) us).length) := by
        simp [canonSplitList, S1, List.length_append, Finset.sum_add_distrib]
      have hsteps_eq : compBatchStepsCost mem0 x.L_w cs0 uPtr (u :: us) =
          ((touchedComps cs0 u).filter fun C => 1 ≤ (compGraph cs0.G₀ C).m).sum (fun C =>
            lsfBatchCostFactor * ((1 + projUpdWords mem0 cs0 C uPtr u) * x.L_w + 1) +
            lsfBatchCostFactor * (projUpdWords mem0 cs0 C uPtr u * x.L_w)) +
          compBatchStepsCost mem0 x.L_w (compLSFStepSingle cs0 u) (uPtr + uLen) us := by
        simp [compBatchStepsCost, huLen_eq]
      have hk_mul : 2650 * k * (u :: us).length = 2650 * k + 2650 * k * us.length := by
        simp only [List.length_cons]; ring
      have h10 : 10 ≤ 10 * k := Nat.le_mul_of_pos_right 10 hk
      rw [hsum_cuts, hsum_sp, hsteps_eq, Nat.mul_add 120, Nat.mul_add 180, Nat.mul_add k, hk_mul]
      rw [hx1_3] at hcost2
      dsimp only [S1, cs0] at hcost1 hcost2 ⊢
      omega
    refine ⟨st3, _, x2, touched2, fun j => cuts1 j ++ cuts2 j, sp1 ++ sp2, hrun_full,
      fun r hr => (hr3_lt10 r hr).trans (hr2_lt10 r hr),
      by rw [hr3_12, hsp_len_add]; omega,
      hx2_1.trans hx1_1, hx2_2.trans hx1_2, hx2_3.trans hx1_3, hx2_4.trans hx1_4,
      hx2_5.trans hx1_5, hx2_6.trans hx1_6, hx2_7.trans hx1_7, hx2_8.trans hx1_8,
      hrep2, hnd2, by simpa [hx1_4] using hlt2, hlen2, by rw [hsp_len_add]; simp; omega, hhp2, hls2,
      fun i hi => by
        by_cases h1 : i < sp1.length
        · have heq : (sp1 ++ sp2)[i] = sp1[i] := List.getElem_append_left h1
          rw [heq, hfr2 _ (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
            (fun j0 => by have := j0.2; omega)
            (fun j0 => Or.inr (by
              rw [hx1_1]; have hm := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ k by have := j0.2; omega)
              rw [Nat.add_mul, Nat.one_mul] at hm; have := hcut_tot_le j0; omega))
            (fun j0 => Or.inr (by
              rw [hx1_1]; have hm := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ k by have := j0.2; omega)
              rw [Nat.add_mul, Nat.one_mul] at hm; have := hcut_tot_le j0; omega))
            (fun _ => Or.inl (by omega)) (fun _ => by omega) (Or.inl (by omega)) (by omega)]
          exact hsp1_m i h1
        · have heq : (sp1 ++ sp2)[i] = sp2[i - sp1.length]'(by rw [hsp_len_add] at hi; omega) :=
            List.getElem_append_right (by omega)
          rw [heq, show splitBase + (nSp + i) = splitBase + (nSp + sp1.length + (i - sp1.length)) by omega]
          exact hsp2_m (i - sp1.length) (by rw [hsp_len_add] at hi; omega),
      fun j => by
        obtain ⟨hbc1, hbc2, _, _, _, _, _, _, _, _, _⟩ := hbr2 j
        obtain ⟨hcc1, hcc2, hcc3, hcc4, hcc5, hcc6, hcc7, hcc8, hcc9⟩ := hcomb_fin j
        refine ⟨by rw [hbc1, List.length_append]; omega, fun i hi => ?_,
          hcc1, hcc2, hcc3, hcc4, hcc5, hcc6, hcc7, hcc8, hcc9⟩
        by_cases h1 : i < (cuts1 j).length
        · have heq : (cuts1 j ++ cuts2 j)[i] = (cuts1 j)[i] := List.getElem_append_left h1
          have hjv_k : j.1 * x.vCap + x.vCap ≤ k * x.vCap := by
            have := Nat.mul_le_mul_right x.vCap (show j.1 + 1 ≤ k by have := j.2; omega)
            rw [Nat.add_mul, Nat.one_mul] at this; exact this
          have hbd_j := le_trans (hbr1 j).2.2 (hR1_le j)
          have hsep : ∀ (j0 : Fin k) (base : ℕ), base = rootsBase ∨ base = fDelBase →
              base + j.1 * x.vCap + (cnts j + i) < base + j0.1 * x.vCap + (cnts j0 + (cuts1 j0).length) ∨
              base + j0.1 * x.vCap + (cnts j0 + (cuts1 j0).length) + (cuts2 j0).length ≤
                base + j.1 * x.vCap + (cnts j + i) := fun j0 base _ => by
            by_cases hjj : j0 = j
            · subst hjj; left; omega
            · have hne : j0.1 ≠ j.1 := fun h => hjj (Fin.ext h)
              rcases lt_or_gt_of_ne hne with hlt' | hgt'
              · right; have hm := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ j.1 by omega)
                rw [Nat.add_mul, Nat.one_mul] at hm; have := hcut_tot_le j0; omega
              · left; have hm := Nat.mul_le_mul_right x.vCap (show j.1 + 1 ≤ j0.1 by omega)
                rw [Nat.add_mul, Nat.one_mul] at hm; omega
          rw [heq]
          constructor
          · rw [hfr2 _ (Or.inr (by dsimp only [rootsBase]; omega)) (by dsimp only [rootsBase]; omega)
              (Or.inr (by dsimp only [rootsBase]; omega)) (Or.inl (by dsimp only [rootsBase]; omega))
              (fun j0 => by have := j0.2; dsimp only [rootsBase]; omega)
              (fun j0 => by rw [hx1_1]; exact hsep j0 rootsBase (Or.inl rfl))
              (fun j0 => Or.inl (by rw [hx1_1]; dsimp only [rootsBase, fDelBase]; omega))
              (fun _ => Or.inl (by dsimp only [rootsBase]; omega))
              (fun _ => by dsimp only [rootsBase]; omega) (Or.inl (by dsimp only [rootsBase]; omega))
              (by dsimp only [rootsBase]; omega)]
            exact ((hbr1 j).2.1 i h1).1
          · rw [hfr2 _ (Or.inr (by dsimp only [fDelBase]; omega)) (by dsimp only [fDelBase]; omega)
              (Or.inr (by dsimp only [fDelBase]; omega)) (Or.inl (by dsimp only [fDelBase]; omega))
              (fun j0 => by have := j0.2; dsimp only [fDelBase]; omega)
              (fun j0 => Or.inr (by
                rw [hx1_1]
                have hm := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ k by have := j0.2; omega)
                rw [Nat.add_mul, Nat.one_mul] at hm; have := hcut_tot_le j0; dsimp only [rootsBase, fDelBase]; omega))
              (fun j0 => by rw [hx1_1]; exact hsep j0 fDelBase (Or.inr rfl))
              (fun _ => Or.inl (by dsimp only [fDelBase]; omega))
              (fun _ => by dsimp only [fDelBase]; omega) (Or.inl (by dsimp only [fDelBase]; omega))
              (by dsimp only [fDelBase]; omega)]
            exact ((hbr1 j).2.1 i h1).2
        · have heq : (cuts1 j ++ cuts2 j)[i] = (cuts2 j)[i - (cuts1 j).length]'(by rw [List.length_append] at hi; omega) :=
            List.getElem_append_right (by omega)
          rw [heq, show cnts j + i = cnts j + (cuts1 j).length + (i - (cuts1 j).length) by omega]
          simpa [hx1_1] using hbc2 (i - (cuts1 j).length) (by rw [List.length_append] at hi; omega),
      fun j => by
        obtain ⟨hsL2_c, hsL2_le, hsL2_e⟩ := hspL2 j
        refine ⟨by rw [hsL2_c]; simp [canonSplitList, S1, List.length_append]; omega,
          by rw [hS'_eq]; simp only [canonSplitList, List.length_append]; dsimp only [S1, compLSFBatchFamily] at hsL2_le ⊢; omega,
          fun i hi => ?_⟩
        by_cases h1 : i < (canonStepSplits (S j) u).length
        · have heq : (canonSplitList (S j) (u :: us))[i] = (canonStepSplits (S j) u)[i] := by
            simp only [canonSplitList]; exact List.getElem_append_left h1
          have hjv_k : j.1 * x.vCap + x.vCap ≤ k * x.vCap := by
            have := Nat.mul_le_mul_right x.vCap (show j.1 + 1 ≤ k by have := j.2; omega)
            rw [Nat.add_mul, Nat.one_mul] at this; exact this
          have hbd_j := le_trans (hsp1_br j).2.1 (hR1_le j)
          have hsp_cell : ∀ off < 4, st3.mem (spBufBase + 4 * (j.1 * x.vCap) + 4 * (spCnts j + i) + off) =
              st2.mem (spBufBase + 4 * (j.1 * x.vCap) + 4 * (spCnts j + i) + off) := fun off hoff =>
            hfr2 _ (Or.inr (by rw [hx1_7]; omega)) (by omega) (Or.inr (by omega))
              (Or.inr (by simp at hidx; omega))
              (fun j0 => by have := j0.2; omega)
              (fun j0 => Or.inr (by
                rw [hx1_1]
                have hm := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ k by have := j0.2; omega)
                rw [Nat.add_mul, Nat.one_mul] at hm; have := hcut_tot_le j0; omega))
              (fun j0 => Or.inr (by
                rw [hx1_1]
                have hm := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ k by have := j0.2; omega)
                rw [Nat.add_mul, Nat.one_mul] at hm; have := hcut_tot_le j0; omega))
              (fun j0 => by
                rw [hx1_1]
                by_cases hjj : j0 = j
                · subst hjj; left; omega
                · have hne : j0.1 ≠ j.1 := fun h => hjj (Fin.ext h)
                  rcases lt_or_gt_of_ne hne with hlt' | hgt'
                  · right; have hm := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ j.1 by omega)
                    rw [Nat.add_mul, Nat.one_mul] at hm
                    have hR2j0 : (compLSFBatchFamily S1 us j0).RF.R.card ≤ x.vCap := by rw [← hS'_eq]; exact hR2_le j0
                    have hbd0 := le_trans (hspL2 j0).2.1 hR2j0; omega
                  · left; have hm := Nat.mul_le_mul_right x.vCap (show j.1 + 1 ≤ j0.1 by omega)
                    rw [Nat.add_mul, Nat.one_mul] at hm; omega)
              (fun _ => by omega) (Or.inl (by omega)) (by omega)
          have hb := (hsp1_br j).2.2 i h1
          rw [heq]
          exact ⟨by simpa using (hsp_cell 0 (by omega)).trans hb.1, (hsp_cell 1 (by omega)).trans hb.2.1,
            (hsp_cell 2 (by omega)).trans hb.2.2.1, (hsp_cell 3 (by omega)).trans hb.2.2.2⟩
        · have heq : (canonSplitList (S j) (u :: us))[i] =
              (canonSplitList (S1 j) us)[i - (canonStepSplits (S j) u).length]'(by
                simp only [canonSplitList, S1, List.length_append] at hi ⊢; omega) := by
            simp only [canonSplitList]; exact List.getElem_append_right (by omega)
          rw [heq, show spCnts j + i = spCnts j + (canonStepSplits (S j) u).length +
            (i - (canonStepSplits (S j) u).length) by omega]
          simpa [hx1_1] using hsL2_e (i - (canonStepSplits (S j) u).length)
            (by simp only [canonSplitList, S1, List.length_append] at hi ⊢; omega),
      fun a ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9 ha10 ha11 =>
        (hfr2 a (by simpa [hx1_7] using ha1) ha2 (by omega)
          (by rcases ha4 with h | h; left; omega; right; rw [hsp_len_add] at h; omega)
          ha5
          (fun j => by rw [hx1_1]; rcases ha6 j with h | h; left; omega; right; rw [List.length_append] at h; omega)
          (fun j => by rw [hx1_1]; rcases ha7 j with h | h; left; omega; right; rw [List.length_append] at h; omega)
          (fun j => by rw [hx1_1]; rcases ha8 j with h | h; left; omega; right; simp only [canonSplitList, S1, List.length_append] at h ⊢; omega)
          ha9 ha10 ha11).trans
        (hfr1 a ha1 ha2 (by omega)
          (by rcases ha4 with h | h; left; omega; right; rw [hsp_len_add] at h; omega)
          ha5
          (fun j => by rcases ha6 j with h | h; left; omega; right; rw [List.length_append] at h; omega)
          (fun j => by rcases ha7 j with h | h; left; omega; right; rw [List.length_append] at h; omega)
          (fun j => by rcases ha8 j with h | h; left; omega; right; simp only [canonSplitList, List.length_append] at h ⊢; omega)
          ha9 ha10 ha11),
      hz2, hcost_total⟩

end

end MinCostFlow.SparseCore.Program
