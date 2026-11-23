module

public import MinCostFlow.SparseCore.Program.AssemblyFirstTourStepIter

import Mathlib.Tactic

/-!
# Inductive verification of the main update loop (`AssemblyFirstTourStepLoop`)

Verifies the `while r15 < r11` loop of `asmFirstTourBlockStepStmt` (`tourBlock_loop_runs`),
dispatching `.insert` (tag 0), forest `.delete` (tag 1, `isOpen = 0`), non-forest `.delete`
(tag 1, `isOpen = 1`), and `.split` (tag 2/3) via the per-case lemmas in
`AssemblyFirstTourStepCases`/`Walls` and the register wrappers in `AssemblyFirstTourStepIter`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

public section

set_option maxHeartbeats 1600000 in
/-- **Inductive verification of the main update loop** (`while r15 < r11`) of `asmFirstTourBlockStepStmt`. -/
theorem tourBlock_loop_runs {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {w vCap eCap bSelf bTour bOut bCopy tourH batch words edits editWords spPtr h statePtr edCopy
      nUpd totalEdits : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpT : HasTourProcs p bTour)
    (hpO : OutProcsAt p bOut (tourOp bTour 8) (tourOp bTour 7) (tourOp bTour 11) (tourOp bTour 9))
    (hpC : p.HasAt bCopy [copyWords])
    (hpRel : p.procs[bSelf + 0]? = some (asmFirstTourConsumeRelStmt (tourOp bTour 1) (outIdxSmallSide bOut)))
    (hpMove : p.procs[bSelf + 1]? = some (asmFirstTourApplyMoveStmt (bTour + 75) (tourOp bTour 0)))
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    {L : List CompSplitEntry} {keep E₀ : Finset ℕ} {G₀ : MGraph}
    (hstatePtr : statePtr = h + 1) (hedCopy : edCopy = h + 4)
    (hbatch_le : batch + words ≤ h) (hsp_le0 : spPtr + 1 + 4 * L.length ≤ h)
    (hsp_disj_st : statePtr + 3 ≤ spPtr ∨ spPtr + 1 + 4 * L.length ≤ statePtr)
    (hbatch_w : batch + words < 2 ^ w) (_hsp_w : spPtr + 1 + 4 * L.length < 2 ^ w)
    (hU_all_lt : nUpd < 2 ^ w) (htot_lt : totalEdits < 2 ^ w) :
    ∀ (U_rem : List Update) (cs : CompLSFState) (ed_rem : List OrdEdit)
      (uPtr uWordsRem ePtr eWordsRem eIdx i spIdx splitPtr last hCur : ℕ)
      (s : TourAbs) (tx : (tourAsmRep vCap eCap).τ) (st : State)
      (M : Finset ℕ) (S_cur : MGraph) (P_done : List Update) (Ys_done : List (List End)),
      let Uq := (splitQuietPrefix cs U_rem).1
      let U_wall := (splitQuietPrefix cs U_rem).2
      let cs_wall := compLSFBatch cs Uq
      let splitsRem := canonSplitList cs_wall U_wall
      let PsRem := restrictSplits keep (canonCoreBatch cs_wall U_wall)
      st.regs 0 = tourH → st.regs 1 = batch → st.regs 2 = words → st.regs 3 = edits →
      st.regs 4 = editWords → st.regs 5 = spPtr → st.regs 6 = h →
      st.regs 7 = statePtr → st.regs 8 = edCopy → st.regs 9 = hCur →
      st.regs 10 = L.length → st.regs 11 = nUpd →
      st.regs 12 = uPtr → st.regs 13 = ePtr → st.regs 14 = eIdx → st.regs 15 = i →
      i + U_rem.length = nUpd →
      batch ≤ uPtr → uPtr + uWordsRem = batch + words →
      ePtr + eWordsRem = edCopy + editWords →
      edCopy ≤ ePtr → edCopy + editWords ≤ hCur →
      ordHandleOf tourH vCap eCap ≤ h →
      eIdx + ed_rem.length = totalEdits →
      CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U_rem →
      (∀ r ∈ (compLSFBatch cs U_rem).RF.R, r < vCap) →
      OrdEditsForBatch cs.G U_rem ed_rem →
      OrdEditsValidFor vCap eCap s.ord ed_rem →
      BatchBodyAt st.mem uPtr cs.G U_rem uWordsRem →
      (∀ a, batch ≤ a → a < batch + words → ¬ (tourAsmRep vCap eCap).foot tourH tx a) →
      (∀ a, edCopy ≤ a → a < edCopy + editWords → ¬ (tourAsmRep vCap eCap).foot tourH tx a) →
      (∀ a, spPtr ≤ a → a < spPtr + 1 + 4 * L.length → ¬ (tourAsmRep vCap eCap).foot tourH tx a) →
      (∀ j < 3, ¬ (tourAsmRep vCap eCap).foot tourH tx (statePtr + j)) →
      (decodeOrdEdits st.mem ed_rem.length ePtr).1 = ed_rem →
      (decodeOrdEdits st.mem ed_rem.length ePtr).2.sum = eWordsRem →
      SplitEntriesAt st.mem spPtr L →
      st.mem statePtr = spIdx ∧ st.mem (statePtr + 1) = splitPtr ∧ st.mem (statePtr + 2) = last →
      (last = 0 ∨ edCopy + editWords ≤ last) →
      spIdx ≤ L.length → L.drop spIdx = splitsRem →
      (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s) tx st.mem →
      (∀ a, (tourAsmRep vCap eCap).foot tourH tx a → a < hCur) →
      ZeroFrom st.mem hCur →
      (∀ v x, x ∈ s.ord v ↔ x.1 ∈ cs.G.E ∧ cs.G.src x = v) →
      GraphEq s.rf.F cs_wall.RF.F → s.rf.R = cs_wall.RF.R →
      TourMarksAt s M → keep ⊆ M → M ⊆ E₀ → M ⊆ cs.G.E →
      Disjoint M cs_wall.RF.F.E → Disjoint keep (batchDeletes U_rem) →
      TourKeepMatch keep s S_cur →
      OutSplitPrefixAt st.mem splitPtr last hCur
        (fun a => (tourAsmRep vCap eCap).foot tourH tx a ∨ a < statePtr + 3)
        keep E₀ G₀ P_done S_cur Ys_done →
      hCur + 159 * (uWordsRem + eWordsRem) + splitsRem.length * tourSplitStepSpace eCap + 4 < 2 ^ w →
      let edEnd := ed_rem.drop (batchEditBlocksLen U_rem)
      ∃ hEnd stF cL txF splitPtrF lastF ePtrF sEnd MEnd SEnd YsLoop,
        Runs w p ω (.loop (.bin .lt (.reg 15) (.reg 11)) (asmFirstTourLoopBody bSelf bTour bOut bCopy))
          st .normal stF cL ∧
        stF.regs 0 = tourH ∧ stF.regs 4 = editWords ∧ stF.regs 6 = h ∧
        stF.regs 7 = statePtr ∧ stF.regs 8 = edCopy ∧ stF.regs 9 = hEnd ∧
        stF.regs 13 = ePtrF ∧ stF.regs 14 = eIdx + batchEditBlocksLen U_rem ∧
        stF.regs 15 = nUpd ∧
        ePtr ≤ ePtrF ∧ ePtrF ≤ edCopy + editWords ∧
        (decodeOrdEdits stF.mem edEnd.length ePtrF).1 = edEnd ∧
        (decodeOrdEdits stF.mem edEnd.length ePtrF).2.sum = edCopy + editWords - ePtrF ∧
        stF.mem statePtr = spIdx + splitsRem.length ∧
        stF.mem (statePtr + 1) = splitPtrF ∧ stF.mem (statePtr + 2) = lastF ∧
        (tourAsmRep vCap eCap).rep tourH (tourToAsmTour sEnd) txF stF.mem ∧
        sEnd.ord = applyOrdEdits s.ord (ed_rem.take (batchEditBlocksLen U_rem)) ∧
        GraphEq sEnd.rf.F (compLSFBatch cs U_rem).RF.F ∧
        sEnd.rf.R = (compLSFBatch cs U_rem).RF.R ∧
        OrdEditsValidFor vCap eCap sEnd.ord edEnd ∧
        TourMarksAt sEnd MEnd ∧ keep ⊆ MEnd ∧ MEnd ⊆ M ∧
        TourKeepMatch keep sEnd SEnd ∧
        OutSplitPrefixAt stF.mem splitPtrF lastF hEnd
          (fun a => (tourAsmRep vCap eCap).foot tourH txF a ∨ a < statePtr + 3)
          keep E₀ G₀ (P_done ++ PsRem) SEnd (Ys_done ++ YsLoop) ∧
        (YsLoop.map List.length).sum + tourMarkPot keep sEnd ≤
          S_cur.batchEnc PsRem + tourMarkPot keep s ∧
        hCur ≤ hEnd ∧
        hEnd ≤ hCur + 159 * (uWordsRem + (ePtrF - ePtr)) + splitsRem.length * tourSplitStepSpace eCap ∧
        ZeroFrom stF.mem hEnd ∧
        (∀ a < hCur, ¬ (tourAsmRep vCap eCap).foot tourH tx a →
          (a < statePtr ∨ statePtr + 3 ≤ a) → (last = 0 ∨ a ≠ last + 4) → stF.mem a = st.mem a) ∧
        (∀ a, (tourAsmRep vCap eCap).foot tourH txF a →
          (tourAsmRep vCap eCap).foot tourH tx a ∨ (hCur ≤ a ∧ a < hEnd)) ∧
        cL + (tourAsmRep vCap eCap).phi tourH txF stF.mem ≤
          tourBlockLoopMul * ((YsLoop.map List.length).sum + splitsRem.length + uWordsRem + (ePtrF - ePtr)) *
            ordStoreLog eCap + 10 + (tourAsmRep vCap eCap).phi tourH tx st.mem := by
  intro U_rem
  induction U_rem with
  | nil =>
    intro cs ed_rem uPtr uWordsRem ePtr eWordsRem eIdx i spIdx splitPtr last hCur
      s tx st M S_cur P_done Ys_done
    dsimp only
    intro hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11 hr12 hr13 hr14 hr15
      hiLen _ _ heEnd heGe _ _ _ _ _ _ _ hOVF _ _ _ _ _ hDec hSum _ hStM _ _ _ hRep hFoot hZero
      _ hFeq hReq hM hkM _ _ _ _ hK hPre hRoom
    have hwide : 18 ≤ 2 ^ w :=
      (tourDS_wide_of_foot hRep hFoot (by omega : hCur + 1 < 2 ^ w)).2
    have hiEq : i = nUpd := by simpa using hiLen
    have hcond0 : (Expr.bin .lt (.reg 15) (.reg 11)).eval w st = some 0 := by
      simp [Expr.eval, hr15, hr11, hiEq, BinOp.eval, (by omega : 0 < 2 ^ w)]
    have hloop0 : Runs w p ω
        (.loop (.bin .lt (.reg 15) (.reg 11)) (asmFirstTourLoopBody bSelf bTour bOut bCopy))
        st .normal st ((Expr.bin .lt (.reg 15) (.reg 11)).size + 1) :=
      runs_loop_iff.mpr (Or.inl ⟨hcond0, rfl, rfl, rfl⟩)
    refine ⟨hCur, st, _, tx, splitPtr, last, ePtr, s, M, S_cur, [], hloop0,
      hr0, hr4, hr6, hr7, hr8, hr9, hr13, by simpa [batchEditBlocksLen] using hr14,
      by rw [hr15, hiEq], le_refl _, by omega, hDec, by simp only [batchEditBlocksLen, List.map_nil, List.sum_nil, List.drop_zero, hSum]; omega,
      by simpa [splitQuietPrefix, canonSplitList] using hStM.1,
      hStM.2.1, hStM.2.2, hRep, rfl, hFeq, hReq, hOVF, hM, hkM, Finset.Subset.rfl, hK,
      by simpa [splitQuietPrefix, canonCoreBatch, restrictSplits] using hPre,
      by simp [splitQuietPrefix, canonCoreBatch, restrictSplits, MGraph.batchEnc],
      le_refl _, by omega, hZero, fun _ _ _ _ _ => rfl, fun _ ha => Or.inl ha, ?_⟩
    simp only [Expr.size]; omega
  | cons u U_rest ih =>
    intro cs ed_rem uPtr uWordsRem ePtr eWordsRem eIdx i spIdx splitPtr last hCur
      s tx st M S_cur P_done Ys_done
    dsimp only
    intro hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11 hr12 hr13 hr14 hr15
      hiLen huGe huEnd heEnd heGe hedLe hordH heIdxTot hI hBU hRlt hOFB hOVF hBB
      hBF hEF hSF hStF hDec hSum hSpAt hStM hLastGe hSpLe hDrop hRep hFoot hZero
      hOrdG hFeq hReq hM hkM hME₀ hMG hMdisj hKdisj hK hPre hRoom
    change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH s tx st.mem at hRep
    have htl : 1 ≤ ordStoreLog eCap := by rw [ordStoreLog_eq_tourLog]; simp [tourLog]
    have hwide : 18 ≤ 2 ^ w :=
      (tourDS_wide_of_foot hRep hFoot (by omega : hCur + 1 < 2 ^ w)).2
    have hiLt : i < nUpd := by simp at hiLen; omega
    have hcond1 : (Expr.bin .lt (.reg 15) (.reg 11)).eval w st = some 1 := by
      simp [Expr.eval, hr15, hr11, hiLt, BinOp.eval, (by omega : 1 < 2 ^ w)]
    obtain ⟨uLen, huLenLe, hUAt, hBBRest⟩ := hBB; have hBU1 : cs.G.UpdateIsValid u := hBU.1
    have hProps1 := compLSFStepSingle_forest_props hI hBU1; set cs1 := compLSFStepSingle cs u
    have hI1 : CompLSFInv C_lsst ℓ₀ cs1 := hProps1.1; have hG1 : cs1.G = cs.G.applyUpdate u := hProps1.2.1
    have hBUrest : cs1.G.BatchIsValid U_rest := hG1.symm ▸ hBU.2
    have hKdisj1 : Disjoint keep (batchDeletes U_rest) :=
      Disjoint.mono_right (fun f hf => by
        obtain ⟨u', hu', h⟩ := (mem_batchDeletes_iff _ _).mp hf
        exact (mem_batchDeletes_iff _ _).mpr ⟨u', List.mem_cons_of_mem _ hu', h⟩) hKdisj
    have hRlt1 : ∀ r ∈ (compLSFBatch cs1 U_rest).RF.R, r < vCap := by
      simpa [compLSFBatch, cs1] using hRlt
    cases u with
    | insert e a b =>
      obtain ⟨rfl, hListU⟩ := hUAt
      obtain ⟨y₁, y₂, ed_rest, rfl, hOFB_rest⟩ := ordEditsForBatch_insert_iff.mp hOFB
      obtain ⟨hWin1, hOVF1⟩ := ordEditsValidFor_cons hOVF
      obtain ⟨hWin2, hOVF_rest⟩ := ordEditsValidFor_cons hOVF1
      have hsq : splitQuietPrefix cs (.insert e a b :: U_rest) =
          (.insert e a b :: (splitQuietPrefix cs1 U_rest).1, (splitQuietPrefix cs1 U_rest).2) := by
        simp [splitQuietPrefix, isQuietUpdate, cs1]
      have hDec0 : (decodeOrdEdit st.mem ePtr).1 = .insertBefore a (e, true) y₁ ∧
          (decodeOrdEdit st.mem (ePtr + 4)).1 = .insertBefore b (e, false) y₂ ∧
          (decodeOrdEdits st.mem ed_rest.length (ePtr + 8)).1 = ed_rest ∧
          (decodeOrdEdits st.mem ed_rest.length (ePtr + 8)).2.sum = eWordsRem - 8 ∧
          8 ≤ eWordsRem := by
        simp only [List.length_cons, decodeOrdEdits, List.cons.injEq, List.sum_cons] at hDec hSum
        have hi1 := decodeOrdEdit_insertBefore_info hDec.1
        rw [hi1.2] at hDec hSum
        have hi2 := decodeOrdEdit_insertBefore_info hDec.2.1
        rw [hi2.2, show ePtr + 4 + 4 = ePtr + 8 by omega] at hDec hSum
        exact ⟨hDec.1, hDec.2.1, hDec.2.2, by omega, by omega⟩
      obtain ⟨hd1, hd2, hDecRest, hSumRest, h8le⟩ := hDec0
      have hw1 : a < vCap ∧ e < eCap ∧ ∀ y' ∈ y₁, y'.1 < eCap := hWin1 _ List.mem_cons_self
      have hw2 : b < vCap ∧ e < eCap ∧ ∀ y' ∈ y₂, y'.1 < eCap := hWin2 _ List.mem_cons_self
      have hBUq : cs.G.BatchIsValid (splitQuietPrefix cs (.insert e a b :: U_rest)).1 := by
        rw [← splitQuietPrefix_append cs (.insert e a b :: U_rest)] at hBU
        exact (batchIsValid_append.mp hBU).1
      have hVeq : s.rf.F.V = cs.G.V :=
        hFeq.1.trans ((compLSF_RF_isRSF (compLSFBatch_inv hI hBUq)).2.1.trans
          (quietPrefix_G_V_eq _ cs hI hBUq (splitQuietPrefix_all_quiet cs _)))
      have heF : e ∉ s.rf.F.E := fun heS =>
        hBU1.1 ((compLSF_RF_isRSF hI).2.2.2.2.2.1 ((compLSFBatch_decremental hI hBUq).1 (hFeq.2.1 ▸ heS)))
      have heM : e ∉ M := fun h => hBU1.1 (hMG h)
      have hek : e ∉ keep := fun h => heM (hkM h)
      obtain ⟨hevI, _, hMI, hKI, hpotI⟩ := tourStep_quiet_insert_sync hRep.valid hw1.2.1 hw1.1 hw2.1
        hBU1.1 heF (hVeq.symm ▸ hBU1.2.1) (hVeq.symm ▸ hBU1.2.2) hOrdG
        (fun y hy => hw1.2.2 y (Option.mem_def.mpr hy)) (fun y hy => hw2.2.2 y (Option.mem_def.mpr hy)) hM hK heM hek
      set rTag := Function.update st.regs 16 0
      obtain ⟨hNext, st1, cIns, tx1, hrunIns, hr9_1, hregs1, hrep1, hhLo1, hhHi1, hzero1, hfr1, hft1, hcost1⟩ :=
        tourBlock_case_insert_runs (ω := ω) hpT hpC hw (st := { st with regs := rTag })
          (by simp [rTag, hr0]) (by simp [rTag, hr9]) (by simp [rTag, hr13])
          hRep hFoot hZero (by omega) hd1 hd2 hevI (by omega)
      have hregs1_le : ∀ r, r ≤ 15 → r ≠ 9 → st1.regs r = st.regs r := fun r hr h9 =>
        (hregs1 r h9 (by omega)).trans (Function.update_of_ne (by omega) _ _)
      obtain ⟨cIter, hrunIter, hcIter⟩ := tourBlock_iter_insert_wrap (bSelf := bSelf) (bOut := bOut)
        hwide (by omega) (by omega) (by simp at heIdxTot; omega) (by omega) hr12 hr13 hr14 hr15
        (hListU 0 (by simp)) hrunIns hregs1_le
      set r15 := Function.update (Function.update (Function.update (Function.update st1.regs 12 (uPtr + 4))
        13 (ePtr + 8)) 14 (eIdx + 2)) 15 (i + 1)
      obtain ⟨hfoot1, hBF1, hEF1, hSF1, hStF1⟩ := tourLoop_foot_transport (by omega) (by omega)
        hedLe (by omega) (by omega) hFoot hBF hEF hSF hStF hft1
      have hDec1 := decodeOrdEdits_shift (mem := st.mem) (mem' := st1.mem) ed_rest.length (ePtr + 8) (ePtr + 8)
        (fun k hk => hfr1 _ (by omega) (hEF _ (by omega) (by omega)))
      have hPre1 := outSplitPrefixAt_mono
        (avoid' := fun x => (tourAsmRep vCap eCap).foot tourH tx1 x ∨ x < statePtr + 3)
        hPre (by omega : hCur ≤ hNext)
        (fun x hx hna h2 => h2.elim (fun hf => (hft1 x hf).elim (fun h0 => hna (Or.inl h0)) (fun h => by omega)) (fun hex => hna (Or.inr hex)))
        (fun x hx hna => hfr1 x hx (fun hf => hna (Or.inl hf)))
      have hsq_wall : compLSFBatch cs (splitQuietPrefix cs (.insert e a b :: U_rest)).1 =
          compLSFBatch cs1 (splitQuietPrefix cs1 U_rest).1 := by rw [hsq]; rfl
      have hsq_w2 : (splitQuietPrefix cs (.insert e a b :: U_rest)).2 = (splitQuietPrefix cs1 U_rest).2 := by rw [hsq]
      rw [hsq_wall] at hFeq hReq hMdisj; rw [hsq_wall, hsq_w2] at hDrop hRoom
      have hStM1 : st1.mem statePtr = spIdx ∧ st1.mem (statePtr + 1) = splitPtr ∧ st1.mem (statePtr + 2) = last :=
        ⟨(hfr1 statePtr (by omega) (by have := hStF 0 (by decide); rwa [Nat.add_zero] at this)).trans hStM.1,
         (hfr1 (statePtr + 1) (by omega) (hStF 1 (by decide))).trans hStM.2.1,
         (hfr1 (statePtr + 2) (by omega) (hStF 2 (by decide))).trans hStM.2.2⟩
      obtain ⟨hEnd, stF, cRest, txF, splitPtrF, lastF, ePtrF, sEnd, MEnd, SEnd, YsLoop, hrunRest,
        hR0F, hR4F, hR6F, hR7F, hR8F, hR9F, hR13F, hR14F, hR15F, hePtrLo, hePtrHi, hDecF, hSumF,
        hStF0, hStF1', hStF2', hRepF, hOrdF, hFeqF, hReqF, hOVFF, hMF, hkMF, hMsubF, hKF,
        hPreF, hPotF, hhLoF, hhHiF, hZeroF, hFrF, hFtF, hCostF⟩ :=
        ih cs1 ed_rest (uPtr + 4) (uWordsRem - 4) (ePtr + 8) (eWordsRem - 8) (eIdx + 2) (i + 1)
          spIdx splitPtr last hNext
          (tourApplyEdits s [.insertBefore a (e, true) y₁, .insertBefore b (e, false) y₂])
          tx1 { st1 with regs := r15 } M S_cur P_done Ys_done
          (by simp [r15, hregs1_le 0 (by decide) (by decide), hr0]) (by simp [r15, hregs1_le 1 (by decide) (by decide), hr1])
          (by simp [r15, hregs1_le 2 (by decide) (by decide), hr2]) (by simp [r15, hregs1_le 3 (by decide) (by decide), hr3])
          (by simp [r15, hregs1_le 4 (by decide) (by decide), hr4]) (by simp [r15, hregs1_le 5 (by decide) (by decide), hr5])
          (by simp [r15, hregs1_le 6 (by decide) (by decide), hr6]) (by simp [r15, hregs1_le 7 (by decide) (by decide), hr7])
          (by simp [r15, hregs1_le 8 (by decide) (by decide), hr8]) (by simp [r15, hr9_1])
          (by simp [r15, hregs1_le 10 (by decide) (by decide), hr10]) (by simp [r15, hregs1_le 11 (by decide) (by decide), hr11])
          (by simp [r15]) (by simp [r15]) (by simp [r15]) (by simp [r15])
          (by simp at hiLen; omega) (by omega) (by omega) (by omega) (by omega) (by omega) hordH
          (by simp at heIdxTot; omega) hI1 hBUrest hRlt1 (hG1.symm ▸ hOFB_rest) hOVF_rest
          (batchBodyAt_congr (hG1.symm ▸ hBBRest) (fun x hx1 hx2 => hfr1 x (by omega) (hBF x (by omega) (by omega))))
          hBF1 hEF1 hSF1 hStF1 (hDec1.symm ▸ hDecRest) (by rw [hDec1, hSumRest])
          (asmFirstSplitEntriesAt_congr hSpAt (fun x hx1 hx2 => hfr1 x (by omega) (hSF x hx1 hx2)))
          hStM1 hLastGe hSpLe hDrop hrep1 hfoot1 hzero1
          (by rw [hG1]; exact ordG_step_insert hOrdG hBU1.1) hFeq hReq hMI hkM hME₀
          (by rw [hG1]; exact Finset.Subset.trans hMG (Finset.subset_insert _ _))
          hMdisj hKdisj1 hKI hPre1 (by omega)
      have hloopAll := (runs_loop_iff (w := w) (p := p) (ω := ω)).mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond1, by decide, hrunIter, hrunRest, rfl⟩))
      refine ⟨hEnd, stF, _, txF, splitPtrF, lastF, ePtrF, sEnd, MEnd, SEnd, YsLoop, hloopAll,
        hR0F, hR4F, hR6F, hR7F, hR8F, hR9F, hR13F, by simpa [batchEditBlocksLen, updateEditBlockLen, Nat.add_assoc] using hR14F,
        hR15F, by omega, hePtrHi, by simpa [batchEditBlocksLen, updateEditBlockLen, Nat.add_comm] using hDecF,
        by simpa [batchEditBlocksLen, updateEditBlockLen, Nat.add_comm] using hSumF,
        by simpa [hsq_wall, hsq_w2] using hStF0, hStF1', hStF2', hRepF,
        by simpa [batchEditBlocksLen, updateEditBlockLen, applyOrdEdits, tourApplyEdits, tourApplyEdit, Nat.add_comm 2, List.take_succ_cons] using hOrdF,
        by simpa [compLSFBatch, cs1] using hFeqF, by simpa [compLSFBatch, cs1] using hReqF,
        by simpa [batchEditBlocksLen, updateEditBlockLen, Nat.add_comm] using hOVFF,
        hMF, hkMF, hMsubF, hKF, by simpa [hsq_wall, hsq_w2] using hPreF, by simpa [hsq_wall, hsq_w2, hpotI] using hPotF,
        by omega, by simpa [hsq_wall, hsq_w2] using (by omega : hEnd ≤ hCur + 159 * (uWordsRem + (ePtrF - ePtr)) + _), hZeroF,
        fun x hx hnf hstO hnl => (hFrF x (by omega) (fun hf => (hft1 x hf).elim hnf fun h => by omega) hstO hnl).trans (hfr1 x hx hnf),
        fun x hx => (hFtF x hx).elim (fun h1 => (hft1 x h1).elim Or.inl fun h => Or.inr ⟨h.1, by omega⟩) fun h => Or.inr ⟨by omega, h.2⟩, ?_⟩
      simp only [hsq_wall, hsq_w2, Expr.size]
      set R_rem := (YsLoop.map List.length).sum +
        (canonSplitList (compLSFBatch cs1 (splitQuietPrefix cs1 U_rest).1) (splitQuietPrefix cs1 U_rest).2).length +
        (uWordsRem - 4) + (ePtrF - (ePtr + 8))
      have htot_eq : (YsLoop.map List.length).sum + (canonSplitList (compLSFBatch cs1 (splitQuietPrefix cs1 U_rest).1)
          (splitQuietPrefix cs1 U_rest).2).length + uWordsRem + (ePtrF - ePtr) = R_rem + 12 := by dsimp only [R_rem]; clear * - huLenLe h8le hePtrLo; omega
      rw [htot_eq]
      have hov : 100 ≤ 150 * 12 * ordStoreLog eCap := le_trans (by omega) (Nat.le_mul_of_pos_right _ htl)
      have hstep : tourBlockCaseMul * 12 * ordStoreLog eCap + 150 * 12 * ordStoreLog eCap = tourBlockLoopMul * 12 * ordStoreLog eCap := by
        rw [tourBlockLoopMul_eq, tourBlockLoopMulFn_eq, ← Nat.add_mul, ← Nat.add_mul]
      have hadd : tourBlockLoopMul * (R_rem + 12) * ordStoreLog eCap =
          tourBlockLoopMul * R_rem * ordStoreLog eCap + tourBlockLoopMul * 12 * ordStoreLog eCap := by rw [Nat.mul_add, Nat.add_mul]
      have hp0 : (tourAsmRep vCap eCap).phi tourH tx { st with regs := rTag }.mem = (tourAsmRep vCap eCap).phi tourH tx st.mem := rfl
      have hp1 : (tourAsmRep vCap eCap).phi tourH tx1 { st1 with regs := r15 }.mem = (tourAsmRep vCap eCap).phi tourH tx1 st1.mem := rfl
      clear * - hcost1 hcIter hCostF hov hstep hadd hp0 hp1; omega
    | delete e =>
      obtain ⟨rfl, hListU⟩ := hUAt
      obtain ⟨ed_rest, rfl, hOFB_rest⟩ := ordEditsForBatch_delete_iff.mp hOFB
      obtain ⟨hWin1, hOVF_rest⟩ := ordEditsValidFor_cons hOVF
      have heLt : e < eCap := hWin1 _ List.mem_cons_self
      have hDec0 : (decodeOrdEdits st.mem ed_rest.length (ePtr + 2)).1 = ed_rest ∧
          (decodeOrdEdits st.mem ed_rest.length (ePtr + 2)).2.sum = eWordsRem - 2 ∧
          2 ≤ eWordsRem := by
        simp only [List.length_cons, decodeOrdEdits, List.cons.injEq, List.sum_cons] at hDec hSum
        have hi1 := decodeOrdEdit_dropEdge_info hDec.1
        rw [hi1.2.2] at hDec hSum; exact ⟨hDec.2, by omega, by omega⟩
      obtain ⟨hDecRest, hSumRest, h2le⟩ := hDec0
      have hek : e ∉ keep := fun hk =>
        Finset.disjoint_left.mp hKdisj hk ((mem_batchDeletes_iff _ _).mpr ⟨.delete e, List.mem_cons_self, rfl⟩)
      have heOrd : (e, true) ∈ s.ord (cs.G.tail e) := (hOrdG _ _).mpr ⟨hBU1, rfl⟩
      have hBUq : cs.G.BatchIsValid (splitQuietPrefix cs (.delete e :: U_rest)).1 := by
        rw [← splitQuietPrefix_append cs (.delete e :: U_rest)] at hBU
        exact (batchIsValid_append.mp hBU).1
      have hVeq : s.rf.F.V = cs.G.V :=
        hFeq.1.trans ((compLSF_RF_isRSF (compLSFBatch_inv hI hBUq)).2.1.trans
          (quietPrefix_G_V_eq _ cs hI hBUq (splitQuietPrefix_all_quiet cs _)))
      have htailLt : cs.G.tail e < vCap := hRep.valid.verts_lt _ (hVeq.symm ▸ (hI.hG_val e hBU1).1)
      set r21 := Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update st.regs 16 1) 17 e) 18 (nodeOfEndBase tourH vCap))
        19 (tx.nodeOf (2 * e))) 20 (nodesBase tourH vCap eCap)) 21 (if e ∉ s.rf.F.E then 1 else 0)
      by_cases heCs : e ∈ cs.RF.F.E
      · -- Wall forest delete (`isOp = 0`)
        have hnq : isQuietUpdate cs (.delete e) = false := by simp [isQuietUpdate, heCs]
        have hsq : splitQuietPrefix cs (.delete e :: U_rest) = ([], .delete e :: U_rest) := by
          simp [splitQuietPrefix, hnq]
        rw [hsq] at hFeq hReq hMdisj hDrop hRoom
        simp only [compLSFBatch, List.foldl_nil] at hFeq hReq hMdisj hDrop hRoom
        have heS : e ∈ s.rf.F.E := hFeq.2.1.symm ▸ heCs
        have heM : e ∉ M := Finset.disjoint_right.mp hMdisj heCs
        obtain ⟨hMidRSF, hMidF, hfrNot, hMidR, hMidRsub⟩ := inputMid_wall_props hI hBU1 hnq
        set mid := inputMid cs (.delete e)
        set kept := cs.RF.root (cs.RF.F.tail e)
        set fresh := newRoot mid.F.R cs.RF.R
        have hkept_eq : kept = s.rf.root (s.rf.F.tail e) := by
          rw [(hFeq.2.2 e heS).1]; exact (graphEq_root_eq hFeq hReq).symm
        have hfrLt : fresh < vCap :=
          hRlt1 fresh ((compLSFBatch_decremental hI1 hBUrest).2 (hMidRsub (hMidR ▸ Finset.mem_insert_self _ _)))
        have hfrV : fresh ∈ s.rf.F.V := by
          rw [hFeq.1, (compLSF_RF_isRSF hI).2.1]
          have := hMidRSF.2.2.1 (hMidR ▸ Finset.mem_insert_self _ _); rwa [hG1] at this
        have hfrNotR : fresh ∉ s.rf.R := hReq ▸ hfrNot
        have hKeq : GraphEq (eraseForestEdge s.rf.F e) mid.F.F := by
          rw [hMidF]; exact graphEq_eraseForestEdge hFeq e
        have huniq' : ∀ v ∈ s.rf.F.V,
            ∃! r, r ∈ insert fresh s.rf.R ∧ (eraseForestEdge s.rf.F e).Connected v r := fun v hvV => by
          have hvG : v ∈ cs1.G.V := by rw [hG1]; exact (compLSF_RF_isRSF hI).2.1 ▸ hFeq.1 ▸ hvV
          obtain ⟨r, ⟨hrR, hvr⟩, hru⟩ := hMidRSF.2.2.2.1 v hvG
          refine ⟨r, ⟨by rwa [hReq, ← hMidR], (graphEq_connected_iff hKeq).mpr hvr⟩,
            fun r' ⟨hr'R, hvr'⟩ => hru r' ⟨by rwa [hMidR, ← hReq], (graphEq_connected_iff hKeq).mp hvr'⟩⟩
        set St := (coreGraph cs.G cs.lsf).E.filter fun x => (coreGraph (cs.G.applyUpdate (.delete e)) mid).tail x = fresh
        set Sh := (coreGraph cs.G cs.lsf).E.filter fun x => (coreGraph (cs.G.applyUpdate (.delete e)) mid).head x = fresh
        have hSt : ∀ f ∈ keep, f ∈ St ↔ (tourCut s e fresh).rf.root (ordSrc s.ord (f, true)) = fresh := fun f hf => by
          have hfG := hMG (hkM hf); have ht : (f, true) ∈ s.ord (cs.G.tail f) := (hOrdG _ _).mpr ⟨hfG, rfl⟩
          have hfc : f ∈ (coreGraph cs.G cs.lsf).E := Finset.mem_sdiff.mpr ⟨hfG, Finset.disjoint_left.mp hMdisj (hkM hf)⟩
          simp only [St, Finset.mem_filter, hfc, true_and]
          change mid.F.root (cs.G.tail f) = fresh ↔ (tourCut s e fresh).rf.root (ordSrc s.ord (f, true)) = fresh
          rw [hRep.valid.compat.ordSrc_eq ht, ← graphEq_root_eq (rf₁ := (tourCut s e fresh).rf) (rf₂ := mid.F) hKeq (by change insert fresh s.rf.R = mid.F.R; rw [hReq, hMidR])]
        have hSh : ∀ f ∈ keep, f ∈ Sh ↔ (tourCut s e fresh).rf.root (ordSrc s.ord (f, false)) = fresh := fun f hf => by
          have hfG := hMG (hkM hf); have hh : (f, false) ∈ s.ord (cs.G.head f) := (hOrdG _ _).mpr ⟨hfG, rfl⟩
          have hfc : f ∈ (coreGraph cs.G cs.lsf).E := Finset.mem_sdiff.mpr ⟨hfG, Finset.disjoint_left.mp hMdisj (hkM hf)⟩
          simp only [Sh, Finset.mem_filter, hfc, true_and]
          change mid.F.root (cs.G.head f) = fresh ↔ (tourCut s e fresh).rf.root (ordSrc s.ord (f, false)) = fresh
          rw [hRep.valid.compat.ordSrc_eq hh, ← graphEq_root_eq (rf₁ := (tourCut s e fresh).rf) (rf₂ := mid.F) hKeq (by change insert fresh s.rf.R = mid.F.R; rw [hReq, hMidR])]
        obtain ⟨_, hvWall, hMWall, hKWall, _, _, _⟩ :=
          tourStep_wall_forestDelete_sync hRep.valid heLt hM hK heS heM hek hkept_eq hfrV hfrNotR huniq' hSt hSh
        have hM1G : M ⊆ cs1.G.E := by
          rw [hG1]; exact fun f hf => Finset.mem_erase.mpr ⟨fun h => heM (h ▸ hf), hMG hf⟩
        obtain ⟨sNext, SNext, hChain, hOrdN, _, hFeqN, hReqN, _, _, _, hMdisjN⟩ :=
          wallStep_tailChain hI hBU hnq hRlt hvWall hKeq
            (by change insert fresh s.rf.R = mid.F.R; rw [hReq, hMidR])
            hMWall hMdisj hKWall hKdisj1 (by rw [hG1]; exact ordG_step_delete hOrdG) (fun f hf => hM1G (hkM hf))
        set cuts := ((forestAfterInput cs.RF.F (.delete e)).E \ cs1.RF.F.E).sort (· ≤ ·)
        set Uq1 := (splitQuietPrefix cs1 U_rest).1; set Uwall1 := (splitQuietPrefix cs1 U_rest).2
        set cs_wall1 := compLSFBatch cs1 Uq1; set spRest := canonSplitList cs_wall1 Uwall1
        set relL := releasesSplitEntries cs1.RF.R mid cuts ++ canonSplitList cs1 Uq1
        have hSpDecomp : canonSplitList cs (.delete e :: U_rest) = ⟨false, 0, kept, fresh⟩ :: relL ++ spRest := by
          simp only [canonSplitList, canonStepSplits, inputSplitEntries,
            heCs, ↓reduceIte, List.cons_append, List.nil_append, relL, spRest, cs1, mid, kept, fresh, cuts]
          rw [← splitQuietPrefix_append cs1 U_rest, asmFirstCanonSplitList_append, List.append_assoc]
        have hPsDecomp : restrictSplits keep (canonCoreBatch cs (.delete e :: U_rest)) =
            .split kept fresh (St ∩ keep) (Sh ∩ keep) ::
              (restrictSplits keep (releasesBatch cs1.G cs1.RF.R mid cuts) ++
               restrictSplits keep (canonCoreBatch cs1 Uq1)) ++
              restrictSplits keep (canonCoreBatch cs_wall1 Uwall1) := by
          simp only [canonCoreBatch, canonStepCore, inputCoreBatch, heCs, ↓reduceIte, refineSplit,
            restrictSplits_append, restrictSplits, cs1, mid, kept, fresh, cuts, St, Sh, hG1]
          rw [← splitQuietPrefix_append cs1 U_rest, canonCoreBatch_append, restrictSplits_append]
          simp only [List.cons_append, List.append_assoc]; rfl
        have hlenS : (canonSplitList cs (.delete e :: U_rest)).length = 1 + relL.length + spRest.length := by
          rw [hSpDecomp]; simp; omega
        have hspIdx_lt : spIdx < L.length := by
          have h1 : (L.drop spIdx).length = L.length - spIdx := List.length_drop
          rw [hDrop, hlenS] at h1; omega
        have hdrop' : L.drop spIdx = ⟨false, 0, kept, fresh⟩ :: relL ++ spRest := hDrop.trans hSpDecomp
        have hroomWall : hCur + 51 + (1 + relL.length) * tourSplitStepSpace eCap + 2 < 2 ^ w := by
          rw [hlenS, Nat.add_mul] at hRoom; omega
        obtain ⟨hNext, st1, cWall, tx1, spPtr1, last1, Yw, YsRel, hrunWall, hr9_1, hregs1,
          hrep1, hM1, hK1, hSt1_0, hSt1_1, hSt1_2, hLast1, hPre1, hPot1, hhLo1, hhHi1, hZero1, hFr1, hFt1, hCost1⟩ :=
          tourBlock_case_forestDel_runs (ω := ω) hpT hpO hpRel hw (st := { st with regs := r21 })
            (by simp [r21, hr0]) (by simp [r21, hr5]) (by simp [r21, hr7])
            (by simp [r21, hr9]) (by simp [r21, hr10]) (by simp [r21])
            hRep hFoot hZero hSpAt (by omega) hSF hStM (by omega) hStF hsp_disj_st
            (by rcases hLastGe with rfl | hl; exact Or.inl rfl; exact Or.inr (Or.inr (by omega)))
            (by rcases hLastGe with rfl | hl; exact Or.inl rfl; exact Or.inr (Or.inr (by omega)))
            hspIdx_lt hdrop' (splitQuietPrefix_snd_stop cs1 U_rest) heS heLt heM hek hkept_eq
            hfrLt hfrV hfrNotR huniq' hSt hSh hM hkM hME₀ hK hPre hChain hroomWall
        have hregs1_le : ∀ r, r ≤ 15 → r ≠ 9 → st1.regs r = st.regs r := fun r hr h9 => by
          rw [hregs1 r h9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
          simp only [r21]; repeat rw [Function.update_of_ne (by omega)]
        obtain ⟨cIter, hrunIter, hcIter⟩ := tourBlock_iter_delete_wrap (bSelf := bSelf) (bTour := bTour) (bOut := bOut) (bCopy := bCopy)
          hwide (by omega) (by omega) (by simp at heIdxTot; omega) (by omega) (by omega)
          hr0 hr12 hr13 hr14 hr15 (hListU 0 (by simp)) (hListU 1 (by simp)) hRep hFoot htailLt heOrd
          (show Runs w p ω (if (if e ∉ s.rf.F.E then 1 else 0) = 0 then _ else _) { st with regs := r21 } _ _ _ from by
            simp only [heS, not_true_eq_false, ↓reduceIte]; exact hrunWall) hregs1_le
        set r15 := Function.update (Function.update (Function.update (Function.update st1.regs 12 (uPtr + 2))
          13 (ePtr + 2)) 14 (eIdx + 1)) 15 (i + 1)
        obtain ⟨hfoot1, hBF1, hEF1, hSF1, hStF1⟩ := tourLoop_foot_transport (by omega) (by omega)
          hedLe (by omega) (by omega) hFoot hBF hEF hSF hStF hFt1
        have hDec1 := decodeOrdEdits_shift (mem := st.mem) (mem' := st1.mem) ed_rest.length (ePtr + 2) (ePtr + 2)
          (fun k hk => hFr1 _ (by omega) (hEF _ (by omega) (by omega)) (Or.inr (by omega))
            (by rcases hLastGe with rfl | hl; exact Or.inl rfl; exact Or.inr (by omega)))
        have hdrop1 : L.drop (spIdx + 1 + relL.length) = spRest := by
          have h1 : (L.drop spIdx).drop (1 + relL.length) = spRest := by
            rw [hdrop', show ⟨false, 0, kept, fresh⟩ :: relL ++ spRest =
              (⟨false, 0, kept, fresh⟩ :: relL) ++ spRest from rfl, List.drop_left' (by simp; omega)]
          simpa [List.drop_drop, Nat.add_assoc] using h1
        have hroomRest : hNext + 159 * (uWordsRem - 2 + (eWordsRem - 2)) + spRest.length * tourSplitStepSpace eCap + 4 < 2 ^ w := by
          rw [hlenS, Nat.add_mul] at hRoom; omega
        obtain ⟨hEnd, stF, cRest, txF, splitPtrF, lastF, ePtrF, sEnd, MEnd, SEnd, YsLoop, hrunRest,
          hR0F, hR4F, hR6F, hR7F, hR8F, hR9F, hR13F, hR14F, hR15F, hePtrLo, hePtrHi, hDecF, hSumF,
          hStF0, hStF1', hStF2', hRepF, hOrdF, hFeqF, hReqF, hOVFF, hMF, hkMF, hMsubF, hKF,
          hPreF, hPotF, hhLoF, hhHiF, hZeroF, hFrF, hFtF, hCostF⟩ :=
          ih cs1 ed_rest (uPtr + 2) (uWordsRem - 2) (ePtr + 2) (eWordsRem - 2) (eIdx + 1) (i + 1)
            (spIdx + 1 + relL.length) spPtr1 last1 hNext sNext tx1 { st1 with regs := r15 } M SNext
            (P_done ++ .split kept fresh (St ∩ keep) (Sh ∩ keep) ::
              (restrictSplits keep (releasesBatch cs1.G cs1.RF.R mid cuts) ++
               restrictSplits keep (canonCoreBatch cs1 Uq1)))
            (Ys_done ++ Yw :: YsRel)
            (by simp [r15, hregs1_le 0 (by decide) (by decide), hr0]) (by simp [r15, hregs1_le 1 (by decide) (by decide), hr1])
            (by simp [r15, hregs1_le 2 (by decide) (by decide), hr2]) (by simp [r15, hregs1_le 3 (by decide) (by decide), hr3])
            (by simp [r15, hregs1_le 4 (by decide) (by decide), hr4]) (by simp [r15, hregs1_le 5 (by decide) (by decide), hr5])
            (by simp [r15, hregs1_le 6 (by decide) (by decide), hr6]) (by simp [r15, hregs1_le 7 (by decide) (by decide), hr7])
            (by simp [r15, hregs1_le 8 (by decide) (by decide), hr8]) (by simp [r15, hr9_1])
            (by simp [r15, hregs1_le 10 (by decide) (by decide), hr10]) (by simp [r15, hregs1_le 11 (by decide) (by decide), hr11])
            (by simp [r15]) (by simp [r15]) (by simp [r15]) (by simp [r15])
            (by simp at hiLen; omega) (by omega) (by omega) (by omega) (by omega) (by omega) hordH
            (by simp at heIdxTot; omega) hI1 hBUrest hRlt1 (hG1.symm ▸ hOFB_rest)
            (by rw [hOrdN]; exact hOVF_rest)
            (batchBodyAt_congr (hG1.symm ▸ hBBRest) (fun x hx1 hx2 => hFr1 x (by omega) (hBF x (by omega) (by omega)) (Or.inl (by omega))
              (by rcases hLastGe with rfl | hl; exact Or.inl rfl; exact Or.inr (by omega))))
            hBF1 hEF1 hSF1 hStF1 (hDec1.symm ▸ hDecRest) (by rw [hDec1, hSumRest])
            (asmFirstSplitEntriesAt_congr hSpAt (fun x hx1 hx2 => hFr1 x (by omega) (hSF x hx1 hx2) (Or.inl (by omega))
              (by rcases hLastGe with rfl | hl; exact Or.inl rfl; exact Or.inr (by omega))))
            ⟨hSt1_0, hSt1_1, hSt1_2⟩ (Or.inr (by omega))
            (by have h1 : (L.drop spIdx).length = L.length - spIdx := List.length_drop; rw [hDrop, hlenS] at h1; omega)
            hdrop1 hrep1 hfoot1 hZero1 (by rw [hOrdN, hG1]; exact ordG_step_delete hOrdG)
            hFeqN hReqN hM1 hkM hME₀ hM1G hMdisjN hKdisj1 hK1 hPre1 hroomRest
        have hloopAll := (runs_loop_iff (w := w) (p := p) (ω := ω)).mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond1, by decide, hrunIter, hrunRest, rfl⟩))
        have hspTot : hEnd ≤ hCur + 159 * (uWordsRem + (ePtrF - ePtr)) +
            (canonSplitList cs (.delete e :: U_rest)).length * tourSplitStepSpace eCap := by
          rw [hlenS, Nat.add_mul]; dsimp only [spRest, cs_wall1, Uq1, Uwall1]; clear * - hhHi1 hhHiF huLenLe hePtrLo; omega
        refine ⟨hEnd, stF, _, txF, splitPtrF, lastF, ePtrF, sEnd, MEnd, SEnd, Yw :: YsRel ++ YsLoop, hloopAll,
          hR0F, hR4F, hR6F, hR7F, hR8F, hR9F, hR13F, by simpa [batchEditBlocksLen, updateEditBlockLen, Nat.add_assoc] using hR14F,
          hR15F, by omega, hePtrHi, by simpa [batchEditBlocksLen, updateEditBlockLen, Nat.add_comm] using hDecF,
          by simpa [batchEditBlocksLen, updateEditBlockLen, Nat.add_comm] using hSumF,
          by rw [hsq]; simp only [compLSFBatch, List.foldl_nil]; rw [hlenS]; dsimp only [spRest, cs_wall1, Uq1, Uwall1]; omega, hStF1', hStF2', hRepF,
          by simpa [batchEditBlocksLen, updateEditBlockLen, applyOrdEdits, tourApplyEdit, tourCut, Nat.add_comm 1, List.take_succ_cons, hOrdN] using hOrdF,
          by simpa [compLSFBatch, cs1] using hFeqF, by simpa [compLSFBatch, cs1] using hReqF,
          by simpa [batchEditBlocksLen, updateEditBlockLen, Nat.add_comm] using hOVFF, hMF, hkMF, hMsubF, hKF,
          by rw [hsq]; simp only [compLSFBatch, List.foldl_nil]; rw [hPsDecomp]; simpa [List.append_assoc] using hPreF,
          ?_, by omega, by rw [hsq]; simpa [compLSFBatch] using hspTot, hZeroF,
          fun a ha hnf hstO hnl => (hFrF a (by omega) (fun hf => (hFt1 a hf).elim hnf fun h => by omega) hstO (Or.inr (by omega))).trans (hFr1 a ha hnf hstO hnl),
          fun a ha => (hFtF a ha).elim (fun h1 => (hFt1 a h1).elim Or.inl fun h => Or.inr ⟨h.1, by omega⟩) fun h => Or.inr ⟨by omega, h.2⟩, ?_⟩
        · rw [hsq]; simp only [compLSFBatch, List.foldl_nil]; rw [hPsDecomp, outBatchEnc_append]
          have hSnext : SNext = S_cur.applyBatch (.split kept fresh (St ∩ keep) (Sh ∩ keep) ::
              (restrictSplits keep (releasesBatch cs1.G cs1.RF.R mid cuts) ++ restrictSplits keep (canonCoreBatch cs1 Uq1))) := by
            rw [hPre1.1, hPre.1]; simp [MGraph.applyBatch, cs1, mid]
          rw [← hSnext]; simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append]
          dsimp only [cs1, mid, cs_wall1, Uwall1, Uq1] at hPot1 hPotF ⊢; clear * - hPot1 hPotF; omega
        · rw [hsq]; simp only [compLSFBatch, List.foldl_nil, Expr.size, List.map_cons, List.map_append, List.sum_cons, List.sum_append]
          set A := Yw.length + (YsRel.map List.length).sum + (1 + relL.length) + 4
          set B := (YsLoop.map List.length).sum + spRest.length + (uWordsRem - 2) + (ePtrF - (ePtr + 2))
          have htot : Yw.length + (YsRel.map List.length).sum + (YsLoop.map List.length).sum +
              (canonSplitList cs (.delete e :: U_rest)).length + uWordsRem + (ePtrF - ePtr) = A + B := by rw [hlenS]; dsimp only [A, B]; clear * - huLenLe h2le hePtrLo; omega
          rw [htot]
          have hov : 120 ≤ 150 * A * ordStoreLog eCap := le_trans (by omega) (Nat.le_mul_of_pos_right _ htl)
          have hstep : tourBlockCaseMul * A * ordStoreLog eCap + 150 * A * ordStoreLog eCap = tourBlockLoopMul * A * ordStoreLog eCap := by
            rw [tourBlockLoopMul_eq, tourBlockLoopMulFn_eq, ← Nat.add_mul, ← Nat.add_mul]
          have hadd : tourBlockLoopMul * (A + B) * ordStoreLog eCap =
              tourBlockLoopMul * A * ordStoreLog eCap + tourBlockLoopMul * B * ordStoreLog eCap := by rw [Nat.mul_add, Nat.add_mul]
          have hp0 : (tourAsmRep vCap eCap).phi tourH tx { st with regs := r21 }.mem = (tourAsmRep vCap eCap).phi tourH tx st.mem := rfl
          have hp1 : (tourAsmRep vCap eCap).phi tourH tx1 { st1 with regs := r15 }.mem = (tourAsmRep vCap eCap).phi tourH tx1 st1.mem := rfl
          clear * - hCost1 hcIter hCostF hov hstep hadd hp0 hp1; omega
      · -- Quiet non-forest delete (`isOp = 1`)
        have hq0 : isQuietUpdate cs (.delete e) = true := by simp [isQuietUpdate, heCs]
        have hsq : splitQuietPrefix cs (.delete e :: U_rest) =
            (.delete e :: (splitQuietPrefix cs1 U_rest).1, (splitQuietPrefix cs1 U_rest).2) := by
          simp [splitQuietPrefix, hq0, cs1]
        have heOpen : e ∉ s.rf.F.E := fun heS =>
          heCs ((compLSFBatch_decremental hI hBUq).1 (hFeq.2.1 ▸ heS))
        obtain ⟨hevD, _, hMD, hKD, hpotD⟩ := tourStep_quiet_delete_sync hRep.valid heLt heOpen hM hK hek
        obtain ⟨hNext, st1, cDrop, tx1, hrunDrop, hr9_1, hregs1, hrep1, hhLo1, hhHi1, hzero1, hfr1, hft1, hcost1⟩ :=
          tourBlock_case_nonForestDel_runs (ω := ω) hpT hw (st := { st with regs := r21 })
            (by simp [r21, hr0]) (by simp [r21, hr9]) (by simp [r21])
            hRep hFoot hZero hevD (by omega)
        have hregs1_le : ∀ r, r ≤ 15 → r ≠ 9 → st1.regs r = st.regs r := fun r hr h9 => by
          rw [hregs1 r h9]; simp only [r21]; repeat rw [Function.update_of_ne (by omega)]
        obtain ⟨cIter, hrunIter, hcIter⟩ := tourBlock_iter_delete_wrap (bSelf := bSelf) (bTour := bTour) (bOut := bOut) (bCopy := bCopy)
          hwide (by omega) (by omega) (by simp at heIdxTot; omega) (by omega) (by omega)
          hr0 hr12 hr13 hr14 hr15 (hListU 0 (by simp)) (hListU 1 (by simp)) hRep hFoot htailLt heOrd
          (show Runs w p ω (if (if e ∉ s.rf.F.E then 1 else 0) = 0 then _ else _) { st with regs := r21 } _ _ _ from by
            simp only [heOpen]; exact hrunDrop) hregs1_le
        set r15 := Function.update (Function.update (Function.update (Function.update st1.regs 12 (uPtr + 2))
          13 (ePtr + 2)) 14 (eIdx + 1)) 15 (i + 1)
        obtain ⟨hfoot1, hBF1, hEF1, hSF1, hStF1⟩ := tourLoop_foot_transport (by omega) (by omega)
          hedLe (by omega) (by omega) hFoot hBF hEF hSF hStF hft1
        have hDec1 := decodeOrdEdits_shift (mem := st.mem) (mem' := st1.mem) ed_rest.length (ePtr + 2) (ePtr + 2)
          (fun k hk => hfr1 _ (by omega) (hEF _ (by omega) (by omega)))
        have hPre1 := outSplitPrefixAt_mono
          (avoid' := fun a => (tourAsmRep vCap eCap).foot tourH tx1 a ∨ a < statePtr + 3)
          hPre (by omega : hCur ≤ hNext)
          (fun a ha hna h2 => h2.elim (fun hf => (hft1 a hf).elim (fun h0 => hna (Or.inl h0)) (fun h => by omega)) (fun hex => hna (Or.inr hex)))
          (fun a ha hna => hfr1 a ha (fun hf => hna (Or.inl hf)))
        have hsq_wall : compLSFBatch cs (splitQuietPrefix cs (.delete e :: U_rest)).1 =
            compLSFBatch cs1 (splitQuietPrefix cs1 U_rest).1 := by rw [hsq]; rfl
        have hsq_w2 : (splitQuietPrefix cs (.delete e :: U_rest)).2 = (splitQuietPrefix cs1 U_rest).2 := by rw [hsq]
        rw [hsq_wall] at hFeq hReq hMdisj; rw [hsq_wall, hsq_w2] at hDrop hRoom
        have hStM1 : st1.mem statePtr = spIdx ∧ st1.mem (statePtr + 1) = splitPtr ∧ st1.mem (statePtr + 2) = last :=
          ⟨(hfr1 statePtr (by omega) (by have := hStF 0 (by decide); rwa [Nat.add_zero] at this)).trans hStM.1,
           (hfr1 (statePtr + 1) (by omega) (hStF 1 (by decide))).trans hStM.2.1,
           (hfr1 (statePtr + 2) (by omega) (hStF 2 (by decide))).trans hStM.2.2⟩
        obtain ⟨hEnd, stF, cRest, txF, splitPtrF, lastF, ePtrF, sEnd, MEnd, SEnd, YsLoop, hrunRest,
          hR0F, hR4F, hR6F, hR7F, hR8F, hR9F, hR13F, hR14F, hR15F, hePtrLo, hePtrHi, hDecF, hSumF,
          hStF0, hStF1', hStF2', hRepF, hOrdF, hFeqF, hReqF, hOVFF, hMF, hkMF, hMsubF, hKF,
          hPreF, hPotF, hhLoF, hhHiF, hZeroF, hFrF, hFtF, hCostF⟩ :=
          ih cs1 ed_rest (uPtr + 2) (uWordsRem - 2) (ePtr + 2) (eWordsRem - 2) (eIdx + 1) (i + 1)
            spIdx splitPtr last hNext (tourApplyEdit s (.dropEdge e)) tx1 { st1 with regs := r15 }
            (M.erase e) S_cur P_done Ys_done
            (by simp [r15, hregs1_le 0 (by decide) (by decide), hr0]) (by simp [r15, hregs1_le 1 (by decide) (by decide), hr1])
            (by simp [r15, hregs1_le 2 (by decide) (by decide), hr2]) (by simp [r15, hregs1_le 3 (by decide) (by decide), hr3])
            (by simp [r15, hregs1_le 4 (by decide) (by decide), hr4]) (by simp [r15, hregs1_le 5 (by decide) (by decide), hr5])
            (by simp [r15, hregs1_le 6 (by decide) (by decide), hr6]) (by simp [r15, hregs1_le 7 (by decide) (by decide), hr7])
            (by simp [r15, hregs1_le 8 (by decide) (by decide), hr8]) (by simp [r15, hr9_1])
            (by simp [r15, hregs1_le 10 (by decide) (by decide), hr10]) (by simp [r15, hregs1_le 11 (by decide) (by decide), hr11])
            (by simp [r15]) (by simp [r15]) (by simp [r15]) (by simp [r15])
            (by simp at hiLen; omega) (by omega) (by omega) (by omega) (by omega) (by omega) hordH
            (by simp at heIdxTot; omega) hI1 hBUrest hRlt1 (hG1.symm ▸ hOFB_rest) hOVF_rest
            (batchBodyAt_congr (hG1.symm ▸ hBBRest) (fun x hx1 hx2 => hfr1 x (by omega) (hBF x (by omega) (by omega))))
            hBF1 hEF1 hSF1 hStF1 (hDec1.symm ▸ hDecRest) (by rw [hDec1, hSumRest])
            (asmFirstSplitEntriesAt_congr hSpAt (fun x hx1 hx2 => hfr1 x (by omega) (hSF x hx1 hx2)))
            hStM1 hLastGe hSpLe hDrop hrep1 hfoot1 hzero1
            (by rw [hG1]; exact ordG_step_delete hOrdG) hFeq hReq hMD
            (fun f hf => Finset.mem_erase.mpr ⟨fun h => hek (h ▸ hf), hkM hf⟩)
            (Finset.Subset.trans (Finset.erase_subset _ _) hME₀)
            (by rw [hG1]; exact Finset.erase_subset_erase _ hMG)
            (Disjoint.mono_left (Finset.erase_subset _ _) hMdisj) hKdisj1 hKD hPre1 (by omega)
        have hloopAll := (runs_loop_iff (w := w) (p := p) (ω := ω)).mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond1, by decide, hrunIter, hrunRest, rfl⟩))
        refine ⟨hEnd, stF, _, txF, splitPtrF, lastF, ePtrF, sEnd, MEnd, SEnd, YsLoop, hloopAll,
          hR0F, hR4F, hR6F, hR7F, hR8F, hR9F, hR13F, by simpa [batchEditBlocksLen, updateEditBlockLen, Nat.add_assoc] using hR14F,
          hR15F, by omega, hePtrHi, by simpa [batchEditBlocksLen, updateEditBlockLen, Nat.add_comm] using hDecF,
          by simpa [batchEditBlocksLen, updateEditBlockLen, Nat.add_comm] using hSumF,
          by simpa [hsq_wall, hsq_w2] using hStF0, hStF1', hStF2', hRepF,
          by simpa [batchEditBlocksLen, updateEditBlockLen, applyOrdEdits, tourApplyEdit, Nat.add_comm 1, List.take_succ_cons] using hOrdF,
          by simpa [compLSFBatch, cs1] using hFeqF, by simpa [compLSFBatch, cs1] using hReqF,
          by simpa [batchEditBlocksLen, updateEditBlockLen, Nat.add_comm] using hOVFF,
          hMF, hkMF, Finset.Subset.trans hMsubF (Finset.erase_subset _ _), hKF,
          by simpa [hsq_wall, hsq_w2] using hPreF,
          by rw [hsq_wall, hsq_w2]; exact le_trans hPotF (Nat.add_le_add_left hpotD _),
          by omega, by simpa [hsq_wall, hsq_w2] using (by omega : hEnd ≤ hCur + 159 * (uWordsRem + (ePtrF - ePtr)) + _), hZeroF,
          fun a ha hnf hstO hnl => (hFrF a (by omega) (fun hf => (hft1 a hf).elim hnf fun h => by omega) hstO hnl).trans (hfr1 a ha hnf),
          fun a ha => (hFtF a ha).elim (fun h1 => (hft1 a h1).elim Or.inl fun h => Or.inr ⟨h.1, by omega⟩) fun h => Or.inr ⟨by omega, h.2⟩, ?_⟩
        simp only [hsq_wall, hsq_w2, Expr.size]
        set R_rem := (YsLoop.map List.length).sum +
          (canonSplitList (compLSFBatch cs1 (splitQuietPrefix cs1 U_rest).1) (splitQuietPrefix cs1 U_rest).2).length +
          (uWordsRem - 2) + (ePtrF - (ePtr + 2))
        have htot_eq : (YsLoop.map List.length).sum + (canonSplitList (compLSFBatch cs1 (splitQuietPrefix cs1 U_rest).1)
            (splitQuietPrefix cs1 U_rest).2).length + uWordsRem + (ePtrF - ePtr) = R_rem + 4 := by dsimp only [R_rem]; clear * - huLenLe h2le hePtrLo; omega
        rw [htot_eq]
        have hc1_le : (4 * tourMul + 40) * ordStoreLog eCap + 120 ≤ tourBlockLoopMul * 4 * ordStoreLog eCap := by
          have h2 : 4 * tourMul + 160 ≤ tourBlockLoopMul * 4 := by
            rw [tourBlockLoopMul_eq, tourBlockLoopMulFn_eq, tourBlockCaseMul_eq, tourBlockCaseMulFn_eq]; omega
          have h3 := Nat.mul_le_mul_right (ordStoreLog eCap) h2
          rw [Nat.add_mul] at h3 ⊢; clear * - h3 htl; omega
        have hadd : tourBlockLoopMul * (R_rem + 4) * ordStoreLog eCap =
            tourBlockLoopMul * R_rem * ordStoreLog eCap + tourBlockLoopMul * 4 * ordStoreLog eCap := by rw [Nat.mul_add, Nat.add_mul]
        have hp0 : (tourAsmRep vCap eCap).phi tourH tx { st with regs := r21 }.mem = (tourAsmRep vCap eCap).phi tourH tx st.mem := rfl
        have hp1 : (tourAsmRep vCap eCap).phi tourH tx1 { st1 with regs := r15 }.mem = (tourAsmRep vCap eCap).phi tourH tx1 st1.mem := rfl
        clear * - hcost1 hcIter hCostF hc1_le hadd hp0 hp1; omega
    | split v v' St Sh =>
      obtain ⟨sel, cMove, ed_rest, rfl, hmov, hOFB_rest⟩ := ordEditsForBatch_split_iff.mp hOFB
      obtain ⟨hWin1, hOVF_rest⟩ := ordEditsValidFor_cons hOVF
      have hw1 : v < vCap ∧ v' < vCap ∧ ∀ x ∈ sel, x.1 < eCap := hWin1 _ List.mem_cons_self
      have hnq : isQuietUpdate cs (.split v v' St Sh) = false := rfl
      have hsq : splitQuietPrefix cs (.split v v' St Sh :: U_rest) = ([], .split v v' St Sh :: U_rest) := rfl
      rw [hsq] at hFeq hReq hMdisj hDrop hRoom
      simp only [compLSFBatch, List.foldl_nil] at hFeq hReq hMdisj hDrop hRoom
      have hUInfo : ∃ tag kt kh, (tag = 2 ∨ tag = 3) ∧ uLen = 5 + kt + kh ∧
          st.mem uPtr = tag ∧ st.mem (uPtr + 1) = v ∧ st.mem (uPtr + 2) = v' ∧
          st.mem (uPtr + 3) = kt ∧ st.mem (uPtr + 4) = kh := by
        rcases hUAt with ⟨Lt, Lh, _, _, _, _, huL, hL⟩ | ⟨Lt, Lh, _, _, _, _, huL, hL⟩
        · exact ⟨2, Lt.length, Lh.length, Or.inl rfl, huL,
            hL 0 (by simp), hL 1 (by simp), hL 2 (by simp), hL 3 (by simp), hL 4 (by simp)⟩
        · exact ⟨3, Lt.length, Lh.length, Or.inr rfl, huL,
            hL 0 (by simp), hL 1 (by simp), hL 2 (by simp), hL 3 (by simp), hL 4 (by simp)⟩
      obtain ⟨tagU, kt, kh, htagU, huLenEq, hmemTag, hmemV, hmemV', hmemKt, hmemKh⟩ := hUInfo
      set m := st.mem (ePtr + 3)
      have hDec0 : (st.mem ePtr = 1 ∨ st.mem ePtr = 2) ∧
          decodeOrdEdit st.mem ePtr = (.moveEnds v v' sel cMove, 4 + m) ∧
          (decodeOrdEdits st.mem ed_rest.length (ePtr + (4 + m))).1 = ed_rest ∧
          (decodeOrdEdits st.mem ed_rest.length (ePtr + (4 + m))).2.sum = eWordsRem - (4 + m) ∧
          4 + m ≤ eWordsRem := by
        simp only [List.length_cons, decodeOrdEdits, List.cons.injEq, List.sum_cons] at hDec hSum
        obtain ⟨ht12, hde⟩ := decodeOrdEdit_moveEnds_info hDec.1
        rw [show (decodeOrdEdit st.mem ePtr).2 = 4 + m from congrArg Prod.snd hde] at hDec hSum
        exact ⟨ht12, hde, hDec.2, by omega, by omega⟩
      obtain ⟨htagE, hdecE, hDecRest, hSumRest, h4mle⟩ := hDec0
      have hF0 := compLSF_RF_isRSF hI
      have hVeq : s.rf.F.V = cs.G.V := hFeq.1.trans hF0.2.1
      have hvv' : v ≠ v' := fun h => hBU1.2.1 (h ▸ hBU1.1)
      have hordv' : s.ord v' = [] := List.eq_nil_iff_forall_not_mem.mpr fun z hz => by
        obtain ⟨hzE, hzs⟩ := (hOrdG v' z).mp hz
        obtain ⟨f, fb⟩ := z; cases fb
        · exact hBU1.2.1 (hzs ▸ (hI.hG_val f hzE).2)
        · exact hBU1.2.1 (hzs ▸ (hI.hG_val f hzE).1)
      have hEdit : TourEditValid vCap eCap s (.moveEnds v v' sel cMove) :=
        ⟨hw1.1, hw1.2.1, hvv', hVeq.symm ▸ hBU1.1, fun h => hBU1.2.1 (hVeq ▸ h), hordv', hw1.2.2⟩
      have hvalid1 : TourValid vCap eCap (tourApplyEdit s (.moveEnds v v' sel cMove)) :=
        tourValid_applyEdit_moveEnds hRep.valid hEdit
      obtain ⟨hMidRSF, hMidF, hfrNot, hMidR, hMidRsub⟩ := inputMid_wall_props hI hBU1 hnq
      set mid := inputMid cs (.split v v' St Sh); set kept := cs.RF.root v; set fresh := newRoot mid.F.R cs.RF.R
      set s1 := tourApplyEdit s (.moveEnds v v' sel cMove); set rTmp := if v' ∈ s1.rf.R then v' else v; set sWall := tourChangeRoot s1 rTmp fresh
      have hkept_eq : kept = s.rf.root v := (graphEq_root_eq hFeq hReq).symm
      have hfrLt : fresh < vCap :=
        hRlt1 fresh ((compLSFBatch_decremental hI1 hBUrest).2 (hMidRsub (hMidR ▸ Finset.mem_insert_self _ _)))
      have hF1eq : GraphEq s1.rf.F mid.F.F := by
        rw [hMidF]; exact tourMove_forest_graphEq hFeq hF0.2.2.2.2 hOrdG hmov
      have hfrV : fresh ∈ s1.rf.F.V := by
        rw [hF1eq.1, hMidRSF.2.1]; exact hMidRSF.2.2.1 (hMidR ▸ Finset.mem_insert_self _ _)
      have hfrNotR : fresh ∉ s.rf.R := hReq ▸ hfrNot
      have huniq' : ∀ w' ∈ s1.rf.F.V, ∃! r, r ∈ insert fresh s.rf.R ∧ s1.rf.F.Connected w' r := fun w' hw' => by
        have hwG : w' ∈ cs1.G.V := hMidRSF.2.1 ▸ hF1eq.1 ▸ hw'
        obtain ⟨r, ⟨hrR, hwr⟩, hru⟩ := hMidRSF.2.2.2.1 w' hwG
        refine ⟨r, ⟨by rwa [hReq, ← hMidR], (graphEq_connected_iff hF1eq).mpr hwr⟩,
          fun r' ⟨hr'R, hwr'⟩ => hru r' ⟨by rwa [hMidR, ← hReq], (graphEq_connected_iff hF1eq).mp hwr'⟩⟩
      have hRwall_eq : sWall.rf.R = mid.F.R := by
        have hsync0 := tourMove_changeRoot_sync hRep.valid hvalid1 hEdit hM hK hkept_eq hfrLt hfrV hfrNotR huniq'
          (St := keep.filter fun f => sWall.rf.root (ordSrc s1.ord (f, true)) = fresh)
          (Sh := keep.filter fun f => sWall.rf.root (ordSrc s1.ord (f, false)) = fresh)
          (fun _ hf => by simp [hf, sWall, rTmp, s1]) (fun _ hf => by simp [hf, sWall, rTmp, s1])
        exact hsync0.2.2.2.1.trans (by rw [hReq, hMidR])
      have hordG1 : ∀ u x, x ∈ sWall.ord u ↔ x.1 ∈ cs1.G.E ∧ cs1.G.src x = u := by
        rw [hG1]; exact ordG_step_split hOrdG hBU1 hI.hG_val hmov
      set StC := (coreGraph cs.G cs.lsf).E.filter fun x => (coreGraph (cs.G.applyUpdate (.split v v' St Sh)) mid).tail x = fresh
      set ShC := (coreGraph cs.G cs.lsf).E.filter fun x => (coreGraph (cs.G.applyUpdate (.split v v' St Sh)) mid).head x = fresh
      have hSt : ∀ f ∈ keep, f ∈ StC ↔ sWall.rf.root (ordSrc s1.ord (f, true)) = fresh := fun f hf => by
        have hfG := hMG (hkM hf); have ht : (f, true) ∈ s1.ord (cs1.G.tail f) := (hordG1 _ _).mpr ⟨hG1 ▸ hfG, rfl⟩
        have hfc : f ∈ (coreGraph cs.G cs.lsf).E := Finset.mem_sdiff.mpr ⟨hfG, Finset.disjoint_left.mp hMdisj (hkM hf)⟩
        simp only [StC, Finset.mem_filter, hfc, true_and]
        change mid.F.root ((cs.G.applyUpdate (.split v v' St Sh)).tail f) = fresh ↔ sWall.rf.root (ordSrc s1.ord (f, true)) = fresh
        rw [← hG1, hvalid1.compat.ordSrc_eq ht, graphEq_root_eq (rf₁ := sWall.rf) (rf₂ := mid.F) hF1eq hRwall_eq]
      have hSh : ∀ f ∈ keep, f ∈ ShC ↔ sWall.rf.root (ordSrc s1.ord (f, false)) = fresh := fun f hf => by
        have hfG := hMG (hkM hf); have hh : (f, false) ∈ s1.ord (cs1.G.head f) := (hordG1 _ _).mpr ⟨hG1 ▸ hfG, rfl⟩
        have hfc : f ∈ (coreGraph cs.G cs.lsf).E := Finset.mem_sdiff.mpr ⟨hfG, Finset.disjoint_left.mp hMdisj (hkM hf)⟩
        simp only [ShC, Finset.mem_filter, hfc, true_and]
        change mid.F.root ((cs.G.applyUpdate (.split v v' St Sh)).head f) = fresh ↔ sWall.rf.root (ordSrc s1.ord (f, false)) = fresh
        rw [← hG1, hvalid1.compat.ordSrc_eq hh, graphEq_root_eq (rf₁ := sWall.rf) (rf₂ := mid.F) hF1eq hRwall_eq]
      obtain ⟨_, _, _, _, hvWall, hMWall, hKWall, _, _, _⟩ :=
        tourMove_changeRoot_sync hRep.valid hvalid1 hEdit hM hK hkept_eq hfrLt hfrV hfrNotR huniq' hSt hSh
      have hM1G : M ⊆ cs1.G.E := by rw [hG1]; exact hMG
      obtain ⟨sNext, SNext, hChain, hOrdN, _, hFeqN, hReqN, _, _, _, hMdisjN⟩ :=
        wallStep_tailChain hI hBU hnq hRlt hvWall hF1eq hRwall_eq hMWall hMdisj hKWall hKdisj1
          hordG1 (fun f hf => hM1G (hkM hf))
      set cuts := ((forestAfterInput cs.RF.F (.split v v' St Sh)).E \ cs1.RF.F.E).sort (· ≤ ·)
      set Uq1 := (splitQuietPrefix cs1 U_rest).1; set Uwall1 := (splitQuietPrefix cs1 U_rest).2
      set cs_wall1 := compLSFBatch cs1 Uq1; set spRest := canonSplitList cs_wall1 Uwall1
      set relL := releasesSplitEntries cs1.RF.R mid cuts ++ canonSplitList cs1 Uq1
      have hSpDecomp : canonSplitList cs (.split v v' St Sh :: U_rest) = ⟨false, 0, kept, fresh⟩ :: relL ++ spRest := by
        simp only [canonSplitList, canonStepSplits, inputSplitEntries,
          List.cons_append, List.nil_append, relL, spRest, cs1, mid, kept, fresh, cuts]
        rw [← splitQuietPrefix_append cs1 U_rest, asmFirstCanonSplitList_append, List.append_assoc]
      have hPsDecomp : restrictSplits keep (canonCoreBatch cs (.split v v' St Sh :: U_rest)) =
          .split kept fresh (StC ∩ keep) (ShC ∩ keep) ::
            (restrictSplits keep (releasesBatch cs1.G cs1.RF.R mid cuts) ++
             restrictSplits keep (canonCoreBatch cs1 Uq1)) ++
            restrictSplits keep (canonCoreBatch cs_wall1 Uwall1) := by
        simp only [canonCoreBatch, canonStepCore, inputCoreBatch, refineSplit,
          restrictSplits_append, restrictSplits, cs1, mid, kept, fresh, cuts, StC, ShC, hG1]
        rw [← splitQuietPrefix_append cs1 U_rest, canonCoreBatch_append, restrictSplits_append]
        simp only [List.cons_append, List.append_assoc]; rfl
      have hlenS : (canonSplitList cs (.split v v' St Sh :: U_rest)).length = 1 + relL.length + spRest.length := by
        rw [hSpDecomp]; simp; omega
      have hspIdx_lt : spIdx < L.length := by
        have h1 : (L.drop spIdx).length = L.length - spIdx := List.length_drop
        rw [hDrop, hlenS] at h1; omega
      have hdrop' : L.drop spIdx = ⟨false, 0, kept, fresh⟩ :: relL ++ spRest := hDrop.trans hSpDecomp
      have hroomWall : hCur + (13 * m + 77) + (1 + relL.length) * tourSplitStepSpace eCap + 2 < 2 ^ w := by
        rw [hlenS, Nat.add_mul] at hRoom; omega
      set r21 := Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update st.regs 16 tagU) 17 v) 18 v') 19 kt) 20 kh) 21 m
      obtain ⟨hNext, st1, cWall, tx1, spPtr1, last1, Yw, YsRel, hrunWall, hr9_1, hregs1,
        hrep1, hM1, hK1, hSt1_0, hSt1_1, hSt1_2, hLast1, hPre1, hPot1, hhLo1, hhHi1, hZero1, hFr1, hFt1, hCost1⟩ :=
        tourBlock_case_split_runs (ω := ω) hpT hpO hpRel hpMove hw (st := { st with regs := r21 })
          (by simp [r21, hr0]) (by simp [r21, hr5]) (by simp [r21, hr7]) (by simp [r21, hr9])
          (by simp [r21, hr10]) (by simp [r21, hr13]) (by simp [r21]) (by simp [r21])
          hRep hFoot hZero (by omega) (by omega) htagE hdecE hEdit hvalid1 hSpAt (by omega) hSF
          hStM (by omega) hStF hsp_disj_st
          (by rcases hLastGe with rfl | hl; exact Or.inl rfl; exact Or.inr (Or.inr (by omega)))
          (by rcases hLastGe with rfl | hl; exact Or.inl rfl; exact Or.inr (Or.inr (by omega)))
          hspIdx_lt hdrop' (splitQuietPrefix_snd_stop cs1 U_rest) hkept_eq hfrLt hfrV hfrNotR
          huniq' hSt hSh hM hkM hME₀ hK hPre hChain hroomWall
      have hregs1_le : ∀ r, r ≤ 21 → r ≠ 9 → st1.regs r = r21 r := fun r hr h9 =>
        hregs1 r h9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      obtain ⟨cIter, hrunIter, hcIter⟩ := tourBlock_iter_split_wrap (ω := ω) (bSelf := bSelf) (bTour := bTour) (bOut := bOut) (bCopy := bCopy)
        hwide (by omega) (by omega) (by simp at heIdxTot; omega) (by omega) htagU
        hr12 hr13 hr14 hr15 hmemTag hmemV hmemV' hmemKt hmemKh rfl hrunWall hregs1_le
      set r15 := Function.update (Function.update (Function.update (Function.update st1.regs 12 (uPtr + 5 + (kt + kh)))
        13 (ePtr + 4 + m)) 14 (eIdx + 1)) 15 (i + 1)
      obtain ⟨hfoot1, hBF1, hEF1, hSF1, hStF1⟩ := tourLoop_foot_transport (by omega) (by omega)
        hedLe (by omega) (by omega) hFoot hBF hEF hSF hStF hFt1
      have hDec1 := decodeOrdEdits_shift (mem := st.mem) (mem' := st1.mem) ed_rest.length (ePtr + (4 + m)) (ePtr + (4 + m))
        (fun k hk => hFr1 _ (by omega) (hEF _ (by omega) (by omega)) (Or.inr (by omega))
          (by rcases hLastGe with rfl | hl; exact Or.inl rfl; exact Or.inr (by omega)))
      have hdrop1 : L.drop (spIdx + 1 + relL.length) = spRest := by
        have h1 : (L.drop spIdx).drop (1 + relL.length) = spRest := by
          rw [hdrop', show ⟨false, 0, kept, fresh⟩ :: relL ++ spRest =
            (⟨false, 0, kept, fresh⟩ :: relL) ++ spRest from rfl, List.drop_left' (by simp; omega)]
        simpa [List.drop_drop, Nat.add_assoc] using h1
      have hroomRest : hNext + 159 * (uWordsRem - uLen + (eWordsRem - (4 + m))) +
          spRest.length * tourSplitStepSpace eCap + 4 < 2 ^ w := by
        rw [hlenS, Nat.add_mul] at hRoom; omega
      obtain ⟨hEnd, stF, cRest, txF, splitPtrF, lastF, ePtrF, sEnd, MEnd, SEnd, YsLoop, hrunRest,
        hR0F, hR4F, hR6F, hR7F, hR8F, hR9F, hR13F, hR14F, hR15F, hePtrLo, hePtrHi, hDecF, hSumF,
        hStF0, hStF1', hStF2', hRepF, hOrdF, hFeqF, hReqF, hOVFF, hMF, hkMF, hMsubF, hKF,
        hPreF, hPotF, hhLoF, hhHiF, hZeroF, hFrF, hFtF, hCostF⟩ :=
        ih cs1 ed_rest (uPtr + uLen) (uWordsRem - uLen) (ePtr + (4 + m)) (eWordsRem - (4 + m)) (eIdx + 1) (i + 1)
          (spIdx + 1 + relL.length) spPtr1 last1 hNext sNext tx1 { st1 with regs := r15 } M SNext
          (P_done ++ .split kept fresh (StC ∩ keep) (ShC ∩ keep) ::
            (restrictSplits keep (releasesBatch cs1.G cs1.RF.R mid cuts) ++
             restrictSplits keep (canonCoreBatch cs1 Uq1)))
          (Ys_done ++ Yw :: YsRel)
          (by simp [r15, hregs1_le 0 (by decide) (by decide), r21, hr0]) (by simp [r15, hregs1_le 1 (by decide) (by decide), r21, hr1])
          (by simp [r15, hregs1_le 2 (by decide) (by decide), r21, hr2]) (by simp [r15, hregs1_le 3 (by decide) (by decide), r21, hr3])
          (by simp [r15, hregs1_le 4 (by decide) (by decide), r21, hr4]) (by simp [r15, hregs1_le 5 (by decide) (by decide), r21, hr5])
          (by simp [r15, hregs1_le 6 (by decide) (by decide), r21, hr6]) (by simp [r15, hregs1_le 7 (by decide) (by decide), r21, hr7])
          (by simp [r15, hregs1_le 8 (by decide) (by decide), r21, hr8]) (by simp [r15, hr9_1])
          (by simp [r15, hregs1_le 10 (by decide) (by decide), r21, hr10]) (by simp [r15, hregs1_le 11 (by decide) (by decide), r21, hr11])
          (by simp [r15]; omega) (by simp [r15]; omega) (by simp [r15]) (by simp [r15])
          (by simp at hiLen; omega) (by omega) (by omega) (by omega) (by omega) (by omega) hordH
          (by simp at heIdxTot; omega) hI1 hBUrest hRlt1 (hG1.symm ▸ hOFB_rest)
          (by rw [hOrdN]; exact hOVF_rest)
          (batchBodyAt_congr (hG1.symm ▸ hBBRest) (fun x hx1 hx2 => hFr1 x (by omega) (hBF x (by omega) (by omega)) (Or.inl (by omega))
            (by rcases hLastGe with rfl | hl; exact Or.inl rfl; exact Or.inr (by omega))))
          hBF1 hEF1 hSF1 hStF1 (hDec1.symm ▸ hDecRest) (by rw [hDec1, hSumRest])
          (asmFirstSplitEntriesAt_congr hSpAt (fun x hx1 hx2 => hFr1 x (by omega) (hSF x hx1 hx2) (Or.inl (by omega))
            (by rcases hLastGe with rfl | hl; exact Or.inl rfl; exact Or.inr (by omega))))
          ⟨hSt1_0, hSt1_1, hSt1_2⟩ (Or.inr (by omega))
          (by have h1 : (L.drop spIdx).length = L.length - spIdx := List.length_drop; rw [hDrop, hlenS] at h1; omega)
          hdrop1 hrep1 hfoot1 hZero1 (by rw [hOrdN]; exact hordG1)
          hFeqN hReqN hM1 hkM hME₀ hM1G hMdisjN hKdisj1 hK1 hPre1 hroomRest
      have hloopAll := (runs_loop_iff (w := w) (p := p) (ω := ω)).mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond1, by decide, hrunIter, hrunRest, rfl⟩))
      have hspTot : hEnd ≤ hCur + 159 * (uWordsRem + (ePtrF - ePtr)) +
          (canonSplitList cs (.split v v' St Sh :: U_rest)).length * tourSplitStepSpace eCap := by
        rw [hlenS, Nat.add_mul]; dsimp only [spRest, cs_wall1, Uq1, Uwall1]; clear * - hhHi1 hhHiF huLenLe huLenEq h4mle hePtrLo; omega
      refine ⟨hEnd, stF, _, txF, splitPtrF, lastF, ePtrF, sEnd, MEnd, SEnd, Yw :: YsRel ++ YsLoop, hloopAll,
        hR0F, hR4F, hR6F, hR7F, hR8F, hR9F, hR13F, by simpa [batchEditBlocksLen, updateEditBlockLen, Nat.add_assoc] using hR14F,
        hR15F, by omega, hePtrHi, by simpa [batchEditBlocksLen, updateEditBlockLen, Nat.add_comm] using hDecF,
        by simpa [batchEditBlocksLen, updateEditBlockLen, Nat.add_comm] using hSumF,
        by rw [hsq]; simp only [compLSFBatch, List.foldl_nil]; rw [hlenS]; dsimp only [spRest, cs_wall1, Uq1, Uwall1]; omega, hStF1', hStF2', hRepF,
        by simpa [batchEditBlocksLen, updateEditBlockLen, applyOrdEdits, tourApplyEdit, tourChangeRoot, Nat.add_comm 1, List.take_succ_cons, hOrdN, sWall, s1] using hOrdF,
        by simpa [compLSFBatch, cs1] using hFeqF, by simpa [compLSFBatch, cs1] using hReqF,
        by simpa [batchEditBlocksLen, updateEditBlockLen, Nat.add_comm] using hOVFF, hMF, hkMF, hMsubF, hKF,
        by rw [hsq]; simp only [compLSFBatch, List.foldl_nil]; rw [hPsDecomp]; simpa [List.append_assoc] using hPreF,
        ?_, by omega, by rw [hsq]; simpa [compLSFBatch] using hspTot, hZeroF,
        fun a ha hnf hstO hnl => (hFrF a (by omega) (fun hf => (hFt1 a hf).elim hnf fun h => by omega) hstO (Or.inr (by omega))).trans (hFr1 a ha hnf hstO hnl),
        fun a ha => (hFtF a ha).elim (fun h1 => (hFt1 a h1).elim Or.inl fun h => Or.inr ⟨h.1, by omega⟩) fun h => Or.inr ⟨by omega, h.2⟩, ?_⟩
      · rw [hsq]; simp only [compLSFBatch, List.foldl_nil]; rw [hPsDecomp, outBatchEnc_append]
        have hSnext : SNext = S_cur.applyBatch (.split kept fresh (StC ∩ keep) (ShC ∩ keep) ::
            (restrictSplits keep (releasesBatch cs1.G cs1.RF.R mid cuts) ++ restrictSplits keep (canonCoreBatch cs1 Uq1))) := by
          rw [hPre1.1, hPre.1]; simp [MGraph.applyBatch, cs1, mid]
        rw [← hSnext]; simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append]
        dsimp only [cs1, mid, cs_wall1, Uwall1, Uq1] at hPot1 hPotF ⊢; clear * - hPot1 hPotF; omega
      · rw [hsq]; simp only [compLSFBatch, List.foldl_nil, Expr.size, List.map_cons, List.map_append, List.sum_cons, List.sum_append]
        set A := Yw.length + (YsRel.map List.length).sum + (1 + relL.length) + (4 + m) + 5
        set B := (YsLoop.map List.length).sum + spRest.length + (uWordsRem - uLen) + (ePtrF - (ePtr + (4 + m)))
        have htot : A + B ≤ Yw.length + (YsRel.map List.length).sum + (YsLoop.map List.length).sum +
            (canonSplitList cs (.split v v' St Sh :: U_rest)).length + uWordsRem + (ePtrF - ePtr) := by rw [hlenS]; dsimp only [A, B]; clear * - huLenLe huLenEq h4mle hePtrLo; omega
        have hov : 120 ≤ 150 * A * ordStoreLog eCap := le_trans (by omega) (Nat.le_mul_of_pos_right _ htl)
        have hstep : tourBlockCaseMul * A * ordStoreLog eCap + 150 * A * ordStoreLog eCap = tourBlockLoopMul * A * ordStoreLog eCap := by
          rw [tourBlockLoopMul_eq, tourBlockLoopMulFn_eq, ← Nat.add_mul, ← Nat.add_mul]
        have hadd : tourBlockLoopMul * A * ordStoreLog eCap + tourBlockLoopMul * B * ordStoreLog eCap ≤
            tourBlockLoopMul * (Yw.length + (YsRel.map List.length).sum + (YsLoop.map List.length).sum +
              (canonSplitList cs (.split v v' St Sh :: U_rest)).length + uWordsRem + (ePtrF - ePtr)) *
              ordStoreLog eCap := by
          rw [← Nat.add_mul, ← Nat.mul_add]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ htot)
        have hp0 : (tourAsmRep vCap eCap).phi tourH tx { st with regs := r21 }.mem = (tourAsmRep vCap eCap).phi tourH tx st.mem := rfl
        have hp1 : (tourAsmRep vCap eCap).phi tourH tx1 { st1 with regs := r15 }.mem = (tourAsmRep vCap eCap).phi tourH tx1 st1.mem := rfl
        clear * - hCost1 hcIter hCostF hov hstep hadd hp0 hp1; omega

end

end MinCostFlow.SparseCore.Program
