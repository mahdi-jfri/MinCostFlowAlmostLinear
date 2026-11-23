module

public import MinCostFlow.SparseCore.Program.AssemblyFsCostP4Helpers

import MinCostFlow.SparseCore.Program.AssemblyFsCostSpanBank
import MinCostFlow.SparseCore.Program.AssemblyFirstWalkCharge
import MinCostFlow.SparseCore.Program.AssemblyFirstStepSideSpan
import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue11
import Mathlib.Tactic

/-!
# Phase 4 task-loop and spanner-bank bounds (`AssemblyFsCostP4Tasks`)

Proves the two task-loop bounds of Phase 4 from `AsmFsPre` and `AsmFsQ₄At`, with zero
`1 ≤ max impl.p_s impl.p_t` premise:

1. `400 * W_tot + 90 * D_tot + 90 * R_tot + 240 * UH_tot + specPhi P_sp (p4SpanAfter ...) ≤
   specPhi P_sp y'.spanS + spanCh`.
2. `(tasks.map fun t => p4TaskPay P_sp y'.spanS st₃.mem t).sum ≤
   spanCh + 9745 * encB + 340 * UH_tot + 170 * D_tot + (811 + 207 * depth) * R_tot + 584 * W_tot`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

public section

set_option maxHeartbeats 1600000 in
/-- **Phase 4 spanner-bank telescoping and `p4TaskPay` sum bound**. -/
theorem asmFsCost_p4_tasks_bounds {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {space : ℕ → ℕ}
    {A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth}
    {st₁ : State} {c₁ : ℕ} {st₂ : State} {c₂ : ℕ} {st₃ : State} {c₃ : ℕ}
    {o₄ : Outcome} {st₄ : State} {c₄ : ℕ}
    {hEnd₂ : ℕ} {y' : AsmBrSide scProgB5 depth} {tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ}
    {lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ} {hEnd₃ : ℕ}
    {tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} {splitPtr outDescPtr : ℕ}
    {mk' : Finset End} {Mset : Finset ℕ} {Ys : List (List End)} {touched : List ℕ}
    {qs : List (SpanUpdTask × P4TaskOut)} {ns : List (ℕ × List ℕ)}
    {x' : BucketSpannerMeta depth y'.cap} {yE : EmbConc}
    {tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} {Ld Li Lr T₀ : List ℕ}
    (hA : AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A)
    (hQ₄ : AsmFsQ₄At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE
      hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀) :
    let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify impl
    let ord' := applyOrdEdits A.ord A.ed
    let info := stepBundleTree sp A.tr A.U A.ord ord'
    let tr' := info.state
    let P_sp := asmBrSP impl w depth y'
    let tasks := p4TasksOf st₃.mem (outDescPtr + 1) touched.length
    let W_tot := (activePairs tr').sum fun q =>
      (updateReembSet (A.tr.dyn q) (info.U_B q) (canonicalSparsify impl)).sum fun e =>
        (piTotal (tr'.dyn q) e).length
    let D_tot := (activePairs tr').sum fun q =>
      (update (A.tr.dyn q) (info.U_B q) (canonicalSparsify impl)).D.card
    let R_tot := (activePairs tr').sum fun q =>
      (updateReembSet (A.tr.dyn q) (info.U_B q) (canonicalSparsify impl)).card
    let UH_tot := (activePairs tr').sum fun q =>
      (update (A.tr.dyn q) (info.U_B q) (canonicalSparsify impl)).UH.length
    let encB := (activePairs tr').sum fun q => (A.tr.dyn q).G.batchEnc (info.U_B q)
    let spanCh := (activePairs tr').sum fun q =>
      spanBatchChargeWith A.tr.spanConst A.tr.spanParams depth
        ((A.tr.initBunG q).n + A.tr.splitBound) (A.tr.initBunG q) (A.tr.dyn q).G (info.U_B q)
    (400 * W_tot + 90 * D_tot + 90 * R_tot + 240 * UH_tot +
        specPhi P_sp (p4SpanAfter P_sp y'.spanS st₃.mem tasks) ≤
      specPhi P_sp y'.spanS + spanCh) ∧
    ((tasks.map fun t => p4TaskPay P_sp y'.spanS st₃.mem t).sum ≤
      spanCh + 9745 * encB + 340 * UH_tot + 170 * D_tot +
        (811 + 207 * depth) * R_tot + 584 * W_tot) := by
  classical
  obtain ⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c,
    mem, pos, ω⟩ := A
  obtain ⟨vCap, eCap, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour, xT0,
    restH, xRest⟩ := x
  intro sp ord' info tr' P_sp tasks W_tot D_tot R_tot UH_tot encB spanCh
  obtain ⟨⟨hScanF, tx₀, hTx, hP2, hP3⟩, hP4⟩ := hQ₄
  unfold AsmFsPre AsmFsPreRaw at hA
  unfold AsmFsScanFacts at hScanF
  dsimp only [AsmFsArgs.newComps] at hA hScanF hP2 hP3 hP4 hTx
  obtain ⟨hM0, hN0, hL1, -, -, -, -, -, -, hR, -, hBat, hU, -, -, hOB, -, -, -, -, -, -, -,
    -, -, hfoot, -, -, -, -⟩ := hA
  obtain ⟨hRA, hv, he, -, -, -, -, -⟩ := hR
  dsimp only at hv he
  subst hv he
  obtain ⟨hM, -, -, -⟩ := hScanF
  obtain rfl : xT0 = tx₀ := (eq_of_heq hTx).symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTourRep, -, hSide, -,
    -, -, hDisj⟩ := hRA
  have hSide' := hSide
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMod⟩ := hSide'
  obtain ⟨hSMO, -, -, -, -, hk, ⟨C_lsst, ℓ₀, hI, -, -⟩, hSpanP, hSpanC, hSplitB0, -,
    -, -, -, -, -, -, -, hSlotInvOld, hInact, -, hInactDyn, hPart, hDynGOld, -,
    hMMax0, -, -⟩ := hMod
  have hTR_loc : ∀ v e, (TRc v e).Local := fun v e =>
    asmTourRepWithPot_local tourAsmRep_local (bundleScanPotMul tourBundleSpec) v e
  have hfootSide : ∀ a, asmSdFoot restH xRest a → a < h := fun a ha => hfoot a ⟨5, by decide, ha⟩
  have hfootT : ∀ a, (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a → a < h :=
    fun a ha => hfoot a ⟨4, by decide, ha⟩
  have hdisjST : ∀ a, asmSdFoot restH xRest a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a :=
    fun a hs ht => hDisj 5 (by decide) 4 (by decide) (by decide) a hs ht
  have hUW : 2 * U.length ≤ words - 1 := batchBodyAt_len_le hBat.1.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hset, -⟩ :=
    asmFirstStep_phase2_pre hTR_loc hSide hTourRep.2.2 hfootSide hfootT hdisjST hU hUW hM
  obtain ⟨-, -, -, -, -, hslc, -, -, hcap5, hsb, -, -, hmMax, -, -, -, -, -, -, -, hslots',
    hkeepSlot, hSlotN, hMatch, hspanS, hSlotInv, -⟩ := hP2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hnd3, -, -, hdesc3, hunt3, hnone3, -⟩ := hP3
  obtain ⟨hqs, hqsOK, hns, hnsOK, hRepX', -⟩ := hP4
  have hNew : ∀ C ∈ (List.map (fun q => xRest.comps.getD q.1 ∅) (scanBatchFold tr.cs.G
      (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps) U).newComps).toFinset,
      C ∈ components tr.cs.G₀ ∧ C ∉ tr.activeComps := by
    intro C hC; rw [hset] at hC
    exact ⟨touchedCompsBatch_subset _ _ (Finset.mem_sdiff.mp hC).1, (Finset.mem_sdiff.mp hC).2⟩
  have hSlot' : SlotMapOK { tr with activeComps := tr.activeComps ∪
      (List.map (fun q => xRest.comps.getD q.1 ∅) (scanBatchFold tr.cs.G (asmFirstScanStart mem
          xRest.cmpH xRest.comps tr.activeComps) U).newComps).toFinset } y'.slotCap y'.cap y'.slots
      y'.slotOf := by
    rw [hslc, hcap5]; exact hSlotN
  have hBReady := asmFirstStep_phase3_ready (ord' := ord') hI hk hU hOB hPart
    hInact hNew hSlot' hMatch hSlotInv.2.2.1
  have hDynGEq := p4_dynGraphEq (fun _ => canonicalSparsify impl) (U := U) (ord' := ord')
    hInact hInactDyn hDynGOld
  have hT := asmFirstStep_p4_slotTasks (P := P_sp) hset
    (fun q hq => by obtain ⟨hs, d, h1, h2, -⟩ := hspanS q hq; exact ⟨hs, d, h1, h2⟩)
    hSMO hSlotInvOld.2.1 hSlotN hslots' hkeepSlot hSlot' hMatch hSlotInv.2.2.1 hBReady
    hDynGEq hnd3 hdesc3 hunt3 hnone3
  have hAP := activePairs_mid_eq sp tr U ord ord' hset
  have hSlotData := p4Span_slotData hT
    (fun q hq => by obtain ⟨hs, d, h1, h2, h3, -⟩ := hspanS q (hAP ▸ hq); exact ⟨hs, d, h1, h2, h3⟩)
    hRepX'
  have hP_L : P_sp.L = depth := rfl
  have hP_splitB : P_sp.splitBound = tr.splitBound := hsb.trans hSplitB0
  have hSpanP' : SparsifyParamsLe (canonicalSparsifyParams P_sp.impl P_sp.mMax).absorbTime
      tr.spanParams := by
    change SparsifyParamsLe (canonicalSparsifyParams impl y'.mMax).absorbTime tr.spanParams
    rw [hmMax]; exact hSpanP
  have hCharge_le : ∀ q ∈ activePairs tr', ∀ (d₀ : DSHist),
      d₀.state P_sp = tr.dyn q → d₀.G₀ = tr.initBunG q →
      d₀.G₀.IsValid → d₀.G₀.m ≤ P_sp.mMax →
      d₀.G₀.BatchIsValid d₀.flat → (∀ u ∈ d₀.flat, isDelOrSplit u) →
      dsBatchCharge P_sp.impl P_sp.mMax P_sp.L (d₀.G₀.n + P_sp.splitBound) d₀.G₀
        (d₀.G₀.applyBatch d₀.flat) (info.U_B q) ≤
      spanBatchChargeWith tr.spanConst tr.spanParams depth
        ((tr.initBunG q).n + tr.splitBound) (tr.initBunG q) (tr.dyn q).G (info.U_B q) := by
    intro q _ d₀ hst₀ hG₀ hVG₀ hGm₀ hBV₀ hds₀
    rw [dsHist_applyBatch_eq_state_G P_sp d₀ hVG₀ hL1 hGm₀ hBV₀ hds₀, hst₀, hG₀, hP_splitB]
    exact dsBatchCharge_le_spanBatchChargeWith P_sp.impl P_sp.mMax depth
      ((tr.initBunG q).n + tr.splitBound) (tr.initBunG q) (tr.dyn q).G (info.U_B q)
      hSpanC hSpanP'
  constructor
  · -- Part 1: Bank + counts bound
    let fSlot : ∀ q ∈ activePairs tr', Fin y'.cap := fun q hq =>
      ⟨y'.slotOf q, (hSlotData q hq).choose⟩
    let S_act : Finset (Fin y'.cap) := (activePairs tr').attach.image fun q => fSlot q.1 q.2
    have hInj_act : Set.InjOn (fun q : { x // x ∈ activePairs tr' } => fSlot q.1 q.2)
        ↑(activePairs tr').attach := fun q₁ _ q₂ _ heq =>
      Subtype.ext (hT.hinj q₁.1 q₁.2 q₂.1 q₂.2 (congrArg Fin.val heq))
    let bBefore (j : Fin y'.cap) : ℕ := match y'.spanS j with | some d => d.bank P_sp | none => 0
    let bAfter (j : Fin y'.cap) : ℕ :=
      match p4SpanAfter P_sp y'.spanS st₃.mem tasks j with | some d => d.bank P_sp | none => 0
    have hOut : ∀ j : Fin y'.cap, j ∉ S_act → bAfter j = bBefore j := by
      intro j hj
      dsimp only [bAfter, bBefore]
      unfold p4SpanAfter
      rw [p4SpanAfter_unchanged P_sp y'.spanS st₃.mem]
      intro hmem
      obtain ⟨t, ht, hts⟩ := List.mem_map.mp hmem
      obtain ⟨q, hq, hqs', -⟩ := hT.htask t ht
      apply hj
      refine Finset.mem_image.mpr ⟨⟨q, hq⟩, Finset.mem_attach _ _, ?_⟩
      exact Fin.ext (hqs'.symm.trans hts)
    have hSplitB : specPhi P_sp y'.spanS = S_act.sum bBefore + (S_actᶜ : Finset _).sum bBefore :=
      (Finset.sum_add_sum_compl S_act bBefore).symm
    have hSplitA : specPhi P_sp (p4SpanAfter P_sp y'.spanS st₃.mem tasks) =
        S_act.sum bAfter + (S_actᶜ : Finset _).sum bAfter :=
      (Finset.sum_add_sum_compl S_act bAfter).symm
    have hCompl : (S_actᶜ : Finset _).sum bAfter = (S_actᶜ : Finset _).sum bBefore :=
      Finset.sum_congr rfl fun j hj => hOut j (Finset.mem_compl.mp hj)
    have hSact_le :
        400 * W_tot + 90 * D_tot + 90 * R_tot + 240 * UH_tot + S_act.sum bAfter ≤
        S_act.sum bBefore + spanCh := by
      rw [Finset.sum_image hInj_act, Finset.sum_image hInj_act]
      have hLHS : 400 * W_tot + 90 * D_tot + 90 * R_tot + 240 * UH_tot +
          (activePairs tr').attach.sum (fun q => bAfter (fSlot q.1 q.2)) =
          (activePairs tr').attach.sum fun q =>
            400 * ((updateReembSet (tr.dyn q.1) (info.U_B q.1) (canonicalSparsify impl)).sum
                fun e => (piTotal (tr'.dyn q.1) e).length) +
            90 * (update (tr.dyn q.1) (info.U_B q.1) (canonicalSparsify impl)).D.card +
            90 * (updateReembSet (tr.dyn q.1) (info.U_B q.1) (canonicalSparsify impl)).card +
            240 * (update (tr.dyn q.1) (info.U_B q.1) (canonicalSparsify impl)).UH.length +
            bAfter (fSlot q.1 q.2) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib]
        simp only [← Finset.mul_sum]
        rw [Finset.sum_attach (activePairs tr') (fun q =>
          (updateReembSet (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).sum fun e =>
            (piTotal (tr'.dyn q) e).length),
          Finset.sum_attach (activePairs tr') (fun q =>
            (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).D.card),
          Finset.sum_attach (activePairs tr') (fun q =>
            (updateReembSet (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).card),
          Finset.sum_attach (activePairs tr') (fun q =>
            (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).UH.length)]
      have hRHS : (activePairs tr').attach.sum (fun q => bBefore (fSlot q.1 q.2)) + spanCh =
          (activePairs tr').attach.sum fun q =>
            bBefore (fSlot q.1 q.2) +
            spanBatchChargeWith tr.spanConst tr.spanParams depth
              ((tr.initBunG q.1).n + tr.splitBound) (tr.initBunG q.1) (tr.dyn q.1).G
              (info.U_B q.1) := by
        rw [Finset.sum_add_distrib, Finset.sum_attach (activePairs tr') (fun q =>
          spanBatchChargeWith tr.spanConst tr.spanParams depth
            ((tr.initBunG q).n + tr.splitBound) (tr.initBunG q) (tr.dyn q).G (info.U_B q))]
      rw [hLHS, hRHS]
      refine Finset.sum_le_sum fun ⟨q, hq⟩ _ => ?_
      obtain ⟨d₀, hd₀, hst₀, hG₀, hEm, hNe⟩ := (hSlotData q hq).choose_spec
      by_cases hU0 : info.U_B q = []
      · obtain ⟨hpa, -⟩ := hEm hU0
        obtain ⟨hUH0, hD0, hR0⟩ := update_nil_counts (tr.dyn q) (canonicalSparsify impl)
        have hba : bAfter (fSlot q hq) = d₀.bank P_sp := by dsimp only [bAfter, fSlot]; rw [hpa]
        have hbb : bBefore (fSlot q hq) = d₀.bank P_sp := by dsimp only [bBefore, fSlot]; rw [hd₀]
        rw [hU0, hUH0, hD0, hR0, hba, hbb]
        simp
      · obtain ⟨hpa, hst1, hVG₀, hGm₀, hBV, hds, hsc, hp1⟩ := hNe hU0
        have hba : bAfter (fSlot q hq) = (⟨d₀.G₀, d₀.Us ++ [info.U_B q]⟩ : DSHist).bank P_sp := by
          dsimp only [bAfter, fSlot]
          change (match p4SpanAfter P_sp y'.spanS st₃.mem tasks ⟨y'.slotOf q, _⟩ with
            | some d => d.bank P_sp | none => 0) = _
          rw [hpa]; rfl
        have hbb : bBefore (fSlot q hq) = d₀.bank P_sp := by dsimp only [bBefore, fSlot]; rw [hd₀]
        rw [hba, hbb]
        have hbank := dsHist_walks_counts_bank_le P_sp d₀ (info.U_B q) hVG₀ hL1 hGm₀ hBV hds
          (by rw [batchSplitCount_append]; exact hsc) hp1
        have hBV₀ : d₀.G₀.BatchIsValid d₀.flat :=
          (MinCostFlow.DynSpanner.batchIsValid_append d₀.G₀ d₀.flat (info.U_B q)).mp hBV |>.1
        have hds₀ : ∀ u ∈ d₀.flat, isDelOrSplit u := fun u hu => hds u (List.mem_append_left _ hu)
        have hch := hCharge_le q hq d₀ hst₀ hG₀ hVG₀ hGm₀ hBV₀ hds₀
        dsimp only at hbank
        change (⟨d₀.G₀, d₀.Us ++ [info.U_B q]⟩ : DSHist).state P_sp = tr'.dyn q at hst1
        change 400 * ((updateReembSet (d₀.state P_sp) (info.U_B q) (canonicalSparsify impl)).sum
            fun e => (piTotal ((⟨d₀.G₀, d₀.Us ++ [info.U_B q]⟩ : DSHist).state P_sp) e).length) +
          90 * (update (d₀.state P_sp) (info.U_B q) (canonicalSparsify impl)).D.card +
          90 * (updateReembSet (d₀.state P_sp) (info.U_B q) (canonicalSparsify impl)).card +
          240 * (update (d₀.state P_sp) (info.U_B q) (canonicalSparsify impl)).UH.length +
          240 * (info.U_B q).length +
          (⟨d₀.G₀, d₀.Us ++ [info.U_B q]⟩ : DSHist).bank P_sp ≤ _ at hbank
        rw [hst₀, hst1] at hbank
        dsimp only
        have hbank' :
            400 * ((updateReembSet (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).sum
                fun e => (piTotal (tr'.dyn q) e).length) +
              90 * (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).D.card +
              90 * (updateReembSet (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).card +
              240 * (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).UH.length +
              (⟨d₀.G₀, d₀.Us ++ [info.U_B q]⟩ : DSHist).bank P_sp ≤
            d₀.bank P_sp +
              dsBatchCharge P_sp.impl P_sp.mMax P_sp.L (d₀.G₀.n + P_sp.splitBound)
                d₀.G₀ (d₀.G₀.applyBatch d₀.flat) (info.U_B q) :=
          le_trans (Nat.add_le_add_right (Nat.le_add_right _ (240 * (info.U_B q).length)) _) hbank
        exact le_trans hbank' (Nat.add_le_add_left hch _)
    rw [hSplitA, hSplitB, hCompl]; omega
  · -- Part 2: `p4TaskPay` sum bound
    let gPair (q : Finset ℕ × ℤ) : ℕ :=
      spanBatchChargeWith tr.spanConst tr.spanParams depth
        ((tr.initBunG q).n + tr.splitBound) (tr.initBunG q) (tr.dyn q).G (info.U_B q) +
      9745 * (tr.dyn q).G.batchEnc (info.U_B q) +
      340 * (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).UH.length +
      170 * (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).D.card +
      (811 + 207 * depth) *
        (updateReembSet (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).card +
      584 * ((updateReembSet (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).sum fun e =>
        (piTotal (tr'.dyn q) e).length)
    have hRHS_eq : (activePairs tr').sum gPair =
        spanCh + 9745 * encB + 340 * UH_tot + 170 * D_tot +
          (811 + 207 * depth) * R_tot + 584 * W_tot := by
      simp only [gPair, spanCh, encB, UH_tot, D_tot, R_tot, W_tot,
        Finset.sum_add_distrib, Finset.mul_sum]
    rw [← hRHS_eq]
    let φ (t : SpanUpdTask) : Option (Finset ℕ × ℤ) :=
      if h : ∃ q ∈ activePairs tr', t.slot = y'.slotOf q then some h.choose else none
    refine list_sum_le_finset_sum_of_pmap (activePairs tr')
      (fun t => p4TaskPay P_sp y'.spanS st₃.mem t) gPair φ tasks ?_ ?_
    · intro t ht
      obtain ⟨q, hq, hts, hbat⟩ := hT.htask t ht
      have hex : ∃ q' ∈ activePairs tr', t.slot = y'.slotOf q' := ⟨q, hq, hts⟩
      have hφ : φ t = some hex.choose := dite_eq_left hex
      have hq_eq : hex.choose = q :=
        hT.hinj _ hex.choose_spec.1 q hq (hex.choose_spec.2.symm.trans hts)
      rw [hφ, hq_eq]
      refine ⟨hq, ?_⟩
      obtain ⟨hs, d₀, hd₀, hst₀, hG₀, -, hNe⟩ := hSlotData q hq
      have hs' : t.slot < y'.cap := hts ▸ hs
      have hd₀' : y'.spanS ⟨t.slot, hs'⟩ = some d₀ := by
        rw [show (⟨t.slot, hs'⟩ : Fin y'.cap) = ⟨y'.slotOf q, hs⟩ from Fin.ext hts]; exact hd₀
      by_cases hnz : st₃.mem t.batchPtr = 0
      · unfold p4TaskPay; rw [p4OnTask_empty hs' hd₀' hnz]; exact Nat.zero_le _
      · obtain ⟨hdec, hzero⟩ := hbat hs' d₀ hd₀'
        change (decodeBatch st₃.mem t.batchPtr (d₀.state P_sp).G).1 = info.U_B q at hdec
        change st₃.mem t.batchPtr = 0 ↔ info.U_B q = [] at hzero
        have hne : info.U_B q ≠ [] := fun h0 => hnz (hzero.mpr h0)
        obtain ⟨-, hst1, hVG₀, hGm₀, hBV, hds, -, -⟩ := hNe hne
        have hBV₀ : d₀.G₀.BatchIsValid d₀.flat :=
          (MinCostFlow.DynSpanner.batchIsValid_append d₀.G₀ d₀.flat (info.U_B q)).mp hBV |>.1
        have hds₀ : ∀ u ∈ d₀.flat, isDelOrSplit u := fun u hu => hds u (List.mem_append_left _ hu)
        have htW : t.W ≤ 5 * (tr.dyn q).G.batchEnc (info.U_B q) + 1 := by
          obtain ⟨i, hi, rfl⟩ := mem_p4TasksOf ht
          obtain ⟨hs_bun, bp, tw, h0, h1, h2, -, -, hSB⟩ := hdesc3 i hi
          obtain ⟨hs_m, B₀, hB₀, hag⟩ := hMatch q (hAP ▸ hq)
          have hfin : (⟨touched[i]'hi, hs_bun⟩ : Fin y'.slotCap) = ⟨y'.slotOf q, hs_m⟩ :=
            Fin.ext (h0.symm.trans hts)
          have hSB' := hSB B₀ (hfin.symm ▸ hB₀)
          have hGeq : GraphEq B₀.graph (tr.dyn q).G :=
            graphEq_trans (bunAgree_graphEq hag) (graphEq_symm (hDynGEq q hq))
          have hbeq : (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 = info.U_B q :=
            (bunAgree_bundleCompStep_eq hag (hBReady _ B₀ hB₀)).1
          have hW_eq : st₃.mem (outDescPtr + 1 + 3 * i + 2) = tw := h2
          rw [hW_eq, ← graphEq_batchEnc hGeq, ← hbeq]
          exact hSB'.2
        have henc_pos : 1 ≤ (tr.dyn q).G.batchEnc (info.U_B q) :=
          batchEnc_pos_of_ne_nil (tr.dyn q).G hne
        unfold p4TaskPay
        rw [p4OnTask_of hs' hd₀' hnz]
        unfold dsUpdateAmortCost
        have hopB : (opBatch P_sp d₀ [0, t.batchPtr, t.W, 0] st₃.mem).1 = info.U_B q := hdec
        have hopW : opWords [0, t.batchPtr, t.W, 0] = t.W := rfl
        have hovh : dsUpdateOpOverhead = 20 := rfl
        rw [hopB, hopW, hovh, hdec]
        have hch := hCharge_le q hq d₀ hst₀ hG₀ hVG₀ hGm₀ hBV₀ hds₀
        have hwork : p4TaskWorkOf P_sp y'.spanS t.slot hs' d₀ (info.U_B q) ≤
            340 * (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).UH.length +
            170 * (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).D.card +
            (811 + 207 * depth) *
              (updateReembSet (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).card +
            584 * ((updateReembSet (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).sum fun e =>
              (piTotal (tr'.dyn q) e).length) := by
          unfold p4TaskWorkOf
          have hcand_sub := p4CopyCand_sub_updateReembSet P_sp d₀ (info.U_B q) hVG₀ hL1 hGm₀
            hBV hds
          have hsum_cand : (p4CopyCand P_sp d₀ (info.U_B q)).sum
                (p4CopyEdgeCost P_sp (y'.spanS.set ⟨t.slot, hs'⟩
                  (some ⟨d₀.G₀, d₀.Us ++ [info.U_B q]⟩)) t.slot ⟨d₀.G₀, d₀.Us ++ [info.U_B q]⟩) ≤
              (updateReembSet (d₀.state P_sp) (info.U_B q) (canonicalSparsify P_sp.impl)).sum
                (fun e => 584 * (piTotal ((⟨d₀.G₀, d₀.Us ++ [info.U_B q]⟩ : DSHist).state P_sp)
                  e).length + 207 * P_sp.L + 676) := by
            calc (p4CopyCand P_sp d₀ (info.U_B q)).sum _
                ≤ (p4CopyCand P_sp d₀ (info.U_B q)).sum (fun e =>
                    584 * (piTotal ((⟨d₀.G₀, d₀.Us ++ [info.U_B q]⟩ : DSHist).state P_sp) e).length +
                    207 * P_sp.L + 676) :=
                  Finset.sum_le_sum fun e he =>
                    p4CopyEdgeCost_le P_sp y'.spanS t.slot hs' d₀ (info.U_B q) he
              _ ≤ _ := Finset.sum_le_sum_of_subset hcand_sub
          have hsum_exp : (updateReembSet (d₀.state P_sp) (info.U_B q)
                (canonicalSparsify P_sp.impl)).sum
                (fun e => 584 * (piTotal ((⟨d₀.G₀, d₀.Us ++ [info.U_B q]⟩ : DSHist).state P_sp)
                  e).length + 207 * P_sp.L + 676) =
              584 * ((updateReembSet (d₀.state P_sp) (info.U_B q)
                  (canonicalSparsify P_sp.impl)).sum fun e =>
                    (piTotal ((⟨d₀.G₀, d₀.Us ++ [info.U_B q]⟩ : DSHist).state P_sp) e).length) +
              (207 * depth + 676) *
                (updateReembSet (d₀.state P_sp) (info.U_B q) (canonicalSparsify P_sp.impl)).card := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul]
            change _ + 207 * (_ * depth) + _ * 676 = _
            ring
          rw [hsum_exp] at hsum_cand
          change (⟨d₀.G₀, d₀.Us ++ [info.U_B q]⟩ : DSHist).state P_sp = tr'.dyn q at hst1
          change (p4CopyCand P_sp d₀ (info.U_B q)).sum _ ≤
            584 * ((updateReembSet (d₀.state P_sp) (info.U_B q) (canonicalSparsify impl)).sum
              fun e => (piTotal ((⟨d₀.G₀, d₀.Us ++ [info.U_B q]⟩ : DSHist).state P_sp) e).length) +
            (207 * depth + 676) *
              (updateReembSet (d₀.state P_sp) (info.U_B q) (canonicalSparsify impl)).card at hsum_cand
          rw [hst₀, hst1] at hsum_cand
          have h1 : (update (d₀.state P_sp) (info.U_B q) (canonicalSparsify P_sp.impl)).UH.length =
              (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).UH.length := by
            rw [hst₀]; rfl
          have h2 : (update (d₀.state P_sp) (info.U_B q) (canonicalSparsify P_sp.impl)).D.card =
              (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).D.card := by
            rw [hst₀]; rfl
          have h3 : (updateReembSet (d₀.state P_sp) (info.U_B q)
                (canonicalSparsify P_sp.impl)).card =
              (updateReembSet (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).card := by
            rw [hst₀]; rfl
          rw [h1, h2, h3]
          calc 340 * (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).UH.length +
                170 * (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).D.card +
                135 * (updateReembSet (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).card +
                (p4CopyCand P_sp d₀ (info.U_B q)).sum _
              ≤ 340 * (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).UH.length +
                170 * (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).D.card +
                135 * (updateReembSet (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).card +
                (584 * ((updateReembSet (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).sum
                    fun e => (piTotal (tr'.dyn q) e).length) +
                  (207 * depth + 676) *
                    (updateReembSet (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).card) :=
                Nat.add_le_add_left hsum_cand _
            _ = _ := by ring
        have hW_bound : 1440 * t.W + 485 + 20 + 600 ≤ 9745 * (tr.dyn q).G.batchEnc (info.U_B q) := by
          omega
        dsimp only [gPair]
        omega
    · intro i hi j hj q h1 h2
      have h1' : (tasks[i]'hi).slot = y'.slotOf q := by
        dsimp only [φ] at h1
        split_ifs at h1 with hex
        injection h1 with hq; rw [← hq]; exact hex.choose_spec.2
      have h2' : (tasks[j]'hj).slot = y'.slotOf q := by
        dsimp only [φ] at h2
        split_ifs at h2 with hex
        injection h2 with hq; rw [← hq]; exact hex.choose_spec.2
      have hmap_eq : (tasks.map SpanUpdTask.slot)[i]'(by simpa using hi) =
          (tasks.map SpanUpdTask.slot)[j]'(by simpa using hj) := by
        simp only [List.getElem_map]; exact h1'.trans h2'.symm
      exact (List.Nodup.getElem_inj_iff hT.hnd).mp hmap_eq

end

end MinCostFlow.SparseCore.Program
