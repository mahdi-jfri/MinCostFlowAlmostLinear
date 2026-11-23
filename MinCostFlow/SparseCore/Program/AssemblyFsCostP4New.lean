module

public import MinCostFlow.SparseCore.Program.AssemblyFsCostP4Helpers
public import MinCostFlow.SparseCore.Program.AssemblyFirstWalkPot

import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActMath
import MinCostFlow.SparseCore.Program.AssemblyFirstWalkBound
import MinCostFlow.SparseCore.Program.AssemblyFirstNewPairs
import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue2
import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue11
import MinCostFlow.SparseCore.Program.AssemblyBranchSideGapS8
import Mathlib.Tactic

/-!
# Phase 4 new-slot, walk-potential, `lazyE`, and candidate-list bounds (`AssemblyFsCostP4New`)

Proves the remaining branch-level Phase 4 bounds from `AsmFsPre` and `AsmFsQ₄At`:

1. `rangeCost (fun s => p4NewPay P_sp (p4SpanAfter ...) s + 20) lo hi + 9 * (hi - lo) +
   300 * walkPot tr' ≤ 300 * walkPot tr + 300 * W_tot + (861 + 142 * depth) * lazySum`.
2. `((List.finRange nNew).map fun i => (lazyE i).length).sum ≤ lazySum`.
3. `nNew ≤ 2 * A.U.length`.
4. `Ld.length`, `Li.length`, and `Lr.length` bounded in terms of `UH_tot`, `D_tot`, `W_tot`,
   `R_tot`, `lazySum`, `A.U.length`, and `A.c.fDel.length`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

/-- Pure helper bounding the sum of `(lazyE i).length` by `newlyActive.sum tr.lazyMachInitCost`. -/
private lemma lazyE_length_sum_le {depth : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {tr : BundleTreeState depth} {U : List Update} {ord : ℕ → List End}
    {comps : List (Finset ℕ)} {ncs : List (ℕ × ℕ)} {lazyE : Fin ncs.length → List ℕ}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (ρ : Rotation tr.cs.G) (hρ : ρ.order = ord)
    (hCnd : comps.Nodup) (hCiff : ∀ C, C ∈ comps ↔ C ∈ components tr.cs.G₀)
    (hNC_nd : (ncs.map Prod.fst).Nodup)
    (hNC_lt : ∀ q ∈ ncs, ∃ hc : q.1 < comps.length,
      comps[q.1]'hc ∉ tr.activeComps ∧ q.2 ∈ (tr.cs.compSt (comps[q.1]'hc)).G.V)
    (hNC_set : (ncs.map fun q => comps.getD q.1 ∅).toFinset =
      touchedCompsBatch tr.cs U \ tr.activeComps)
    (hLazyEPost : ∀ k (hk : k < ncs.length),
      (lazyE ⟨k, hk⟩).Pairwise (· < ·) ∧
      (lazyE ⟨k, hk⟩).toFinset = compCoreEdges tr (comps.getD (ncs.getD k (0, 0)).1 ∅))
    (hInact : ∀ C ∈ components tr.cs.G₀, C ∉ tr.activeComps →
      tr.activeBuckets C = (compCoreEdges tr C).image tr.origBucket ∧
      ∀ b ∈ tr.activeBuckets C,
        BunAgree (initBundleFor tr.cs ord
          (bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket C b) tr.k) (tr.bun (C, b)) ∧
        tr.initBunG (C, b) = normGraph (tr.bun (C, b)).graph)
    (hLazy0 : ∀ C ∉ tr.activeComps, ((tr.activeBuckets C).sum fun b => tr.spanConst *
      spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b))) ≤
        tr.lazyMachInitCost C)
    (h1_spanC : 1 ≤ tr.spanConst) :
    ((List.finRange ncs.length).map fun i => (lazyE i).length).sum ≤
      (touchedCompsBatch tr.cs U \ tr.activeComps).sum fun C => tr.lazyMachInitCost C := by
  let φ (i : Fin ncs.length) : Option (Finset ℕ) :=
    some (comps.getD (ncs.getD i.1 (0, 0)).1 ∅)
  refine list_sum_le_finset_sum_of_pmap (touchedCompsBatch tr.cs U \ tr.activeComps)
    (fun i => (lazyE i).length) (fun C => tr.lazyMachInitCost C) φ
    (List.finRange ncs.length) ?_ ?_
  · intro i _
    cases i with
    | mk k hk =>
      dsimp only [φ]
      have hmem_ncs : ncs[k]'hk ∈ ncs := List.getElem_mem hk
      obtain ⟨hc_lt, hnotAct, -⟩ := hNC_lt _ hmem_ncs
      have hgetD_ncs : ncs.getD k (0, 0) = ncs[k]'hk := List.getD_eq_getElem _ _ hk
      have hgetD_c : comps.getD (ncs.getD k (0, 0)).1 ∅ = comps[(ncs[k]'hk).1]'hc_lt := by
        rw [hgetD_ncs, List.getD_eq_getElem _ _ hc_lt]
      have hC_new : comps.getD (ncs.getD k (0, 0)).1 ∅ ∈
          touchedCompsBatch tr.cs U \ tr.activeComps := by
        rw [← hNC_set, List.mem_toFinset]
        exact List.mem_map.mpr ⟨ncs[k]'hk, hmem_ncs, by rw [hgetD_ncs]⟩
      refine ⟨hC_new, ?_⟩
      obtain ⟨hpw, htoF⟩ := hLazyEPost k hk
      have hnd_le : (lazyE ⟨k, hk⟩).Nodup := hpw.imp Nat.ne_of_lt
      rw [← List.toFinset_card_of_nodup hnd_le, htoF, hgetD_c]
      have hC0 : comps[(ncs[k]'hk).1]'hc_lt ∈ components tr.cs.G₀ :=
        (hCiff _).mp (List.getElem_mem hc_lt)
      obtain ⟨hBktsEq, hLazyBun⟩ := hInact _ hC0 hnotAct
      rw [inactive_compCoreEdges_card_eq hI ρ hρ hBktsEq hLazyBun]
      refine le_trans ?_ (hLazy0 _ hnotAct)
      refine Finset.sum_le_sum fun b _ => ?_
      have h1 := m_add_one_le_spanInitBound tr.spanParams depth tr.splitBound
        (tr.initBunG (comps[(ncs[k]'hk).1]'hc_lt, b))
      exact le_trans (by omega) (Nat.le_mul_of_pos_left _ h1_spanC)
  · intro i hi_lt j hj_lt C h1 h2
    have hi' : i < ncs.length := by rwa [List.length_finRange] at hi_lt
    have hj' : j < ncs.length := by rwa [List.length_finRange] at hj_lt
    have hfi : (List.finRange ncs.length)[i]'hi_lt = ⟨i, hi'⟩ := List.getElem_finRange hi_lt
    have hfj : (List.finRange ncs.length)[j]'hj_lt = ⟨j, hj'⟩ := List.getElem_finRange hj_lt
    rw [hfi] at h1; rw [hfj] at h2
    dsimp only [φ] at h1 h2
    injection h1 with h1'
    injection h2 with h2'
    have hci := (hNC_lt _ (List.getElem_mem hi')).1
    have hcj := (hNC_lt _ (List.getElem_mem hj')).1
    rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hci] at h1'
    rw [List.getD_eq_getElem _ _ hj', List.getD_eq_getElem _ _ hcj] at h2'
    have hidx : (ncs[i]'hi').1 = (ncs[j]'hj').1 :=
      (List.Nodup.getElem_inj_iff hCnd).mp (h1'.trans h2'.symm)
    have hmap_eq : (ncs.map Prod.fst)[i]'(by simpa using hi') =
        (ncs.map Prod.fst)[j]'(by simpa using hj') := by
      simp only [List.getElem_map]; exact hidx
    exact (List.Nodup.getElem_inj_iff hNC_nd).mp hmap_eq

public section

set_option maxHeartbeats 2400000 in
/-- **Phase 4 new-slot loop, `walkPot`, `lazyE`, and `Ld`/`Li`/`Lr` bounds**. -/
theorem asmFsCost_p4_new_bounds {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
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
    let lo := A.x.xRest.slots.length
    let hi := lo + newCompsBucketSum A.tr A.x.xRest.comps
      (A.newComps A.x.xRest.cmpH A.x.xRest.comps)
    let W_tot := (activePairs tr').sum fun q =>
      (updateReembSet (A.tr.dyn q) (info.U_B q) (canonicalSparsify impl)).sum fun e =>
        (piTotal (tr'.dyn q) e).length
    let D_tot := (activePairs tr').sum fun q =>
      (update (A.tr.dyn q) (info.U_B q) (canonicalSparsify impl)).D.card
    let R_tot := (activePairs tr').sum fun q =>
      (updateReembSet (A.tr.dyn q) (info.U_B q) (canonicalSparsify impl)).card
    let UH_tot := (activePairs tr').sum fun q =>
      (update (A.tr.dyn q) (info.U_B q) (canonicalSparsify impl)).UH.length
    let lazySum := info.newlyActive.sum fun C => A.tr.lazyMachInitCost C
    (rangeCost (fun s => p4NewPay P_sp (p4SpanAfter P_sp y'.spanS st₃.mem tasks) s + 20) lo hi +
        9 * (hi - lo) + 300 * walkPot tr' ≤
      300 * walkPot A.tr + 300 * W_tot + (861 + 142 * depth) * lazySum) ∧
    (((List.finRange (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length).map
        fun i => (lazyE i).length).sum ≤ lazySum) ∧
    ((A.newComps A.x.xRest.cmpH A.x.xRest.comps).length ≤ 2 * A.U.length) ∧
    (Ld.length ≤ UH_tot + D_tot + W_tot + A.U.length ∧
      Li.length ≤ UH_tot + D_tot + W_tot + 2 * lazySum + 2 * A.U.length + A.c.fDel.length ∧
      Lr.length ≤ R_tot + lazySum) := by
  classical
  obtain ⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c,
    mem, pos, ω⟩ := A
  obtain ⟨vCap, eCap, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour, xT0,
    restH, xRest⟩ := x
  intro sp ord' info tr' P_sp tasks lo hi W_tot D_tot R_tot UH_tot lazySum
  dsimp only [AsmFsArgs.newComps] at ⊢
  obtain ⟨⟨hScanF, tx₀, hTx, hP2, hP3⟩, hP4⟩ := hQ₄
  unfold AsmFsPre AsmFsPreRaw at hA
  unfold AsmFsScanFacts at hScanF
  dsimp only [AsmFsArgs.newComps] at hA hScanF hP2 hP3 hP4 hTx
  obtain ⟨hM0, hN0, hL1, -, -, -, -, -, -, hR, hFacts', hBat, hU, -, -, hOB, -, -, -, -, -, -, -,
    -, -, hfoot, -, -, -, -⟩ := hA
  obtain ⟨hRA, hv, he, -, -, -, -, -⟩ := hR
  dsimp only at hv he
  subst hv he
  obtain ⟨hM, -, -, -⟩ := hScanF
  obtain rfl : xT0 = tx₀ := (eq_of_heq hTx).symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTourRep, -, hSide, -,
    -, -, hDisj⟩ := hRA
  have hSide' := hSide
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMaps, hMod⟩ := hSide'
  obtain ⟨hSMO, -, -, hRestartMod, -, hk, ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩, hSpanP, hSpanC, hSplitB0, -,
    hBD, -, -, hLazy0, -, -, -, hSlotInvOld, hInact, hCross, hInactDyn, hPart, hDynGOld, -,
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
  obtain ⟨-, -, -, -, -, hslc, -, -, hcap5, hsb, hspV, hspE, hmMax, -, -, -, -, -, -, -, hslots',
    hkeepSlot, hSlotN, hMatch, hspanS, hSlotInv, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hLazyEPost, -⟩ := hP2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hnd3, -, -, hdesc3, hunt3, hnone3, -⟩ := hP3
  obtain ⟨hqs, hqsOK, hns, hnsOK, hRepX', -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hLd_nd, hLi_nd, hLr_nd, hLd_iff, hLi_iff,
    hLr_iff⟩ := hP4
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
  have hSM := hT.model hqs hqsOK hns hnsOK
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
  have hDynG_tr : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      (tr.dyn (C, b)).G.E = (tr.bun (C, b)).edges := fun C hC b hb =>
    asmFirstActiveDynGraphInv_E hDynGOld hC hb
  have hDynG'_inv : AsmFirstActiveDynGraphInv tr' :=
    asmFirstActiveDynGraphInv_step sp hI hU hOB hk hInact hInactDyn hPart hDynGOld
  have hDynG_tr' : ∀ C ∈ tr'.activeComps, ∀ b ∈ tr.activeBuckets C,
      (tr'.dyn (C, b)).G.E = (tr'.bun (C, b)).edges := fun C hC b hb =>
    asmFirstActiveDynGraphInv_E hDynG'_inv hC hb
  -- Newly active pairs & lazy init bounds
  let newPairs : Finset (Finset ℕ × ℤ) := activePairs tr' \ activePairs tr
  have hNewPairs_eq : newPairs =
      info.newlyActive.biUnion fun C => (tr.activeBuckets C).image (C, ·) := by
    ext ⟨C, b⟩
    simp only [newPairs, Finset.mem_sdiff, mem_activePairs, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨⟨hC', hb⟩, hnot⟩
      have hC_new : C ∈ info.newlyActive := by
        rcases Finset.mem_union.mp hC' with hOld | hN
        · exact absurd ⟨hOld, hb⟩ hnot
        · exact hN
      exact ⟨C, hC_new, b, hb, rfl⟩
    · rintro ⟨C', hC', b', hb', heq⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      have hnotOld : C' ∉ tr.activeComps := (Finset.mem_sdiff.mp hC').2
      exact ⟨⟨Finset.mem_union_right _ hC', hb'⟩, fun h => hnotOld h.1⟩
  have hSum_newPairs : ∀ f : Finset ℕ × ℤ → ℕ,
      newPairs.sum f =
        info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b => f (C, b) := by
    intro f
    rw [hNewPairs_eq, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun C _ => ?_
      rw [Finset.sum_image]; intro b₁ _ b₂ _ heq; exact (Prod.mk.inj heq).2
    · intro C₁ _ C₂ _ hne
      refine Finset.disjoint_left.mpr fun q h1 h2 => ?_
      obtain ⟨b₁, -, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨b₂, -, heq⟩ := Finset.mem_image.mp h2
      exact hne (Prod.mk.inj heq).1.symm
  have h1_spanC : 1 ≤ tr.spanConst :=
    le_trans (by unfold dsAmortConst; omega) hSpanC
  have hlo_eq : lo = xRest.slots.length := rfl
  have hhi_eq : hi = xRest.slots.length + newCompsBucketSum tr xRest.comps
      (scanBatchFold tr.cs.G (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps) U).newComps :=
    rfl
  have hlo_le : lo ≤ hi := Nat.le_add_right _ _
  have hNewPairs_m1 : newPairs.sum (fun q => (tr.initBunG q).m + 1) ≤ lazySum := by
    rw [hSum_newPairs]
    refine Finset.sum_le_sum fun C hC => ?_
    have hnotAct : C ∉ tr.activeComps := (Finset.mem_sdiff.mp hC).2
    refine le_trans ?_ (hLazy0 C hnotAct)
    refine Finset.sum_le_sum fun b _ => ?_
    have h1 := m_add_one_le_spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b))
    exact le_trans h1 (Nat.le_mul_of_pos_left _ h1_spanC)
  -- ==== Part 1: `p4NewPay` + `9 * (hi - lo)` + `300 * walkPot tr'` ====
  have hPart3 : rangeCost (fun s => p4NewPay P_sp (p4SpanAfter P_sp y'.spanS st₃.mem tasks) s + 20)
        lo hi + 9 * (hi - lo) + 300 * walkPot tr' ≤
      300 * walkPot tr + 300 * W_tot + (861 + 142 * depth) * lazySum := by
    have hSlotInRange : ∀ s ∈ List.range' lo (hi - lo),
        ∃ q ∈ newPairs, s = y'.slotOf q := by
      intro s hs
      rw [List.mem_range'_1] at hs
      obtain ⟨q, hq, rfl⟩ := hT.hnewSlot s hs.1 (by omega)
      refine ⟨q, Finset.mem_sdiff.mpr ⟨hq, ?_⟩, rfl⟩
      intro hqOld
      have hlt : xRest.slotOf q < lo := by
        have hmem := hSMO.2.1 q hqOld
        rw [hSlotInvOld.2.1, List.mem_range] at hmem
        exact hmem
      have heq := hkeepSlot q hqOld
      omega
    have hRange_le : rangeCost (fun s => p4NewPay P_sp (p4SpanAfter P_sp y'.spanS st₃.mem tasks) s
          + 20) lo hi + 9 * (hi - lo) ≤
        (561 + 142 * depth) * lazySum +
        284 * newPairs.sum (fun q =>
          ((tr'.dyn q).G.E \ tr'.S_cur.E).sum fun e => (piTotal (tr'.dyn q) e).length) := by
      have h9 : rangeCost (fun s => p4NewPay P_sp (p4SpanAfter P_sp y'.spanS st₃.mem tasks) s + 20)
            lo hi + 9 * (hi - lo) =
          ((List.range' lo (hi - lo)).map
            (fun s => p4NewPay P_sp (p4SpanAfter P_sp y'.spanS st₃.mem tasks) s + 20 + 9)).sum := by
        unfold rangeCost
        have hlen : (List.range' lo (hi - lo)).length = hi - lo := List.length_range'
        have hconst : ∀ l : List ℕ, ∀ f : ℕ → ℕ,
            (l.map fun s => f s + 9).sum = (l.map f).sum + 9 * l.length := by
          intro l f; induction l with
          | nil => simp
          | cons a tl ih => simp [ih]; ring
        exact ((hconst _ _).trans (by rw [hlen])).symm
      rw [h9]
      let gNew (q : Finset ℕ × ℤ) : ℕ :=
        (561 + 142 * depth) * ((tr.initBunG q).m + 1) +
        284 * (((tr'.dyn q).G.E \ tr'.S_cur.E).sum fun e => (piTotal (tr'.dyn q) e).length)
      have hSum_gNew : newPairs.sum gNew ≤
          (561 + 142 * depth) * lazySum +
          284 * newPairs.sum (fun q =>
            ((tr'.dyn q).G.E \ tr'.S_cur.E).sum fun e => (piTotal (tr'.dyn q) e).length) := by
        dsimp only [gNew]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left (561 + 142 * depth) hNewPairs_m1) _
      refine le_trans ?_ hSum_gNew
      let φ (s : ℕ) : Option (Finset ℕ × ℤ) :=
        if h : ∃ q ∈ newPairs, s = y'.slotOf q then some h.choose else none
      refine list_sum_le_finset_sum_of_pmap newPairs
        (fun s => p4NewPay P_sp (p4SpanAfter P_sp y'.spanS st₃.mem tasks) s + 20 + 9)
        gNew φ (List.range' lo (hi - lo)) ?_ ?_
      · intro s hs
        obtain ⟨q, hqNew, rfl⟩ := hSlotInRange s hs
        have hex : ∃ q' ∈ newPairs, y'.slotOf q = y'.slotOf q' := ⟨q, hqNew, rfl⟩
        have hφ : φ (y'.slotOf q) = some hex.choose := dite_eq_left hex
        have hq' : q ∈ activePairs tr' := (Finset.mem_sdiff.mp hqNew).1
        have hq_eq : hex.choose = q :=
          hT.hinj _ (Finset.mem_sdiff.mp hex.choose_spec.1).1 q hq' hex.choose_spec.2.symm
        rw [hφ, hq_eq]
        refine ⟨hqNew, ?_⟩
        obtain ⟨hs_cap, d₀, -, hst₀, hG₀, hEm, hNe⟩ := hSlotData q hq'
        have hd'_facts : ∃ d' : DSHist,
            p4SpanAfter P_sp y'.spanS st₃.mem tasks ⟨y'.slotOf q, hs_cap⟩ = some d' ∧
            d'.state P_sp = tr'.dyn q ∧ d'.G₀ = tr.initBunG q ∧
            (d'.state P_sp).G.E ⊆ d'.G₀.E := by
          by_cases hU0 : info.U_B q = []
          · obtain ⟨hpa, hVG₀, hGm₀, hBV₀, hds₀⟩ := hEm hU0
            have hst' : d₀.state P_sp = tr'.dyn q := by
              rw [hst₀]
              show tr.dyn q = (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).state
              rw [hU0]; simp [update, updateGo]
            have hEsub : (d₀.state P_sp).G.E ⊆ d₀.G₀.E := by
              rw [← dsHist_applyBatch_eq_state_G P_sp d₀ hVG₀ hL1 hGm₀ hBV₀ hds₀]
              exact applyBatch_E_subset_of_delOrSplit _ _ hds₀
            exact ⟨d₀, hpa, hst', hG₀, hEsub⟩
          · obtain ⟨hpa, hst1, hVG₀, hGm₀, hBV, hds, -, -⟩ := hNe hU0
            let d₁ : DSHist := ⟨d₀.G₀, d₀.Us ++ [info.U_B q]⟩
            have hfl : d₁.flat = d₀.flat ++ info.U_B q := dsHist_flat_append d₀ (info.U_B q)
            have hEsub : (d₁.state P_sp).G.E ⊆ d₁.G₀.E := by
              rw [← dsHist_applyBatch_eq_state_G P_sp d₁ hVG₀ hL1 hGm₀ (hfl ▸ hBV) (hfl ▸ hds)]
              exact applyBatch_E_subset_of_delOrSplit _ _ (hfl ▸ hds)
            exact ⟨d₁, hpa, hst1, hG₀, hEsub⟩
        obtain ⟨d', hpa, hst', hG₀', hEsub⟩ := hd'_facts
        have hpay_eq : p4NewPay P_sp (p4SpanAfter P_sp y'.spanS st₃.mem tasks) (y'.slotOf q) =
            p4NewWork P_sp (p4SpanAfter P_sp y'.spanS st₃.mem tasks) (y'.slotOf q) d' := by
          unfold p4NewPay; simp only [hs_cap, ↓reduceDIte, hpa]
        rw [hpay_eq]
        have hnw := p4NewWork_add_20_le P_sp (p4SpanAfter P_sp y'.spanS st₃.mem tasks)
          (y'.slotOf q) hs_cap d' hpa hEsub
        rw [hst', hG₀'] at hnw
        obtain ⟨C_lsst', ℓ₀', hI', -, -⟩ := hFacts'.2.1
        have hH'_eq := scur_inter_dynG_eq_dynH hI' hFacts'.2.2.1 hFacts'.2.2.2.1
          (mem_activePairs.mp hq').1 (mem_activePairs.mp hq').2
          (hDynG_tr' q.1 (mem_activePairs.mp hq').1 q.2 (mem_activePairs.mp hq').2)
        have hsdiff : (tr'.dyn q).G.E \ (tr'.dyn q).H.E = (tr'.dyn q).G.E \ tr'.S_cur.E := by
          rw [← hH'_eq]; ext e; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
        rw [hsdiff] at hnw
        dsimp only [gNew]
        have hnw' : p4NewWork P_sp (p4SpanAfter P_sp y'.spanS st₃.mem tasks) (y'.slotOf q) d' + 20 ≤
            (561 + 142 * depth) * (tr.initBunG q).m + 420 +
            284 * ((tr'.dyn q).G.E \ tr'.S_cur.E).sum (fun e => (piTotal (tr'.dyn q) e).length) :=
          hnw
        have hmul : (561 + 142 * depth) * (tr.initBunG q).m + 429 ≤
            (561 + 142 * depth) * ((tr.initBunG q).m + 1) := by
          rw [Nat.mul_add, Nat.mul_one]; omega
        omega
      · intro i hi_lt j hj_lt q h1 h2
        have h1' : (List.range' lo (hi - lo))[i]'hi_lt = y'.slotOf q := by
          dsimp only [φ] at h1; split_ifs at h1 with hex
          injection h1 with hq; rw [← hq]; exact hex.choose_spec.2
        have h2' : (List.range' lo (hi - lo))[j]'hj_lt = y'.slotOf q := by
          dsimp only [φ] at h2; split_ifs at h2 with hex
          injection h2 with hq; rw [← hq]; exact hex.choose_spec.2
        have hndR : (List.range' lo (hi - lo)).Nodup := List.nodup_range'
        exact (List.Nodup.getElem_inj_iff hndR).mp (h1'.trans h2'.symm)
    obtain ⟨C_lsst', ℓ₀', hI', -, -⟩ := hFacts'.2.1
    let dMap : Finset ℕ × ℤ → DSHist := fun q =>
      if h : q ∈ activePairs tr' then (hSlotData q h).choose_spec.choose else ⟨tr.cs.G, []⟩
    have hOld_wp : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
        (dMap (C, b)).state P_sp = tr.dyn (C, b) ∧
        (dMap (C, b)).G₀.IsValid ∧ (dMap (C, b)).G₀.m ≤ P_sp.mMax ∧
        (dMap (C, b)).G₀.BatchIsValid ((dMap (C, b)).flat ++ info.U_B (C, b)) ∧
        (∀ u ∈ (dMap (C, b)).flat ++ info.U_B (C, b), isDelOrSplit u) := by
      intro C hC b hb
      have hq' : (C, b) ∈ activePairs tr' :=
        mem_activePairs.mpr ⟨Finset.mem_union_left _ hC, hb⟩
      have hd_def : dMap (C, b) = (hSlotData (C, b) hq').choose_spec.choose := dite_eq_left hq'
      rw [hd_def]
      obtain ⟨-, hst₀, -, hEm, hNe⟩ := (hSlotData (C, b) hq').choose_spec.choose_spec
      by_cases hU0 : info.U_B (C, b) = []
      · obtain ⟨-, hVG₀, hGm₀, hBV₀, hds₀⟩ := hEm hU0
        rw [hU0, List.append_nil]; exact ⟨hst₀, hVG₀, hGm₀, hBV₀, hds₀⟩
      · obtain ⟨-, -, hVG₀, hGm₀, hBV, hds, -, -⟩ := hNe hU0
        exact ⟨hst₀, hVG₀, hGm₀, hBV, hds⟩
    have hNew_wp : ∀ C ∈ info.newlyActive, ∀ b ∈ tr.activeBuckets C,
        tr.dyn (C, b) = DSHist.state P_sp ⟨tr.initBunG (C, b), []⟩ ∧
        (tr.initBunG (C, b)).IsValid ∧ (tr.initBunG (C, b)).m ≤ P_sp.mMax ∧
        (tr.initBunG (C, b)).BatchIsValid (info.U_B (C, b)) ∧
        (∀ u ∈ info.U_B (C, b), isDelOrSplit u) := by
      intro C hC b hb
      have hq' : (C, b) ∈ activePairs tr' :=
        mem_activePairs.mpr ⟨Finset.mem_union_right _ hC, hb⟩
      have hC0 : C ∈ components tr.cs.G₀ :=
        touchedCompsBatch_subset _ _ (Finset.mem_sdiff.mp hC).1
      have hnotAct : C ∉ tr.activeComps := (Finset.mem_sdiff.mp hC).2
      have hdyn0 : tr.dyn (C, b) = DSHist.state P_sp ⟨tr.initBunG (C, b), []⟩ := by
        have h1 := hInactDyn C hC0 hnotAct b hb
        dsimp only [P_sp, asmBrSP] at h1 ⊢
        rw [hsb, hspV, hspE, hmMax]
        exact h1
      obtain ⟨hs_n, d₀, -, -, hG₀, hEm, hNe⟩ := hSlotData (C, b) hq'
      have hVGm : (tr.initBunG (C, b)).IsValid ∧ (tr.initBunG (C, b)).m ≤ P_sp.mMax := by
        rw [← hG₀]
        by_cases hU0 : info.U_B (C, b) = []
        · obtain ⟨-, h1, h2, -⟩ := hEm hU0; exact ⟨h1, h2⟩
        · obtain ⟨-, -, h1, h2, -⟩ := hNe hU0; exact ⟨h1, h2⟩
      obtain ⟨hAg, hInitG, -⟩ := (hInact C hC0 hnotAct).2.2.2.2 b hb
      obtain ⟨ρ', σ', hρ', hσ', hRB⟩ := hOB
      have hP_part : (tr.bun (C, b)).IsPartition
          (coreRotation (L := tr.cs.lsf) ρ' hI.hG_val (compLSF_RF_isRSF hI)) tr.k :=
        (bunAgree_isPartition_iff hAg).mp
          (initBundleFor_isPartition hI ρ' hρ' (Finset.filter_subset _ _) hk)
      have hBReady_p : BundleStepReady tr.cs (tr.bun (C, b)) tr.k ord ord' U :=
        ⟨C_lsst, ℓ₀, hI, ρ', σ', hρ', hσ', hRB, hU, hP_part⟩
      have hSpec := bundleCompStep_spec hBReady_p
      have hGeq : GraphEq (tr.bun (C, b)).graph (tr.initBunG (C, b)) := by
        rw [hInitG]; exact graphEq_symm (normGraph_graphEq _)
      exact ⟨hdyn0, hVGm.1, hVGm.2, (graphEq_batchIsValid hGeq _).mp hSpec.2.1, hSpec.2.2.2.1⟩
    have hWP := walkPot_step_le P_sp tr U ord ord' hL1 ⟨C_lsst, ℓ₀, hI⟩ hRestartMod hBD
      hDynG_tr ⟨C_lsst', ℓ₀', hI'⟩ hFacts'.2.2.1 hFacts'.2.2.2.1 hDynG_tr' dMap hOld_wp hNew_wp
    have hInitWalks : (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        (tr.initBunG (C, b)).E.sum fun e => (piTotal (tr.dyn (C, b)) e).length) ≤ lazySum := by
      refine Finset.sum_le_sum fun C hC => ?_
      have hnotAct : C ∉ tr.activeComps := (Finset.mem_sdiff.mp hC).2
      have heq_sum : ((tr.activeBuckets C).sum fun b =>
            (tr.initBunG (C, b)).E.sum fun e => (piTotal (tr.dyn (C, b)) e).length) =
          ((tr.activeBuckets C).sum fun b =>
            (tr.initBunG (C, b)).E.sum fun e =>
              (piTotal (DSHist.state P_sp ⟨tr.initBunG (C, b), []⟩) e).length) := by
        refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun e _ => ?_
        exact congrArg (fun st : DynSpannerState depth => (piTotal st e).length)
          (hNew_wp C hC b hb).1
      rw [heq_sum]
      exact newlyActive_walks_le_lazyMachInitCost P_sp tr C hSpanP' h1_spanC
        (le_of_eq hP_splitB) (fun b hb => ⟨(hNew_wp C hC b hb).2.1, (hNew_wp C hC b hb).2.2.1⟩)
        (hLazy0 C hnotAct)
    have hNewWalks_le_step : newPairs.sum (fun q =>
        ((tr'.dyn q).G.E \ tr'.S_cur.E).sum fun e => (piTotal (tr'.dyn q) e).length) ≤
        stepNewWalks sp tr U ord ord' := by
      rw [hSum_newPairs]
      unfold stepNewWalks; exact Nat.le_add_left _ _
    have hW_eq : (tr'.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        (updateReembSet (tr.dyn (C, b)) (info.U_B (C, b)) (canonicalSparsify P_sp.impl)).sum
          fun e => (piTotal (tr'.dyn (C, b)) e).length) = W_tot := by
      exact (sum_activePairs_eq tr' (fun q =>
        (updateReembSet (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).sum fun e =>
          (piTotal (tr'.dyn q) e).length)).symm
    dsimp only at hWP
    change stepNewWalks sp tr U ord ord' + walkPot tr' ≤
      walkPot tr +
      (tr'.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        (updateReembSet (tr.dyn (C, b)) (info.U_B (C, b)) (canonicalSparsify P_sp.impl)).sum
          fun e => (piTotal (tr'.dyn (C, b)) e).length) +
      (info.newlyActive.sum fun C => (tr.activeBuckets C).sum fun b =>
        (tr.initBunG (C, b)).E.sum fun e => (piTotal (tr.dyn (C, b)) e).length) at hWP
    rw [hW_eq] at hWP
    have hring : (561 + 142 * depth) * lazySum + 300 * lazySum = (861 + 142 * depth) * lazySum := by
      ring
    omega
  -- ==== Parts 2 & 3: `lazyE` total length and `newComps.length ≤ 2 * U.length` ====
  have hCnd : xRest.comps.Nodup := hMaps.2.2.2.2.1
  have hCiff : ∀ C, C ∈ xRest.comps ↔ C ∈ components tr.cs.G₀ := hMaps.2.2.2.2.2.1
  obtain ⟨hNC_nd, hNC_lt, hNC_set, hNC_len, -, -⟩ :=
    asmFirstStep_newComps_ok (cmpMap₀ := fun v => mem (xRest.cmpH + v)) hI hU hCnd hCiff
      (asmSdMaps_cmp_ok hMaps) hCross
  set ncs := (scanBatchFold tr.cs.G
    (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps) U).newComps
  have hLazyE_sum : ((List.finRange ncs.length).map fun i => (lazyE i).length).sum ≤ lazySum :=
    lazyE_length_sum_le hI ρ hρ hCnd hCiff hNC_nd hNC_lt hNC_set
      (fun k hk => by obtain ⟨-, -, hpw, htoF, -⟩ := hLazyEPost k hk; exact ⟨hpw, htoF⟩)
      (fun C hC0 hnotAct => by
        obtain ⟨-, hBktsEq, -, -, hLazyBun⟩ := hInact C hC0 hnotAct
        exact ⟨hBktsEq, fun b hb => ⟨(hLazyBun b hb).1, (hLazyBun b hb).2.1⟩⟩)
      hLazy0 h1_spanC
  -- ==== Part 4: `Ld.length`, `Li.length`, `Lr.length` ====
  have hPart6 : Ld.length ≤ UH_tot + D_tot + W_tot + U.length ∧
      Li.length ≤ UH_tot + D_tot + W_tot + 2 * lazySum + 2 * U.length + c.fDel.length ∧
      Lr.length ≤ R_tot + lazySum := by
    let W := (p4SpanWV P_sp y'.spanS st₃.mem tr.S_cur.E yEmb.view tasks qs ns).1
    have hqs_step := foldl_p4WVStep_delSup_insSup_le P_sp y'.spanS st₃.mem tr.S_cur.E qs
      (⟨∅, ∅, ∅, [], [], [], ∅, []⟩, yEmb.view) hqsOK (by
        intro q hq hs d hd hnz
        obtain ⟨p', hp', hps, hbat⟩ := hSM.htask q hq
        obtain ⟨hs', d₀, hd₀, -, -, -, hNe⟩ := hSlotData p' hp'
        have hdd : d = d₀ := by
          have hfin : (⟨q.1.slot, hs⟩ : Fin y'.cap) = ⟨y'.slotOf p', hs'⟩ := Fin.ext hps
          rw [hfin, hd₀] at hd; exact (Option.some.inj hd).symm
        subst hdd
        obtain ⟨hdec, hzero⟩ := hbat hs d hd
        have hne : info.U_B p' ≠ [] := fun h0 => hnz (hzero.mpr h0)
        obtain ⟨-, -, hVG₀, hGm₀, hBV, hds, -, -⟩ := hNe hne
        rw [hdec]; exact ⟨hVG₀, hL1, hGm₀, hBV, hds⟩)
    have hqs_sum : (qs.map fun q =>
        p4OnTask y'.spanS st₃.mem 0 (fun _ _ d =>
          let Uq := (decodeBatch st₃.mem q.1.batchPtr (d.state P_sp).G).1
          let d' : DSHist := ⟨d.G₀, d.Us ++ [Uq]⟩
          (update (d.state P_sp) Uq (canonicalSparsify P_sp.impl)).UH.length +
            (update (d.state P_sp) Uq (canonicalSparsify P_sp.impl)).D.card +
            (updateReembSet (d.state P_sp) Uq (canonicalSparsify P_sp.impl)).sum
              (fun e => (piTotal (d'.state P_sp) e).length)) q.1).sum ≤
        UH_tot + D_tot + W_tot := by
      let gCnt (q : Finset ℕ × ℤ) : ℕ :=
        (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).UH.length +
        (update (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).D.card +
        (updateReembSet (tr.dyn q) (info.U_B q) (canonicalSparsify impl)).sum
          (fun e => (piTotal (tr'.dyn q) e).length)
      have hRHS : (activePairs tr').sum gCnt = UH_tot + D_tot + W_tot := by
        simp only [gCnt, UH_tot, D_tot, W_tot, Finset.sum_add_distrib]
      rw [← hRHS]
      let φ (q : SpanUpdTask × P4TaskOut) : Option (Finset ℕ × ℤ) :=
        if h : ∃ p' ∈ activePairs tr', q.1.slot = y'.slotOf p' then some h.choose else none
      refine list_sum_le_finset_sum_of_pmap (activePairs tr') _ gCnt φ qs ?_ ?_
      · intro q hq
        obtain ⟨p', hp', hps, hbat⟩ := hSM.htask q hq
        have hex : ∃ p'' ∈ activePairs tr', q.1.slot = y'.slotOf p'' := ⟨p', hp', hps⟩
        have hφ : φ q = some hex.choose := dite_eq_left hex
        have hp_eq : hex.choose = p' :=
          hT.hinj _ hex.choose_spec.1 p' hp' (hex.choose_spec.2.symm.trans hps)
        rw [hφ, hp_eq]
        refine ⟨hp', ?_⟩
        obtain ⟨hs', d₀, hd₀, hst₀, -, -, hNe⟩ := hSlotData p' hp'
        have hs : q.1.slot < y'.cap := hps ▸ hs'
        have hd₀' : y'.spanS ⟨q.1.slot, hs⟩ = some d₀ := by
          rw [show (⟨q.1.slot, hs⟩ : Fin y'.cap) = ⟨y'.slotOf p', hs'⟩ from Fin.ext hps]; exact hd₀
        by_cases hnz : st₃.mem q.1.batchPtr = 0
        · rw [p4OnTask_empty hs hd₀' hnz]; exact Nat.zero_le _
        · obtain ⟨hdec, hzero⟩ := hbat hs d₀ hd₀'
          have hne : info.U_B p' ≠ [] := fun h0 => hnz (hzero.mpr h0)
          obtain ⟨-, hst1, -⟩ := hNe hne
          rw [p4OnTask_of hs hd₀' hnz]; dsimp only [gCnt]
          rw [hdec, hst₀, hst1]; exact le_rfl
      · intro i hi_lt j hj_lt p' h1 h2
        have h1' : (qs[i]'hi_lt).1.slot = y'.slotOf p' := by
          dsimp only [φ] at h1; split_ifs at h1 with hex
          injection h1 with hp; rw [← hp]; exact hex.choose_spec.2
        have h2' : (qs[j]'hj_lt).1.slot = y'.slotOf p' := by
          dsimp only [φ] at h2; split_ifs at h2 with hex
          injection h2 with hp; rw [← hp]; exact hex.choose_spec.2
        have hmap_eq : ((qs.map Prod.fst).map SpanUpdTask.slot)[i]'(by simpa using hi_lt) =
            ((qs.map Prod.fst).map SpanUpdTask.slot)[j]'(by simpa using hj_lt) := by
          simp only [List.getElem_map]; exact h1'.trans h2'.symm
        exact (List.Nodup.getElem_inj_iff hSM.hnd).mp hmap_eq
    have hns_step := foldl_p4NewStep_delSup_insSup_le P_sp
      (p4SpanAfter P_sp y'.spanS st₃.mem tasks) ns
      (qs.foldl (p4WVStep P_sp y'.spanS st₃.mem tr.S_cur.E)
        (⟨∅, ∅, ∅, [], [], [], ∅, []⟩, yEmb.view))
    have hns_sum : (ns.map fun q => q.2.toFinset.card).sum ≤ lazySum := by
      have hNewPairs_m : newPairs.sum (fun q => (tr.initBunG q).m) ≤ lazySum :=
        le_trans (Finset.sum_le_sum fun _ _ => Nat.le_succ _) hNewPairs_m1
      refine le_trans ?_ hNewPairs_m
      let φ (q : ℕ × List ℕ) : Option (Finset ℕ × ℤ) :=
        if h : ∃ p' ∈ newPairs, q.1 = y'.slotOf p' then some h.choose else none
      refine list_sum_le_finset_sum_of_pmap newPairs (fun q => q.2.toFinset.card)
        (fun p' => (tr.initBunG p').m) φ ns ?_ ?_
      · intro q hq
        have hq1_mem : q.1 ∈ List.range' lo (hi - lo) := by
          have hmem : q.1 ∈ ns.map Prod.fst := List.mem_map_of_mem hq
          rw [hns] at hmem; exact hmem
        rw [List.mem_range'_1] at hq1_mem
        obtain ⟨p', hp', hps⟩ := hT.hnewSlot q.1 hq1_mem.1 (by omega)
        have hpNew : p' ∈ newPairs := by
          refine Finset.mem_sdiff.mpr ⟨hp', fun hOld => ?_⟩
          have hlt : xRest.slotOf p' < lo := by
            have hmem := hSMO.2.1 p' hOld; rw [hSlotInvOld.2.1, List.mem_range] at hmem; exact hmem
          have heq := hkeepSlot p' hOld; omega
        have hex : ∃ p'' ∈ newPairs, q.1 = y'.slotOf p'' := ⟨p', hpNew, hps⟩
        have hφ : φ q = some hex.choose := dite_eq_left hex
        have hp_eq : hex.choose = p' :=
          hT.hinj _ (Finset.mem_sdiff.mp hex.choose_spec.1).1 p' hp'
            (hex.choose_spec.2.symm.trans hps)
        rw [hφ, hp_eq]
        refine ⟨hpNew, ?_⟩
        obtain ⟨hs_cap, d₀, -, -, hG₀, hEm, hNe⟩ := hSlotData p' hp'
        have hs : q.1 < y'.cap := hps ▸ hs_cap
        by_cases hU0 : info.U_B p' = []
        · obtain ⟨hpa, hVG₀, hGm₀, hBV₀, hds₀⟩ := hEm hU0
          have hpa' : p4SpanAfter P_sp y'.spanS st₃.mem tasks ⟨q.1, hs⟩ = some d₀ := by
            rw [show (⟨q.1, hs⟩ : Fin y'.cap) = ⟨y'.slotOf p', hs_cap⟩ from Fin.ext hps]; exact hpa
          rw [(hnsOK q hq hs d₀ hpa').2,
            ← dsHist_applyBatch_eq_state_G P_sp d₀ hVG₀ hL1 hGm₀ hBV₀ hds₀, ← hG₀]
          exact Finset.card_le_card (applyBatch_E_subset_of_delOrSplit _ _ hds₀)
        · obtain ⟨hpa, -, hVG₀, hGm₀, hBV, hds, -, -⟩ := hNe hU0
          let d₁ : DSHist := ⟨d₀.G₀, d₀.Us ++ [info.U_B p']⟩
          have hfl : d₁.flat = d₀.flat ++ info.U_B p' := dsHist_flat_append d₀ (info.U_B p')
          have hpa' : p4SpanAfter P_sp y'.spanS st₃.mem tasks ⟨q.1, hs⟩ = some d₁ := by
            rw [show (⟨q.1, hs⟩ : Fin y'.cap) = ⟨y'.slotOf p', hs_cap⟩ from Fin.ext hps]; exact hpa
          rw [(hnsOK q hq hs d₁ hpa').2,
            ← dsHist_applyBatch_eq_state_G P_sp d₁ hVG₀ hL1 hGm₀ (hfl ▸ hBV) (hfl ▸ hds), ← hG₀]
          exact Finset.card_le_card (applyBatch_E_subset_of_delOrSplit _ _ (hfl ▸ hds))
      · intro i hi_lt j hj_lt p' h1 h2
        have h1' : (ns[i]'hi_lt).1 = y'.slotOf p' := by
          dsimp only [φ] at h1; split_ifs at h1 with hex
          injection h1 with hp; rw [← hp]; exact hex.choose_spec.2
        have h2' : (ns[j]'hj_lt).1 = y'.slotOf p' := by
          dsimp only [φ] at h2; split_ifs at h2 with hex
          injection h2 with hp; rw [← hp]; exact hex.choose_spec.2
        have hnd_ns : (ns.map Prod.fst).Nodup := by rw [hns]; exact List.nodup_range'
        have hmap_eq : (ns.map Prod.fst)[i]'(by simpa using hi_lt) =
            (ns.map Prod.fst)[j]'(by simpa using hj_lt) := by
          simp only [List.getElem_map]; exact h1'.trans h2'.symm
        exact (List.Nodup.getElem_inj_iff hnd_ns).mp hmap_eq
    have hW_del : W.delSup.toFinset.card ≤ UH_tot + D_tot + W_tot := by
      dsimp only [W, p4SpanWV]
      rw [hns_step.1]; dsimp only at hqs_step hqs_sum
      simp only [List.toFinset_nil, Finset.card_empty, zero_add] at hqs_step
      omega
    have hW_ins : W.insSup.toFinset.card ≤ UH_tot + D_tot + W_tot + lazySum := by
      dsimp only [W, p4SpanWV]
      dsimp only at hqs_step hqs_sum
      simp only [List.toFinset_nil, Finset.card_empty, zero_add] at hqs_step
      omega
    let lazyUnion : Finset ℕ := (Finset.univ : Finset (Fin ncs.length)).biUnion fun i =>
      (lazyE i).toFinset
    have hLazyU_card : lazyUnion.card ≤ lazySum := by
      calc lazyUnion.card
          ≤ (Finset.univ : Finset (Fin ncs.length)).sum fun i => (lazyE i).toFinset.card :=
            Finset.card_biUnion_le
        _ ≤ (Finset.univ : Finset (Fin ncs.length)).sum fun i => (lazyE i).length :=
            Finset.sum_le_sum fun i _ => List.toFinset_card_le _
        _ = ((List.finRange ncs.length).map fun i => (lazyE i).length).sum :=
            Fin.sum_univ_def _
        _ ≤ lazySum := hLazyE_sum
    have hp4R_card : (p4ReembSet P_sp tr info).card ≤ R_tot := by
      unfold p4ReembSet
      rw [show R_tot = tr'.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
          (updateReembSet (tr.dyn (C, b)) (info.U_B (C, b)) (canonicalSparsify impl)).card from
        sum_activePairs_eq tr' _]
      exact le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun C _ => Finset.card_biUnion_le)
    refine ⟨?_, ?_, ?_⟩
    · rw [← List.toFinset_card_of_nodup hLd_nd]
      have hsub : Ld.toFinset ⊆ W.delSup.toFinset ∪ batchDeletes U := fun e he => by
        rcases (hLd_iff e).mp (List.mem_toFinset.mp he) with h1 | h2
        · exact Finset.mem_union_left _ (List.mem_toFinset.mpr h1)
        · exact Finset.mem_union_right _ h2
      have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have h2 := batchDeletes_card_le U
      omega
    · rw [← List.toFinset_card_of_nodup hLi_nd]
      have hsub : Li.toFinset ⊆ W.insSup.toFinset ∪ batchDeletes U ∪ batchInsEdges U ∪
          lazyUnion ∪ c.fDel.toFinset := fun e he => by
        rcases (hLi_iff e).mp (List.mem_toFinset.mp he) with h1 | h2 | h3 | ⟨i, hi⟩ | h5
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr h1))))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ h2)))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h3))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, List.mem_toFinset.mpr hi⟩))
        · exact Finset.mem_union_right _ (List.mem_toFinset.mpr h5)
      have hc1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hc2 := Finset.card_union_le
        (W.insSup.toFinset ∪ batchDeletes U ∪ batchInsEdges U) lazyUnion
      have hc3 := Finset.card_union_le (W.insSup.toFinset ∪ batchDeletes U) (batchInsEdges U)
      have hc4 := Finset.card_union_le W.insSup.toFinset (batchDeletes U)
      have hbd := batchDeletes_card_le U
      have hbi := batchInsEdges_card_le U
      have hcf := List.toFinset_card_le c.fDel
      omega
    · rw [← List.toFinset_card_of_nodup hLr_nd]
      have hsub : Lr.toFinset ⊆ p4ReembSet P_sp tr info ∪ lazyUnion := fun e he => by
        rcases (hLr_iff e).mp (List.mem_toFinset.mp he) with h1 | ⟨i, hi⟩
        · exact Finset.mem_union_left _ h1
        · exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, List.mem_toFinset.mpr hi⟩)
      have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      omega
  exact ⟨hPart3, hLazyE_sum, hNC_len, hPart6⟩

end

end MinCostFlow.SparseCore.Program
