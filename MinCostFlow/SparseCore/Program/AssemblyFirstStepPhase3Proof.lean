module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase3Defs

import WordRAM.Tactic

/-!
# Phase 3 end-to-end verification (`AssemblyFirstStepPhase3Proof`)

Proves `asmFirstPhase3_runs` for `asmFirstPhase3Stmt` (`AssemblyFirstStepPhase3Defs.lean`),
chaining:
1. `asmFirstBuildDelTriples_runs` (del-triples on `tr.cs.RF` before tour edits),
2. `asmFirstBuildGroups_runs` (ancestor-tracked split groups from P4's `SplitEntriesAt`),
3. `asmFirstTourBlockStep_runs` (P2 tour step + `OutMarksOf` + `OutSplitListsAt`),
4. `asmFirstBunStepModel_runs` (P5 headroom bundle step + `asmTourRepWithPot` telescoping +
   touched-slot `SmallBatchAt` descriptors + exact untouched-slot empty-batch guarantee).

Writes `[splitPtr, outDescPtr]` at `[h, h + 2)`, returns `hEnd ≤ h + asmFirstPhase3Space ...`,
preserves `OutSplitListsAt` with `avoid := fun a => a < h + 2 ∨ TRpot.foot tourH tx_pot' a`, and
bounds the combined amortized cost against `branchStepCharge` and `asmTourRepWithPot`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

public section

set_option maxHeartbeats 1200000 in
theorem asmFirstPhase3_runs {w depth slotCap vCap eCap bBun bTour bOut bCopy bTourStep
      fDelTriples fBuildGroups bunH tourH batch words edits editWords spPtr delEdgesPtr h pos : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpBun : p.HasAt bBun (bundleProcs bBun (tourOp bTour 4) (tourOp bTour 12) (tourOp bTour 10)))
    (hpT : HasTourProcs p bTour)
    (hpO : OutProcsAt p bOut (tourOp bTour 8) (tourOp bTour 7) (tourOp bTour 11) (tourOp bTour 9))
    (hpC : p.HasAt bCopy [copyWords])
    (hpTS : p.HasAt bTourStep (asmFirstTourBlockProcs bTourStep bTour bOut bCopy))
    (hfDel : p.procs[fDelTriples]? = some (asmFirstBuildDelTriplesStmt (bBun + bundleIdxReadParent)))
    (hfGrp : p.procs[fBuildGroups]? = some (asmFirstBuildGroupsStmt (bBun + bundleOffSort)))
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {U : List Update} {ord : ℕ → List End} {ed : List OrdEdit}
    {mk : Finset End} {delEdges : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap}
    {tx_pot : (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).τ}
    {mem₀ : ℕ → ℕ}
    (hready : OutStepReady sp tr U ord (applyOrdEdits ord ed))
    (hOFB : OrdEditsForBatch tr.cs.G U ed)
    (hOVF : OrdEditsValidFor vCap eCap ord ed)
    (hRlt : ∀ r ∈ (compLSFBatch tr.cs U).RF.R, r < vCap)
    (hE_old : ∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E, e < eCap)
    (hE_new : ∀ e ∈ (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).E, e < eCap)
    (hDel_set : delEdges.toFinset = batchDeletes U)
    (hDel_cap : ∀ e ∈ delEdges, e < eCap)
    (hMarks : OutMarksOf ⟨coreTour ord tr.cs.RF, mk⟩ (outCoreOrder tr ord) tr.S_cur.E)
    (hinv0 : bunRestartInv vCap eCap S₀ (outCoreOrder tr ord))
    (hMatch0 : ∀ q ∈ activePairs (stepBundleTree sp tr U ord (applyOrdEdits ord ed)).state,
      ∃ (hs : slotOf q < slotCap) (B : BundleState), S₀ ⟨slotOf q, hs⟩ = some B ∧ BunAgree B (tr.bun q))
    (hBunNone : ∀ j : Fin slotCap, S₀ j ≠ none →
      ∃ q ∈ activePairs (stepBundleTree sp tr U ord (applyOrdEdits ord ed)).state, slotOf q = j.1)
    (hSlotInj : ∀ q₁ ∈ activePairs (stepBundleTree sp tr U ord (applyOrdEdits ord ed)).state,
      ∀ q₂ ∈ activePairs (stepBundleTree sp tr U ord (applyOrdEdits ord ed)).state,
        slotOf q₁ = slotOf q₂ → q₁ = q₂)
    (hBReady : ∀ j B₀, S₀ j = some B₀ → BundleStepReady tr.cs B₀ tr.k ord (applyOrdEdits ord ed) U)
    (hRepB : (bunTableHeadroomRep slotCap vCap eCap tr.k).rep bunH S₀ m mem₀)
    (hRepT : (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).rep
      tourH ⟨ord, tr.cs.RF, mk⟩ tx_pot mem₀)
    (hBatch : SmallBatchAt mem₀ batch tr.cs.G U words)
    (hEdits : OrdEditsAt mem₀ edits ed editWords)
    (hSpAt : SplitEntriesAt mem₀ spPtr (canonSplitList tr.cs U))
    (hDelAt : ListAt mem₀ delEdgesPtr delEdges)
    (hw16 : 16 ≤ 2 ^ w) (hw_sq : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (htourH_w : tourH < 2 ^ w) (_hslotCap_w : slotCap < 2 ^ w)
    (hBatch_le : batch + words ≤ h) (hEdits_le : edits + editWords ≤ h)
    (hSp_le : spPtr + splitEntriesWords (canonSplitList tr.cs U) ≤ h)
    (hDel_le : delEdgesPtr + delEdges.length ≤ h)
    (htbl_le : bunH + bundleTableFixedSize slotCap eCap ≤ h)
    (hblks_w : ∀ js : Fin slotCap, ∀ q c, m.slotBlocks js = some (q, c) → q + bundleSlotBlockSize c < 2 ^ w)
    (hfootB_lt : ∀ a, (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m a → a < h)
    (hfootT_lt : ∀ a, (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).foot tourH tx_pot a → a < h)
    (hdisjBT : ∀ a, (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m a →
      ¬ (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).foot tourH tx_pot a)
    (hBF : ∀ a, batch ≤ a → a < batch + words →
      ¬ (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).foot tourH tx_pot a)
    (hEF : ∀ a, edits ≤ a → a < edits + editWords →
      ¬ (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).foot tourH tx_pot a)
    (hSF : ∀ a, spPtr ≤ a → a < spPtr + splitEntriesWords (canonSplitList tr.cs U) →
      ¬ (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).foot tourH tx_pot a)
    (hDF : ∀ a, delEdgesPtr ≤ a → a < delEdgesPtr + delEdges.length →
      ¬ (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).foot tourH tx_pot a)
    (hZero : ZeroFrom mem₀ h)
    (hSpace : h + asmFirstPhase3Space slotCap vCap eCap words editWords delEdges.length < 2 ^ w) :
    let ord' := applyOrdEdits ord ed
    let info := stepBundleTree sp tr U ord ord'
    let keep := outKeep sp tr U ord ord'
    let G₁ := tr.S_cur.applyBatch ((outDelList sp tr U ord ord').map Update.delete)
    let S' := tableAfterStepRuns tr.cs tr.k ord' U S₀
    let TRpot := asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap
    ∃ hEnd st' cost tx_pot' splitPtr outDescPtr mk' M Ys, ∃ touched : List ℕ,
      Runs w p ω (asmFirstPhase3Stmt fDelTriples fBuildGroups (bTourStep + 2) (bBun + bundleIdxStep))
        (startState [bunH, slotCap, vCap, tourH, batch, words, edits, editWords, spPtr, delEdgesPtr, delEdges.length, h] mem₀ pos)
        (.returned hEnd) st' cost ∧
      (bunTableHeadroomRep slotCap vCap eCap tr.k).rep bunH S' m st'.mem ∧
      bunRestartInv vCap eCap S' (outCoreOrder info.state ord') ∧
      BunTableMatches info.state slotOf S' ∧
      TRpot.rep tourH ⟨ord', info.state.cs.RF, mk'⟩ tx_pot' st'.mem ∧
      keep ⊆ M ∧ M ⊆ tr.S_cur.E ∧
      OutMarksOf ⟨coreTour ord' info.state.cs.RF, mk'⟩ (outCoreOrder info.state ord') M ∧
      OutSplitListsAt st'.mem hEnd (fun a => a < h + 2 ∨ TRpot.foot tourH tx_pot' a)
        keep tr.S_cur.E splitPtr G₁ (restrictSplits keep info.U_core) Ys ∧
      (Ys.map List.length).sum ≤
        G₁.batchEnc (restrictSplits keep info.U_core) +
          markPot keep tr.S_cur.E (coreGraph tr.cs.G tr.cs.lsf) ∧
      st'.mem h = splitPtr ∧ st'.mem (h + 1) = outDescPtr ∧
      h + 2 ≤ outDescPtr ∧ outDescPtr + 1 + 3 * slotCap ≤ hEnd ∧
      touched.Nodup ∧ (∀ s ∈ touched, s < slotCap) ∧
      st'.mem outDescPtr = touched.length ∧
      (∀ i (hi : i < touched.length),
        let s := touched[i]'hi
        ∃ (hs : s < slotCap) (batchPtr totalWords : ℕ),
          st'.mem (outDescPtr + 1 + 3 * i) = s ∧
          st'.mem (outDescPtr + 1 + 3 * i + 1) = batchPtr ∧
          st'.mem (outDescPtr + 1 + 3 * i + 2) = totalWords ∧
          outDescPtr + 1 + 3 * slotCap ≤ batchPtr ∧ batchPtr + totalWords ≤ hEnd ∧
          ∀ B₀, S₀ ⟨s, hs⟩ = some B₀ →
            SmallBatchAt st'.mem batchPtr B₀.graph (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 totalWords) ∧
      (∀ j B₀, S₀ j = some B₀ → j.1 ∉ touched →
        (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 = []) ∧
      (∀ j : Fin slotCap, S₀ j = none → j.1 ∉ touched) ∧
      h + 2 ≤ hEnd ∧
      hEnd ≤ h + asmFirstPhase3Space slotCap vCap eCap words editWords delEdges.length ∧
      ZeroFrom st'.mem hEnd ∧
      (∀ a, TRpot.foot tourH tx_pot' a → TRpot.foot tourH tx_pot a ∨ (h + 2 ≤ a ∧ a < hEnd)) ∧
      (∀ a < h, ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m a →
        ¬ TRpot.foot tourH tx_pot a → st'.mem a = mem₀ a) ∧
      cost + 70 * touched.length + (bunTableHeadroomRep slotCap vCap eCap tr.k).phi bunH m st'.mem +
          TRpot.phi tourH tx_pot' st'.mem ≤
        buildDelTriplesCost tourBundleSpec eCap delEdges.length +
        buildGroupsCost (canonSplitList tr.cs U).length +
        tourBlockStepMul *
          ((Ys.map List.length).sum + tr.S_cur.batchEnc info.U_S + words + editWords + 1) *
          ordStoreLog eCap +
        bundleStepCost tourBundleSpec eCap delEdges.length
          (splitGroupsOf ((canonSplitList tr.cs U).map fun s => (s.kept, s.fresh))) +
        bunPhiMul * branchStepCharge sp tr U ord ord' +
        bundleScanPotMul tourBundleSpec eCap *
          (2 * (U.length + (canonSplitList tr.cs U).length) * (Nat.log 2 (4 * eCap) + 2)) + 120 +
        (bunTableHeadroomRep slotCap vCap eCap tr.k).phi bunH m mem₀ +
        TRpot.phi tourH tx_pot mem₀ := by
  intro ord' info keep G₁ S' TRpot
  have hready0 := hready
  obtain ⟨C_lsst, ℓ₀, hI, hBU, hOB, _, _, _, _⟩ := hready
  have hI' := compLSFBatch_inv hI hBU
  obtain ⟨ρ, σ, hρ, hσ, hrot0⟩ := hOB
  set L := canonSplitList tr.cs U
  set pairs := L.map fun s => (s.kept, s.fresh)
  set gs := splitGroupsOf pairs
  set oldRoots := splitOldRoots pairs
  set cord := outCoreOrder tr ord
  set cord' := outCoreOrder info.state ord'
  have hL_le_vCap : L.length ≤ vCap :=
    asmFirstCanonSplitList_length_le_vCap hI hBU ⟨ρ, σ, hρ, hσ, hrot0⟩ hRlt
  have hL_le_vCap' : L.length ≤ vCap := hL_le_vCap
  have hSpace_un : h + (2 + buildDelTriplesSpace tourBundleSpec delEdges.length +
      buildGroupsSpace vCap vCap + tourBlockStepSpace vCap eCap words editWords +
      (1 + 3 * slotCap) + phase3BunStepSpaceBound slotCap vCap eCap) < 2 ^ w := by
    unfold asmFirstPhase3Space at hSpace; exact hSpace
  have hSp_words : splitEntriesWords L = 1 + 4 * L.length := rfl
  have hvCapW : vCap < 2 ^ w := by nlinarith
  have heCapW : 2 * eCap < 2 ^ w := by nlinarith
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  have hT_ok0 : TourCordOK ord tr.cs.RF cord := ⟨tr.cs, outCoreOrder_coreCordOf hI ρ hρ, rfl⟩
  let σ' : Rotation info.state.cs.G := (compLSFBatch_G tr.cs U).symm ▸ σ
  have hσ' : σ'.order = ord' := by
    dsimp only [σ']
    have hcast : ∀ {G H : MGraph} (he : G = H) (τ : Rotation G), (he ▸ τ : Rotation H).order = τ.order := by
      intro G H he τ; cases he; rfl
    exact (hcast _ σ).trans hσ
  have hT_ok1 : TourCordOK ord' info.state.cs.RF cord' :=
    ⟨info.state.cs, outCoreOrder_coreCordOf hI' σ' hσ', rfl⟩
  -- Split-group model facts
  obtain ⟨hL_vCap, hOldList_eq, hgs_pos, hgs_lt, hgs_nd, hgs_sub, hgs_disj,
      hold_len, hold_nd, hold_sub, htot_le, hwords_le,
      ⟨addG, addR, hgrp_sum, hrest_le, htot_add⟩, hbin⟩ :=
    splitGroups_model_spec (w := w) (sparsify := sp) (vCap := vCap) (eCap := eCap) (S₀ := S₀)
      hI hBU ⟨ρ, σ, hρ, hσ, hrot0⟩ hRlt hvCapW hE_old hE_new hBReady
  have htot_le' : groupsTotalLen gs ≤ 2 * L.length := htot_le
  have hwords_le' : groupsWords gs ≤ 3 * L.length := hwords_le
  have hcord'_bounds : ∀ v x, x ∈ cord' v → v < vCap ∧ x.1 < eCap := fun v x hx => by
    rw [show cord' v = outCoreOrder info.state ord' v from rfl,
      outCoreOrder_eq_coreRotation hI' σ' hσ'] at hx
    obtain ⟨hxE, hsrc⟩ := ((coreRotation (L := info.state.cs.lsf) σ' hI'.hG_val (compLSF_RF_isRSF hI')).mem_order v x).mp hx
    have hG'V : (coreGraph info.state.cs.G info.state.cs.lsf).V = info.state.cs.RF.R := rfl
    have hvR : v ∈ info.state.cs.RF.R := by
      rw [← hG'V, ← hsrc]
      have hval := coreGraph_isValid (L := info.state.cs.lsf) hI'.hG_val (compLSF_RF_isRSF hI')
      cases hx2 : x.2
      · simp only [MGraph.src, hx2]; exact (hval x.1 hxE).2
      · simp only [MGraph.src, hx2]; exact (hval x.1 hxE).1
    exact ⟨hRlt v hvR, hE_new x.1 hxE⟩
  -- Initial state & r12 := h + 2
  set args0 := [bunH, slotCap, vCap, tourH, batch, words, edits, editWords, spPtr, delEdgesPtr, delEdges.length, h]
  set st0 := startState args0 mem₀ pos
  set delPtr := h + 2
  set st1 : State := { st0 with regs := Function.update st0.regs 12 delPtr }
  have ha12 : Runs w p ω (.assign 12 (.bin .add (.reg 11) (.const 2))) st0 .normal st1 4 :=
    runs_assign_iff.mpr ⟨delPtr, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st0, args0, startState]))
      (Expr.eval_const h2w) (by omega), rfl, rfl, rfl⟩
  -- Call 1: `fDelTriples [bunH, tourH, delEdgesPtr, nDel, delPtr]`
  let htour0 := tourDS_asmTourCordView_bundleTourAt w vCap eCap p bTour hpT ord tr.cs.RF cord mk
  have hrepT0 : htour0.rep.rep tourH cord tx_pot.1 mem₀ := ⟨rfl, hT_ok0, hRepT.1⟩
  obtain ⟨hp2, stD, cD, tx1, dels, hrunD, hdels_len, hdels_fst, hdels_mem, hdels_lt, hdels_par,
      hRepB1, hRepT1, hhp2_lo, hhp2_hi, hz1, hft1, hfr1, hfrB1, hcD⟩ :=
    asmFirstBuildDelTriples_runs (TS := tourBundleSpec) (h := delPtr) (pos := st1.pos) (ω := ω) hpBun htour0
      hw16 hvCapW heCapW (by omega) htourH_w hRepB hrepT0 hinv0
      (fun a ha => lt_trans (hfootB_lt a ha) (by omega))
      (fun a ha => lt_trans (hfootT_lt a ha) (by omega))
      hdisjBT hDelAt (by omega) hDF hDel_cap (fun a ha => hZero a (by omega)) (by omega)
  set st2 : State := ⟨stD.mem, Function.update st1.regs 13 hp2, stD.pos⟩
  have hcall1 : Runs w p ω (.call 13 fDelTriples [.reg 0, .reg 3, .reg 9, .reg 10, .reg 12])
      st1 .normal st2 (argsSize [.reg 0, .reg 3, .reg 9, .reg 10, .reg 12] + cD + 1) :=
    runs_call_iff.mpr ⟨[bunH, tourH, delEdgesPtr, delEdges.length, delPtr], _, .returned hp2, stD, cD,
      by simp [evalArgs, Expr.eval, st1, st0, args0, startState], hfDel, hrunD, rfl, rfl, rfl⟩
  -- Call 2: `fBuildGroups [spPtr, vCap, hp2]`
  have hpSort : p.HasAt (bBun + bundleOffSort) (sortProcs (bBun + bundleOffSort)) := fun i hi => by
    have h1 := hpBun i (by simp only [bundleProcs, List.length_append]; omega)
    simp only [bundleProcs] at h1
    rw [List.getElem_append_left (by simp only [List.length_append]; omega),
      List.getElem_append_left hi] at h1
    simpa [bundleOffSort] using h1
  have hSp1 : SplitEntriesAt stD.mem spPtr L := by
    refine ⟨(hfr1 spPtr (by omega) (hSF spPtr (le_refl _) (by omega))).trans hSpAt.1, fun i hi => ?_⟩
    obtain ⟨h0, h1, h2, h3⟩ := hSpAt.2 i hi
    exact ⟨(hfr1 _ (by omega) (hSF _ (by omega) (by omega))).trans h0,
      (hfr1 _ (by omega) (hSF _ (by omega) (by omega))).trans h1,
      (hfr1 _ (by omega) (hSF _ (by omega) (by omega))).trans h2,
      (hfr1 _ (by omega) (hSF _ (by omega) (by omega))).trans h3⟩
  have hGrpSpace : hp2 + buildGroupsSpace vCap L.length < 2 ^ w := by
    have : buildGroupsSpace vCap L.length ≤ buildGroupsSpace vCap vCap := by unfold buildGroupsSpace; omega
    omega
  obtain ⟨hp3, groupPtr, stG, cG, hrunG, hnG_mem, hgp_mem, hgs_mem1, hgp_lo, hhp3_lo, hhp3_hi,
      hz2, hfr2, hcG⟩ :=
    asmFirstBuildGroups_runs (pos := st2.pos) (ω := ω) hpSort hw16 hSp1 (by omega)
      hL_vCap hOldList_eq hz1 hGrpSpace
  have hgs_mem1' : readGroups stG.mem groupPtr gs.length = gs := hgs_mem1
  have hhp3_lo' : groupPtr + groupsWords gs = hp3 := hhp3_lo
  have hhp3_hi' : hp3 ≤ hp2 + buildGroupsSpace vCap L.length := hhp3_hi
  set st3 : State := ⟨stG.mem, Function.update st2.regs 14 hp3, stG.pos⟩
  have hcall2 : Runs w p ω (.call 14 fBuildGroups [.reg 8, .reg 2, .reg 13])
      st2 .normal st3 (argsSize [.reg 8, .reg 2, .reg 13] + cG + 1) :=
    runs_call_iff.mpr ⟨[spPtr, vCap, hp2], _, .returned hp3, stG, cG,
      by simp [evalArgs, Expr.eval, st2, st1, st0, args0, startState], hfGrp, hrunG, rfl, rfl, rfl⟩
  -- Call 3: `fTourStep [tourH, batch, words, edits, editWords, spPtr, hp3]`
  have hT_foot1_lt : ∀ a, (tourAsmRep vCap eCap).foot tourH tx1 a → a < hp2 := fun a ha => by
    rcases hft1 a ha with h0 | ⟨_, hhi⟩; exact lt_of_lt_of_le (hfootT_lt a h0) (by omega); exact hhi
  have hRepT2 : (tourAsmRep vCap eCap).rep tourH ⟨ord, tr.cs.RF, mk⟩ tx1 stG.mem :=
    (tourAsmRep_local vCap eCap tourH _ tx1 stD.mem stG.mem
      fun a ha => (hfr2 a (hT_foot1_lt a ha)).symm).1 hRepT1.2.2
  have hBatch2 : BatchAt stG.mem batch tr.cs.G U words :=
    (smallBatchAt_of_agree hBatch fun a ha1 ha2 =>
      (hfr2 a (by omega)).trans (hfr1 a (by omega) (hBF a ha1 ha2))).1
  have hEdits2 : OrdEditsAt stG.mem edits ed editWords :=
    ordEditsAt_of_agree hEdits fun a ha1 ha2 =>
      (hfr2 a (by omega)).trans (hfr1 a (by omega) (hEF a ha1 ha2))
  have hSp2 : SplitEntriesAt stG.mem spPtr L := by
    refine ⟨(hfr2 spPtr (by omega)).trans hSp1.1, fun i hi => ?_⟩
    obtain ⟨h0, h1, h2, h3⟩ := hSp1.2 i hi
    exact ⟨(hfr2 _ (by omega)).trans h0, (hfr2 _ (by omega)).trans h1,
      (hfr2 _ (by omega)).trans h2, (hfr2 _ (by omega)).trans h3⟩
  have hBF1 : ∀ a, batch ≤ a → a < batch + words → ¬ (tourAsmRep vCap eCap).foot tourH tx1 a :=
    fun a ha1 ha2 hf => by rcases hft1 a hf with h0 | ⟨hlo, _⟩; exact hBF a ha1 ha2 h0; omega
  have hSF1 : ∀ a, spPtr ≤ a → a < spPtr + 1 + 4 * L.length → ¬ (tourAsmRep vCap eCap).foot tourH tx1 a :=
    fun a ha1 ha2 hf => by rcases hft1 a hf with h0 | ⟨hlo, _⟩; exact hSF a ha1 (by rw [hSp_words]; omega) h0; omega
  have hRoomTS : hp3 + tourBlockStepSpace vCap eCap words editWords < 2 ^ w := by
    have : buildGroupsSpace vCap L.length ≤ buildGroupsSpace vCap vCap := by unfold buildGroupsSpace; omega
    omega
  obtain ⟨bdTS, hbdTS, hp4, stT, cT, tx2, splitPtr, mk', M, Ys, hrunT, hRepT3, hkeepM, hMScur,
      hMarks', hOutSplit, hYs_le, hsp_mem, hhp4_lo, hhp4_hi, hz3, hfr3, hft3, hcT⟩ :=
    asmFirstTourBlockStep_runs (pos := st3.pos) (ω := ω) hpT hpO hpC hpTS hw_sq sp
      hready0 hRlt hOFB hOVF hMarks hRepT2 (fun a ha => lt_of_lt_of_le (hT_foot1_lt a ha) (by omega))
      hz2 hBatch2 hEdits2 hSp2 (by omega) (by omega)
      (by have hEqL : (canonSplitList tr.cs U).length = L.length := rfl; rw [hSp_words] at hSp_le; omega) hBF1 hSF1 hRoomTS
  set st4 : State := ⟨stT.mem, Function.update st3.regs 15 hp4, stT.pos⟩
  have hcall3 : Runs w p ω (.call 15 (bTourStep + 2) [.reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 14])
      st3 .normal st4 (argsSize [.reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 14] + cT + 1) :=
    runs_call_iff.mpr ⟨[tourH, batch, words, edits, editWords, spPtr, hp3], bdTS, .returned hp4, stT, cT,
      by simp [evalArgs, Expr.eval, st3, st2, st1, st0, args0, startState], hbdTS, hrunT, rfl, rfl, rfl⟩
  -- Load `nG = mem[hp2]`, `groupPtr = mem[hp2 + 1]`, compute `hp5 = hp4 + 1 + 3 * slotCap`
  have hnt_hp2 : ¬ (tourAsmRep vCap eCap).foot tourH tx1 hp2 := fun hf => by have := hT_foot1_lt hp2 hf; omega
  have hnt_hp2_1 : ¬ (tourAsmRep vCap eCap).foot tourH tx1 (hp2 + 1) := fun hf => by have := hT_foot1_lt (hp2 + 1) hf; omega
  have hnG_stT : stT.mem hp2 = gs.length := (hfr3 hp2 (by omega) hnt_hp2).trans hnG_mem
  have hgp_stT : stT.mem (hp2 + 1) = groupPtr := (hfr3 (hp2 + 1) (by omega) hnt_hp2_1).trans hgp_mem
  set hp5 := hp4 + 1 + 3 * slotCap
  have hhp5_w : hp5 < 2 ^ w := by
    have : buildGroupsSpace vCap L.length ≤ buildGroupsSpace vCap vCap := by unfold buildGroupsSpace; omega
    omega
  set st5 : State := { st4 with regs := Function.update st4.regs 16 gs.length }
  set st6 : State := { st5 with regs := Function.update st5.regs 17 groupPtr }
  set st7 : State := { st6 with regs := Function.update st6.regs 18 hp5 }
  have ha16 : Runs w p ω (.assign 16 (.load (.reg 13))) st4 .normal st5 3 :=
    runs_assign_iff.mpr ⟨gs.length, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [st4, st3, st2])) hnG_stT, rfl, rfl, rfl⟩
  have ha17 : Runs w p ω (.assign 17 (.load (.bin .add (.reg 13) (.const 1)))) st5 .normal st6 5 :=
    runs_assign_iff.mpr ⟨groupPtr, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2]))
      (Expr.eval_const h1w) (by omega)) hgp_stT, rfl, rfl, rfl⟩
  have ha18 : Runs w p ω (.assign 18 (.bin .add (.bin .add (.reg 15) (.const 1)) (.bin .mul (.const 3) (.reg 1)))) st6 .normal st7 8 :=
    runs_assign_iff.mpr ⟨hp5, Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st6, st5, st4])) (Expr.eval_const h1w) (by omega))
      (Expr.eval_mul (Expr.eval_const h3w) (Expr.eval_reg_of_eq (by simp [st6, st5, st4, st3, st2, st1, st0, args0, startState])) (by omega))
      (by omega), rfl, rfl, rfl⟩
  -- Call 4: `fBunStep [bunH, tourH, nDel, delPtr, gs.length, groupPtr, hp4, hp5]`
  let htour1 := tourDS_asmTourCordView_bundleTourAt w vCap eCap p bTour hpT ord' info.state.cs.RF cord' mk'
  have hRepT3_view : htour1.rep.rep tourH cord' tx2 stT.mem := ⟨rfl, hT_ok1, hRepT3⟩
  have hB_disj_tx1 : ∀ a, (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m a →
      ¬ (tourAsmRep vCap eCap).foot tourH tx1 a := fun a ha hf => by
    rcases hft1 a hf with h0 | ⟨hlo, _⟩; exact hdisjBT a ha h0; have := hfootB_lt a ha; omega
  have hB_ag_stT : ∀ a, (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m a → stT.mem a = stD.mem a :=
    fun a ha => (hfr3 a (lt_trans (hfootB_lt a ha) (by omega)) (hB_disj_tx1 a ha)).trans
      (hfr2 a (lt_trans (hfootB_lt a ha) (by omega)))
  have hRepB3 : (bunTableHeadroomRep slotCap vCap eCap tr.k).rep bunH S₀ m stT.mem :=
    (bunTableHeadroomRep_local slotCap vCap eCap tr.k bunH S₀ m stD.mem stT.mem
      fun a ha => (hB_ag_stT a ha).symm).1 hRepB1
  have hphiB_eq : (bunTableHeadroomRep slotCap vCap eCap tr.k).phi bunH m stT.mem =
      (bunTableHeadroomRep slotCap vCap eCap tr.k).phi bunH m mem₀ := by
    have h1 := (bunTableHeadroomRep_local slotCap vCap eCap tr.k bunH S₀ m stD.mem stT.mem
      fun a ha => (hB_ag_stT a ha).symm).2
    have h2 := (bunTableHeadroomRep_local slotCap vCap eCap tr.k bunH S₀ m mem₀ stD.mem
      fun a ha => (hfrB1 a ha).symm).2
    exact h1.symm.trans h2.symm
  have hphiT1_eq : (tourAsmRep vCap eCap).phi tourH tx1 stG.mem = (tourAsmRep vCap eCap).phi tourH tx1 stD.mem :=
    (tourAsmRep_local vCap eCap tourH ⟨ord, tr.cs.RF, mk⟩ tx1 stD.mem stG.mem
      fun a ha => (hfr2 a (hT_foot1_lt a ha)).symm).2.symm
  have hD_eq : (dels.map Prod.fst).toFinset = batchDeletes U := by rw [hdels_fst]; exact hDel_set
  have hdels_mem3 : readDelTriples stT.mem delPtr delEdges.length = dels := by
    rw [← hdels_mem]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    have hnt0 : ¬ (tourAsmRep vCap eCap).foot tourH tx1 (delPtr + 3 * i) := fun hf => by
      rcases hft1 _ hf with h0 | ⟨hlo, _⟩; have := hfootT_lt _ h0; omega; omega
    have hnt1 : ¬ (tourAsmRep vCap eCap).foot tourH tx1 (delPtr + 3 * i + 1) := fun hf => by
      rcases hft1 _ hf with h0 | ⟨hlo, _⟩; have := hfootT_lt _ h0; omega; omega
    have hnt2 : ¬ (tourAsmRep vCap eCap).foot tourH tx1 (delPtr + 3 * i + 2) := fun hf => by
      rcases hft1 _ hf with h0 | ⟨hlo, _⟩; have := hfootT_lt _ h0; omega; omega
    have e0 := (hfr3 (delPtr + 3 * i) (by omega) hnt0).trans (hfr2 (delPtr + 3 * i) (by omega))
    have e1 := (hfr3 (delPtr + 3 * i + 1) (by omega) hnt1).trans (hfr2 (delPtr + 3 * i + 1) (by omega))
    have e2 := (hfr3 (delPtr + 3 * i + 2) (by omega) hnt2).trans (hfr2 (delPtr + 3 * i + 2) (by omega))
    simp only [e0, e1, e2]
  have hgs_mem3 : readGroups stT.mem groupPtr gs.length = gs := by
    have hcongr : ∀ (ptr : ℕ), hp2 ≤ ptr →
        (∀ a, ptr ≤ a → a < hp3 → stT.mem a = stG.mem a) →
        ∀ n, ptr + groupsWords (readGroups stG.mem ptr n) ≤ hp3 →
          readGroups stT.mem ptr n = readGroups stG.mem ptr n := by
      intro ptr _ hag n
      induction n generalizing ptr with
      | zero => intro _; rfl
      | succ n ih =>
        intro hle
        have hlen_lt : ptr + 1 + stG.mem ptr ≤ hp3 := by
          simp only [readGroups, groupsWords, List.map_cons, List.sum_cons, List.length_map, List.length_range] at hle; omega
        have h0 : stT.mem ptr = stG.mem ptr := hag ptr (le_refl _) (by omega)
        simp only [readGroups, h0]
        congr 1
        · refine List.map_congr_left fun j hj => ?_
          have hj' := List.mem_range.mp hj
          exact hag (ptr + 1 + j) (by omega) (by omega)
        · apply ih (ptr + 1 + stG.mem ptr) (by omega) (fun a ha1 ha2 => hag a (by omega) ha2)
          simp only [readGroups, groupsWords, List.map_cons, List.sum_cons, List.length_map, List.length_range] at hle ⊢
          omega
    exact (hcongr groupPtr (by omega)
      (fun a ha1 ha2 => hfr3 a ha2 (fun hf => by have := hT_foot1_lt a hf; omega)) gs.length
      (by rw [hgs_mem1']; omega)).trans hgs_mem1'
  have hT_foot2_lt : ∀ a, (tourAsmRep vCap eCap).foot tourH tx2 a → a < hp4 := fun a ha => by
    rcases hft3 a ha with h1 | ⟨_, hhi⟩; exact lt_of_lt_of_le (hT_foot1_lt a h1) (by omega); exact hhi
  have hT_foot2_disj_B : ∀ a, (tourAsmRep vCap eCap).foot tourH tx2 a →
      ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m a := fun a ha hb => by
    rcases hft3 a ha with h1 | ⟨hlo, _⟩; exact hB_disj_tx1 a hb h1; have := hfootB_lt a hb; omega
  have hT_foot2_disj_grp : ∀ a, (tourAsmRep vCap eCap).foot tourH tx2 a →
      a < groupPtr ∨ groupPtr + groupsWords gs ≤ a := fun a ha => by
    rcases hft3 a ha with h1 | ⟨hlo, _⟩
    · exact Or.inl (lt_of_lt_of_le (hT_foot1_lt a h1) (by omega))
    · exact Or.inr (by omega)
  have hcord'_nd : ∀ v, (cord' v).Nodup := fun v => by
    rw [show cord' v = outCoreOrder info.state ord' v from rfl, outCoreOrder_eq_coreRotation hI' σ' hσ']
    exact (coreRotation (L := info.state.cs.lsf) σ' hI'.hG_val (compLSF_RF_isRSF hI')).nodup v
  have hsrc_iff_all : ∀ j B₀, S₀ j = some B₀ →
      ∀ x ∈ Bundle.edgeEnds (B₀.edges \ batchDeletes U), ∀ v,
        x ∈ cord' v ↔ (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).src x = v := by
    intro j B₀ hS₀ x hx v
    have hpart := (bundleRunsStep_spec (hBReady j B₀ hS₀)).1.1 σ' hI'.hG_val (compLSF_RF_isRSF hI') hσ'
    have hxE : x.1 ∈ (coreGraph info.state.cs.G info.state.cs.lsf).E := by
      have hsub := hpart.1; rw [(bundleRunsStep_spec (hBReady j B₀ hS₀)).2.2.2.2.1] at hsub
      exact hsub ((Bundle.mem_edgeEnds _ _).mp hx)
    exact outCoreOrder_mem_iff_src hI' σ' hσ' hxE v
  have hdisjS₀ : ∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ B₁ B₂,
      S₀ j₁ = some B₁ → S₀ j₂ = some B₂ → Disjoint B₁.edges B₂.edges :=
    hRepB.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hB_cap_S₀ : ∀ j B₀, S₀ j = some B₀ → ∀ e ∈ B₀.edges, e < eCap := fun j B₀ hS₀ e he => by
    have hSlot := hRepB.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j
    rw [hS₀] at hSlot
    cases hm : m.slotBlocks j with
    | none => simp [hm] at hSlot
    | some pc =>
      simp only [hm] at hSlot
      exact hSlot.2.1.choose_spec.2.2.1 e he
  have hhp5_sp : ∀ (maxIdxs touched : List ℕ),
      maxIdxs.length = gs.length →
      (∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length) →
      touched.Nodup → (∀ s ∈ touched, s < slotCap) →
      let candSet := addCandsForGroups (tableDelEdges S₀ (batchDeletes U)) cord' gs maxIdxs (fun _ => ∅) gs.length
      let scanLen := slotScannedEnds S₀ (batchDeletes U) cord' gs maxIdxs
      hp5 + bundleStepSpace tourBundleSpec S₀ (batchDeletes U) candSet scanLen cord' gs touched < 2 ^ w := by
    intro maxIdxs touched _ hmax_lt hndT hltT
    have hle : bundleStepSpace tourBundleSpec S₀ (batchDeletes U)
        (addCandsForGroups (tableDelEdges S₀ (batchDeletes U)) cord' gs maxIdxs (fun _ => ∅) gs.length)
        (slotScannedEnds S₀ (batchDeletes U) cord' gs maxIdxs) cord' gs touched ≤
        phase3BunStepSpaceBound slotCap vCap eCap :=
      bundleStepSpace_le_phase3 (vCap := vCap) (eCap := eCap) hdisjS₀ hB_cap_S₀
        hcord'_nd (fun v x hx => (hcord'_bounds v x hx).2) hgs_nd hgs_disj (by clear * - htot_le' hL_le_vCap'; omega)
        hmax_lt hndT hltT hsrc_iff_all hbin
    have hbg_le : buildGroupsSpace vCap L.length ≤ buildGroupsSpace vCap vCap := by unfold buildGroupsSpace; omega
    clear * - hSpace_un hhp2_hi hhp3_hi' hhp4_hi hle hbg_le
    omega
  obtain ⟨bdB, hbdB, stB, cB, hp6, tx3, maxIdxs, touched, hrunB, hmax_lt, hndT, hltT, huntouched,
      htouchNone, hRepB4, hRepT4, hinv', hMatch', hhp6_lo, hhp6_hi, hz4, hft4, hout0, hdescs, hfr4, hcB⟩ :=
    asmFirstBunStepModel_runs (TS := tourBundleSpec) (sparsify := sp) (pos := st7.pos) (ω := ω)
      hpBun htour1 hD_eq hinv0 hMatch0 hBReady hcord'_bounds hw16 htourH_w hpk_w
      (by omega) hblks_w (by omega) (by omega) (by omega)
      (fun a ha => lt_trans (hfootB_lt a ha) (by omega)) (by omega) (by omega) (by omega)
      (fun a ha1 _ hb => by have := hfootB_lt a hb; omega)
      (fun a ha1 _ hb => by have := hfootB_lt a hb; omega)
      (fun a ha1 _ hb => by have := hfootB_lt a hb; omega)
      (fun a ha => lt_trans (hT_foot2_lt a ha) (by omega))
      hT_foot2_disj_B hT_foot2_disj_grp
      (fun a ha => Or.inl (hT_foot2_lt a ha))
      (fun a ha => hz3 a (by omega)) hRepT3_view hRepB3
      hdels_len hdels_mem3 hdels_lt (fun i hi _ js B hSB heB => hdels_par i hi js B hSB heB)
      hgs_mem3 hgs_pos hgs_lt hgs_nd hgs_sub hgs_disj hold_len hold_nd hold_sub
      hgrp_sum hrest_le hbin hhp5_sp
  set st8 : State := ⟨stB.mem, Function.update st7.regs 19 hp6, stB.pos⟩
  have hcall4 : Runs w p ω (.call 19 (bBun + bundleIdxStep)
      [.reg 0, .reg 3, .reg 10, .reg 12, .reg 16, .reg 17, .reg 15, .reg 18])
      st7 .normal st8 (argsSize [.reg 0, .reg 3, .reg 10, .reg 12, .reg 16, .reg 17, .reg 15, .reg 18] + cB + 1) :=
    runs_call_iff.mpr ⟨[bunH, tourH, delEdges.length, delPtr, gs.length, groupPtr, hp4, hp5],
      bdB, .returned hp6, stB, cB,
      by simp [evalArgs, Expr.eval, st7, st6, st5, st4, st3, st2, st1, st0, args0, startState],
      hbdB, hrunB, rfl, rfl, rfl⟩
  -- Epilogue: store `splitPtr = mem[hp3]` at `h`, `outDescPtr = hp4` at `h + 1`, return `hp6`
  have hnt_hp3_2 : ¬ (tourAsmRep vCap eCap).foot tourH tx2 hp3 := fun hf => by
    rcases hft3 hp3 hf with h1 | ⟨hlo, _⟩; have := hT_foot1_lt hp3 h1; omega; omega
  have hsp_stB : stB.mem hp3 = splitPtr :=
    (hfr4 hp3 (by omega) (fun hb => by have := hfootB_lt hp3 hb; omega) (Or.inl (by omega)) hnt_hp3_2).trans hsp_mem
  set mEnd1 := Function.update stB.mem h splitPtr
  set mEnd := Function.update mEnd1 (h + 1) hp4
  set stEnd : State := ⟨mEnd, st8.regs, st8.pos⟩
  have hsOut1 : Runs w p ω (.store (.reg 11) (.load (.reg 14))) st8 .normal ⟨mEnd1, st8.regs, st8.pos⟩ 4 :=
    runs_store_iff.mpr ⟨h, splitPtr, Expr.eval_reg_of_eq (by simp [st8, st7, st6, st5, st4, st3, st2, st1, st0, args0, startState]),
      Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [st8, st7, st6, st5, st4, st3])) hsp_stB, rfl, rfl, rfl⟩
  have hsOut2 : Runs w p ω (.store (.bin .add (.reg 11) (.const 1)) (.reg 15))
      ⟨mEnd1, st8.regs, st8.pos⟩ .normal stEnd 5 :=
    runs_store_iff.mpr ⟨h + 1, hp4, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st8, st7, st6, st5, st4, st3, st2, st1, st0, args0, startState]))
      (Expr.eval_const h1w) (by omega), Expr.eval_reg_of_eq (by simp [st8, st7, st6, st5, st4]), rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.reg 19)) stEnd (.returned hp6) stEnd 2 :=
    runs_ret_iff.mpr ⟨hp6, Expr.eval_reg_of_eq (by simp [stEnd, st8]), rfl, rfl, rfl⟩
  have hfull :=
    runs_seq_iff.mpr (Or.inr ⟨st1, _, _, ha12,
    runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hcall1,
    runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hcall2,
    runs_seq_iff.mpr (Or.inr ⟨st4, _, _, hcall3,
    runs_seq_iff.mpr (Or.inr ⟨st5, _, _, ha16,
    runs_seq_iff.mpr (Or.inr ⟨st6, _, _, ha17,
    runs_seq_iff.mpr (Or.inr ⟨st7, _, _, ha18,
    runs_seq_iff.mpr (Or.inr ⟨st8, _, _, hcall4,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hsOut1,
    runs_seq_iff.mpr (Or.inr ⟨stEnd, _, _, hsOut2, hret, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- Final representations, footprints, `OutSplitListsAt`, `batchSplitCount` bound, and cost telescoping
  have hft_final : ∀ a, (tourAsmRep vCap eCap).foot tourH tx3 a →
      (tourAsmRep vCap eCap).foot tourH tx_pot.1 a ∨ (h + 2 ≤ a ∧ a < hp6) := fun a ha => by
    rcases hft4 a ha with h2 | ⟨hlo, hhi⟩
    · rcases hft3 a h2 with h1 | ⟨hlo, hhi⟩
      · rcases hft1 a h1 with h0 | ⟨hlo, hhi⟩
        · exact Or.inl h0
        · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, hhi⟩
  have hB_end_ag : ∀ a, (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m a → mEnd a = stB.mem a :=
    fun a ha => by
      have := hfootB_lt a ha
      dsimp only [mEnd, mEnd1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hT_end_ag : ∀ a, (tourAsmRep vCap eCap).foot tourH tx3 a → mEnd a = stB.mem a :=
    fun a ha => by
      have hne0 : a ≠ h := fun heq => by
        rcases hft_final a ha with h0 | ⟨hlo, _⟩; have := hfootT_lt a h0; omega; omega
      have hne1 : a ≠ h + 1 := fun heq => by
        rcases hft_final a ha with h0 | ⟨hlo, _⟩; have := hfootT_lt a h0; omega; omega
      dsimp only [mEnd, mEnd1]; rw [Function.update_of_ne hne1, Function.update_of_ne hne0]
  have hRepB_end : (bunTableHeadroomRep slotCap vCap eCap tr.k).rep bunH S' m mEnd :=
    (bunTableHeadroomRep_local slotCap vCap eCap tr.k bunH S' m stB.mem mEnd
      fun a ha => (hB_end_ag a ha).symm).1 hRepB4
  have hphiB_end : (bunTableHeadroomRep slotCap vCap eCap tr.k).phi bunH m mEnd =
      (bunTableHeadroomRep slotCap vCap eCap tr.k).phi bunH m stB.mem :=
    (bunTableHeadroomRep_local slotCap vCap eCap tr.k bunH S' m stB.mem mEnd
      fun a ha => (hB_end_ag a ha).symm).2.symm
  have hRepT_end_base : (tourAsmRep vCap eCap).rep tourH ⟨ord', info.state.cs.RF, mk'⟩ tx3 mEnd :=
    (tourAsmRep_local vCap eCap tourH ⟨ord', info.state.cs.RF, mk'⟩ tx3 stB.mem mEnd
      fun a ha => (hT_end_ag a ha).symm).1 hRepT4.2.2
  have hphiT_end_base : (tourAsmRep vCap eCap).phi tourH tx3 mEnd = (tourAsmRep vCap eCap).phi tourH tx3 stB.mem :=
    (tourAsmRep_local vCap eCap tourH ⟨ord', info.state.cs.RF, mk'⟩ tx3 stB.mem mEnd
      fun a ha => (hT_end_ag a ha).symm).2.symm
  set tx_pot' : TRpot.τ := (tx3, bundleScanPotMul tourBundleSpec eCap * tourPot info.state.cs.RF.R cord')
  have hRepT_end : TRpot.rep tourH ⟨ord', info.state.cs.RF, mk'⟩ tx_pot' mEnd :=
    ⟨hRepT_end_base, by rw [tourPotOfAbs_eq_of_tourCordOK mk' hT_ok1]⟩
  have hOutSplit_end : OutSplitListsAt mEnd hp6 (fun a => a < h + 2 ∨ TRpot.foot tourH tx_pot' a)
      keep tr.S_cur.E splitPtr G₁ (restrictSplits keep info.U_core) Ys := by
    refine outSplitListsAt_mono (by omega) ?_ ?_ hOutSplit
    · intro x hx hnav
      have hx_ge : hp3 + 1 ≤ x := by by_contra hlt; exact hnav (Or.inl (by omega))
      have hnt2 : ¬ (tourAsmRep vCap eCap).foot tourH tx2 x := fun hf => hnav (Or.inr hf)
      have hnb : ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m x := fun hb => by
        have := hfootB_lt x hb; omega
      dsimp only [mEnd, mEnd1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hfr4 x (by omega) hnb (Or.inl (by omega)) hnt2
    · intro x hx h2
      rcases h2 with hlt | hf3
      · exact Or.inl (by omega)
      · rcases hft4 x hf3 with h2' | ⟨hlo, _⟩
        · exact Or.inr h2'
        · omega
  have hhh_bun_le : bundleStepSpace tourBundleSpec S₀ (batchDeletes U)
      (addCandsForGroups (tableDelEdges S₀ (batchDeletes U)) cord' gs maxIdxs (fun _ => ∅) gs.length)
      (slotScannedEnds S₀ (batchDeletes U) cord' gs maxIdxs) cord' gs touched ≤
      phase3BunStepSpaceBound slotCap vCap eCap :=
    bundleStepSpace_le_phase3 (vCap := vCap) (eCap := eCap) hdisjS₀ hB_cap_S₀
      hcord'_nd (fun v x hx => (hcord'_bounds v x hx).2) hgs_nd hgs_disj (by omega)
      hmax_lt hndT hltT hsrc_iff_all hbin
  have hsum_bsc_le : (∑ j : Fin slotCap, match S₀ j with
      | none => 0
      | some B₀ => batchSplitCount (bundleCompStep tr.cs B₀ tr.k ord ord' U).1) ≤
      branchStepCharge sp tr U ord ord' := by
    set P_act := activePairs info.state
    let fSlot : Fin slotCap → ℕ := fun j => match S₀ j with
      | none => 0
      | some B₀ => batchSplitCount (bundleCompStep tr.cs B₀ tr.k ord ord' U).1
    let gPair : Finset ℕ × ℤ → ℕ := fun q => (tr.dyn q).G.batchEnc (info.U_B q)
    have hsum_P : (∑ j : Fin slotCap, fSlot j) ≤ ∑ q ∈ P_act, gPair q := by
      let S_img : Finset (Fin slotCap) := P_act.attach.image fun ⟨q, hq⟩ => ⟨slotOf q, (hMatch0 q hq).choose⟩
      have h1 : (∑ j : Fin slotCap, fSlot j) = ∑ j ∈ S_img, fSlot j := by
        symm
        refine Finset.sum_subset (Finset.subset_univ _) fun j _ hnj => ?_
        dsimp only [fSlot]
        cases hSj : S₀ j with
        | none => rfl
        | some B₀ =>
          exfalso; apply hnj
          obtain ⟨q, hq, hsq⟩ := hBunNone j (by simp [hSj])
          exact Finset.mem_image.mpr ⟨⟨q, hq⟩, Finset.mem_attach _ _, Fin.ext hsq⟩
      rw [h1, Finset.sum_image]
      · rw [← Finset.sum_attach P_act gPair]
        refine Finset.sum_le_sum fun ⟨q, hq⟩ _ => ?_
        obtain ⟨hs, B₀, hS₀, hag⟩ := hMatch0 q hq
        have hr := hBReady ⟨slotOf q, hs⟩ B₀ hS₀
        have hcomp := bunAgree_bundleCompStep_eq hag hr
        have hU_eq : (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 = info.U_B q := by
          simpa only [info, stepBundleTree] using hcomp.1
        change fSlot ⟨slotOf q, (hMatch0 q hq).choose⟩ ≤ gPair q
        have hfin : (⟨slotOf q, (hMatch0 q hq).choose⟩ : Fin slotCap) = ⟨slotOf q, hs⟩ := rfl
        rw [hfin]; dsimp only [fSlot, gPair]; simp only [hS₀, hU_eq]
        exact batchSplitCount_le_batchEnc (tr.dyn q).G (info.U_B q)
      · intro ⟨q₁, hq₁⟩ _ ⟨q₂, hq₂⟩ _ heq
        exact Subtype.ext (hSlotInj q₁ hq₁ q₂ hq₂ (congrArg Fin.val heq))
    have hact_eq : (∑ q ∈ P_act, gPair q) =
        info.state.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
          (tr.dyn (C, b)).G.batchEnc (info.U_B (C, b)) := by
      dsimp only [P_act, activePairs, gPair]
      rw [Finset.sum_biUnion]
      · refine Finset.sum_congr rfl fun C _ => ?_
        have hB_eq : info.state.activeBuckets C = tr.activeBuckets C := rfl
        rw [hB_eq, Finset.sum_image]
        intro b₁ _ b₂ _ h; exact (Prod.mk.inj h).2
      · intro C₁ _ C₂ _ hne
        exact Finset.disjoint_left.mpr fun p h1 h2 => by
          rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩
          rcases Finset.mem_image.mp h2 with ⟨_, _, h⟩
          exact hne (Prod.mk.inj h).1.symm
    have hch : (info.state.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        (tr.dyn (C, b)).G.batchEnc (info.U_B (C, b))) ≤ branchStepCharge sp tr U ord ord' := by
      dsimp only [branchStepCharge, info]
      exact le_trans (by omega) (Nat.le_mul_of_pos_right _ (one_le_bundleLogFactor _ _))
    exact hsum_P.trans (hact_eq ▸ hch)
  refine ⟨hp6, stEnd, _, tx_pot', splitPtr, hp4, mk', M, Ys, touched, hfull,
    hRepB_end, hinv', hMatch', hRepT_end, hkeepM, hMScur, hMarks', hOutSplit_end, hYs_le,
    by change mEnd h = splitPtr; dsimp only [mEnd, mEnd1]; rw [Function.update_of_ne (by omega), Function.update_self],
    by change mEnd (h + 1) = hp4; dsimp only [mEnd]; exact Function.update_self _ _ _,
    by omega, by omega, hndT, hltT,
    by change mEnd hp4 = touched.length; dsimp only [mEnd, mEnd1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hout0,
    fun i hi => by
      obtain ⟨hs, bp, tw, h0, h1, h2, hlo, hhi, hbat⟩ := hdescs i hi
      refine ⟨hs, bp, tw,
        by change mEnd _ = _; dsimp only [mEnd, mEnd1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact h0,
        by change mEnd _ = _; dsimp only [mEnd, mEnd1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact h1,
        by change mEnd _ = _; dsimp only [mEnd, mEnd1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact h2,
        hlo, hhi, fun B₀ hS₀ => smallBatchAt_of_agree (hbat B₀ hS₀) fun x hx1 hx2 => by
          change mEnd x = stB.mem x; dsimp only [mEnd, mEnd1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]⟩,
    huntouched, htouchNone, by omega,
    by unfold asmFirstPhase3Space
       have hbg_le : buildGroupsSpace vCap L.length ≤ buildGroupsSpace vCap vCap := by unfold buildGroupsSpace; omega
       have hhp6_b : hp6 ≤ hp5 + phase3BunStepSpaceBound slotCap vCap eCap :=
         hhp6_hi.trans (Nat.add_le_add_left hhh_bun_le hp5)
       clear * - hhp2_hi hhp3_hi' hhp4_hi hhp6_b hbg_le
       omega,
    fun a ha => by
      change mEnd a = 0; dsimp only [mEnd, mEnd1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hz4 a ha,
    hft_final,
    fun a ha hnb hnt => by
      change mEnd a = mem₀ a; dsimp only [mEnd, mEnd1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      have hnt1 : ¬ (tourAsmRep vCap eCap).foot tourH tx1 a := fun hf => by
        rcases hft1 a hf with h0 | ⟨hlo, _⟩; exact hnt h0; omega
      have hnt2 : ¬ (tourAsmRep vCap eCap).foot tourH tx2 a := fun hf => by
        rcases hft3 a hf with h1 | ⟨hlo, _⟩; exact hnt1 h1; omega
      exact (hfr4 a (by omega) hnb (Or.inl (by omega)) hnt2).trans
        ((hfr3 a (by omega) hnt1).trans ((hfr2 a (by omega)).trans (hfr1 a (by omega) hnt))),
    ?_⟩
  -- Cost + potential telescoping
  have hphi_tx0 : TRpot.phi tourH tx_pot mem₀ =
      (tourAsmRep vCap eCap).phi tourH tx_pot.1 mem₀ +
        bundleScanPotMul tourBundleSpec eCap * tourPot tr.cs.RF.R cord := by
    dsimp only [TRpot, asmTourRepWithPot]
    rw [hRepT.2, tourPotOfAbs_eq_of_tourCordOK mk hT_ok0]
  have hphi_tx1 : TRpot.phi tourH tx_pot' mEnd =
      (tourAsmRep vCap eCap).phi tourH tx3 stB.mem +
        bundleScanPotMul tourBundleSpec eCap * tourPot info.state.cs.RF.R cord' := by
    dsimp only [TRpot, asmTourRepWithPot, tx_pot']
    rw [hphiT_end_base]
  have hm_bsc : bunPhiMul * (∑ j : Fin slotCap, match S₀ j with
      | none => 0
      | some B₀ => batchSplitCount (bundleCompStep tr.cs B₀ tr.k ord ord' U).1) ≤
      bunPhiMul * branchStepCharge sp tr U ord ord' := Nat.mul_le_mul_left _ hsum_bsc_le
  have hm_add : bundleScanPotMul tourBundleSpec eCap *
      (((∑ gi ∈ Finset.range gs.length, addG gi) +
        ∑ r ∈ info.state.cs.RF.R \ (Finset.range gs.length).biUnion (fun gi => (gs.getD gi []).toFinset), addR r) *
        (Nat.log 2 (4 * eCap) + 2)) ≤
      bundleScanPotMul tourBundleSpec eCap * (2 * (U.length + L.length) * (Nat.log 2 (4 * eCap) + 2)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ htot_add)
  rw [hphiB_end, hphi_tx1, hphi_tx0]
  rw [hphiB_eq] at hcB
  rw [hphiT1_eq] at hcT
  dsimp only [htour0, htour1, tourDS_asmTourCordView_bundleTourAt, asmTourCordView, cordRepM, asmTourView] at hcD hcB
  simp only [argsSize, Expr.size]
  have hmul_dist : bundleScanPotMul tourBundleSpec eCap *
      (tourPot tr.cs.RF.R cord +
        ((∑ gi ∈ Finset.range gs.length, addG gi) +
          ∑ r ∈ info.state.cs.RF.R \ (Finset.range gs.length).biUnion (fun gi => (gs.getD gi []).toFinset), addR r) *
        (Nat.log 2 (4 * eCap) + 2)) =
      bundleScanPotMul tourBundleSpec eCap * tourPot tr.cs.RF.R cord +
      bundleScanPotMul tourBundleSpec eCap *
        (((∑ gi ∈ Finset.range gs.length, addG gi) +
          ∑ r ∈ info.state.cs.RF.R \ (Finset.range gs.length).biUnion (fun gi => (gs.getD gi []).toFinset), addR r) *
        (Nat.log 2 (4 * eCap) + 2)) := Nat.mul_add _ _ _
  rw [hmul_dist] at hcB
  have hcB' : cB + 70 * touched.length + (bunTableHeadroomRep slotCap vCap eCap tr.k).phi bunH m stB.mem +
      bundleScanPotMul tourBundleSpec eCap * tourPot info.state.cs.RF.R cord' +
      (tourAsmRep vCap eCap).phi tourH tx3 stB.mem ≤
      bundleStepCost tourBundleSpec eCap delEdges.length gs +
      bunPhiMul * branchStepCharge sp tr U ord ord' +
      (bunTableHeadroomRep slotCap vCap eCap tr.k).phi bunH m mem₀ +
      (bundleScanPotMul tourBundleSpec eCap * tourPot tr.cs.RF.R cord +
        bundleScanPotMul tourBundleSpec eCap * (2 * (U.length + L.length) * (Nat.log 2 (4 * eCap) + 2))) +
      (tourAsmRep vCap eCap).phi tourH tx2 stT.mem :=
    hcB.trans (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_left hm_bsc _) _)
        (Nat.add_le_add_left hm_add _)) _)
  have hcT' : cT + (tourAsmRep vCap eCap).phi tourH tx2 stT.mem ≤
      tourBlockStepMul * ((Ys.map List.length).sum + tr.S_cur.batchEnc info.U_S + words + editWords + 1) *
        ordStoreLog eCap + (tourAsmRep vCap eCap).phi tourH tx1 stD.mem := hcT
  clear * - hcD hcG hcT' hcB'
  omega

end

end MinCostFlow.SparseCore.Program
