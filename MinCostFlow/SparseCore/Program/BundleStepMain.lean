module

public import MinCostFlow.SparseCore.Program.BundleStepCostHelpers

/-!
# End-to-end verification of `bundleStepStmt` (`BundleStepMain`)

Chains Phase 1 (`bundleStepDel_runs`), Phase 2 (`bundleStepScan_runs`), and Phase 3
(`bundleStepEmitSlot_runs` over all touched slots) to prove `bundleStep_runs`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

public section

/-- End-to-end verification of `bundleStepStmt bStepDel bStepScan bStepEmitSlot`
(`args = [tbl, tourH, delCount, delPtr, groupCount, groupPtr, outDescPtr, h₀]`):
executes Phase 1 (edge deletions), Phase 2 (smaller-side tour scan), and Phase 3 (per-slot
bundle splitting and `BatchAt`/`BatchBodyLensAt` emission), restoring `BundleTableRepAt` for
`tableAfterStep S₀ D src' candSet`. -/
theorem bundleStep_runs {TS : BundleTourSpec}
    {w slotCap vCap eCap tbl tourH delCount delPtr groupPtr outDescPtr h₀ pos : ℕ}
    {pProg : Program}
    {bDllPush bDllErase bMergeSort bTourList bTourLen bTourOwner bStepDel bStepScan bStepEmitSlot : ℕ}
    {ω : ℕ → Bool}
    (htour : BundleTourAt TS w vCap eCap pProg bTourList bTourLen bTourOwner)
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap}
    {dels : List (ℕ × ℕ × ℕ)} {gs : List (List ℕ)}
    {cord' : ℕ → List End} {src' : End → ℕ} {tx₀ : htour.rep.τ} {mem₀ : ℕ → ℕ}
    (hpPush : pProg.HasAt bDllPush [bundleDllPushStmt])
    (hpErase : pProg.HasAt bDllErase [bundleDllEraseStmt])
    (hMergeSort : ∀ L : List ℕ, MeetsContract w pProg bMergeSort (mergeSortContract w L))
    (hpDel : pProg.HasAt bStepDel [bundleStepDelStmt bDllErase])
    (hpScan : pProg.HasAt bStepScan [bundleStepScanStmt bTourLen bTourList])
    (hpEmit : pProg.HasAt bStepEmitSlot [bundleStepEmitSlotStmt bDllPush bDllErase bMergeSort bTourOwner])
    (hw16 : 16 ≤ 2 ^ w) (htourH_w : tourH < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hblks_w : ∀ js : Fin slotCap, ∀ q c, m.slotBlocks js = some (q, c) →
      q + bundleSlotBlockSize c < 2 ^ w)
    (hdel_w : delPtr + 3 * delCount < 2 ^ w)
    (hgrp_w : groupPtr + groupsWords gs < 2 ^ w)
    (hout_w : outDescPtr + 1 + 3 * slotCap < 2 ^ w)
    (hfoot_lt : ∀ a, bundleTableFoot eCap tbl m a → a < h₀)
    (_hdel_lt : delPtr + 3 * delCount ≤ h₀)
    (hgrp_lt : groupPtr + groupsWords gs ≤ h₀)
    (hout_lt : outDescPtr + 1 + 3 * slotCap ≤ h₀)
    (hdel_disj_foot : ∀ a, delPtr ≤ a → a < delPtr + 3 * delCount → ¬ bundleTableFoot eCap tbl m a)
    (hgrp_disj_foot : ∀ a, groupPtr ≤ a → a < groupPtr + groupsWords gs → ¬ bundleTableFoot eCap tbl m a)
    (hout_disj_foot : ∀ a, outDescPtr ≤ a → a < outDescPtr + 1 + 3 * slotCap → ¬ bundleTableFoot eCap tbl m a)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h₀)
    (htfoot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a → ¬ bundleTableFoot eCap tbl m a)
    (htfoot_disj_grp : ∀ a, htour.rep.foot tourH tx₀ a → a < groupPtr ∨ groupPtr + groupsWords gs ≤ a)
    (htfoot_disj_out : ∀ a, htour.rep.foot tourH tx₀ a → a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a)
    (hzero : ZeroFrom mem₀ h₀)
    (htrep : htour.rep.rep tourH cord' tx₀ mem₀)
    (hrep0 : BundleTableRepAt slotCap vCap eCap tbl S₀ m mem₀)
    (hdels_len : dels.length = delCount)
    (hdels_mem : readDelTriples mem₀ delPtr delCount = dels)
    (hdels_lt : ∀ tr ∈ dels, tr.1 < eCap ∧ tr.2.1 < 2 ^ w ∧ tr.2.2 < 2 ^ w)
    (hdels_par : ∀ i (hi : i < dels.length), dels[i].1 ∉ delPrefixSet dels i →
      ∀ (j : Fin slotCap) (B : BundleState), S₀ j = some B →
        dels[i].1 ∈ B.edges →
        dels[i].2.1 = B.parent (B.bundleOf (dels[i].1, true)) ∧
        dels[i].2.2 = B.parent (B.bundleOf (dels[i].1, false)))
    (hgs_mem : readGroups mem₀ groupPtr gs.length = gs)
    (hgs_pos : ∀ G ∈ gs, 0 < G.length)
    (hgs_lt : ∀ G ∈ gs, ∀ v ∈ G, v < vCap ∧ v < 2 ^ w)
    (hgs_nodup : ∀ G ∈ gs, G.Nodup)
    (hgs_disj : ∀ i (hi : i < gs.length) j (hj : j < gs.length), i ≠ j →
      Disjoint gs[i].toFinset gs[j].toFinset)
    (hgs_ends_lt : ∀ G ∈ gs, ∀ v ∈ G, ∀ x ∈ cord' v, x.1 < eCap)
    (hgs_nd : ∀ G ∈ gs, ∀ v ∈ G, (cord' v).Nodup)
    (hsrc_lt : ∀ j : Fin slotCap, ∀ B₀, S₀ j = some B₀ →
      ∀ x ∈ edgeEnds (B₀.edges \ (dels.map Prod.fst).toFinset), src' x < vCap)
    (hsrc_mem : ∀ j : Fin slotCap, ∀ B₀, S₀ j = some B₀ →
      ∀ x ∈ edgeEnds (B₀.edges \ (dels.map Prod.fst).toFinset), x ∈ cord' (src' x))
    (hsrc_uniq : ∀ j : Fin slotCap, ∀ B₀, S₀ j = some B₀ →
      ∀ x ∈ edgeEnds (B₀.edges \ (dels.map Prod.fst).toFinset), ∀ v', x ∈ cord' v' → v' = src' x)
    (hbundle_in_group : ∀ j B₀, S₀ j = some B₀ → ∀ b ∈ B₀.vertices,
      2 ≤ (finalRootsOf B₀ (B₀.edges \ (dels.map Prod.fst).toFinset) src' b).card →
        ∃ gi, ∃ (hgi : gi < gs.length),
          ∀ x ∈ survivingEnds B₀ (B₀.edges \ (dels.map Prod.fst).toFinset) b,
            src' x ∈ gs[gi].toFinset)
    (hcap_ok : ∀ (maxIdxs : List ℕ) (j : Fin slotCap) (B₀ : BundleState) (p bunCap : ℕ),
      maxIdxs.length = gs.length →
      (∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length) →
      S₀ j = some B₀ → m.slotBlocks j = some (p, bunCap) →
      B₀.vertices.card + slotScannedEnds S₀ (dels.map Prod.fst).toFinset cord' gs maxIdxs j ≤ bunCap)
    (hh_sp : ∀ (maxIdxs : List ℕ) (touched : List ℕ),
      maxIdxs.length = gs.length →
      (∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length) →
      touched.Nodup → (∀ s ∈ touched, s < slotCap) →
      let candSet := addCandsForGroups (tableDelEdges S₀ (dels.map Prod.fst).toFinset)
        cord' gs maxIdxs (fun _ => ∅) gs.length
      let scanLen := slotScannedEnds S₀ (dels.map Prod.fst).toFinset cord' gs maxIdxs
      h₀ + bundleStepSpace TS S₀ (dels.map Prod.fst).toFinset candSet scanLen cord' gs touched < 2 ^ w) :
    let D := (dels.map Prod.fst).toFinset
    let S_del := tableDelEdges S₀ D
    ∃ st' c h' tx' maxIdxs touched,
      let candSet := addCandsForGroups S_del cord' gs maxIdxs (fun _ => ∅) gs.length
      let scanLen := slotScannedEnds S₀ D cord' gs maxIdxs
      let S_final := tableAfterStep S₀ D src' candSet
      Runs w pProg ω (bundleStepStmt bStepDel bStepScan bStepEmitSlot)
        (startState [tbl, tourH, delCount, delPtr, gs.length, groupPtr, outDescPtr, h₀] mem₀ pos)
        (.returned h') st' c ∧
      maxIdxs.length = gs.length ∧
      (∀ gi (hgi : gi < gs.length), ∃ hm : maxIdxs.getD gi 0 < gs[gi].length,
        ∀ j (hj : j < gs[gi].length), (cord' gs[gi][j]).length ≤ (cord' gs[gi][maxIdxs.getD gi 0]).length) ∧
      touched.Nodup ∧ (∀ s ∈ touched, s < slotCap) ∧
      (∀ j : Fin slotCap, match S₀ j with
        | none => j.1 ∉ touched
        | some B₀ => j.1 ∈ touched ↔ (B₀.edges ∩ D).Nonempty ∨ (candSet j).Nonempty) ∧
      h₀ ≤ h' ∧ h' ≤ h₀ + bundleStepSpace TS S₀ D candSet scanLen cord' gs touched ∧
      ZeroFrom st'.mem h' ∧
      htour.rep.rep tourH cord' tx' st'.mem ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < h')) ∧
      BundleTableRepAt slotCap vCap eCap tbl S_final m st'.mem ∧
      st'.mem (btBunCapAddr tbl slotCap eCap) = mem₀ (btBunCapAddr tbl slotCap eCap) ∧
      st'.mem outDescPtr = touched.length ∧
      (∀ i (hi : i < touched.length),
        let s := touched[i]'hi
        ∃ (hs : s < slotCap) (batchPtr totalWords : ℕ),
          st'.mem (outDescPtr + 1 + 3 * i) = s ∧
          st'.mem (outDescPtr + 1 + 3 * i + 1) = batchPtr ∧
          st'.mem (outDescPtr + 1 + 3 * i + 2) = totalWords ∧
          h₀ ≤ batchPtr ∧ batchPtr + totalWords ≤ h' ∧
          ∀ B₀, S₀ ⟨s, hs⟩ = some B₀ →
            SmallBatchAt st'.mem batchPtr B₀.graph (slotBatchOf S₀ D src' candSet ⟨s, hs⟩) totalWords ∧
            ∃ lens, lens.length = (slotBatchOf S₀ D src' candSet ⟨s, hs⟩).length ∧
              lens.sum = totalWords - 1 ∧
              BatchBodyLensAt st'.mem (batchPtr + 1) B₀.graph
                (slotBatchOf S₀ D src' candSet ⟨s, hs⟩) lens) ∧
      (∀ a < h₀, ¬ bundleTableFoot eCap tbl m a →
        (a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a) →
        ¬ htour.rep.foot tourH tx₀ a → st'.mem a = mem₀ a) ∧
      c + 70 * touched.length + htour.rep.phi tourH tx' st'.mem ≤
        bundleStepCost TS eCap delCount gs +
        bundleScanPotMul TS eCap * totalNonMaxLen cord' gs maxIdxs +
        htour.rep.phi tourH tx₀ mem₀ := by
  intro D S_del
  have htbl_h : tbl + bundleTableFixedSize slotCap eCap ≤ h₀ := by
    have := hfoot_lt (tbl + bundleTableFixedSize slotCap eCap - 1)
      (Or.inl ⟨by unfold bundleTableFixedSize; omega, by unfold bundleTableFixedSize; omega⟩)
    unfold bundleTableFixedSize at this ⊢; omega
  have htbl_w' : tbl + (14 + 7 * slotCap + 8 * eCap) < 2 ^ w := htbl_w
  have hsp0_w : h₀ + bundleStepScanSpace TS cord' gs < 2 ^ w := by
    have := hh_sp (gs.map fun _ => 0) [] (by simp)
      (fun gi hgi => by
        rw [List.getD_eq_getElem _ _ (by simp [hgi]), List.getElem_map]
        exact hgs_pos _ (List.getElem_mem hgi))
      List.nodup_nil (fun _ h => by cases h)
    unfold bundleStepSpace bundleStepEmitTotalSpace at this; simp at this; omega
  have hdisj₀ : ∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ B₁ B₂,
      S₀ j₁ = some B₁ → S₀ j₂ = some B₂ → Disjoint B₁.edges B₂.edges :=
    hrep0.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hslotCap_mem : mem₀ tbl = slotCap := by simpa [btOffSlotCap] using hrep0.1
  have hcandH_hdr : mem₀ (tbl + 11) = btSlotCandHeadBase tbl slotCap eCap := by
    simpa [btOffSlotCandHead] using hrep0.2.2.2.2.2.2.2.2.2.2.2.1
  have hcur0_init : ∀ s < slotCap, mem₀ (btCurBunBase tbl slotCap eCap + s) = 0 ∧
      mem₀ (btCurTagBase tbl slotCap eCap + s) = 0 :=
    hrep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hblks_disj_tbl : ∀ j : Fin slotCap, ∀ p c, m.slotBlocks j = some (p, c) →
      p + bundleSlotBlockSize c ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ p := by
    intro j p c hm
    have hj := hrep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j
    cases hS : S₀ j with
    | none => rw [hS, hm] at hj; exact False.elim hj
    | some B => rw [hS, hm] at hj; exact hj.2.2
  have hnot_core_of_hi : ∀ a, tbl + bundleTableCoreSize slotCap eCap ≤ a →
      a < tbl + bundleTableFixedSize slotCap eCap → ¬ bundleTableCoreFoot eCap tbl m a := by
    intro a ha1 ha2 hc
    rcases hc with ⟨_, hc2⟩ | ⟨j, p, c, hm, hp1, hp2⟩
    · omega
    · have hdj := hblks_disj_tbl j p c hm; unfold bundleTableCoreSize bundleTableFixedSize at *; omega
  set tBuf := btTouchedBufBase tbl slotCap eCap
  set tCnt := btTouchedCntAddr tbl slotCap eCap
  have htBuf_not_core : ∀ a, tBuf ≤ a → a < tBuf + slotCap → ¬ bundleTableCoreFoot eCap tbl m a :=
    fun a ha1 ha2 => hnot_core_of_hi a
      (by unfold tBuf btTouchedBufBase at ha1; unfold bundleTableCoreSize; omega)
      (by unfold tBuf btTouchedBufBase at ha2; unfold bundleTableFixedSize; omega)
  have htCnt_not_core : ¬ bundleTableCoreFoot eCap tbl m tCnt :=
    hnot_core_of_hi tCnt (by unfold tCnt btTouchedCntAddr bundleTableCoreSize; omega)
      (by unfold tCnt btTouchedCntAddr bundleTableFixedSize; omega)
  have htBuf_in_foot : ∀ a, tBuf ≤ a → a < tBuf + slotCap → bundleTableFoot eCap tbl m a :=
    fun a ha1 ha2 => Or.inl
      ⟨by unfold tBuf btTouchedBufBase at ha1; omega,
       by unfold tBuf btTouchedBufBase at ha2; unfold bundleTableFixedSize; omega⟩
  have htCnt_in_foot : bundleTableFoot eCap tbl m tCnt := btTouchedCnt_in_foot
  have hbErase_mc : ∀ prevBase nextBase headAddr key L,
      MeetsContract w pProg bDllErase
        (bundleDllEraseContract w prevBase nextBase headAddr (2 * eCap) key L) :=
    fun prevBase nextBase headAddr key L =>
      bundleDllErase_meetsContract (p := pProg) (b := bDllErase) hpErase
  -- Header: 4 assigns (`r8 = slotCap`, `r9 = tBuf`, `r10 = tCnt`, `r11 = h₀`)
  set st0 := startState [tbl, tourH, delCount, delPtr, gs.length, groupPtr, outDescPtr, h₀] mem₀ pos
  let r8 := Function.update st0.regs 8 slotCap
  let r9 := Function.update r8 9 tBuf
  let r10 := Function.update r9 10 tCnt
  let r11 := Function.update r10 11 h₀
  let stH : State := { st0 with regs := r11 }
  have ha8 : Runs w pProg ω (.assign 8 (.load (.reg 0))) st0 .normal { st0 with regs := r8 } 3 :=
    runs_assign_iff.mpr ⟨slotCap, by simp [Expr.eval, st0, startState, hslotCap_mem], rfl, rfl, rfl⟩
  have ha9 : Runs w pProg ω (.assign 9 (.bin .add (.load (.bin .add (.reg 0) (.const 11)))
      (.bin .mul (.const 3) (.reg 8)))) { st0 with regs := r8 } .normal { st0 with regs := r9 } 9 :=
    runs_assign_iff.mpr ⟨tBuf, by
      have heq : btSlotCandHeadBase tbl slotCap eCap + 3 * slotCap = tBuf := by
        unfold tBuf btTouchedBufBase btSlotCandHeadBase; omega
      simp [Expr.eval, BinOp.eval, r8, st0, startState, show 11 < 2 ^ w by omega,
        show 3 < 2 ^ w by omega, show tbl + 11 < 2 ^ w by omega, hcandH_hdr,
        show 3 * slotCap < 2 ^ w by omega, heq,
        show tBuf < 2 ^ w by unfold tBuf btTouchedBufBase; omega], rfl, rfl, by simp [Expr.size]⟩
  have ha10 : Runs w pProg ω (.assign 10 (.bin .add (.reg 9) (.reg 8))) { st0 with regs := r9 } .normal { st0 with regs := r10 } 4 :=
    runs_assign_iff.mpr ⟨tCnt, by
      have heq : tBuf + slotCap = tCnt := by unfold tBuf tCnt btTouchedBufBase btTouchedCntAddr; omega
      simp [Expr.eval, BinOp.eval, r9, r8, heq, show tCnt < 2 ^ w by unfold tCnt btTouchedCntAddr; omega], rfl, rfl, rfl⟩
  have ha11 : Runs w pProg ω (.assign 11 (.reg 7)) { st0 with regs := r10 } .normal stH 2 :=
    runs_assign_iff.mpr ⟨h₀, by simp [Expr.eval, r10, r9, r8, st0, startState], rfl, rfl, rfl⟩
  -- Phase 1: `bStepDel`
  have hdel_disj_tBuf : ∀ a, delPtr ≤ a → a < delPtr + 3 * delCount →
      a < tBuf ∨ tBuf + slotCap ≤ a := fun a ha1 ha2 => by
    by_contra h; push Not at h
    exact hdel_disj_foot a ha1 ha2 (htBuf_in_foot a h.1 h.2)
  obtain ⟨stD, cD, touched1, hrunD, hafterD, htouch1, hfrD, hcD⟩ :=
    bundleStepDel_runs (w := w) (tbl := tbl) (delCount := delCount) (delPtr := delPtr)
      (touchedBufPtr := tBuf) (pos := pos) (pProg := pProg) (bDllErase := bDllErase) (ω := ω)
      hbErase_mc hw16 htbl_w hblks_w hdel_w
      (by unfold tBuf btTouchedBufBase; omega) hdel_disj_foot htBuf_not_core hdel_disj_tBuf
      hrep0 hdels_len hdels_mem hdels_lt hdels_par
  have hcallD : Runs w pProg ω (.call 12 bStepDel [.reg 0, .reg 2, .reg 3, .reg 9])
      stH .normal { mem := stD.mem, regs := Function.update r11 12 touched1.length, pos := stD.pos } (cD + 5) :=
    runs_call_iff.mpr ⟨[tbl, delCount, delPtr, tBuf], bundleStepDelStmt bDllErase, .returned touched1.length, stD, cD,
      by simp [evalArgs, Expr.eval, stH, r11, r10, r9, r8, st0, startState],
      hpDel.get (i := 0) (by simp), hrunD, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  let stD1 : State :=
    { mem := Function.update stD.mem tCnt touched1.length
      regs := Function.update r11 12 touched1.length
      pos := stD.pos }
  have hstCnt1 : Runs w pProg ω (.store (.reg 10) (.reg 12))
      { mem := stD.mem, regs := Function.update r11 12 touched1.length, pos := stD.pos } .normal stD1 3 :=
    runs_store_iff.mpr ⟨tCnt, touched1.length,
      by simp [Expr.eval, r11, r10], by simp [Expr.eval], rfl, rfl, rfl⟩
  -- Prepare Phase 2 preconditions on `stD1.mem`
  have hfrD1 : ∀ a, ¬ bundleTableCoreFoot eCap tbl m a → (a < tBuf ∨ tBuf + slotCap ≤ a) → a ≠ tCnt →
      stD1.mem a = mem₀ a := fun a hnf ha hnc => by
    dsimp only [stD1]; rw [Function.update_of_ne hnc]; exact hfrD a hnf ha
  have hfrD1_out : ∀ a, ¬ bundleTableFoot eCap tbl m a → stD1.mem a = mem₀ a := fun a hnf =>
    hfrD1 a (fun hc => hnf (bundleTableCoreFoot_subset_foot hc))
      (by by_contra h; push Not at h; exact hnf (htBuf_in_foot a h.1 h.2))
      (fun h => hnf (h ▸ htCnt_in_foot))
  have hgs_mem1 : readGroups stD1.mem groupPtr gs.length = gs := by
    rw [readGroups_agree_outside_foot hfrD1_out (by rw [hgs_mem]; exact hgrp_disj_foot), hgs_mem]
  have hafterS0 : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m (fun _ => ∅) touched1 stD1.mem :=
    (bundleTableAfterDel_to_afterScan hafterD).of_agree fun a ha =>
      (show stD1.mem a = stD.mem a by
        dsimp only [stD1]; exact Function.update_of_ne (fun (heq : a = tCnt) => htCnt_not_core (heq ▸ ha)) _ _).symm
  have htrD1 : htour.rep.rep tourH cord' tx₀ stD1.mem :=
    (htour.rep_local tourH cord' tx₀ mem₀ stD1.mem fun a ha =>
      (hfrD1_out a (htfoot_disj_tbl a ha)).symm).1 htrep
  have hphiD1 : htour.rep.phi tourH tx₀ stD1.mem = htour.rep.phi tourH tx₀ mem₀ :=
    ((htour.rep_local tourH cord' tx₀ mem₀ stD1.mem fun a ha =>
      (hfrD1_out a (htfoot_disj_tbl a ha)).symm).2).symm
  -- Phase 2: `bStepScan`
  have hcur0_D1 : ∀ s < slotCap,
      stD1.mem (btCurBunBase tbl slotCap eCap + s) = 0 ∧
      stD1.mem (btCurTagBase tbl slotCap eCap + s) = 0 := fun s hs => by
    have hcb_nc : ¬ bundleTableCoreFoot eCap tbl m (btCurBunBase tbl slotCap eCap + s) :=
      hnot_core_of_hi _ (by unfold btCurBunBase bundleTableCoreSize; omega)
        (by unfold btCurBunBase bundleTableFixedSize; omega)
    have hct_nc : ¬ bundleTableCoreFoot eCap tbl m (btCurTagBase tbl slotCap eCap + s) :=
      hnot_core_of_hi _ (by unfold btCurTagBase bundleTableCoreSize; omega)
        (by unfold btCurTagBase bundleTableFixedSize; omega)
    exact ⟨(hfrD1 _ hcb_nc (Or.inl (by unfold btCurBunBase tBuf btTouchedBufBase; omega))
        (by unfold btCurBunBase tCnt btTouchedCntAddr; omega)).trans (hcur0_init s hs).1,
      (hfrD1 _ hct_nc (Or.inl (by unfold btCurTagBase tBuf btTouchedBufBase; omega))
        (by unfold btCurTagBase tCnt btTouchedCntAddr; omega)).trans (hcur0_init s hs).2⟩
  obtain ⟨stS, cS, hS, txS, maxIdxs, touched, hrunS, hmaxLen, hmaxSpec, hhS_lo, hhS_hi, hzfS,
    htrS, htfS, hafterS, htouchS, hscanS, hscanInS, htcntS, hfrS, hcS⟩ :=
    bundleStepScan_runs (w := w) (slotCap := slotCap) (vCap := vCap) (eCap := eCap) (tbl := tbl)
      (tourH := tourH) (groupPtr := groupPtr) (touchedCountPtr := tCnt) (touchedBufPtr := tBuf)
      (h₀ := h₀) (pos := stD1.pos) (ω := ω) htour hw16 htourH_w hpk_w htbl_w hblks_w
      hgrp_w (by unfold tCnt btTouchedCntAddr; omega) (by unfold tBuf btTouchedBufBase; omega)
      hgs_mem1 hgs_pos hgs_lt hgs_ends_lt hgs_nd
      hfoot_lt (by unfold tBuf btTouchedBufBase bundleTableFixedSize at *; omega) hgrp_lt
      (by unfold tCnt btTouchedCntAddr bundleTableFixedSize at *; omega)
      htBuf_not_core
      (fun a ha1 _ => Or.inr (by unfold tBuf btTouchedBufBase at ha1; unfold btCurTagBase; omega))
      hgrp_disj_foot
      (fun a ha1 ha2 => by by_contra h; push Not at h; exact hgrp_disj_foot a ha1 ha2 (htBuf_in_foot a h.1 h.2))
      htCnt_not_core
      (Or.inr (by unfold tCnt btTouchedCntAddr btCurTagBase; omega))
      (Or.inr (by unfold tBuf tCnt btTouchedBufBase btTouchedCntAddr; omega))
      (by by_contra h; push Not at h; exact hgrp_disj_foot tCnt h.1 h.2 htCnt_in_foot)
      htfoot_lt htfoot_disj_tbl
      (fun a ha => by by_contra h; push Not at h; exact htfoot_disj_tbl a ha (htBuf_in_foot a h.1 h.2))
      htfoot_disj_grp (fun hf => htfoot_disj_tbl tCnt hf htCnt_in_foot)
      (fun a ha => (hfrD1_out a (fun hf => by have := hfoot_lt a hf; omega)).trans (hzero a ha))
      hsp0_w htrD1 hafterS0
      (fun i hi => by
        dsimp only [stD1]
        have := touched_len_le_slotCap hafterD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hafterD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        rw [Function.update_of_ne (by unfold tBuf tCnt btTouchedBufBase btTouchedCntAddr; omega)]; exact htouch1 i hi)
      hcur0_D1
      (by simp [stD1])
  set candSet := addCandsForGroups S_del cord' gs maxIdxs (fun _ => ∅) gs.length
  set scanEnds := addScanEndsForGroups S_del cord' gs maxIdxs (fun _ => ∅) (fun _ => []) gs.length
  set scanLen := slotScannedEnds S₀ D cord' gs maxIdxs
  have hndT : touched.Nodup := hafterS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hltT : ∀ s ∈ touched, s < slotCap := hafterS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have htlen_le : touched.length ≤ slotCap := touched_len_le_slotCap hndT hltT
  have hval_all : ∀ j B₀, S₀ j = some B₀ →
      ScanValidForSlot { B₀ with edges := B₀.edges \ D } src' (candSet j) (scanEnds j) ∧
      (∀ b ∈ candSet j, ∃ t ∈ scanEnds j, t.1 = b) ∧
      (candSet j).card ≤ (scanEnds j).length := fun j B₀ hS₀j =>
    scanValidForSlot_of_scan hS₀j hgs_nodup hgs_disj hgs_nd (fun gi hgi => (hmaxSpec gi hgi).1)
      (fun x hx w => ⟨fun hm => (hsrc_uniq j B₀ hS₀j x hx w hm).symm,
        fun heq => heq ▸ hsrc_mem j B₀ hS₀j x hx⟩)
      (hbundle_in_group j B₀ hS₀j)
  have hscan_nil_not_touched : ∀ s (hs : s < slotCap), s ∉ touched → scanEnds ⟨s, hs⟩ = [] :=
    fun _ hs hnot => scanEnds_nil_of_not_touched hafterS (fun j B₀ hS => (hval_all j B₀ hS).1) hs hnot
  have hsp_full : h₀ + bundleStepSpace TS S₀ D candSet scanLen cord' gs touched < 2 ^ w :=
    hh_sp maxIdxs touched hmaxLen (fun gi hgi => (hmaxSpec gi hgi).1) hndT hltT
  -- Call `bStepScan` + load `r12` + store `outDescPtr`
  let r11S := Function.update stD1.regs 11 hS
  let stS0 : State := { mem := stS.mem, regs := r11S, pos := stS.pos }
  have hcallS : Runs w pProg ω (.call 11 bStepScan [.reg 0, .reg 1, .reg 4, .reg 5, .reg 10, .reg 9, .reg 11])
      stD1 .normal stS0 (cS + 8) :=
    runs_call_iff.mpr ⟨[tbl, tourH, gs.length, groupPtr, tCnt, tBuf, h₀],
      bundleStepScanStmt bTourLen bTourList, .returned hS, stS, cS,
      by simp [evalArgs, Expr.eval, stD1, r11, r10, r9, r8, st0, startState],
      hpScan.get (i := 0) (by simp), hrunS, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  let r12S := Function.update r11S 12 touched.length
  let stS1 : State := { mem := Function.update stS.mem outDescPtr touched.length, regs := r12S, pos := stS.pos }
  have ha12S : Runs w pProg ω (.assign 12 (.load (.reg 10))) stS0 .normal { stS0 with regs := r12S } 3 :=
    runs_assign_iff.mpr ⟨touched.length, by simp [Expr.eval, stS0, r11S, stD1, r11, r10, htcntS], rfl, rfl, rfl⟩
  have hstOut0 : Runs w pProg ω (.store (.reg 6) (.reg 12)) { stS0 with regs := r12S } .normal stS1 3 :=
    runs_store_iff.mpr ⟨outDescPtr, touched.length,
      by simp [Expr.eval, r12S, r11S, stD1, r11, r10, r9, r8, st0, startState],
      by simp [Expr.eval, r12S], rfl, rfl, rfl⟩
  -- Phase 3: `forRange 13 0 touched.length` calling `bStepEmitSlot`
  have hEmit0 : BundleTableEmitState slotCap vCap eCap tbl S₀ D m candSet S_del touched stS1.mem :=
    (BundleTableEmitState.of_afterScan hdisj₀ hafterS).of_agree_foot fun a ha => by
      dsimp only [stS1]; rw [Function.update_of_ne (fun heq => hout_disj_foot a (by omega) (by omega) ha)]
  have htrS1 : htour.rep.rep tourH cord' txS stS1.mem :=
    (htour.rep_local tourH cord' txS stS.mem stS1.mem fun a ha => by
      dsimp only [stS1]; rw [Function.update_of_ne (fun heq => by
        rw [heq] at ha; rcases htfS outDescPtr ha with h0 | ⟨h1, _⟩
        · have := htfoot_disj_out outDescPtr h0; omega
        · omega)]).1 htrS
  have hphiS1 : htour.rep.phi tourH txS stS1.mem = htour.rep.phi tourH txS stS.mem :=
    ((htour.rep_local tourH cord' txS stS.mem stS1.mem fun a ha => by
      dsimp only [stS1]; rw [Function.update_of_ne (fun heq => by
        rw [heq] at ha; rcases htfS outDescPtr ha with h0 | ⟨h1, _⟩
        · have := htfoot_disj_out outDescPtr h0; omega
        · omega)]).2).symm
  let S_pref : ℕ → BundleTableState slotCap := fun i j =>
    if j.1 ∈ touched.take i then tableAfterStep S₀ D src' candSet j else S_del j
  let Acc := ℕ × htour.rep.τ
  let Inv : ℕ → Acc → State → Prop := fun i acc st =>
    let (hCur, tx) := acc
    (∀ r ≤ 12, r ≠ 11 → st.regs r = stS1.regs r) ∧
    st.regs 11 = hCur ∧ st.regs 13 = i ∧
    hS ≤ hCur ∧ hCur ≤ hS + bundleStepEmitTotalSpace TS S₀ D candSet scanLen (touched.take i) ∧
    ZeroFrom st.mem hCur ∧
    htour.rep.rep tourH cord' tx st.mem ∧
    (∀ a, htour.rep.foot tourH tx a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < hCur)) ∧
    BundleTableEmitState slotCap vCap eCap tbl S₀ D m candSet (S_pref i) (touched.drop i) st.mem ∧
    ListAt st.mem tBuf touched ∧
    (∀ s (hs : s < slotCap),
      if s ∈ touched.drop i then
        ScanNodesAt eCap st.mem h₀ hS (st.mem (btCurBunBase tbl slotCap eCap + s)) (scanEnds ⟨s, hs⟩) ∧
        ScanNodesIn st.mem (fun a => ¬ htour.rep.foot tourH tx a)
          (st.mem (btCurBunBase tbl slotCap eCap + s)) (scanEnds ⟨s, hs⟩) ∧
        st.mem (btCurTagBase tbl slotCap eCap + s) = (scanEnds ⟨s, hs⟩).length
      else
        st.mem (btCurBunBase tbl slotCap eCap + s) = 0 ∧
        st.mem (btCurTagBase tbl slotCap eCap + s) = 0) ∧
    st.mem (btBunCapAddr tbl slotCap eCap) = mem₀ (btBunCapAddr tbl slotCap eCap) ∧
    st.mem outDescPtr = touched.length ∧
    (∀ k (hk : k < i) (hk' : k < touched.length),
      let s := touched[k]'hk'
      ∃ (hs : s < slotCap) (batchPtr totalWords : ℕ),
        st.mem (outDescPtr + 1 + 3 * k) = s ∧
        st.mem (outDescPtr + 1 + 3 * k + 1) = batchPtr ∧
        st.mem (outDescPtr + 1 + 3 * k + 2) = totalWords ∧
        h₀ ≤ batchPtr ∧ batchPtr + totalWords ≤ hCur ∧
        (∀ a, batchPtr ≤ a → a < batchPtr + totalWords → ¬ htour.rep.foot tourH tx a) ∧
        ∀ B₀, S₀ ⟨s, hs⟩ = some B₀ →
          SmallBatchAt st.mem batchPtr B₀.graph (slotBatchOf S₀ D src' candSet ⟨s, hs⟩) totalWords ∧
          ∃ lens, lens.length = (slotBatchOf S₀ D src' candSet ⟨s, hs⟩).length ∧
            lens.sum = totalWords - 1 ∧
            BatchBodyLensAt st.mem (batchPtr + 1) B₀.graph
              (slotBatchOf S₀ D src' candSet ⟨s, hs⟩) lens) ∧
    (∀ a < h₀, ¬ bundleTableFoot eCap tbl m a →
      (a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a) →
      ¬ htour.rep.foot tourH tx₀ a → st.mem a = mem₀ a)
  let stepCost : ℕ → ℕ := fun i =>
    let s := touched.getD i 0
    (if hs : s < slotCap then
      bundleStepEmitSlotCost TS eCap (slotDelCnt S₀ D ⟨s, hs⟩) (slotCandCnt candSet ⟨s, hs⟩)
        (scanLen ⟨s, hs⟩)
    else 0) + 35
  let emitBody : Stmt :=
    .assign 14 (.load (.bin .add (.reg 9) (.reg 13))) ;;
    .assign 15 (.bin .add (.bin .add (.reg 6) (.const 1)) (.bin .mul (.const 3) (.reg 13))) ;;
    .call 11 bStepEmitSlot [.reg 0, .reg 1, .reg 14, .reg 15, .reg 11]
  obtain ⟨stE, cE, ⟨hEnd, txEnd⟩, hrunE, hInvE, hcE⟩ :=
    runs_forRange_pot (w := w) (p := pProg) (ω := ω) (r := 13) (lo := .const 0) (hi := .reg 12)
      (body := emitBody) (fun acc st => htour.rep.phi tourH acc.2 st.mem) Inv stepCost touched.length
      (by omega) (fun _ => by omega) (st₀ := stS1) (a₀ := (hS, txS))
      (by
        refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], ?_, rfl⟩
        refine ⟨fun r hr _ => by simp [show r ≠ 13 by omega], by simp [stS1, r12S, r11S], by simp,
          le_refl _, by simp [bundleStepEmitTotalSpace],
          fun a ha => by dsimp only [stS1]; rw [Function.update_of_ne (by omega)]; exact hzfS a ha,
          htrS1, fun a ha => by rcases htfS a ha with h0 | ⟨h1, h2⟩; exact Or.inl h0; exact Or.inr ⟨h1, h2⟩,
          by simpa [S_pref] using hEmit0,
          fun i hi => by
            dsimp only [stS1]
            have hi_lt : i < slotCap := lt_of_lt_of_le hi htlen_le
            rw [Function.update_of_ne (fun heq => hout_disj_foot (tBuf + i) (by omega) (by omega)
              (htBuf_in_foot (tBuf + i) (by omega) (by omega)))]
            exact htouchS i hi,
          fun s hs => by
            have hcb_ne : btCurBunBase tbl slotCap eCap + s ≠ outDescPtr :=
              fun heq => hout_disj_foot _ (by omega) (by omega) (btCurBun_in_foot hs)
            have hct_ne : btCurTagBase tbl slotCap eCap + s ≠ outDescPtr :=
              fun heq => hout_disj_foot _ (by omega) (by omega) (btCurTag_in_foot hs)
            have hmem_cb : stS1.mem (btCurBunBase tbl slotCap eCap + s) = stS.mem (btCurBunBase tbl slotCap eCap + s) :=
              Function.update_of_ne hcb_ne _ _
            have hmem_ct : stS1.mem (btCurTagBase tbl slotCap eCap + s) = stS.mem (btCurTagBase tbl slotCap eCap + s) :=
              Function.update_of_ne hct_ne _ _
            obtain ⟨hsn_s, hct_s⟩ := hscanS ⟨s, hs⟩
            simp only [List.drop_zero]
            split_ifs with hmem
            · rw [hmem_cb, hmem_ct]
              obtain ⟨h1, h2⟩ := scanNodesAt_mono_of_in (mem' := stS1.mem) hsn_s (hscanInS ⟨s, hs⟩) (le_refl _)
                (fun a ha1 _ _ => by dsimp only [stS1]; exact Function.update_of_ne (by omega) _ _)
                (fun _ _ _ hp => hp)
              exact ⟨h1, h2, hct_s⟩
            · have hnil := hscan_nil_not_touched s hs hmem
              rw [hnil] at hsn_s hct_s
              exact ⟨hmem_cb.trans hsn_s, hmem_ct.trans hct_s⟩,
          by
            have hka_nc : ¬ bundleTableCoreFoot eCap tbl m (btBunCapAddr tbl slotCap eCap) :=
              hnot_core_of_hi _ (by unfold btBunCapAddr bundleTableCoreSize; omega)
                (by unfold btBunCapAddr bundleTableFixedSize; omega)
            have hka_lt : btBunCapAddr tbl slotCap eCap < h₀ := hfoot_lt _ btBunCap_in_foot
            dsimp only [stS1]
            rw [Function.update_of_ne (fun heq => hout_disj_foot _ (by omega) (by omega) btBunCap_in_foot),
              hfrS _ hka_lt hka_nc (Or.inr (by unfold btBunCapAddr btCurTagBase; omega))
                (Or.inr (by unfold btBunCapAddr tBuf btTouchedBufBase; omega))
                (by unfold btBunCapAddr tCnt btTouchedCntAddr; omega)
                (fun hf => htfoot_disj_tbl _ hf btBunCap_in_foot),
              hfrD1 _ hka_nc (Or.inr (by unfold btBunCapAddr tBuf btTouchedBufBase; omega))
                (by unfold btBunCapAddr tCnt btTouchedCntAddr; omega)],
          by simp [stS1], fun _ hk => by omega,
          fun a ha hnf hout hnt => by
            dsimp only [stS1]; rw [Function.update_of_ne (by omega)]
            exact (hfrS a ha (fun hc => hnf (bundleTableCoreFoot_subset_foot hc))
              (by by_contra h; push Not at h
                  exact hnf (Or.inl ⟨by unfold btCurBunBase at h; omega,
                    by unfold btCurTagBase at h; unfold bundleTableFixedSize; omega⟩))
              (by by_contra h; push Not at h; exact hnf (htBuf_in_foot a h.1 h.2))
              (fun h => hnf (h ▸ htCnt_in_foot)) hnt).trans (hfrD1_out a hnf)⟩)
      (fun _ _ _ _ hI => hI.2.2.1)
      (fun _ _ st _ hI => by simp [Expr.eval, hI.1 12 (by decide) (by decide), stS1, r12S])
      (fun i ⟨hCur, tx⟩ st hi hI => by
        rcases hI with ⟨hregs, hr11c, hr13c, hhS_le, hhCur_le, hzfc, htrc, htfc, hEmitc,
          htouchc, hcur0c, hka_c, hout0c, hdescs, hfrc⟩
        set s := touched[i]'hi
        have hs_lt : s < slotCap := hltT s (List.getElem_mem hi)
        set js : Fin slotCap := ⟨s, hs_lt⟩
        have hs_in_drop : s ∈ touched.drop i := by rw [List.drop_eq_getElem_cons hi]; exact List.mem_cons_self
        have hS0_some : ∃ B₀, S₀ js = some B₀ := by
          have hdj := hafterS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 js
          cases hS0 : S₀ js with
          | none => rw [hS0] at hdj; exact False.elim (hdj.2 (List.getElem_mem hi))
          | some B₀ => exact ⟨B₀, rfl⟩
        obtain ⟨B₀, hS₀s⟩ := hS0_some
        have hblks_some : ∃ p bunCap, m.slotBlocks js = some (p, bunCap) := by
          have hsj := hEmitc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 js
          have hSr := hEmitc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 js
          rw [hS₀s] at hSr
          cases hSc : S_pref i js with
          | none => rw [hSc] at hSr; exact False.elim hSr
          | some B =>
            rw [hSc] at hsj
            cases hm : m.slotBlocks js with
            | none => rw [hm] at hsj; exact False.elim hsj
            | some pb => exact ⟨pb.1, pb.2, rfl⟩
        obtain ⟨p, bunCap, hblks⟩ := hblks_some
        have hsp_succ : bundleStepEmitTotalSpace TS S₀ D candSet scanLen (touched.take (i + 1)) =
            bundleStepEmitTotalSpace TS S₀ D candSet scanLen (touched.take i) +
            bundleStepEmitSlotSpace TS (slotDelCnt S₀ D js) (slotCandCnt candSet js)
              (scanLen js) :=
          emitTotalSpace_take_succ TS S₀ D candSet scanLen hi hs_lt
        have hsp_le := emitTotalSpace_take_le TS S₀ D candSet scanLen touched (i := i + 1)
        have h1 : slotDelCnt S₀ D js = (B₀.edges ∩ D).card := by simp [slotDelCnt, hS₀s]
        have h2 : slotCandCnt candSet js = (candSet js).card := rfl
        have h3 : scanLen js = (scanEnds js).length := rfl
        have hh_room : hCur + bundleStepEmitSlotSpace TS (B₀.edges ∩ D).card (candSet js).card
            (scanEnds js).length < 2 ^ w := by
          rw [← h1, ← h2, ← h3]; unfold bundleStepSpace at hsp_full; omega
        set outI := outDescPtr + 1 + 3 * i
        let r14 := Function.update st.regs 14 s
        let r15 := Function.update r14 15 outI
        have ha14 : Runs w pProg ω (.assign 14 (.load (.bin .add (.reg 9) (.reg 13))))
            st .normal { st with regs := r14 } 5 :=
          runs_assign_iff.mpr ⟨s, by
            simp [Expr.eval, BinOp.eval, hregs 9 (by decide) (by decide), stS1, r12S, r11S, stD1, r11, r10, r9,
              hr13c, show tBuf + i < 2 ^ w by unfold tBuf btTouchedBufBase; omega, htouchc i hi, s], rfl, rfl, rfl⟩
        have ha15 : Runs w pProg ω (.assign 15 (.bin .add (.bin .add (.reg 6) (.const 1)) (.bin .mul (.const 3) (.reg 13))))
            { st with regs := r14 } .normal { st with regs := r15 } 8 :=
          runs_assign_iff.mpr ⟨outI, by
            simp [Expr.eval, BinOp.eval, r14, hregs 6 (by decide) (by decide), stS1, r12S, r11S, stD1, r11, r10, r9, r8,
              st0, startState, hr13c, show 1 < 2 ^ w by omega, show 3 < 2 ^ w by omega,
              show outDescPtr + 1 < 2 ^ w by omega, show 3 * i < 2 ^ w by omega,
              show outDescPtr + 1 + 3 * i < 2 ^ w by omega, outI],
            rfl, rfl, by simp [Expr.size]⟩
        have hcur_s := hcur0c s hs_lt
        simp only [hs_in_drop, ↓reduceIte] at hcur_s
        have hp_le_h0 : p + bundleSlotBlockSize bunCap ≤ h₀ := by
          have := hfoot_lt (p + bundleSlotBlockSize bunCap - 1)
            (Or.inr ⟨js, p, bunCap, hblks, by unfold bundleSlotBlockSize; omega, by unfold bundleSlotBlockSize; omega⟩)
          unfold bundleSlotBlockSize at this ⊢; omega
        obtain ⟨stEm, cEm, hNext, txNext, batchPtr, totalWords, hrunEm, hhN_lo, hhN_hi, hbp_lo, hbp_hi,
          hzfN, htrN, htfN, hEmitN, hcurB0_s, hcurT0_s, hbatN, hblensN, ho0, ho1, ho2, hfrEm, hcEm⟩ :=
          bundleStepEmitSlot_runs (w := w) (slotCap := slotCap) (vCap := vCap) (eCap := eCap) (tbl := tbl)
            (tourH := tourH) (s := s) (outDescPtr := outI) (hStart := h₀) (hScanEnd := hS)
            (h₀ := hCur) (pos := st.pos) (ω := ω) (scan_j := scanEnds js)
            htour hpPush hpErase hMergeSort hw16 htourH_w hpk_w htbl_w hblks_w
            hs_in_drop hs_lt hS₀s hblks
            (by unfold bundleTableFixedSize at htbl_h; omega) hhS_lo hhS_le htbl_h (Or.inl hp_le_h0)
            (by omega) (by omega)
            (fun a ha1 ha2 => hout_disj_foot a (by omega) (by omega))
            (fun a ha => lt_of_lt_of_le (hfoot_lt a ha) (by omega))
            (fun a ha => by rcases htfc a ha with h0 | ⟨_, h2⟩; exact lt_of_lt_of_le (htfoot_lt a h0) (by omega); exact h2)
            (fun a ha => by
              rcases htfc a ha with h0 | ⟨h1, _⟩
              · exact htfoot_disj_tbl a h0
              · intro hf; have := hfoot_lt a hf; omega)
            (fun a ha => by
              rcases htfc a ha with h0 | ⟨h1, _⟩
              · have := htfoot_disj_out a h0; omega
              · right; omega)
            hzfc htrc hEmitc (hsrc_lt js B₀ hS₀s) (hsrc_mem js B₀ hS₀s) (hsrc_uniq js B₀ hS₀s)
            (hval_all js B₀ hS₀s).1 hcur_s.1 hcur_s.2.2
            (hcap_ok maxIdxs js B₀ p bunCap hmaxLen (fun gi hgi => (hmaxSpec gi hgi).1) hS₀s hblks)
            hh_room
        let stNext : State := { mem := stEm.mem, regs := Function.update r15 11 hNext, pos := stEm.pos }
        have hcallEm : Runs w pProg ω (.call 11 bStepEmitSlot [.reg 0, .reg 1, .reg 14, .reg 15, .reg 11])
            { st with regs := r15 } .normal stNext (cEm + 6) :=
          runs_call_iff.mpr ⟨[tbl, tourH, s, outI, hCur],
            bundleStepEmitSlotStmt bDllPush bDllErase bMergeSort bTourOwner, .returned hNext, stEm, cEm,
            by simp [evalArgs, Expr.eval, r15, r14, hregs 0 (by decide) (by decide),
                hregs 1 (by decide) (by decide), hr11c, stS1, r12S, r11S, stD1, r11, r10, r9, r8, st0, startState],
            hpEmit.get (i := 0) (by simp), hrunEm, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
        have hS_next_eq : Function.update (S_pref i) js
            (some (byRootSplitFold B₀ (B₀.edges \ D) src'
              (((B₀.edges ∩ D).sort (· ≤ ·)).map Update.delete) ((candSet js).sort (· ≤ ·))).2) =
            S_pref (i + 1) := by
          funext j
          by_cases hj : j = js
          · subst hj; simp only [Function.update_self, S_pref, tableAfterStep, hS₀s]
            have hm : s ∈ touched.take (i + 1) := by
              rw [List.take_succ_eq_append_getElem hi]; exact List.mem_append_right _ List.mem_cons_self
            simp [js, hm]
          · simp only [Function.update_of_ne hj, S_pref]
            have hne_s : j.1 ≠ s := fun h => hj (Fin.ext h)
            have hiff : j.1 ∈ touched.take (i + 1) ↔ j.1 ∈ touched.take i := by
              rw [List.take_succ_eq_append_getElem hi]
              simp only [List.mem_append, List.mem_singleton, or_iff_left_iff_imp]
              exact fun h => False.elim (hne_s h)
            simp [hiff]
        rw [hS_next_eq, list_drop_erase_head hi] at hEmitN
        have hfr_below : ∀ a < hCur, ¬ bundleTableCoreFoot eCap tbl m a →
            a ≠ btCurBunBase tbl slotCap eCap + s → a ≠ btCurTagBase tbl slotCap eCap + s →
            (a < outI ∨ outI + 3 ≤ a) → ¬ htour.rep.foot tourH tx a → stNext.mem a = st.mem a :=
          fun a ha hnf hcb hct hout hnt => hfrEm a ha hnf hcb hct hout hnt
        have hfr_below_out : ∀ a < hCur, ¬ bundleTableFoot eCap tbl m a →
            (a < outI ∨ outI + 3 ≤ a) → ¬ htour.rep.foot tourH tx a → stNext.mem a = st.mem a :=
          fun a ha hnf hout hnt => hfrEm a ha (fun hc => hnf (bundleTableCoreFoot_subset_foot hc))
            (fun heq => hnf (heq ▸ btCurBun_in_foot hs_lt)) (fun heq => hnf (heq ▸ btCurTag_in_foot hs_lt)) hout hnt
        have htouch_next : ListAt stNext.mem tBuf touched := fun k hk => by
          have hk_lt : k < slotCap := lt_of_lt_of_le hk htlen_le
          have htk_ft := htBuf_in_foot (tBuf + k) (by omega) (by omega)
          rw [hfr_below (tBuf + k) (lt_of_lt_of_le (hfoot_lt _ htk_ft) (by omega))
            (htBuf_not_core _ (by omega) (by omega))
            (by unfold tBuf btTouchedBufBase btCurBunBase; omega)
            (by unfold tBuf btTouchedBufBase btCurTagBase; omega)
            (by by_contra h; push Not at h; exact hout_disj_foot (tBuf + k) (by omega) (by omega) htk_ft)
            (fun hf => by
              rcases htfc _ hf with h0 | ⟨h1, _⟩
              · exact htfoot_disj_tbl _ h0 htk_ft
              · have := hfoot_lt _ htk_ft; omega)]
          exact htouchc k hk
        have hcur0_next := bundleStep_curScan_step hndT hi rfl hs_lt hhS_lo hhS_le hbp_lo hfoot_lt
          (fun a ha1 ha2 => hout_disj_foot a (by omega) (by omega)) (by omega) hnot_core_of_hi
          (fun a ha => by rcases htfc a ha with h0 | ⟨h1, _⟩; exact htfoot_disj_tbl a h0; intro hf; have := hfoot_lt a hf; omega)
          htfN hcurB0_s hcurT0_s hfr_below hcur0c
        have hka_next : stNext.mem (btBunCapAddr tbl slotCap eCap) = mem₀ (btBunCapAddr tbl slotCap eCap) := by
          have hka_ft : bundleTableFoot eCap tbl m (btBunCapAddr tbl slotCap eCap) := btBunCap_in_foot
          have hka_nc : ¬ bundleTableCoreFoot eCap tbl m (btBunCapAddr tbl slotCap eCap) :=
            hnot_core_of_hi _ (by unfold btBunCapAddr bundleTableCoreSize; omega)
              (by unfold btBunCapAddr bundleTableFixedSize; omega)
          rw [hfr_below _ (lt_of_lt_of_le (hfoot_lt _ hka_ft) (by omega)) hka_nc
            (by unfold btBunCapAddr btCurBunBase; omega) (by unfold btBunCapAddr btCurTagBase; omega)
            (by by_contra h; push Not at h; exact hout_disj_foot _ (by omega) (by omega) hka_ft)
            (fun hf => by
              rcases htfc _ hf with h0 | ⟨h1, _⟩
              · exact htfoot_disj_tbl _ h0 hka_ft
              · have := hfoot_lt _ hka_ft; omega)]
          exact hka_c
        refine ⟨stNext, 5 + (8 + (cEm + 6) + 1) + 1, (hNext, txNext),
          bundle_runs_seq_normal ha14 (bundle_runs_seq_normal ha15 hcallEm),
          by simp [stNext, r15, r14, hr13c], ?_, rfl, ?_⟩
        · refine ⟨fun r hr h11 => by
              simp only [Function.update_of_ne (show r ≠ 13 by omega), stNext, r15, r14,
                Function.update_of_ne h11, Function.update_of_ne (show r ≠ 15 by omega),
                Function.update_of_ne (show r ≠ 14 by omega)]
              exact hregs r hr h11,
            by simp [stNext], by simp, by omega,
            by have hdl : ((B₀.edges ∩ D).sort (· ≤ ·)).length = (B₀.edges ∩ D).card := Finset.length_sort _
               have hcl : ((candSet js).sort (· ≤ ·)).length = (candSet js).card := Finset.length_sort _
               rw [hdl, hcl, ← h1, ← h2, ← h3] at hhN_hi; rw [hsp_succ]; omega,
            hzfN, htrN, fun a ha => by
              rcases htfN a ha with h0 | ⟨h1', h2'⟩
              · rcases htfc a h0 with h00 | ⟨h1'', h2''⟩; exact Or.inl h00; exact Or.inr ⟨h1'', by omega⟩
              · exact Or.inr ⟨by omega, h2'⟩,
            hEmitN, htouch_next, hcur0_next, hka_next,
            (hfr_below_out outDescPtr (by omega) (hout_disj_foot outDescPtr (le_refl _) (by omega))
              (Or.inl (by omega)) (fun hf => by
                rcases htfc outDescPtr hf with h0 | ⟨h1', _⟩
                · have := htfoot_disj_out outDescPtr h0; omega
                · omega)).trans hout0c,
            ?_, ?_⟩
          · intro k hk hk'
            by_cases hki : k = i
            · subst hki
              refine ⟨hs_lt, batchPtr, totalWords, ho0, ho1, ho2, by omega, hbp_hi,
                fun a ha1 ha2 hf => by
                  rcases htfN a hf with h0 | ⟨h1', _⟩
                  · rcases htfc a h0 with h00 | ⟨_, h2'⟩
                    · have := htfoot_lt a h00; omega
                    · omega
                  · omega,
                fun B₁ hS1 => ?_⟩
              rw [hS₀s] at hS1; cases hS1
              have hsb : slotBatchOf S₀ D src' candSet ⟨s, hs_lt⟩ =
                  (byRootSplitFold B₀ (B₀.edges \ D) src'
                    (((B₀.edges ∩ D).sort (· ≤ ·)).map Update.delete)
                    ((candSet js).sort (· ≤ ·))).1 := by
                simp only [slotBatchOf, hS₀s, js]
              rw [hsb]; exact ⟨hbatN, hblensN⟩
            · obtain ⟨hs_k, bp_k, tw_k, hd0, hd1, hd2, hbp_lo_k, hbp_hi_k, hbp_disj_k, hbat_k⟩ := hdescs k (by omega) hk'
              have hne_out : ∀ d < 3, stNext.mem (outDescPtr + 1 + 3 * k + d) = st.mem (outDescPtr + 1 + 3 * k + d) :=
                fun d hd => hfr_below_out _ (by omega) (hout_disj_foot _ (by omega) (by omega))
                  (Or.inl (by omega)) (fun hf => by
                    rcases htfc _ hf with h0 | ⟨h1', _⟩
                    · have := htfoot_disj_out _ h0; omega
                    · omega)
              refine ⟨hs_k, bp_k, tw_k, (hne_out 0 (by decide)).trans hd0, (hne_out 1 (by decide)).trans hd1,
                (hne_out 2 (by decide)).trans hd2, hbp_lo_k, by omega,
                fun a ha1 ha2 hf => by
                  rcases htfN a hf with h0 | ⟨h1', _⟩
                  · exact hbp_disj_k a ha1 ha2 h0
                  · omega,
                fun B₁ hS1 => ?_⟩
              obtain ⟨hBAt_k, lens_k, hlen_k, hsum_k, hbl_k⟩ := hbat_k B₁ hS1
              have htw_pos : 1 ≤ tw_k := hBAt_k.1.1
              have hbat_eq : ∀ a, bp_k ≤ a → a < bp_k + tw_k → stNext.mem a = st.mem a := fun a ha1 ha2 =>
                hfr_below_out a (by omega) (fun hf => by have := hfoot_lt a hf; omega)
                  (Or.inr (by omega)) (hbp_disj_k a ha1 ha2)
              refine ⟨⟨⟨hBAt_k.1.1, (hbat_eq bp_k (le_refl _) (by omega)).trans hBAt_k.1.2.1,
                batchBodyAt_agree hBAt_k.1.2.2 fun a ha1 ha2 => hbat_eq a (by omega) (by omega)⟩, hBAt_k.2⟩,
                lens_k, hlen_k, hsum_k, hbl_k.of_agree fun j hj => hbat_eq (bp_k + 1 + j) (by omega) (by omega)⟩
          · intro a ha hnf hout hnt
            rw [hfr_below_out a (by omega) hnf (by omega) (fun hf => by
              rcases htfc a hf with h0 | ⟨h1', _⟩; exact hnt h0; omega)]
            exact hfrc a ha hnf hout hnt
        · have hget : touched.getD i 0 = s := List.getD_eq_getElem touched 0 hi
          have hdl : ((B₀.edges ∩ D).sort (· ≤ ·)).length = (B₀.edges ∩ D).card := Finset.length_sort _
          have hcl : ((candSet js).sort (· ≤ ·)).length = (candSet js).card := Finset.length_sort _
          dsimp only [stepCost, stNext]; rw [hget]; simp only [hs_lt, ↓reduceDIte]
          rw [hdl, hcl, ← h1, ← h2, ← h3] at hcEm
          dsimp only [js] at hcEm
          clear * - hcEm; omega)
  -- Final `.ret (.reg 11)`
  rcases hInvE with ⟨_, hr11E, _, hhSE, hhHiE, hzfE, htrE, htfE, hEmitE, _, hcur0E, hkaE, hout0E, hdescsE, hfrE⟩
  have hret : Runs w pProg ω (.ret (.reg 11)) stE (.returned hEnd) stE 2 :=
    runs_ret_iff.mpr ⟨hEnd, by simp [Expr.eval, hr11E], rfl, rfl, rfl⟩
  have hfull := bundle_runs_seq_normal ha8 (bundle_runs_seq_normal ha9 (bundle_runs_seq_normal ha10
    (bundle_runs_seq_normal ha11 (bundle_runs_seq_normal hcallD (bundle_runs_seq_normal hstCnt1
      (bundle_runs_seq_normal hcallS (bundle_runs_seq_normal ha12S (bundle_runs_seq_normal hstOut0
        (bundle_runs_seq_normal hrunE hret)))))))))
  have hS_final_eq : S_pref touched.length = tableAfterStep S₀ D src' candSet := by
    funext j
    simp only [S_pref, List.take_length, tableAfterStep, S_del, tableDelEdges]
    cases hS0 : S₀ j with
    | none => simp
    | some B₀ =>
      by_cases hm : j.1 ∈ touched
      · simp [hm]
      · simp only [hm, ↓reduceIte]
        have hdj := hafterS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j
        rw [hS0] at hdj
        have hD0 : B₀.edges ∩ D = ∅ := by
          ext e; simp only [Finset.notMem_empty, iff_false]
          intro he; exact hm (hdj.1.mpr (Or.inl ⟨e, he⟩))
        have hC0 : candSet j = ∅ := by
          ext b; simp only [Finset.notMem_empty, iff_false]
          intro hb; exact hm (hdj.1.mpr (Or.inr ⟨b, hb⟩))
        have hsub : B₀.edges \ D = B₀.edges := by
          ext e; simp only [Finset.mem_sdiff, and_iff_left_iff_imp]
          intro he hD; exact Finset.notMem_empty e (hD0 ▸ Finset.mem_inter.mpr ⟨he, hD⟩)
        simp [byRootSplitFold, hD0, hC0, hsub]
  rw [hS_final_eq, List.drop_length] at hEmitE
  have hcur0E' : ∀ s < slotCap,
      stE.mem (btCurBunBase tbl slotCap eCap + s) = 0 ∧
      stE.mem (btCurTagBase tbl slotCap eCap + s) = 0 := fun s hs => by
    simpa [List.drop_length] using hcur0E s hs
  have hrepFinal := hEmitE.to_tableRepAt hcur0E'
  have hsp_end : bundleStepEmitTotalSpace TS S₀ D candSet scanLen (touched.take touched.length) =
      bundleStepEmitTotalSpace TS S₀ D candSet scanLen touched := by
    unfold bundleStepEmitTotalSpace; rw [List.take_length]
  rw [hsp_end] at hhHiE
  have hhEnd_hi : hEnd ≤ h₀ + bundleStepSpace TS S₀ D candSet scanLen cord' gs touched := by
    unfold bundleStepSpace; clear * - hhS_hi hhHiE; omega
  refine ⟨stE, _, hEnd, txEnd, maxIdxs, touched, hfull, hmaxLen, hmaxSpec, hndT, hltT, ?_,
    by clear * - hhS_lo hhSE; omega, hhEnd_hi, hzfE, htrE,
    fun a ha => by rcases htfE a ha with h0 | ⟨h1, h2⟩; exact Or.inl h0; exact Or.inr ⟨by clear * - h1; omega, h2⟩,
    hrepFinal, hkaE, hout0E,
    fun i hi => by
      obtain ⟨hs, bp, tw, h0, h1, h2, hlo, hhi, _, hbat⟩ := hdescsE i hi hi
      exact ⟨hs, bp, tw, h0, h1, h2, hlo, hhi, hbat⟩,
    hfrE, ?_⟩
  · intro j
    have hdj := hafterS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j
    cases hS0 : S₀ j with
    | none => rw [hS0] at hdj; exact hdj.2
    | some B₀ => rw [hS0] at hdj; exact hdj.1
  · have hrc := rangeCost_emit_eq TS eCap S₀ D candSet scanLen touched
    dsimp only [stepCost] at hcE
    rw [hrc] at hcE; simp only [Expr.size] at hcE
    rw [hphiS1] at hcE; rw [hphiD1] at hcS
    have hcE' : cE + htour.rep.phi tourH txEnd stE.mem ≤
        bundleStepEmitTotalCost TS eCap S₀ D
          (addCandsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) gs.length)
          (slotScannedEnds S₀ D cord' gs maxIdxs) touched +
        44 * touched.length + 7 + htour.rep.phi tourH txS stS.mem := by
      have h1 : bundleStepEmitTotalCost TS eCap S₀ D candSet scanLen touched + 35 * touched.length +
          touched.length * (1 + 8) + 1 + 1 + 5 + htour.rep.phi tourH txS stS.mem =
          bundleStepEmitTotalCost TS eCap S₀ D
            (addCandsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) gs.length)
            (slotScannedEnds S₀ D cord' gs maxIdxs) touched +
          44 * touched.length + 7 + htour.rep.phi tourH txS stS.mem := by
        dsimp only [candSet, scanLen, S_del]; ring
      exact h1 ▸ hcE
    exact bundleStep_cost_combine hrep0 hafterS
      ((List.toFinset_card_le _).trans (by simp [hdels_len])) hval_all hcD hcS hcE'

end

end MinCostFlow.SparseCore.Program
