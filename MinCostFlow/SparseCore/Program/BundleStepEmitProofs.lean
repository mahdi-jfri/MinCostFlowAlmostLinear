module

public import MinCostFlow.SparseCore.Program.BundleStepEmitPrep

/-!
# Full Phase 3 single-slot emission verification (`BundleStepEmitProofs`)

Verifies `bundleStepEmitSlotStmt` end-to-end (`bundleStepEmitSlot_runs`) together with the
exact `bundleRunsStep` equivalence corollary (`bundleStepEmitSlot_eq_bundleRunsStep`), running
in time and space proportional to the slot's scanned candidate ends `scan_j.length`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

public section

/-! ## 1. Main Phase 3 theorem: `bundleStepEmitSlot_runs` -/

set_option maxHeartbeats 400000 in
/-- End-to-end verification of `bundleStepEmitSlotStmt` on one touched slot `s ∈ remTouched`:
pops and sorts deletions and candidate bundles, builds the scanned-end CSR clearing
`btCurBunBase[s]`/`btCurTagBase[s]`, emits `BatchAt` (and `BatchBodyLensAt`) at a fresh
`batchPtr`, writes `[s, batchPtr, totalWords]` to `outDescPtr`, updates `BundleTableEmitState` by
erasing `s` from `remTouched` and replacing slot `s` with `(byRootSplitFold ...).2`, and respects
the space bound `bundleStepEmitSlotSpace` and amortized cost bound `bundleStepEmitSlotCost`
(both parameterized by `scan_j.length`). -/
theorem bundleStepEmitSlot_runs {TS : BundleTourSpec}
    {w slotCap vCap eCap tbl tourH s outDescPtr hStart hScanEnd h₀ pos : ℕ}
    {pProg : Program} {bDllPush bDllErase bMergeSort bTourList bTourLen bTourOwner : ℕ} {ω : ℕ → Bool}
    (htour : BundleTourAt TS w vCap eCap pProg bTourList bTourLen bTourOwner)
    {S₀ S_cur : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {candSet : Fin slotCap → Finset ℕ} {remTouched : List ℕ}
    {B₀ : BundleState} {p bunCap : ℕ}
    {cord' : ℕ → List End} {src' : End → ℕ} {scan_j : List (ℕ × ℕ × ℕ)}
    {tx₀ : htour.rep.τ} {mem₀ : ℕ → ℕ}
    (hpPush : pProg.HasAt bDllPush [bundleDllPushStmt])
    (hpErase : pProg.HasAt bDllErase [bundleDllEraseStmt])
    (hMergeSort : ∀ L : List ℕ, MeetsContract w pProg bMergeSort (mergeSortContract w L))
    (hw16 : 16 ≤ 2 ^ w) (htourH_w : tourH < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hblks_w : ∀ js : Fin slotCap, ∀ q c, m.slotBlocks js = some (q, c) →
      q + bundleSlotBlockSize c < 2 ^ w)
    (hs_mem : s ∈ remTouched) (hs_lt : s < slotCap)
    (hS₀s : S₀ ⟨s, hs_lt⟩ = some B₀)
    (hblks : m.slotBlocks ⟨s, hs_lt⟩ = some (p, bunCap))
    (hhStart_pos : 1 ≤ hStart) (hhStart_le : hStart ≤ hScanEnd) (hhScan_le : hScanEnd ≤ h₀)
    (htbl_le_hStart : tbl + bundleTableFixedSize slotCap eCap ≤ hStart)
    (hp_disj_scan : p + bundleSlotBlockSize bunCap ≤ hStart ∨ hScanEnd ≤ p)
    (hout_w : outDescPtr + 3 < 2 ^ w)
    (hout_lt : outDescPtr + 3 ≤ h₀)
    (hout_disj_foot : ∀ a, outDescPtr ≤ a → a < outDescPtr + 3 → ¬ bundleTableFoot eCap tbl m a)
    (hfoot_lt : ∀ a, bundleTableFoot eCap tbl m a → a < h₀)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h₀)
    (htfoot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a → ¬ bundleTableFoot eCap tbl m a)
    (htfoot_disj_out : ∀ a, htour.rep.foot tourH tx₀ a → a < outDescPtr ∨ outDescPtr + 3 ≤ a)
    (hzero : ZeroFrom mem₀ h₀)
    (htrep : htour.rep.rep tourH cord' tx₀ mem₀)
    (hemit : BundleTableEmitState slotCap vCap eCap tbl S₀ D m candSet S_cur remTouched mem₀)
    (hsrc_lt : ∀ x ∈ edgeEnds (B₀.edges \ D), src' x < vCap)
    (hsrc_mem : ∀ x ∈ edgeEnds (B₀.edges \ D), x ∈ cord' (src' x))
    (hsrc_uniq : ∀ x ∈ edgeEnds (B₀.edges \ D), ∀ v', x ∈ cord' v' → v' = src' x)
    (hval : ScanValidForSlot { B₀ with edges := B₀.edges \ D } src' (candSet ⟨s, hs_lt⟩) scan_j)
    (hscan : ScanNodesAt eCap mem₀ hStart hScanEnd (mem₀ (btCurBunBase tbl slotCap eCap + s)) scan_j)
    (htag : mem₀ (btCurTagBase tbl slotCap eCap + s) = scan_j.length)
    (hnb_cap : B₀.vertices.card + scan_j.length ≤ bunCap)
    (hh_sp : h₀ + bundleStepEmitSlotSpace TS (B₀.edges ∩ D).card (candSet ⟨s, hs_lt⟩).card
      scan_j.length < 2 ^ w) :
    let dels := (B₀.edges ∩ D).sort (· ≤ ·)
    let cands := (candSet ⟨s, hs_lt⟩).sort (· ≤ ·)
    let fast := byRootSplitFold B₀ (B₀.edges \ D) src' (dels.map Update.delete) cands
    let S_next : BundleTableState slotCap := Function.update S_cur ⟨s, hs_lt⟩ (some fast.2)
    ∃ st' c h' tx' batchPtr totalWords,
      Runs w pProg ω (bundleStepEmitSlotStmt bDllPush bDllErase bMergeSort bTourOwner)
        (startState [tbl, tourH, s, outDescPtr, h₀] mem₀ pos) (.returned h') st' c ∧
      h₀ ≤ h' ∧ h' ≤ h₀ + bundleStepEmitSlotSpace TS dels.length cands.length scan_j.length ∧
      h₀ ≤ batchPtr ∧ batchPtr + totalWords ≤ h' ∧
      ZeroFrom st'.mem h' ∧
      htour.rep.rep tourH cord' tx' st'.mem ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx₀ a ∨ (batchPtr + totalWords ≤ a ∧ a < h')) ∧
      BundleTableEmitState slotCap vCap eCap tbl S₀ D m candSet S_next (remTouched.erase s) st'.mem ∧
      st'.mem (btCurBunBase tbl slotCap eCap + s) = 0 ∧
      st'.mem (btCurTagBase tbl slotCap eCap + s) = 0 ∧
      SmallBatchAt st'.mem batchPtr B₀.graph fast.1 totalWords ∧
      (∃ lens, lens.length = fast.1.length ∧ lens.sum = totalWords - 1 ∧
        BatchBodyLensAt st'.mem (batchPtr + 1) B₀.graph fast.1 lens) ∧
      st'.mem outDescPtr = s ∧ st'.mem (outDescPtr + 1) = batchPtr ∧ st'.mem (outDescPtr + 2) = totalWords ∧
      (∀ a < h₀, ¬ bundleTableCoreFoot eCap tbl m a →
        a ≠ btCurBunBase tbl slotCap eCap + s → a ≠ btCurTagBase tbl slotCap eCap + s →
        (a < outDescPtr ∨ outDescPtr + 3 ≤ a) →
        ¬ htour.rep.foot tourH tx₀ a → st'.mem a = mem₀ a) ∧
      c + htour.rep.phi tourH tx' st'.mem ≤
        bundleStepEmitSlotCost TS eCap dels.length cands.length scan_j.length +
        htour.rep.phi tourH tx₀ mem₀ := by
  intro dels cands fast S_next
  set B_del : BundleState := { B₀ with edges := B₀.edges \ D }
  set js : Fin slotCap := ⟨s, hs_lt⟩
  have hemit_copy := hemit
  rcases hemit with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hS_rel, _, _, hslots, _, _, _, _, hdel, _⟩
  have hS_js : S_cur js = some B_del := by
    have hr := hS_rel js; rw [hS₀s] at hr
    cases hSc : S_cur js with
    | none => rw [hSc] at hr; exact False.elim hr
    | some Bc => rw [hSc] at hr; congr 1; exact hr.2 hs_mem
  have hslot_js := hslots js; rw [hS_js, hblks] at hslot_js; simp only [js, hs_mem, ↓reduceIte] at hslot_js
  obtain ⟨_, hp_disj_tbl, hrepCand_js⟩ := hslot_js
  obtain ⟨nB₀, hV₀, _, hE₀_lt, _, _, _, _, _, _, _, _, _, _, hcand_lt0, _, _⟩ := hrepCand_js
  have hdel_js := hdel js; rw [hS₀s] at hdel_js; simp only [js, hs_mem, ↓reduceIte] at hdel_js
  obtain ⟨dL, hdL_sll, hdL_mem⟩ := hdel_js
  have hdels_len : dels.length = (B₀.edges ∩ D).card := Finset.length_sort _
  have hcands_len : cands.length = (candSet js).card := Finset.length_sort _
  have hh_sp' : h₀ + (2 + 4 * dels.length + 3 * cands.length + (17 + 2 * TS.querySpace) * scan_j.length) < 2 ^ w := by
    rw [hdels_len, hcands_len]; exact hh_sp
  have htbl_h : tbl + bundleTableFixedSize slotCap eCap ≤ h₀ := le_trans htbl_le_hStart (le_trans hhStart_le hhScan_le)
  have hp_h : p + bundleSlotBlockSize bunCap ≤ h₀ := by
    have := hfoot_lt (p + bundleSlotBlockSize bunCap - 1)
      (Or.inr ⟨js, p, bunCap, hblks, by unfold bundleSlotBlockSize; omega, by unfold bundleSlotBlockSize; omega⟩)
    unfold bundleSlotBlockSize at this ⊢; omega
  have hp_w : p + bundleSlotBlockSize bunCap < 2 ^ w := hblks_w js p bunCap hblks
  have hL := emitSlotLayout_mk hs_lt htbl_w htbl_h hp_disj_tbl
  have hend_lt : ∀ x ∈ edgeEnds B_del.edges, endKey x < 2 * eCap := fun x hx => by
    have := hE₀_lt x.1 ((mem_edgeEnds _ _).mp hx)
    rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
  set hB := h₀ + 2 * dels.length + 2 * cands.length
  set offPtr := hB + 2 * scan_j.length
  set bufPtr := offPtr + cands.length + 1
  set hCSR := bufPtr + scan_j.length
  set hC := hCSR + 1 + 2 * dels.length + 6 * scan_j.length
  have hsp_mul : (17 + 2 * TS.querySpace) * scan_j.length =
      9 * scan_j.length + (8 + 2 * TS.querySpace) * scan_j.length := by ring
  have hsp_cands : hC + (8 + 2 * TS.querySpace) * scan_j.length < 2 ^ w := by
    change h₀ + 2 * dels.length + 2 * cands.length + 2 * scan_j.length + cands.length + 1 +
      scan_j.length + 1 + 2 * dels.length + 6 * scan_j.length + (8 + 2 * TS.querySpace) * scan_j.length < 2 ^ w
    clear * - hh_sp' hsp_mul; omega
  -- Steps 0 + 3A + 3B + 3B' + 3C via `bundleStepEmitSlot_prep_runs`
  obtain ⟨stC, cPrep, hrunPrep, hr1C, hr2C, hr3C, hr4C, hr6C, hr7C, hr8C, hr9C, hr10C, hr11C, hr12C,
    hr13C, hr14C, hr18C, hr19C, hr20C, hr21C, hr22C, hdelH0, hdL0, hcandH0, hcurB0, hcurT0,
    hbatC, hGC, hzfC, htrC, hphiC, hrep_C, heb_C, hcandLat_C, hcsr_C, hfr_toC, hcPrep⟩ :=
    bundleStepEmitSlot_prep_runs (htour := htour) (ω := ω) (outDescPtr := outDescPtr) (pos := pos)
      (hStart := hStart) (hScanEnd := hScanEnd) (scan_j := scan_j) (src' := src')
      hMergeSort hw16 hpk_w htbl_w hp_w hs_mem hs_lt hS₀s hblks hhStart_pos hhStart_le hhScan_le
      htbl_le_hStart hp_disj_scan hfoot_lt htfoot_lt htfoot_disj_tbl
      hzero htrep hemit_copy hsrc_lt hval hscan htag hh_sp'
  -- Step 3D: candsLoop
  have hnb_cap' : nB₀ + scan_j.length ≤ bunCap := by
    have : B₀.vertices.card = nB₀ := by rw [show B₀.vertices = B_del.vertices from rfl, hV₀, Finset.card_range]
    clear * - hnb_cap this; omega
  obtain ⟨stD, cD, txD, hD, totalWords, hrunD, hregsD, hr4D, hhD_lo, hhD_hi, hr21D, htw_lo, htw_hi,
    hr22D, hrepD, hED, hGD, hbatD, hebD, htrD, htfD, hzfD, hfrD, hcD⟩ :=
    bundleStepEmitSlot_candsLoop (htour := htour) (ω := ω) (st₀ := stC) (G₀ := B₀.graph)
      (ops₀ := dels.map Update.delete) (B₀ := B_del) (cands := cands) (candSet_j := candSet js)
      (scan_j := scan_j) (nB₀ := nB₀)
      (p := p) (bunCap := bunCap) (tourH := tourH) (candArr := h₀ + 2 * dels.length)
      (offPtr := offPtr) (bufPtr := bufPtr)
      (batchPtr := hCSR) (writeOff₀ := 1 + 2 * dels.length) (updCnt₀ := dels.length)
      (prevBase := btEndPrevBase tbl slotCap eCap) (nextBase := btEndNextBase tbl slotCap eCap)
      (endBundleBase := btEndBundleBase tbl slotCap eCap) (h₀ := hC)
      hpPush hpErase hMergeSort hw16 htourH_w hL.e2_w hpk_w
      hL.prev_w hL.next_w hL.eb_w hp_w
      (by clear * - hh_sp'; omega) (by clear * - hsp_cands; omega) (by clear * - hsp_cands; omega)
      (by clear * - hsp_cands; omega) (by clear * - hsp_cands; omega)
      hsp_cands hV₀ (Finset.sort_nodup _ _)
      (fun b hb => hcand_lt0 b ((Finset.mem_sort (· ≤ ·)).mp hb))
      (fun b hb => (Finset.mem_sort (· ≤ ·)).mp hb)
      (fun t ht => (Finset.mem_sort (· ≤ ·)).mpr (hval.2.1 t ht).1)
      hval hnb_cap' hsrc_lt hsrc_mem hsrc_uniq
      (Or.inl hL.prev_le_next) hL.blk_disj_prev hL.blk_disj_next
      (Or.inl hL.eb_le_prev) (Or.inl (le_trans hL.eb_le_prev (le_trans (Nat.le_add_right _ _) hL.prev_le_next)))
      (hL.blk_disj_eb.symm)
      (Or.inr (le_trans hp_h (by clear * -; omega)))
      (Or.inr (le_trans hL.prev_le_h (by clear * -; omega)))
      (Or.inr (le_trans hL.next_le_h (by clear * -; omega)))
      (Or.inr (le_trans hL.eb_le_h (by clear * -; omega)))
      (by clear * -; omega)
      (le_trans hp_h (by clear * -; omega)) (le_trans hL.prev_le_h (by clear * -; omega))
      (le_trans hL.next_le_h (by clear * -; omega)) (le_trans hL.eb_le_h (by clear * -; omega))
      (by clear * -; omega)
      (Or.inr (le_trans hp_h (Nat.le_add_right _ _)))
      (Or.inr (le_trans hL.prev_le_h (Nat.le_add_right _ _)))
      (Or.inr (le_trans hL.next_le_h (Nat.le_add_right _ _)))
      (Or.inr (le_trans hL.eb_le_h (Nat.le_add_right _ _)))
      (Or.inl (by clear * -; omega))
      (by clear * -; omega)
      (Or.inr (le_trans hp_h (by clear * -; omega)))
      (Or.inr (le_trans hL.prev_le_h (by clear * -; omega)))
      (Or.inr (le_trans hL.next_le_h (by clear * -; omega)))
      (Or.inr (le_trans hL.eb_le_h (by clear * -; omega)))
      (Or.inl (by clear * -; omega))
      (by clear * -; omega)
      (Or.inr (le_trans hp_h (by clear * -; omega)))
      (Or.inr (le_trans hL.prev_le_h (by clear * -; omega)))
      (Or.inr (le_trans hL.next_le_h (by clear * -; omega)))
      (Or.inr (le_trans hL.eb_le_h (by clear * -; omega)))
      (Or.inl (by clear * -; omega))
      htrC (fun a ha => lt_of_lt_of_le (htfoot_lt a ha) (by clear * -; omega))
      (fun a ha => by
        by_contra hnot; push Not at hnot
        exact htfoot_disj_tbl a ha (Or.inr ⟨js, p, bunCap, hblks, hnot.1, hnot.2⟩))
      (fun a ha => by
        by_contra hnot; push Not at hnot
        exact htfoot_disj_tbl a ha (by
          have h := btEndPrev_in_foot (tbl := tbl) (slotCap := slotCap) (eCap := eCap) (m := m)
            (k := a - btEndPrevBase tbl slotCap eCap) (by clear * - hnot; omega)
          rwa [Nat.add_sub_cancel' hnot.1] at h))
      (fun a ha => by
        by_contra hnot; push Not at hnot
        exact htfoot_disj_tbl a ha (by
          have h := btEndNext_in_foot (tbl := tbl) (slotCap := slotCap) (eCap := eCap) (m := m)
            (k := a - btEndNextBase tbl slotCap eCap) (by clear * - hnot; omega)
          rwa [Nat.add_sub_cancel' hnot.1] at h))
      (fun a ha => by
        by_contra hnot; push Not at hnot
        exact htfoot_disj_tbl a ha (by
          have h := btEndBundle_in_foot (tbl := tbl) (slotCap := slotCap) (eCap := eCap) (m := m)
            (k := a - btEndBundleBase tbl slotCap eCap) (by clear * - hnot; omega)
          rwa [Nat.add_sub_cancel' hnot.1] at h))
      (fun a ha => Or.inl (lt_of_lt_of_le (htfoot_lt a ha) (by clear * -; omega)))
      (fun a ha => Or.inl (lt_of_lt_of_le (htfoot_lt a ha) (by clear * -; omega)))
      (fun a ha => Or.inl (lt_of_lt_of_le (htfoot_lt a ha) (by clear * -; omega)))
      (fun a ha => Or.inl (lt_of_lt_of_le (htfoot_lt a ha) (by clear * -; omega)))
      hzfC hrep_C heb_C hGC (by rw [show 1 + 2 * dels.length - 1 = 2 * dels.length by clear * -; omega]; exact batchBodyAt_deletes_small hbatC)
      (by clear * -; omega) (by simp) hcandLat_C hcsr_C
      hr1C hr4C hr6C hr7C hr8C hr9C hr10C hr11C hr13C hr14C hr18C hr19C hr20C hr21C hr22C
  have hvr_eq : ∀ b, byRootVRuns B_del B_del.edges src' b = byRootVRuns B₀ (B₀.edges \ D) src' b := fun b => by
    have hs_eq : survivingEnds B_del B_del.edges b = survivingEnds B₀ (B₀.edges \ D) b := by
      ext x; simp only [survivingEnds, BundleState.mem_ends, Finset.mem_filter, Finset.mem_sdiff, B_del]; tauto
    simp only [byRootVRuns, rawByRootVRuns, finalRootsOf, hs_eq]
  have hfast_eq :
      ((cands.map fun b => (b, byRootVRuns B_del B_del.edges src' b)).foldl runsFoldStep
        (dels.map Update.delete, B_del)) = fast := by
    simp only [fast, byRootSplitFold, hvr_eq]; rfl
  rw [hfast_eq] at hr22D hrepD hED hGD hbatD hebD
  -- Step 3E: 5 tail stores + `.ret (.reg 4)`
  have hr2D : stD.regs 2 = s := (hregsD 2 (by decide) (by decide) (by decide) (by decide)).trans hr2C
  have hr3D : stD.regs 3 = outDescPtr := (hregsD 3 (by decide) (by decide) (by decide) (by decide)).trans hr3C
  have hr12D : stD.regs 12 = btSlotTouchedBase tbl slotCap eCap := (hregsD 12 (by decide) (by decide) (by decide) (by decide)).trans hr12C
  have hr20D : stD.regs 20 = hCSR := (hregsD 20 (by decide) (by decide) (by decide) (by decide)).trans hr20C
  let m1 := Function.update stD.mem (btSlotTouchedBase tbl slotCap eCap + s) 0
  let m2 := Function.update m1 hCSR fast.1.length
  let m3 := Function.update m2 outDescPtr s
  let m4 := Function.update m3 (outDescPtr + 1) hCSR
  let m5 := Function.update m4 (outDescPtr + 2) totalWords
  let stEnd : State := { stD with mem := m5 }
  have hst1 : Runs w pProg ω (.store (.bin .add (.reg 12) (.reg 2)) (.const 0)) stD .normal { stD with mem := m1 } 5 :=
    runs_store_iff.mpr ⟨btSlotTouchedBase tbl slotCap eCap + s, 0,
      by simp [Expr.eval, BinOp.eval, hr12D, hr2D, hL.tch_w],
      by simp [Expr.eval, show 0 < 2 ^ w by clear * - hw16; omega], rfl, rfl, rfl⟩
  have hst2 : Runs w pProg ω (.store (.reg 20) (.reg 22)) { stD with mem := m1 } .normal { stD with mem := m2 } 3 :=
    runs_store_iff.mpr ⟨hCSR, fast.1.length, by simp [Expr.eval, hr20D], by simp [Expr.eval, hr22D], rfl, rfl, rfl⟩
  have hst3 : Runs w pProg ω (.store (.reg 3) (.reg 2)) { stD with mem := m2 } .normal { stD with mem := m3 } 3 :=
    runs_store_iff.mpr ⟨outDescPtr, s, by simp [Expr.eval, hr3D], by simp [Expr.eval, hr2D], rfl, rfl, rfl⟩
  have hst4 : Runs w pProg ω (.store (.bin .add (.reg 3) (.const 1)) (.reg 20)) { stD with mem := m3 } .normal { stD with mem := m4 } 5 :=
    runs_store_iff.mpr ⟨outDescPtr + 1, hCSR,
      by simp [Expr.eval, BinOp.eval, hr3D, show 1 < 2 ^ w by clear * - hw16; omega, show outDescPtr + 1 < 2 ^ w by clear * - hout_w; omega],
      by simp [Expr.eval, hr20D], rfl, rfl, rfl⟩
  have hst5 : Runs w pProg ω (.store (.bin .add (.reg 3) (.const 2)) (.reg 21)) { stD with mem := m4 } .normal stEnd 5 :=
    runs_store_iff.mpr ⟨outDescPtr + 2, totalWords,
      by simp [Expr.eval, BinOp.eval, hr3D, show 2 < 2 ^ w by clear * - hw16; omega, show outDescPtr + 2 < 2 ^ w by clear * - hout_w; omega],
      by simp [Expr.eval, hr21D], rfl, rfl, rfl⟩
  have hret : Runs w pProg ω (.ret (.reg 4)) stEnd (.returned hD) stEnd 2 :=
    runs_ret_iff.mpr ⟨hD, by simp [Expr.eval, stEnd, hr4D], rfl, rfl, rfl⟩
  have htail := bundle_runs_seq_normal hst1 (bundle_runs_seq_normal hst2 (bundle_runs_seq_normal hst3
    (bundle_runs_seq_normal hst4 (bundle_runs_seq_normal hst5 hret))))
  have hfull := hrunPrep (bundle_runs_seq_normal hrunD htail)
  -- Memory frame helpers
  have hm5_eq : ∀ a, a ≠ btSlotTouchedBase tbl slotCap eCap + s → a ≠ hCSR →
      (a < outDescPtr ∨ outDescPtr + 3 ≤ a) → stEnd.mem a = stD.mem a := fun a h1 h2 h3 => by
    dsimp only [stEnd, m5, m4, m3, m2, m1]
    rw [Function.update_of_ne (by clear * - h3; omega), Function.update_of_ne (by clear * - h3; omega),
        Function.update_of_ne (by clear * - h3; omega), Function.update_of_ne h2, Function.update_of_ne h1]
  have hlocEnd := htour.rep_local tourH cord' txD stD.mem stEnd.mem fun a ha => by
    rcases htfD a ha with h0 | ⟨h1, _⟩
    · exact (hm5_eq a (fun heq => htfoot_disj_tbl a h0 (heq ▸ btSlotTouched_in_foot hs_lt))
        (by have := htfoot_lt a h0; clear * - this; omega) (htfoot_disj_out a h0)).symm
    · exact (hm5_eq a (by have := hL.tch_lt_h; clear * - h1 this; omega)
        (by clear * - h1; omega) (Or.inr (by clear * - hout_lt h1; omega))).symm
  have hbatEnd : SmallBatchBodyAt stEnd.mem (hCSR + 1) B₀.graph fast.1 (totalWords - 1) :=
    smallBatchBodyAt_agree hbatD fun a ha1 _ => hm5_eq a
      (by have := hL.tch_lt_h; clear * - ha1 this; omega) (by clear * - ha1; omega)
      (Or.inr (by clear * - hout_lt ha1; omega))
  have hbatchAt : SmallBatchAt stEnd.mem hCSR B₀.graph fast.1 totalWords :=
    hbatEnd.to_smallBatchAt (by clear * - htw_lo; omega)
      (by dsimp only [stEnd, m5, m4, m3, m2]
          rw [Function.update_of_ne (by clear * - hout_lt; omega), Function.update_of_ne (by clear * - hout_lt; omega),
              Function.update_of_ne (by clear * - hout_lt; omega), Function.update_self])
  have htbl_unch : ∀ a < h₀, a ≠ btSlotTouchedBase tbl slotCap eCap + s →
      a ≠ btSlotDelHeadBase tbl slotCap eCap + s → (∀ e ∈ B₀.edges ∩ D, a ≠ btSlotDelNextBase tbl slotCap eCap + e) →
      a ≠ btSlotCandHeadBase tbl slotCap eCap + s →
      a ≠ btCurBunBase tbl slotCap eCap + s → a ≠ btCurTagBase tbl slotCap eCap + s →
      (a < p ∨ p + bundleSlotBlockSize bunCap ≤ a) →
      (∀ x ∈ edgeEnds B_del.edges, a ≠ btEndPrevBase tbl slotCap eCap + endKey x ∧
        a ≠ btEndNextBase tbl slotCap eCap + endKey x ∧ a ≠ btEndBundleBase tbl slotCap eCap + endKey x) →
      (a < outDescPtr ∨ outDescPtr + 3 ≤ a) → ¬ htour.rep.foot tourH tx₀ a → stEnd.mem a = mem₀ a :=
    fun a ha0 h1 h2 h3 h4 hcb hct h5 h6 h7 h8 => by
      rw [hm5_eq a h1 (by clear * - ha0; omega) h7,
        hfrD a h8 h5 h6 (Or.inl (by clear * - ha0; omega)) (Or.inl (by clear * - ha0; omega)),
        hfr_toC a ha0 h2 h3 h4 hcb hct (by unfold bsInCandBase; clear * - h5; omega)]
  have hEmitEnd : BundleTableEmitState slotCap vCap eCap tbl S₀ D m candSet S_next (remTouched.erase s) stEnd.mem :=
    bundleStepEmitSlot_postEmit hs_mem hs_lt hS₀s hblks hemit_copy hED
      (hrepD.of_agree
        (fun a h1 h2 => (hm5_eq a (by have := hL.blk_disj_tch; clear * - h1 h2 this; omega)
          (by clear * - h2 hp_h; omega)
          (by by_contra hnot; push Not at hnot
              exact hout_disj_foot a hnot.1 hnot.2 (Or.inr ⟨js, p, bunCap, hblks, h1, h2⟩))).symm)
        (fun k hk => (hm5_eq _ (by have h1 := hL.prev_le_next; have h2 := hL.next_le_tch; clear * - hk h1 h2; omega)
          (by have := hL.prev_le_h; clear * - hk this; omega)
          (by by_contra hnot; push Not at hnot; exact hout_disj_foot _ hnot.1 hnot.2 (btEndPrev_in_foot hk))).symm)
        (fun k hk => (hm5_eq _ (by have := hL.next_le_tch; clear * - hk this; omega)
          (by have := hL.next_le_h; clear * - hk this; omega)
          (by by_contra hnot; push Not at hnot; exact hout_disj_foot _ hnot.1 hnot.2 (btEndNext_in_foot hk))).symm))
      (fun x hx => by
        have hxk := hend_lt x hx
        rw [hm5_eq _ (by have h1 := hL.eb_le_prev; have h2 := hL.prev_le_next; have h3 := hL.next_le_tch; clear * - hxk h1 h2 h3; omega)
          (by have := hL.eb_le_h; clear * - hxk this; omega)
          (by by_contra hnot; push Not at hnot; exact hout_disj_foot _ hnot.1 hnot.2 (btEndBundle_in_foot hxk))]
        exact hebD x hx)
      (by dsimp only [stEnd, m5, m4, m3, m2, m1]
          rw [Function.update_of_ne (by by_contra h; exact hout_disj_foot _ (by clear * - h; omega) (by clear * - h; omega) (btSlotTouched_in_foot hs_lt)),
              Function.update_of_ne (by by_contra h; exact hout_disj_foot _ (by clear * - h; omega) (by clear * - h; omega) (btSlotTouched_in_foot hs_lt)),
              Function.update_of_ne (by by_contra h; exact hout_disj_foot _ (by clear * - h; omega) (by clear * - h; omega) (btSlotTouched_in_foot hs_lt)),
              Function.update_of_ne (by have := hL.tch_lt_h; clear * - this; omega), Function.update_self])
      (by rw [hm5_eq _ (by have := hL.tch_le_delH; clear * - hs_lt this; omega)
            (by have := hL.delH_le_h; clear * - hs_lt this; omega)
            (by by_contra hnot; push Not at hnot; exact hout_disj_foot _ hnot.1 hnot.2 (btSlotDelHead_in_foot hs_lt)),
            hfrD _ (fun hf => htfoot_disj_tbl _ hf (btSlotDelHead_in_foot hs_lt)) hL.blk_disj_delH
              (fun x hx => by have hxk := hend_lt x hx; have h1 := hL.eb_le_prev; have h2 := hL.prev_le_next; have h3 := hL.next_le_tch; have h4 := hL.tch_le_delH
                              exact ⟨by clear * - hxk h2 h3 h4; omega, by clear * - hxk h3 h4; omega, by clear * - hxk h1 h2 h3 h4; omega⟩)
              (Or.inl (by have := hL.delH_le_h; clear * - hs_lt this; omega))
              (Or.inl (by have := hL.delH_le_h; clear * - hs_lt this; omega)), hdelH0])
      (fun e he => by
        have he_lt := hdL_sll.mem_lt e ((hdL_mem e).mpr he)
        rw [hm5_eq _ (by have h1 := hL.tch_le_delH; have h2 := hL.delH_le_delN; clear * - hs_lt h1 h2; omega)
          (by have := hL.delN_le_h; clear * - he_lt this; omega)
          (by by_contra hnot'; push Not at hnot'; exact hout_disj_foot _ hnot'.1 hnot'.2 (btSlotDelNext_in_foot he_lt)),
          hfrD _ (fun hf => htfoot_disj_tbl _ hf (btSlotDelNext_in_foot he_lt)) (hL.blk_disj_delN e he_lt)
            (fun x hx => by have hxk := hend_lt x hx; have h1 := hL.eb_le_prev; have h2 := hL.prev_le_next; have h3 := hL.next_le_tch; have h4 := hL.tch_le_delH; have h5 := hL.delH_le_delN
                            exact ⟨by clear * - hxk h2 h3 h4 h5; omega, by clear * - hxk h3 h4 h5; omega, by clear * - hxk h1 h2 h3 h4 h5; omega⟩)
            (Or.inl (by have := hL.delN_le_h; clear * - he_lt this; omega))
            (Or.inl (by have := hL.delN_le_h; clear * - he_lt this; omega)), hdL0 e he])
      (by rw [hm5_eq _ (by have h1 := hL.tch_le_delH; have h2 := hL.delH_le_delN; have h3 := hL.delN_le_candH; clear * - hs_lt h1 h2 h3; omega)
            (by have := hL.candH_le_h; clear * - hs_lt this; omega)
            (by by_contra hnot; push Not at hnot; exact hout_disj_foot _ hnot.1 hnot.2 (btSlotCandHead_in_foot hs_lt)),
            hfrD _ (fun hf => htfoot_disj_tbl _ hf (btSlotCandHead_in_foot hs_lt))
              (by have := hL.blk_disj_candH; clear * - hs_lt this; omega)
              (fun x hx => by have hxk := hend_lt x hx; have h1 := hL.eb_le_prev; have h2 := hL.prev_le_next; have h3 := hL.next_le_tch; have h4 := hL.tch_le_delH; have h5 := hL.delH_le_delN; have h6 := hL.delN_le_candH
                              exact ⟨by clear * - hxk h2 h3 h4 h5 h6; omega, by clear * - hxk h3 h4 h5 h6; omega, by clear * - hxk h1 h2 h3 h4 h5 h6; omega⟩)
              (Or.inl (by have := hL.candH_le_h; clear * - hs_lt this; omega))
              (Or.inl (by have := hL.candH_le_h; clear * - hs_lt this; omega)), hcandH0])
      (fun a hfa h1 h2 h3 h4 hcb hct h5 h6 =>
        htbl_unch a (hfoot_lt a hfa) h1 h2 h3 h4 hcb hct h5 h6
          (by by_contra hnot; push Not at hnot; exact hout_disj_foot a hnot.1 hnot.2 hfa)
          (fun hf => htfoot_disj_tbl a hf hfa))
  have hcurB_end : stEnd.mem (btCurBunBase tbl slotCap eCap + s) = 0 := by
    rw [hm5_eq _ (by have h1 := hL.tch_le_delH; have h2 := hL.delH_le_delN; have h3 := hL.delN_le_candH; have h4 := hL.candH_le_curB; clear * - hs_lt h1 h2 h3 h4; omega)
      (by have := hL.curB_le_h; clear * - hs_lt this; omega)
      (by by_contra hnot; push Not at hnot; exact hout_disj_foot _ hnot.1 hnot.2 (btCurBun_in_foot hs_lt)),
      hfrD _ (fun hf => htfoot_disj_tbl _ hf (btCurBun_in_foot hs_lt))
        (by have := hL.blk_disj_curB; clear * - hs_lt this; omega)
        (fun x hx => by have hxk := hend_lt x hx; have h1 := hL.eb_le_prev; have h2 := hL.prev_le_next; have h3 := hL.next_le_tch; have h4 := hL.tch_le_delH; have h5 := hL.delH_le_delN; have h6 := hL.delN_le_candH; have h7 := hL.candH_le_curB
                        exact ⟨by clear * - hxk h2 h3 h4 h5 h6 h7; omega, by clear * - hxk h3 h4 h5 h6 h7; omega, by clear * - hxk h1 h2 h3 h4 h5 h6 h7; omega⟩)
        (Or.inl (by have := hL.curB_le_h; clear * - hs_lt this; omega))
        (Or.inl (by have := hL.curB_le_h; clear * - hs_lt this; omega)), hcurB0]
  have hcurT_end : stEnd.mem (btCurTagBase tbl slotCap eCap + s) = 0 := by
    rw [hm5_eq _ (by have h1 := hL.tch_le_delH; have h2 := hL.delH_le_delN; have h3 := hL.delN_le_candH; have h4 := hL.candH_le_curB; have h5 := hL.curB_le_curT; clear * - hs_lt h1 h2 h3 h4 h5; omega)
      (by have := hL.curT_le_h; clear * - hs_lt this; omega)
      (by by_contra hnot; push Not at hnot; exact hout_disj_foot _ hnot.1 hnot.2 (btCurTag_in_foot hs_lt)),
      hfrD _ (fun hf => htfoot_disj_tbl _ hf (btCurTag_in_foot hs_lt))
        (by have := hL.blk_disj_curT; clear * - hs_lt this; omega)
        (fun x hx => by have hxk := hend_lt x hx; have h1 := hL.eb_le_prev; have h2 := hL.prev_le_next; have h3 := hL.next_le_tch; have h4 := hL.tch_le_delH; have h5 := hL.delH_le_delN; have h6 := hL.delN_le_candH; have h7 := hL.candH_le_curB; have h8 := hL.curB_le_curT
                        exact ⟨by clear * - hxk h2 h3 h4 h5 h6 h7 h8; omega, by clear * - hxk h3 h4 h5 h6 h7 h8; omega, by clear * - hxk h1 h2 h3 h4 h5 h6 h7 h8; omega⟩)
        (Or.inl (by have := hL.curT_le_h; clear * - hs_lt this; omega))
        (Or.inl (by have := hL.curT_le_h; clear * - hs_lt this; omega)), hcurT0]
  refine ⟨stEnd, _, hD, txD, hCSR, totalWords, hfull,
    by clear * - hhD_lo; omega,
    by unfold bundleStepEmitSlotSpace
       change hD ≤ hC + (8 + 2 * TS.querySpace) * scan_j.length at hhD_hi
       clear * - hhD_hi hsp_mul; omega,
    by clear * -; omega, by clear * - hhD_lo htw_hi; omega,
    fun a ha => (hm5_eq a (by have := hL.tch_lt_h; clear * - ha hhD_lo this; omega)
      (by clear * - ha hhD_lo; omega) (Or.inr (by clear * - ha hhD_lo hout_lt; omega))).trans (hzfD a ha),
    hlocEnd.1 htrD, fun a ha => by rcases htfD a ha with h0 | ⟨h1, h2⟩; exact Or.inl h0; exact Or.inr ⟨by clear * - h1 htw_hi; omega, h2⟩,
    hEmitEnd, hcurB_end, hcurT_end, hbatchAt, batchBodyAt_exists_lens hbatEnd.to_batchBodyAt,
    by dsimp only [stEnd, m5, m4, m3]; rw [Function.update_of_ne (by clear * -; omega), Function.update_of_ne (by clear * -; omega), Function.update_self],
    by dsimp only [stEnd, m5, m4]; rw [Function.update_of_ne (by clear * -; omega), Function.update_self],
    by dsimp only [stEnd, m5]; exact Function.update_self _ _ _,
    fun a ha hnf hcb hct hout hnt => htbl_unch a ha
      (fun heq => hnf (heq ▸ btSlotTouched_in_coreFoot hs_lt))
      (fun heq => hnf (heq ▸ btSlotDelHead_in_coreFoot hs_lt))
      (fun e he heq => hnf (heq ▸ btSlotDelNext_in_coreFoot (hdL_sll.mem_lt e ((hdL_mem e).mpr he))))
      (fun heq => hnf (heq ▸ btSlotCandHead_in_coreFoot hs_lt))
      hcb hct
      (by by_contra hnot; push Not at hnot; exact hnf (Or.inr ⟨js, p, bunCap, hblks, hnot.1, hnot.2⟩))
      (fun x hx => by
        have hxk := hend_lt x hx
        exact ⟨fun heq => hnf (heq ▸ btEndPrev_in_coreFoot hxk),
          fun heq => hnf (heq ▸ btEndNext_in_coreFoot hxk), fun heq => hnf (heq ▸ btEndBundle_in_coreFoot hxk)⟩)
      hout hnt, ?_⟩
  rw [← hlocEnd.2]
  rw [hphiC] at hcD
  change cPrep ≤ 300 * dels.length * (Nat.log 2 (dels.length + 1) + 1) +
    300 * cands.length * (Nat.log 2 (cands.length + 1) + 1) +
    80 * scan_j.length + 50 * cands.length + 430 at hcPrep
  change cD + htour.rep.phi tourH txD stD.mem ≤
    (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * scan_j.length + 1) + 1) + 920) * scan_j.length +
      429 * cands.length + 7 + htour.rep.phi tourH tx₀ mem₀ at hcD
  have hmul_c : (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * scan_j.length + 1) + 1) + 1050) * scan_j.length =
      (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * scan_j.length + 1) + 1) + 920) * scan_j.length +
      130 * scan_j.length := by ring
  unfold bundleStepEmitSlotCost; clear * - hcPrep hcD hmul_c; omega

/-! ## 5. Model equivalence corollary (`bundleStepEmitSlot_eq_bundleRunsStep`) -/

/-- Under `BundleStepReady`, when `D = batchDeletes U` and `candSet` equals `exactSplitCands`,
the batch `fast.1` and state `fast.2` produced by `bundleStepEmitSlot_runs` agree identically
with `bundleRunsStep cs B₀ k ord' U` on updates, vertices, edges, and `bundleOf`. -/
theorem bundleStepEmitSlot_eq_bundleRunsStep {cs : CompLSFState} {B₀ : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} {candSet : Finset ℕ}
    (h : BundleStepReady cs B₀ k ord ord' U)
    (hcand : candSet = (exactSplitCands B₀ (B₀.edges \ batchDeletes U)
      (Chain.coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src).toFinset) :
    let D := batchDeletes U
    let src' := (Chain.coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src
    let dels := (B₀.edges ∩ D).sort (· ≤ ·)
    let cands := candSet.sort (· ≤ ·)
    let fast := byRootSplitFold B₀ (B₀.edges \ D) src' (dels.map Update.delete) cands
    let res := bundleRunsStep cs B₀ k ord' U
    res.1 = fast.1 ∧ res.2.vertices = fast.2.vertices ∧
    res.2.edges = fast.2.edges ∧ res.2.bundleOf = fast.2.bundleOf := by
  intro D src' dels cands fast res
  have hcands_eq : cands = exactSplitCands B₀ (B₀.edges \ D) src' := by
    have hnd : (exactSplitCands B₀ (B₀.edges \ D) src').Nodup :=
      (Finset.sort_nodup _ _).filter _
    have hpw : (exactSplitCands B₀ (B₀.edges \ D) src').Pairwise (· ≤ ·) :=
      (Finset.pairwise_sort _ _).filter _
    have h1 := sorted_perm_eq_toFinset_sort hnd (List.Perm.refl _) hpw
    dsimp only [cands]; rw [hcand, ← h1]
  simpa only [fast, hcands_eq] using bundleRunsStep_eq_byRoot h

end

end MinCostFlow.SparseCore.Program
