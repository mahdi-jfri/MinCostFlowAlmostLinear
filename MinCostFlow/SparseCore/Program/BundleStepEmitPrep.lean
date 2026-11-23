module

public import MinCostFlow.SparseCore.Program.BundleStepEmitLoop

/-!
# Phase 3 slot preparation verification (`BundleStepEmitPrep`)

Proves `bundleStepEmitSlot_prep_runs`, covering the header loads, Phase 3A (`PopDels`),
Phase 3B (`PopCands`), Phase 3B' (`BuildCSR`), and Phase 3C (`DelRecs`) prefix of
`bundleStepEmitSlotStmt`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

public section

structure EmitSlotLayout (w slotCap eCap tbl p bunCap s h₀ : ℕ) : Prop where
  e2_w : 2 * eCap < 2 ^ w
  delH_w : btSlotDelHeadBase tbl slotCap eCap + slotCap < 2 ^ w
  delN_w : btSlotDelNextBase tbl slotCap eCap + eCap < 2 ^ w
  candH_w : btSlotCandHeadBase tbl slotCap eCap + slotCap < 2 ^ w
  curB_w : btCurBunBase tbl slotCap eCap + slotCap < 2 ^ w
  curT_w : btCurTagBase tbl slotCap eCap + slotCap < 2 ^ w
  eb_w : btEndBundleBase tbl slotCap eCap + 2 * eCap < 2 ^ w
  prev_w : btEndPrevBase tbl slotCap eCap + 2 * eCap < 2 ^ w
  next_w : btEndNextBase tbl slotCap eCap + 2 * eCap < 2 ^ w
  tch_w : btSlotTouchedBase tbl slotCap eCap + s < 2 ^ w
  delH_le_delN : btSlotDelHeadBase tbl slotCap eCap + slotCap ≤ btSlotDelNextBase tbl slotCap eCap
  delH_le_h : btSlotDelHeadBase tbl slotCap eCap + slotCap ≤ h₀
  delN_le_h : btSlotDelNextBase tbl slotCap eCap + eCap ≤ h₀
  candH_le_h : btSlotCandHeadBase tbl slotCap eCap + slotCap ≤ h₀
  curB_le_h : btCurBunBase tbl slotCap eCap + slotCap ≤ h₀
  curT_le_h : btCurTagBase tbl slotCap eCap + slotCap ≤ h₀
  eb_le_h : btEndBundleBase tbl slotCap eCap + 2 * eCap ≤ h₀
  prev_le_h : btEndPrevBase tbl slotCap eCap + 2 * eCap ≤ h₀
  next_le_h : btEndNextBase tbl slotCap eCap + 2 * eCap ≤ h₀
  tch_lt_h : btSlotTouchedBase tbl slotCap eCap + s < h₀
  eb_le_prev : btEndBundleBase tbl slotCap eCap + 2 * eCap ≤ btEndPrevBase tbl slotCap eCap
  prev_le_next : btEndPrevBase tbl slotCap eCap + 2 * eCap ≤ btEndNextBase tbl slotCap eCap
  next_le_tch : btEndNextBase tbl slotCap eCap + 2 * eCap ≤ btSlotTouchedBase tbl slotCap eCap
  tch_le_delH : btSlotTouchedBase tbl slotCap eCap + slotCap ≤ btSlotDelHeadBase tbl slotCap eCap
  delN_le_candH : btSlotDelNextBase tbl slotCap eCap + eCap ≤ btSlotCandHeadBase tbl slotCap eCap
  candH_le_curB : btSlotCandHeadBase tbl slotCap eCap + slotCap ≤ btCurBunBase tbl slotCap eCap
  curB_le_curT : btCurBunBase tbl slotCap eCap + slotCap ≤ btCurTagBase tbl slotCap eCap
  blk_disj_candH : p + bundleSlotBlockSize bunCap ≤ btSlotCandHeadBase tbl slotCap eCap ∨
    btSlotCandHeadBase tbl slotCap eCap + slotCap ≤ p
  blk_disj_curB : p + bundleSlotBlockSize bunCap ≤ btCurBunBase tbl slotCap eCap ∨
    btCurBunBase tbl slotCap eCap + slotCap ≤ p
  blk_disj_curT : p + bundleSlotBlockSize bunCap ≤ btCurTagBase tbl slotCap eCap ∨
    btCurTagBase tbl slotCap eCap + slotCap ≤ p
  blk_disj_eb : p + bundleSlotBlockSize bunCap ≤ btEndBundleBase tbl slotCap eCap ∨
    btEndBundleBase tbl slotCap eCap + 2 * eCap ≤ p
  blk_disj_prev : p + bundleSlotBlockSize bunCap ≤ btEndPrevBase tbl slotCap eCap ∨
    btEndPrevBase tbl slotCap eCap + 2 * eCap ≤ p
  blk_disj_next : p + bundleSlotBlockSize bunCap ≤ btEndNextBase tbl slotCap eCap ∨
    btEndNextBase tbl slotCap eCap + 2 * eCap ≤ p
  blk_disj_tch : btSlotTouchedBase tbl slotCap eCap + s < p ∨
    p + bundleSlotBlockSize bunCap ≤ btSlotTouchedBase tbl slotCap eCap + s
  blk_disj_delH : btSlotDelHeadBase tbl slotCap eCap + s < p ∨
    p + bundleSlotBlockSize bunCap ≤ btSlotDelHeadBase tbl slotCap eCap + s
  blk_disj_delN : ∀ e < eCap, btSlotDelNextBase tbl slotCap eCap + e < p ∨
    p + bundleSlotBlockSize bunCap ≤ btSlotDelNextBase tbl slotCap eCap + e

lemma emitSlotLayout_mk {w slotCap eCap tbl p bunCap s h₀ : ℕ}
    (hs_lt : s < slotCap)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (htbl_h : tbl + bundleTableFixedSize slotCap eCap ≤ h₀)
    (hp_disj_tbl : p + bundleSlotBlockSize bunCap ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ p) :
    EmitSlotLayout w slotCap eCap tbl p bunCap s h₀ := by
  unfold bundleTableFixedSize at htbl_w htbl_h hp_disj_tbl
  refine ⟨by omega,
    by unfold btSlotDelHeadBase; omega, by unfold btSlotDelNextBase; omega,
    by unfold btSlotCandHeadBase; omega, by unfold btCurBunBase; omega, by unfold btCurTagBase; omega,
    by unfold btEndBundleBase; omega, by unfold btEndPrevBase; omega, by unfold btEndNextBase; omega,
    by unfold btSlotTouchedBase; omega,
    by unfold btSlotDelHeadBase btSlotDelNextBase; omega,
    by unfold btSlotDelHeadBase; omega, by unfold btSlotDelNextBase; omega,
    by unfold btSlotCandHeadBase; omega, by unfold btCurBunBase; omega, by unfold btCurTagBase; omega,
    by unfold btEndBundleBase; omega, by unfold btEndPrevBase; omega, by unfold btEndNextBase; omega,
    by unfold btSlotTouchedBase; omega,
    by unfold btEndBundleBase btEndPrevBase; omega,
    by unfold btEndPrevBase btEndNextBase; omega,
    by unfold btEndNextBase btSlotTouchedBase; omega,
    by unfold btSlotTouchedBase btSlotDelHeadBase; omega,
    by unfold btSlotDelNextBase btSlotCandHeadBase; omega,
    by unfold btSlotCandHeadBase btCurBunBase; omega,
    by unfold btCurBunBase btCurTagBase; omega,
    by unfold btSlotCandHeadBase; omega, by unfold btCurBunBase; omega, by unfold btCurTagBase; omega,
    by unfold btEndBundleBase; omega, by unfold btEndPrevBase; omega, by unfold btEndNextBase; omega,
    by unfold btSlotTouchedBase; omega, by unfold btSlotDelHeadBase; omega,
    fun e he => by unfold btSlotDelNextBase; omega⟩

set_option maxHeartbeats 400000 in
lemma bundleStepEmitSlot_prep_runs {TS : BundleTourSpec}
    {w slotCap vCap eCap tbl tourH s outDescPtr hStart hScanEnd h₀ pos : ℕ}
    {pProg : Program} {bMergeSort bTourList bTourLen bTourOwner : ℕ} {ω : ℕ → Bool}
    (htour : BundleTourAt TS w vCap eCap pProg bTourList bTourLen bTourOwner)
    {S₀ S_cur : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {candSet : Fin slotCap → Finset ℕ} {remTouched : List ℕ}
    {B₀ : BundleState} {p bunCap : ℕ}
    {cord' : ℕ → List End} {src' : End → ℕ} {scan_j : List (ℕ × ℕ × ℕ)}
    {tx₀ : htour.rep.τ} {mem₀ : ℕ → ℕ}
    (hMergeSort : ∀ L : List ℕ, MeetsContract w pProg bMergeSort (mergeSortContract w L))
    (hw16 : 16 ≤ 2 ^ w) (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hp_w : p + bundleSlotBlockSize bunCap < 2 ^ w)
    (hs_mem : s ∈ remTouched) (hs_lt : s < slotCap)
    (hS₀s : S₀ ⟨s, hs_lt⟩ = some B₀)
    (hblks : m.slotBlocks ⟨s, hs_lt⟩ = some (p, bunCap))
    (hhStart_pos : 1 ≤ hStart) (hhStart_le : hStart ≤ hScanEnd) (hhScan_le : hScanEnd ≤ h₀)
    (htbl_le_hStart : tbl + bundleTableFixedSize slotCap eCap ≤ hStart)
    (hp_disj_scan : p + bundleSlotBlockSize bunCap ≤ hStart ∨ hScanEnd ≤ p)
    (hfoot_lt : ∀ a, bundleTableFoot eCap tbl m a → a < h₀)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h₀)
    (htfoot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a → ¬ bundleTableFoot eCap tbl m a)
    (hzero : ZeroFrom mem₀ h₀)
    (htrep : htour.rep.rep tourH cord' tx₀ mem₀)
    (hemit : BundleTableEmitState slotCap vCap eCap tbl S₀ D m candSet S_cur remTouched mem₀)
    (hsrc_lt : ∀ x ∈ edgeEnds (B₀.edges \ D), src' x < vCap)
    (hval : ScanValidForSlot { B₀ with edges := B₀.edges \ D } src' (candSet ⟨s, hs_lt⟩) scan_j)
    (hscan : ScanNodesAt eCap mem₀ hStart hScanEnd (mem₀ (btCurBunBase tbl slotCap eCap + s)) scan_j)
    (htag : mem₀ (btCurTagBase tbl slotCap eCap + s) = scan_j.length)
    (hh_sp' : h₀ + (2 + 4 * ((B₀.edges ∩ D).sort (· ≤ ·)).length +
        3 * ((candSet ⟨s, hs_lt⟩).sort (· ≤ ·)).length +
        (17 + 2 * TS.querySpace) * scan_j.length) < 2 ^ w) :
    let dels := (B₀.edges ∩ D).sort (· ≤ ·)
    let cands := (candSet ⟨s, hs_lt⟩).sort (· ≤ ·)
    let B_del : BundleState := { B₀ with edges := B₀.edges \ D }
    let hB := h₀ + 2 * dels.length + 2 * cands.length
    let offPtr := hB + 2 * scan_j.length
    let bufPtr := offPtr + cands.length + 1
    let hCSR := bufPtr + scan_j.length
    let hC := hCSR + 1 + 2 * dels.length + 6 * scan_j.length
    ∃ stC cPrep,
      (∀ {sTail o stF cTail},
        Runs w pProg ω sTail stC o stF cTail →
        Runs w pProg ω
          (.assign 5 (.load (.bin .add (.reg 0) (.const 2))) ;;
           .assign 6 (.bin .mul (.const 2) (.reg 5)) ;;
           .assign 7 (.load (.bin .add (.load (.bin .add (.reg 0) (.const 3))) (.reg 2))) ;;
           .assign 8 (.load (.reg 7)) ;;
           .assign 9 (.load (.bin .add (.reg 0) (.const 5))) ;;
           .assign 10 (.load (.bin .add (.reg 0) (.const 6))) ;;
           .assign 11 (.load (.bin .add (.reg 0) (.const 7))) ;;
           .assign 12 (.load (.bin .add (.reg 0) (.const 8))) ;;
           .assign 13 (.load (.bin .add (.reg 0) (.const 9))) ;;
           .assign 14 (.load (.bin .add (.reg 0) (.const 10))) ;;
           .assign 15 (.load (.bin .add (.reg 0) (.const 11))) ;;
           bundleStepEmitPopDelsStmt bMergeSort ;;
           bundleStepEmitPopCandsStmt bMergeSort ;;
           bundleStepEmitBuildCSRStmt ;;
           bundleStepEmitDelRecsStmt ;; sTail)
          (startState [tbl, tourH, s, outDescPtr, h₀] mem₀ pos) o stF (cPrep + cTail)) ∧
      stC.regs 1 = tourH ∧ stC.regs 2 = s ∧ stC.regs 3 = outDescPtr ∧ stC.regs 4 = hC ∧
      stC.regs 6 = 2 * eCap ∧ stC.regs 7 = p ∧ stC.regs 8 = bunCap ∧
      stC.regs 9 = btEndBundleBase tbl slotCap eCap ∧ stC.regs 10 = btEndPrevBase tbl slotCap eCap ∧
      stC.regs 11 = btEndNextBase tbl slotCap eCap ∧ stC.regs 12 = btSlotTouchedBase tbl slotCap eCap ∧
      stC.regs 13 = offPtr ∧ stC.regs 14 = bufPtr ∧
      stC.regs 18 = h₀ + 2 * dels.length ∧ stC.regs 19 = cands.length ∧
      stC.regs 20 = hCSR ∧ stC.regs 21 = 1 + 2 * dels.length ∧ stC.regs 22 = dels.length ∧
      stC.mem (btSlotDelHeadBase tbl slotCap eCap + s) = 0 ∧
      (∀ e ∈ B₀.edges ∩ D, stC.mem (btSlotDelNextBase tbl slotCap eCap + e) = 0) ∧
      stC.mem (btSlotCandHeadBase tbl slotCap eCap + s) = 0 ∧
      stC.mem (btCurBunBase tbl slotCap eCap + s) = 0 ∧
      stC.mem (btCurTagBase tbl slotCap eCap + s) = 0 ∧
      BatchBodyAt stC.mem (hCSR + 1) B₀.graph (dels.map Update.delete) (2 * dels.length) ∧
      B₀.graph.applyBatch (dels.map Update.delete) = B_del.graph ∧
      ZeroFrom stC.mem hC ∧
      htour.rep.rep tourH cord' tx₀ stC.mem ∧
      htour.rep.phi tourH tx₀ stC.mem = htour.rep.phi tourH tx₀ mem₀ ∧
      BundleSlotRepAt eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
        p bunCap B_del stC.mem ∧
      (∀ x ∈ edgeEnds B_del.edges,
        stC.mem (btEndBundleBase tbl slotCap eCap + endKey x) = B_del.bundleOf x) ∧
      ListAt stC.mem (h₀ + 2 * dels.length) cands ∧
      CSRAt eCap stC.mem offPtr bufPtr cands scan_j ∧
      (∀ a < h₀, a ≠ btSlotDelHeadBase tbl slotCap eCap + s →
        (∀ e ∈ B₀.edges ∩ D, a ≠ btSlotDelNextBase tbl slotCap eCap + e) →
        a ≠ btSlotCandHeadBase tbl slotCap eCap + s →
        a ≠ btCurBunBase tbl slotCap eCap + s →
        a ≠ btCurTagBase tbl slotCap eCap + s →
        (a < bsInCandBase p bunCap ∨ p + bundleSlotBlockSize bunCap ≤ a) →
        stC.mem a = mem₀ a) ∧
      cPrep ≤ 300 * dels.length * (Nat.log 2 (dels.length + 1) + 1) +
        300 * cands.length * (Nat.log 2 (cands.length + 1) + 1) +
        80 * scan_j.length + 50 * cands.length + 430 := by
  intro dels cands B_del hB offPtr bufPtr hCSR hC
  change h₀ + (2 + 4 * dels.length + 3 * cands.length + (17 + 2 * TS.querySpace) * scan_j.length) < 2 ^ w at hh_sp'
  set js : Fin slotCap := ⟨s, hs_lt⟩
  have hemit_copy := hemit
  rcases hemit with ⟨hmem_sc0, _, _, _, _, _, _, _, _, _, _, _,
    _, _, hS_rel, _, hendB, hslots, _, _, _, _, hdel, _⟩
  have hS_js : S_cur js = some B_del := by
    have hr := hS_rel js; rw [hS₀s] at hr
    cases hSc : S_cur js with
    | none => rw [hSc] at hr; exact False.elim hr
    | some Bc => rw [hSc] at hr; congr 1; exact hr.2 hs_mem
  have hslot_js := hslots js; rw [hS_js, hblks] at hslot_js; simp only [js, hs_mem, ↓reduceIte] at hslot_js
  obtain ⟨hp_mem, hp_disj_tbl, hrepCand_js⟩ := hslot_js
  have hrepCand_js_copy := hrepCand_js
  obtain ⟨nB₀, hV₀, hnB₀_le, hE₀_lt, _, _, hcap_mem, _, _, _, _, _, _, _, hcand_lt0, _, _⟩ := hrepCand_js
  have hdel_js := hdel js; rw [hS₀s] at hdel_js; simp only [js, hs_mem, ↓reduceIte] at hdel_js
  obtain ⟨dL, hdL_sll, hdL_mem⟩ := hdel_js
  have hdels_len : dels.length = (B₀.edges ∩ D).card := Finset.length_sort _
  have hcands_len : cands.length = (candSet js).card := Finset.length_sort _
  have hdL_len : dL.length = (B₀.edges ∩ D).card := by
    have hset : dL.toFinset = B₀.edges ∩ D := by ext e; simp [hdL_mem]
    rw [← hset, List.toFinset_card_of_nodup hdL_sll.nodup]
  have hdels_eq_D : B₀.edges \ dels.toFinset = B₀.edges \ D := by ext e; simp [dels]
  have htbl_h : tbl + bundleTableFixedSize slotCap eCap ≤ h₀ := le_trans htbl_le_hStart (le_trans hhStart_le hhScan_le)
  have hp_h : p + bundleSlotBlockSize bunCap ≤ h₀ := by
    have := hfoot_lt (p + bundleSlotBlockSize bunCap - 1)
      (Or.inr ⟨js, p, bunCap, hblks, by unfold bundleSlotBlockSize; omega, by unfold bundleSlotBlockSize; omega⟩)
    unfold bundleSlotBlockSize at this ⊢; omega
  have hL := emitSlotLayout_mk hs_lt htbl_w htbl_h hp_disj_tbl
  have h9_le : 9 * scan_j.length ≤ (17 + 2 * TS.querySpace) * scan_j.length := Nat.mul_le_mul_right _ (by omega)
  -- Step 0: Header assigns
  obtain ⟨stH, hrunH, hmemH, _, hr0H, hr1H, hr2H, hr3H, hr4H, _, hr6H, hr7H, hr8H, hr9H,
    hr10H, hr11H, hr12H, hr13H, hr14H, hr15H⟩ :=
    bundleStepEmitSlot_hdr_runs (pProg := pProg) (ω := ω) (tourH := tourH) (outDescPtr := outDescPtr)
      (h₀ := h₀) (pos := pos) hw16 htbl_w hs_lt hp_mem hcap_mem hemit_copy
  -- Step 3A: PopDels
  obtain ⟨stA, cA, hrunA, hregsA, hr4A, hr16A, hr17A, _, hdelH0, hdL0, hdelLat, hzfA, hfrA, hcA⟩ :=
    bundleStepEmitPopDels_runs (ω := ω) (st₀ := stH) (eCap := eCap) (s := s)
      (delHeadBase := btSlotDelHeadBase tbl slotCap eCap)
      (delNextBase := btSlotDelNextBase tbl slotCap eCap) (hCur := h₀) (dL := dL)
      (delSet := B₀.edges ∩ D) hMergeSort hw16 (by have := hL.e2_w; clear * - this; omega)
      (by have := hL.delH_w; clear * - hs_lt this; omega) hL.delN_w
      (by clear * - hdL_len hdels_len hh_sp'; omega)
      (Or.inl (by have := hL.delH_le_delN; clear * - hs_lt this; omega))
      (Or.inl (by have := hL.delH_le_h; clear * - hs_lt this; omega))
      (Or.inl hL.delN_le_h)
      (hmemH.symm ▸ hdL_sll) hdL_mem (hmemH.symm ▸ hzero) hr2H hr4H hr13H hr14H
  rw [hdL_len, ← hdels_len] at hr4A hr17A hzfA hfrA hcA
  -- Step 3B: PopCands
  have hrepCand_A : BundleSlotRepCand eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
      p bunCap B_del (btSlotCandHeadBase tbl slotCap eCap + s) (candSet js) stA.mem := by
    have hag : ∀ a, (p ≤ a ∧ a < p + bundleSlotBlockSize bunCap) ∨
        (btEndPrevBase tbl slotCap eCap ≤ a ∧ a < btEndPrevBase tbl slotCap eCap + 2 * eCap) ∨
        (btEndNextBase tbl slotCap eCap ≤ a ∧ a < btEndNextBase tbl slotCap eCap + 2 * eCap) ∨
        a = btSlotCandHeadBase tbl slotCap eCap + s → stA.mem a = mem₀ a := fun a ha => by
      rw [← hmemH]
      refine hfrA a ?_ (fun e he => ?_) (Or.inl ?_)
      · rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | rfl
        · have := hL.blk_disj_delH; clear * - h1 h2 this; omega
        · have h1' := hL.prev_le_next; have h2' := hL.next_le_tch; have h3' := hL.tch_le_delH; clear * - h1 h2 h1' h2' h3'; omega
        · have h2' := hL.next_le_tch; have h3' := hL.tch_le_delH; clear * - h1 h2 h2' h3'; omega
        · have h1' := hL.delH_le_delN; have h2' := hL.delN_le_candH; clear * - hs_lt h1' h2'; omega
      · have he_lt := hdL_sll.mem_lt e he
        rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | rfl
        · have := hL.blk_disj_delN e he_lt; clear * - h1 h2 this; omega
        · have h1' := hL.prev_le_next; have h2' := hL.next_le_tch; have h3' := hL.tch_le_delH; have h4' := hL.delH_le_delN
          clear * - h1 h2 h1' h2' h3' h4'; omega
        · have h2' := hL.next_le_tch; have h3' := hL.tch_le_delH; have h4' := hL.delH_le_delN
          clear * - h1 h2 h2' h3' h4'; omega
        · have h4' := hL.delN_le_candH; clear * - he_lt h4'; omega
      · rcases ha with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | rfl
        · clear * - h2 hp_h; omega
        · have := hL.prev_le_h; clear * - h2 this; omega
        · have := hL.next_le_h; clear * - h2 this; omega
        · have := hL.candH_le_h; clear * - hs_lt this; omega
    exact BundleSlotRepCand.of_agree_ends hrepCand_js_copy
      (fun off hoff => hag _ (Or.inl ⟨Nat.le_add_right _ _, by omega⟩))
      (hag _ (Or.inr (Or.inr (Or.inr rfl))))
      (fun k hk _ => ⟨hag _ (Or.inr (Or.inl ⟨Nat.le_add_right _ _, by omega⟩)),
        hag _ (Or.inr (Or.inr (Or.inl ⟨Nat.le_add_right _ _, by omega⟩)))⟩)
  obtain ⟨stB, cB, hrunB, hregsB, hr4B, hr18B, hr19B, hcandH0, hrepB, hcandLat, hzfB, hfrB, hcB⟩ :=
    bundleStepEmitPopCands_runs (ω := ω) (st₀ := stA) (s := s) (p := p) (bunCap := bunCap)
      (prevBase := btEndPrevBase tbl slotCap eCap) (nextBase := btEndNextBase tbl slotCap eCap)
      (candHeadBase := btSlotCandHeadBase tbl slotCap eCap) (hCur := h₀ + 2 * dels.length)
      (candSet := candSet js) hMergeSort hw16 hp_w
      (by have := hL.candH_w; clear * - hs_lt this; omega) (by clear * - hcands_len hh_sp'; omega)
      (by have := hL.blk_disj_candH; clear * - hs_lt this; omega)
      (Or.inl (by have := hL.candH_le_h; clear * - hs_lt this; omega))
      (Or.inl (le_trans hp_h (Nat.le_add_right _ _)))
      hL.blk_disj_prev hL.blk_disj_next
      (Or.inr (by have h1 := hL.prev_le_next; have h2 := hL.next_le_tch; have h3 := hL.tch_le_delH; have h4 := hL.delH_le_delN; have h5 := hL.delN_le_candH; clear * - h1 h2 h3 h4 h5; omega))
      (Or.inr (by have h2 := hL.next_le_tch; have h3 := hL.tch_le_delH; have h4 := hL.delH_le_delN; have h5 := hL.delN_le_candH; clear * - h2 h3 h4 h5; omega))
      (Or.inr (le_trans hL.prev_le_h (Nat.le_add_right _ _)))
      (Or.inr (le_trans hL.next_le_h (Nat.le_add_right _ _)))
      hrepCand_A hzfA ((hregsA 2 (by decide) (by decide)).trans hr2H) hr4A
      ((hregsA 7 (by decide) (by decide)).trans hr7H) ((hregsA 8 (by decide) (by decide)).trans hr8H)
      ((hregsA 15 (by decide) (by decide)).trans hr15H)
  rw [← hcands_len] at hr4B hr19B hzfB hfrB hcB
  -- Step 3B': BuildCSR
  have hseen0_B : ∀ b < bunCap, stB.mem (bsSeenBase p bunCap + b) = 0 := fun b hb =>
    (hrepB.choose_spec.2.2.2.2.2.2.2.2.2.2.2 b hb).1
  have hfr_toB : ∀ a < h₀, a ≠ btSlotDelHeadBase tbl slotCap eCap + s →
      (∀ e ∈ B₀.edges ∩ D, a ≠ btSlotDelNextBase tbl slotCap eCap + e) →
      a ≠ btSlotCandHeadBase tbl slotCap eCap + s →
      (a < bsInCandBase p bunCap ∨ p + bundleSlotBlockSize bunCap ≤ a) →
      stB.mem a = mem₀ a := fun a h5 h1 h2 h3 h4 => by
    rw [hfrB a h3 h4 (Or.inl (by omega)), hfrA a h1 (fun e he => h2 e ((hdL_mem e).mp he)) (Or.inl h5), hmemH]
  have hcurB_eq_B : stB.mem (btCurBunBase tbl slotCap eCap + s) = mem₀ (btCurBunBase tbl slotCap eCap + s) :=
    hfr_toB _ (by have := hL.curB_le_h; clear * - hs_lt this; omega)
      (by have h1 := hL.delH_le_delN; have h2 := hL.delN_le_candH; have h3 := hL.candH_le_curB; clear * - hs_lt h1 h2 h3; omega)
      (fun e he => by have he_lt := hdL_sll.mem_lt e ((hdL_mem e).mpr he); have h2 := hL.delN_le_candH; have h3 := hL.candH_le_curB; clear * - he_lt h2 h3; omega)
      (by have h3 := hL.candH_le_curB; clear * - hs_lt h3; omega)
      (by have := hL.blk_disj_curB; unfold bsInCandBase; clear * - hs_lt this; omega)
  have hcurT_eq_B : stB.mem (btCurTagBase tbl slotCap eCap + s) = mem₀ (btCurTagBase tbl slotCap eCap + s) :=
    hfr_toB _ (by have := hL.curT_le_h; clear * - hs_lt this; omega)
      (by have h1 := hL.delH_le_delN; have h2 := hL.delN_le_candH; have h3 := hL.candH_le_curB; have h4 := hL.curB_le_curT; clear * - hs_lt h1 h2 h3 h4; omega)
      (fun e he => by have he_lt := hdL_sll.mem_lt e ((hdL_mem e).mpr he); have h2 := hL.delN_le_candH; have h3 := hL.candH_le_curB; have h4 := hL.curB_le_curT; clear * - he_lt h2 h3 h4; omega)
      (by have h3 := hL.candH_le_curB; have h4 := hL.curB_le_curT; clear * - hs_lt h3 h4; omega)
      (by have := hL.blk_disj_curT; unfold bsInCandBase; clear * - hs_lt this; omega)
  have hscan_B : ScanNodesAt eCap stB.mem hStart hScanEnd (stB.mem (btCurBunBase tbl slotCap eCap + s)) scan_j := by
    rw [hcurB_eq_B]
    refine scanNodesAt_mono hscan (le_refl _) fun a ha1 ha2 => ?_
    refine hfr_toB a (by omega)
      (by unfold bundleTableFixedSize at htbl_le_hStart; unfold btSlotDelHeadBase; omega)
      (fun e he => by have he_lt := hdL_sll.mem_lt e ((hdL_mem e).mpr he); unfold bundleTableFixedSize at htbl_le_hStart; unfold btSlotDelNextBase; omega)
      (by unfold bundleTableFixedSize at htbl_le_hStart; unfold btSlotCandHeadBase; omega)
      (by unfold bsInCandBase; clear * - hp_disj_scan ha1 ha2; omega)
  have hmem_sc_B : stB.mem tbl = slotCap := by
    rw [hfr_toB tbl (by unfold bundleTableFixedSize at htbl_h; omega)
      (by unfold btSlotDelHeadBase; omega) (fun _ _ => by unfold btSlotDelNextBase; omega)
      (by unfold btSlotCandHeadBase; omega)
      (by unfold bundleTableFixedSize at hp_disj_tbl; unfold bsInCandBase; omega)]
    exact hmem_sc0
  obtain ⟨stCSR, cCSR, hrunCSR, hregsCSR, hr4CSR, hr13CSR, hr14CSR, hr23CSR, hcurB0, hcurT0,
    hcsr, hzfCSR, hfrCSR, hcCSR⟩ :=
    bundleStepEmitBuildCSR_runs (ω := ω) (st₀ := stB) (slotCap := slotCap) (eCap := eCap)
      (tbl := tbl) (s := s) (p := p) (bunCap := bunCap) (candArr := h₀ + 2 * dels.length)
      (hStart := hStart) (h₀ := hScanEnd) (hCur := hB) (cands := cands) (scan_j := scan_j)
      hw16 hs_lt htbl_w hp_w (by clear * - hh_sp'; omega)
      (by clear * - hh_sp' h9_le; omega)
      hhStart_pos hhStart_le (by clear * - hhScan_le; omega)
      (by unfold bundleTableFixedSize at htbl_le_hStart; unfold btCurTagBase; omega)
      (by clear * - hp_h; omega) hp_disj_scan hp_disj_tbl
      (by clear * -; omega) (Or.inr (by clear * - hp_h; omega))
      (Or.inr (by have := hL.curT_le_h; clear * - this; omega))
      (Finset.sort_nodup _ _)
      (fun b hb => lt_of_lt_of_le (hcand_lt0 b ((Finset.mem_sort (· ≤ ·)).mp hb)) hnB₀_le)
      (fun t ht => (Finset.mem_sort (· ≤ ·)).mpr (hval.2.1 t ht).1)
      (fun t ht => by
        have ht_end := (hval.2.1 t ht).2.1
        have ht_src := (hval.2.1 t ht).2.2
        have hlt_v : t.2.1 < vCap := ht_src ▸ hsrc_lt _ ((mem_edgeEnds _ _).mpr ((BundleState.mem_ends _ _ _).mp ht_end).1)
        have hlt_k : t.2.2 < 2 * eCap := by
          have := hE₀_lt (endOfKey t.2.2).1 ((BundleState.mem_ends _ _ _).mp ht_end).1
          have hkeq := bundle_endKey_endOfKey t.2.2
          rcases hxk : endOfKey t.2.2 with ⟨ee, side⟩
          rw [hxk] at this hkeq; cases side <;> simp [endKey] at hkeq <;> omega
        have hmul := Nat.mul_le_mul_right (2 * eCap) (show t.2.1 + 1 ≤ vCap by omega)
        unfold packEndKey; rw [Nat.add_mul, Nat.one_mul] at hmul; omega)
      hmem_sc_B hseen0_B hscan_B (hcurT_eq_B.trans htag) hcandLat hzfB
      ((hregsB 0 (by decide) (by decide)).trans ((hregsA 0 (by decide) (by decide)).trans hr0H))
      ((hregsB 2 (by decide) (by decide)).trans ((hregsA 2 (by decide) (by decide)).trans hr2H))
      hr4B
      ((hregsB 7 (by decide) (by decide)).trans ((hregsA 7 (by decide) (by decide)).trans hr7H))
      ((hregsB 8 (by decide) (by decide)).trans ((hregsA 8 (by decide) (by decide)).trans hr8H))
      ((hregsB 15 (by decide) (by decide)).trans ((hregsA 15 (by decide) (by decide)).trans hr15H))
      hr18B hr19B
  -- Step 3C: DelRecs (reads `r23 = scan_j.length`)
  have hdelLat_CSR : ListAt stCSR.mem h₀ dels := fun i hi => by
    rw [hfrCSR (h₀ + i) (by have := hL.curB_le_h; clear * - hs_lt this; omega)
      (by have := hL.curT_le_h; clear * - hs_lt this; omega) (Or.inl (by clear * - hi; omega)),
      hfrB (h₀ + i) (by have := hL.candH_le_h; clear * - hs_lt this; omega)
        (Or.inr (by clear * - hp_h; omega)) (Or.inl (by clear * - hi; omega))]
    exact hdelLat i hi
  obtain ⟨stC, cC, hrunC, hregsC, hr4C, hr20C, hr21C, hr22C, hbatC, hGC, hzfC, hfrC, hcC⟩ :=
    bundleStepEmitDelRecs_runs (ω := ω) (B₀ := B₀) (dels := dels) (st₀ := stCSR)
      (delArr := h₀) (hCur := hCSR) (scannedEnds := scan_j.length)
      hw16 (by clear * - hh_sp'; omega) hdelLat_CSR hzfCSR
      (by clear * - hh_sp' h9_le; omega)
      (Or.inl (by clear * -; omega))
      hr4CSR
      ((hregsCSR 16 (by decide) (by decide) (by decide) (by decide)).trans ((hregsB 16 (by decide) (by decide)).trans hr16A))
      ((hregsCSR 17 (by decide) (by decide) (by decide) (by decide)).trans ((hregsB 17 (by decide) (by decide)).trans hr17A))
      hr23CSR
  rw [hdels_eq_D] at hGC
  have hfr_toC : ∀ a < h₀, a ≠ btSlotDelHeadBase tbl slotCap eCap + s →
      (∀ e ∈ B₀.edges ∩ D, a ≠ btSlotDelNextBase tbl slotCap eCap + e) →
      a ≠ btSlotCandHeadBase tbl slotCap eCap + s →
      a ≠ btCurBunBase tbl slotCap eCap + s →
      a ≠ btCurTagBase tbl slotCap eCap + s →
      (a < bsInCandBase p bunCap ∨ p + bundleSlotBlockSize bunCap ≤ a) →
      stC.mem a = mem₀ a := fun a h5 h1 h2 h3 hcb hct h4 => by
    rw [hfrC a (Or.inl (by clear * - h5; omega)),
      hfrCSR a hcb hct (Or.inl (by clear * - h5; omega)),
      hfr_toB a h5 h1 h2 h3 h4]
  have htour_loc := htour.rep_local tourH cord' tx₀ mem₀ stC.mem fun a ha => (hfr_toC a
    (htfoot_lt a ha)
    (fun heq => htfoot_disj_tbl a ha (heq ▸ btSlotDelHead_in_foot hs_lt))
    (fun e he heq => htfoot_disj_tbl a ha (heq ▸ btSlotDelNext_in_foot (hdL_sll.mem_lt e ((hdL_mem e).mpr he))))
    (fun heq => htfoot_disj_tbl a ha (heq ▸ btSlotCandHead_in_foot hs_lt))
    (fun heq => htfoot_disj_tbl a ha (heq ▸ btCurBun_in_foot hs_lt))
    (fun heq => htfoot_disj_tbl a ha (heq ▸ btCurTag_in_foot hs_lt))
    (by by_contra hnot; push Not at hnot
        exact htfoot_disj_tbl a ha (Or.inr ⟨js, p, bunCap, hblks, by unfold bsInCandBase at hnot; omega, hnot.2⟩))).symm
  refine ⟨stC, 66 + (cA + (cB + (cCSR + (cC + 1) + 1) + 1) + 1), fun {sTail o stF cTail} hTail => ?_,
    (hregsC 1 (by decide) (by decide)).trans ((hregsCSR 1 (by decide) (by decide) (by decide) (by decide)).trans ((hregsB 1 (by decide) (by decide)).trans ((hregsA 1 (by decide) (by decide)).trans hr1H))),
    (hregsC 2 (by decide) (by decide)).trans ((hregsCSR 2 (by decide) (by decide) (by decide) (by decide)).trans ((hregsB 2 (by decide) (by decide)).trans ((hregsA 2 (by decide) (by decide)).trans hr2H))),
    (hregsC 3 (by decide) (by decide)).trans ((hregsCSR 3 (by decide) (by decide) (by decide) (by decide)).trans ((hregsB 3 (by decide) (by decide)).trans ((hregsA 3 (by decide) (by decide)).trans hr3H))),
    hr4C,
    (hregsC 6 (by decide) (by decide)).trans ((hregsCSR 6 (by decide) (by decide) (by decide) (by decide)).trans ((hregsB 6 (by decide) (by decide)).trans ((hregsA 6 (by decide) (by decide)).trans hr6H))),
    (hregsC 7 (by decide) (by decide)).trans ((hregsCSR 7 (by decide) (by decide) (by decide) (by decide)).trans ((hregsB 7 (by decide) (by decide)).trans ((hregsA 7 (by decide) (by decide)).trans hr7H))),
    (hregsC 8 (by decide) (by decide)).trans ((hregsCSR 8 (by decide) (by decide) (by decide) (by decide)).trans ((hregsB 8 (by decide) (by decide)).trans ((hregsA 8 (by decide) (by decide)).trans hr8H))),
    (hregsC 9 (by decide) (by decide)).trans ((hregsCSR 9 (by decide) (by decide) (by decide) (by decide)).trans ((hregsB 9 (by decide) (by decide)).trans ((hregsA 9 (by decide) (by decide)).trans hr9H))),
    (hregsC 10 (by decide) (by decide)).trans ((hregsCSR 10 (by decide) (by decide) (by decide) (by decide)).trans ((hregsB 10 (by decide) (by decide)).trans ((hregsA 10 (by decide) (by decide)).trans hr10H))),
    (hregsC 11 (by decide) (by decide)).trans ((hregsCSR 11 (by decide) (by decide) (by decide) (by decide)).trans ((hregsB 11 (by decide) (by decide)).trans ((hregsA 11 (by decide) (by decide)).trans hr11H))),
    (hregsC 12 (by decide) (by decide)).trans ((hregsCSR 12 (by decide) (by decide) (by decide) (by decide)).trans ((hregsB 12 (by decide) (by decide)).trans ((hregsA 12 (by decide) (by decide)).trans hr12H))),
    (hregsC 13 (by decide) (by decide)).trans hr13CSR,
    (hregsC 14 (by decide) (by decide)).trans hr14CSR,
    (hregsC 18 (by decide) (by decide)).trans ((hregsCSR 18 (by decide) (by decide) (by decide) (by decide)).trans hr18B),
    (hregsC 19 (by decide) (by decide)).trans ((hregsCSR 19 (by decide) (by decide) (by decide) (by decide)).trans hr19B),
    hr20C, hr21C, hr22C,
    by rw [hfrC _ (Or.inl (by have := hL.delH_le_h; clear * - hs_lt this; omega)),
           hfrCSR _ (by have h1 := hL.delH_le_delN; have h2 := hL.delN_le_candH; have h3 := hL.candH_le_curB; clear * - hs_lt h1 h2 h3; omega)
             (by have h1 := hL.delH_le_delN; have h2 := hL.delN_le_candH; have h3 := hL.candH_le_curB; have h4 := hL.curB_le_curT; clear * - hs_lt h1 h2 h3 h4; omega)
             (Or.inl (by have := hL.delH_le_h; clear * - hs_lt this; omega)),
           hfrB _ (by have h1 := hL.delH_le_delN; have h2 := hL.delN_le_candH; clear * - hs_lt h1 h2; omega)
             (by have := hL.blk_disj_delH; unfold bsInCandBase; clear * - this; omega)
             (Or.inl (by have := hL.delH_le_h; clear * - hs_lt this; omega)), hdelH0],
    fun e he => by
      have hedL := (hdL_mem e).mpr he
      have he_lt := hdL_sll.mem_lt e hedL
      rw [hfrC _ (Or.inl (by have := hL.delN_le_h; clear * - he_lt this; omega)),
          hfrCSR _ (by have h2 := hL.delN_le_candH; have h3 := hL.candH_le_curB; clear * - he_lt h2 h3; omega)
            (by have h2 := hL.delN_le_candH; have h3 := hL.candH_le_curB; have h4 := hL.curB_le_curT; clear * - he_lt h2 h3 h4; omega)
            (Or.inl (by have := hL.delN_le_h; clear * - he_lt this; omega)),
          hfrB _ (by have := hL.delN_le_candH; clear * - he_lt this; omega)
            (by have := hL.blk_disj_delN e he_lt; unfold bsInCandBase; clear * - this; omega)
            (Or.inl (by have := hL.delN_le_h; clear * - he_lt this; omega)), hdL0 e hedL],
    by rw [hfrC _ (Or.inl (by have := hL.candH_le_h; clear * - hs_lt this; omega)),
           hfrCSR _ (by have := hL.candH_le_curB; clear * - hs_lt this; omega)
             (by have h3 := hL.candH_le_curB; have h4 := hL.curB_le_curT; clear * - hs_lt h3 h4; omega)
             (Or.inl (by have := hL.candH_le_h; clear * - hs_lt this; omega)), hcandH0],
    by rw [hfrC _ (Or.inl (by have := hL.curB_le_h; clear * - hs_lt this; omega)), hcurB0],
    by rw [hfrC _ (Or.inl (by have := hL.curT_le_h; clear * - hs_lt this; omega)), hcurT0],
    hbatC, hGC, hzfC, htour_loc.1 htrep, htour_loc.2.symm,
    hrepB.of_agree
      (fun a h1 h2 => by
        symm
        rw [hfrC a (Or.inl (by clear * - h2 hp_h; omega)),
          hfrCSR a (by have := hL.blk_disj_curB; clear * - h1 h2 hs_lt this; omega)
            (by have := hL.blk_disj_curT; clear * - h1 h2 hs_lt this; omega)
            (Or.inl (by clear * - h2 hp_h; omega))])
      (fun k hk => by
        symm
        rw [hfrC _ (Or.inl (by have := hL.prev_le_h; clear * - hk this; omega)),
          hfrCSR _ (by have h1 := hL.prev_le_next; have h2 := hL.next_le_tch; have h3 := hL.tch_le_delH; have h4 := hL.delH_le_delN; have h5 := hL.delN_le_candH; have h6 := hL.candH_le_curB; clear * - hk h1 h2 h3 h4 h5 h6; omega)
            (by have h1 := hL.prev_le_next; have h2 := hL.next_le_tch; have h3 := hL.tch_le_delH; have h4 := hL.delH_le_delN; have h5 := hL.delN_le_candH; have h6 := hL.candH_le_curB; have h7 := hL.curB_le_curT; clear * - hk h1 h2 h3 h4 h5 h6 h7; omega)
            (Or.inl (by have := hL.prev_le_h; clear * - hk this; omega))])
      (fun k hk => by
        symm
        rw [hfrC _ (Or.inl (by have := hL.next_le_h; clear * - hk this; omega)),
          hfrCSR _ (by have h2 := hL.next_le_tch; have h3 := hL.tch_le_delH; have h4 := hL.delH_le_delN; have h5 := hL.delN_le_candH; have h6 := hL.candH_le_curB; clear * - hk h2 h3 h4 h5 h6; omega)
            (by have h2 := hL.next_le_tch; have h3 := hL.tch_le_delH; have h4 := hL.delH_le_delN; have h5 := hL.delN_le_candH; have h6 := hL.candH_le_curB; have h7 := hL.curB_le_curT; clear * - hk h2 h3 h4 h5 h6 h7; omega)
            (Or.inl (by have := hL.next_le_h; clear * - hk this; omega))]),
    fun x hx => by
      have hxk : endKey x < 2 * eCap := by
        have := hE₀_lt x.1 ((mem_edgeEnds _ _).mp hx)
        rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
      rw [hfr_toC _ (by have := hL.eb_le_h; clear * - hxk this; omega)
        (by have h1 := hL.eb_le_prev; have h2 := hL.prev_le_next; have h3 := hL.next_le_tch; have h4 := hL.tch_le_delH; clear * - hxk h1 h2 h3 h4; omega)
        (fun e _ => by have h1 := hL.eb_le_prev; have h2 := hL.prev_le_next; have h3 := hL.next_le_tch; have h4 := hL.tch_le_delH; have h5 := hL.delH_le_delN; clear * - hxk h1 h2 h3 h4 h5; omega)
        (by have h1 := hL.eb_le_prev; have h2 := hL.prev_le_next; have h3 := hL.next_le_tch; have h4 := hL.tch_le_delH; have h5 := hL.delH_le_delN; have h6 := hL.delN_le_candH; clear * - hxk h1 h2 h3 h4 h5 h6; omega)
        (by have h1 := hL.eb_le_prev; have h2 := hL.prev_le_next; have h3 := hL.next_le_tch; have h4 := hL.tch_le_delH; have h5 := hL.delH_le_delN; have h6 := hL.delN_le_candH; have h7 := hL.candH_le_curB; clear * - hxk h1 h2 h3 h4 h5 h6 h7; omega)
        (by have h1 := hL.eb_le_prev; have h2 := hL.prev_le_next; have h3 := hL.next_le_tch; have h4 := hL.tch_le_delH; have h5 := hL.delH_le_delN; have h6 := hL.delN_le_candH; have h7 := hL.candH_le_curB; have h8 := hL.curB_le_curT; clear * - hxk h1 h2 h3 h4 h5 h6 h7 h8; omega)
        (by have := hL.blk_disj_eb; unfold bsInCandBase; clear * - hxk this; omega)]
      exact hendB js B_del hS_js x hx,
    fun i hi => by
      rw [hfrC _ (Or.inl (by clear * - hi; omega)),
          hfrCSR _ (by have := hL.curB_le_h; clear * - hs_lt this; omega)
            (by have := hL.curT_le_h; clear * - hs_lt this; omega) (Or.inl (by clear * - hi; omega))]
      exact hcandLat i hi,
    ⟨fun i hi => by rw [hfrC _ (Or.inl (by clear * - hi; omega))]; exact hcsr.1 i hi,
     fun i hi => by
       obtain ⟨L', hperm', hlat'⟩ := hcsr.2 i hi
       refine ⟨L', hperm', fun t ht => ?_⟩
       have hlen' : L'.length = (scan_j.filter fun x => x.1 == cands[i]'hi).length := by
         rw [hperm'.length_eq, List.length_map]
       have hoff_eq := hcsr.1 i (by omega)
       have hsum_all := sum_filter_lengths_eq (Finset.sort_nodup _ _) (fun x hx => (Finset.mem_sort (· ≤ ·)).mpr (hval.2.1 x hx).1)
       have htake_le : ((cands.take (i + 1)).map fun b => (scan_j.filter fun x => x.1 == b).length).sum ≤ scan_j.length := by
         have h := congrArg (fun l => (l.map fun b => (scan_j.filter fun x => x.1 == b).length).sum) (List.take_append_drop (i + 1) cands)
         rw [List.map_append, List.sum_append, hsum_all] at h; omega
       have htake_s : ((cands.take (i + 1)).map fun b => (scan_j.filter fun x => x.1 == b).length).sum =
           ((cands.take i).map fun b => (scan_j.filter fun x => x.1 == b).length).sum + L'.length := by
         rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]; simp [hlen']
       have hmem_off : stC.mem (offPtr + i) = stCSR.mem (offPtr + i) :=
         hfrC _ (Or.inl (by clear * - hi; omega))
       have hlt_buf : bufPtr + stCSR.mem (offPtr + i) + t < hCSR := by
         rw [hoff_eq]; clear * - htake_le htake_s ht; omega
       rw [hmem_off, hfrC _ (Or.inl (lt_trans hlt_buf (Nat.lt_succ_self hCSR)))]
       exact hlat' t ht⟩,
    hfr_toC, ?_⟩
  · have hrun := hrunH (bundle_runs_seq_normal hrunA (bundle_runs_seq_normal hrunB
      (bundle_runs_seq_normal hrunCSR (bundle_runs_seq_normal hrunC hTail))))
    rw [show 66 + (cA + (cB + (cCSR + (cC + 1) + 1) + 1) + 1) + cTail =
        66 + (cA + (cB + (cCSR + (cC + cTail + 1) + 1) + 1) + 1) by clear * -; omega]
    exact hrun
  · have hlogD : 1 ≤ Nat.log 2 (dels.length + 1) + 1 := Nat.le_add_left _ _
    have hlogC : 1 ≤ Nat.log 2 (cands.length + 1) + 1 := Nat.le_add_left _ _
    have hdel_lin : 75 * dels.length ≤ 100 * dels.length * (Nat.log 2 (dels.length + 1) + 1) := by
      calc 75 * dels.length ≤ 100 * dels.length := by clear * -; omega
        _ = 100 * dels.length * 1 := (Nat.mul_one _).symm
        _ ≤ 100 * dels.length * (Nat.log 2 (dels.length + 1) + 1) := Nat.mul_le_mul_left _ hlogD
    have hcand_lin : 75 * cands.length ≤ 100 * cands.length * (Nat.log 2 (cands.length + 1) + 1) := by
      calc 75 * cands.length ≤ 100 * cands.length := by clear * -; omega
        _ = 100 * cands.length * 1 := (Nat.mul_one _).symm
        _ ≤ 100 * cands.length * (Nat.log 2 (cands.length + 1) + 1) := Nat.mul_le_mul_left _ hlogC
    have hmul300D : 300 * dels.length * (Nat.log 2 (dels.length + 1) + 1) =
        200 * dels.length * (Nat.log 2 (dels.length + 1) + 1) +
        100 * dels.length * (Nat.log 2 (dels.length + 1) + 1) := by ring
    have hmul300C : 300 * cands.length * (Nat.log 2 (cands.length + 1) + 1) =
        200 * cands.length * (Nat.log 2 (cands.length + 1) + 1) +
        100 * cands.length * (Nat.log 2 (cands.length + 1) + 1) := by ring
    clear * - hcA hcB hcCSR hcC hdel_lin hcand_lin hmul300D hmul300C; omega

end

end MinCostFlow.SparseCore.Program
