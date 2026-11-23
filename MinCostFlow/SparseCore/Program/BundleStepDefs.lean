module

public import MinCostFlow.SparseCore.Program.BundleStepEmitProofs
public import MinCostFlow.SparseCore.Program.BundleStepDelProof
public import MinCostFlow.SparseCore.BundleTreeCore

/-!
# Definitions and helper lemmas for `bundleStep` (`BundleStepDefs`)

Defines `bundleStepStmt bStepDel bStepScan bStepEmitSlot` (`args = [tbl, tourH, delCount, delPtr,
groupCount, groupPtr, outDescPtr, h]`), its space/cost specifications (`bundleStepSpace`,
`bundleStepCost`), post-step state/batch specifications (`tableAfterStep`, `slotBatchOf`), and
footprint-agreement and range-cost helper lemmas used in `BundleStepMain`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. `bundleStepStmt` and space / cost / state specifications -/

/-- `args = [tbl, tourH, delCount, delPtr, groupCount, groupPtr, outDescPtr, h]`:
runs Phase 1 (`bStepDel`), Phase 2 (`bStepScan`), and Phase 3 (`bStepEmitSlot` over every touched
slot), using the table-resident `touchedBuf[slotCap]` and `touchedCnt[1]` scratch arrays, writing
`[touchedCount, s_0, batchPtr_0, words_0, ...]` at `outDescPtr`, and returning `h'`. -/
def bundleStepStmt (bStepDel bStepScan bStepEmitSlot : ℕ) : Stmt :=
  .assign 8 (.load (.reg 0)) ;;                                                  -- slotCap
  .assign 9 (.bin .add (.load (.bin .add (.reg 0) (.const 11)))
    (.bin .mul (.const 3) (.reg 8))) ;;                                          -- btTouchedBufBase
  .assign 10 (.bin .add (.reg 9) (.reg 8)) ;;                                    -- btTouchedCntAddr
  .assign 11 (.reg 7) ;;                                                         -- h0
  .call 12 bStepDel [.reg 0, .reg 2, .reg 3, .reg 9] ;;
  .store (.reg 10) (.reg 12) ;;
  .call 11 bStepScan [.reg 0, .reg 1, .reg 4, .reg 5, .reg 10, .reg 9, .reg 11] ;;
  .assign 12 (.load (.reg 10)) ;;                                                -- totalTouched
  .store (.reg 6) (.reg 12) ;;
  forRange 13 (.const 0) (.reg 12)
    (.assign 14 (.load (.bin .add (.reg 9) (.reg 13))) ;;                        -- s := touched[i]
     .assign 15 (.bin .add (.bin .add (.reg 6) (.const 1)) (.bin .mul (.const 3) (.reg 13))) ;;
     .call 11 bStepEmitSlot [.reg 0, .reg 1, .reg 14, .reg 15, .reg 11]) ;;
  .ret (.reg 11)

lemma bundleStepStmt_noRand (bStepDel bStepScan bStepEmitSlot : ℕ) :
    (bundleStepStmt bStepDel bStepScan bStepEmitSlot).NoRand := by
  trivial

/-- Number of deleted edges in slot `j`. -/
noncomputable def slotDelCnt {slotCap : ℕ} (S₀ : BundleTableState slotCap) (D : Finset ℕ)
    (j : Fin slotCap) : ℕ :=
  match S₀ j with
  | none => 0
  | some B₀ => (B₀.edges ∩ D).card

/-- Number of candidate splitting bundles in slot `j`. -/
def slotCandCnt {slotCap : ℕ} (candSet : Fin slotCap → Finset ℕ) (j : Fin slotCap) : ℕ :=
  (candSet j).card

/-- Total surviving ends across all candidate splitting bundles of slot `j`. -/
noncomputable def slotCandEndsSum {slotCap : ℕ} (S₀ : BundleTableState slotCap) (D : Finset ℕ)
    (candSet : Fin slotCap → Finset ℕ) (j : Fin slotCap) : ℕ :=
  match S₀ j with
  | none => 0
  | some B₀ =>
      (((candSet j).sort (· ≤ ·)).map fun b =>
        (({ B₀ with edges := B₀.edges \ D } : BundleState).ends b).card).sum

/-- Number of scanned candidate-bundle ends recorded for slot `j` by Phase 2 Pass C. -/
noncomputable def slotScannedEnds {slotCap : ℕ} (S₀ : BundleTableState slotCap) (D : Finset ℕ)
    (cord' : ℕ → List End) (gs : List (List ℕ)) (maxIdxs : List ℕ) (j : Fin slotCap) : ℕ :=
  (addScanEndsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) (fun _ => [])
    gs.length j).length

/-- Total Phase 3 heap space across a list of touched slots, parameterized by per-slot scanned
end counts `scanLen : Fin slotCap → ℕ`. -/
noncomputable def bundleStepEmitTotalSpace (TS : BundleTourSpec) {slotCap : ℕ}
    (S₀ : BundleTableState slotCap) (D : Finset ℕ) (candSet : Fin slotCap → Finset ℕ)
    (scanLen : Fin slotCap → ℕ) (touched : List ℕ) : ℕ :=
  (touched.map fun s =>
    if hs : s < slotCap then
      bundleStepEmitSlotSpace TS (slotDelCnt S₀ D ⟨s, hs⟩) (slotCandCnt candSet ⟨s, hs⟩)
        (scanLen ⟨s, hs⟩)
    else 0).sum

/-- Total Phase 3 cost (excluding tour potential drop) across a list of touched slots,
parameterized by per-slot scanned end counts `scanLen : Fin slotCap → ℕ`. -/
noncomputable def bundleStepEmitTotalCost (TS : BundleTourSpec) (eCap : ℕ) {slotCap : ℕ}
    (S₀ : BundleTableState slotCap) (D : Finset ℕ) (candSet : Fin slotCap → Finset ℕ)
    (scanLen : Fin slotCap → ℕ) (touched : List ℕ) : ℕ :=
  (touched.map fun s =>
    if hs : s < slotCap then
      bundleStepEmitSlotCost TS eCap (slotDelCnt S₀ D ⟨s, hs⟩) (slotCandCnt candSet ⟨s, hs⟩)
        (scanLen ⟨s, hs⟩)
    else 0).sum

/-- Total heap space budget for `bundleStepStmt` (free of `slotCap` and `candEndsSum`). -/
noncomputable def bundleStepSpace (TS : BundleTourSpec) {slotCap : ℕ}
    (S₀ : BundleTableState slotCap) (D : Finset ℕ) (candSet : Fin slotCap → Finset ℕ)
    (scanLen : Fin slotCap → ℕ) (cord' : ℕ → List End) (gs : List (List ℕ))
    (touched : List ℕ) : ℕ :=
  bundleStepScanSpace TS cord' gs + bundleStepEmitTotalSpace TS S₀ D candSet scanLen touched

/-- Total cost bound for `bundleStepStmt` (excluding tour potential drop and `tourPot` drop).
All Phase 3 scanned-end, candidate-sorting, and per-touched-slot work is absorbed into `delCount`
and `bundleScanPotMul TS eCap * totalNonMaxLen`. -/
def bundleStepCost (TS : BundleTourSpec) (eCap delCount : ℕ) (gs : List (List ℕ)) : ℕ :=
  300 * delCount * (Nat.log 2 (delCount + 1) + 1) + 1070 * delCount +
    bundleStepScanCost TS eCap gs + 160

/-- Emitted update batch for slot `j` under deletions `D`, final roots `src'`, and candidate set
`candSet j`. -/
noncomputable def slotBatchOf {slotCap : ℕ} (S₀ : BundleTableState slotCap) (D : Finset ℕ)
    (src' : End → ℕ) (candSet : Fin slotCap → Finset ℕ) (j : Fin slotCap) : List Update :=
  match S₀ j with
  | none => []
  | some B₀ =>
      let dels := (B₀.edges ∩ D).sort (· ≤ ·)
      let cands := (candSet j).sort (· ≤ ·)
      (byRootSplitFold B₀ (B₀.edges \ D) src' (dels.map Update.delete) cands).1

/-- Updated table state after applying `byRootSplitFold` to every active slot. -/
noncomputable def tableAfterStep {slotCap : ℕ} (S₀ : BundleTableState slotCap) (D : Finset ℕ)
    (src' : End → ℕ) (candSet : Fin slotCap → Finset ℕ) : BundleTableState slotCap :=
  fun j =>
    match S₀ j with
    | none => none
    | some B₀ =>
        let dels := (B₀.edges ∩ D).sort (· ≤ ·)
        let cands := (candSet j).sort (· ≤ ·)
        some (byRootSplitFold B₀ (B₀.edges \ D) src' (dels.map Update.delete) cands).2

end

public section

/-! ## 2. Footprint agreement and list / cost helpers -/

lemma BundleTableAfterScan.of_agree_coreFoot {slotCap vCap eCap tbl : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {candSet : Fin slotCap → Finset ℕ} {touched : List ℕ} {mem mem' : ℕ → ℕ}
    (h : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m candSet touched mem)
    (hag : ∀ a, bundleTableCoreFoot eCap tbl m a → mem' a = mem a) :
    BundleTableAfterScan slotCap vCap eCap tbl S₀ D m candSet touched mem' := by
  rcases h with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8', r9', r10', r11',
    hd, hes, heb, hsl, hdb, hnd, hlt, htch, hdl, hdN0⟩
  refine ⟨(hag _ (btHeader_in_coreFoot (by decide))).trans r0, (hag _ (btHeader_in_coreFoot (by decide))).trans r1,
    (hag _ (btHeader_in_coreFoot (by decide))).trans r2, (hag _ (btHeader_in_coreFoot (by decide))).trans r3,
    (hag _ (btHeader_in_coreFoot (by decide))).trans r4, (hag _ (btHeader_in_coreFoot (by decide))).trans r5,
    (hag _ (btHeader_in_coreFoot (by decide))).trans r6, (hag _ (btHeader_in_coreFoot (by decide))).trans r7,
    (hag _ (btHeader_in_coreFoot (by decide))).trans r8', (hag _ (btHeader_in_coreFoot (by decide))).trans r9',
    (hag _ (btHeader_in_coreFoot (by decide))).trans r10', (hag _ (btHeader_in_coreFoot (by decide))).trans r11',
    hd, fun e he => ⟨fun j B hS heB => (hag _ (btEdgeSlot_in_coreFoot he)).trans ((hes e he).1 j B hS heB),
      fun hnone => (hag _ (btEdgeSlot_in_coreFoot he)).trans ((hes e he).2 hnone)⟩,
    fun j B hS x hx => by
      have hxk : endKey x < 2 * eCap := by
        have hsj := hsl j; rw [hS] at hsj
        cases hm : m.slotBlocks j with
        | none => rw [hm] at hsj; exact False.elim hsj
        | some pb =>
          rw [hm] at hsj; have := hsj.2.1.choose_spec.2.2.1 x.1 ((mem_edgeEnds _ _).mp hx)
          rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
      exact (hag _ (btEndBundle_in_coreFoot hxk)).trans (heb j B hS x hx),
    fun j => by
      have hsj := hsl j
      cases hS : tableDelEdges S₀ D j with
      | none =>
        rw [hS] at hsj
        cases hm : m.slotBlocks j with
        | none => rw [hm] at hsj; exact ⟨(hag _ (btSlotPtr_in_coreFoot j.2)).trans hsj.1,
            (hag _ (btSlotCandHead_in_coreFoot j.2)).trans hsj.2.1, hsj.2.2⟩
        | some _ => rw [hm] at hsj; exact False.elim hsj
      | some B =>
        rw [hS] at hsj
        cases hm : m.slotBlocks j with
        | none => rw [hm] at hsj; exact False.elim hsj
        | some pb =>
          rcases pb with ⟨p, c⟩; rw [hm] at hsj
          exact ⟨(hag _ (btSlotPtr_in_coreFoot j.2)).trans hsj.1,
            hsj.2.1.of_agree_ends (fun off hoff => hag _ (Or.inr ⟨j, p, c, hm, Nat.le_add_right _ _, by omega⟩))
              (hag _ (btSlotCandHead_in_coreFoot j.2))
              (fun k hk _ => ⟨hag _ (btEndPrev_in_coreFoot hk), hag _ (btEndNext_in_coreFoot hk)⟩), hsj.2.2⟩,
    hdb, hnd, hlt, fun s hs => (hag _ (btSlotTouched_in_coreFoot hs)).trans (htch s hs),
    fun j => by
      have hdj := hdl j
      cases hS0 : S₀ j with
      | none => rw [hS0] at hdj; exact ⟨(hag _ (btSlotDelHead_in_coreFoot j.2)).trans hdj.1, hdj.2⟩
      | some B₀ =>
        rw [hS0] at hdj; rcases hdj with ⟨hiff, dL, hsll, hdL⟩
        exact ⟨hiff, dL, hsll.of_agree (hag _ (btSlotDelHead_in_coreFoot j.2))
          fun e he => hag _ (btSlotDelNext_in_coreFoot (hsll.mem_lt e he)), hdL⟩,
    fun e he hnot => (hag _ (btSlotDelNext_in_coreFoot he)).trans (hdN0 e he hnot)⟩

lemma BundleTableAfterScan.of_agree_foot {slotCap vCap eCap tbl : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {candSet : Fin slotCap → Finset ℕ} {touched : List ℕ} {mem mem' : ℕ → ℕ}
    (h : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m candSet touched mem)
    (hag : ∀ a, bundleTableFoot eCap tbl m a → mem' a = mem a) :
    BundleTableAfterScan slotCap vCap eCap tbl S₀ D m candSet touched mem' :=
  h.of_agree_coreFoot fun a ha => hag a (bundleTableCoreFoot_subset_foot ha)

lemma BundleTableEmitState.of_agree_foot {slotCap vCap eCap tbl : ℕ}
    {S₀ S_cur : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {candSet : Fin slotCap → Finset ℕ} {remTouched : List ℕ} {mem mem' : ℕ → ℕ}
    (h : BundleTableEmitState slotCap vCap eCap tbl S₀ D m candSet S_cur remTouched mem)
    (hag : ∀ a, bundleTableFoot eCap tbl m a → mem' a = mem a) :
    BundleTableEmitState slotCap vCap eCap tbl S₀ D m candSet S_cur remTouched mem' := by
  rcases h with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8', r9', r10', r11',
    hd0, hdc, hSr, hes, heb, hsl, hdb, hnd, hlt, htch, hdl, hdN0⟩
  refine ⟨(hag _ (btHeader_in_foot (by decide))).trans r0, (hag _ (btHeader_in_foot (by decide))).trans r1,
    (hag _ (btHeader_in_foot (by decide))).trans r2, (hag _ (btHeader_in_foot (by decide))).trans r3,
    (hag _ (btHeader_in_foot (by decide))).trans r4, (hag _ (btHeader_in_foot (by decide))).trans r5,
    (hag _ (btHeader_in_foot (by decide))).trans r6, (hag _ (btHeader_in_foot (by decide))).trans r7,
    (hag _ (btHeader_in_foot (by decide))).trans r8', (hag _ (btHeader_in_foot (by decide))).trans r9',
    (hag _ (btHeader_in_foot (by decide))).trans r10', (hag _ (btHeader_in_foot (by decide))).trans r11',
    hd0, hdc, hSr, fun e he => ⟨fun j B hS heB => (hag _ (btEdgeSlot_in_foot he)).trans ((hes e he).1 j B hS heB),
      fun hnone => (hag _ (btEdgeSlot_in_foot he)).trans ((hes e he).2 hnone)⟩,
    fun j B hS x hx => by
      have hxk : endKey x < 2 * eCap := by
        have hsj := hsl j; rw [hS] at hsj
        cases hm : m.slotBlocks j with
        | none => rw [hm] at hsj; exact False.elim hsj
        | some pb =>
          rw [hm] at hsj
          have : x.1 < eCap := by
            split_ifs at hsj
            · exact hsj.2.2.choose_spec.2.2.1 x.1 ((mem_edgeEnds _ _).mp hx)
            · exact hsj.2.2.1.choose_spec.2.2.1 x.1 ((mem_edgeEnds _ _).mp hx)
          rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
      exact (hag _ (btEndBundle_in_foot hxk)).trans (heb j B hS x hx),
    fun j => by
      have hsj := hsl j
      cases hS : S_cur j with
      | none =>
        rw [hS] at hsj
        cases hm : m.slotBlocks j with
        | none => rw [hm] at hsj; exact ⟨(hag _ (btSlotPtr_in_foot j.2)).trans hsj.1,
            (hag _ (btSlotCandHead_in_foot j.2)).trans hsj.2.1, hsj.2.2⟩
        | some _ => rw [hm] at hsj; exact False.elim hsj
      | some B =>
        rw [hS] at hsj
        cases hm : m.slotBlocks j with
        | none => rw [hm] at hsj; exact False.elim hsj
        | some pb =>
          rcases pb with ⟨p, c⟩; rw [hm] at hsj
          refine ⟨(hag _ (btSlotPtr_in_foot j.2)).trans hsj.1, hsj.2.1, ?_⟩
          split_ifs at hsj ⊢
          · exact hsj.2.2.of_agree_ends (fun off hoff => hag _ (Or.inr ⟨j, p, c, hm, Nat.le_add_right _ _, by omega⟩))
              (hag _ (btSlotCandHead_in_foot j.2))
              (fun k hk _ => ⟨hag _ (btEndPrev_in_foot hk), hag _ (btEndNext_in_foot hk)⟩)
          · exact ⟨hsj.2.2.1.of_agree_ends (fun off hoff => hag _ (Or.inr ⟨j, p, c, hm, Nat.le_add_right _ _, by omega⟩))
              (fun k hk _ => ⟨hag _ (btEndPrev_in_foot hk), hag _ (btEndNext_in_foot hk)⟩),
              (hag _ (btSlotCandHead_in_foot j.2)).trans hsj.2.2.2⟩,
    hdb, hnd, hlt, fun s hs => (hag _ (btSlotTouched_in_foot hs)).trans (htch s hs),
    fun j => by
      have hdj := hdl j
      cases hS0 : S₀ j with
      | none => rw [hS0] at hdj; exact (hag _ (btSlotDelHead_in_foot j.2)).trans hdj
      | some B₀ =>
        rw [hS0] at hdj; split_ifs at hdj ⊢
        · rcases hdj with ⟨dL, hsll, hdL⟩
          exact ⟨dL, hsll.of_agree (hag _ (btSlotDelHead_in_foot j.2))
            fun e he => hag _ (btSlotDelNext_in_foot (hsll.mem_lt e he)), hdL⟩
        · exact (hag _ (btSlotDelHead_in_foot j.2)).trans hdj,
    fun e he hnot => (hag _ (btSlotDelNext_in_foot he)).trans (hdN0 e he hnot)⟩

lemma touched_len_le_slotCap {slotCap : ℕ} {touched : List ℕ}
    (hnd : touched.Nodup) (hlt : ∀ s ∈ touched, s < slotCap) : touched.length ≤ slotCap := by
  have hsub : touched.toFinset ⊆ Finset.range slotCap := fun s hs =>
    Finset.mem_range.mpr (hlt s (List.mem_toFinset.mp hs))
  rw [← List.toFinset_card_of_nodup hnd]
  exact (Finset.card_le_card hsub).trans (by simp)

lemma list_drop_erase_head {L : List ℕ} {i : ℕ} (hi : i < L.length) :
    (L.drop i).erase L[i] = L.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons hi, List.erase_cons_head]

lemma emitTotalSpace_take_succ (TS : BundleTourSpec) {slotCap : ℕ}
    (S₀ : BundleTableState slotCap) (D : Finset ℕ) (candSet : Fin slotCap → Finset ℕ)
    (scanLen : Fin slotCap → ℕ)
    {touched : List ℕ} {i : ℕ} (hi : i < touched.length) (hs : touched[i] < slotCap) :
    bundleStepEmitTotalSpace TS S₀ D candSet scanLen (touched.take (i + 1)) =
      bundleStepEmitTotalSpace TS S₀ D candSet scanLen (touched.take i) +
      bundleStepEmitSlotSpace TS (slotDelCnt S₀ D ⟨touched[i], hs⟩)
        (slotCandCnt candSet ⟨touched[i], hs⟩) (scanLen ⟨touched[i], hs⟩) := by
  unfold bundleStepEmitTotalSpace
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]
  simp [hs]

lemma emitTotalSpace_take_le (TS : BundleTourSpec) {slotCap : ℕ}
    (S₀ : BundleTableState slotCap) (D : Finset ℕ) (candSet : Fin slotCap → Finset ℕ)
    (scanLen : Fin slotCap → ℕ) (touched : List ℕ) {i : ℕ} :
    bundleStepEmitTotalSpace TS S₀ D candSet scanLen (touched.take i) ≤
      bundleStepEmitTotalSpace TS S₀ D candSet scanLen touched := by
  unfold bundleStepEmitTotalSpace
  have h := congrArg (fun l => (l.map fun s =>
    if hs : s < slotCap then
      bundleStepEmitSlotSpace TS (slotDelCnt S₀ D ⟨s, hs⟩) (slotCandCnt candSet ⟨s, hs⟩)
        (scanLen ⟨s, hs⟩)
    else 0).sum) (List.take_append_drop i touched)
  rw [List.map_append, List.sum_append] at h; omega

lemma rangeCost_emit_eq (TS : BundleTourSpec) (eCap : ℕ) {slotCap : ℕ}
    (S₀ : BundleTableState slotCap) (D : Finset ℕ) (candSet : Fin slotCap → Finset ℕ)
    (scanLen : Fin slotCap → ℕ) (touched : List ℕ) :
    rangeCost (fun i =>
      let s := touched.getD i 0
      (if hs : s < slotCap then
        bundleStepEmitSlotCost TS eCap (slotDelCnt S₀ D ⟨s, hs⟩) (slotCandCnt candSet ⟨s, hs⟩)
          (scanLen ⟨s, hs⟩)
      else 0) + 35) 0 touched.length =
      bundleStepEmitTotalCost TS eCap S₀ D candSet scanLen touched + 35 * touched.length := by
  have hgo : ∀ k ≤ touched.length,
      rangeCost (fun i =>
        let s := touched.getD i 0
        (if hs : s < slotCap then
          bundleStepEmitSlotCost TS eCap (slotDelCnt S₀ D ⟨s, hs⟩) (slotCandCnt candSet ⟨s, hs⟩)
            (scanLen ⟨s, hs⟩)
        else 0) + 35) 0 k =
        bundleStepEmitTotalCost TS eCap S₀ D candSet scanLen (touched.take k) + 35 * k := by
    intro k; induction k with
    | zero => intro _; simp [rangeCost, bundleStepEmitTotalCost]
    | succ k ih =>
      intro hk
      have hk_lt : k < touched.length := by omega
      have hrc : rangeCost (fun i =>
          let s := touched.getD i 0
          (if hs : s < slotCap then
            bundleStepEmitSlotCost TS eCap (slotDelCnt S₀ D ⟨s, hs⟩) (slotCandCnt candSet ⟨s, hs⟩)
              (scanLen ⟨s, hs⟩)
          else 0) + 35) 0 (k + 1) =
          rangeCost (fun i =>
          let s := touched.getD i 0
          (if hs : s < slotCap then
            bundleStepEmitSlotCost TS eCap (slotDelCnt S₀ D ⟨s, hs⟩) (slotCandCnt candSet ⟨s, hs⟩)
              (scanLen ⟨s, hs⟩)
          else 0) + 35) 0 k +
          ((if hs : touched[k] < slotCap then
            bundleStepEmitSlotCost TS eCap (slotDelCnt S₀ D ⟨touched[k], hs⟩)
              (slotCandCnt candSet ⟨touched[k], hs⟩) (scanLen ⟨touched[k], hs⟩)
          else 0) + 35) := by
        unfold rangeCost
        rw [Nat.sub_zero, Nat.sub_zero, List.range'_concat, List.map_append, List.sum_append]
        simp [List.getElem?_eq_getElem hk_lt]
      have htk : bundleStepEmitTotalCost TS eCap S₀ D candSet scanLen (touched.take (k + 1)) =
          bundleStepEmitTotalCost TS eCap S₀ D candSet scanLen (touched.take k) +
          (if hs : touched[k] < slotCap then
            bundleStepEmitSlotCost TS eCap (slotDelCnt S₀ D ⟨touched[k], hs⟩)
              (slotCandCnt candSet ⟨touched[k], hs⟩) (scanLen ⟨touched[k], hs⟩)
          else 0) := by
        unfold bundleStepEmitTotalCost
        rw [List.take_succ_eq_append_getElem hk_lt, List.map_append, List.sum_append]; simp
      rw [hrc, ih (by omega), htk]; ring
  have hfull : bundleStepEmitTotalCost TS eCap S₀ D candSet scanLen (touched.take touched.length) =
      bundleStepEmitTotalCost TS eCap S₀ D candSet scanLen touched := by
    unfold bundleStepEmitTotalCost; rw [List.take_length]
  rw [← hfull]; exact hgo touched.length (le_refl _)

end

end MinCostFlow.SparseCore.Program
