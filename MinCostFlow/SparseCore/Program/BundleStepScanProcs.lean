module

public import MinCostFlow.SparseCore.Program.BundleStepDel
public import MinCostFlow.SparseCore.Program.BundleStepScanPassCDefs
public import MinCostFlow.SparseCore.Program.BundleTourInterface
public import MinCostFlow.SparseCore.Program.BundleModelBridge

/-!
# Phase 2 smaller-side root scan procedures (`BundleStepScanProcs`)

Defines `bundleStepScanStmt bTourLen bTourList` and its sub-statements (max-tour search,
Pass A end counting, Pass B candidate enqueue + zeroing of `seen`), the concatenated group
layout `readGroups`, the intermediate table predicate `BundleTableAfterScan`, and the
verification of the max-tour search loop (`bundleStepScanMax_runs`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Sub-statements and Phase 2 procedure -/

/-- Finds `r17 = maxIdx` and `r18 = maxLen` over `j ∈ [0, r15)` of `cord' (mem[r16 + j])`,
calling `bTourLen [r1, w, r6]` and updating heap pointer `r6`. -/
def bundleStepScanMaxStmt (bTourLen : ℕ) : Stmt :=
  .assign 17 (.const 0) ;;
  .assign 18 (.const 0) ;;
  forRange 19 (.const 0) (.reg 15)
    (.assign 20 (.load (.bin .add (.reg 16) (.reg 19))) ;;
     .assign 21 (.reg 6) ;;
     .call 6 bTourLen [.reg 1, .reg 20, .reg 6] ;;
     .assign 22 (.load (.reg 21)) ;;
     .cond (.bin .lt (.reg 18) (.reg 22))
       (.assign 17 (.reg 19) ;;
        .assign 18 (.reg 22))
       .nop)

/-- Pass A over `r22` ends stored in `EndListAt` at `r21`: increments `seen[b]` for every active
end in `r21`. Uses scratch registers `23..31`. -/
def bundleStepScanPassAStmt : Stmt :=
  forRange 23 (.const 0) (.reg 22)
    (.assign 24 (.load (.bin .add (.bin .add (.reg 21) (.const 1)) (.reg 23))) ;;
     .assign 25 (.bin .div (.reg 24) (.const 2)) ;;
     .assign 26 (.load (.bin .add (.reg 8) (.reg 25))) ;;
     .cond (.reg 26)
       (.assign 27 (.bin .sub (.reg 26) (.const 1)) ;;
        .assign 28 (.load (.bin .add (.reg 7) (.reg 27))) ;;
        .assign 29 (.load (.reg 28)) ;;
        .assign 30 (.load (.bin .add (.reg 9) (.reg 24))) ;;
        .assign 31 (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
          (.bin .mul (.const 3) (.reg 29))) (.reg 30)) ;;
        .store (.reg 31) (.bin .add (.load (.reg 31)) (.const 1)))
       .nop)

/-- Pass B over `r22` ends stored in `EndListAt` at `r21`: for each active end whose bundle has
`seenVal = seen[b] > 0`, zeroes `seen[b]`, and if `seenVal < size[b]` and `inCand[b] = 0`, marks
`inCand[b] := 1`, pushes `b` to `slotCandHead[s]`/`candNext`, and marks `s` touched if new. -/
def bundleStepScanPassBStmt : Stmt :=
  forRange 23 (.const 0) (.reg 22)
    (.assign 24 (.load (.bin .add (.bin .add (.reg 21) (.const 1)) (.reg 23))) ;;
     .assign 25 (.bin .div (.reg 24) (.const 2)) ;;
     .assign 26 (.load (.bin .add (.reg 8) (.reg 25))) ;;
     .cond (.reg 26)
       (.assign 27 (.bin .sub (.reg 26) (.const 1)) ;;
        .assign 28 (.load (.bin .add (.reg 7) (.reg 27))) ;;
        .assign 29 (.load (.reg 28)) ;;
        .assign 30 (.load (.bin .add (.reg 9) (.reg 24))) ;;
        .assign 31 (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
          (.bin .mul (.const 3) (.reg 29))) (.reg 30)) ;;
        .assign 32 (.load (.reg 31)) ;;
        .cond (.reg 32)
          (.store (.reg 31) (.const 0) ;;
           .assign 33 (.load (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
             (.reg 29)) (.reg 30))) ;;
           .cond (.bin .lt (.reg 32) (.reg 33))
             (.assign 34 (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
                (.bin .mul (.const 4) (.reg 29))) (.reg 30)) ;;
              .assign 35 (.load (.reg 34)) ;;
              .cond (.bin .eq (.reg 35) (.const 0))
                (.store (.reg 34) (.const 1) ;;
                 .assign 36 (.load (.bin .add (.reg 11) (.reg 27))) ;;
                 .store (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
                   (.bin .mul (.const 5) (.reg 29))) (.reg 30)) (.reg 36) ;;
                 .store (.bin .add (.reg 11) (.reg 27)) (.bin .add (.reg 30) (.const 1)) ;;
                 .assign 36 (.load (.bin .add (.reg 10) (.reg 27))) ;;
                 .cond (.bin .eq (.reg 36) (.const 0))
                   (.store (.bin .add (.reg 10) (.reg 27)) (.const 1) ;;
                    .store (.bin .add (.reg 5) (.reg 13)) (.reg 27) ;;
                    .assign 13 (.bin .add (.reg 13) (.const 1)))
                   .nop)
                .nop)
             .nop)
          .nop)
       .nop)

/-- Processes one non-maximal root `w = mem[r16 + r19]` by exporting `cord' w` via `bTourList`,
running Pass A, Pass B, and Pass C (recording active ends of candidate splitting bundles). -/
def bundleStepScanRootStmt (bTourList : ℕ) : Stmt :=
  .assign 20 (.load (.bin .add (.reg 16) (.reg 19))) ;;
  .assign 21 (.reg 6) ;;
  .call 6 bTourList [.reg 1, .reg 20, .reg 6] ;;
  .assign 22 (.load (.reg 21)) ;;
  bundleStepScanPassAStmt ;;
  bundleStepScanPassBStmt ;;
  bundleStepScanPassCStmt

/-- `args = [tbl, tourH, groupCount, groupPtr, touchedCountPtr, touchedBufPtr, h]`:
scans all non-largest roots in each split group, enqueues all splitting bundles into
`slotCandHead`/`candNext`, updates `touchedBufPtr` and `mem[touchedCountPtr]`, and returns `h'`. -/
def bundleStepScanStmt (bTourLen bTourList : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 0) (.const 3))) ;;                           -- slotPtrBase
  .assign 8 (.load (.bin .add (.reg 0) (.const 4))) ;;                           -- edgeSlotBase
  .assign 9 (.load (.bin .add (.reg 0) (.const 5))) ;;                           -- endBundleBase
  .assign 10 (.load (.bin .add (.reg 0) (.const 8))) ;;                          -- slotTouchedBase
  .assign 11 (.load (.bin .add (.reg 0) (.const 11))) ;;                         -- slotCandHeadBase
  .assign 12 (.reg 3) ;;                                                         -- curPtr := groupPtr
  .assign 13 (.load (.reg 4)) ;;                                                 -- touchedCount
  forRange 14 (.const 0) (.reg 2)
    (.assign 15 (.load (.reg 12)) ;;                                             -- c := mem[curPtr]
     .assign 16 (.bin .add (.reg 12) (.const 1)) ;;                              -- wBase := curPtr + 1
     bundleStepScanMaxStmt bTourLen ;;
     forRange 19 (.const 0) (.reg 15)
       (.cond (.bin .eq (.reg 19) (.reg 17))
         .nop
         (bundleStepScanRootStmt bTourList)) ;;
     .assign 12 (.bin .add (.bin .add (.reg 12) (.const 1)) (.reg 15))) ;;
  .store (.reg 4) (.reg 13) ;;
  .ret (.reg 6)

lemma bundleStepScanStmt_noRand (bTourLen bTourList : ℕ) :
    (bundleStepScanStmt bTourLen bTourList).NoRand := by
  trivial

/-! ## 2. Concatenated group records, space/cost bounds, and post-scan state -/

/-- Reads `g` concatenated `[c, w_0, ..., w_{c-1}]` split-group records starting at `ptr`. -/
def readGroups (mem : ℕ → ℕ) (ptr : ℕ) : ℕ → List (List ℕ)
  | 0 => []
  | g + 1 =>
    let c := mem ptr
    ((List.range c).map fun j => mem (ptr + 1 + j)) :: readGroups mem (ptr + 1 + c) g

/-- Total number of words occupied by concatenated group records `gs`. -/
def groupsWords (gs : List (List ℕ)) : ℕ :=
  (gs.map fun G => 1 + G.length).sum

/-- Total number of core vertices across all groups `gs`. -/
def groupsTotalLen (gs : List (List ℕ)) : ℕ :=
  (gs.map List.length).sum

/-- Heap space budget for Phase 2 on groups `gs` under final tours `cord'` (including `3` words per
scanned end for Pass C's per-slot linked-list nodes). -/
def bundleStepScanSpace (TS : BundleTourSpec) (cord' : ℕ → List End) (gs : List (List ℕ)) : ℕ :=
  TS.querySpace * groupsTotalLen gs +
    (gs.map fun G => (G.map fun w => TS.listSpace (cord' w).length + 3 * (cord' w).length).sum).sum

/-- Amortized cost bound (excluding the tour-potential drop) for Phase 2. -/
def bundleStepScanCost (TS : BundleTourSpec) (eCap : ℕ) (gs : List (List ℕ)) : ℕ :=
  (2 * TS.mul * ordStoreLog eCap + 200) * groupsTotalLen gs + 70 * gs.length + 80

/-- Multiplier on `tourPot` in the amortized analysis of Phase 2 and Phase 3 (covers Pass A +
Pass B + Pass C + Phase 3 scanned-end CSR, candidate sorting, and two-branch splitting). -/
def bundleScanPotMul (TS : BundleTourSpec) (eCap : ℕ) : ℕ :=
  (3 * TS.mul + 900) * ordStoreLog eCap + 4600

/-- Slot-block representation with `seen` zeroed, `inCand` matching `candSet`, and `candNext`
encoding a singly-linked list of `candSet` (all other fields identical to `BundleSlotRepAt`). -/
def BundleSlotRepCand (eCap prevBase nextBase p bunCap : ℕ) (B : BundleState)
    (candHeadAddr : ℕ) (candSet : Finset ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ nB : ℕ,
    B.vertices = Finset.range nB ∧ nB ≤ bunCap ∧
    (∀ e ∈ B.edges, e < eCap) ∧
    (∀ x ∈ edgeEnds B.edges, B.bundleOf x < nB) ∧
    (∀ b, nB ≤ b → B.parent b = 0) ∧
    mem (p + bsOffBunCap) = bunCap ∧
    mem (p + bsOffNB) = nB ∧
    mem (p + bsOffNE) = B.edges.card ∧
    (∀ b < nB, ∃ L : List ℕ,
      IsDoublyLinkedList mem prevBase nextBase (bsHeadBase p + b) (2 * eCap) L ∧
      mem (bsSizeBase p bunCap + b) = L.length ∧
      ∀ k, k ∈ L ↔ endOfKey k ∈ B.ends b) ∧
    (∀ b < nB, B.ends b = ∅ → mem (bsParentBase p bunCap + b) = B.parent b) ∧
    (∀ b, nB ≤ b → b < bunCap →
      mem (bsHeadBase p + b) = 0 ∧ mem (bsSizeBase p bunCap + b) = 0 ∧
      mem (bsParentBase p bunCap + b) = 0) ∧
    (∀ b < bunCap, mem (bsSeenBase p bunCap + b) = 0) ∧
    (∀ b < bunCap, mem (bsInCandBase p bunCap + b) = if b ∈ candSet then 1 else 0) ∧
    (∀ b ∈ candSet, b < nB) ∧
    (∃ cL : List ℕ,
      IsSinglyLinkedList mem (bsCandNextBase p bunCap) candHeadAddr bunCap cL ∧
      ∀ b, b ∈ cL ↔ b ∈ candSet) ∧
    (∀ b < bunCap, b ∉ candSet → mem (bsCandNextBase p bunCap + b) = 0)

/-- Full table state during/after Phase 2: extends `BundleTableAfterDel` with per-slot candidate
sets `candSet : Fin slotCap → Finset ℕ` stored in `slotCandHead`/`inCand`/`candNext`. -/
def BundleTableAfterScan (slotCap vCap eCap tbl : ℕ) (S₀ : BundleTableState slotCap)
    (D : Finset ℕ) (m : BundleTableMeta slotCap) (candSet : Fin slotCap → Finset ℕ)
    (touched : List ℕ) (mem : ℕ → ℕ) : Prop :=
  let S := tableDelEdges S₀ D
  let prevBase := btEndPrevBase tbl slotCap eCap
  let nextBase := btEndNextBase tbl slotCap eCap
  mem (tbl + btOffSlotCap) = slotCap ∧
  mem (tbl + btOffVCap) = vCap ∧
  mem (tbl + btOffECap) = eCap ∧
  mem (tbl + btOffSlotPtr) = btSlotPtrBase tbl ∧
  mem (tbl + btOffEdgeSlot) = btEdgeSlotBase tbl slotCap ∧
  mem (tbl + btOffEndBundle) = btEndBundleBase tbl slotCap eCap ∧
  mem (tbl + btOffEndPrev) = prevBase ∧
  mem (tbl + btOffEndNext) = nextBase ∧
  mem (tbl + btOffSlotTouched) = btSlotTouchedBase tbl slotCap eCap ∧
  mem (tbl + btOffSlotDelHead) = btSlotDelHeadBase tbl slotCap eCap ∧
  mem (tbl + btOffSlotDelNext) = btSlotDelNextBase tbl slotCap eCap ∧
  mem (tbl + btOffSlotCandHead) = btSlotCandHeadBase tbl slotCap eCap ∧
  (∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ B₁ B₂,
    S j₁ = some B₁ → S j₂ = some B₂ → Disjoint B₁.edges B₂.edges) ∧
  (∀ e < eCap,
    (∀ (j : Fin slotCap) (B : BundleState), S j = some B → e ∈ B.edges →
      mem (btEdgeSlotBase tbl slotCap + e) = j.1 + 1) ∧
    ((∀ (j : Fin slotCap) (B : BundleState), S j = some B → e ∉ B.edges) →
      mem (btEdgeSlotBase tbl slotCap + e) = 0)) ∧
  (∀ (j : Fin slotCap) (B : BundleState), S j = some B →
    ∀ x ∈ edgeEnds B.edges,
      mem (btEndBundleBase tbl slotCap eCap + endKey x) = B.bundleOf x) ∧
  (∀ j : Fin slotCap,
    match S j, m.slotBlocks j with
    | none, none => mem (btSlotPtrBase tbl + j.1) = 0 ∧
        mem (btSlotCandHeadBase tbl slotCap eCap + j.1) = 0 ∧ candSet j = ∅
    | some B, some (p, bunCap) =>
        mem (btSlotPtrBase tbl + j.1) = p ∧
        BundleSlotRepCand eCap prevBase nextBase p bunCap B
          (btSlotCandHeadBase tbl slotCap eCap + j.1) (candSet j) mem ∧
        (p + bundleSlotBlockSize bunCap ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ p)
    | _, _ => False) ∧
  (∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ p₁ c₁ p₂ c₂,
    m.slotBlocks j₁ = some (p₁, c₁) → m.slotBlocks j₂ = some (p₂, c₂) →
    p₁ + bundleSlotBlockSize c₁ ≤ p₂ ∨ p₂ + bundleSlotBlockSize c₂ ≤ p₁) ∧
  touched.Nodup ∧
  (∀ s ∈ touched, s < slotCap) ∧
  (∀ s < slotCap, mem (btSlotTouchedBase tbl slotCap eCap + s) = if s ∈ touched then 1 else 0) ∧
  (∀ j : Fin slotCap,
    match S₀ j with
    | none => mem (btSlotDelHeadBase tbl slotCap eCap + j.1) = 0 ∧ j.1 ∉ touched
    | some B₀ =>
        (j.1 ∈ touched ↔ (B₀.edges ∩ D).Nonempty ∨ (candSet j).Nonempty) ∧
        ∃ dL : List ℕ,
          IsSinglyLinkedList mem (btSlotDelNextBase tbl slotCap eCap)
            (btSlotDelHeadBase tbl slotCap eCap + j.1) eCap dL ∧
          (∀ e, e ∈ dL ↔ e ∈ B₀.edges ∩ D)) ∧
  (∀ e < eCap, (∀ j : Fin slotCap, ∀ B₀, S₀ j = some B₀ → e ∉ B₀.edges ∩ D) →
    mem (btSlotDelNextBase tbl slotCap eCap + e) = 0)

end

public section

/-! ## 3. Basic helpers for `BundleTableAfterScan` and `readGroups` -/

lemma bundleTableAfterDel_to_afterScan {slotCap vCap eCap tbl : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {touched : List ℕ} {mem : ℕ → ℕ}
    (h : BundleTableAfterDel slotCap vCap eCap tbl S₀ D m touched mem) :
    BundleTableAfterScan slotCap vCap eCap tbl S₀ D m (fun _ => ∅) touched mem := by
  rcases h with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11,
    hdisjE, hedgeSlot, hendBun, hslots, hdisjB, htnd, htlt, htflag, hcand0, hdelL, hdelN0⟩
  refine ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11,
    hdisjE, hedgeSlot, hendBun, fun j => ?_, hdisjB, htnd, htlt, htflag, fun j => ?_, hdelN0⟩
  · have hj := hslots j
    change match tableDelEdges S₀ D j, m.slotBlocks j with
      | none, none => mem (btSlotPtrBase tbl + j.1) = 0
      | some B, some (p, bunCap) =>
          mem (btSlotPtrBase tbl + j.1) = p ∧
          BundleSlotRepAt eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
            p bunCap B mem ∧
          (p + bundleSlotBlockSize bunCap ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ p)
      | _, _ => False at hj
    change match tableDelEdges S₀ D j, m.slotBlocks j with
      | none, none => mem (btSlotPtrBase tbl + j.1) = 0 ∧
          mem (btSlotCandHeadBase tbl slotCap eCap + j.1) = 0 ∧ (∅ : Finset ℕ) = ∅
      | some B, some (p, bunCap) =>
          mem (btSlotPtrBase tbl + j.1) = p ∧
          BundleSlotRepCand eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
            p bunCap B (btSlotCandHeadBase tbl slotCap eCap + j.1) ∅ mem ∧
          (p + bundleSlotBlockSize bunCap ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ p)
      | _, _ => False
    cases hSj : tableDelEdges S₀ D j with
    | none =>
      rw [hSj] at hj
      cases hm : m.slotBlocks j with
      | none => rw [hm] at hj; exact ⟨hj, hcand0 j.1 j.2, rfl⟩
      | some _ => rw [hm] at hj; exact False.elim hj
    | some B =>
      rw [hSj] at hj
      cases hm : m.slotBlocks j with
      | none => rw [hm] at hj; exact False.elim hj
      | some pb =>
        rcases pb with ⟨p, cap⟩; rw [hm] at hj
        obtain ⟨hptr, ⟨nB, hV, hnB, hE, hbo, hpar0, h0, h1, h2, hdll, hpar, htail, hscr⟩, hdj⟩ := hj
        refine ⟨hptr, ⟨nB, hV, hnB, hE, hbo, hpar0, h0, h1, h2, hdll, hpar, htail,
          fun b hb => (hscr b hb).1, fun b hb => by simp [(hscr b hb).2.1],
          (fun _ hb => by cases hb), ⟨[], hcand0 j.1 j.2, by simp⟩,
          fun b hb _ => (hscr b hb).2.2⟩, hdj⟩
  · have hj := hdelL j
    change match S₀ j with
      | none => mem (btSlotDelHeadBase tbl slotCap eCap + j.1) = 0 ∧ j.1 ∉ touched
      | some B₀ => (j.1 ∈ touched ↔ (B₀.edges ∩ D).Nonempty) ∧ _ at hj
    cases hSj : S₀ j with
    | none => rw [hSj] at hj; exact hj
    | some B₀ => rw [hSj] at hj; simpa using hj

lemma BundleSlotRepCand.of_agree {eCap prevBase nextBase p bunCap : ℕ} {B : BundleState}
    {candHeadAddr : ℕ} {candSet : Finset ℕ} {mem mem' : ℕ → ℕ}
    (h : BundleSlotRepCand eCap prevBase nextBase p bunCap B candHeadAddr candSet mem)
    (hblk : ∀ a, p ≤ a → a < p + bundleSlotBlockSize bunCap → mem a = mem' a)
    (hprev : ∀ k < 2 * eCap, mem (prevBase + k) = mem' (prevBase + k))
    (hnext : ∀ k < 2 * eCap, mem (nextBase + k) = mem' (nextBase + k))
    (hch : mem candHeadAddr = mem' candHeadAddr) :
    BundleSlotRepCand eCap prevBase nextBase p bunCap B candHeadAddr candSet mem' := by
  obtain ⟨nB, hV, hnB, hE, hbo, hpar0, h0, h1, h2, hdll, hpar, htail, hseen, hic, hc_lt,
    ⟨cL, hcL_sll, hcL_mem⟩, hcN0⟩ := h
  have hb : ∀ off < bundleSlotBlockSize bunCap, mem' (p + off) = mem (p + off) :=
    fun off hoff => (hblk (p + off) (Nat.le_add_right _ _) (by omega)).symm
  refine ⟨nB, hV, hnB, hE, hbo, hpar0,
    (hb bsOffBunCap (by unfold bsOffBunCap bundleSlotBlockSize; omega)).trans h0,
    (hb bsOffNB (by unfold bsOffNB bundleSlotBlockSize; omega)).trans h1,
    (hb bsOffNE (by unfold bsOffNE bundleSlotBlockSize; omega)).trans h2,
    fun b hbl => ?_, fun b hbl hem => ?_, fun b hge hlt => ?_,
    fun b hbl => ?_, fun b hbl => ?_, hc_lt,
    ⟨cL, hcL_sll.of_agree hch.symm fun x hx => by
      have hxlt := hcL_sll.mem_lt x hx
      have := hb (3 + 5 * bunCap + x) (by unfold bundleSlotBlockSize; omega)
      simpa [bsCandNextBase, Nat.add_assoc] using this,
      hcL_mem⟩,
    fun b hbl hnot => ?_⟩
  · obtain ⟨L, hL, hsz, hmem⟩ := hdll b hbl
    have hb_cap : b < bunCap := lt_of_lt_of_le hbl hnB
    have hhd' := hb (3 + b) (by unfold bundleSlotBlockSize; omega)
    refine ⟨L, hL.of_agree
      (by simpa [bsHeadBase, Nat.add_assoc] using hhd')
      (fun k hk => (hprev k (hL.2.1 k hk)).symm) (fun k hk => (hnext k (hL.2.1 k hk)).symm),
      ?_, hmem⟩
    have hsz' := hb (3 + bunCap + b) (by unfold bundleSlotBlockSize; omega)
    simpa [bsSizeBase, Nat.add_assoc] using hsz'.trans (by simpa [bsSizeBase, Nat.add_assoc] using hsz)
  · have hb_cap : b < bunCap := lt_of_lt_of_le hbl hnB
    have hpa' := hb (3 + 2 * bunCap + b) (by unfold bundleSlotBlockSize; omega)
    simpa [bsParentBase, Nat.add_assoc] using hpa'.trans (by simpa [bsParentBase, Nat.add_assoc] using hpar b hbl hem)
  · obtain ⟨t1, t2, t3⟩ := htail b hge hlt
    have ht1 := hb (3 + b) (by unfold bundleSlotBlockSize; omega)
    have ht2 := hb (3 + bunCap + b) (by unfold bundleSlotBlockSize; omega)
    have ht3 := hb (3 + 2 * bunCap + b) (by unfold bundleSlotBlockSize; omega)
    exact ⟨by simpa [bsHeadBase, Nat.add_assoc] using ht1.trans (by simpa [bsHeadBase, Nat.add_assoc] using t1),
      by simpa [bsSizeBase, Nat.add_assoc] using ht2.trans (by simpa [bsSizeBase, Nat.add_assoc] using t2),
      by simpa [bsParentBase, Nat.add_assoc] using ht3.trans (by simpa [bsParentBase, Nat.add_assoc] using t3)⟩
  · have hs' := hb (3 + 3 * bunCap + b) (by unfold bundleSlotBlockSize; omega)
    simpa [bsSeenBase, Nat.add_assoc] using hs'.trans (by simpa [bsSeenBase, Nat.add_assoc] using hseen b hbl)
  · have hi' := hb (3 + 4 * bunCap + b) (by unfold bundleSlotBlockSize; omega)
    simpa [bsInCandBase, Nat.add_assoc] using hi'.trans (by simpa [bsInCandBase, Nat.add_assoc] using hic b hbl)
  · have hc' := hb (3 + 5 * bunCap + b) (by unfold bundleSlotBlockSize; omega)
    simpa [bsCandNextBase, Nat.add_assoc] using hc'.trans (by simpa [bsCandNextBase, Nat.add_assoc] using hcN0 b hbl hnot)

lemma BundleTableAfterScan.of_agree {slotCap vCap eCap tbl : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {candSet : Fin slotCap → Finset ℕ} {touched : List ℕ} {mem mem' : ℕ → ℕ}
    (h : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m candSet touched mem)
    (hag : ∀ a, bundleTableCoreFoot eCap tbl m a → mem a = mem' a) :
    BundleTableAfterScan slotCap vCap eCap tbl S₀ D m candSet touched mem' := by
  have hf : ∀ off < bundleTableCoreSize slotCap eCap, mem' (tbl + off) = mem (tbl + off) :=
    fun off hoff => (hag (tbl + off) (Or.inl ⟨by omega, by omega⟩)).symm
  rcases h with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11,
    hdisjE, hedgeSlot, hendBun, hslots, hdisjB, htnd, htlt, htflag, hdelL, hdelN0⟩
  refine ⟨(hf 0 (by unfold bundleTableCoreSize; omega)).trans r0,
    (hf 1 (by unfold bundleTableCoreSize; omega)).trans r1,
    (hf 2 (by unfold bundleTableCoreSize; omega)).trans r2,
    (hf 3 (by unfold bundleTableCoreSize; omega)).trans r3,
    (hf 4 (by unfold bundleTableCoreSize; omega)).trans r4,
    (hf 5 (by unfold bundleTableCoreSize; omega)).trans r5,
    (hf 6 (by unfold bundleTableCoreSize; omega)).trans r6,
    (hf 7 (by unfold bundleTableCoreSize; omega)).trans r7,
    (hf 8 (by unfold bundleTableCoreSize; omega)).trans r8,
    (hf 9 (by unfold bundleTableCoreSize; omega)).trans r9,
    (hf 10 (by unfold bundleTableCoreSize; omega)).trans r10,
    (hf 11 (by unfold bundleTableCoreSize; omega)).trans r11,
    hdisjE, fun e he => ?_, fun j B hSj x hx => ?_, fun j => ?_, hdisjB, htnd, htlt,
    fun s hs => ?_, fun j => ?_, fun e he hnot => ?_⟩
  · have hEq : mem' (btEdgeSlotBase tbl slotCap + e) = mem (btEdgeSlotBase tbl slotCap + e) :=
      (hag _ (Or.inl ⟨by unfold btEdgeSlotBase; omega, by unfold btEdgeSlotBase bundleTableCoreSize; omega⟩)).symm
    rw [hEq]; exact hedgeSlot e he
  · have hkx : endKey x < 2 * eCap := by
      have hj := hslots j; rw [hSj] at hj
      cases hm : m.slotBlocks j with
      | none => rw [hm] at hj; exact False.elim hj
      | some pb =>
        rw [hm] at hj
        have he_lt := hj.2.1.choose_spec.2.2.1 x.1 ((mem_edgeEnds _ _).mp hx)
        rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
    have hEq : mem' (btEndBundleBase tbl slotCap eCap + endKey x) = mem (btEndBundleBase tbl slotCap eCap + endKey x) :=
      (hag _ (Or.inl ⟨by unfold btEndBundleBase; omega, by unfold btEndBundleBase bundleTableCoreSize; omega⟩)).symm
    rw [hEq]; exact hendBun j B hSj x hx
  · have hj := hslots j
    have hj_lt : j.1 < slotCap := j.2
    have hptr : mem' (btSlotPtrBase tbl + j.1) = mem (btSlotPtrBase tbl + j.1) :=
      (hag _ (Or.inl ⟨by unfold btSlotPtrBase; omega, by unfold btSlotPtrBase bundleTableCoreSize; clear * - hj_lt; omega⟩)).symm
    have hch : mem (btSlotCandHeadBase tbl slotCap eCap + j.1) = mem' (btSlotCandHeadBase tbl slotCap eCap + j.1) :=
      hag _ (Or.inl ⟨by unfold btSlotCandHeadBase; omega, by unfold btSlotCandHeadBase bundleTableCoreSize; clear * - hj_lt; omega⟩)
    change match tableDelEdges S₀ D j, m.slotBlocks j with
      | none, none => mem (btSlotPtrBase tbl + j.1) = 0 ∧
          mem (btSlotCandHeadBase tbl slotCap eCap + j.1) = 0 ∧ candSet j = ∅
      | some B, some (p, bunCap) =>
          mem (btSlotPtrBase tbl + j.1) = p ∧
          BundleSlotRepCand eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
            p bunCap B (btSlotCandHeadBase tbl slotCap eCap + j.1) (candSet j) mem ∧
          (p + bundleSlotBlockSize bunCap ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ p)
      | _, _ => False at hj
    change match tableDelEdges S₀ D j, m.slotBlocks j with
      | none, none => mem' (btSlotPtrBase tbl + j.1) = 0 ∧
          mem' (btSlotCandHeadBase tbl slotCap eCap + j.1) = 0 ∧ candSet j = ∅
      | some B, some (p, bunCap) =>
          mem' (btSlotPtrBase tbl + j.1) = p ∧
          BundleSlotRepCand eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
            p bunCap B (btSlotCandHeadBase tbl slotCap eCap + j.1) (candSet j) mem' ∧
          (p + bundleSlotBlockSize bunCap ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ p)
      | _, _ => False
    cases hSj : tableDelEdges S₀ D j with
    | none =>
      rw [hSj] at hj
      cases hm : m.slotBlocks j with
      | none => rw [hm] at hj; exact ⟨hptr.trans hj.1, hch.symm.trans hj.2.1, hj.2.2⟩
      | some _ => rw [hm] at hj; exact False.elim hj
    | some B =>
      rw [hSj] at hj
      cases hm : m.slotBlocks j with
      | none => rw [hm] at hj; exact False.elim hj
      | some pb =>
        rcases pb with ⟨p, cap⟩; rw [hm] at hj
        refine ⟨hptr.trans hj.1, hj.2.1.of_agree
          (fun a ha1 ha2 => hag a (Or.inr ⟨j, p, cap, hm, ha1, ha2⟩))
          (fun k hk => hag _ (Or.inl ⟨by unfold btEndPrevBase; omega, by unfold btEndPrevBase bundleTableCoreSize; omega⟩))
          (fun k hk => hag _ (Or.inl ⟨by unfold btEndNextBase; omega, by unfold btEndNextBase bundleTableCoreSize; omega⟩))
          hch, hj.2.2⟩
  · have hEq : mem' (btSlotTouchedBase tbl slotCap eCap + s) = mem (btSlotTouchedBase tbl slotCap eCap + s) :=
      (hag _ (Or.inl ⟨by unfold btSlotTouchedBase; omega, by unfold btSlotTouchedBase bundleTableCoreSize; omega⟩)).symm
    rw [hEq]; exact htflag s hs
  · have hj := hdelL j
    have hj_lt : j.1 < slotCap := j.2
    have hdh : mem' (btSlotDelHeadBase tbl slotCap eCap + j.1) = mem (btSlotDelHeadBase tbl slotCap eCap + j.1) :=
      (hag _ (Or.inl ⟨by unfold btSlotDelHeadBase; omega, by unfold btSlotDelHeadBase bundleTableCoreSize; clear * - hj_lt; omega⟩)).symm
    change match S₀ j with
      | none => mem (btSlotDelHeadBase tbl slotCap eCap + j.1) = 0 ∧ j.1 ∉ touched
      | some B₀ => (j.1 ∈ touched ↔ (B₀.edges ∩ D).Nonempty ∨ (candSet j).Nonempty) ∧ _ at hj
    cases hSj : S₀ j with
    | none => rw [hSj] at hj; exact ⟨hdh.trans hj.1, hj.2⟩
    | some B₀ =>
      rw [hSj] at hj
      rcases hj with ⟨htj, dL, hdL_sll, hdL_mem⟩
      exact ⟨htj, dL, hdL_sll.of_agree hdh fun x hx =>
        (hag _ (Or.inl ⟨by unfold btSlotDelNextBase; omega,
          by unfold btSlotDelNextBase bundleTableCoreSize; have := hdL_sll.mem_lt x hx; omega⟩)).symm,
        hdL_mem⟩
  · have hEq : mem' (btSlotDelNextBase tbl slotCap eCap + e) = mem (btSlotDelNextBase tbl slotCap eCap + e) :=
      (hag _ (Or.inl ⟨by unfold btSlotDelNextBase; omega, by unfold btSlotDelNextBase bundleTableCoreSize; omega⟩)).symm
    rw [hEq]; exact hdelN0 e he hnot

/-! ## 4. Verification of max-tour search (`bundleStepScanMax_runs`) -/

/-- Verifies `bundleStepScanMaxStmt bTourLen` on a group `G` stored at `wBase`: finds `maxIdx`
maximizing `(cord' G[j]).length` while preserving all memory outside `[h₀, h') ∪ tourFoot`. -/
lemma bundleStepScanMax_runs {TS : BundleTourSpec} {w vCap eCap tourH wBase h₀ : ℕ}
    {pProg : Program} {bTourList bTourLen bTourOwner : ℕ}
    {htour : BundleTourAt TS w vCap eCap pProg bTourList bTourLen bTourOwner}
    {cord' : ℕ → List End} {G : List ℕ} {tx₀ : htour.rep.τ} {st₀ : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (htourH_w : tourH < 2 ^ w)
    (hG_pos : 0 < G.length)
    (hG_lt : ∀ v ∈ G, v < vCap ∧ v < 2 ^ w)
    (hG_mem : ListAt st₀.mem wBase G)
    (hwBase_h : wBase + G.length ≤ h₀)
    (hwBase_disj_tour : ∀ a, wBase ≤ a → a < wBase + G.length → ¬ htour.rep.foot tourH tx₀ a)
    (hh_sp_w : h₀ + TS.querySpace * G.length < 2 ^ w)
    (htrep : htour.rep.rep tourH cord' tx₀ st₀.mem)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h₀)
    (hzero : ZeroFrom st₀.mem h₀)
    (hr1 : st₀.regs 1 = tourH) (hr6 : st₀.regs 6 = h₀)
    (hr15 : st₀.regs 15 = G.length) (hr16 : st₀.regs 16 = wBase) :
    ∃ st' c h' tx' maxIdx,
      Runs w pProg ω (bundleStepScanMaxStmt bTourLen) st₀ .normal st' c ∧
      (∀ r, r ≤ 16 → r ≠ 6 → st'.regs r = st₀.regs r) ∧
      st'.regs 6 = h' ∧ st'.regs 17 = maxIdx ∧
      (∃ hm : maxIdx < G.length,
        ∀ j (hj : j < G.length), (cord' G[j]).length ≤ (cord' G[maxIdx]).length) ∧
      h₀ ≤ h' ∧ h' ≤ h₀ + TS.querySpace * G.length ∧
      ZeroFrom st'.mem h' ∧
      htour.rep.rep tourH cord' tx' st'.mem ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < h')) ∧
      (∀ a < h₀, ¬ htour.rep.foot tourH tx₀ a → st'.mem a = st₀.mem a) ∧
      c + htour.rep.phi tourH tx' st'.mem ≤
        (TS.mul * ordStoreLog eCap + 50) * G.length + 25 + htour.rep.phi tourH tx₀ st₀.mem := by
  have h1_w : 1 < 2 ^ w := by omega
  have hc_w : G.length < 2 ^ w := by
    have hq := TS.querySpace_ge
    have hle : G.length ≤ TS.querySpace * G.length := by simpa using Nat.mul_le_mul_right G.length hq
    omega
  set st1 : State := { st₀ with regs := Function.update st₀.regs 17 0 }
  set st2 : State := { st1 with regs := Function.update st1.regs 18 0 }
  have ha17 : Runs w pProg ω (.assign 17 (.const 0)) st₀ .normal st1 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have ha18 : Runs w pProg ω (.assign 18 (.const 0)) st1 .normal st2 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  -- Loop invariant over (hCur, tx, maxIdx, maxLen)
  let Acc := ℕ × htour.rep.τ × ℕ × ℕ
  let Inv' : ℕ → Acc → State → Prop := fun j acc st =>
    let (hCur, tx, mIdx, mLen) := acc
    (∀ r, r ≤ 16 → r ≠ 6 → st.regs r = st₀.regs r) ∧
    st.regs 6 = hCur ∧ st.regs 17 = mIdx ∧ st.regs 18 = mLen ∧ st.regs 19 = j ∧
    h₀ ≤ hCur ∧ hCur ≤ h₀ + TS.querySpace * j ∧
    ZeroFrom st.mem hCur ∧
    htour.rep.rep tourH cord' tx st.mem ∧
    (∀ a, htour.rep.foot tourH tx a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < hCur)) ∧
    (∀ a < h₀, ¬ htour.rep.foot tourH tx₀ a → st.mem a = st₀.mem a) ∧
    mIdx < G.length ∧
    (j = 0 → mIdx = 0 ∧ mLen = 0) ∧
    (0 < j → ∃ hmj : mIdx < G.length, mLen = (cord' G[mIdx]).length ∧
      ∀ k (hk : k < j) (hkg : k < G.length), (cord' G[k]).length ≤ mLen)
  obtain ⟨st_end, c_loop, ⟨hEnd, txEnd, maxIdx, maxLen⟩, hrun_loop, hInv_end, hc_loop⟩ :=
    runs_forRange_pot (w := w) (p := pProg) (ω := ω) (r := 19) (lo := .const 0) (hi := .reg 15)
      (phi := fun acc st => htour.rep.phi tourH acc.2.1 st.mem) (Inv := Inv')
      (stepCost := fun _ => TS.mul * ordStoreLog eCap + 36) G.length
      (by omega) (fun _ => by omega) (st₀ := st2) (a₀ := (h₀, tx₀, 0, 0))
      (by
        refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], ?_, rfl⟩
        exact ⟨fun r hr _ => by simp [st2, st1, show r ≠ 19 by omega, show r ≠ 18 by omega, show r ≠ 17 by omega],
          by simp [st2, st1, hr6], by simp [st2, st1], by simp [st2], by simp,
          le_refl _, by simp, hzero, htrep, fun _ h => Or.inl h, fun _ _ _ => rfl,
          hG_pos, fun _ => ⟨rfl, rfl⟩, fun h => by omega⟩)
      (fun _ _ _ _ hI => hI.2.2.2.2.1)
      (fun _ _ st _ hI => by simp [Expr.eval, hI.1 15 (by decide) (by decide), hr15])
      (fun j ⟨hCur, tx, mIdx, mLen⟩ st hj hI => by
        rcases hI with ⟨hregs, hr6c, hr17c, hr18c, hr19c, hh0_le, hhCur_le, hzeroC, htrepC,
          htfootC, hfrC, hmIdx_lt, h0_len, hpos_len⟩
        set v := G[j]'hj
        have hv_lt := hG_lt v (List.getElem_mem hj)
        have hmem_v : st.mem (wBase + j) = v := by
          rw [hfrC (wBase + j) (by omega) (hwBase_disj_tour _ (by omega) (by omega))]
          exact hG_mem j hj
        have hCur_sp : hCur + TS.querySpace < 2 ^ w := by
          have h1 : TS.querySpace * (j + 1) ≤ TS.querySpace * G.length :=
            Nat.mul_le_mul_left _ (by omega)
          have h2 : TS.querySpace * (j + 1) = TS.querySpace * j + TS.querySpace := by ring
          omega
        set st_a := { st with regs := Function.update st.regs 20 v }
        set st_b := { st_a with regs := Function.update st_a.regs 21 hCur }
        have ha20 : Runs w pProg ω (.assign 20 (.load (.bin .add (.reg 16) (.reg 19)))) st .normal st_a 5 :=
          runs_assign_iff.mpr ⟨v, by
            simp [Expr.eval, BinOp.eval, hregs 16 (by decide) (by decide), hr16, hr19c, hmem_v,
              show wBase + j < 2 ^ w by omega], rfl, rfl, rfl⟩
        have ha21 : Runs w pProg ω (.assign 21 (.reg 6)) st_a .normal st_b 2 :=
          runs_assign_iff.mpr ⟨hCur, by simp [Expr.eval, st_a, hr6c], rfl, rfl, rfl⟩
        have htfoot_ltC : ∀ a, htour.rep.foot tourH tx a → a < hCur := fun a ha => by
          rcases htfootC a ha with h0 | ⟨_, hlt⟩
          · exact Nat.lt_of_lt_of_le (htfoot_lt a h0) hh0_le
          · exact hlt
        obtain ⟨body, hbody, oL, st_c_raw, cL, tx', hrunL, htrep', hlen_mem, hh'_ge, hresp, hcL⟩ :=
          htour.len_runs tourH v hCur cord' tx st.mem st_b.pos ω htourH_w hv_lt.1 hv_lt.2
            (by omega) htrepC htfoot_ltC hzeroC hCur_sp
        rcases hresp with ⟨hhCur_le', hh'_le, hzero', hfrL, htfoot'⟩
        set h' := oL.value
        set st_c : State := { mem := st_c_raw.mem, regs := Function.update st_b.regs 6 h', pos := st_c_raw.pos }
        have hcall : Runs w pProg ω (.call 6 bTourLen [.reg 1, .reg 20, .reg 6]) st_b .normal st_c (cL + 4) := by
          have hargs : evalArgs w st_b [.reg 1, .reg 20, .reg 6] = some [tourH, v, hCur] := by
            simp [evalArgs, Expr.eval, st_b, st_a, hregs 1 (by decide) (by decide), hr1, hr6c]
          have hc : Runs w pProg ω (.call 6 bTourLen [.reg 1, .reg 20, .reg 6]) st_b .normal
              { mem := st_c_raw.mem, regs := Function.update st_b.regs 6 oL.value, pos := st_c_raw.pos }
              (argsSize [.reg 1, .reg 20, .reg 6] + cL + 1) :=
            runs_call_iff.mpr ⟨[tourH, v, hCur], body, oL, st_c_raw, cL, hargs, hbody, hrunL, rfl, rfl, rfl⟩
          simpa [argsSize, Expr.size, st_c, h', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hc
        set lenV := (cord' v).length
        set st_d : State := { st_c with regs := Function.update st_c.regs 22 lenV }
        have ha22 : Runs w pProg ω (.assign 22 (.load (.reg 21))) st_c .normal st_d 3 :=
          runs_assign_iff.mpr ⟨lenV, by simp [Expr.eval, st_c, st_b, hlen_mem], rfl, rfl, rfl⟩
        have hlt_eval : (Expr.bin .lt (.reg 18) (.reg 22)).eval w st_d =
            some (if mLen < lenV then 1 else 0) := by
          by_cases h : mLen < lenV <;>
            simp [Expr.eval, BinOp.eval, st_d, st_c, st_b, st_a, hr18c, h, h1_w]
        by_cases hgt : mLen < lenV
        · set st_e1 : State := { st_d with regs := Function.update st_d.regs 17 j }
          set st_e2 : State := { st_e1 with regs := Function.update st_e1.regs 18 lenV }
          have h17 : Runs w pProg ω (.assign 17 (.reg 19)) st_d .normal st_e1 2 :=
            runs_assign_iff.mpr ⟨j, by simp [Expr.eval, st_d, st_c, st_b, st_a, hr19c], rfl, rfl, rfl⟩
          have h18 : Runs w pProg ω (.assign 18 (.reg 22)) st_e1 .normal st_e2 2 :=
            runs_assign_iff.mpr ⟨lenV, by simp [Expr.eval, st_e1, st_d], rfl, rfl, rfl⟩
          have hcond : Runs w pProg ω (.cond (.bin .lt (.reg 18) (.reg 22))
              (.assign 17 (.reg 19) ;; .assign 18 (.reg 22)) .nop) st_d .normal st_e2 9 :=
            runs_cond_iff.mpr ⟨1, 5, by simpa [hgt] using hlt_eval,
              by simpa using bundle_runs_seq_normal h17 h18, rfl⟩
          refine ⟨st_e2, 5 + (2 + ((cL + 4) + (3 + 9 + 1) + 1) + 1) + 1, (h', tx', j, lenV),
            bundle_runs_seq_normal ha20 (bundle_runs_seq_normal ha21
              (bundle_runs_seq_normal hcall (bundle_runs_seq_normal ha22 hcond))),
            by simp [st_e2, st_e1, st_d, st_c, st_b, st_a, hr19c], ?_, ?_⟩
          · refine ⟨fun r hr hne6 => by
                simp [st_e2, st_e1, st_d, st_c, st_b, st_a, show r ≠ 19 by omega, show r ≠ 18 by omega, show r ≠ 17 by omega,
                  show r ≠ 22 by omega, hne6, show r ≠ 21 by omega, show r ≠ 20 by omega, hregs r hr hne6],
              by simp [st_e2, st_e1, st_d, st_c], by simp [st_e2, st_e1], by simp [st_e2], by simp,
              le_trans hh0_le hhCur_le', by
                have : TS.querySpace * (j + 1) = TS.querySpace * j + TS.querySpace := by ring
                omega,
              hzero', htrep', fun a ha => by
                rcases htfoot' a ha with h1 | ⟨h1, h2⟩
                · rcases htfootC a h1 with h0 | ⟨ha1, ha2⟩
                  · exact Or.inl h0
                  · exact Or.inr ⟨ha1, Nat.lt_of_lt_of_le ha2 hhCur_le'⟩
                · exact Or.inr ⟨le_trans hh0_le h1, h2⟩,
              fun a ha hnf => by
                have hnfC : ¬ htour.rep.foot tourH tx a := fun h => by
                  rcases htfootC a h with h0 | ⟨ha1, _⟩
                  · exact hnf h0
                  · omega
                exact (hfrL a (Nat.lt_of_lt_of_le ha hh0_le) hnfC).trans (hfrC a ha hnf),
              hj, fun h => by omega, fun _ => ⟨hj, rfl, fun k hk hkg => by
                by_cases hkj : k = j
                · subst hkj; exact le_refl _
                · have hpos : 0 < j := by omega
                  obtain ⟨_, _, hle⟩ := hpos_len hpos
                  have := hle k (by omega) hkg
                  omega⟩⟩
          · dsimp only [st_e2, st_e1, st_d, st_c]; omega
        · have hcond : Runs w pProg ω (.cond (.bin .lt (.reg 18) (.reg 22))
              (.assign 17 (.reg 19) ;; .assign 18 (.reg 22)) .nop) st_d .normal st_d 5 :=
            runs_cond_iff.mpr ⟨0, 1, by simpa [hgt] using hlt_eval,
              by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
          have hmLen_eq : (j = 0 → lenV = 0) := fun hj0 => by have := (h0_len hj0).2; omega
          refine ⟨st_d, 5 + (2 + ((cL + 4) + (3 + 5 + 1) + 1) + 1) + 1, (h', tx', mIdx, mLen),
            bundle_runs_seq_normal ha20 (bundle_runs_seq_normal ha21
              (bundle_runs_seq_normal hcall (bundle_runs_seq_normal ha22 hcond))),
            by simp [st_d, st_c, st_b, st_a, hr19c], ?_, ?_⟩
          · refine ⟨fun r hr hne6 => by
                simp [st_d, st_c, st_b, st_a, show r ≠ 19 by omega, show r ≠ 22 by omega, hne6, show r ≠ 21 by omega,
                  show r ≠ 20 by omega, hregs r hr hne6],
              by simp [st_d, st_c], by simp [st_d, st_c, st_b, st_a, hr17c],
              by simp [st_d, st_c, st_b, st_a, hr18c], by simp,
              le_trans hh0_le hhCur_le', by
                have : TS.querySpace * (j + 1) = TS.querySpace * j + TS.querySpace := by ring
                omega,
              hzero', htrep', fun a ha => by
                rcases htfoot' a ha with h1 | ⟨h1, h2⟩
                · rcases htfootC a h1 with h0 | ⟨ha1, ha2⟩
                  · exact Or.inl h0
                  · exact Or.inr ⟨ha1, Nat.lt_of_lt_of_le ha2 hhCur_le'⟩
                · exact Or.inr ⟨le_trans hh0_le h1, h2⟩,
              fun a ha hnf => by
                have hnfC : ¬ htour.rep.foot tourH tx a := fun h => by
                  rcases htfootC a h with h0 | ⟨ha1, _⟩
                  · exact hnf h0
                  · omega
                exact (hfrL a (Nat.lt_of_lt_of_le ha hh0_le) hnfC).trans (hfrC a ha hnf),
              hmIdx_lt, fun h => by omega, fun _ => ?_⟩
            by_cases hj0 : j = 0
            · subst hj0
              obtain ⟨hm0, hml0⟩ := h0_len rfl
              subst hm0
              have hlen0 : (cord' G[0]).length = 0 := hmLen_eq rfl
              exact ⟨hmIdx_lt, by rw [hml0, hlen0], fun k hk _ => by
                have hk0 : k = 0 := by omega
                subst hk0; rw [hml0, hlen0]⟩
            · have hpos : 0 < j := by omega
              obtain ⟨hmj, hml, hle⟩ := hpos_len hpos
              refine ⟨hmj, hml, fun k hk hkg => ?_⟩
              by_cases hkj : k = j
              · subst hkj; dsimp only [lenV, v] at hgt; omega
              · exact hle k (by omega) hkg
          · dsimp only [st_d, st_c]; omega)
  rcases hInv_end with ⟨hregs, hr6e, hr17e, _, _, hh0_le, hhEnd_le, hzeroE, htrepE,
    htfootE, hfrE, hmIdx_lt, _, hpos_len⟩
  obtain ⟨_, hmLen_eq, hmax⟩ := hpos_len hG_pos
  refine ⟨st_end, 2 + (2 + c_loop + 1) + 1, hEnd, txEnd, maxIdx,
    bundle_runs_seq_normal ha17 (bundle_runs_seq_normal ha18 hrun_loop),
    hregs, hr6e, hr17e, ⟨hmIdx_lt, fun j hj => hmLen_eq ▸ hmax j hj hj⟩,
    hh0_le, hhEnd_le, hzeroE, htrepE, htfootE, hfrE, ?_⟩
  have hrc : rangeCost (fun _ => TS.mul * ordStoreLog eCap + 36) 0 G.length =
      (TS.mul * ordStoreLog eCap + 36) * G.length := by
    rw [rangeCost_zero_eq_range]; simp [Nat.mul_comm]
  rw [hrc] at hc_loop; simp only [Expr.size_const, Expr.size_reg, st2, st1] at hc_loop
  have hmul : (TS.mul * ordStoreLog eCap + 50) * G.length =
      (TS.mul * ordStoreLog eCap + 36) * G.length + 14 * G.length := by ring
  omega

end

end MinCostFlow.SparseCore.Program
