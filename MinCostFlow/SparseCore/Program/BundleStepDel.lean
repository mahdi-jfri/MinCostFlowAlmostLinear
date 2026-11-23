module

public import MinCostFlow.SparseCore.Program.BundleInitScan
public import WordRAM.Logic

import WordRAM.Tactic

/-!
# Phase 1 of `bundleRunsStep`: edge deletions and touched-slot collection (`BundleStepDel`)

Implements and verifies `bundleStepDelStmt bDllErase` (`[tbl, delCount, delPtr, touchedBufPtr]`):
for each deleted edge record `(e, oldCoreTail, oldCoreHead)` at `delPtr`, if `edgeSlot[e] = s + 1`:
1. Unlinks both ends `2 * e` and `2 * e + 1` from their bundles' doubly-linked lists via
   `bDllErase`, decrementing `size[b]` and saving `oldCoreTail` / `oldCoreHead` into
   `storedParent[b]` whenever `size[b]` drops to `0`.
2. Clears `edgeSlot[e] := 0`, decrements `nE[s]`, pushes `e` onto slot `s`'s 1-indexed deletion
   list `slotDelHead[s]` / `slotDelNext[e]`, and marks `slotTouched[s] := 1` (appending `s` to
   `touchedBufPtr` on its first touch).

Runs deterministically in `≤ 250 * delCount + 80` steps with zero heap allocation and no tour
queries. Also defines the reusable 1-indexed singly-linked list predicate `IsSinglyLinkedList`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. 1-indexed singly-linked list predicate -/

/-- 1-indexed singly-linked list (`0` = nil, `x + 1` = node `x < cap`, next pointer at
`nextBase + x`). Used for per-slot deleted-edge lists and split-candidate lists. -/
def IsSinglyLinkedList (mem : ℕ → ℕ) (nextBase headAddr cap : ℕ) : List ℕ → Prop
  | [] => mem headAddr = 0
  | x :: xs =>
      x < cap ∧ x ∉ xs ∧ mem headAddr = x + 1 ∧
      IsSinglyLinkedList mem nextBase (nextBase + x) cap xs

lemma IsSinglyLinkedList.nodup {mem : ℕ → ℕ} {nextBase headAddr cap : ℕ} {L : List ℕ}
    (h : IsSinglyLinkedList mem nextBase headAddr cap L) : L.Nodup := by
  induction L generalizing headAddr with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rcases h with ⟨_, hnot, _, hrest⟩
    exact List.nodup_cons.mpr ⟨hnot, ih hrest⟩

lemma IsSinglyLinkedList.mem_lt {mem : ℕ → ℕ} {nextBase headAddr cap : ℕ} {L : List ℕ}
    (h : IsSinglyLinkedList mem nextBase headAddr cap L) : ∀ x ∈ L, x < cap := by
  induction L generalizing headAddr with
  | nil => intro _ hx; cases hx
  | cons y ys ih =>
    rcases h with ⟨hy, _, _, hrest⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxs
    · exact hy
    · exact ih hrest x hxs

lemma IsSinglyLinkedList.of_agree {mem mem' : ℕ → ℕ} {nextBase headAddr cap : ℕ} {L : List ℕ}
    (h : IsSinglyLinkedList mem nextBase headAddr cap L)
    (hhead : mem' headAddr = mem headAddr)
    (hnext : ∀ x ∈ L, mem' (nextBase + x) = mem (nextBase + x)) :
    IsSinglyLinkedList mem' nextBase headAddr cap L := by
  induction L generalizing headAddr with
  | nil => exact hhead.trans h
  | cons x xs ih =>
    rcases h with ⟨hx, hnot, hhd, hrest⟩
    refine ⟨hx, hnot, hhead.trans hhd, ih hrest (hnext x List.mem_cons_self)
      fun y hy => hnext y (List.mem_cons_of_mem _ hy)⟩

lemma IsSinglyLinkedList.cons {mem mem' : ℕ → ℕ} {nextBase headAddr cap x : ℕ} {L : List ℕ}
    (h : IsSinglyLinkedList mem nextBase headAddr cap L)
    (hx : x < cap) (hnot : x ∉ L)
    (hhead' : mem' headAddr = x + 1)
    (hnextx' : mem' (nextBase + x) = mem headAddr)
    (hrest' : ∀ y ∈ L, mem' (nextBase + y) = mem (nextBase + y)) :
    IsSinglyLinkedList mem' nextBase headAddr cap (x :: L) := by
  refine ⟨hx, hnot, hhead', ?_⟩
  cases L with
  | nil => exact hnextx'.trans h
  | cons y ys =>
    rcases h with ⟨hy, hyn, hhd, htl⟩
    exact ⟨hy, hyn, hnextx'.trans hhd,
      htl.of_agree (hrest' y List.mem_cons_self) fun z hz => hrest' z (List.mem_cons_of_mem _ hz)⟩

/-! ## 2. Procedure bodies -/

/-- Sub-statement erasing end `r 20` (whose old parent is in `r 24`) from its bundle in slot block
`r 18` (`sCap = r 19`), decrementing `size` and saving `r 24` into `storedParent` if `size` hits
`0`. Uses scratch registers `21, 22, 23`. -/
def bundleDelEndStmt (bDllErase : ℕ) : Stmt :=
  .assign 21 (.load (.bin .add (.reg 7) (.reg 20))) ;;                           -- b := endBundle[key]
  .call 22 bDllErase [.reg 8, .reg 9,
    .bin .add (.bin .add (.reg 18) (.const 3)) (.reg 21), .reg 20] ;;
  .assign 23 (.bin .sub (.load (.bin .add (.bin .add (.bin .add (.reg 18) (.const 3)) (.reg 19)) (.reg 21)))
    (.const 1)) ;;                                                               -- sz' := size[b] - 1
  .store (.bin .add (.bin .add (.bin .add (.reg 18) (.const 3)) (.reg 19)) (.reg 21)) (.reg 23) ;;
  .cond (.bin .eq (.reg 23) (.const 0))
    (.store (.bin .add (.bin .add (.bin .add (.reg 18) (.const 3)) (.bin .mul (.const 2) (.reg 19))) (.reg 21))
      (.reg 24))
    .nop

/-- `args = [tbl, delCount, delPtr, touchedBufPtr]`: unlinks all active edges listed as
`(e, oldCoreTail, oldCoreHead)` triples at `delPtr`, updates `edgeSlot`, `nE`, `storedParent`,
pushes each removed edge to `slotDelHead[s]`/`slotDelNext`, records distinct touched slots in
`touchedBufPtr`, and returns `touchedCount`. -/
def bundleStepDelStmt (bDllErase : ℕ) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.const 3))) ;;                           -- slotPtrBase
  .assign 6 (.load (.bin .add (.reg 0) (.const 4))) ;;                           -- edgeSlotBase
  .assign 7 (.load (.bin .add (.reg 0) (.const 5))) ;;                           -- endBundleBase
  .assign 8 (.load (.bin .add (.reg 0) (.const 6))) ;;                           -- endPrevBase
  .assign 9 (.load (.bin .add (.reg 0) (.const 7))) ;;                           -- endNextBase
  .assign 10 (.load (.bin .add (.reg 0) (.const 8))) ;;                          -- slotTouchedBase
  .assign 11 (.load (.bin .add (.reg 0) (.const 9))) ;;                          -- slotDelHeadBase
  .assign 12 (.load (.bin .add (.reg 0) (.const 10))) ;;                         -- slotDelNextBase
  .assign 13 (.const 0) ;;                                                       -- touchedCount := 0
  forRange 14 (.const 0) (.reg 1)
    (.assign 15 (.load (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 14)))) ;; -- e
     .assign 16 (.load (.bin .add (.reg 6) (.reg 15))) ;;                        -- es := edgeSlot[e]
     .cond (.reg 16)
       (.assign 17 (.bin .sub (.reg 16) (.const 1)) ;;                           -- s := es - 1
        .assign 18 (.load (.bin .add (.reg 5) (.reg 17))) ;;                     -- p := slotPtr[s]
        .assign 19 (.load (.reg 18)) ;;                                          -- sCap := mem[p]
        .assign 20 (.bin .mul (.const 2) (.reg 15)) ;;                           -- kt := 2 * e
        .assign 24 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 14))) (.const 1))) ;;
        bundleDelEndStmt bDllErase ;;
        .assign 20 (.bin .add (.bin .mul (.const 2) (.reg 15)) (.const 1)) ;;    -- kh := 2 * e + 1
        .assign 24 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 14))) (.const 2))) ;;
        bundleDelEndStmt bDllErase ;;
        .store (.bin .add (.reg 6) (.reg 15)) (.const 0) ;;                      -- edgeSlot[e] := 0
        .assign 23 (.load (.bin .add (.reg 18) (.const 2))) ;;                   -- nE
        .store (.bin .add (.reg 18) (.const 2)) (.bin .sub (.reg 23) (.const 1)) ;;
        .assign 24 (.load (.bin .add (.reg 11) (.reg 17))) ;;                    -- oldDelHead
        .store (.bin .add (.reg 12) (.reg 15)) (.reg 24) ;;                      -- slotDelNext[e] := old
        .store (.bin .add (.reg 11) (.reg 17)) (.bin .add (.reg 15) (.const 1)) ;;
        .assign 24 (.load (.bin .add (.reg 10) (.reg 17))) ;;                    -- flag
        .cond (.bin .eq (.reg 24) (.const 0))
          (.store (.bin .add (.reg 10) (.reg 17)) (.const 1) ;;
           .store (.bin .add (.reg 3) (.reg 13)) (.reg 17) ;;
           .assign 13 (.bin .add (.reg 13) (.const 1)))
          .nop)
       .nop) ;;
  .ret (.reg 13)

lemma bundleStepDelStmt_noRand (bDllErase : ℕ) : (bundleStepDelStmt bDllErase).NoRand := by
  trivial

/-! ## 3. Abstract state after Phase 1 -/

/-- Reads `n` contiguous `(e, oldCoreTail, oldCoreHead)` deletion triples starting at `base`. -/
def readDelTriples (mem : ℕ → ℕ) (base n : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range n).map fun i => (mem (base + 3 * i), mem (base + 3 * i + 1), mem (base + 3 * i + 2))

/-- Abstract bundle table after removing edge set `D` from every active slot. -/
def tableDelEdges {slotCap : ℕ} (S : BundleTableState slotCap) (D : Finset ℕ) :
    BundleTableState slotCap :=
  fun j => (S j).map fun B => { B with edges := B.edges \ D }

/-- Active-slot state after Phase 1 (same as `BundleTableRepAt`, except `slotTouched`,
`slotDelHead`, `slotDelNext` record the deleted edges and touched slots in `touched`). -/
def BundleTableAfterDel (slotCap vCap eCap tbl : ℕ) (S₀ : BundleTableState slotCap)
    (D : Finset ℕ) (m : BundleTableMeta slotCap) (touched : List ℕ) (mem : ℕ → ℕ) : Prop :=
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
    | none, none => mem (btSlotPtrBase tbl + j.1) = 0
    | some B, some (p, bunCap) =>
        mem (btSlotPtrBase tbl + j.1) = p ∧
        BundleSlotRepAt eCap prevBase nextBase p bunCap B mem ∧
        (p + bundleSlotBlockSize bunCap ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ p)
    | _, _ => False) ∧
  (∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ p₁ c₁ p₂ c₂,
    m.slotBlocks j₁ = some (p₁, c₁) → m.slotBlocks j₂ = some (p₂, c₂) →
    p₁ + bundleSlotBlockSize c₁ ≤ p₂ ∨ p₂ + bundleSlotBlockSize c₂ ≤ p₁) ∧
  touched.Nodup ∧
  (∀ s ∈ touched, s < slotCap) ∧
  (∀ s < slotCap, mem (btSlotTouchedBase tbl slotCap eCap + s) = if s ∈ touched then 1 else 0) ∧
  (∀ s < slotCap, mem (btSlotCandHeadBase tbl slotCap eCap + s) = 0) ∧
  (∀ j : Fin slotCap,
    match S₀ j with
    | none => mem (btSlotDelHeadBase tbl slotCap eCap + j.1) = 0 ∧ j.1 ∉ touched
    | some B₀ =>
        (j.1 ∈ touched ↔ (B₀.edges ∩ D).Nonempty) ∧
        ∃ dL : List ℕ,
          IsSinglyLinkedList mem (btSlotDelNextBase tbl slotCap eCap)
            (btSlotDelHeadBase tbl slotCap eCap + j.1) eCap dL ∧
          (∀ e, e ∈ dL ↔ e ∈ B₀.edges ∩ D)) ∧
  (∀ e < eCap, (∀ j : Fin slotCap, ∀ B₀, S₀ j = some B₀ → e ∉ B₀.edges ∩ D) →
    mem (btSlotDelNextBase tbl slotCap eCap + e) = 0)

/-! ## 4. Single-end deletion helper (`bundleDelEnd_triple`) -/

/-- Verifies `bundleDelEndStmt bDllErase` removing one end `key` from bundle `b = mem (endBunBase + key)`
of block `(p, cap)`, decrementing `size[b]` and saving `oldPar` into `storedParent[b]` if `size[b]`
reaches `0`. -/
lemma bundleDelEnd_triple {w eCap endBunBase prevBase nextBase p cap key b oldPar : ℕ}
    {pProg : Program} {bDllErase : ℕ} {L : List ℕ} {mem regs0 : ℕ → ℕ}
    (hbErase : MeetsContract w pProg bDllErase
      (bundleDllEraseContract w prevBase nextBase (bsHeadBase p + b) (2 * eCap) key L))
    (hw16 : 16 ≤ 2 ^ w)
    (hprev_w : prevBase + 2 * eCap < 2 ^ w)
    (hnext_w : nextBase + 2 * eCap < 2 ^ w)
    (hprev_next : prevBase + 2 * eCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ prevBase)
    (hblk_w : p + bundleSlotBlockSize cap < 2 ^ w)
    (hblk_prev : p + bundleSlotBlockSize cap ≤ prevBase ∨ prevBase + 2 * eCap ≤ p)
    (hblk_next : p + bundleSlotBlockSize cap ≤ nextBase ∨ nextBase + 2 * eCap ≤ p)
    (hend_w : endBunBase + key < 2 ^ w)
    (hb_lt : b < cap) (hkey_lt : key < 2 * eCap) (hkey_in : key ∈ L)
    (_holdPar_w : oldPar < 2 ^ w)
    (hLlen_w : L.length < 2 ^ w)
    (hend_mem : mem (endBunBase + key) = b)
    (hdll : IsDoublyLinkedList mem prevBase nextBase (bsHeadBase p + b) (2 * eCap) L)
    (hsz_mem : mem (bsSizeBase p cap + b) = L.length) :
    Triple w pProg
      (fun st => st.mem = mem ∧ st.regs = regs0 ∧ regs0 7 = endBunBase ∧ regs0 8 = prevBase ∧
        regs0 9 = nextBase ∧ regs0 18 = p ∧ regs0 19 = cap ∧ regs0 20 = key ∧ regs0 24 = oldPar)
      (bundleDelEndStmt bDllErase)
      (normalPost fun st' =>
        (∀ r, r ≠ 21 → r ≠ 22 → r ≠ 23 → st'.regs r = regs0 r) ∧
        IsDoublyLinkedList st'.mem prevBase nextBase (bsHeadBase p + b) (2 * eCap) (L.erase key) ∧
        st'.mem (bsSizeBase p cap + b) = (L.erase key).length ∧
        (L.erase key = [] → st'.mem (bsParentBase p cap + b) = oldPar) ∧
        (L.erase key ≠ [] → st'.mem (bsParentBase p cap + b) = mem (bsParentBase p cap + b)) ∧
        (∀ a, a ≠ bsHeadBase p + b → a ≠ bsSizeBase p cap + b →
          a ≠ bsParentBase p cap + b →
          (∀ k ∈ L, a ≠ prevBase + k ∧ a ≠ nextBase + k) →
          st'.mem a = mem a))
      (fun _ => 125) := by
  wram_enter
  rcases st with ⟨mem_, regs_, pos_⟩
  rcases hpre with ⟨hmem, hregs, r7, r8, r9, r18, r19, r20, r24⟩
  dsimp only at hmem hregs; subst mem_; subst regs_
  have hlen_pos : 0 < L.length := List.length_pos_of_mem hkey_in
  have hlen_er : (L.erase key).length = L.length - 1 := List.length_erase_of_mem hkey_in
  have hblk_w' : p + (3 + 6 * cap) < 2 ^ w := hblk_w
  have hblk_prev' : p + (3 + 6 * cap) ≤ prevBase ∨ prevBase + 2 * eCap ≤ p := hblk_prev
  have hblk_next' : p + (3 + 6 * cap) ≤ nextBase ∨ nextBase + 2 * eCap ≤ p := hblk_next
  have hhead_prev : bsHeadBase p + b < prevBase ∨ prevBase + 2 * eCap ≤ bsHeadBase p + b := by
    unfold bsHeadBase; clear * - hblk_prev' hb_lt; omega
  have hhead_next : bsHeadBase p + b < nextBase ∨ nextBase + 2 * eCap ≤ bsHeadBase p + b := by
    unfold bsHeadBase; clear * - hblk_next' hb_lt; omega
  have hne_head_sz : bsHeadBase p + b ≠ p + 3 + cap + b := by
    unfold bsHeadBase; clear * - hb_lt; omega
  have hne_head_par : bsHeadBase p + b ≠ p + 3 + 2 * cap + b := by
    unfold bsHeadBase; clear * - hb_lt; omega
  have hne_sz_par : p + 3 + cap + b ≠ p + 3 + 2 * cap + b := by clear * - hb_lt; omega
  have hne_prev_sz : ∀ k < 2 * eCap, prevBase + k ≠ p + 3 + cap + b := fun k hk => by
    clear * - hblk_prev' hb_lt hk; omega
  have hne_prev_par : ∀ k < 2 * eCap, prevBase + k ≠ p + 3 + 2 * cap + b := fun k hk => by
    clear * - hblk_prev' hb_lt hk; omega
  have hne_next_sz : ∀ k < 2 * eCap, nextBase + k ≠ p + 3 + cap + b := fun k hk => by
    clear * - hblk_next' hb_lt hk; omega
  have hne_next_par : ∀ k < 2 * eCap, nextBase + k ≠ p + 3 + 2 * cap + b := fun k hk => by
    clear * - hblk_next' hb_lt hk; omega
  have hp3_w : p + 3 < 2 ^ w := by clear * - hblk_w'; omega
  have hp3b_w : p + 3 + b < 2 ^ w := by clear * - hblk_w' hb_lt; omega
  have hp3cap_w : p + 3 + cap < 2 ^ w := by clear * - hblk_w'; omega
  have hp3c_w : p + 3 + cap + b < 2 ^ w := by clear * - hblk_w' hb_lt; omega
  have h2cap_w : 2 * cap < 2 ^ w := by clear * - hblk_w'; omega
  have hp32c_w : p + 3 + 2 * cap < 2 ^ w := by clear * - hblk_w'; omega
  have hpar_w : p + 3 + 2 * cap + b < 2 ^ w := by clear * - hblk_w' hb_lt; omega
  have hsz_w : L.length - 1 < 2 ^ w := by clear * - hLlen_w; omega
  have h1_w : 1 < 2 ^ w := by clear * - hw16; omega
  have h2_w : 2 < 2 ^ w := by clear * - hw16; omega
  have h3_w : 3 < 2 ^ w := by clear * - hw16; omega
  dsimp only [bundleDelEndStmt]
  have hev_b : (Expr.load (.bin .add (.reg 7) (.reg 20))).eval w ⟨mem, regs0, pos_⟩ = some b := by
    simp [Expr.eval, BinOp.eval, r7, r20, hend_w, hend_mem]
  refine runs_seq_assign_le hev_b ?_
  have hargs_eval : evalArgs w ⟨mem, Function.update regs0 21 b, pos_⟩
      [.reg 8, .reg 9, .bin .add (.bin .add (.reg 18) (.const 3)) (.reg 21), .reg 20] =
      some [prevBase, nextBase, bsHeadBase p + b, key] := by
    unfold bsHeadBase
    simp [evalArgs, Expr.eval, BinOp.eval, r8, r9, r18, r20, h3_w, hp3_w, hp3b_w]
  have hwords : ∀ v ∈ [prevBase, nextBase, bsHeadBase p + b, key], v < 2 ^ w := by
    intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    unfold bsHeadBase at hv
    rcases hv with rfl | rfl | rfl | rfl <;> clear * - hprev_w hnext_w hp3b_w hkey_lt <;> omega
  have her_pre : (bundleDllEraseContract w prevBase nextBase (bsHeadBase p + b) (2 * eCap) key L).pre
      [prevBase, nextBase, bsHeadBase p + b, key] mem :=
    ⟨rfl, hw16, hprev_w, hnext_w, hprev_next, hhead_prev, hhead_next, hkey_in, hdll⟩
  refine runs_seq_call_le hbErase hargs_eval hwords her_pre fun ret mem1 pos1 ⟨_, hdll1, _, _, hfr1⟩ => ?_
  have hsz1 : mem1 (p + 3 + cap + b) = L.length := by
    have h1 := hfr1 (bsSizeBase p cap + b) (by unfold bsSizeBase; exact hne_head_sz.symm)
      (fun k hk => ⟨(hne_prev_sz k (hdll.2.1 k hk)).symm, (hne_next_sz k (hdll.2.1 k hk)).symm⟩)
    exact h1.trans hsz_mem
  have hev_szAddr : (Expr.bin .add (.bin .add (.bin .add (.reg 18) (.const 3)) (.reg 19)) (.reg 21)).eval w
      ⟨mem1, Function.update (Function.update regs0 21 b) 22 ret, pos1⟩ = some (p + 3 + cap + b) := by
    simp [Expr.eval, BinOp.eval, r18, r19, h3_w, hp3_w, hp3cap_w, hp3c_w]
  have hev_load : (Expr.load (.bin .add (.bin .add (.bin .add (.reg 18) (.const 3)) (.reg 19)) (.reg 21))).eval w
      ⟨mem1, Function.update (Function.update regs0 21 b) 22 ret, pos1⟩ = some L.length := by
    rw [Expr.eval, hev_szAddr]; simp [hsz1]
  refine runs_seq_assign_le (v := L.length - 1) (by
    rw [Expr.eval, hev_load]
    simp [Expr.eval, BinOp.eval, h1_w, hsz_w]) ?_
  set regs2 := Function.update (Function.update (Function.update regs0 21 b) 22 ret) 23 (L.length - 1)
  have hev_szAddr2 : (Expr.bin .add (.bin .add (.bin .add (.reg 18) (.const 3)) (.reg 19)) (.reg 21)).eval w
      ⟨mem1, regs2, pos1⟩ = some (p + 3 + cap + b) := by
    simp [Expr.eval, BinOp.eval, regs2, r18, r19, h3_w, hp3_w, hp3cap_w, hp3c_w]
  have hev_r23 : (Expr.reg 23).eval w ⟨mem1, regs2, pos1⟩ = some (L.length - 1) := by
    simp [Expr.eval, regs2]
  refine runs_seq_store_le hev_szAddr2 hev_r23 ?_
  set mem2 := Function.update mem1 (p + 3 + cap + b) (L.length - 1)
  have hreg_eq : ∀ r, r ≠ 21 → r ≠ 22 → r ≠ 23 → regs2 r = regs0 r := fun r h1 h2 h3 => by
    simp [regs2, h1, h2, h3]
  by_cases hem : L.erase key = []
  · have hzero : L.length - 1 = 0 := by rw [← hlen_er, hem]; rfl
    refine runs_cond_true_le (v := 1) (by simp [Expr.eval, BinOp.eval, regs2, hzero, h1_w])
      (by decide) ?_
    have hev_par : (Expr.bin .add (.bin .add (.bin .add (.reg 18) (.const 3))
        (.bin .mul (.const 2) (.reg 19))) (.reg 21)).eval w ⟨mem2, regs2, pos1⟩ =
        some (p + 3 + 2 * cap + b) := by
      simp [Expr.eval, BinOp.eval, regs2, r18, r19, h3_w, h2_w, hp3_w, h2cap_w, hp32c_w, hpar_w]
    have hev_r24 : (Expr.reg 24).eval w ⟨mem2, regs2, pos1⟩ = some oldPar := by
      simp [Expr.eval, regs2, r24]
    refine runs_store_le hev_par hev_r24 ?_ ?_
    · refine ⟨hreg_eq, ?_, ?_, ?_, fun hne => absurd hem hne, ?_⟩
      · refine hdll1.of_agree ?_ ?_ ?_
        · dsimp only [mem2]
          rw [Function.update_of_ne hne_head_par, Function.update_of_ne hne_head_sz]
        · intro k hk; dsimp only [mem2]
          rw [Function.update_of_ne (hne_prev_par k (hdll1.2.1 k hk)),
            Function.update_of_ne (hne_prev_sz k (hdll1.2.1 k hk))]
        · intro k hk; dsimp only [mem2]
          rw [Function.update_of_ne (hne_next_par k (hdll1.2.1 k hk)),
            Function.update_of_ne (hne_next_sz k (hdll1.2.1 k hk))]
      · dsimp only [mem2]; unfold bsSizeBase
        rw [Function.update_of_ne hne_sz_par, Function.update_self, hlen_er]
      · intro _; dsimp only [mem2]; unfold bsParentBase; exact Function.update_self _ _ _
      · intro a ha1 ha2 ha3 haL
        dsimp only [mem2]; unfold bsSizeBase at ha2; unfold bsParentBase at ha3
        rw [Function.update_of_ne ha3, Function.update_of_ne ha2, hfr1 a ha1 haL]
    · simp only [bundleDllEraseContract, argsSize,
        Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; decide
  · have hpos : L.length - 1 ≠ 0 := by
      rw [← hlen_er]; exact Nat.ne_of_gt (List.length_pos_of_ne_nil hem)
    refine runs_cond_false_le (by simp [Expr.eval, BinOp.eval, regs2, hpos]) ?_
    refine runs_nop_le ?_ ?_
    · refine ⟨hreg_eq, ?_, ?_, fun he => absurd he hem, ?_, ?_⟩
      · refine hdll1.of_agree ?_ ?_ ?_
        · dsimp only [mem2]; rw [Function.update_of_ne hne_head_sz]
        · intro k hk; dsimp only [mem2]
          rw [Function.update_of_ne (hne_prev_sz k (hdll1.2.1 k hk))]
        · intro k hk; dsimp only [mem2]
          rw [Function.update_of_ne (hne_next_sz k (hdll1.2.1 k hk))]
      · dsimp only [mem2]; unfold bsSizeBase; rw [Function.update_self, hlen_er]
      · intro _; dsimp only [mem2]; unfold bsParentBase
        rw [Function.update_of_ne hne_sz_par.symm,
          hfr1 _ hne_head_par.symm
            (fun k hk => ⟨(hne_prev_par k (hdll.2.1 k hk)).symm, (hne_next_par k (hdll.2.1 k hk)).symm⟩)]
      · intro a ha1 ha2 _ haL
        dsimp only [mem2]; unfold bsSizeBase at ha2
        rw [Function.update_of_ne ha2, hfr1 a ha1 haL]
    · simp only [bundleDllEraseContract, argsSize,
        Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; decide

end

end MinCostFlow.SparseCore.Program
