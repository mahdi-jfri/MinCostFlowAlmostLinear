module

public import MinCostFlow.SparseCore.Program.BundleLayout
public import WordRAM.Logic

/-!
# Phase 2 Pass C definitions: scanned-end list layout and pure model (`BundleStepScanPassCDefs`)

Defines:
* `packEndKey eCap v key := v * (2 * eCap) + key` (shared between Phase 2 Pass C and Phase 3),
* `bundleStepScanPassCStmt`: Pass C of `bundleStepScanRootStmt`, which pushes a 3-word heap node
  `[b, packEndKey eCap v key, oldHead]` onto `btCurBunBase[s]` and increments `btCurTagBase[s]`
  for every active end in `cord' v` belonging to a splitting candidate bundle (`inCand[b] = 1`),
* `ScanNodesAt` and `SlotScanListAt`: the heap linked-list invariant for `btCurBunBase`/`btCurTagBase`,
* `addScanEndsForList`: pure specification of Pass C's per-slot scanned-end lists.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore

@[expose] public section

/-- Packs `(v, key)` into a single word `v * (2 * eCap) + key` preserving lexicographic order. -/
def packEndKey (eCap v key : ℕ) : ℕ :=
  v * (2 * eCap) + key

/-- Pass C over `r22` ends stored in `EndListAt` at `r21` for non-maximal root `r20 = v`:
for every active end whose bundle has `inCand[b] ≠ 0`, allocates a 3-word heap node
`[b, v * (2 * eCap) + key, curBun[s]]` at `r6`, sets `curBun[s] := r6`, advances `r6 := r6 + 3`,
and increments `curTag[s]`. Uses scratch registers `23..37`; updates only `r6` among `r0..r22`. -/
def bundleStepScanPassCStmt : Stmt :=
  .assign 23 (.load (.reg 0)) ;;
  .assign 24 (.bin .mul (.const 2) (.load (.bin .add (.reg 0) (.const 2)))) ;;
  .assign 25 (.bin .add (.reg 11) (.reg 23)) ;;
  .assign 26 (.bin .add (.reg 25) (.reg 23)) ;;
  .assign 27 (.bin .mul (.reg 20) (.reg 24)) ;;
  forRange 28 (.const 0) (.reg 22)
    (.assign 29 (.load (.bin .add (.bin .add (.reg 21) (.const 1)) (.reg 28))) ;;
     .assign 30 (.bin .div (.reg 29) (.const 2)) ;;
     .assign 31 (.load (.bin .add (.reg 8) (.reg 30))) ;;
     .cond (.reg 31)
       (.assign 32 (.bin .sub (.reg 31) (.const 1)) ;;
        .assign 33 (.load (.bin .add (.reg 7) (.reg 32))) ;;
        .assign 34 (.load (.reg 33)) ;;
        .assign 35 (.load (.bin .add (.reg 9) (.reg 29))) ;;
        .assign 36 (.load (.bin .add (.bin .add (.bin .add (.reg 33) (.const 3))
          (.bin .mul (.const 4) (.reg 34))) (.reg 35))) ;;
        .cond (.reg 36)
          (.assign 37 (.load (.bin .add (.reg 25) (.reg 32))) ;;
           .store (.reg 6) (.reg 35) ;;
           .store (.bin .add (.reg 6) (.const 1)) (.bin .add (.reg 27) (.reg 29)) ;;
           .store (.bin .add (.reg 6) (.const 2)) (.reg 37) ;;
           .store (.bin .add (.reg 25) (.reg 32)) (.reg 6) ;;
           .assign 6 (.bin .add (.reg 6) (.const 3)) ;;
           .assign 37 (.load (.bin .add (.reg 26) (.reg 32))) ;;
           .store (.bin .add (.reg 26) (.reg 32)) (.bin .add (.reg 37) (.const 1)))
          .nop)
       .nop)

lemma bundleStepScanPassCStmt_noRand : bundleStepScanPassCStmt.NoRand := by
  trivial

/-- Heap-allocated singly-linked list of 3-word scanned-end nodes
`[b, packEndKey eCap v key, nextPtr]` whose addresses lie in `[lo, hi)` (`1 ≤ lo`). -/
def ScanNodesAt (eCap : ℕ) (mem : ℕ → ℕ) (lo hi : ℕ) : ℕ → List (ℕ × ℕ × ℕ) → Prop
  | ptr, [] => ptr = 0
  | ptr, (b, v, key) :: rest =>
      lo ≤ ptr ∧ ptr + 3 ≤ hi ∧
      mem ptr = b ∧ mem (ptr + 1) = packEndKey eCap v key ∧
      ScanNodesAt eCap mem lo hi (mem (ptr + 2)) rest

/-- Every 3-word node in the linked list satisfies `P` on its 3 addresses. -/
def ScanNodesIn (mem : ℕ → ℕ) (P : ℕ → Prop) : ℕ → List (ℕ × ℕ × ℕ) → Prop
  | ptr, [] => ptr = 0
  | ptr, _ :: rest =>
      P ptr ∧ P (ptr + 1) ∧ P (ptr + 2) ∧ ScanNodesIn mem P (mem (ptr + 2)) rest

/-- Per-slot scanned-end linked-list invariant: `btCurBunBase[j]` heads `ScanNodesAt` for
`scanEnds j` in `[lo, hi)`, and `btCurTagBase[j] = (scanEnds j).length`. -/
def SlotScanListAt (slotCap eCap tbl : ℕ) (mem : ℕ → ℕ) (lo hi : ℕ)
    (scanEnds : Fin slotCap → List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ j : Fin slotCap,
    ScanNodesAt eCap mem lo hi (mem (btCurBunBase tbl slotCap eCap + j.1)) (scanEnds j) ∧
    mem (btCurTagBase tbl slotCap eCap + j.1) = (scanEnds j).length

/-- Pure Pass C update: prepends `(B.bundleOf x, v, endKey x)` to `scan j` for each `x ∈ xs`
belonging to an active slot `S j = some B` with `B.bundleOf x ∈ candSet j`. -/
noncomputable def addScanEndsForList {slotCap : ℕ} (S : BundleTableState slotCap)
    (candSet : Fin slotCap → Finset ℕ) (v : ℕ) (xs : List End)
    (scan₀ : Fin slotCap → List (ℕ × ℕ × ℕ)) : Fin slotCap → List (ℕ × ℕ × ℕ) :=
  open Classical in
  xs.foldl (fun acc x => fun j =>
    match S j with
    | none => acc j
    | some B =>
      if x.1 ∈ B.edges ∧ B.bundleOf x ∈ candSet j then
        (B.bundleOf x, v, endKey x) :: acc j
      else acc j) scan₀

end

public section

lemma scanNodesAt_mono {eCap lo hi hi' ptr : ℕ} {mem mem' : ℕ → ℕ} {L : List (ℕ × ℕ × ℕ)}
    (h : ScanNodesAt eCap mem lo hi ptr L) (hle : hi ≤ hi')
    (hag : ∀ a, lo ≤ a → a < hi → mem' a = mem a) :
    ScanNodesAt eCap mem' lo hi' ptr L := by
  induction L generalizing ptr with
  | nil => exact h
  | cons t rest ih =>
    rcases t with ⟨b, v, key⟩
    rcases h with ⟨hlo, hhi, h0, h1, hrest⟩
    refine ⟨hlo, by omega, (hag ptr hlo (by omega)).trans h0,
      (hag (ptr + 1) (by omega) (by omega)).trans h1, ?_⟩
    rw [hag (ptr + 2) (by omega) (by omega)]
    exact ih hrest

lemma scanNodesAt_mono_of_in {eCap lo hi hi' ptr : ℕ} {mem mem' : ℕ → ℕ}
    {P Q : ℕ → Prop} {L : List (ℕ × ℕ × ℕ)}
    (h : ScanNodesAt eCap mem lo hi ptr L) (hin : ScanNodesIn mem P ptr L) (hle : hi ≤ hi')
    (hag : ∀ a, lo ≤ a → a < hi → P a → mem' a = mem a)
    (hPQ : ∀ a, lo ≤ a → a < hi → P a → Q a) :
    ScanNodesAt eCap mem' lo hi' ptr L ∧ ScanNodesIn mem' Q ptr L := by
  induction L generalizing ptr with
  | nil => exact ⟨h, hin⟩
  | cons t rest ih =>
    rcases t with ⟨b, v, key⟩
    rcases h with ⟨hlo, hhi, h0, h1, hrest⟩
    rcases hin with ⟨hp0, hp1, hp2, hrin⟩
    have hm2 : mem' (ptr + 2) = mem (ptr + 2) := hag (ptr + 2) (by omega) (by omega) hp2
    obtain ⟨h1', h2'⟩ := ih hrest hrin
    refine ⟨⟨hlo, by omega, (hag ptr hlo (by omega) hp0).trans h0,
      (hag (ptr + 1) (by omega) (by omega) hp1).trans h1, by rw [hm2]; exact h1'⟩,
      ⟨hPQ ptr hlo (by omega) hp0, hPQ (ptr + 1) (by omega) (by omega) hp1,
       hPQ (ptr + 2) (by omega) (by omega) hp2, by rw [hm2]; exact h2'⟩⟩

lemma slotScanListAt_mono {slotCap eCap tbl lo hi hi' : ℕ} {mem mem' : ℕ → ℕ}
    {scanEnds : Fin slotCap → List (ℕ × ℕ × ℕ)}
    (h : SlotScanListAt slotCap eCap tbl mem lo hi scanEnds) (hle : hi ≤ hi')
    (hag_cur : ∀ s < slotCap,
      mem' (btCurBunBase tbl slotCap eCap + s) = mem (btCurBunBase tbl slotCap eCap + s) ∧
      mem' (btCurTagBase tbl slotCap eCap + s) = mem (btCurTagBase tbl slotCap eCap + s))
    (hag_heap : ∀ a, lo ≤ a → a < hi → mem' a = mem a) :
    SlotScanListAt slotCap eCap tbl mem' lo hi' scanEnds := fun j => by
  obtain ⟨hnd, hcnt⟩ := h j
  obtain ⟨hcb, hct⟩ := hag_cur j.1 j.2
  rw [hcb, hct]
  exact ⟨scanNodesAt_mono hnd hle hag_heap, hcnt⟩

lemma slotScanListAt_empty {slotCap eCap tbl lo hi : ℕ} {mem : ℕ → ℕ}
    (hzero : ∀ s < slotCap,
      mem (btCurBunBase tbl slotCap eCap + s) = 0 ∧
      mem (btCurTagBase tbl slotCap eCap + s) = 0) :
    SlotScanListAt slotCap eCap tbl mem lo hi (fun _ => []) := fun j => by
  obtain ⟨h1, h2⟩ := hzero j.1 j.2
  exact ⟨h1, h2⟩

lemma addScanEndsForList_nil {slotCap : ℕ} (S : BundleTableState slotCap)
    (candSet : Fin slotCap → Finset ℕ) (v : ℕ) (scan₀ : Fin slotCap → List (ℕ × ℕ × ℕ)) :
    addScanEndsForList S candSet v [] scan₀ = scan₀ := rfl

lemma addScanEndsForList_take_succ {slotCap : ℕ} (S : BundleTableState slotCap)
    (candSet : Fin slotCap → Finset ℕ) (v : ℕ) (xs : List End)
    (scan₀ : Fin slotCap → List (ℕ × ℕ × ℕ)) {i : ℕ} (hi : i < xs.length) :
    addScanEndsForList S candSet v (xs.take (i + 1)) scan₀ =
      fun j =>
        let prev := addScanEndsForList S candSet v (xs.take i) scan₀ j
        match S j with
        | none => prev
        | some B =>
          open Classical in
          if (xs[i]'hi).1 ∈ B.edges ∧ B.bundleOf (xs[i]'hi) ∈ candSet j then
            (B.bundleOf (xs[i]'hi), v, endKey (xs[i]'hi)) :: prev
          else prev := by
  unfold addScanEndsForList
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma addScanEndsForList_mem_iff {slotCap : ℕ} {S : BundleTableState slotCap}
    {candSet : Fin slotCap → Finset ℕ} {v : ℕ} {xs : List End}
    {scan₀ : Fin slotCap → List (ℕ × ℕ × ℕ)} {j : Fin slotCap} {b w k : ℕ} :
    (b, w, k) ∈ addScanEndsForList S candSet v xs scan₀ j ↔
      (b, w, k) ∈ scan₀ j ∨
        ∃ B, S j = some B ∧ w = v ∧ ∃ x ∈ xs, x ∈ B.ends b ∧ b ∈ candSet j ∧ endKey x = k := by
  induction xs generalizing scan₀ with
  | nil => simp [addScanEndsForList]
  | cons x rest ih =>
    simp only [addScanEndsForList, List.foldl_cons] at ih ⊢
    rw [ih]
    constructor
    · rintro (hhead | ⟨B, hSj, rfl, y, hy, hyB, hbc, rfl⟩)
      · cases hSj : S j with
        | none => simp only [hSj] at hhead; exact Or.inl hhead
        | some B =>
          simp only [hSj] at hhead
          split_ifs at hhead with hcond
          · rcases List.mem_cons.mp hhead with heq | hmem
            · obtain ⟨hb, hwk⟩ := Prod.mk.inj heq
              obtain ⟨hw, hk⟩ := Prod.mk.inj hwk
              exact Or.inr ⟨B, rfl, hw, x, List.mem_cons_self,
                (BundleState.mem_ends B b x).mpr ⟨hcond.1, hb.symm⟩, hb ▸ hcond.2, hk.symm⟩
            · exact Or.inl hmem
          · exact Or.inl hhead
      · exact Or.inr ⟨B, hSj, rfl, y, List.mem_cons_of_mem _ hy, hyB, hbc, rfl⟩
    · rintro (h0 | ⟨B, hSj, rfl, y, hy, hyB, hbc, rfl⟩)
      · left
        cases hSj : S j with
        | none => exact h0
        | some B =>
          dsimp only
          split_ifs
          · exact List.mem_cons_of_mem _ h0
          · exact h0
      · rcases List.mem_cons.mp hy with rfl | hy'
        · left
          have hxy := (BundleState.mem_ends B b y).mp hyB
          simp only [hSj]
          have hcond : y.1 ∈ B.edges ∧ B.bundleOf y ∈ candSet j := ⟨hxy.1, hxy.2.symm ▸ hbc⟩
          rw [ite_eq_left hcond]
          simp [hxy.2]
        · exact Or.inr ⟨B, hSj, rfl, y, hy', hyB, hbc, rfl⟩

lemma addScanEndsForList_sum_le {slotCap : ℕ} {S : BundleTableState slotCap}
    (hdisj : ∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ B₁ B₂,
      S j₁ = some B₁ → S j₂ = some B₂ → Disjoint B₁.edges B₂.edges)
    (candSet : Fin slotCap → Finset ℕ) (v : ℕ) (xs : List End)
    (scan₀ : Fin slotCap → List (ℕ × ℕ × ℕ)) :
    (∑ j : Fin slotCap, (addScanEndsForList S candSet v xs scan₀ j).length) ≤
      (∑ j : Fin slotCap, (scan₀ j).length) + xs.length := by
  classical
  induction xs generalizing scan₀ with
  | nil => simp [addScanEndsForList]
  | cons x rest ih =>
    simp only [addScanEndsForList, List.foldl_cons, List.length_cons]
    set scan1 : Fin slotCap → List (ℕ × ℕ × ℕ) := fun j =>
      match S j with
      | none => scan₀ j
      | some B =>
        if x.1 ∈ B.edges ∧ B.bundleOf x ∈ candSet j then
          (B.bundleOf x, v, endKey x) :: scan₀ j
        else scan₀ j
    have hstep : (∑ j : Fin slotCap, (scan1 j).length) ≤ (∑ j : Fin slotCap, (scan₀ j).length) + 1 := by
      by_cases hex : ∃ j₀ : Fin slotCap, ∃ B₀, S j₀ = some B₀ ∧ x.1 ∈ B₀.edges
      · obtain ⟨j₀, B₀, hSj₀, hx₀⟩ := hex
        have hoth : ∀ j : Fin slotCap, j ≠ j₀ → (scan1 j).length = (scan₀ j).length := by
          intro j hne
          dsimp only [scan1]
          cases hSj : S j with
          | none => rfl
          | some B =>
            have hnot : x.1 ∉ B.edges := fun hx =>
              Finset.disjoint_left.mp (hdisj j j₀ hne B B₀ hSj hSj₀) hx hx₀
            simp [hnot]
        have hj₀ : (scan1 j₀).length ≤ (scan₀ j₀).length + 1 := by
          dsimp only [scan1]; simp only [hSj₀]; split_ifs <;> simp
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀),
          ← Finset.add_sum_erase _ (fun j => (scan₀ j).length) (Finset.mem_univ j₀)]
        have hsum_eq : (∑ j ∈ Finset.univ.erase j₀, (scan1 j).length) =
            ∑ j ∈ Finset.univ.erase j₀, (scan₀ j).length :=
          Finset.sum_congr rfl fun j hj => hoth j (Finset.mem_erase.mp hj).1
        rw [hsum_eq]; omega
      · have hall : ∀ j : Fin slotCap, (scan1 j).length = (scan₀ j).length := by
          intro j; dsimp only [scan1]
          cases hSj : S j with
          | none => rfl
          | some B =>
            have hnot : x.1 ∉ B.edges := fun hx => hex ⟨j, B, hSj, hx⟩
            simp [hnot]
        rw [Finset.sum_congr rfl fun j _ => hall j]; omega
    exact (ih scan1).trans (by omega)

end

end MinCostFlow.SparseCore.Program
