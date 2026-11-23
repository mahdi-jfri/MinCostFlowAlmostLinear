module

public import MinCostFlow.MinRatio.WireSelectHeapSiftDown
import WordRAM.Tactic

/-!
# Per-level candidate list ops and heap-mutation lemmas for the select-heap

Implements the O(1) doubly-linked list procedures operating on `SelectHeapLoc`'s per-level
candidate lists (`candHead[0..d]`, `candPrev[0..cap)`, `candNext[0..cap)`):
- `candListConsBody` (`[hb, lvl, e]`): prepends `e` to level `lvl`'s candidate list.
- `candListEraseBody` (`[hb, lvl, e]`): removes `e` from level `lvl`'s candidate list.

Also proves the pure structural lemmas for the three select-heap mutations (`insert`, `replaceKey`,
`deleteSwapLast`), reducing restoration of `SelectHeapOrder` to a single `siftUp` or `siftDown`
call.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

/-! ## 1. Per-level candidate list procedures (`cons` and `erase`) -/

/-- Prepend edge `e` to level `lvl`'s 1-indexed doubly-linked candidate list.
Arguments: `[hb, lvl, e]`. -/
def candListConsBody : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const shCandHeadOff))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const shCandPrevOff))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const shCandNextOff))) ;;
  .assign 6 (.load (.bin .add (.reg 3) (.reg 1))) ;;
  .store (.bin .add (.reg 4) (.reg 2)) (.const 0) ;;
  .store (.bin .add (.reg 5) (.reg 2)) (.reg 6) ;;
  .cond (.reg 6)
    (.store (.bin .add (.reg 4) (.bin .sub (.reg 6) (.const 1))) (.bin .add (.reg 2) (.const 1)))
    .nop ;;
  .store (.bin .add (.reg 3) (.reg 1)) (.bin .add (.reg 2) (.const 1)) ;;
  .ret (.const 0)

theorem candListConsBody_noRand : candListConsBody.NoRand := by
  simp [candListConsBody, Stmt.NoRand]

/-- Erase edge `e` from level `lvl`'s 1-indexed doubly-linked candidate list.
Arguments: `[hb, lvl, e]`. -/
def candListEraseBody : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const shCandHeadOff))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const shCandPrevOff))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const shCandNextOff))) ;;
  .assign 6 (.load (.bin .add (.reg 4) (.reg 2))) ;;
  .assign 7 (.load (.bin .add (.reg 5) (.reg 2))) ;;
  .cond (.reg 6)
    (.store (.bin .add (.reg 5) (.bin .sub (.reg 6) (.const 1))) (.reg 7))
    (.store (.bin .add (.reg 3) (.reg 1)) (.reg 7)) ;;
  .cond (.reg 7)
    (.store (.bin .add (.reg 4) (.bin .sub (.reg 7) (.const 1))) (.reg 6))
    .nop ;;
  .store (.bin .add (.reg 4) (.reg 2)) (.const 0) ;;
  .store (.bin .add (.reg 5) (.reg 2)) (.const 0) ;;
  .ret (.const 0)

theorem candListEraseBody_noRand : candListEraseBody.NoRand := by
  simp [candListEraseBody, Stmt.NoRand]

/-- Contract for `candListConsBody`: prepends `e` to `lists lvl`, preserving all other lists and
all memory outside `[loc.candHead, loc.numBase)`. -/
def candListConsContract (w : ℕ) (loc : SelectHeapLoc) (size : ℕ)
    (lists : ℕ → List ℕ) : Contract where
  pre args mem :=
    ∃ lvl e, args = [loc.hb, lvl, e] ∧
      16 < 2 ^ w ∧ loc.endAddr < 2 ^ w ∧
      lvl ≤ loc.d ∧ e < loc.cap ∧
      SelectHeapHeaderAt mem loc size ∧
      (∀ i ≤ loc.d, IsDoublyLinkedList mem loc.candPrev loc.candNext (loc.candHead + i) loc.cap (lists i)) ∧
      (∀ i ≤ loc.d, e ∉ lists i) ∧
      (∀ i j, i ≤ loc.d → j ≤ loc.d → i ≠ j → ∀ x, x ∈ lists i → x ∉ lists j)
  post args mem ret mem' :=
    let lvl := args.getD 1 0
    let e := args.getD 2 0
    ret = 0 ∧
    (∀ i ≤ loc.d, IsDoublyLinkedList mem' loc.candPrev loc.candNext (loc.candHead + i) loc.cap
      (if i = lvl then e :: lists i else lists i)) ∧
    (∀ a, (a < loc.candHead ∨ loc.numBase ≤ a) → mem' a = mem a)
  cost _ _ := 85

/-- Contract for `candListEraseBody`: removes `e` from `lists lvl`, preserving all other lists and
all memory outside `[loc.candHead, loc.numBase)`. -/
def candListEraseContract (w : ℕ) (loc : SelectHeapLoc) (size : ℕ)
    (lists : ℕ → List ℕ) : Contract where
  pre args mem :=
    ∃ lvl e, args = [loc.hb, lvl, e] ∧
      16 < 2 ^ w ∧ loc.endAddr < 2 ^ w ∧
      lvl ≤ loc.d ∧ e < loc.cap ∧ e ∈ lists lvl ∧
      SelectHeapHeaderAt mem loc size ∧
      (∀ i ≤ loc.d, IsDoublyLinkedList mem loc.candPrev loc.candNext (loc.candHead + i) loc.cap (lists i)) ∧
      (∀ i j, i ≤ loc.d → j ≤ loc.d → i ≠ j → ∀ x, x ∈ lists i → x ∉ lists j)
  post args mem ret mem' :=
    let lvl := args.getD 1 0
    let e := args.getD 2 0
    ret = 0 ∧
    (∀ i ≤ loc.d, IsDoublyLinkedList mem' loc.candPrev loc.candNext (loc.candHead + i) loc.cap
      (if i = lvl then (lists i).erase e else lists i)) ∧
    (∀ a, (a < loc.candHead ∨ loc.numBase ≤ a) → mem' a = mem a)
  cost _ _ := 110

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

private lemma selectHeap_cand_header_reads {mem : ℕ → ℕ} {loc : SelectHeapLoc} {size : ℕ}
    (hhdr : SelectHeapHeaderAt mem loc size) :
    mem (loc.hb + 9) = loc.candHead ∧
    mem (loc.hb + 10) = loc.candPrev ∧
    mem (loc.hb + 11) = loc.candNext :=
  ⟨by simpa using hhdr 9 (by simp),
   by simpa using hhdr 10 (by simp),
   by simpa using hhdr 11 (by simp)⟩

private lemma selectHeap_cand_bounds {loc : SelectHeapLoc} :
    loc.hb + 14 ≤ loc.candHead ∧
    loc.candHead + (loc.d + 1) = loc.candPrev ∧
    loc.candPrev + loc.cap = loc.candNext ∧
    loc.candNext + loc.cap = loc.numBase ∧
    loc.numBase ≤ loc.endAddr := by
  have heq := loc.endAddr_eq
  unfold SelectHeapLoc.numBase SelectHeapLoc.candNext SelectHeapLoc.candPrev SelectHeapLoc.candHead
    SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize at *
  omega

/-- `candListConsBody` meets `candListConsContract` in at most 85 steps. -/
theorem candListCons_meetsContract {w proc : ℕ} {loc : SelectHeapLoc} {size : ℕ}
    {lists : ℕ → List ℕ} {p : Program}
    (hp : p.procs[proc]? = some candListConsBody) :
    MeetsContract w p proc (candListConsContract w loc size lists) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨lvl, e, rfl, hw16, hendW, hlvl, he, hhdr, hdlls, heNot, hdisj⟩ := hpre
  have hcb := selectHeap_cand_bounds (loc := loc)
  have hhr := selectHeap_cand_header_reads hhdr
  have hw1 : 1 < 2 ^ w := by omega
  have hhbw : loc.hb < 2 ^ w := hwords loc.hb (by simp)
  have hlvlw : lvl < 2 ^ w := hwords lvl (by simp)
  have hew : e < 2 ^ w := hwords e (by simp)
  have hchW : loc.candHead < 2 ^ w := by omega
  have hcpW : loc.candPrev < 2 ^ w := by omega
  have hcnW : loc.candNext < 2 ^ w := by omega
  have hL := hdlls lvl hlvl
  let oldHead := mem (loc.candHead + lvl)
  have holdW : oldHead < 2 ^ w := by
    cases hLcases : lists lvl with
    | nil =>
      have h0 : oldHead = 0 := by simpa [oldHead, hLcases] using hL.2.2.1
      omega
    | cons h0 xs =>
      have hval : oldHead = h0 + 1 := by simpa [oldHead, hLcases] using hL.2.2.1
      have hh0 : h0 < loc.cap := hL.2.1 h0 (by simp [hLcases])
      omega
  apply runs_start_le
  dsimp only [startState]
  unfold candListConsBody
  simp only [shCandHeadOff, shCandPrevOff, shCandNextOff]
  refine runs_seq_assign_flat (v := loc.candHead) (by eval_expr; exact hhr.1) ?_
  refine runs_seq_assign_flat (v := loc.candPrev) (by eval_expr; exact hhr.2.1) ?_
  refine runs_seq_assign_flat (v := loc.candNext) (by eval_expr; exact hhr.2.2) ?_
  refine runs_seq_assign_flat (v := oldHead) (by eval_expr) ?_
  refine runs_seq_store_flat (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (by eval_expr) (by eval_expr) ?_
  -- Branch on `oldHead ≠ 0`
  by_cases hoh : oldHead = 0
  · have hLnil : lists lvl = [] := (hL.head_eq_zero_iff).mp hoh
    refine runs_seq_cond_le (v := 0) (by eval_expr) (fun h => absurd rfl h) ?_
    intro _
    refine runs_seq_nop_le ?_
    refine runs_seq_store_flat (by eval_expr) (by eval_expr) ?_
    refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
    · dsimp only [candListConsContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
      refine ⟨trivial, fun i hi => ?_, fun a ha => ?_⟩
      · by_cases hil : i = lvl
        · subst i
          simp only [↓reduceIte]
          refine hL.cons he (heNot _ hi) (by simp)
            (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self])
            (by rw [Function.update_of_ne (by omega), Function.update_self])
            (fun _ _ hEq => by rw [hLnil] at hEq; cases hEq)
            (fun _ hy _ => by rw [hLnil] at hy; simp at hy)
            (fun _ hy => by rw [hLnil] at hy; simp at hy)
        · simp only [hil, ↓reduceIte]
          refine (hdlls i hi).of_agree
            (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
            (fun y hy => by
              have hye : y ≠ e := fun h => heNot i hi (h ▸ hy)
              have hyCap : y < loc.cap := (hdlls i hi).2.1 y hy
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
            (fun y hy => by
              have hye : y ≠ e := fun h => heNot i hi (h ▸ hy)
              have hyCap : y < loc.cap := (hdlls i hi).2.1 y hy
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · simp only [candListConsContract, Expr.size]; omega
  · -- `oldHead ≠ 0`, so `lists lvl = h0 :: xs` and `oldHead = h0 + 1`
    cases hLcases : lists lvl with
    | nil =>
      have h0 : oldHead = 0 := by simpa [oldHead, hLcases] using hL.2.2.1
      exact (hoh h0).elim
    | cons h0 xs =>
      have hval : oldHead = h0 + 1 := by simpa [oldHead, hLcases] using hL.2.2.1
      have hh0 : h0 < loc.cap := hL.2.1 h0 (by simp [hLcases])
      have hh0e : h0 ≠ e := fun h => heNot lvl hlvl (by simp [hLcases, h])
      refine runs_seq_cond_le (v := oldHead) (by eval_expr) ?_ (fun h => absurd h hoh)
      intro _
      refine runs_seq_store_flat (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_flat (by eval_expr) (by eval_expr) ?_
      refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
      · dsimp only [candListConsContract]
        simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
        refine ⟨trivial, fun i hi => ?_, fun a ha => ?_⟩
        · by_cases hil : i = lvl
          · subst i
            simp only [↓reduceIte]
            refine hL.cons he (heNot _ hi) (by simp)
              (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega), Function.update_self])
              (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self])
              (fun h0' xs' hEq => by
                rw [hLcases] at hEq; injection hEq with hh' _
                subst hh'
                rw [Function.update_of_ne (by omega), hval]; simp)
              (fun y hy hne => by
                have hy0 : y ≠ h0 := fun h => hne xs (by rw [hLcases, h])
                have hye : y ≠ e := fun h => heNot _ hi (h ▸ hy)
                have hyCap : y < loc.cap := (hdlls _ hi).2.1 y hy
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                    Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
              (fun y hy => by
                have hye : y ≠ e := fun h => heNot _ hi (h ▸ hy)
                have hyCap : y < loc.cap := (hdlls _ hi).2.1 y hy
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                    Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
          · simp only [hil, ↓reduceIte]
            refine (hdlls i hi).of_agree
              (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
              (fun y hy => by
                have hye : y ≠ e := fun h => heNot i hi (h ▸ hy)
                have hy0 : y ≠ h0 := fun h => hdisj lvl i hlvl hi (Ne.symm hil) h0 (by simp [hLcases]) (h ▸ hy)
                have hyCap : y < loc.cap := (hdlls i hi).2.1 y hy
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                    Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
              (fun y hy => by
                have hye : y ≠ e := fun h => heNot i hi (h ▸ hy)
                have hyCap : y < loc.cap := (hdlls i hi).2.1 y hy
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                    Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · simp only [candListConsContract, Expr.size]; omega

/-- `candListEraseBody` meets `candListEraseContract` in at most 110 steps. -/
theorem candListErase_meetsContract {w proc : ℕ} {loc : SelectHeapLoc} {size : ℕ}
    {lists : ℕ → List ℕ} {p : Program}
    (hp : p.procs[proc]? = some candListEraseBody) :
    MeetsContract w p proc (candListEraseContract w loc size lists) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨lvl, e, rfl, hw16, hendW, hlvl, he, heMem, hhdr, hdlls, hdisj⟩ := hpre
  have hcb := selectHeap_cand_bounds (loc := loc)
  have hhr := selectHeap_cand_header_reads hhdr
  have hw1 : 1 < 2 ^ w := by omega
  have hhbw : loc.hb < 2 ^ w := hwords loc.hb (by simp)
  have hlvlw : lvl < 2 ^ w := hwords lvl (by simp)
  have hew : e < 2 ^ w := hwords e (by simp)
  have hchW : loc.candHead < 2 ^ w := by omega
  have hcpW : loc.candPrev < 2 ^ w := by omega
  have hcnW : loc.candNext < 2 ^ w := by omega
  have hL := hdlls lvl hlvl
  obtain ⟨k, hk, hLk⟩ := List.getElem_of_mem heMem
  have hidx : (lists lvl).idxOf e = k := by rw [← hLk]; exact hL.1.idxOf_getElem k hk
  have hp_k := (hL.2.2.2 k hk).1
  have hn_k := (hL.2.2.2 k hk).2
  rw [hLk] at hp_k hn_k
  let pv := mem (loc.candPrev + e)
  let nv := mem (loc.candNext + e)
  have hpvLe : pv ≤ loc.cap := by
    dsimp only [pv]; rw [hp_k]
    split_ifs with h0
    · omega
    · have : (lists lvl)[k - 1]'(by omega) < loc.cap := hL.2.1 _ (List.getElem_mem (by omega))
      omega
  have hnvLe : nv ≤ loc.cap := by
    dsimp only [nv]; rw [hn_k]
    split_ifs with h1
    · omega
    · have hk1 : k + 1 < (lists lvl).length := by omega
      have hlt : (lists lvl)[k + 1]'hk1 < loc.cap := hL.2.1 _ (List.getElem_mem hk1)
      rw [List.getD_eq_getElem _ _ hk1]; omega
  have hpvW : pv < 2 ^ w := by omega
  have hnvW : nv < 2 ^ w := by omega
  -- Helper to verify final memory after the 4 conditional/unconditional stores
  have hfinish : ∀ (memF : ℕ → ℕ),
      (∀ a, (a < loc.candHead ∨ loc.numBase ≤ a) → memF a = mem a) →
      (∀ i ≤ loc.d, i ≠ lvl → memF (loc.candHead + i) = mem (loc.candHead + i)) →
      (memF (loc.candHead + lvl) = if pv = 0 then nv else mem (loc.candHead + lvl)) →
      (∀ y < loc.cap, y ≠ e →
        memF (loc.candPrev + y) = if nv ≠ 0 ∧ y = nv - 1 then pv else mem (loc.candPrev + y)) →
      (∀ y < loc.cap, y ≠ e →
        memF (loc.candNext + y) = if pv ≠ 0 ∧ y = pv - 1 then nv else mem (loc.candNext + y)) →
      (∀ i ≤ loc.d, IsDoublyLinkedList memF loc.candPrev loc.candNext (loc.candHead + i) loc.cap
        (if i = lvl then (lists i).erase e else lists i)) ∧
      (∀ a, (a < loc.candHead ∨ loc.numBase ≤ a) → memF a = mem a) := by
    intro memF hout hheadOther hheadLvl hprevY hnextY
    refine ⟨fun i hi => ?_, hout⟩
    by_cases hil : i = lvl
    · subst i
      simp only [↓reduceIte]
      refine hL.erase heMem (fun _ _ => hheadLvl) (fun hEr => ?_) ?_ ?_ ?_ ?_
      · have hlen1 : (lists lvl).length = 1 := by
          have := List.length_erase_of_mem heMem; rw [hEr] at this; simp at this; omega
        have hk0 : k = 0 := by omega
        have hpv0 : pv = 0 := by dsimp only [pv]; rw [hp_k, ite_eq_left hk0]
        have hnv0 : nv = 0 := by dsimp only [nv]; rw [hn_k, ite_eq_left (by omega)]
        rw [hheadLvl, ite_eq_left hpv0, hnv0]
      · intro y hy hne
        have hyL := List.mem_of_mem_erase hy
        have hye : y ≠ e := fun h => by
          have hnd := hL.1
          have := (List.nodup_iff_count_le_one.mp hnd) e
          rw [h] at hy
          have hcnt : List.count e ((lists lvl).erase e) = List.count e (lists lvl) - 1 :=
            List.count_erase_self
          have hpos : 0 < List.count e ((lists lvl).erase e) := List.count_pos_iff.mpr hy
          omega
        rw [hprevY y (hL.2.1 y hyL) hye, ite_eq_right]
        rintro ⟨hnv0, rfl⟩
        rw [hidx] at hne
        dsimp only [nv] at hnv0 hne
        rw [hn_k] at hnv0 hne
        split_ifs at hnv0 with hk1
        · exact hnv0 rfl
        · have hk1lt : k + 1 < (lists lvl).length := by omega
          simp only [hk1lt, ↓reduceDIte] at hne
          rw [ite_eq_right hk1, List.getD_eq_getElem _ _ hk1lt] at hne
          exact hne (by omega)
      · intro k' hk' hLk'
        have hkEq : k' = k := hL.1.getElem_inj_iff.mp (hLk'.trans hLk.symm)
        subst k'
        have hne1 : (lists lvl)[k + 1] ≠ e := fun h => by
          have := hL.1.getElem_inj_iff.mp (h.trans hLk.symm); omega
        have hnvEq : nv = (lists lvl)[k + 1] + 1 := by
          dsimp only [nv]; rw [hn_k, ite_eq_right (by omega), List.getD_eq_getElem _ _ hk']
        rw [hprevY _ (hL.2.1 _ (List.getElem_mem hk')) hne1, ite_eq_left ⟨by omega, by omega⟩]
      · intro y hy hne
        have hyL := List.mem_of_mem_erase hy
        have hye : y ≠ e := fun h => by
          have hnd := hL.1
          have := (List.nodup_iff_count_le_one.mp hnd) e
          rw [h] at hy
          have hcnt : List.count e ((lists lvl).erase e) = List.count e (lists lvl) - 1 :=
            List.count_erase_self
          have hpos : 0 < List.count e ((lists lvl).erase e) := List.count_pos_iff.mpr hy
          omega
        rw [hnextY y (hL.2.1 y hyL) hye, ite_eq_right]
        rintro ⟨hpv0, rfl⟩
        rw [hidx] at hne
        dsimp only [pv] at hpv0 hne
        rw [hp_k] at hpv0 hne
        split_ifs at hpv0 with hk0
        · exact hpv0 rfl
        · have hk0lt : k - 1 < (lists lvl).length := by omega
          simp only [hk0, ↓reduceIte] at hne
          simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk0lt,
            Option.getD_some] at hne
          exact hne (by omega)
      · intro k' hk' hk'pos hLk'
        have hkEq : k' = k := hL.1.getElem_inj_iff.mp (hLk'.trans hLk.symm)
        subst k'
        have hk1lt : k - 1 < (lists lvl).length := by omega
        have hne1 : (lists lvl)[k - 1] ≠ e := fun h => by
          have := hL.1.getElem_inj_iff.mp (h.trans hLk.symm); omega
        have hpvEq : pv = (lists lvl)[k - 1] + 1 := by
          dsimp only [pv]; rw [hp_k, ite_eq_right (by omega)]
        rw [hnextY _ (hL.2.1 _ (List.getElem_mem hk1lt)) hne1, ite_eq_left ⟨by omega, by omega⟩]
    · simp only [hil, ↓reduceIte]
      have hnotLvl (y : ℕ) (hy : y ∈ lists i) : y ∉ lists lvl := fun h =>
        hdisj i lvl hi hlvl hil y hy h
      refine (hdlls i hi).of_agree (hheadOther i hi hil) (fun y hy => ?_) (fun y hy => ?_)
      · have hye : y ≠ e := fun h => hnotLvl y hy (h ▸ heMem)
        rw [hprevY y ((hdlls i hi).2.1 y hy) hye, ite_eq_right]
        rintro ⟨hnv0, rfl⟩
        dsimp only [nv] at hnv0 hy
        rw [hn_k] at hnv0 hy
        split_ifs at hnv0 with hk1
        · exact hnv0 rfl
        · have hk1lt : k + 1 < (lists lvl).length := by omega
          have hmem : nv - 1 ∈ lists lvl := by
            dsimp only [nv]; rw [hn_k, ite_eq_right hk1, List.getD_eq_getElem _ _ hk1lt]
            simp
          exact hnotLvl (nv - 1) (by dsimp only [nv]; rw [hn_k]; exact hy) hmem
      · have hye : y ≠ e := fun h => hnotLvl y hy (h ▸ heMem)
        rw [hnextY y ((hdlls i hi).2.1 y hy) hye, ite_eq_right]
        rintro ⟨hpv0, rfl⟩
        dsimp only [pv] at hpv0 hy
        rw [hp_k] at hpv0 hy
        split_ifs at hpv0 with hk0
        · exact hpv0 rfl
        · have hk1lt : k - 1 < (lists lvl).length := by omega
          have hmem : pv - 1 ∈ lists lvl := by
            dsimp only [pv]; rw [hp_k, ite_eq_right hk0]
            simp
          exact hnotLvl (pv - 1) (by dsimp only [pv]; rw [hp_k]; exact hy) hmem
  apply runs_start_le
  dsimp only [startState]
  unfold candListEraseBody
  simp only [shCandHeadOff, shCandPrevOff, shCandNextOff]
  refine runs_seq_assign_flat (v := loc.candHead) (by eval_expr; exact hhr.1) ?_
  refine runs_seq_assign_flat (v := loc.candPrev) (by eval_expr; exact hhr.2.1) ?_
  refine runs_seq_assign_flat (v := loc.candNext) (by eval_expr; exact hhr.2.2) ?_
  refine runs_seq_assign_flat (v := pv) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := nv) (by eval_expr) ?_
  -- First branch on `pv ≠ 0`, then on `nv ≠ 0`
  have htail : ∀ (mem1 : ℕ → ℕ) (regs1 : ℕ → ℕ) (k0 : ℕ),
      regs1 2 = e → regs1 4 = loc.candPrev → regs1 5 = loc.candNext →
      regs1 6 = pv → regs1 7 = nv →
      (∀ a, (a < loc.candHead ∨ loc.numBase ≤ a) → mem1 a = mem a) →
      (∀ i ≤ loc.d, i ≠ lvl → mem1 (loc.candHead + i) = mem (loc.candHead + i)) →
      (mem1 (loc.candHead + lvl) = if pv = 0 then nv else mem (loc.candHead + lvl)) →
      (∀ y < loc.cap, mem1 (loc.candPrev + y) = mem (loc.candPrev + y)) →
      (∀ y < loc.cap, y ≠ e →
        mem1 (loc.candNext + y) = if pv ≠ 0 ∧ y = pv - 1 then nv else mem (loc.candNext + y)) →
      k0 + 50 ≤ 110 →
      ∃ o st' c, Runs w p ω
        (.cond (.reg 7)
          (.store (.bin .add (.reg 4) (.bin .sub (.reg 7) (.const 1))) (.reg 6))
          .nop ;;
         .store (.bin .add (.reg 4) (.reg 2)) (.const 0) ;;
         .store (.bin .add (.reg 5) (.reg 2)) (.const 0) ;;
         .ret (.const 0))
        ⟨mem1, regs1, pos⟩ o st' c ∧
        (candListEraseContract w loc size lists).post [loc.hb, lvl, e] mem o.value st'.mem ∧
        k0 + c ≤ (candListEraseContract w loc size lists).cost [loc.hb, lvl, e] mem := by
    intro mem1 regs1 k0 hr2 hr4 hr5 hr6 hr7 hout1 hho1 hhl1 hp1 hn1 hk0
    by_cases hnv0 : nv = 0
    · refine runs_seq_cond_le (v := 0) (by simp [Expr.eval, hr7, hnv0]) (fun h => absurd rfl h) ?_
      intro _
      refine runs_seq_nop_le ?_
      refine runs_seq_store_flat (x := loc.candPrev + e) (v := 0)
        (by simp [Expr.eval, BinOp.eval, hr4, hr2, show loc.candPrev + e < 2 ^ w by omega])
        (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_
      refine runs_seq_store_flat (x := loc.candNext + e) (v := 0)
        (by simp [Expr.eval, BinOp.eval, hr5, hr2, show loc.candNext + e < 2 ^ w by omega])
        (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_
      refine runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_ ?_
      · dsimp only [candListEraseContract]
        simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
        refine ⟨trivial, hfinish _ ?_ ?_ ?_ ?_ ?_⟩
        · intro a ha
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hout1 a ha
        · intro i hi hil
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hho1 i hi hil
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hhl1
        · intro y hy hye
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), ite_eq_right (by simp [hnv0])]
          exact hp1 y hy
        · intro y hy hye
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hn1 y hy hye
      · simp only [candListEraseContract, Expr.size]; omega
    · refine runs_seq_cond_le (v := nv) (by simp [Expr.eval, hr7]) ?_ (fun h => absurd h hnv0)
      intro _
      refine runs_seq_store_flat (x := loc.candPrev + (nv - 1)) (v := pv)
        (by simp [Expr.eval, BinOp.eval, hr4, hr7, hw1, show nv - 1 < 2 ^ w by omega,
            show loc.candPrev + (nv - 1) < 2 ^ w by omega])
        (by simp [Expr.eval, hr6]) ?_
      refine runs_seq_store_flat (x := loc.candPrev + e) (v := 0)
        (by simp [Expr.eval, BinOp.eval, hr4, hr2, show loc.candPrev + e < 2 ^ w by omega])
        (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_
      refine runs_seq_store_flat (x := loc.candNext + e) (v := 0)
        (by simp [Expr.eval, BinOp.eval, hr5, hr2, show loc.candNext + e < 2 ^ w by omega])
        (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_
      refine runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_ ?_
      · dsimp only [candListEraseContract]
        simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
        refine ⟨trivial, hfinish _ ?_ ?_ ?_ ?_ ?_⟩
        · intro a ha
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]; exact hout1 a ha
        · intro i hi hil
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]; exact hho1 i hi hil
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]; exact hhl1
        · intro y hy hye
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          by_cases hyn : y = nv - 1
          · subst hyn; simp [hnv0]
          · rw [Function.update_of_ne (by omega), ite_eq_right (by simp [hyn])]; exact hp1 y hy
        · intro y hy hye
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]; exact hn1 y hy hye
      · simp only [candListEraseContract, Expr.size]; omega
  by_cases hpv0 : pv = 0
  · refine runs_seq_cond_le (v := 0) (by eval_expr) (fun h => absurd rfl h) ?_
    intro _
    refine runs_seq_store_flat (x := loc.candHead + lvl) (v := nv) (by eval_expr) (by eval_expr) ?_
    apply htail
    · simp
    · simp
    · simp
    · simp
    · simp
    · intro a ha; exact Function.update_of_ne (by omega) ..
    · intro i hi hil; exact Function.update_of_ne (by omega) ..
    · simp [hpv0]
    · intro y hy; exact Function.update_of_ne (by omega) ..
    · intro y hy _
      simp only [hpv0, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      exact Function.update_of_ne (by omega) ..
    · simp only [Expr.size]; omega
  · refine runs_seq_cond_le (v := pv) (by eval_expr) ?_ (fun h => absurd h hpv0)
    intro _
    refine runs_seq_store_flat (x := loc.candNext + (pv - 1)) (v := nv) (by eval_expr) (by eval_expr) ?_
    apply htail
    · simp
    · simp
    · simp
    · simp
    · simp
    · intro a ha; exact Function.update_of_ne (by omega) ..
    · intro i hi hil; exact Function.update_of_ne (by omega) ..
    · rw [ite_eq_right hpv0]; exact Function.update_of_ne (by omega) ..
    · intro y hy; exact Function.update_of_ne (by omega) ..
    · intro y hy _
      by_cases hyp : y = pv - 1
      · subst hyp; simp [hpv0]
      · simp only [hyp, and_false, ↓reduceIte]
        exact Function.update_of_ne (by omega) ..
    · simp only [Expr.size]; omega

/-! ## 2. Pure heap-order restoration lemmas for insert, replace, and delete -/

/-- After appending a new edge `e` at slot `size` of a valid heap of size `size`,
`SelectHeapOrderExceptUp` holds at position `size`. -/
theorem selectHeap_exceptUp_of_append {mem mem' : ℕ → ℕ} {loc : SelectHeapLoc} {h size : ℕ}
    (_hbij : SelectHeapBijection mem loc size)
    (hord : SelectHeapOrder mem loc h size)
    (harr : ∀ p < size, mem' (loc.arrPtr + p) = mem (loc.arrPtr + p))
    (hkey : ∀ p < size, ∀ q < size,
      loc.edgeBetter mem' h (mem (loc.arrPtr + p)) (mem (loc.arrPtr + q)) =
        loc.edgeBetter mem h (mem (loc.arrPtr + p)) (mem (loc.arrPtr + q))) :
    SelectHeapOrderExceptUp mem' loc h (size + 1) size := by
  refine ⟨Nat.lt_succ_self size, fun p hp0 hp hps => ?_, fun _ c hc hck => by omega⟩
  have hplt : p < size := by omega
  have hparlt : (p - 1) / 2 < size := by omega
  rw [harr _ hparlt, harr _ hplt, hkey _ hparlt _ hplt]
  exact hord p hp0 hplt

/-- After modifying only the key (or replacing the edge) at position `k < size'` in a heap where
every non-`k` edge still satisfies parent-child order and `parent(k)` still beats every child of `k`,
a single comparison against `parent(k)` selects `SelectHeapOrderExceptUp` or
`SelectHeapOrderExceptDown`. -/
theorem selectHeap_except_of_replaceAt {mem : ℕ → ℕ} {loc : SelectHeapLoc} {h size' k : ℕ}
    (hk : k < size')
    (hbij : SelectHeapBijection mem loc size')
    (hkeys : SelectHeapKeysValid mem loc h)
    (hother : ∀ p, 0 < p → p < size' → p ≠ k → (p - 1) / 2 ≠ k →
      loc.edgeBetter mem h (mem (loc.arrPtr + (p - 1) / 2)) (mem (loc.arrPtr + p)) = true)
    (hskip : 0 < k → ∀ c < size', (c - 1) / 2 = k →
      loc.edgeBetter mem h (mem (loc.arrPtr + (k - 1) / 2)) (mem (loc.arrPtr + c)) = true) :
    (0 < k ∧ loc.edgeBetter mem h (mem (loc.arrPtr + k)) (mem (loc.arrPtr + (k - 1) / 2)) = true →
      SelectHeapOrderExceptUp mem loc h size' k) ∧
    ((k = 0 ∨ loc.edgeBetter mem h (mem (loc.arrPtr + k)) (mem (loc.arrPtr + (k - 1) / 2)) = false) →
      SelectHeapOrderExceptDown mem loc h size' k) := by
  constructor
  · rintro ⟨hk0, hbeat⟩
    refine ⟨hk, fun p hp0 hp hpk => ?_, hskip⟩
    by_cases hpar : (p - 1) / 2 = k
    · rw [hpar]
      have hparLt : (k - 1) / 2 < size' := by omega
      have hdK := (hkeys _ (hbij.2.1 k hk) (hbij.pos_arr_ne_zero hk)).2.2.2
      have hdP := (hkeys _ (hbij.2.1 _ hparLt) (hbij.pos_arr_ne_zero hparLt)).2.2.2
      have hdC := (hkeys _ (hbij.2.1 p hp) (hbij.pos_arr_ne_zero hp)).2.2.2
      exact keyBetter_trans_pos hdK hdP hdC hbeat (hskip hk0 p hp hpar)
    · exact hother p hp0 hp hpk hpar
  · intro hnotBeat
    refine ⟨hk, fun p hp0 hp hpar => ?_, hskip⟩
    by_cases hpk : p = k
    · subst hpk
      rcases hnotBeat with rfl | hfalse
      · omega
      · have hparLt : (p - 1) / 2 < size' := by omega
        have hne : mem (loc.arrPtr + (p - 1) / 2) ≠ mem (loc.arrPtr + p) := fun heq => by
          have := hbij.arr_inj hparLt hp heq; omega
        rcases keyBetter_total_of_ne (n₁ := loc.readNum mem h (mem (loc.arrPtr + (p - 1) / 2)))
            (d₁ := loc.readDen mem h (mem (loc.arrPtr + (p - 1) / 2)))
            (n₂ := loc.readNum mem h (mem (loc.arrPtr + p)))
            (d₂ := loc.readDen mem h (mem (loc.arrPtr + p))) hne with h1 | h2
        · exact h1
        · change loc.edgeBetter mem h (mem (loc.arrPtr + p)) (mem (loc.arrPtr + (p - 1) / 2)) = true at h2
          rw [hfalse] at h2; cases h2
    · exact hother p hp0 hp hpk hpar

/-- Transitivity of parent over grandchild in any valid `SelectHeapOrder`: if `0 < k < size` and
`(c - 1) / 2 = k` with `c < size`, then `arr[(k - 1) / 2]` beats `arr[c]`. -/
theorem selectHeapOrder_grandparent_beats_child {mem : ℕ → ℕ} {loc : SelectHeapLoc}
    {h size k c : ℕ}
    (hbij : SelectHeapBijection mem loc size)
    (hkeys : SelectHeapKeysValid mem loc h)
    (hord : SelectHeapOrder mem loc h size)
    (hk0 : 0 < k) (hk : k < size) (hc : c < size) (hck : (c - 1) / 2 = k) :
    loc.edgeBetter mem h (mem (loc.arrPtr + (k - 1) / 2)) (mem (loc.arrPtr + c)) = true := by
  have hparLt : (k - 1) / 2 < size := by omega
  have hc0 : 0 < c := by omega
  have hdP := (hkeys _ (hbij.2.1 _ hparLt) (hbij.pos_arr_ne_zero hparLt)).2.2.2
  have hdK := (hkeys _ (hbij.2.1 k hk) (hbij.pos_arr_ne_zero hk)).2.2.2
  have hdC := (hkeys _ (hbij.2.1 c hc) (hbij.pos_arr_ne_zero hc)).2.2.2
  have h1 := hord k hk0 hk
  have h2 := hord c hc0 hc
  rw [hck] at h2
  exact keyBetter_trans_pos hdP hdK hdC h1 h2

end MinCostFlow.MinRatio
