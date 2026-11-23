module

public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import WordRAM.Logic
import WordRAM.Tactic

/-!
# Doubly-Linked Ghost-List and Scratch Helpers for Per-Component LSF (`CompGhostOps`)

Implements and verifies five small deterministic (`NoRand`) Word-RAM helper procedures used by
the per-component LSF batch dispatcher (`CompBatchProcs.lean`):

* `ghostConsProc`: `O(1)` prepend of an edge `e` onto a 1-indexed `IsDoublyLinkedList` with
  length counter.
* `ghostEraseProc`: `O(1)` removal of an edge `e` from a 1-indexed `IsDoublyLinkedList` with
  length counter.
* `ghostAppendProc`: `O(|L| + 1)` traversal copying a 1-indexed `IsDoublyLinkedList` into a
  contiguous output slice (used for Tag-3 projected splits).
* `compZeroRangeProc`: `O(len + 1)` zeroing of a temporary scratch slice.
* `compMarkTouchProc`: `O(1)` deduplicated insertion of a touched component index into the
  output list using a mark array.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Procedure indices and bodies -/

def compHelperIdxCons : ℕ := 0
def compHelperIdxErase : ℕ := 1
def compHelperIdxAppend : ℕ := 2
def compHelperIdxZero : ℕ := 3
def compHelperIdxMark : ℕ := 4

/-- `args = [headAddr, prevBase, nextBase, cntAddr, e]`: prepend `e` to the 1-indexed
doubly-linked list at `headAddr` and increment `mem[cntAddr]`. Returns `0`. -/
def ghostConsProc : Stmt :=
  .assign 5 (.load (.reg 0)) ;;
  .store (.bin .add (.reg 1) (.reg 4)) (.const 0) ;;
  .store (.bin .add (.reg 2) (.reg 4)) (.reg 5) ;;
  .cond (.reg 5)
    (.store (.bin .add (.reg 1) (.bin .sub (.reg 5) (.const 1)))
      (.bin .add (.reg 4) (.const 1)))
    .nop ;;
  .store (.reg 0) (.bin .add (.reg 4) (.const 1)) ;;
  .assign 6 (.load (.reg 3)) ;;
  .store (.reg 3) (.bin .add (.reg 6) (.const 1)) ;;
  .ret (.const 0)

/-- `args = [headAddr, prevBase, nextBase, cntAddr, e]`: remove `e` from the 1-indexed
doubly-linked list at `headAddr` and decrement `mem[cntAddr]`. Returns `0`. -/
def ghostEraseProc : Stmt :=
  .assign 5 (.load (.bin .add (.reg 1) (.reg 4))) ;;
  .assign 6 (.load (.bin .add (.reg 2) (.reg 4))) ;;
  .cond (.reg 5)
    (.store (.bin .add (.reg 2) (.bin .sub (.reg 5) (.const 1))) (.reg 6))
    (.store (.reg 0) (.reg 6)) ;;
  .cond (.reg 6)
    (.store (.bin .add (.reg 1) (.bin .sub (.reg 6) (.const 1))) (.reg 5))
    .nop ;;
  .store (.bin .add (.reg 1) (.reg 4)) (.const 0) ;;
  .store (.bin .add (.reg 2) (.reg 4)) (.const 0) ;;
  .assign 7 (.load (.reg 3)) ;;
  .store (.reg 3) (.bin .sub (.reg 7) (.const 1)) ;;
  .ret (.const 0)

/-- `args = [headAddr, nextBase, outPtr]`: copy the 1-indexed doubly-linked list starting at
`mem[headAddr]` into `[outPtr, outPtr + len)`, returning `len`. -/
def ghostAppendProc : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.const 0) ;;
  .loop (.reg 3)
    (.assign 5 (.bin .sub (.reg 3) (.const 1)) ;;
     .store (.bin .add (.reg 2) (.reg 4)) (.reg 5) ;;
     .assign 3 (.load (.bin .add (.reg 1) (.reg 5))) ;;
     .assign 4 (.bin .add (.reg 4) (.const 1))) ;;
  .ret (.reg 4)

/-- `args = [ptr, len]`: store `0` into `[ptr, ptr + len)`, returning `0`. -/
def compZeroRangeProc : Stmt :=
  .assign 2 (.const 0) ;;
  .loop (.bin .lt (.reg 2) (.reg 1))
    (.store (.bin .add (.reg 0) (.reg 2)) (.const 0) ;;
     .assign 2 (.bin .add (.reg 2) (.const 1))) ;;
  .ret (.const 0)

/-- `args = [markBase, listBase, cntAddr, c]`: if `mem[markBase + c] = 0`, set it to `1`,
append `c` to `listBase[cnt]`, and increment `mem[cntAddr]`. Returns `0`. -/
def compMarkTouchProc : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.reg 3))) ;;
  .cond (.reg 4)
    (.ret (.const 0))
    (.store (.bin .add (.reg 0) (.reg 3)) (.const 1) ;;
     .assign 5 (.load (.reg 2)) ;;
     .store (.bin .add (.reg 1) (.reg 5)) (.reg 3) ;;
     .store (.reg 2) (.bin .add (.reg 5) (.const 1)) ;;
     .ret (.const 0))

/-- Bundled helper procedure list (`5` deterministic procedures). -/
def compHelperProcs : List Stmt :=
  [ghostConsProc, ghostEraseProc, ghostAppendProc, compZeroRangeProc, compMarkTouchProc]

lemma compHelperProcs_length : compHelperProcs.length = 5 := rfl

lemma compHelperProcs_noRand : ∀ s ∈ compHelperProcs, s.NoRand := by
  intro s hs
  simp only [compHelperProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    simp [ghostConsProc, ghostEraseProc, ghostAppendProc, compZeroRangeProc, compMarkTouchProc,
      Stmt.NoRand]

/-! ## 2. Contracts -/

/-- Contract for `ghostConsProc` (`[headAddr, prevBase, nextBase, cntAddr, e]`). -/
def ghostConsContract (w cap : ℕ) (L : List ℕ) : Contract where
  pre args mem := ∃ headAddr prevBase nextBase cntAddr e,
    args = [headAddr, prevBase, nextBase, cntAddr, e] ∧
    16 ≤ 2 ^ w ∧ e < cap ∧ e ∉ L ∧
    headAddr < 2 ^ w ∧ cntAddr < 2 ^ w ∧
    prevBase + cap < 2 ^ w ∧ nextBase + cap < 2 ^ w ∧
    cap + 1 < 2 ^ w ∧ L.length + 1 < 2 ^ w ∧
    headAddr ≠ cntAddr ∧
    (∀ x < cap, prevBase + x ≠ headAddr ∧ prevBase + x ≠ cntAddr) ∧
    (∀ x < cap, nextBase + x ≠ headAddr ∧ nextBase + x ≠ cntAddr) ∧
    (∀ x < cap, ∀ y < cap, prevBase + x ≠ nextBase + y) ∧
    IsDoublyLinkedList mem prevBase nextBase headAddr cap L ∧
    mem cntAddr = L.length
  post args mem ret mem' := ∃ headAddr prevBase nextBase cntAddr e,
    args = [headAddr, prevBase, nextBase, cntAddr, e] ∧ ret = 0 ∧
    IsDoublyLinkedList mem' prevBase nextBase headAddr cap (e :: L) ∧
    mem' cntAddr = L.length + 1 ∧
    ∀ a, a ≠ headAddr → a ≠ cntAddr →
      a ≠ prevBase + e → a ≠ nextBase + e →
      (∀ h₀ xs, L = h₀ :: xs → a ≠ prevBase + h₀) →
      mem' a = mem a
  cost _ _ := 70

/-- Contract for `ghostEraseProc` (`[headAddr, prevBase, nextBase, cntAddr, e]`). -/
def ghostEraseContract (w cap : ℕ) (L : List ℕ) : Contract where
  pre args mem := ∃ headAddr prevBase nextBase cntAddr e,
    args = [headAddr, prevBase, nextBase, cntAddr, e] ∧
    16 ≤ 2 ^ w ∧ e < cap ∧ e ∈ L ∧
    headAddr < 2 ^ w ∧ cntAddr < 2 ^ w ∧
    prevBase + cap < 2 ^ w ∧ nextBase + cap < 2 ^ w ∧
    cap + 1 < 2 ^ w ∧ L.length < 2 ^ w ∧
    headAddr ≠ cntAddr ∧
    (∀ x < cap, prevBase + x ≠ headAddr ∧ prevBase + x ≠ cntAddr) ∧
    (∀ x < cap, nextBase + x ≠ headAddr ∧ nextBase + x ≠ cntAddr) ∧
    (∀ x < cap, ∀ y < cap, prevBase + x ≠ nextBase + y) ∧
    IsDoublyLinkedList mem prevBase nextBase headAddr cap L ∧
    mem cntAddr = L.length
  post args mem ret mem' := ∃ headAddr prevBase nextBase cntAddr e,
    args = [headAddr, prevBase, nextBase, cntAddr, e] ∧ ret = 0 ∧
    IsDoublyLinkedList mem' prevBase nextBase headAddr cap (L.erase e) ∧
    mem' cntAddr = L.length - 1 ∧
    ∀ a, a ≠ headAddr → a ≠ cntAddr →
      (∀ x ∈ L, a ≠ prevBase + x ∧ a ≠ nextBase + x) →
      mem' a = mem a
  cost _ _ := 90

/-- Contract for `ghostAppendProc` (`[headAddr, nextBase, outPtr]`). -/
def ghostAppendContract (w cap : ℕ) (L : List ℕ) : Contract where
  pre args mem := ∃ headAddr nextBase outPtr prevBase,
    args = [headAddr, nextBase, outPtr] ∧
    16 ≤ 2 ^ w ∧ headAddr < 2 ^ w ∧ nextBase + cap < 2 ^ w ∧
    outPtr + L.length < 2 ^ w ∧ cap + 1 < 2 ^ w ∧
    (∀ i < L.length, outPtr + i ≠ headAddr ∧ ∀ x < cap, outPtr + i ≠ nextBase + x) ∧
    IsDoublyLinkedList mem prevBase nextBase headAddr cap L
  post args mem ret mem' := ∃ headAddr nextBase outPtr,
    args = [headAddr, nextBase, outPtr] ∧ ret = L.length ∧
    ListAt mem' outPtr L ∧
    ∀ a, a < outPtr ∨ outPtr + L.length ≤ a → mem' a = mem a
  cost _ _ := 40 * L.length + 25

/-- Contract for `compZeroRangeProc` (`[ptr, len]`). -/
def compZeroRangeContract (w : ℕ) : Contract where
  pre args _ := ∃ ptr len, args = [ptr, len] ∧ 16 ≤ 2 ^ w ∧ ptr + len < 2 ^ w
  post args mem ret mem' := ∃ ptr len, args = [ptr, len] ∧ ret = 0 ∧
    (∀ i < len, mem' (ptr + i) = 0) ∧
    (∀ a, a < ptr ∨ ptr + len ≤ a → mem' a = mem a)
  cost args _ := 20 * args.getD 1 0 + 15

/-- Contract for `compMarkTouchProc` (`[markBase, listBase, cntAddr, c]`). -/
def compMarkTouchContract (w cap : ℕ) (L : List ℕ) : Contract where
  pre args mem := ∃ markBase listBase cntAddr c,
    args = [markBase, listBase, cntAddr, c] ∧
    16 ≤ 2 ^ w ∧ c < cap ∧ markBase + cap < 2 ^ w ∧
    cntAddr < 2 ^ w ∧ listBase + L.length + 1 < 2 ^ w ∧
    cntAddr ≠ markBase + c ∧ listBase + L.length ≠ markBase + c ∧
    listBase + L.length ≠ cntAddr ∧
    (∀ i < L.length, listBase + i ≠ markBase + c ∧ listBase + i ≠ cntAddr) ∧
    mem cntAddr = L.length ∧ ListAt mem listBase L ∧
    (mem (markBase + c) = 0 ∨ mem (markBase + c) = 1)
  post args mem ret mem' := ∃ markBase listBase cntAddr c,
    args = [markBase, listBase, cntAddr, c] ∧ ret = 0 ∧
    let L' := if mem (markBase + c) = 0 then L ++ [c] else L
    mem' (markBase + c) = 1 ∧
    mem' cntAddr = L'.length ∧
    ListAt mem' listBase L' ∧
    ∀ a, a ≠ markBase + c → a ≠ cntAddr → a ≠ listBase + L.length → mem' a = mem a
  cost _ _ := 60

end

/-! ## 3. Verification -/

public section

/-- Verification of `compZeroRangeProc`. -/
theorem compZeroRange_meetsContract {w b : ℕ} {p : Program}
    (hp : p.procs[b]? = some compZeroRangeProc) :
    MeetsContract w p b (compZeroRangeContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨ptr, len, rfl, hw16, hbd⟩
  have hw1 : 1 < 2 ^ w := by omega
  have hloop : ∀ ω' rem i (st : State), i ≤ len → len - i = rem →
      st.regs 0 = ptr → st.regs 1 = len → st.regs 2 = i →
      (∀ k < i, st.mem (ptr + k) = 0) →
      (∀ a, a < ptr ∨ ptr + i ≤ a → st.mem a = mem a) →
      ∃ st' c, Runs w p ω'
          (.loop (.bin .lt (.reg 2) (.reg 1))
            (.store (.bin .add (.reg 0) (.reg 2)) (.const 0) ;;
             .assign 2 (.bin .add (.reg 2) (.const 1))))
          st .normal st' c ∧
        (∀ k < len, st'.mem (ptr + k) = 0) ∧
        (∀ a, a < ptr ∨ ptr + len ≤ a → st'.mem a = mem a) ∧
        c ≤ 20 * rem + 6 := by
    intro ω' rem
    induction rem with
    | zero =>
      intro i st hi hrem hr0 hr1 hr2 hz hfr
      have hieq : i = len := by omega
      subst hieq
      refine ⟨st, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr1, hr2],
        rfl, rfl, by simp [Expr.size]⟩), hz, hfr, by omega⟩
    | succ rem ih =>
      intro i st hi hrem hr0 hr1 hr2 hz hfr
      have hilt : i < len := by omega
      let mem1 := Function.update st.mem (ptr + i) 0
      let st1 : State := { st with mem := mem1 }
      let st2 : State := { st1 with regs := Function.update st1.regs 2 (i + 1) }
      have hs1 : Runs w p ω' (.store (.bin .add (.reg 0) (.reg 2)) (.const 0)) st .normal st1 5 :=
        runs_store_iff.mpr ⟨ptr + i, 0, by eval_expr, by eval_expr, rfl, rfl, by simp [Expr.size]⟩
      have hs2 : Runs w p ω' (.assign 2 (.bin .add (.reg 2) (.const 1))) st1 .normal st2 4 :=
        runs_assign_iff.mpr ⟨i + 1, by eval_expr, rfl, rfl, by simp [Expr.size]⟩
      have hbody : Runs w p ω' _ st .normal st2 10 :=
        runs_seq_iff.mpr (Or.inr ⟨st1, 5, 4, hs1, hs2, rfl⟩)
      obtain ⟨st', c', hrun', hz', hfr', hc'⟩ := ih (i + 1) st2 (by omega) (by omega)
        (by simp [st2, st1, hr0]) (by simp [st2, st1, hr1]) (by simp [st2])
        (fun k hk => by
          dsimp only [st2, st1, mem1]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
          · rw [Function.update_of_ne (by omega)]; exact hz k hk'
          · exact Function.update_self _ _ _)
        (fun a ha => by
          dsimp only [st2, st1, mem1]
          rw [Function.update_of_ne (by omega)]
          exact hfr a (by omega))
      refine ⟨st', 3 + 10 + c' + 1,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st2, 10, c',
          by simp [Expr.eval, BinOp.eval, hr1, hr2, hilt, hw1], by decide, hbody, hrun',
          by simp [Expr.size]⟩)), hz', hfr', by omega⟩
  refine runs_start_le ?_
  unfold compZeroRangeProc
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  have htr : Triple w p
      (fun st => st.regs 0 = ptr ∧ st.regs 1 = len ∧ st.regs 2 = 0 ∧ st.mem = mem)
      (.loop (.bin .lt (.reg 2) (.reg 1))
        (.store (.bin .add (.reg 0) (.reg 2)) (.const 0) ;;
         .assign 2 (.bin .add (.reg 2) (.const 1))))
      (normalPost fun st' =>
        (∀ k < len, st'.mem (ptr + k) = 0) ∧
        (∀ a, a < ptr ∨ ptr + len ≤ a → st'.mem a = mem a))
      (fun _ => 20 * len + 6) := by
    intro st ω' ⟨h0, h1, h2, hm⟩
    obtain ⟨st', c', hr, hz, hfr, hc⟩ := hloop ω' len 0 st (Nat.zero_le _) (by omega) h0 h1 h2
      (fun _ hk => by omega) (fun _ _ => by rw [hm])
    exact ⟨.normal, st', c', hr, ⟨hz, hfr⟩, hc⟩
  refine runs_seq_triple_le htr ⟨by simp [startState], by simp [startState], by simp, rfl⟩ ?_
  intro st₁ ⟨hz', hfr'⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨ptr, len, rfl, rfl, hz', hfr'⟩ ?_
  simp only [compZeroRangeContract, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, Expr.size]
  omega

/-- Verification of `compMarkTouchProc`. -/
theorem compMarkTouch_meetsContract {w cap b : ℕ} {L : List ℕ} {p : Program}
    (hp : p.procs[b]? = some compMarkTouchProc) :
    MeetsContract w p b (compMarkTouchContract w cap L) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨markBase, listBase, cntAddr, c, rfl, hw16, hc, hmb, hca, hlb,
    hne1, hne2, hne3, hneL, hcnt, hLA, hmk⟩
  have hw1 : 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold compMarkTouchProc
  refine runs_seq_assign_le (v := mem (markBase + c)) (by eval_expr) ?_
  refine runs_cond_le (v := mem (markBase + c)) (by eval_expr) ?_ ?_
  · intro hne
    have hmk1 : mem (markBase + c) = 1 := hmk.resolve_left hne
    refine runs_ret_le (v := 0) (by eval_expr) ?_ (by simp [compMarkTouchContract, Expr.size])
    exact ⟨markBase, listBase, cntAddr, c, rfl, rfl, hmk1,
      by rw [ite_eq_right hne]; exact hcnt, by rw [ite_eq_right hne]; exact hLA, fun _ _ _ _ => rfl⟩
  · intro hmk0
    refine runs_seq_store_le (x := markBase + c) (v := 1) (by eval_expr) (by eval_expr) ?_
    have hm1_cnt : Function.update mem (markBase + c) 1 cntAddr = L.length := by
      rw [Function.update_of_ne hne1, hcnt]
    refine runs_seq_assign_le (v := L.length) (by eval_expr) ?_
    refine runs_seq_store_le (x := listBase + L.length) (v := c) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cntAddr) (v := L.length + 1) (by eval_expr) (by eval_expr) ?_
    refine runs_ret_le (v := 0) (by eval_expr) ?_ (by simp [compMarkTouchContract, Expr.size])
    refine ⟨markBase, listBase, cntAddr, c, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [Function.update_of_ne (Ne.symm hne1), Function.update_of_ne (Ne.symm hne2),
        Function.update_self]
    · simp only [hmk0, ↓reduceIte, List.length_append, List.length_singleton, Function.update_self]
    · simp only [hmk0, ↓reduceIte]
      intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · have hneA := hneL i hi'
        simp only [startState, List.getElem_append_left hi', Function.update_of_ne hneA.2,
          Function.update_of_ne (by omega : listBase + i ≠ listBase + L.length),
          Function.update_of_ne hneA.1]
        exact hLA i hi'
      · simp [startState, Function.update_of_ne hne3]
    · intro a ha1 ha2 ha3
      simp only [startState, Function.update_of_ne ha2, Function.update_of_ne ha3,
        Function.update_of_ne ha1]

/-- Verification of `ghostAppendProc`. -/
theorem ghostAppend_meetsContract {w cap b : ℕ} {L : List ℕ} {p : Program}
    (hp : p.procs[b]? = some ghostAppendProc) :
    MeetsContract w p b (ghostAppendContract w cap L) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨headAddr, nextBase, outPtr, prevBase, rfl, hw16, hha, hnb, hop, hcap, hdisj, hDLL⟩
  have hw1 : 1 < 2 ^ w := by omega
  rcases hDLL with ⟨_, hltCap, hhead, hbody⟩
  have hloop : ∀ ω' rem i (st : State), (hi : i ≤ L.length) → L.length - i = rem →
      st.regs 1 = nextBase → st.regs 2 = outPtr →
      st.regs 3 = (if hi : i < L.length then L[i] + 1 else 0) →
      st.regs 4 = i →
      (∀ k (hk : k < i), st.mem (outPtr + k) = L[k]'(by omega)) →
      (∀ a, a < outPtr ∨ outPtr + i ≤ a → st.mem a = mem a) →
      ∃ st' c, Runs w p ω'
          (.loop (.reg 3)
            (.assign 5 (.bin .sub (.reg 3) (.const 1)) ;;
             .store (.bin .add (.reg 2) (.reg 4)) (.reg 5) ;;
             .assign 3 (.load (.bin .add (.reg 1) (.reg 5))) ;;
             .assign 4 (.bin .add (.reg 4) (.const 1))))
          st .normal st' c ∧
        st'.regs 4 = L.length ∧
        ListAt st'.mem outPtr L ∧
        (∀ a, a < outPtr ∨ outPtr + L.length ≤ a → st'.mem a = mem a) ∧
        c ≤ 40 * rem + 6 := by
    intro ω' rem
    induction rem with
    | zero =>
      intro i st hi hrem _ _ hr3 hr4 hpref hfr
      have hieq : i = L.length := by omega
      subst hieq
      have hr3_0 : st.regs 3 = 0 := by simpa using hr3
      refine ⟨st, 2, runs_loop_iff.mpr (Or.inl ⟨by eval_expr, rfl, rfl, by simp [Expr.size]⟩),
        hr4, fun k hk => hpref k hk, hfr, by omega⟩
    | succ rem ih =>
      intro i st hi hrem hr1 hr2 hr3 hr4 hpref hfr
      have hilt : i < L.length := by omega
      have hr3_v : st.regs 3 = L[i] + 1 := by simpa [hilt] using hr3
      have hLi_cap : L[i] < cap := hltCap _ (List.getElem_mem hilt)
      let st1 : State := { st with regs := Function.update st.regs 5 L[i] }
      let mem2 := Function.update st.mem (outPtr + i) L[i]
      let st2 : State := { st1 with mem := mem2 }
      have hnxt_eq : mem2 (nextBase + L[i]) =
          (if i + 1 = L.length then 0 else L.getD (i + 1) 0 + 1) := by
        have hne : nextBase + L[i] ≠ outPtr + i := Ne.symm ((hdisj i hilt).2 _ hLi_cap)
        have hnot : nextBase + L[i] < outPtr ∨ outPtr + i ≤ nextBase + L[i] := by
          by_cases hlt' : nextBase + L[i] < outPtr
          · exact Or.inl hlt'
          · right; by_contra hlt2
            exact (hdisj (nextBase + L[i] - outPtr) (by omega)).2 _ hLi_cap (by omega)
        dsimp only [mem2]; rw [Function.update_of_ne hne, hfr _ hnot]; exact (hbody i hilt).2
      let nxtVal := if hi1 : i + 1 < L.length then L[i + 1] + 1 else 0
      have hnxt_eq' : mem2 (nextBase + L[i]) = nxtVal := by
        rw [hnxt_eq]; dsimp only [nxtVal]
        by_cases hi1 : i + 1 < L.length
        · simp [hi1, show i + 1 ≠ L.length by omega]
        · simp [show i + 1 = L.length by omega]
      have hnxt_lt : nxtVal < 2 ^ w := by
        dsimp only [nxtVal]; split_ifs with hi1
        · have := hltCap _ (List.getElem_mem hi1); omega
        · omega
      let st3 : State := { st2 with regs := Function.update st2.regs 3 nxtVal }
      let st4 : State := { st3 with regs := Function.update st3.regs 4 (i + 1) }
      have hs1 : Runs w p ω' (.assign 5 (.bin .sub (.reg 3) (.const 1))) st .normal st1 4 :=
        runs_assign_iff.mpr ⟨L[i], by simp [Expr.eval, BinOp.eval, hr3_v, hw1, show L[i] < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hs2 : Runs w p ω' (.store (.bin .add (.reg 2) (.reg 4)) (.reg 5)) st1 .normal st2 5 :=
        runs_store_iff.mpr ⟨outPtr + i, L[i], by eval_expr, by eval_expr, rfl, rfl, by simp [Expr.size]⟩
      have hs3 : Runs w p ω' (.assign 3 (.load (.bin .add (.reg 1) (.reg 5)))) st2 .normal st3 5 :=
        runs_assign_iff.mpr ⟨nxtVal, by simp [Expr.eval, BinOp.eval, st2, st1, hr1,
          show nextBase + L[i] < 2 ^ w by omega, hnxt_eq'], rfl, rfl, by simp [Expr.size]⟩
      have hs4 : Runs w p ω' (.assign 4 (.bin .add (.reg 4) (.const 1))) st3 .normal st4 4 :=
        runs_assign_iff.mpr ⟨i + 1, by eval_expr, rfl, rfl, by simp [Expr.size]⟩
      have hbodyRun : Runs w p ω' _ st .normal st4 21 :=
        runs_seq_iff.mpr (Or.inr ⟨st1, 4, 16, hs1, runs_seq_iff.mpr (Or.inr ⟨st2, 5, 10, hs2,
          runs_seq_iff.mpr (Or.inr ⟨st3, 5, 4, hs3, hs4, rfl⟩), rfl⟩), rfl⟩)
      obtain ⟨st', c', hr', hr4', hLA', hfr', hc'⟩ := ih (i + 1) st4 (by omega) (by omega)
        (by simp [st4, st3, st2, st1, hr1]) (by simp [st4, st3, st2, st1, hr2])
        (by simp [st4, st3, nxtVal]) (by simp [st4])
        (fun k hk => by
          dsimp only [st4, st3, st2, mem2]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
          · rw [Function.update_of_ne (by omega)]; exact hpref k hk'
          · exact Function.update_self _ _ _)
        (fun a ha => by dsimp only [st4, st3, st2, mem2]; rw [Function.update_of_ne (by omega)]; exact hfr a (by omega))
      refine ⟨st', 1 + 21 + c' + 1, runs_loop_iff.mpr (Or.inr (Or.inr ⟨L[i] + 1, st4, 21, c',
        by eval_expr, Nat.succ_ne_zero _, hbodyRun, hr', by simp [Expr.size]⟩)), hr4', hLA', hfr', by omega⟩
  have hhd_eq : mem headAddr = (if hi : 0 < L.length then L[0] + 1 else 0) := by
    cases L <;> simpa using hhead
  have hhd_lt : mem headAddr < 2 ^ w := by
    rw [hhd_eq]; split_ifs with h0
    · have := hltCap _ (List.getElem_mem h0); omega
    · omega
  refine runs_start_le ?_
  unfold ghostAppendProc
  refine runs_seq_assign_le (v := mem headAddr) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  have htr : Triple w p
      (fun st => st.regs 1 = nextBase ∧ st.regs 2 = outPtr ∧
        st.regs 3 = (if hi : 0 < L.length then L[0] + 1 else 0) ∧
        st.regs 4 = 0 ∧ st.mem = mem)
      (.loop (.reg 3)
        (.assign 5 (.bin .sub (.reg 3) (.const 1)) ;;
         .store (.bin .add (.reg 2) (.reg 4)) (.reg 5) ;;
         .assign 3 (.load (.bin .add (.reg 1) (.reg 5))) ;;
         .assign 4 (.bin .add (.reg 4) (.const 1))))
      (normalPost fun st' =>
        st'.regs 4 = L.length ∧ ListAt st'.mem outPtr L ∧
        (∀ a, a < outPtr ∨ outPtr + L.length ≤ a → st'.mem a = mem a))
      (fun _ => 40 * L.length + 6) := by
    intro st ω' ⟨h1, h2, h3, h4, hm⟩
    obtain ⟨st', c', hr, hr4', hLA', hfr', hc⟩ := hloop ω' L.length 0 st (Nat.zero_le _) (by omega)
      h1 h2 h3 h4 (fun _ hk => by omega) (fun _ _ => by rw [hm])
    exact ⟨.normal, st', c', hr, ⟨hr4', hLA', hfr'⟩, hc⟩
  refine runs_seq_triple_le htr
    ⟨by simp [startState], by simp [startState], by simpa [startState] using hhd_eq, by simp, rfl⟩ ?_
  intro st₁ ⟨hr4', hLA', hfr'⟩
  refine runs_ret_le (v := L.length) (by eval_expr) ⟨headAddr, nextBase, outPtr, rfl, rfl, hLA', hfr'⟩ ?_
  simp only [ghostAppendContract, Expr.size]; omega

/-- Verification of `ghostConsProc`. -/
theorem ghostCons_meetsContract {w cap b : ℕ} {L : List ℕ} {p : Program}
    (hp : p.procs[b]? = some ghostConsProc) :
    MeetsContract w p b (ghostConsContract w cap L) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨headAddr, prevBase, nextBase, cntAddr, e, rfl, hw16, heCap, heNotL,
    hha, hca, hpb, hnb, hcap1, hlen1, hneHC, hdisjP, hdisjN, hdisjPN, hDLL, hcnt⟩
  have hw1 : 1 < 2 ^ w := by omega
  have hhd_lt : mem headAddr < 2 ^ w := by
    have hhd := hDLL.2.2.1
    cases L with
    | nil => dsimp only at hhd; omega
    | cons h₀ xs =>
      dsimp only at hhd
      have := hDLL.2.1 h₀ List.mem_cons_self; omega
  refine runs_start_le ?_
  unfold ghostConsProc
  refine runs_seq_assign_le (v := mem headAddr) (by eval_expr) ?_
  refine runs_seq_store_le (x := prevBase + e) (v := 0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := nextBase + e) (v := mem headAddr) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_cond_le (v := mem headAddr) (by eval_expr) ?_ ?_
  · intro hhd_ne
    cases L with
    | nil => exact absurd hDLL.2.2.1 hhd_ne
    | cons h₀ xs =>
      have hhd_eq : mem headAddr = h₀ + 1 := hDLL.2.2.1
      have hh0_cap : h₀ < cap := hDLL.2.1 h₀ List.mem_cons_self
      have he_ne_h0 : e ≠ h₀ := fun h => heNotL (h ▸ List.mem_cons_self)
      refine runs_seq_store_le (x := prevBase + h₀) (v := e + 1)
        (by simp [Expr.eval, BinOp.eval, startState, hhd_eq, hw1,
              show h₀ < 2 ^ w by omega, show prevBase + h₀ < 2 ^ w by omega])
        (by eval_expr) ?_
      refine runs_seq_store_le (x := headAddr) (v := e + 1) (by eval_expr) (by eval_expr) ?_
      have hcnt_m : Function.update (Function.update (Function.update
          (Function.update mem (prevBase + e) 0) (nextBase + e) (mem headAddr))
          (prevBase + h₀) (e + 1)) headAddr (e + 1) cntAddr = (h₀ :: xs).length := by
        rw [Function.update_of_ne (Ne.symm hneHC),
          Function.update_of_ne (Ne.symm (hdisjP h₀ hh0_cap).2),
          Function.update_of_ne (Ne.symm (hdisjN e heCap).2),
          Function.update_of_ne (Ne.symm (hdisjP e heCap).2), hcnt]
      refine runs_seq_assign_le (v := (h₀ :: xs).length) (by eval_expr) ?_
      refine runs_seq_store_le (x := cntAddr) (v := (h₀ :: xs).length + 1)
        (by eval_expr) (by eval_expr) ?_
      refine runs_ret_le (v := 0) (by eval_expr) ?_ (by simp [ghostConsContract, Expr.size])
      refine ⟨headAddr, prevBase, nextBase, cntAddr, e, rfl, rfl, ?_, Function.update_self _ _ _, ?_⟩
      · refine hDLL.cons heCap heNotL ?_ ?_ ?_ ?_ ?_ ?_
        · simp only [startState, Function.update_of_ne hneHC, Function.update_self]
        · simp only [startState, Function.update_of_ne (hdisjP e heCap).2,
            Function.update_of_ne (hdisjP e heCap).1,
            Function.update_of_ne (by omega : prevBase + e ≠ prevBase + h₀),
            Function.update_of_ne (hdisjPN e heCap e heCap), Function.update_self]
        · simp only [startState, Function.update_of_ne (hdisjN e heCap).2,
            Function.update_of_ne (hdisjN e heCap).1,
            Function.update_of_ne (Ne.symm (hdisjPN h₀ hh0_cap e heCap)), Function.update_self]
        · intro h₀' xs' heq
          rcases List.cons.inj heq with ⟨rfl, rfl⟩
          simp only [startState, Function.update_of_ne (hdisjP h₀ hh0_cap).2,
            Function.update_of_ne (hdisjP h₀ hh0_cap).1, Function.update_self]
        · intro y hy hne_hd
          have hy_cap := hDLL.2.1 y hy
          have hy_ne_e : y ≠ e := fun h => heNotL (h ▸ hy)
          have hy_ne_h0 : y ≠ h₀ := fun h => hne_hd xs (h ▸ rfl)
          simp only [startState, Function.update_of_ne (hdisjP y hy_cap).2,
            Function.update_of_ne (hdisjP y hy_cap).1,
            Function.update_of_ne (by omega : prevBase + y ≠ prevBase + h₀),
            Function.update_of_ne (hdisjPN y hy_cap e heCap),
            Function.update_of_ne (by omega : prevBase + y ≠ prevBase + e)]
        · intro y hy
          have hy_cap := hDLL.2.1 y hy
          have hy_ne_e : y ≠ e := fun h => heNotL (h ▸ hy)
          simp only [startState, Function.update_of_ne (hdisjN y hy_cap).2,
            Function.update_of_ne (hdisjN y hy_cap).1,
            Function.update_of_ne (Ne.symm (hdisjPN h₀ hh0_cap y hy_cap)),
            Function.update_of_ne (by omega : nextBase + y ≠ nextBase + e),
            Function.update_of_ne (Ne.symm (hdisjPN e heCap y hy_cap))]
      · intro a ha1 ha2 ha3 ha4 ha5
        simp only [startState, Function.update_of_ne ha2, Function.update_of_ne ha1,
          Function.update_of_ne (ha5 h₀ xs rfl), Function.update_of_ne ha4,
          Function.update_of_ne ha3]
  · intro hhd_0
    cases L with
    | cons h₀ xs =>
      have hhd := hDLL.2.2.1; dsimp only at hhd; omega
    | nil =>
      refine runs_seq_nop_le ?_
      refine runs_seq_store_le (x := headAddr) (v := e + 1) (by eval_expr) (by eval_expr) ?_
      have hcnt_m : Function.update (Function.update (Function.update mem (prevBase + e) 0)
          (nextBase + e) (mem headAddr)) headAddr (e + 1) cntAddr = 0 := by
        rw [Function.update_of_ne (Ne.symm hneHC),
          Function.update_of_ne (Ne.symm (hdisjN e heCap).2),
          Function.update_of_ne (Ne.symm (hdisjP e heCap).2), hcnt]; rfl
      refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, startState, hcnt_m]) ?_
      refine runs_seq_store_le (x := cntAddr) (v := 1) (by eval_expr)
        (by simp [Expr.eval, BinOp.eval, hw1]) ?_
      refine runs_ret_le (v := 0) (by eval_expr) ?_ (by simp [ghostConsContract, Expr.size])
      refine ⟨headAddr, prevBase, nextBase, cntAddr, e, rfl, rfl, ?_, Function.update_self _ _ _, ?_⟩
      · refine hDLL.cons heCap heNotL ?_ ?_ ?_ ?_ ?_ ?_
        · simp only [startState, Function.update_of_ne hneHC, Function.update_self]
        · simp only [startState, Function.update_of_ne (hdisjP e heCap).2,
            Function.update_of_ne (hdisjP e heCap).1,
            Function.update_of_ne (hdisjPN e heCap e heCap), Function.update_self]
        · simp only [startState, Function.update_of_ne (hdisjN e heCap).2,
            Function.update_of_ne (hdisjN e heCap).1, Function.update_self]
        · intro _ _ heq; cases heq
        · intro _ hy; cases hy
        · intro _ hy; cases hy
      · intro a ha1 ha2 ha3 ha4 _
        simp only [startState, Function.update_of_ne ha2, Function.update_of_ne ha1,
          Function.update_of_ne ha4, Function.update_of_ne ha3]

/-- Verification of `ghostEraseProc`. -/
theorem ghostErase_meetsContract {w cap b : ℕ} {L : List ℕ} {p : Program}
    (hp : p.procs[b]? = some ghostEraseProc) :
    MeetsContract w p b (ghostEraseContract w cap L) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨headAddr, prevBase, nextBase, cntAddr, e, rfl, hw16, heCap, heInL,
    hha, hca, hpb, hnb, hcap1, hlenW, hneHC, hdisjP, hdisjN, hdisjPN, hDLL, hcnt⟩
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨k, hk, hLk⟩ := List.getElem_of_mem heInL
  have hidx_e : L.idxOf e = k := by
    rw [← hLk]; exact hDLL.1.idxOf_getElem k hk
  have ⟨hp_eq, hn_eq⟩ := hDLL.2.2.2 k hk
  rw [hLk] at hp_eq hn_eq
  set pVal := mem (prevBase + e)
  set nVal := mem (nextBase + e)
  have hp_lt : pVal < 2 ^ w := by
    rw [show pVal = (if k = 0 then 0 else L[k - 1]'(by omega) + 1) from hp_eq]
    split_ifs
    · omega
    · have := hDLL.2.1 _ (List.getElem_mem (by omega : k - 1 < L.length)); omega
  have hn_lt : nVal < 2 ^ w := by
    rw [show nVal = (if k + 1 = L.length then 0 else L.getD (k + 1) 0 + 1) from hn_eq]
    split_ifs with hlast
    · omega
    · have hk1 : k + 1 < L.length := by omega
      rw [List.getD_eq_getElem _ _ hk1]
      have := hDLL.2.1 _ (List.getElem_mem hk1); omega
  -- Helper finishing the last 5 statements from any memory `mem2` produced after the two conditionals
  have htail : ∀ (mem2 : ℕ → ℕ) (regs : ℕ → ℕ) (costPrefix : ℕ),
      regs 0 = headAddr → regs 1 = prevBase → regs 2 = nextBase → regs 3 = cntAddr →
      regs 4 = e → regs 5 = pVal → regs 6 = nVal →
      mem2 cntAddr = L.length →
      (mem2 headAddr = if pVal = 0 then nVal else mem headAddr) →
      (∀ x < cap, x ≠ e →
        mem2 (nextBase + x) =
          if pVal ≠ 0 ∧ x = pVal - 1 then nVal else mem (nextBase + x)) →
      (∀ x < cap, x ≠ e →
        mem2 (prevBase + x) =
          if nVal ≠ 0 ∧ x = nVal - 1 then pVal else mem (prevBase + x)) →
      (∀ a, a ≠ headAddr → a ≠ cntAddr →
        (∀ x ∈ L, a ≠ prevBase + x ∧ a ≠ nextBase + x) → mem2 a = mem a) →
      costPrefix + 34 ≤ 90 →
      ∃ o st' c, Runs w p ω
          (.store (.bin .add (.reg 1) (.reg 4)) (.const 0) ;;
           .store (.bin .add (.reg 2) (.reg 4)) (.const 0) ;;
           .assign 7 (.load (.reg 3)) ;;
           .store (.reg 3) (.bin .sub (.reg 7) (.const 1)) ;;
           .ret (.const 0))
          { mem := mem2, regs := regs, pos := pos } o st' c ∧
        (ghostEraseContract w cap L).post [headAddr, prevBase, nextBase, cntAddr, e] mem o.value st'.mem ∧
        costPrefix + c ≤ 90 := by
    intro mem2 regs costPrefix hr0 hr1 hr2 hr3 hr4 hr5 hr6 hcnt2 hhd2 hnx2 hpr2 hfr2 hcp
    refine runs_seq_store_le (x := prevBase + e) (v := 0) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := nextBase + e) (v := 0) (by eval_expr) (by eval_expr) ?_
    have hcnt3 : Function.update (Function.update mem2 (prevBase + e) 0) (nextBase + e) 0 cntAddr =
        L.length := by
      rw [Function.update_of_ne (Ne.symm (hdisjN e heCap).2),
        Function.update_of_ne (Ne.symm (hdisjP e heCap).2), hcnt2]
    refine runs_seq_assign_le (v := L.length) (by eval_expr) ?_
    refine runs_seq_store_le (x := cntAddr) (v := L.length - 1) (by eval_expr) (by eval_expr) ?_
    refine runs_ret_le (v := 0) (by eval_expr) ?_ (by simp [Expr.size]; omega)
    set memF := Function.update (Function.update (Function.update mem2 (prevBase + e) 0)
      (nextBase + e) 0) cntAddr (L.length - 1)
    have hhdF : memF headAddr = if pVal = 0 then nVal else mem headAddr := by
      dsimp only [memF]
      rw [Function.update_of_ne hneHC, Function.update_of_ne (Ne.symm (hdisjN e heCap).1),
        Function.update_of_ne (Ne.symm (hdisjP e heCap).1), hhd2]
    have hprF : ∀ x < cap, x ≠ e →
        memF (prevBase + x) = if nVal ≠ 0 ∧ x = nVal - 1 then pVal else mem (prevBase + x) := by
      intro x hx hxe
      dsimp only [memF]
      rw [Function.update_of_ne (hdisjP x hx).2, Function.update_of_ne (hdisjPN x hx e heCap),
        Function.update_of_ne (by omega), hpr2 x hx hxe]
    have hnxF : ∀ x < cap, x ≠ e →
        memF (nextBase + x) = if pVal ≠ 0 ∧ x = pVal - 1 then nVal else mem (nextBase + x) := by
      intro x hx hxe
      dsimp only [memF]
      rw [Function.update_of_ne (hdisjN x hx).2, Function.update_of_ne (by omega),
        Function.update_of_ne (Ne.symm (hdisjPN e heCap x hx)), hnx2 x hx hxe]
    refine ⟨headAddr, prevBase, nextBase, cntAddr, e, rfl, rfl, ?_, Function.update_self _ _ _, ?_⟩
    · refine hDLL.erase heInL (fun _ _ => hhdF) ?_ ?_ ?_ ?_ ?_
      · intro hemp
        have hlen1' : L.length = 1 := by
          have := List.length_erase_of_mem heInL; rw [hemp] at this; simp at this; omega
        have hk0 : k = 0 := by omega
        have hp0 : pVal = 0 := by simp [pVal, hp_eq, hk0]
        have hn0 : nVal = 0 := by simp [nVal, hn_eq, show k + 1 = L.length by omega]
        dsimp only; rw [hhdF]; simp [hp0, hn0]
      · intro y hy hne_q
        have hyL := List.mem_of_mem_erase hy
        have hy_cap := hDLL.2.1 y hyL
        have hy_ne : y ≠ e := (hDLL.1.mem_erase_iff.mp hy).1
        dsimp only; rw [hprF y hy_cap hy_ne]
        have hnot : ¬(nVal ≠ 0 ∧ y = nVal - 1) := fun ⟨hn_ne, hy_eq⟩ => by
          have hk1 : k + 1 < L.length := by
            by_contra hge; exact hn_ne (by simp [nVal, hn_eq, show k + 1 = L.length by omega])
          have hn_val : nVal = L[k + 1] + 1 := by
            simp [nVal, hn_eq, show k + 1 ≠ L.length by omega, List.getD, hk1]
          apply hne_q; simpa [hidx_e, hk1] using (show y = L[k + 1] by omega)
        simp [hnot]
      · intro k' hk' hLk'
        have hk_eq : k' = k := (hDLL.1.getElem_inj_iff).mp (hLk'.trans hLk.symm)
        subst hk_eq
        have hq_cap := hDLL.2.1 _ (List.getElem_mem hk')
        have hq_ne : L[k' + 1] ≠ e := fun h => by
          have := hDLL.1.getElem_inj_iff.mp (h.trans hLk.symm); omega
        have hn_val : nVal = L[k' + 1] + 1 := by
          simp [nVal, hn_eq, show k' + 1 ≠ L.length by omega, List.getD, hk']
        dsimp only; rw [hprF _ hq_cap hq_ne]
        simp [show nVal ≠ 0 by omega, show L[k' + 1] = nVal - 1 by omega]; rfl
      · intro y hy hne_p
        have hyL := List.mem_of_mem_erase hy
        have hy_cap := hDLL.2.1 y hyL
        have hy_ne : y ≠ e := (hDLL.1.mem_erase_iff.mp hy).1
        dsimp only; rw [hnxF y hy_cap hy_ne]
        have hnot : ¬(pVal ≠ 0 ∧ y = pVal - 1) := fun ⟨hp_ne, hy_eq⟩ => by
          have hk_pos : 0 < k := by
            by_contra h0; exact hp_ne (by simp [pVal, hp_eq, show k = 0 by omega])
          have hp_val : pVal = L[k - 1]'(by omega) + 1 := by
            simp [pVal, hp_eq, show k ≠ 0 by omega]
          apply hne_p
          have hget : L[k - 1]! = L[k - 1]'(by omega) := getElem!_pos L (k - 1) (by omega)
          simpa [hidx_e, show k ≠ 0 by omega, hget] using (show y = L[k - 1]'(by omega) by omega)
        simp [hnot]
      · intro k' hk' hkpos hLk'
        have hk_eq : k' = k := (hDLL.1.getElem_inj_iff).mp (hLk'.trans hLk.symm)
        subst hk_eq
        have hp_cap := hDLL.2.1 _ (List.getElem_mem (by omega : k' - 1 < L.length))
        have hp_ne : L[k' - 1]'(by omega) ≠ e := fun h => by
          have := hDLL.1.getElem_inj_iff.mp (h.trans hLk.symm); omega
        have hp_val : pVal = L[k' - 1]'(by omega) + 1 := by
          simp [pVal, hp_eq, show k' ≠ 0 by omega]
        dsimp only; rw [hnxF _ hp_cap hp_ne]
        simp [show pVal ≠ 0 by omega, show L[k' - 1]'(by omega) = pVal - 1 by omega]; rfl
    · intro a ha1 ha2 hall
      dsimp only [memF]
      rw [Function.update_of_ne ha2, Function.update_of_ne (hall e heInL).2,
        Function.update_of_ne (hall e heInL).1]
      exact hfr2 a ha1 ha2 hall
  -- Factor the second conditional (`nVal ≠ 0`) across both branches of the first conditional
  have hsecond : ∀ (mem1 : ℕ → ℕ) (regs : ℕ → ℕ) (cp : ℕ),
      regs 0 = headAddr → regs 1 = prevBase → regs 2 = nextBase → regs 3 = cntAddr →
      regs 4 = e → regs 5 = pVal → regs 6 = nVal →
      mem1 cntAddr = L.length →
      (mem1 headAddr = if pVal = 0 then nVal else mem headAddr) →
      (∀ x < cap, x ≠ e →
        mem1 (nextBase + x) = if pVal ≠ 0 ∧ x = pVal - 1 then nVal else mem (nextBase + x)) →
      (∀ x < cap, x ≠ e → mem1 (prevBase + x) = mem (prevBase + x)) →
      (∀ a, a ≠ headAddr → a ≠ cntAddr →
        (∀ x ∈ L, a ≠ prevBase + x ∧ a ≠ nextBase + x) → mem1 a = mem a) →
      cp + 48 ≤ 90 →
      ∃ o st' c, Runs w p ω
          (.cond (.reg 6)
            (.store (.bin .add (.reg 1) (.bin .sub (.reg 6) (.const 1))) (.reg 5)) .nop ;;
           .store (.bin .add (.reg 1) (.reg 4)) (.const 0) ;;
           .store (.bin .add (.reg 2) (.reg 4)) (.const 0) ;;
           .assign 7 (.load (.reg 3)) ;;
           .store (.reg 3) (.bin .sub (.reg 7) (.const 1)) ;;
           .ret (.const 0))
          { mem := mem1, regs := regs, pos := pos } o st' c ∧
        (ghostEraseContract w cap L).post [headAddr, prevBase, nextBase, cntAddr, e] mem o.value st'.mem ∧
        cp + c ≤ 90 := by
    intro mem1 regs cp hr0 hr1 hr2 hr3 hr4 hr5 hr6 hcnt1 hhd1 hnx1 hpr1 hfr1 hcp
    refine runs_seq_cond_le (v := nVal) (by eval_expr) ?_ ?_
    · intro hn_ne
      have hk1 : k + 1 < L.length := by
        by_contra hge; exact hn_ne (by simp [nVal, hn_eq, show k + 1 = L.length by omega])
      have hn_val : nVal = L[k + 1] + 1 := by
        simp [nVal, hn_eq, show k + 1 ≠ L.length by omega, List.getD, hk1]
      have hn_mem : nVal - 1 ∈ L := by
        have : nVal - 1 = L[k + 1] := by omega
        rw [this]; exact List.getElem_mem hk1
      have hn_cap : nVal - 1 < cap := hDLL.2.1 _ hn_mem
      refine runs_seq_store_le (x := prevBase + (nVal - 1)) (v := pVal)
        (by eval_expr) (by eval_expr) ?_
      refine htail _ _ _ hr0 hr1 hr2 hr3 hr4 hr5 hr6 ?_ ?_ ?_ ?_ ?_ (by simp [Expr.size]; omega)
      · dsimp only; rw [Function.update_of_ne (Ne.symm (hdisjP _ hn_cap).2), hcnt1]
      · dsimp only; rw [Function.update_of_ne (Ne.symm (hdisjP _ hn_cap).1), hhd1]
      · intro x hx hxe
        dsimp only; rw [Function.update_of_ne (Ne.symm (hdisjPN _ hn_cap x hx)), hnx1 x hx hxe]
      · intro x hx hxe
        by_cases hxn : x = nVal - 1
        · subst hxn; simp [Function.update_self, hn_ne]
        · dsimp only; rw [Function.update_of_ne (by omega : prevBase + x ≠ prevBase + (nVal - 1))]
          simp [hpr1 x hx hxe, hxn]
      · intro a ha1 ha2 hall
        dsimp only; rw [Function.update_of_ne (hall _ hn_mem).1]; exact hfr1 a ha1 ha2 hall
    · intro hn_0
      refine runs_seq_nop_le ?_
      refine htail _ _ _ hr0 hr1 hr2 hr3 hr4 hr5 hr6 hcnt1 hhd1 hnx1
        (fun x hx hxe => by simp [hpr1 x hx hxe, hn_0]) hfr1
        (by simp [Expr.size]; omega)
  -- Step through the first two loads and first conditional
  refine runs_start_le ?_
  unfold ghostEraseProc
  refine runs_seq_assign_le (v := pVal) (by eval_expr) ?_
  refine runs_seq_assign_le (v := nVal) (by eval_expr) ?_
  refine runs_seq_cond_le (v := pVal) (by eval_expr) ?_ ?_
  · intro hp_ne
    have hk_pos : 0 < k := by
      by_contra h0; exact hp_ne (by simp [pVal, hp_eq, show k = 0 by omega])
    have hp_val : pVal = L[k - 1]'(by omega) + 1 := by
      simp [pVal, hp_eq, show k ≠ 0 by omega]
    have hp_mem : pVal - 1 ∈ L := by
      have : pVal - 1 = L[k - 1]'(by omega) := by omega
      rw [this]; exact List.getElem_mem (by omega)
    have hp_cap : pVal - 1 < cap := hDLL.2.1 _ hp_mem
    refine runs_seq_store_le (x := nextBase + (pVal - 1)) (v := nVal)
      (by eval_expr) (by eval_expr) ?_
    refine hsecond _ _ _ (by simp [startState]) (by simp [startState]) (by simp [startState])
      (by simp [startState]) (by simp [startState]) (by simp) (by simp) ?_ ?_ ?_ ?_ ?_
      (by simp [Expr.size])
    · simp [startState, Function.update_of_ne (Ne.symm (hdisjN _ hp_cap).2), hcnt]
    · simp [startState, hp_ne, Function.update_of_ne (Ne.symm (hdisjN _ hp_cap).1)]
    · intro x hx _
      by_cases hxp : x = pVal - 1
      · subst hxp; simp [startState, Function.update_self, hp_ne]
      · simp [startState, hxp]
    · intro x hx _; simp [startState, Function.update_of_ne (hdisjPN x hx _ hp_cap)]
    · intro a _ _ hall; simp [startState, Function.update_of_ne (hall _ hp_mem).2]
  · intro hp_0
    refine runs_seq_store_le (x := headAddr) (v := nVal) (by eval_expr) (by eval_expr) ?_
    refine hsecond _ _ _ (by simp [startState]) (by simp [startState]) (by simp [startState])
      (by simp [startState]) (by simp [startState]) (by simp) (by simp) ?_ ?_ ?_ ?_ ?_
      (by simp [Expr.size])
    · simp [startState, Function.update_of_ne (Ne.symm hneHC), hcnt]
    · simp [startState, hp_0, Function.update_self]
    · intro x hx _
      simp [startState, Function.update_of_ne (hdisjN x hx).1, hp_0]
    · intro x hx _; simp [startState, Function.update_of_ne (hdisjP x hx).1]
    · intro a ha1 _ _; simp [startState, Function.update_of_ne ha1]

end

end MinCostFlow.SparseCore.Program
