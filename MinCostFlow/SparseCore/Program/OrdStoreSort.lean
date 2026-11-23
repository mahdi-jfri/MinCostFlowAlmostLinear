module

public import MinCostFlow.SparseCore.Program.OrdStoreHeap
public import WordRAM.Tactic
import Mathlib.Tactic

/-!
# In-place Word-RAM heapsort for `(pos, node)` pairs

This file implements `ordSiftDownBody` and `ordHeapSortBody` on an array of `n` pairs `(pos, node)`
stored consecutively at address `arr` (`mem (arr + 2 * i) = pos`, `mem (arr + 2 * i + 1) = node`).
Both procedures are deterministic (`NoRand`), touch only `[arr, arr + 2 * n)` with zero extra
heap scratch, and run in worst-case `O(n * (Nat.log 2 (n + 2) + 1) + 1)` word operations.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM

/-! ### Small `Runs` helpers -/

private theorem ord_runs_assign {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr}
    {st : State} {v : ℕ} (he : e.eval w st = some v) :
    Runs w p ω (.assign r e) st .normal { st with regs := Function.update st.regs r v } (e.size + 1) :=
  runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩

private theorem ord_runs_seq_normal {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt}
    {st st₁ st₂ : State} {o : Outcome} {c₁ c₂ : ℕ}
    (h₁ : Runs w p ω s st .normal st₁ c₁) (h₂ : Runs w p ω t st₁ o st₂ c₂) :
    Runs w p ω (.seq s t) st o st₂ (c₁ + c₂ + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h₁, h₂, rfl⟩)

private theorem ord_runs_seq_run_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt}
    {st st₁ : State} {c₁ k T : ℕ} {Q : Outcome → State → Prop}
    (h₁ : Runs w p ω s st .normal st₁ c₁)
    (hrest : ∃ o st' c, Runs w p ω t st₁ o st' c ∧ Q o st' ∧ (k + c₁ + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq s t) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c, h₂, hq, hc⟩ := hrest
  exact ⟨o, st', c₁ + c + 1, ord_runs_seq_normal h₁ h₂, hq, by omega⟩

private theorem ord_runs_loop_false {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st : State} (he : e.eval w st = some 0) :
    Runs w p ω (.loop e body) st .normal st (e.size + 1) :=
  runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, rfl⟩)

private theorem ord_runs_loop_true {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st st₁ st₂ : State} {o : Outcome} {v c₁ c₂ : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h₁ : Runs w p ω body st .normal st₁ c₁) (h₂ : Runs w p ω (.loop e body) st₁ o st₂ c₂) :
    Runs w p ω (.loop e body) st o st₂ (e.size + c₁ + c₂ + 1) :=
  runs_loop_iff.mpr (Or.inr (Or.inr ⟨v, st₁, c₁, c₂, he, hv, h₁, h₂, rfl⟩))

/-! ### Machine procedures -/

/-- `ordSiftDown` on `[arr, idx, hi]`: sift `idx` down in the max-heap `arr[0 .. hi)`.
Recursive on `selfProc`. Uses zero heap scratch. -/
def ordSiftDownBody (selfProc : ℕ) : Stmt :=
  .assign 3 (.bin .add (.bin .add (.reg 1) (.reg 1)) (.const 1)) ;;
  .cond (.bin .lt (.reg 3) (.reg 2))
    (.assign 4 (.reg 1) ;;
     .assign 5 (.load (.bin .add (.reg 0) (.bin .add (.reg 1) (.reg 1)))) ;;
     .assign 6 (.load (.bin .add (.reg 0) (.bin .add (.reg 3) (.reg 3)))) ;;
     .cond (.bin .lt (.reg 5) (.reg 6))
       (.assign 4 (.reg 3) ;; .assign 5 (.reg 6)) .nop ;;
     .assign 7 (.bin .add (.reg 3) (.const 1)) ;;
     .cond (.bin .lt (.reg 7) (.reg 2))
       (.assign 8 (.load (.bin .add (.reg 0) (.bin .add (.reg 7) (.reg 7)))) ;;
        .cond (.bin .lt (.reg 5) (.reg 8))
          (.assign 4 (.reg 7) ;; .assign 5 (.reg 8)) .nop)
       .nop ;;
     .cond (.bin .eq (.reg 4) (.reg 1))
       (.ret (.const 0))
       (.assign 9 (.bin .add (.reg 0) (.bin .add (.reg 1) (.reg 1))) ;;
        .assign 10 (.bin .add (.reg 0) (.bin .add (.reg 4) (.reg 4))) ;;
        .assign 11 (.load (.reg 9)) ;;
        .assign 12 (.load (.bin .add (.reg 9) (.const 1))) ;;
        .assign 13 (.load (.reg 10)) ;;
        .assign 14 (.load (.bin .add (.reg 10) (.const 1))) ;;
        .store (.reg 9) (.reg 13) ;;
        .store (.bin .add (.reg 9) (.const 1)) (.reg 14) ;;
        .store (.reg 10) (.reg 11) ;;
        .store (.bin .add (.reg 10) (.const 1)) (.reg 12) ;;
        .call 15 selfProc [.reg 0, .reg 4, .reg 2] ;;
        .ret (.const 0)))
    (.ret (.const 0))

theorem ordSiftDownBody_noRand (selfProc : ℕ) : (ordSiftDownBody selfProc).NoRand := by
  simp [ordSiftDownBody, Stmt.NoRand]

/-- `ordHeapSort` on `[arr, n]`: in-place heapsort of `n` pairs `(pos, node)` at `arr`.
`siftProc` is the procedure index of `ordSiftDownBody`. -/
def ordHeapSortBody (siftProc : ℕ) : Stmt :=
  .assign 2 (.reg 1) ;;
  .loop (.reg 2)
    (.assign 2 (.bin .sub (.reg 2) (.const 1)) ;;
     .call 3 siftProc [.reg 0, .reg 2, .reg 1]) ;;
  .assign 4 (.reg 1) ;;
  .loop (.bin .lt (.const 1) (.reg 4))
    (.assign 4 (.bin .sub (.reg 4) (.const 1)) ;;
     .assign 5 (.bin .add (.reg 0) (.bin .add (.reg 4) (.reg 4))) ;;
     .assign 6 (.load (.reg 0)) ;;
     .assign 7 (.load (.bin .add (.reg 0) (.const 1))) ;;
     .assign 8 (.load (.reg 5)) ;;
     .assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
     .store (.reg 0) (.reg 8) ;;
     .store (.bin .add (.reg 0) (.const 1)) (.reg 9) ;;
     .store (.reg 5) (.reg 6) ;;
     .store (.bin .add (.reg 5) (.const 1)) (.reg 7) ;;
     .call 3 siftProc [.reg 0, .const 0, .reg 4]) ;;
  .ret (.const 0)

theorem ordHeapSortBody_noRand (siftProc : ℕ) : (ordHeapSortBody siftProc).NoRand := by
  simp [ordHeapSortBody, Stmt.NoRand]

def ORD_SIFT_STEP_COST : ℕ := 160
def ORD_SORT_COST_MUL : ℕ := 420

/-! ### Run theorem for `ordSiftDownBody` -/

theorem ordSiftDownBody_runs {w : ℕ} {p : Program} {siftProc : ℕ}
    (hself : p.procs[siftProc]? = some (ordSiftDownBody siftProc)) (ω : ℕ → Bool)
    {arr lo hi : ℕ} (hhi_w : arr + 2 * hi + 2 < 2 ^ w) :
    ∀ (m idx pos : ℕ) {mem : ℕ → ℕ},
      siftMeasure idx hi ≤ m → lo ≤ idx → idx < hi →
      HeapExcept (readPairs mem arr hi) lo hi idx →
      HeapGrand (readPairs mem arr hi) lo hi idx →
      ∃ o st' c, Runs w p ω (ordSiftDownBody siftProc)
          (startState [arr, idx, hi] mem pos) o st' c ∧
        (MaxHeapOn (readPairs st'.mem arr hi) lo hi ∧
          (readPairs st'.mem arr hi).Perm (readPairs mem arr hi) ∧
          (∀ a, (a < arr ∨ arr + 2 * hi ≤ a) → st'.mem a = mem a)) ∧
        0 + c ≤ (m + 1) * ORD_SIFT_STEP_COST := by
  intro m
  induction m with
  | zero =>
    intro idx pos mem hm hlo hidx hex hgr
    have hl_ge : ¬ (2 * idx + 1 < hi) := by
      intro hlt; have := siftMeasure_child_lt (Or.inl rfl) hlt; omega
    have hw2 : 1 < 2 ^ w := by omega
    unfold ordSiftDownBody
    rw [startState]
    wram_step; try dsimp only
    refine runs_cond_le (Expr.eval_lt_false (by eval_expr) (by eval_expr) (by omega) hw2)
      (fun h => absurd rfl h) (fun _ => ?_)
    wram_step
    · refine ⟨maxHeapOn_of_except hex (fun h1 => absurd h1 hl_ge)
        (fun h2 => absurd (by omega) hl_ge), List.Perm.refl _, fun _ _ => rfl⟩
    · unfold ORD_SIFT_STEP_COST; wram_cost
  | succ m ih =>
    intro idx pos mem hm hlo hidx hex hgr
    have hw2 : 1 < 2 ^ w := by omega
    have hxs_len : (readPairs mem arr hi).length = hi := readPairs_length mem arr hi
    unfold ordSiftDownBody
    rw [startState]
    wram_step; try dsimp only
    by_cases hlt : idx + idx + 1 < hi
    · have hl_lt : 2 * idx + 1 < hi := by omega
      have hkey_idx : mem (arr + (idx + idx)) = ((readPairs mem arr hi)[idx]'(by omega)).1 := by
        rw [readPairs_getElem]; congr 2; omega
      have hkey_l : mem (arr + (idx + idx + 1 + (idx + idx + 1))) =
          ((readPairs mem arr hi)[2 * idx + 1]'(by omega)).1 := by
        rw [readPairs_getElem]; congr 2; omega
      refine runs_cond_le (Expr.eval_lt_true (by eval_expr) (by eval_expr) hlt hw2)
        (fun _ => ?_) (fun h => absurd h Nat.one_ne_zero)
      wram_step; try dsimp only
      wram_step; try dsimp only
      wram_step; try dsimp only
      set kIdx := mem (arr + (idx + idx)) with hkIdx
      set kL := mem (arr + (idx + idx + 1 + (idx + idx + 1))) with hkL
      have hafterR : ∀ (st₂ : State) (best kBest : ℕ),
          st₂.mem = mem → st₂.regs 0 = arr → st₂.regs 1 = idx → st₂.regs 2 = hi →
          st₂.regs 4 = best →
          (best = idx ∧ kL ≤ kIdx ∧ (∀ hr : 2 * idx + 2 < hi, mem (arr + 2 * (2 * idx + 2)) ≤ kIdx) ∨
           (best = 2 * idx + 1 ∨ best = 2 * idx + 2) ∧ best < hi ∧
             kBest = mem (arr + 2 * best) ∧ kIdx < kBest ∧ kL ≤ kBest ∧
             (∀ hr : 2 * idx + 2 < hi, mem (arr + 2 * (2 * idx + 2)) ≤ kBest)) →
          ∃ o st' c, Runs w p ω
            (.cond (.bin .eq (.reg 4) (.reg 1))
              (.ret (.const 0))
              (.assign 9 (.bin .add (.reg 0) (.bin .add (.reg 1) (.reg 1))) ;;
               .assign 10 (.bin .add (.reg 0) (.bin .add (.reg 4) (.reg 4))) ;;
               .assign 11 (.load (.reg 9)) ;;
               .assign 12 (.load (.bin .add (.reg 9) (.const 1))) ;;
               .assign 13 (.load (.reg 10)) ;;
               .assign 14 (.load (.bin .add (.reg 10) (.const 1))) ;;
               .store (.reg 9) (.reg 13) ;;
               .store (.bin .add (.reg 9) (.const 1)) (.reg 14) ;;
               .store (.reg 10) (.reg 11) ;;
               .store (.bin .add (.reg 10) (.const 1)) (.reg 12) ;;
               .call 15 siftProc [.reg 0, .reg 4, .reg 2] ;;
               .ret (.const 0))) st₂ o st' c ∧
            (MaxHeapOn (readPairs st'.mem arr hi) lo hi ∧
              (readPairs st'.mem arr hi).Perm (readPairs mem arr hi) ∧
              (∀ a, (a < arr ∨ arr + 2 * hi ≤ a) → st'.mem a = mem a)) ∧
            75 + c ≤ (m + 1 + 1) * ORD_SIFT_STEP_COST := by
        intro st₂ best kBest hmem₂ h20 h21 h22 h24 hbest
        rcases hbest with ⟨rfl, hLle, hRle⟩ | ⟨hch, hblt, hkB, hgt, hLle, hRle⟩
        · refine runs_cond_le (Expr.eval_eq_true (Expr.eval_reg_of_eq h24) (Expr.eval_reg_of_eq h21) rfl hw2)
            (fun _ => ?_) (fun h => absurd h Nat.one_ne_zero)
          wram_step
          · rw [hmem₂]
            refine ⟨maxHeapOn_of_except hex ?_ ?_, List.Perm.refl _, fun _ _ => rfl⟩
            · intro _ _ _; rw [← hkey_l, ← hkey_idx]; exact hLle
            · intro h2 _ _; rw [readPairs_getElem, ← hkey_idx]; exact hRle h2
          · unfold ORD_SIFT_STEP_COST
            have : 1 * 160 ≤ (m + 1 + 1) * 160 := Nat.mul_le_mul_right 160 (by omega)
            wram_cost
        · have hne_bi : best ≠ idx := by omega
          refine runs_cond_le (Expr.eval_eq_false (Expr.eval_reg_of_eq h24) (Expr.eval_reg_of_eq h21) hne_bi hw2)
            (fun h => absurd rfl h) (fun _ => ?_)
          have hst2_eq : st₂ = { st₂ with mem := mem } := by cases st₂; dsimp only at hmem₂ ⊢; rw [hmem₂]
          rw [hst2_eq]
          have hr9_eq : arr + (idx + idx) = arr + 2 * idx := by omega
          have hr10_eq : arr + (best + best) = arr + 2 * best := by omega
          refine runs_seq_assign_le (Expr.eval_add (Expr.eval_reg_of_eq h20)
            (Expr.eval_add (Expr.eval_reg_of_eq h21) (Expr.eval_reg_of_eq h21) (by omega)) (by omega)) ?_
          refine runs_seq_assign_le (Expr.eval_add (Expr.eval_reg_of_eq (v := arr) (by simp [h20]))
            (Expr.eval_add (Expr.eval_reg_of_eq (v := best) (by simp [h24]))
              (Expr.eval_reg_of_eq (v := best) (by simp [h24])) (by omega)) (by omega)) ?_
          refine runs_seq_assign_le (Expr.eval_load (Expr.eval_reg_of_eq (v := arr + (idx + idx)) (by simp))) ?_
          refine runs_seq_assign_le (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (v := arr + (idx + idx)) (by simp))
            (Expr.eval_const (by omega)) (by omega))) ?_
          refine runs_seq_assign_le (Expr.eval_load (Expr.eval_reg_of_eq (v := arr + (best + best)) (by simp))) ?_
          refine runs_seq_assign_le (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (v := arr + (best + best)) (by simp))
            (Expr.eval_const (by omega)) (by omega))) ?_
          refine runs_seq_store_le (Expr.eval_reg_of_eq (v := arr + (idx + idx)) (by simp))
            (Expr.eval_reg_of_eq (v := mem (arr + (best + best))) (by simp)) ?_
          refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := arr + (idx + idx)) (by simp))
            (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_reg_of_eq (v := mem (arr + (best + best) + 1)) (by simp)) ?_
          refine runs_seq_store_le (Expr.eval_reg_of_eq (v := arr + (best + best)) (by simp))
            (Expr.eval_reg_of_eq (v := mem (arr + (idx + idx))) (by simp)) ?_
          refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := arr + (best + best)) (by simp))
            (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_reg_of_eq (v := mem (arr + (idx + idx) + 1)) (by simp)) ?_
          dsimp only
          set mSw := Function.update
            (Function.update
              (Function.update
                (Function.update mem (arr + (idx + idx)) (mem (arr + (best + best))))
                (arr + (idx + idx) + 1) (mem (arr + (best + best) + 1)))
              (arr + (best + best)) (mem (arr + (idx + idx))))
            (arr + (best + best) + 1) (mem (arr + (idx + idx) + 1)) with hmSw
          have hsw : readPairs mSw arr hi = swapPairs (readPairs mem arr hi) idx best ∧
              (∀ a, (a < arr ∨ arr + 2 * hi ≤ a) → mSw a = mem a) := by
            have := readPairs_swapMem (mem := mem) (arr := arr) (n := hi) hidx hblt hne_bi.symm
            simpa only [hmSw, hr9_eq, hr10_eq] using this
          have hstep_inv := heap_swap_step (xs := readPairs mem arr hi) (lo := lo) (hi := hi)
            (idx := idx) (best := best) (le_of_eq hxs_len.symm) hlo hidx hch hblt hex hgr
            (by rw [← hkey_idx, readPairs_getElem, ← hkB]; exact hgt)
            (fun h1 => by rw [← hkey_l, readPairs_getElem, ← hkB]; exact hLle)
            (fun h2 => by rw [readPairs_getElem, readPairs_getElem, ← hkB]; exact hRle h2)
          rw [← hsw.1] at hstep_inv
          have hmeas : siftMeasure best hi ≤ m := by
            have := siftMeasure_child_lt hch hblt; omega
          obtain ⟨o₁, st₃, c₁, hrun₁, ⟨hheap₃, hperm₃, hout₃⟩, hc₁⟩ :=
            ih best st₂.pos (mem := mSw) hmeas (by omega) hblt hstep_inv.1 hstep_inv.2
          refine ord_runs_seq_run_le
            (runs_call_iff.mpr ⟨[arr, best, hi], ordSiftDownBody siftProc, o₁, st₃, c₁,
              by eval_expr, hself, hrun₁, rfl, rfl, rfl⟩) ?_
          wram_step
          · refine ⟨hheap₃, hperm₃.trans (hsw.1 ▸ swapPairs_perm (by omega) (by omega)),
              fun a ha => (hout₃ a ha).trans (hsw.2 a ha)⟩
          · have : (m + 1 + 1) * ORD_SIFT_STEP_COST =
                (m + 1) * ORD_SIFT_STEP_COST + ORD_SIFT_STEP_COST := by ring
            rw [this]
            unfold ORD_SIFT_STEP_COST at hc₁ ⊢
            simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
              argsSize_cons, argsSize_nil] at *
            omega
      have hafterL : ∀ (st₁ : State) (b1 k1 : ℕ),
          st₁.mem = mem → st₁.regs 0 = arr → st₁.regs 1 = idx → st₁.regs 2 = hi →
          st₁.regs 3 = idx + idx + 1 → st₁.regs 4 = b1 → st₁.regs 5 = k1 →
          (b1 = idx ∧ k1 = kIdx ∧ kL ≤ kIdx ∨ b1 = 2 * idx + 1 ∧ k1 = kL ∧ kIdx < kL) →
          ∃ o st' c, Runs w p ω
            (.assign 7 (.bin .add (.reg 3) (.const 1)) ;;
             .cond (.bin .lt (.reg 7) (.reg 2))
               (.assign 8 (.load (.bin .add (.reg 0) (.bin .add (.reg 7) (.reg 7)))) ;;
                .cond (.bin .lt (.reg 5) (.reg 8))
                  (.assign 4 (.reg 7) ;; .assign 5 (.reg 8)) .nop)
               .nop ;;
             .cond (.bin .eq (.reg 4) (.reg 1))
               (.ret (.const 0))
               (.assign 9 (.bin .add (.reg 0) (.bin .add (.reg 1) (.reg 1))) ;;
                .assign 10 (.bin .add (.reg 0) (.bin .add (.reg 4) (.reg 4))) ;;
                .assign 11 (.load (.reg 9)) ;;
                .assign 12 (.load (.bin .add (.reg 9) (.const 1))) ;;
                .assign 13 (.load (.reg 10)) ;;
                .assign 14 (.load (.bin .add (.reg 10) (.const 1))) ;;
                .store (.reg 9) (.reg 13) ;;
                .store (.bin .add (.reg 9) (.const 1)) (.reg 14) ;;
                .store (.reg 10) (.reg 11) ;;
                .store (.bin .add (.reg 10) (.const 1)) (.reg 12) ;;
                .call 15 siftProc [.reg 0, .reg 4, .reg 2] ;;
                .ret (.const 0))) st₁ o st' c ∧
            (MaxHeapOn (readPairs st'.mem arr hi) lo hi ∧
              (readPairs st'.mem arr hi).Perm (readPairs mem arr hi) ∧
              (∀ a, (a < arr ∨ arr + 2 * hi ≤ a) → st'.mem a = mem a)) ∧
            45 + c ≤ (m + 1 + 1) * ORD_SIFT_STEP_COST := by
        intro st₁ b1 k1 hmem₁ hr0 hr1 hr2 hr3 hr4 hr5 hb1
        have hst1_eq : st₁ = { st₁ with mem := mem } := by cases st₁; dsimp only at hmem₁ ⊢; rw [hmem₁]
        rw [hst1_eq]
        refine runs_seq_assign_le (Expr.eval_add (Expr.eval_reg_of_eq hr3) (Expr.eval_const (by omega)) (by omega)) ?_
        by_cases hrt : idx + idx + 1 + 1 < hi
        · refine runs_seq_cond_le (Expr.eval_lt_true (Expr.eval_reg_of_eq (v := idx + idx + 1 + 1) (by simp))
              (Expr.eval_reg_of_eq (v := hi) (by simp [hr2])) hrt hw2)
            (fun _ => ?_) (fun h => absurd h Nat.one_ne_zero)
          refine runs_seq_assoc_le ?_
          refine runs_seq_assign_le (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (v := arr) (by simp [hr0]))
            (Expr.eval_add (Expr.eval_reg_of_eq (v := idx + idx + 1 + 1) (by simp))
              (Expr.eval_reg_of_eq (v := idx + idx + 1 + 1) (by simp)) (by omega)) (by omega))) ?_
          set kR := mem (arr + (idx + idx + 1 + 1 + (idx + idx + 1 + 1))) with hkR
          have hkR_eq : kR = mem (arr + 2 * (2 * idx + 2)) := by rw [hkR]; congr 2; omega
          by_cases hkr : k1 < kR
          · refine runs_seq_cond_le
              (Expr.eval_lt_true (Expr.eval_reg_of_eq (v := k1) (by simp [hr5]))
                (Expr.eval_reg_of_eq (v := kR) (by simp [hkR])) hkr hw2)
              (fun _ => ?_) (fun h => absurd h Nat.one_ne_zero)
            refine runs_seq_assoc_le ?_
            refine runs_seq_assign_le (Expr.eval_reg_of_eq (v := idx + idx + 1 + 1) (by simp)) ?_
            refine runs_seq_assign_le (Expr.eval_reg_of_eq (v := kR) (by simp [hkR])) ?_
            refine (fun ⟨o, st', c, hrun, hq, hc⟩ => ⟨o, st', c, hrun, hq, by
              simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load] at *; omega⟩)
              (hafterR _ (idx + idx + 1 + 1) kR rfl
                (by simp [hr0]) (by simp [hr1]) (by simp [hr2]) (by simp) (by
                  right
                  refine ⟨Or.inr (by omega), by omega, by rw [hkR]; congr 2; omega, ?_, ?_, ?_⟩
                  · rcases hb1 with ⟨_, rfl, _⟩ | ⟨_, rfl, h⟩ <;> omega
                  · rcases hb1 with ⟨_, rfl, h⟩ | ⟨_, rfl, _⟩ <;> omega
                  · intro _; rw [← hkR_eq]))
          · refine runs_seq_cond_le
              (Expr.eval_lt_false (Expr.eval_reg_of_eq (v := k1) (by simp [hr5]))
                (Expr.eval_reg_of_eq (v := kR) (by simp [hkR])) (by omega) hw2)
              (fun h => absurd rfl h) (fun _ => ?_)
            refine runs_seq_nop_le ?_
            refine (fun ⟨o, st', c, hrun, hq, hc⟩ => ⟨o, st', c, hrun, hq, by
              simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load] at *; omega⟩)
              (hafterR _ b1 k1 rfl
                (by simp [hr0]) (by simp [hr1]) (by simp [hr2]) (by simp [hr4]) (by
                  rcases hb1 with ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩
                  · left; exact ⟨rfl, h, fun _ => by rw [← hkR_eq]; omega⟩
                  · right
                    refine ⟨Or.inl rfl, by omega, by rw [hkL]; congr 2; omega, h, le_refl _,
                      fun _ => by rw [← hkR_eq]; omega⟩))
        · refine runs_seq_cond_le (Expr.eval_lt_false (Expr.eval_reg_of_eq (v := idx + idx + 1 + 1) (by simp))
              (Expr.eval_reg_of_eq (v := hi) (by simp [hr2])) (by omega) hw2)
            (fun h => absurd rfl h) (fun _ => ?_)
          refine runs_seq_nop_le ?_
          refine (fun ⟨o, st', c, hrun, hq, hc⟩ => ⟨o, st', c, hrun, hq, by
            simp only [Expr.size_bin, Expr.size_reg, Expr.size_const] at *; omega⟩)
            (hafterR _ b1 k1 rfl
              (by simp [hr0]) (by simp [hr1]) (by simp [hr2]) (by simp [hr4]) (by
                rcases hb1 with ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩
                · left; exact ⟨rfl, h, fun hr => absurd (by omega) hrt⟩
                · right
                  refine ⟨Or.inl rfl, by omega, by rw [hkL]; congr 2; omega, h, le_refl _,
                    fun hr => absurd (by omega) hrt⟩))
      by_cases hkl : kIdx < kL
      · refine runs_seq_cond_le (Expr.eval_lt_true (by eval_expr) (by eval_expr) hkl hw2)
          (fun _ => ?_) (fun h => absurd h Nat.one_ne_zero)
        refine runs_seq_assoc_le ?_
        wram_step; try dsimp only
        wram_step; try dsimp only
        refine (fun ⟨o, st', c, hrun, hq, hc⟩ => ⟨o, st', c, hrun, hq, by
          simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load] at *; omega⟩)
          (hafterL _ (idx + idx + 1) kL rfl
            (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
            (Or.inr ⟨by omega, rfl, hkl⟩))
      · refine runs_seq_cond_le (Expr.eval_lt_false (by eval_expr) (by eval_expr) (by omega) hw2)
          (fun h => absurd rfl h) (fun _ => ?_)
        refine runs_seq_nop_le ?_
        refine (fun ⟨o, st', c, hrun, hq, hc⟩ => ⟨o, st', c, hrun, hq, by
          simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load] at *; omega⟩)
          (hafterL _ idx kIdx rfl
            (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
            (Or.inl ⟨rfl, rfl, by omega⟩))
    · refine runs_cond_le (Expr.eval_lt_false (by eval_expr) (by eval_expr) (by omega) hw2)
        (fun h => absurd rfl h) (fun _ => ?_)
      wram_step
      · refine ⟨maxHeapOn_of_except hex (fun h1 => absurd (by omega) hlt)
          (fun h2 => absurd (by omega) hlt), List.Perm.refl _, fun _ _ => rfl⟩
      · unfold ORD_SIFT_STEP_COST
        have : 1 * 160 ≤ (m + 1 + 1) * 160 := Nat.mul_le_mul_right 160 (by omega)
        wram_cost

/-! ### Run theorem for `ordHeapSortBody` -/

theorem ordHeapSortBody_runs {w : ℕ} {p : Program} {siftProc : ℕ}
    (hsift : p.procs[siftProc]? = some (ordSiftDownBody siftProc)) (ω : ℕ → Bool)
    {arr n pos : ℕ} {mem : ℕ → ℕ} (hw : arr + 2 * n + 2 < 2 ^ w) :
    ∃ o st' c, Runs w p ω (ordHeapSortBody siftProc) (startState [arr, n] mem pos) o st' c ∧
      ((readPairs st'.mem arr n).Pairwise (fun a b => a.1 ≤ b.1) ∧
        (readPairs st'.mem arr n).Perm (readPairs mem arr n) ∧
        (∀ a, (a < arr ∨ arr + 2 * n ≤ a) → st'.mem a = mem a)) ∧
      0 + c ≤ ORD_SORT_COST_MUL * (n * (Nat.log 2 (n + 2) + 1) + 1) := by
  have hw2 : 1 < 2 ^ w := by omega
  set L := Nat.log 2 (n + 1) with hL
  have hL_le : L ≤ Nat.log 2 (n + 2) := Nat.log_mono_right (by omega)
  have hphase1 : ∀ (i : ℕ) (st : State),
      i ≤ n → st.regs 0 = arr → st.regs 1 = n → st.regs 2 = i →
      MaxHeapOn (readPairs st.mem arr n) i n →
      (readPairs st.mem arr n).Perm (readPairs mem arr n) →
      (∀ a, (a < arr ∨ arr + 2 * n ≤ a) → st.mem a = mem a) →
      ∃ st₁ c₁, Runs w p ω (.loop (.reg 2)
          (.assign 2 (.bin .sub (.reg 2) (.const 1)) ;;
           .call 3 siftProc [.reg 0, .reg 2, .reg 1])) st .normal st₁ c₁ ∧
        st₁.regs 0 = arr ∧ st₁.regs 1 = n ∧
        MaxHeapOn (readPairs st₁.mem arr n) 0 n ∧
        (readPairs st₁.mem arr n).Perm (readPairs mem arr n) ∧
        (∀ a, (a < arr ∨ arr + 2 * n ≤ a) → st₁.mem a = mem a) ∧
        c₁ ≤ i * ((L + 1) * ORD_SIFT_STEP_COST + 20) + 5 := by
    intro i
    induction i with
    | zero =>
      intro st _ hr0 hr1 hr2 hheap hperm hout
      refine ⟨st, 2, ord_runs_loop_false (Expr.eval_reg_of_eq hr2), hr0, hr1, hheap, hperm, hout, by omega⟩
    | succ i ih =>
      intro st hi hr0 hr1 hr2 hheap hperm hout
      have hst_sub : (Expr.bin .sub (.reg 2) (.const 1)).eval w st = some i := by
        have h1 := Expr.eval_sub (Expr.eval_reg_of_eq hr2) (Expr.eval_const (by omega)) (by omega)
        simpa [Nat.add_sub_cancel] using h1
      have hstep_inv := maxHeapOn_suffix_step hheap
      have hmeas : siftMeasure i n ≤ L := Nat.sub_le _ _
      obtain ⟨o₁, stA, cA, hrunA, ⟨hheapA, hpermA, houtA⟩, hcA⟩ :=
        ordSiftDownBody_runs hsift ω hw L i st.pos hmeas (le_refl i) (by omega)
          hstep_inv.1 hstep_inv.2
      let st_mid : State := { st with regs := Function.update st.regs 2 i }
      have hrun_assign : Runs w p ω (.assign 2 (.bin .sub (.reg 2) (.const 1))) st .normal st_mid 4 :=
        ord_runs_assign hst_sub
      have hrun_call : Runs w p ω (.call 3 siftProc [.reg 0, .reg 2, .reg 1]) st_mid .normal
          { stA with regs := Function.update st_mid.regs 3 o₁.value }
          (argsSize [.reg 0, .reg 2, .reg 1] + cA + 1) := by
        refine runs_call_iff.mpr ⟨[arr, i, n], ordSiftDownBody siftProc, o₁, stA, cA, ?_, hsift,
          hrunA, rfl, rfl, rfl⟩
        have r0 : st_mid.regs 0 = arr := by simp [st_mid, hr0]
        have r2 : st_mid.regs 2 = i := by simp [st_mid]
        have r1 : st_mid.regs 1 = n := by simp [st_mid, hr1]
        eval_expr
      have hbody := ord_runs_seq_normal hrun_assign hrun_call
      obtain ⟨st₁, c₁, hloop, h10, h11, h1heap, h1perm, h1out, hc₁⟩ :=
        ih { stA with regs := Function.update st_mid.regs 3 o₁.value } (by omega)
          (by simp [st_mid, hr0]) (by simp [st_mid, hr1]) (by simp [st_mid])
          hheapA (hpermA.trans hperm) (fun a ha => (houtA a ha).trans (hout a ha))
      refine ⟨st₁, _, ord_runs_loop_true (Expr.eval_reg_of_eq hr2) (by omega) hbody hloop,
        h10, h11, h1heap, h1perm, h1out, ?_⟩
      simp only [argsSize_cons, argsSize_nil, Expr.size_reg] at *
      have hmul : (i + 1) * ((L + 1) * ORD_SIFT_STEP_COST + 20) =
          i * ((L + 1) * ORD_SIFT_STEP_COST + 20) + ((L + 1) * ORD_SIFT_STEP_COST + 20) := by ring
      omega
  have hphase2 : ∀ (e : ℕ) (st : State),
      e ≤ n → st.regs 0 = arr → st.regs 4 = e →
      MaxHeapOn (readPairs st.mem arr e) 0 e →
      ((readPairs st.mem arr n).drop e).Pairwise (fun a b => a.1 ≤ b.1) →
      (∀ a ∈ (readPairs st.mem arr n).take e, ∀ b ∈ (readPairs st.mem arr n).drop e, a.1 ≤ b.1) →
      (readPairs st.mem arr n).Perm (readPairs mem arr n) →
      (∀ a, (a < arr ∨ arr + 2 * n ≤ a) → st.mem a = mem a) →
      ∃ st₂ c₂, Runs w p ω (.loop (.bin .lt (.const 1) (.reg 4))
          (.assign 4 (.bin .sub (.reg 4) (.const 1)) ;;
           .assign 5 (.bin .add (.reg 0) (.bin .add (.reg 4) (.reg 4))) ;;
           .assign 6 (.load (.reg 0)) ;;
           .assign 7 (.load (.bin .add (.reg 0) (.const 1))) ;;
           .assign 8 (.load (.reg 5)) ;;
           .assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
           .store (.reg 0) (.reg 8) ;;
           .store (.bin .add (.reg 0) (.const 1)) (.reg 9) ;;
           .store (.reg 5) (.reg 6) ;;
           .store (.bin .add (.reg 5) (.const 1)) (.reg 7) ;;
           .call 3 siftProc [.reg 0, .const 0, .reg 4])) st .normal st₂ c₂ ∧
        (readPairs st₂.mem arr n).Pairwise (fun a b => a.1 ≤ b.1) ∧
        (readPairs st₂.mem arr n).Perm (readPairs mem arr n) ∧
        (∀ a, (a < arr ∨ arr + 2 * n ≤ a) → st₂.mem a = mem a) ∧
        c₂ ≤ e * ((L + 1) * ORD_SIFT_STEP_COST + 65) + 10 := by
    intro e
    induction e with
    | zero =>
      intro st _ hr0 hr4 _ hsorted _ hperm hout
      have hcond : (Expr.bin .lt (.const 1) (.reg 4)).eval w st = some 0 :=
        Expr.eval_lt_false (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr4) (by omega) hw2
      refine ⟨st, _, ord_runs_loop_false hcond, by simpa using hsorted, hperm, hout,
        by simp only [Expr.size_bin, Expr.size_const, Expr.size_reg]; omega⟩
    | succ e ih =>
      intro st he hr0 hr4 hheap hsorted hpart hperm hout
      by_cases he0 : e = 0
      · subst he0
        have hcond : (Expr.bin .lt (.const 1) (.reg 4)).eval w st = some 0 :=
          Expr.eval_lt_false (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr4) (by omega) hw2
        have hpw : (readPairs st.mem arr n).Pairwise (fun a b => a.1 ≤ b.1) := by
          cases hxs : readPairs st.mem arr n with
          | nil => exact List.Pairwise.nil
          | cons a tl =>
            rw [hxs] at hsorted hpart
            simp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
              List.mem_singleton, forall_eq] at hsorted hpart
            exact List.pairwise_cons.mpr ⟨hpart, hsorted⟩
        refine ⟨st, _, ord_runs_loop_false hcond, hpw, hperm, hout,
          by simp only [Expr.size_bin, Expr.size_const, Expr.size_reg]; omega⟩
      · have hcond : (Expr.bin .lt (.const 1) (.reg 4)).eval w st = some 1 :=
          Expr.eval_lt_true (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr4) (by omega) hw2
        have htake_eq : ∀ m k, k ≤ n → (readPairs m arr n).take k = readPairs m arr k := by
          intro m k hk
          apply List.ext_getElem
          · simp [readPairs_length]; omega
          · intro j hj _
            simp [List.getElem_take, readPairs_getElem]
        have hheap_n : MaxHeapOn (readPairs st.mem arr n) 0 (e + 1) := by
          intro j hj
          have hjp := hheap j hj
          constructor
          · intro h1 h1' hj'
            have := hjp.1 h1 (by rw [readPairs_length]; exact h1) (by rw [readPairs_length]; omega)
            simp only [readPairs_getElem] at this ⊢
            exact this
          · intro h2 h2' hj'
            have := hjp.2 h2 (by rw [readPairs_length]; exact h2) (by rw [readPairs_length]; omega)
            simp only [readPairs_getElem] at this ⊢
            exact this
        have hextr := extract_step_inv (readPairs_length st.mem arr n) he hheap_n hsorted hpart
        have hgoal : ∃ o stA cA, Runs w p ω
            (.assign 4 (.bin .sub (.reg 4) (.const 1)) ;;
             .assign 5 (.bin .add (.reg 0) (.bin .add (.reg 4) (.reg 4))) ;;
             .assign 6 (.load (.reg 0)) ;;
             .assign 7 (.load (.bin .add (.reg 0) (.const 1))) ;;
             .assign 8 (.load (.reg 5)) ;;
             .assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
             .store (.reg 0) (.reg 8) ;;
             .store (.bin .add (.reg 0) (.const 1)) (.reg 9) ;;
             .store (.reg 5) (.reg 6) ;;
             .store (.bin .add (.reg 5) (.const 1)) (.reg 7) ;;
             .call 3 siftProc [.reg 0, .const 0, .reg 4]) st o stA cA ∧
            (o = .normal ∧ stA.regs 0 = arr ∧ stA.regs 4 = e ∧
              MaxHeapOn (readPairs stA.mem arr e) 0 e ∧
              ((readPairs stA.mem arr n).drop e).Pairwise (fun a b => a.1 ≤ b.1) ∧
              (∀ a ∈ (readPairs stA.mem arr n).take e, ∀ b ∈ (readPairs stA.mem arr n).drop e, a.1 ≤ b.1) ∧
              (readPairs stA.mem arr n).Perm (readPairs mem arr n) ∧
              (∀ a, (a < arr ∨ arr + 2 * n ≤ a) → stA.mem a = mem a)) ∧
            0 + cA ≤ (L + 1) * ORD_SIFT_STEP_COST + 60 := by
          refine runs_seq_assign_le (by
            have h1 := Expr.eval_sub (Expr.eval_reg_of_eq hr4) (Expr.eval_const (by omega)) (by omega)
            simpa [Nat.add_sub_cancel] using h1) ?_
          refine runs_seq_assign_le (Expr.eval_add (Expr.eval_reg_of_eq (v := arr) (by simp [hr0]))
            (Expr.eval_add (Expr.eval_reg_of_eq (v := e) (by simp))
              (Expr.eval_reg_of_eq (v := e) (by simp)) (by omega)) (by omega)) ?_
          refine runs_seq_assign_le (Expr.eval_load (Expr.eval_reg_of_eq (v := arr) (by simp [hr0]))) ?_
          refine runs_seq_assign_le (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (v := arr) (by simp [hr0]))
            (Expr.eval_const (by omega)) (by omega))) ?_
          refine runs_seq_assign_le (Expr.eval_load (Expr.eval_reg_of_eq (v := arr + (e + e)) (by simp))) ?_
          refine runs_seq_assign_le (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (v := arr + (e + e)) (by simp))
            (Expr.eval_const (by omega)) (by omega))) ?_
          refine runs_seq_store_le (Expr.eval_reg_of_eq (v := arr) (by simp [hr0]))
            (Expr.eval_reg_of_eq (v := st.mem (arr + (e + e))) (by simp)) ?_
          refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := arr) (by simp [hr0]))
            (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_reg_of_eq (v := st.mem (arr + (e + e) + 1)) (by simp)) ?_
          refine runs_seq_store_le (Expr.eval_reg_of_eq (v := arr + (e + e)) (by simp))
            (Expr.eval_reg_of_eq (v := st.mem arr) (by simp)) ?_
          refine runs_seq_store_le (Expr.eval_add (Expr.eval_reg_of_eq (v := arr + (e + e)) (by simp))
            (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_reg_of_eq (v := st.mem (arr + 1)) (by simp)) ?_
          dsimp only
          set mSw := Function.update
            (Function.update
              (Function.update
                (Function.update st.mem arr (st.mem (arr + (e + e))))
                (arr + 1) (st.mem (arr + (e + e) + 1)))
              (arr + (e + e)) (st.mem arr))
            (arr + (e + e) + 1) (st.mem (arr + 1)) with hmSw
          have hsw : readPairs mSw arr n = swapPairs (readPairs st.mem arr n) 0 e ∧
              (∀ a, (a < arr ∨ arr + 2 * n ≤ a) → mSw a = st.mem a) := by
            have h0eq : arr + 2 * 0 = arr := by omega
            have heeq : arr + 2 * e = arr + (e + e) := by omega
            have := readPairs_swapMem (mem := st.mem) (arr := arr) (n := n) (by omega) (by omega) (Ne.symm he0)
            simpa only [hmSw, h0eq, heeq] using this
          have hinv_e := hextr.2.2 (by omega)
          rw [← hsw.1, htake_eq mSw e (by omega)] at hinv_e
          have hmeas : siftMeasure 0 e ≤ L := by
            unfold siftMeasure
            have : Nat.log 2 (e + 1) ≤ Nat.log 2 (n + 1) := Nat.log_mono_right (by omega)
            omega
          obtain ⟨o₁, stB, cB, hrunB, ⟨hheapB, hpermB, houtB⟩, hcB⟩ :=
            ordSiftDownBody_runs hsift ω (by omega : arr + 2 * e + 2 < 2 ^ w)
              L 0 st.pos (mem := mSw) hmeas (le_refl 0) (by omega) hinv_e.1 hinv_e.2
          refine ⟨.normal, _, _,
            runs_call_iff.mpr ⟨[arr, 0, e], ordSiftDownBody siftProc, o₁, stB, cB,
              by eval_expr, hsift, hrunB, rfl, rfl, rfl⟩, ?_, ?_⟩
          · have hdrop_same : (readPairs stB.mem arr n).drop e = (readPairs mSw arr n).drop e := by
              apply List.ext_getElem (by simp [readPairs_length])
              intro k hk _
              simp only [List.getElem_drop, readPairs_getElem]
              rw [houtB (arr + 2 * (e + k)) (Or.inr (by omega)),
                  houtB (arr + 2 * (e + k) + 1) (Or.inr (by omega))]
            have htake_perm : ((readPairs stB.mem arr n).take e).Perm ((readPairs mSw arr n).take e) := by
              rw [htake_eq _ e (by omega), htake_eq _ e (by omega)]
              exact hpermB
            have hfull_perm : (readPairs stB.mem arr n).Perm (readPairs mSw arr n) := by
              rw [← List.take_append_drop e (readPairs stB.mem arr n),
                  ← List.take_append_drop e (readPairs mSw arr n), hdrop_same]
              exact htake_perm.append_right _
            refine ⟨rfl, by simp [hr0], by simp, hheapB, ?_, ?_, ?_, ?_⟩
            · rw [hdrop_same, hsw.1]; exact hextr.1
            · intro a ha b hb
              rw [hdrop_same, hsw.1] at hb
              exact hextr.2.1 a (hsw.1 ▸ htake_perm.mem_iff.mp ha) b hb
            · exact hfull_perm.trans (hsw.1 ▸ (swapPairs_perm (by rw [readPairs_length]; omega)
                (by rw [readPairs_length]; omega)).trans hperm)
            · intro a ha
              exact (houtB a (by rcases ha with h | h; exact Or.inl h; exact Or.inr (by omega))).trans
                ((hsw.2 a ha).trans (hout a ha))
          · simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
              argsSize_cons, argsSize_nil] at *
            omega
        obtain ⟨o, stA, cA, hbody, ⟨rfl, hA0, hA4, hAheap, hAsort, hApart, hAperm, hAout⟩, hcA⟩ := hgoal
        obtain ⟨st₂, c₂, hloop, h2sort, h2perm, h2out, hc₂⟩ :=
          ih stA (by omega) hA0 hA4 hAheap hAsort hApart hAperm hAout
        refine ⟨st₂, _, ord_runs_loop_true hcond (by decide) hbody hloop, h2sort, h2perm, h2out, ?_⟩
        simp only [Expr.size_bin, Expr.size_const, Expr.size_reg] at *
        have hmul : (e + 1) * ((L + 1) * ORD_SIFT_STEP_COST + 65) =
            e * ((L + 1) * ORD_SIFT_STEP_COST + 65) + ((L + 1) * ORD_SIFT_STEP_COST + 65) := by ring
        omega
  unfold ordHeapSortBody
  rw [startState]
  wram_step; try dsimp only
  have hinit_heap : MaxHeapOn (readPairs mem arr n) n n := fun j hj =>
    ⟨fun h1 => absurd h1 (by omega), fun h2 => absurd h2 (by omega)⟩
  obtain ⟨st₁, c₁, hrun₁, h10, h11, h1heap, h1perm, h1out, hc₁⟩ :=
    hphase1 n { mem := mem, regs := Function.update (fun i => [arr, n].getD i 0) 2 n, pos := pos }
      (le_refl n) (by simp) (by simp) (by simp) hinit_heap (List.Perm.refl _) (fun _ _ => rfl)
  refine ord_runs_seq_run_le hrun₁ ?_
  wram_step; try dsimp only
  obtain ⟨st₂, c₂, hrun₂, h2sort, h2perm, h2out, hc₂⟩ :=
    hphase2 n { st₁ with regs := Function.update st₁.regs 4 n }
      (le_refl n) (by simp [h10]) (by simp) h1heap
      (by rw [List.drop_eq_nil_of_le (le_of_eq (readPairs_length _ _ _))]; exact List.Pairwise.nil)
      (by intro _ _ b hb; rw [List.drop_eq_nil_of_le (le_of_eq (readPairs_length _ _ _))] at hb; exact absurd hb (List.not_mem_nil))
      h1perm h1out
  refine ord_runs_seq_run_le hrun₂ ?_
  wram_step
  · exact ⟨h2sort, h2perm, h2out⟩
  · have hbound : n * ((L + 1) * ORD_SIFT_STEP_COST + 20) +
        n * ((L + 1) * ORD_SIFT_STEP_COST + 65) + 50 ≤
        ORD_SORT_COST_MUL * (n * (Nat.log 2 (n + 2) + 1) + 1) := by
      unfold ORD_SIFT_STEP_COST ORD_SORT_COST_MUL
      have h1 : (L + 1) * 160 + 20 + ((L + 1) * 160 + 65) ≤ 420 * (Nat.log 2 (n + 2) + 1) := by omega
      have h2 := Nat.mul_le_mul_left n h1
      nlinarith
    simp only [Expr.size_reg, Expr.size_const] at *
    omega

end MinCostFlow.SparseCore.Program
