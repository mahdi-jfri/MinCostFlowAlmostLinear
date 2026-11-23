module

public import MinCostFlow.SparseCore.Program.OrdStoreDropEdge
public import MinCostFlow.SparseCore.Program.OrdStoreInsert
public import MinCostFlow.SparseCore.Program.OrdStoreRotateTo
public import MinCostFlow.SparseCore.Program.OrdStoreMoveEnds
import Mathlib.Tactic

/-!
# Order Store Edit Batch Procedure (`op 0`)

This file implements and verifies `ordStoreEditBody` on `[b, edits, words, heap]`, applying the
encoded edit batch `OrdEditsAt mem edits (readOrdEdits mem edits) words`. To avoid any aliasing
between the input edit buffer and the store footprint, the procedure first copies `edits[0..words-1]`
to `heap[0..words-1]`, executes each edit using `heap + words` as scratch for `moveEnds`, clears
`heap[0..words-1]` back to zero, and returns `heap`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState MinCostFlow.DynSpanner.Program

def ORD_EDIT_MUL : ℕ := 32000

/-- Copy `r2` words from `r1` to `r3`. -/
def ordCopyLoop : Stmt :=
  .loop (.bin .lt (.reg 4) (.reg 2))
    (.assign 5 (.load (.bin .add (.reg 1) (.reg 4))) ;;
     .store (.bin .add (.reg 3) (.reg 4)) (.reg 5) ;;
     .assign 4 (.bin .add (.reg 4) (.const 1)))

/-- Zero `r2` words starting at `r3`. -/
def ordZeroRangeLoop : Stmt :=
  .loop (.bin .lt (.reg 4) (.reg 2))
    (.store (.bin .add (.reg 3) (.reg 4)) (.const 0) ;;
     .assign 4 (.bin .add (.reg 4) (.const 1)))

/-- Dispatch loop for `ordStoreEdit`: executes `r4` edits starting at `r5`, with scratch at `r6`. -/
def ordEditDispatchLoop (dropProc insProc rotProc moveProc : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 7) (.reg 4))
    (.assign 8 (.load (.reg 5)) ;;
     .cond (.bin .eq (.reg 8) (.const 0))
       (.assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
        .call 14 dropProc [.reg 0, .reg 9] ;;
        .assign 5 (.bin .add (.reg 5) (.const 2)))
       (.cond (.bin .lt (.reg 8) (.const 3))
         (.assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
          .assign 10 (.load (.bin .add (.reg 5) (.const 2))) ;;
          .assign 11 (.load (.bin .add (.reg 5) (.const 3))) ;;
          .assign 12 (.bin .sub (.reg 8) (.const 1)) ;;
          .assign 13 (.bin .add (.reg 5) (.const 4)) ;;
          .call 14 moveProc [.reg 0, .reg 9, .reg 10, .reg 12, .reg 11, .reg 13, .reg 6] ;;
          .assign 5 (.bin .add (.reg 13) (.reg 11)))
         (.cond (.bin .eq (.reg 8) (.const 3))
           (.assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
            .assign 10 (.load (.bin .add (.reg 5) (.const 2))) ;;
            .assign 11 (.load (.bin .add (.reg 5) (.const 3))) ;;
            .call 14 insProc [.reg 0, .reg 9, .reg 10, .reg 11] ;;
            .assign 5 (.bin .add (.reg 5) (.const 4)))
           (.assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
            .assign 10 (.load (.bin .add (.reg 5) (.const 2))) ;;
            .call 14 rotProc [.reg 0, .reg 9, .reg 10] ;;
            .assign 5 (.bin .add (.reg 5) (.const 3))))) ;;
     .assign 7 (.bin .add (.reg 7) (.const 1)))

/-- `ordStoreEdit` (`op 0`) on `[b, edits, words, heap]`. -/
def ordStoreEditBody (dropProc insProc rotProc moveProc : ℕ) : Stmt :=
  .assign 4 (.const 0) ;;
  ordCopyLoop ;;
  .assign 4 (.load (.reg 3)) ;;
  .assign 5 (.bin .add (.reg 3) (.const 1)) ;;
  .assign 6 (.bin .add (.reg 3) (.reg 2)) ;;
  .assign 7 (.const 0) ;;
  ordEditDispatchLoop dropProc insProc rotProc moveProc ;;
  .assign 4 (.const 0) ;;
  ordZeroRangeLoop ;;
  .ret (.reg 3)

theorem ordStoreEditBody_noRand (dP iP rP mP : ℕ) : (ordStoreEditBody dP iP rP mP).NoRand := by
  simp [ordStoreEditBody, ordCopyLoop, ordZeroRangeLoop, ordEditDispatchLoop, Stmt.NoRand]

/-! ### Helper lemmas for copy, zero, and shifted edit decoding -/

private theorem readList_shift {m₁ m₂ : ℕ → ℕ} {a₁ a₂ n : ℕ}
    (h : ∀ i < n, m₂ (a₂ + i) = m₁ (a₁ + i)) :
    readList m₂ a₂ n = readList m₁ a₁ n := by
  apply List.ext_getElem (by simp [readList_length])
  intro i hi _
  have hi' : i < n := by rw [readList_length] at hi; exact hi
  rw [readList_getElem, readList_getElem]; exact h i hi'

private theorem decodeOrdEdit_shift {m₁ m₂ : ℕ → ℕ} {a₁ a₂ : ℕ}
    (h : ∀ i < (decodeOrdEdit m₁ a₁).2, m₂ (a₂ + i) = m₁ (a₁ + i)) :
    decodeOrdEdit m₂ a₂ = decodeOrdEdit m₁ a₁ := by
  have hge2 := decodeOrdEdit_words_ge_two m₁ a₁
  have h0 : m₂ a₂ = m₁ a₁ := by simpa using h 0 (by omega)
  have h1 : m₂ (a₂ + 1) = m₁ (a₁ + 1) := h 1 (by omega)
  unfold decodeOrdEdit
  by_cases ht0 : m₁ a₁ = 0
  · simp [h0, ht0, h1]
  · by_cases ht12 : m₁ a₁ = 1 ∨ m₁ a₁ = 2
    · have hw : (decodeOrdEdit m₁ a₁).2 = 4 + m₁ (a₁ + 3) := by
        rcases ht12 with ht1 | ht2
        · simp [decodeOrdEdit, ht0, ht1]
        · simp [decodeOrdEdit, ht0, ht2]
      have h2 : m₂ (a₂ + 2) = m₁ (a₁ + 2) := h 2 (by omega)
      have h3 : m₂ (a₂ + 3) = m₁ (a₁ + 3) := h 3 (by omega)
      have hrl : readList m₂ (a₂ + 4) (m₁ (a₁ + 3)) = readList m₁ (a₁ + 4) (m₁ (a₁ + 3)) :=
        readList_shift fun i hi => by
          have := h (4 + i) (by omega); rwa [← Nat.add_assoc, ← Nat.add_assoc] at this
      simp [h0, ht0, ht12, h1, h2, h3, hrl]
    · by_cases ht3 : m₁ a₁ = 3
      · have hw : (decodeOrdEdit m₁ a₁).2 = 4 := by simp [decodeOrdEdit, ht0, ht12, ht3]
        have h2 : m₂ (a₂ + 2) = m₁ (a₁ + 2) := h 2 (by omega)
        have h3 : m₂ (a₂ + 3) = m₁ (a₁ + 3) := h 3 (by omega)
        simp [h0, ht0, ht12, ht3, h1, h2, h3]
      · have hw : (decodeOrdEdit m₁ a₁).2 = 3 := by simp [decodeOrdEdit, ht0, ht12, ht3]
        have h2 : m₂ (a₂ + 2) = m₁ (a₁ + 2) := h 2 (by omega)
        simp [h0, ht0, ht12, ht3, h1, h2]

private theorem decodeOrdEdits_shift {m₁ m₂ : ℕ → ℕ} :
    ∀ count a₁ a₂,
      (∀ i < ((decodeOrdEdits m₁ count a₁).2).sum, m₂ (a₂ + i) = m₁ (a₁ + i)) →
      decodeOrdEdits m₂ count a₂ = decodeOrdEdits m₁ count a₁
  | 0, _, _, _ => rfl
  | count + 1, a₁, a₂, h => by
    simp only [decodeOrdEdits, List.sum_cons] at h ⊢
    have hd : decodeOrdEdit m₂ a₂ = decodeOrdEdit m₁ a₁ :=
      decodeOrdEdit_shift fun i hi => h i (by omega)
    have hrest : decodeOrdEdits m₂ count (a₂ + (decodeOrdEdit m₂ a₂).2) =
        decodeOrdEdits m₁ count (a₁ + (decodeOrdEdit m₁ a₁).2) := by
      rw [hd]
      exact decodeOrdEdits_shift count (a₁ + (decodeOrdEdit m₁ a₁).2) (a₂ + (decodeOrdEdit m₁ a₁).2)
        fun i hi => by
          have := h ((decodeOrdEdit m₁ a₁).2 + i) (by omega)
          rwa [← Nat.add_assoc, ← Nat.add_assoc] at this
    rw [hrest, hd]

private theorem ordCopyLoop_runs {w src dst words : ℕ} {p : Program} (ω : ℕ → Bool) {st0 : State}
    (hsrc_le : src + words ≤ dst) (hdst_w : dst + words < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hr1 : st0.regs 1 = src) (hr2 : st0.regs 2 = words) (hr3 : st0.regs 3 = dst) (hr4 : st0.regs 4 = 0) :
    ∃ st' c, Runs w p ω ordCopyLoop st0 .normal st' c ∧
      (∀ r, r ≠ 4 → r ≠ 5 → st'.regs r = st0.regs r) ∧
      (∀ i < words, st'.mem (dst + i) = st0.mem (src + i)) ∧
      (∀ a, ¬ (dst ≤ a ∧ a < dst + words) → st'.mem a = st0.mem a) ∧
      c ≤ 35 * words + 15 := by
  have hloop : ∀ rem (i : ℕ) (st : State),
      i + rem = words →
      st.regs 1 = src → st.regs 2 = words → st.regs 3 = dst → st.regs 4 = i →
      (∀ t < i, st.mem (dst + t) = st0.mem (src + t)) →
      (∀ a, ¬ (dst ≤ a ∧ a < dst + words) → st.mem a = st0.mem a) →
      ∃ st' c, Runs w p ω ordCopyLoop st .normal st' c ∧
        (∀ r, r ≠ 4 → r ≠ 5 → st'.regs r = st.regs r) ∧
        (∀ t < words, st'.mem (dst + t) = st0.mem (src + t)) ∧
        (∀ a, ¬ (dst ≤ a ∧ a < dst + words) → st'.mem a = st0.mem a) ∧
        c ≤ 35 * rem + 15 := by
    intro rem
    induction rem with
    | zero =>
      intro i st hi r1 r2 r3 r4 hcp hout
      have hi_eq : i = words := by omega
      subst hi_eq
      have hc : (Expr.bin .lt (.reg 4) (.reg 2)).eval w st = some 0 :=
        Expr.eval_lt_false (Expr.eval_reg_of_eq r4) (Expr.eval_reg_of_eq r2) (by omega) (by omega)
      refine ⟨st, _, ord_runs_loop_false hc, fun _ _ _ => rfl, hcp, hout, by simp [Expr.size_bin, Expr.size_reg]⟩
    | succ rem ih =>
      intro i st hi r1 r2 r3 r4 hcp hout
      have hc : (Expr.bin .lt (.reg 4) (.reg 2)).eval w st = some 1 :=
        Expr.eval_lt_true (Expr.eval_reg_of_eq r4) (Expr.eval_reg_of_eq r2) (by omega) (by omega)
      have ha5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 1) (.reg 4)))) st .normal
          { st with regs := Function.update st.regs 5 (st0.mem (src + i)) } _ :=
        runs_assign_iff.mpr ⟨st0.mem (src + i), Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r1)
          (Expr.eval_reg_of_eq r4) (by omega)) (hout (src + i) (by omega)), rfl, rfl, rfl⟩
      set st1 : State := { st with regs := Function.update st.regs 5 (st0.mem (src + i)) }
      have hs1 : Runs w p ω (.store (.bin .add (.reg 3) (.reg 4)) (.reg 5)) st1 .normal
          { st1 with mem := Function.update st.mem (dst + i) (st0.mem (src + i)) } _ :=
        runs_store_iff.mpr ⟨dst + i, st0.mem (src + i), Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1, r3]))
          (Expr.eval_reg_of_eq (by simp [st1, r4])) (by omega), Expr.eval_reg_of_eq (by simp [st1]), rfl, rfl, rfl⟩
      set st2 : State := { st1 with mem := Function.update st.mem (dst + i) (st0.mem (src + i)) }
      have ha4 : Runs w p ω (.assign 4 (.bin .add (.reg 4) (.const 1))) st2 .normal
          { st2 with regs := Function.update st2.regs 4 (i + 1) } _ :=
        runs_assign_iff.mpr ⟨i + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2, st1, r4]))
          (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
      set st3 : State := { st2 with regs := Function.update st2.regs 4 (i + 1) }
      obtain ⟨stF, cF, hrunF, hregF, hcpF, houtF, hcF⟩ :=
        ih (i + 1) st3 (by omega) (by simp [st3, st2, st1, r1]) (by simp [st3, st2, st1, r2])
          (by simp [st3, st2, st1, r3]) (by simp [st3])
          (fun t ht => by
            dsimp only [st3, st2]
            by_cases hti : t = i
            · subst hti; simp
            · rw [Function.update_of_ne (by omega)]; exact hcp t (by omega))
          (fun a ha => by dsimp only [st3, st2]; rw [Function.update_of_ne (by omega)]; exact hout a ha)
      refine ⟨stF, _, ord_runs_loop_true hc Nat.one_ne_zero
        (ord_runs_seq_normal ha5 (ord_runs_seq_normal hs1 ha4)) hrunF,
        fun r h4 h5 => by rw [hregF r h4 h5]; simp [st3, st2, st1, h4, h5], hcpF, houtF, ?_⟩
      simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
      omega
  exact hloop words 0 st0 (by omega) hr1 hr2 hr3 hr4 (fun _ ht => by omega) (fun _ _ => rfl)

private theorem ordZeroRangeLoop_runs {w dst words : ℕ} {p : Program} (ω : ℕ → Bool) {st0 : State}
    (hz : ZeroFrom st0.mem (dst + words)) (hdst_w : dst + words < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hr2 : st0.regs 2 = words) (hr3 : st0.regs 3 = dst) (hr4 : st0.regs 4 = 0) :
    ∃ st' c, Runs w p ω ordZeroRangeLoop st0 .normal st' c ∧
      (∀ r, r ≠ 4 → st'.regs r = st0.regs r) ∧
      ZeroFrom st'.mem dst ∧
      (∀ a < dst, st'.mem a = st0.mem a) ∧
      c ≤ 25 * words + 15 := by
  have hloop : ∀ rem (i : ℕ) (st : State),
      i + rem = words →
      st.regs 2 = words → st.regs 3 = dst → st.regs 4 = i →
      (∀ a, dst ≤ a → a < dst + i → st.mem a = 0) →
      ZeroFrom st.mem (dst + words) →
      (∀ a < dst, st.mem a = st0.mem a) →
      ∃ st' c, Runs w p ω ordZeroRangeLoop st .normal st' c ∧
        (∀ r, r ≠ 4 → st'.regs r = st.regs r) ∧
        ZeroFrom st'.mem dst ∧
        (∀ a < dst, st'.mem a = st0.mem a) ∧
        c ≤ 25 * rem + 15 := by
    intro rem
    induction rem with
    | zero =>
      intro i st hi r2 r3 r4 hpre hpost hlt
      have hi_eq : i = words := by omega
      subst hi_eq
      have hc : (Expr.bin .lt (.reg 4) (.reg 2)).eval w st = some 0 :=
        Expr.eval_lt_false (Expr.eval_reg_of_eq r4) (Expr.eval_reg_of_eq r2) (by omega) (by omega)
      refine ⟨st, _, ord_runs_loop_false hc, fun _ _ => rfl,
        fun a ha => by by_cases h : a < dst + i; exact hpre a ha h; exact hpost a (by omega),
        hlt, by simp [Expr.size_bin, Expr.size_reg]⟩
    | succ rem ih =>
      intro i st hi r2 r3 r4 hpre hpost hlt
      have hc : (Expr.bin .lt (.reg 4) (.reg 2)).eval w st = some 1 :=
        Expr.eval_lt_true (Expr.eval_reg_of_eq r4) (Expr.eval_reg_of_eq r2) (by omega) (by omega)
      have hs1 : Runs w p ω (.store (.bin .add (.reg 3) (.reg 4)) (.const 0)) st .normal
          { st with mem := Function.update st.mem (dst + i) 0 } _ :=
        runs_store_iff.mpr ⟨dst + i, 0, Expr.eval_add (Expr.eval_reg_of_eq r3) (Expr.eval_reg_of_eq r4) (by omega),
          Expr.eval_const (by omega), rfl, rfl, rfl⟩
      set st1 : State := { st with mem := Function.update st.mem (dst + i) 0 }
      have ha4 : Runs w p ω (.assign 4 (.bin .add (.reg 4) (.const 1))) st1 .normal
          { st1 with regs := Function.update st1.regs 4 (i + 1) } _ :=
        runs_assign_iff.mpr ⟨i + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1, r4]))
          (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
      set st2 : State := { st1 with regs := Function.update st1.regs 4 (i + 1) }
      obtain ⟨stF, cF, hrunF, hregF, hzF, hltF, hcF⟩ :=
        ih (i + 1) st2 (by omega) (by simp [st2, st1, r2]) (by simp [st2, st1, r3]) (by simp [st2])
          (fun a ha1 ha2 => by
            dsimp only [st2, st1]
            by_cases h : a = dst + i; · rw [h, Function.update_self]
            · rw [Function.update_of_ne h]; exact hpre a ha1 (by omega))
          (fun a ha => by dsimp only [st2, st1]; rw [Function.update_of_ne (by omega)]; exact hpost a ha)
          (fun a ha => by dsimp only [st2, st1]; rw [Function.update_of_ne (by omega)]; exact hlt a ha)
      refine ⟨stF, _, ord_runs_loop_true hc Nat.one_ne_zero (ord_runs_seq_normal hs1 ha4) hrunF,
        fun r h4 => by rw [hregF r h4]; simp [st2, st1, h4], hzF, hltF, ?_⟩
      simp only [Expr.size_bin, Expr.size_reg, Expr.size_const] at *
      omega
  exact hloop words 0 st0 (by omega) hr2 hr3 hr4 (fun _ ha1 ha2 => by omega) hz (fun _ _ => rfl)

/-! ### Main `ordStoreEditBody` verification -/

theorem ordStoreEditBody_runs
    {w b edits words heap pos rotProc stepProc splayProc splayRootProc
      siftProc sortProc walkProc joinProc unlinkProc allocProc freeTreeProc
      dropProc insProc rotToProc moveProc : ℕ} {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc))
    (hsplayRoot : p.procs[splayRootProc]? = some (ordSplayRootBody splayProc))
    (hsift : p.procs[siftProc]? = some (ordSiftDownBody siftProc))
    (hsort : p.procs[sortProc]? = some (ordHeapSortBody siftProc))
    (hwalk : p.procs[walkProc]? = some (ordWalkExtremeBody splayProc))
    (hjoin : p.procs[joinProc]? = some (ordJoinBody walkProc))
    (hunlink : p.procs[unlinkProc]? = some (ordUnlinkBody splayProc joinProc))
    (halloc : p.procs[allocProc]? = some ordAllocBody)
    (hfree : p.procs[freeTreeProc]? = some ordFreeTreeBody)
    (hdrop : p.procs[dropProc]? = some (ordDropEdgeBody unlinkProc freeTreeProc))
    (hins : p.procs[insProc]? = some (ordInsertBeforeBody allocProc splayRootProc joinProc))
    (hrotTo : p.procs[rotToProc]? = some (ordRotateToBody splayRootProc joinProc))
    (hmove : p.procs[moveProc]? = some (ordMoveEndsBody splayRootProc sortProc unlinkProc joinProc freeTreeProc))
    (ω : ℕ → Bool) {mem : ℕ → ℕ} {ord : ℕ → List End} {S : OrdStoreState}
    (hinv : OrdInv ord S) (harena : OrdArenaAt b S mem)
    (hedits : OrdEditsAt mem edits (readOrdEdits mem edits) words)
    (hedits_le : edits + words ≤ heap)
    (hwithin : OrdEditsWithin S.vCap S.eCap (readOrdEdits mem edits))
    (huniq_all : OrdEditsUniqueWithin S.vCap S.eCap ord (readOrdEdits mem edits))
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ heap)
    (hz : ZeroFrom mem heap) (hw : heap + (3 * words + 2) < 2 ^ w) :
    ∃ o st' c, Runs w p ω (ordStoreEditBody dropProc insProc rotToProc moveProc)
        (startState [b, edits, words, heap] mem pos) o st' c ∧
      o.value = heap ∧
      (∃ S' : OrdStoreState,
        OrdInv (applyOrdEdits ord (readOrdEdits mem edits)) S' ∧
        OrdArenaAt b S' st'.mem ∧
        OrdFrame b S.vCap S.eCap heap mem st'.mem ∧
        S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
        c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' ≤
          ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S +
            ORD_EDIT_MUL * (words + 1) * ordStoreLog S.eCap) := by
  have hlog : 1 ≤ ordStoreLog S.eCap := ordStoreLog_pos S.eCap
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ heap := hfoot
  have hwide : 16 ≤ 2 ^ w := by omega
  set st0 : State := startState [b, edits, words, heap] mem pos
  -- Step 1: Copy edits[0..words-1] to heap[0..words-1]
  have ha4a : Runs w p ω (.assign 4 (.const 0)) st0 .normal
      { st0 with regs := Function.update st0.regs 4 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 4 0 }
  obtain ⟨st2, cCp, hrunCp, hregCp, hcp_mem, hcp_out, hcCp⟩ :=
    ordCopyLoop_runs (p := p) ω (st0 := st1) hedits_le (by omega) hwide
      (by simp [st1, st0, startState]) (by simp [st1, st0, startState])
      (by simp [st1, st0, startState]) (by simp [st1])
  have harena2 : OrdArenaAt b S st2.mem :=
    harena.congr hinv.next_le fun a ha => hcp_out a (by unfold ordFoot at ha; omega)
  have hz2 : ZeroFrom st2.mem (heap + words) := fun a ha => (hcp_out a (by omega)).trans (hz a (by omega))
  have hcount_eq : st2.mem heap = mem edits := by
    have hwords_pos : 0 < words := by have := hedits.2.1; omega
    simpa [st1, st0, startState] using hcp_mem 0 hwords_pos
  have hdec_eq : decodeOrdEdits st2.mem (mem edits) (heap + 1) = decodeOrdEdits mem (mem edits) (edits + 1) := by
    apply decodeOrdEdits_shift
    intro i hi
    have hwords_eq := hedits.2.1
    have := hcp_mem (1 + i) (by omega)
    rwa [← Nat.add_assoc, ← Nat.add_assoc] at this
  have ha4b : Runs w p ω (.assign 4 (.load (.reg 3))) st2 .normal
      { st2 with regs := Function.update st2.regs 4 (mem edits) } _ :=
    runs_assign_iff.mpr ⟨mem edits, Expr.eval_load_of_eq
      (Expr.eval_reg_of_eq (by rw [hregCp 3 (by decide) (by decide)]; simp [st1, st0, startState]))
      hcount_eq, rfl, rfl, rfl⟩
  set st3 : State := { st2 with regs := Function.update st2.regs 4 (mem edits) }
  have ha5b : Runs w p ω (.assign 5 (.bin .add (.reg 3) (.const 1))) st3 .normal
      { st3 with regs := Function.update st3.regs 5 (heap + 1) } _ :=
    runs_assign_iff.mpr ⟨heap + 1, Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st3, hregCp 3 (by decide) (by decide), st1, st0, startState]))
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  set st4 : State := { st3 with regs := Function.update st3.regs 5 (heap + 1) }
  have ha6b : Runs w p ω (.assign 6 (.bin .add (.reg 3) (.reg 2))) st4 .normal
      { st4 with regs := Function.update st4.regs 6 (heap + words) } _ :=
    runs_assign_iff.mpr ⟨heap + words, Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st4, st3, hregCp 3 (by decide) (by decide), st1, st0, startState]))
      (Expr.eval_reg_of_eq (by simp [st4, st3, hregCp 2 (by decide) (by decide), st1, st0, startState]))
      (by omega), rfl, rfl, rfl⟩
  set st5 : State := { st4 with regs := Function.update st4.regs 6 (heap + words) }
  have ha7b : Runs w p ω (.assign 7 (.const 0)) st5 .normal
      { st5 with regs := Function.update st5.regs 7 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set st6 : State := { st5 with regs := Function.update st5.regs 7 0 }
  have hcount_le : mem edits ≤ words := by
    have h1 := decodeOrdEdits_words_ge_two_mul mem (mem edits) (edits + 1)
    have h2 := hedits.2.1; omega
  -- Step 2: Dispatch loop over remaining edits in st2.mem[heap + 1 .. heap + words - 1]
  have hdisp : ∀ rem (i ptr : ℕ) (st : State) (Si : OrdStoreState) (curOrd : ℕ → List End),
      i + rem = mem edits →
      heap + 1 ≤ ptr →
      ptr + ((decodeOrdEdits st2.mem rem ptr).2).sum ≤ heap + words →
      OrdEditsWithin S.vCap S.eCap (decodeOrdEdits st2.mem rem ptr).1 →
      OrdEditsUniqueWithin S.vCap S.eCap curOrd (decodeOrdEdits st2.mem rem ptr).1 →
      OrdInv curOrd Si → OrdArenaAt b Si st.mem → Si.vCap = S.vCap → Si.eCap = S.eCap →
      ZeroFrom st.mem (heap + words) →
      (∀ a, heap ≤ a → a < heap + words → st.mem a = st2.mem a) →
      (∀ a < heap, ¬ ordFoot b S.vCap S.eCap a → st.mem a = mem a) →
      st.regs 0 = b → st.regs 2 = words → st.regs 3 = heap →
      st.regs 4 = mem edits → st.regs 5 = ptr → st.regs 6 = heap + words → st.regs 7 = i →
      ∃ st' c, ∃ S' : OrdStoreState,
        Runs w p ω (ordEditDispatchLoop dropProc insProc rotToProc moveProc) st .normal st' c ∧
        st'.regs 2 = words ∧ st'.regs 3 = heap ∧
        OrdInv (applyOrdEdits curOrd (decodeOrdEdits st2.mem rem ptr).1) S' ∧
        OrdArenaAt b S' st'.mem ∧
        S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
        ZeroFrom st'.mem (heap + words) ∧
        (∀ a < heap, ¬ ordFoot b S.vCap S.eCap a → st'.mem a = mem a) ∧
        c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' ≤
          ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT Si +
            31000 * ((decodeOrdEdits st2.mem rem ptr).2).sum * ordStoreLog S.eCap + 20 := by
    intro rem
    induction rem with
    | zero =>
      intro i ptr st Si curOrd hi _ _ _ _ hinvi harenai hvi hei hzi hbuf hlt r0 r2 r3 r4 r5 r6 r7
      have hi_eq : i = mem edits := by omega
      subst hi_eq
      have hcond : (Expr.bin .lt (.reg 7) (.reg 4)).eval w st = some 0 :=
        Expr.eval_lt_false (Expr.eval_reg_of_eq r7) (Expr.eval_reg_of_eq r4) (by omega) (by omega)
      refine ⟨st, _, Si, ord_runs_loop_false hcond, r2, r3, hinvi, harenai, hvi, hei, hzi, hlt,
        by simp [Expr.size_bin, Expr.size_reg, decodeOrdEdits]; omega⟩
    | succ rem ih =>
      intro i ptr st Si curOrd hi hptr_ge hptr_le hwi huniqi hinvi harenai hvi hei hzi hbuf hlt
        r0 r2 r3 r4 r5 r6 r7
      have hcond : (Expr.bin .lt (.reg 7) (.reg 4)).eval w st = some 1 :=
        Expr.eval_lt_true (Expr.eval_reg_of_eq r7) (Expr.eval_reg_of_eq r4) (by omega) (by omega)
      set d := decodeOrdEdit st2.mem ptr with hd_def
      set rest := decodeOrdEdits st2.mem rem (ptr + d.2) with hrest_def
      have hdec_cons : decodeOrdEdits st2.mem (rem + 1) ptr = (d.1 :: rest.1, d.2 :: rest.2) := rfl
      have hsum_cons : ((decodeOrdEdits st2.mem (rem + 1) ptr).2).sum = d.2 + rest.2.sum := by
        rw [hdec_cons]; simp
      have hd_ge2 : 2 ≤ d.2 := decodeOrdEdit_words_ge_two st2.mem ptr
      have hw_hd : match d.1 with
          | .dropEdge e => e < S.eCap
          | .moveEnds v v' sel _ => v < S.vCap ∧ v' < S.vCap ∧ ∀ x ∈ sel, x.1 < S.eCap
          | .insertBefore v x y => v < S.vCap ∧ x.1 < S.eCap ∧ ∀ y' ∈ y, y'.1 < S.eCap
          | .rotateTo v y => v < S.vCap ∧ y.1 < S.eCap :=
        hwi d.1 (by rw [hdec_cons]; exact List.mem_cons_self)
      have hw_tl : OrdEditsWithin S.vCap S.eCap rest.1 := fun e he =>
        hwi e (by rw [hdec_cons]; exact List.mem_cons_of_mem d.1 he)
      have huniq_hd : OrdUniqueWithin S.vCap S.eCap (applyOrdEdit curOrd d.1) :=
        (OrdEditsUniqueWithin.head (by rw [hdec_cons] at huniqi; exact huniqi)).2
      have huniq_tl : OrdEditsUniqueWithin S.vCap S.eCap (applyOrdEdit curOrd d.1) rest.1 :=
        OrdEditsUniqueWithin.tail (by rw [hdec_cons] at huniqi; exact huniqi)
      set tag := st2.mem ptr with htag_def
      have hm_tag : st.mem ptr = tag := hbuf ptr (by omega) (by omega)
      have ha8 : Runs w p ω (.assign 8 (.load (.reg 5))) st .normal
          { st with regs := Function.update st.regs 8 tag } _ :=
        runs_assign_iff.mpr ⟨tag, Expr.eval_load_of_eq (Expr.eval_reg_of_eq r5) hm_tag, rfl, rfl, rfl⟩
      set stA : State := { st with regs := Function.update st.regs 8 tag }
      -- Execute one edit according to tag
      have hstep_edit : ∃ stB cB, ∃ S1 : OrdStoreState,
          Runs w p ω
            (.cond (.bin .eq (.reg 8) (.const 0))
              (.assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
               .call 14 dropProc [.reg 0, .reg 9] ;;
               .assign 5 (.bin .add (.reg 5) (.const 2)))
              (.cond (.bin .lt (.reg 8) (.const 3))
                (.assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
                 .assign 10 (.load (.bin .add (.reg 5) (.const 2))) ;;
                 .assign 11 (.load (.bin .add (.reg 5) (.const 3))) ;;
                 .assign 12 (.bin .sub (.reg 8) (.const 1)) ;;
                 .assign 13 (.bin .add (.reg 5) (.const 4)) ;;
                 .call 14 moveProc [.reg 0, .reg 9, .reg 10, .reg 12, .reg 11, .reg 13, .reg 6] ;;
                 .assign 5 (.bin .add (.reg 13) (.reg 11)))
                (.cond (.bin .eq (.reg 8) (.const 3))
                  (.assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
                   .assign 10 (.load (.bin .add (.reg 5) (.const 2))) ;;
                   .assign 11 (.load (.bin .add (.reg 5) (.const 3))) ;;
                   .call 14 insProc [.reg 0, .reg 9, .reg 10, .reg 11] ;;
                   .assign 5 (.bin .add (.reg 5) (.const 4)))
                  (.assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
                   .assign 10 (.load (.bin .add (.reg 5) (.const 2))) ;;
                   .call 14 rotToProc [.reg 0, .reg 9, .reg 10] ;;
                   .assign 5 (.bin .add (.reg 5) (.const 3)))))) stA .normal stB cB ∧
          stB.regs 0 = b ∧ stB.regs 2 = words ∧ stB.regs 3 = heap ∧
          stB.regs 4 = mem edits ∧ stB.regs 5 = ptr + d.2 ∧ stB.regs 6 = heap + words ∧ stB.regs 7 = i ∧
          OrdInv (applyOrdEdit curOrd d.1) S1 ∧ OrdArenaAt b S1 stB.mem ∧
          S1.vCap = S.vCap ∧ S1.eCap = S.eCap ∧
          ZeroFrom stB.mem (heap + words) ∧
          (∀ a, heap ≤ a → a < heap + words → stB.mem a = st2.mem a) ∧
          (∀ a < heap, ¬ ordFoot b S.vCap S.eCap a → stB.mem a = mem a) ∧
          cB + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S1 ≤
            ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT Si + 31000 * d.2 * ordStoreLog S.eCap - 40 := by
        by_cases ht0 : tag = 0
        · have hc0 : (Expr.bin .eq (.reg 8) (.const 0)).eval w stA = some 1 :=
            Expr.eval_eq_true (Expr.eval_reg_of_eq (v := 0) (by simp [stA, ht0]))
              (Expr.eval_const (by omega)) rfl (by omega)
          have hd_eq : d = (.dropEdge (st2.mem (ptr + 1)), 2) := by simp [hd_def, decodeOrdEdit, ← htag_def, ht0]
          have hd1 : d.1 = .dropEdge (st2.mem (ptr + 1)) := by rw [hd_eq]
          have hd2 : d.2 = 2 := by rw [hd_eq]
          have he_lt : st2.mem (ptr + 1) < S.eCap := by rw [hd1] at hw_hd; exact hw_hd
          have ha9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 5) (.const 1)))) stA .normal
              { stA with regs := Function.update stA.regs 9 (st2.mem (ptr + 1)) } _ :=
            runs_assign_iff.mpr ⟨st2.mem (ptr + 1), Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [stA, r5])) (Expr.eval_const (by omega)) (by omega))
              (hbuf (ptr + 1) (by omega) (by omega)), rfl, rfl, rfl⟩
          set st1' : State := { stA with regs := Function.update stA.regs 9 (st2.mem (ptr + 1)) }
          obtain ⟨oD, stD, cD, hrunD, S1, hinv1, harena1, hfr1, hv1, he1, hphi1⟩ :=
            ordDropEdgeBody_runs hrot hstep hsplay hwalk hjoin hunlink hfree ω
              (e := st2.mem (ptr + 1)) hinvi harenai
              (by omega) (by rw [hvi, hei]; omega) hzi (by omega) hwide (pos := st1'.pos)
          have hcallD : Runs w p ω (.call 14 dropProc [.reg 0, .reg 9]) st1' .normal
              { stD with regs := Function.update st1'.regs 14 oD.value } (argsSize [.reg 0, .reg 9] + cD + 1) :=
            runs_call_iff.mpr ⟨[b, st2.mem (ptr + 1)], ordDropEdgeBody unlinkProc freeTreeProc, oD, stD, cD,
              evalArgs_cons (Expr.eval_reg_of_eq (by simp [st1', stA, r0]))
                (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st1'])) (evalArgs_nil _ _)),
              hdrop, hrunD, rfl, rfl, rfl⟩
          set st2' : State := { stD with regs := Function.update st1'.regs 14 oD.value }
          have ha5' : Runs w p ω (.assign 5 (.bin .add (.reg 5) (.const 2))) st2' .normal
              { st2' with regs := Function.update st2'.regs 5 (ptr + 2) } _ :=
            runs_assign_iff.mpr ⟨ptr + 2, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2', st1', stA, r5]))
              (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
          refine ⟨_, _, S1, ord_runs_cond_true hc0 Nat.one_ne_zero (ord_runs_seq_normal ha9 (ord_runs_seq_normal hcallD ha5')),
            by simp [st2', st1', stA, r0], by simp [st2', st1', stA, r2], by simp [st2', st1', stA, r3],
            by simp [st2', st1', stA, r4], by simp [hd2], by simp [st2', st1', stA, r6], by simp [st2', st1', stA, r7],
            hd1 ▸ hinv1, harena1, hv1.trans hvi, he1.trans hei, hfr1.1,
            fun a ha1 ha2 => (hfr1.2 a ha2 (by rw [hvi, hei]; unfold ordFoot; omega)).trans (hbuf a ha1 ha2),
            fun a ha hnf => (hfr1.2 a (by omega) (by rw [hvi, hei]; exact hnf)).trans (hlt a ha hnf), ?_⟩
          rw [hei] at hphi1; rw [hd2]
          unfold ORD_DROP_AMORT at hphi1
          simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil] at *
          have h100 : 100 ≤ 40000 * ordStoreLog S.eCap := by have := Nat.le_mul_of_pos_right 40000 hlog; omega
          have : 31000 * 2 * ordStoreLog S.eCap = 22000 * ordStoreLog S.eCap + 40000 * ordStoreLog S.eCap := by ring
          omega
        · have hc0 : (Expr.bin .eq (.reg 8) (.const 0)).eval w stA = some 0 :=
            Expr.eval_eq_false (Expr.eval_reg_of_eq (v := tag) (by simp [stA]))
              (Expr.eval_const (by omega)) ht0 (by omega)
          by_cases ht12 : tag < 3
          · have h12 : tag = 1 ∨ tag = 2 := by omega
            have hc12 : (Expr.bin .lt (.reg 8) (.const 3)).eval w stA = some 1 :=
              Expr.eval_lt_true (Expr.eval_reg_of_eq (v := tag) (by simp [stA]))
                (Expr.eval_const (by omega)) ht12 (by omega)
            set v := st2.mem (ptr + 1)
            set v' := st2.mem (ptr + 2)
            set len := st2.mem (ptr + 3)
            set comp : Bool := decide (tag = 2)
            have hcomp_w : tag - 1 = if comp then 1 else 0 := by rcases h12 with h | h <;> simp [comp, h]
            have hd_eq : d = (.moveEnds v v' ((readList st2.mem (ptr + 4) len).map endOfKey).toFinset comp, 4 + len) := by
              simp [hd_def, decodeOrdEdit, ← htag_def, ht0, h12, v, v', len, comp]
            have hd1 : d.1 = .moveEnds v v' ((readList st2.mem (ptr + 4) len).map endOfKey).toFinset comp := by rw [hd_eq]
            have hd2 : d.2 = 4 + len := by rw [hd_eq]
            have hrl_eq : readList st.mem (ptr + 4) len = readList st2.mem (ptr + 4) len :=
              readList_shift fun j hj => hbuf (ptr + 4 + j) (by omega) (by omega)
            have hv_lt : v < S.vCap := by rw [hd1] at hw_hd; exact hw_hd.1
            have hv'_lt : v' < S.vCap := by rw [hd1] at hw_hd; exact hw_hd.2.1
            have harr_w : ∀ j < len, st.mem (ptr + 4 + j) < 2 ^ w := fun j hj => by
              rw [hd1] at hw_hd
              have hm : endOfKey (st2.mem (ptr + 4 + j)) ∈ ((readList st2.mem (ptr + 4) len).map endOfKey).toFinset := by
                rw [List.mem_toFinset, List.mem_map]
                refine ⟨st2.mem (ptr + 4 + j), ?_, rfl⟩
                have h1 := readList_getElem st2.mem (ptr + 4) len j (by rw [readList_length]; exact hj)
                rw [← h1]; exact List.getElem_mem (by rw [readList_length]; exact hj)
              have hlt_e := hw_hd.2.2 _ hm
              have hk_lt := key_lt_two_mul_of_endOfKey hlt_e
              rw [hbuf (ptr + 4 + j) (by omega) (by omega)]; omega
            have ha9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 5) (.const 1)))) stA .normal
                { stA with regs := Function.update stA.regs 9 v } _ :=
              runs_assign_iff.mpr ⟨v, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [stA, r5]))
                (Expr.eval_const (by omega)) (by omega)) (hbuf (ptr + 1) (by omega) (by omega)), rfl, rfl, rfl⟩
            set st1' : State := { stA with regs := Function.update stA.regs 9 v }
            have ha10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 5) (.const 2)))) st1' .normal
                { st1' with regs := Function.update st1'.regs 10 v' } _ :=
              runs_assign_iff.mpr ⟨v', Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1', stA, r5]))
                (Expr.eval_const (by omega)) (by omega)) (hbuf (ptr + 2) (by omega) (by omega)), rfl, rfl, rfl⟩
            set st2' : State := { st1' with regs := Function.update st1'.regs 10 v' }
            have ha11 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 5) (.const 3)))) st2' .normal
                { st2' with regs := Function.update st2'.regs 11 len } _ :=
              runs_assign_iff.mpr ⟨len, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2', st1', stA, r5]))
                (Expr.eval_const (by omega)) (by omega)) (hbuf (ptr + 3) (by omega) (by omega)), rfl, rfl, rfl⟩
            set st3' : State := { st2' with regs := Function.update st2'.regs 11 len }
            have ha12 : Runs w p ω (.assign 12 (.bin .sub (.reg 8) (.const 1))) st3' .normal
                { st3' with regs := Function.update st3'.regs 12 (if comp then 1 else 0) } _ :=
              runs_assign_iff.mpr ⟨if comp then 1 else 0, by
                have h1 : (Expr.bin .sub (.reg 8) (.const 1)).eval w st3' = some (tag - 1) :=
                  Expr.eval_sub (Expr.eval_reg_of_eq (by simp [st3', st2', st1', stA]))
                    (Expr.eval_const (by omega)) (by omega)
                rwa [hcomp_w] at h1, rfl, rfl, rfl⟩
            set st4' : State := { st3' with regs := Function.update st3'.regs 12 (if comp then 1 else 0) }
            have ha13 : Runs w p ω (.assign 13 (.bin .add (.reg 5) (.const 4))) st4' .normal
                { st4' with regs := Function.update st4'.regs 13 (ptr + 4) } _ :=
              runs_assign_iff.mpr ⟨ptr + 4, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4', st3', st2', st1', stA, r5]))
                (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
            set st5' : State := { st4' with regs := Function.update st4'.regs 13 (ptr + 4) }
            obtain ⟨oM, stM, cM, hrunM, S1, hinv1, harena1, hfr1, hv1, he1, hphi1⟩ :=
              ordMoveEndsBody_runs hrot hstep hsplay hsplayRoot hsift hsort hwalk hjoin hunlink hfree ω
                hinvi harenai (by rw [hvi]; exact hv_lt) (by rw [hvi]; exact hv'_lt)
                (by rw [hvi, hei, hrl_eq, ← hd1]; exact huniq_hd)
                (by omega) (fun a ha1 _ hf => by rw [hvi, hei] at hf; unfold ordFoot at hf; omega)
                harr_w (by rw [hvi, hei]; omega) hzi (by omega) hwide (pos := st5'.pos)
            have hcallM : Runs w p ω (.call 14 moveProc [.reg 0, .reg 9, .reg 10, .reg 12, .reg 11, .reg 13, .reg 6]) st5' .normal
                { stM with regs := Function.update st5'.regs 14 oM.value }
                (argsSize [.reg 0, .reg 9, .reg 10, .reg 12, .reg 11, .reg 13, .reg 6] + cM + 1) :=
              runs_call_iff.mpr ⟨[b, v, v', if comp then 1 else 0, len, ptr + 4, heap + words],
                ordMoveEndsBody splayRootProc sortProc unlinkProc joinProc freeTreeProc, oM, stM, cM,
                evalArgs_cons (Expr.eval_reg_of_eq (by simp [st5', st4', st3', st2', st1', stA, r0]))
                  (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st5', st4', st3', st2', st1']))
                    (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st5', st4', st3', st2']))
                      (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st5', st4']))
                        (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st5', st4', st3']))
                          (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st5']))
                            (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st5', st4', st3', st2', st1', stA, r6]))
                              (evalArgs_nil _ _))))))),
                hmove, hrunM, rfl, rfl, rfl⟩
            set st6' : State := { stM with regs := Function.update st5'.regs 14 oM.value }
            have ha5' : Runs w p ω (.assign 5 (.bin .add (.reg 13) (.reg 11))) st6' .normal
                { st6' with regs := Function.update st6'.regs 5 (ptr + 4 + len) } _ :=
              runs_assign_iff.mpr ⟨ptr + 4 + len, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st6', st5']))
                (Expr.eval_reg_of_eq (by simp [st6', st5', st4', st3'])) (by omega), rfl, rfl, rfl⟩
            refine ⟨_, _, S1,
              ord_runs_cond_false hc0 (ord_runs_cond_true hc12 Nat.one_ne_zero
                (ord_runs_seq_normal ha9 (ord_runs_seq_normal ha10 (ord_runs_seq_normal ha11
                  (ord_runs_seq_normal ha12 (ord_runs_seq_normal ha13 (ord_runs_seq_normal hcallM ha5'))))))),
              by simp [st6', st5', st4', st3', st2', st1', stA, r0],
              by simp [st6', st5', st4', st3', st2', st1', stA, r2],
              by simp [st6', st5', st4', st3', st2', st1', stA, r3],
              by simp [st6', st5', st4', st3', st2', st1', stA, r4],
              by simp [hd2]; omega,
              by simp [st6', st5', st4', st3', st2', st1', stA, r6],
              by simp [st6', st5', st4', st3', st2', st1', stA, r7],
              by rw [hd1, ← hrl_eq]; exact hinv1, harena1, hv1.trans hvi, he1.trans hei, hfr1.1,
              fun a ha1 ha2 => (hfr1.2 a ha2 (by rw [hvi, hei]; unfold ordFoot; omega)).trans (hbuf a ha1 ha2),
              fun a ha hnf => (hfr1.2 a (by omega) (by rw [hvi, hei]; exact hnf)).trans (hlt a ha hnf), ?_⟩
            rw [hei] at hphi1; rw [hd2]
            unfold ORD_MOVE_AMORT at hphi1
            simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil] at *
            have h1 : 30000 * ((len + 1) * ordStoreLog S.eCap) =
                30000 * (len * ordStoreLog S.eCap) + 30000 * ordStoreLog S.eCap := by ring
            have h2 : 31000 * (4 + len) * ordStoreLog S.eCap =
                31000 * (len * ordStoreLog S.eCap) + 124000 * ordStoreLog S.eCap := by ring
            have h90 : 200 ≤ 94000 * ordStoreLog S.eCap := by have := Nat.le_mul_of_pos_right 94000 hlog; omega
            omega
          · have hc12 : (Expr.bin .lt (.reg 8) (.const 3)).eval w stA = some 0 :=
              Expr.eval_lt_false (Expr.eval_reg_of_eq (v := tag) (by simp [stA]))
                (Expr.eval_const (by omega)) (by omega) (by omega)
            have hnot12 : ¬ (tag = 1 ∨ tag = 2) := by omega
            by_cases ht3 : tag = 3
            · have hc3 : (Expr.bin .eq (.reg 8) (.const 3)).eval w stA = some 1 :=
                Expr.eval_eq_true (Expr.eval_reg_of_eq (v := 3) (by simp [stA, ht3]))
                  (Expr.eval_const (by omega)) rfl (by omega)
              set v := st2.mem (ptr + 1)
              set keyX := st2.mem (ptr + 2)
              set yWord := st2.mem (ptr + 3)
              have hd_eq : d = (.insertBefore v (endOfKey keyX) (if yWord = 0 then none else some (endOfKey (yWord - 1))), 4) := by
                simp [hd_def, decodeOrdEdit, ← htag_def, ht0, hnot12, ht3, v, keyX, yWord]
              have hd1 : d.1 = .insertBefore v (endOfKey keyX) (if yWord = 0 then none else some (endOfKey (yWord - 1))) := by rw [hd_eq]
              have hd2 : d.2 = 4 := by rw [hd_eq]
              have hy_w : yWord < 2 ^ w := by
                rw [hd1] at hw_hd
                by_cases hy0 : yWord = 0; · omega
                · have hye : (endOfKey (yWord - 1)).1 < S.eCap := hw_hd.2.2 (endOfKey (yWord - 1)) (by simp [hy0])
                  have hk := key_lt_two_mul_of_endOfKey hye; omega
              have ha9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 5) (.const 1)))) stA .normal
                  { stA with regs := Function.update stA.regs 9 v } _ :=
                runs_assign_iff.mpr ⟨v, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [stA, r5]))
                  (Expr.eval_const (by omega)) (by omega)) (hbuf (ptr + 1) (by omega) (by omega)), rfl, rfl, rfl⟩
              set st1' : State := { stA with regs := Function.update stA.regs 9 v }
              have ha10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 5) (.const 2)))) st1' .normal
                  { st1' with regs := Function.update st1'.regs 10 keyX } _ :=
                runs_assign_iff.mpr ⟨keyX, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1', stA, r5]))
                  (Expr.eval_const (by omega)) (by omega)) (hbuf (ptr + 2) (by omega) (by omega)), rfl, rfl, rfl⟩
              set st2' : State := { st1' with regs := Function.update st1'.regs 10 keyX }
              have ha11 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 5) (.const 3)))) st2' .normal
                  { st2' with regs := Function.update st2'.regs 11 yWord } _ :=
                runs_assign_iff.mpr ⟨yWord, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2', st1', stA, r5]))
                  (Expr.eval_const (by omega)) (by omega)) (hbuf (ptr + 3) (by omega) (by omega)), rfl, rfl, rfl⟩
              set st3' : State := { st2' with regs := Function.update st2'.regs 11 yWord }
              obtain ⟨oI, stI, cI, hrunI, S1, hinv1, harena1, hfr1, hv1, he1, hphi1⟩ :=
                ordInsertBeforeBody_runs hrot hstep hsplay hsplayRoot hwalk hjoin halloc ω hinvi harenai hy_w
                  (by rw [hvi, hei, ← hd1]; exact huniq_hd) (by rw [hvi, hei]; omega) hzi (by omega) hwide (pos := st3'.pos)
              have hcallI : Runs w p ω (.call 14 insProc [.reg 0, .reg 9, .reg 10, .reg 11]) st3' .normal
                  { stI with regs := Function.update st3'.regs 14 oI.value }
                  (argsSize [.reg 0, .reg 9, .reg 10, .reg 11] + cI + 1) :=
                runs_call_iff.mpr ⟨[b, v, keyX, yWord], ordInsertBeforeBody allocProc splayRootProc joinProc, oI, stI, cI,
                  evalArgs_cons (Expr.eval_reg_of_eq (by simp [st3', st2', st1', stA, r0]))
                    (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st3', st2', st1']))
                      (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st3', st2']))
                        (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st3'])) (evalArgs_nil _ _)))),
                  hins, hrunI, rfl, rfl, rfl⟩
              set st4' : State := { stI with regs := Function.update st3'.regs 14 oI.value }
              have ha5' : Runs w p ω (.assign 5 (.bin .add (.reg 5) (.const 4))) st4' .normal
                  { st4' with regs := Function.update st4'.regs 5 (ptr + 4) } _ :=
                runs_assign_iff.mpr ⟨ptr + 4, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4', st3', st2', st1', stA, r5]))
                  (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
              refine ⟨_, _, S1,
                ord_runs_cond_false hc0 (ord_runs_cond_false hc12 (ord_runs_cond_true hc3 Nat.one_ne_zero
                  (ord_runs_seq_normal ha9 (ord_runs_seq_normal ha10 (ord_runs_seq_normal ha11
                    (ord_runs_seq_normal hcallI ha5')))))),
                by simp [st4', st3', st2', st1', stA, r0], by simp [st4', st3', st2', st1', stA, r2],
                by simp [st4', st3', st2', st1', stA, r3], by simp [st4', st3', st2', st1', stA, r4],
                by simp [hd2], by simp [st4', st3', st2', st1', stA, r6], by simp [st4', st3', st2', st1', stA, r7],
                hd1 ▸ hinv1, harena1, hv1.trans hvi, he1.trans hei, hfr1.1,
                fun a ha1 ha2 => (hfr1.2 a ha2 (by rw [hvi, hei]; unfold ordFoot; omega)).trans (hbuf a ha1 ha2),
                fun a ha hnf => (hfr1.2 a (by omega) (by rw [hvi, hei]; exact hnf)).trans (hlt a ha hnf), ?_⟩
              rw [hei] at hphi1; rw [hd2]
              unfold ORD_INS_AMORT at hphi1
              simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil] at *
              have h1 : 200 ≤ 110000 * ordStoreLog S.eCap := by have := Nat.le_mul_of_pos_right 110000 hlog; omega
              have : 31000 * 4 * ordStoreLog S.eCap = 14000 * ordStoreLog S.eCap + 110000 * ordStoreLog S.eCap := by ring
              omega
            · have hc3 : (Expr.bin .eq (.reg 8) (.const 3)).eval w stA = some 0 :=
                Expr.eval_eq_false (Expr.eval_reg_of_eq (v := tag) (by simp [stA]))
                  (Expr.eval_const (by omega)) ht3 (by omega)
              set v := st2.mem (ptr + 1)
              set keyY := st2.mem (ptr + 2)
              have hd_eq : d = (.rotateTo v (endOfKey keyY), 3) := by
                simp [hd_def, decodeOrdEdit, ← htag_def, ht0, hnot12, ht3, v, keyY]
              have hd1 : d.1 = .rotateTo v (endOfKey keyY) := by rw [hd_eq]
              have hd2 : d.2 = 3 := by rw [hd_eq]
              have hv_lt : v < S.vCap := by rw [hd1] at hw_hd; exact hw_hd.1
              have hkY_lt : keyY < 2 * S.eCap := by
                rw [hd1] at hw_hd; exact key_lt_two_mul_of_endOfKey hw_hd.2
              have ha9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 5) (.const 1)))) stA .normal
                  { stA with regs := Function.update stA.regs 9 v } _ :=
                runs_assign_iff.mpr ⟨v, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [stA, r5]))
                  (Expr.eval_const (by omega)) (by omega)) (hbuf (ptr + 1) (by omega) (by omega)), rfl, rfl, rfl⟩
              set st1' : State := { stA with regs := Function.update stA.regs 9 v }
              have ha10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 5) (.const 2)))) st1' .normal
                  { st1' with regs := Function.update st1'.regs 10 keyY } _ :=
                runs_assign_iff.mpr ⟨keyY, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1', stA, r5]))
                  (Expr.eval_const (by omega)) (by omega)) (hbuf (ptr + 2) (by omega) (by omega)), rfl, rfl, rfl⟩
              set st2' : State := { st1' with regs := Function.update st1'.regs 10 keyY }
              obtain ⟨oR, stR, cR, hrunR, S1, hinv1, harena1, hfr1, hv1, he1, hphi1⟩ :=
                ordRotateToBody_runs hrot hstep hsplay hsplayRoot hwalk hjoin ω
                  (v := v) (keyY := keyY) hinvi harenai
                  (by omega) (by omega) (by rw [hvi, hei]; omega) hzi (by omega) hwide (pos := st2'.pos)
              have hcallR : Runs w p ω (.call 14 rotToProc [.reg 0, .reg 9, .reg 10]) st2' .normal
                  { stR with regs := Function.update st2'.regs 14 oR.value }
                  (argsSize [.reg 0, .reg 9, .reg 10] + cR + 1) :=
                runs_call_iff.mpr ⟨[b, v, keyY], ordRotateToBody splayRootProc joinProc, oR, stR, cR,
                  evalArgs_cons (Expr.eval_reg_of_eq (by simp [st2', st1', stA, r0]))
                    (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st2', st1']))
                      (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st2'])) (evalArgs_nil _ _))),
                  hrotTo, hrunR, rfl, rfl, rfl⟩
              set st3' : State := { stR with regs := Function.update st2'.regs 14 oR.value }
              have ha5' : Runs w p ω (.assign 5 (.bin .add (.reg 5) (.const 3))) st3' .normal
                  { st3' with regs := Function.update st3'.regs 5 (ptr + 3) } _ :=
                runs_assign_iff.mpr ⟨ptr + 3, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st3', st2', st1', stA, r5]))
                  (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
              refine ⟨_, _, S1,
                ord_runs_cond_false hc0 (ord_runs_cond_false hc12 (ord_runs_cond_false hc3
                  (ord_runs_seq_normal ha9 (ord_runs_seq_normal ha10 (ord_runs_seq_normal hcallR ha5'))))),
                by simp [st3', st2', st1', stA, r0], by simp [st3', st2', st1', stA, r2],
                by simp [st3', st2', st1', stA, r3], by simp [st3', st2', st1', stA, r4],
                by simp [hd2], by simp [st3', st2', st1', stA, r6], by simp [st3', st2', st1', stA, r7],
                hd1 ▸ hinv1, harena1, hv1.trans hvi, he1.trans hei, hfr1.1,
                fun a ha1 ha2 => (hfr1.2 a ha2 (by rw [hvi, hei]; unfold ordFoot; omega)).trans (hbuf a ha1 ha2),
                fun a ha hnf => (hfr1.2 a (by omega) (by rw [hvi, hei]; exact hnf)).trans (hlt a ha hnf), ?_⟩
              rw [hei] at hphi1; rw [hd2]
              unfold ORD_ROT_AMORT at hphi1
              simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil] at *
              have h1 : 200 ≤ 81000 * ordStoreLog S.eCap := by have := Nat.le_mul_of_pos_right 81000 hlog; omega
              have : 31000 * 3 * ordStoreLog S.eCap = 12000 * ordStoreLog S.eCap + 81000 * ordStoreLog S.eCap := by ring
              omega
      obtain ⟨stB, cB, S1, hrunB, b0, b2, b3, b4, b5, b6, b7, hinv1, harena1, hv1, he1, hz1, hbuf1, hlt1, hphiB⟩ := hstep_edit
      have ha7' : Runs w p ω (.assign 7 (.bin .add (.reg 7) (.const 1))) stB .normal
          { stB with regs := Function.update stB.regs 7 (i + 1) } _ :=
        runs_assign_iff.mpr ⟨i + 1, Expr.eval_add (Expr.eval_reg_of_eq b7) (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
      set stC : State := { stB with regs := Function.update stB.regs 7 (i + 1) }
      obtain ⟨stF, cF, SF, hrunF, f2, f3, hinvF, harenaF, hvF, heF, hzF, hltF, hphiF⟩ :=
        ih (i + 1) (ptr + d.2) stC S1 (applyOrdEdit curOrd d.1) (by omega) (by omega)
          (by rw [← hrest_def]; rw [hsum_cons] at hptr_le; omega)
          hw_tl huniq_tl hinv1 harena1 hv1 he1 hz1 hbuf1 hlt1
          (by simp [stC, b0]) (by simp [stC, b2]) (by simp [stC, b3]) (by simp [stC, b4])
          (by simp [stC, b5]) (by simp [stC, b6]) (by simp [stC])
      refine ⟨stF, _, SF,
        ord_runs_loop_true hcond Nat.one_ne_zero
          (ord_runs_seq_normal ha8 (ord_runs_seq_normal hrunB ha7')) hrunF,
        f2, f3, by simpa [applyOrdEdits, hdec_cons] using hinvF, harenaF, hvF, heF, hzF, hltF, ?_⟩
      rw [← hrest_def] at hphiF
      have hmul : 31000 * ((decodeOrdEdits st2.mem (rem + 1) ptr).2).sum * ordStoreLog S.eCap =
          31000 * d.2 * ordStoreLog S.eCap + 31000 * rest.2.sum * ordStoreLog S.eCap := by
        rw [hsum_cons]; ring
      have hge40 : 40 ≤ 31000 * d.2 * ordStoreLog S.eCap := by
        have := Nat.mul_le_mul (Nat.mul_le_mul_left 31000 hd_ge2) hlog; omega
      simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
      omega
  obtain ⟨stD, cD, SF, hrunD, d2, d3, hinvF, harenaF, hvF, heF, hzD, hltD, hphiD⟩ :=
    hdisp (mem edits) 0 (heap + 1) st6 S ord (by omega) (by omega)
      (by rw [hdec_eq]; have := hedits.2.1; omega)
      (by rw [hdec_eq]; exact hwithin) (by rw [hdec_eq]; exact huniq_all)
      hinv harena2 rfl rfl hz2 (fun _ _ _ => rfl)
      (fun a ha _ => hcp_out a (by omega))
      (by simp [st6, st5, st4, st3, hregCp 0 (by decide) (by decide), st1, st0, startState])
      (by simp [st6, st5, st4, st3, hregCp 2 (by decide) (by decide), st1, st0, startState])
      (by simp [st6, st5, st4, st3, hregCp 3 (by decide) (by decide), st1, st0, startState])
      (by simp [st6, st5, st4, st3]) (by simp [st6, st5, st4]) (by simp [st6, st5]) (by simp [st6])
  -- Step 3: Zero heap[0..words-1] and return heap
  have ha4c : Runs w p ω (.assign 4 (.const 0)) stD .normal
      { stD with regs := Function.update stD.regs 4 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set stD1 : State := { stD with regs := Function.update stD.regs 4 0 }
  obtain ⟨stZ, cZ, hrunZ, hregZ, hzZ, hltZ, hcZ⟩ :=
    ordZeroRangeLoop_runs (p := p) ω (st0 := stD1) hzD (by omega) hwide
      (by simp [stD1, d2]) (by simp [stD1, d3]) (by simp [stD1])
  have hret : Runs w p ω (.ret (.reg 3)) stZ (.returned heap) stZ _ :=
    runs_ret_iff.mpr ⟨heap, Expr.eval_reg_of_eq (by rw [hregZ 3 (by decide)]; simp [stD1, d3]), rfl, rfl, rfl⟩
  have hfull := ord_runs_seq_normal ha4a (ord_runs_seq_normal hrunCp (ord_runs_seq_normal ha4b
    (ord_runs_seq_normal ha5b (ord_runs_seq_normal ha6b (ord_runs_seq_normal ha7b
      (ord_runs_seq_normal hrunD (ord_runs_seq_normal ha4c (ord_runs_seq_normal hrunZ hret))))))))
  refine ⟨.returned heap, stZ, _, hfull, rfl, SF,
    by rw [hdec_eq] at hinvF; exact hinvF,
    harenaF.congr hinvF.next_le (fun a ha => hltZ a (by rw [hvF, heF] at ha; unfold ordFoot at ha; omega)),
    ⟨hzZ, fun a ha hnf => (hltZ a ha).trans (hltD a ha hnf)⟩, hvF, heF, ?_⟩
  rw [hdec_eq] at hphiD
  have hsum_le : ((decodeOrdEdits mem (mem edits) (edits + 1)).2).sum ≤ words := by
    have := hedits.2.1; omega
  have hmul_sum : 31000 * ((decodeOrdEdits mem (mem edits) (edits + 1)).2).sum * ordStoreLog S.eCap ≤
      31000 * (words * ordStoreLog S.eCap) := by
    have := Nat.mul_le_mul_right (ordStoreLog S.eCap) (Nat.mul_le_mul_left 31000 hsum_le)
    simpa [Nat.mul_assoc] using this
  have hwords_l : words ≤ words * ordStoreLog S.eCap := Nat.le_mul_of_pos_right words hlog
  have hrhs : ORD_EDIT_MUL * (words + 1) * ordStoreLog S.eCap =
      32000 * (words * ordStoreLog S.eCap) + 32000 * ordStoreLog S.eCap := by
    unfold ORD_EDIT_MUL; ring
  have h100 : 200 ≤ 32000 * ordStoreLog S.eCap := by have := Nat.le_mul_of_pos_right 32000 hlog; omega
  simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
  omega

end MinCostFlow.SparseCore.Program
