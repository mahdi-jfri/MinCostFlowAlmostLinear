module

public import MinCostFlow.SparseCore.Program.AssemblyFirstTourStepChain

import Mathlib.Tactic

/-!
# Edit-layout helpers and quiet/tail cases for `asmFirstTourBlockStepStmt` (`AssemblyFirstTourStepCases`)

Provides:
1. `decodeOrdEdit` / `decodeOrdEdits` / `OrdEditsAt` slicing, shift, and wrapping lemmas.
2. Parametric cost multiplier `tourBlockCaseMul` and sequential associativity `runs_seq_assoc`.
3. Verification of:
   - `tourBlock_popSplitEntry_runs` (5-statement split-entry pop shared by wall iterations),
   - `tourBlock_case_insert_runs` (tag 0: copy 8 words + `tourOp 0`),
   - `tourBlock_case_nonForestDel_runs` (tag 1, `isOpen = 1`: `[1, 0, e]` + `tourOp 0`),
   - `tourBlock_tail_rot_runs` (trailing `rotateTo` block).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## 1. `decodeOrdEdit` / `decodeOrdEdits` / `OrdEditsAt` helper lemmas -/

public section

theorem decodeOrdEdit_shift {mem mem' : ℕ → ℕ} {src dst : ℕ}
    (h : ∀ i < (decodeOrdEdit mem src).2, mem' (dst + i) = mem (src + i)) :
    decodeOrdEdit mem' dst = decodeOrdEdit mem src := by
  have h0 : mem' dst = mem src := by
    have hpos : 0 < (decodeOrdEdit mem src).2 := by
      unfold decodeOrdEdit; split_ifs <;> omega
    simpa using h 0 hpos
  unfold decodeOrdEdit at h ⊢
  by_cases ht0 : mem src = 0
  · have ht0' : mem' dst = 0 := h0.trans ht0
    simp only [ht0, ht0', ↓reduceIte] at h ⊢
    have h1 : mem' (dst + 1) = mem (src + 1) := h 1 (by omega)
    rw [h1]
  · have ht0' : mem' dst ≠ 0 := by rwa [h0]
    by_cases ht12 : mem src = 1 ∨ mem src = 2
    · have ht12' : mem' dst = 1 ∨ mem' dst = 2 := by rwa [h0]
      simp only [ht0, ht0', ht12, ht12', ↓reduceIte] at h ⊢
      have h1 : mem' (dst + 1) = mem (src + 1) := h 1 (by omega)
      have h2 : mem' (dst + 2) = mem (src + 2) := h 2 (by omega)
      have h3 : mem' (dst + 3) = mem (src + 3) := h 3 (by omega)
      have hrl : readList mem' (dst + 4) (mem' (dst + 3)) = readList mem (src + 4) (mem (src + 3)) := by
        rw [h3]; simp only [readList]
        refine List.map_congr_left fun i hi => ?_
        have hilt : i < mem (src + 3) := List.mem_range.mp hi
        simpa [Nat.add_assoc] using h (4 + i) (by omega)
      rw [hrl, h0, h1, h2, h3]
    · have ht12' : ¬(mem' dst = 1 ∨ mem' dst = 2) := by rwa [h0]
      by_cases ht3 : mem src = 3
      · have ht3' : mem' dst = 3 := h0.trans ht3
        simp [ht3, ht3'] at h ⊢
        have h1 : mem' (dst + 1) = mem (src + 1) := h 1 (by omega)
        have h2 : mem' (dst + 2) = mem (src + 2) := h 2 (by omega)
        have h3 : mem' (dst + 3) = mem (src + 3) := h 3 (by omega)
        simp [h1, h2, h3]
      · have ht3' : mem' dst ≠ 3 := by rwa [h0]
        simp [ht0, ht0', ht12, ht12', ht3, ht3'] at h ⊢
        have h1 : mem' (dst + 1) = mem (src + 1) := h 1 (by omega)
        have h2 : mem' (dst + 2) = mem (src + 2) := h 2 (by omega)
        simp [h1, h2]

theorem decodeOrdEdits_shift {mem mem' : ℕ → ℕ} :
    ∀ (n src dst : ℕ),
      (∀ i < (decodeOrdEdits mem n src).2.sum, mem' (dst + i) = mem (src + i)) →
      decodeOrdEdits mem' n dst = decodeOrdEdits mem n src
  | 0, _, _, _ => rfl
  | n + 1, src, dst, h => by
    simp only [decodeOrdEdits, List.sum_cons] at h ⊢
    have h1 : decodeOrdEdit mem' dst = decodeOrdEdit mem src :=
      decodeOrdEdit_shift (fun i hi => h i (by omega))
    have h2 : decodeOrdEdits mem' n (dst + (decodeOrdEdit mem src).2) =
        decodeOrdEdits mem n (src + (decodeOrdEdit mem src).2) :=
      decodeOrdEdits_shift n (src + (decodeOrdEdit mem src).2) (dst + (decodeOrdEdit mem src).2)
        (fun i hi => by simpa [Nat.add_assoc] using h ((decodeOrdEdit mem src).2 + i) (by omega))
    rw [h1, h2]

theorem decodeOrdEdits_len (mem : ℕ → ℕ) :
    ∀ (n a : ℕ), (decodeOrdEdits mem n a).1.length = n ∧ (decodeOrdEdits mem n a).2.length = n
  | 0, _ => ⟨rfl, rfl⟩
  | n + 1, a => by
    simp only [decodeOrdEdits, List.length_cons]
    have ih := decodeOrdEdits_len mem n (a + (decodeOrdEdit mem a).2)
    exact ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2⟩

theorem decodeOrdEdit_insertBefore_info {mem : ℕ → ℕ} {a v : ℕ} {x : End} {y : Option End}
    (h : (decodeOrdEdit mem a).1 = .insertBefore v x y) :
    mem a = 3 ∧ (decodeOrdEdit mem a).2 = 4 := by
  unfold decodeOrdEdit at h ⊢
  by_cases h0 : mem a = 0
  · simp [h0] at h
  · by_cases h12 : mem a = 1 ∨ mem a = 2
    · simp [h0, h12] at h
    · by_cases h3 : mem a = 3
      · simp [h3]
      · simp [h0, h12, h3] at h

theorem decodeOrdEdit_dropEdge_info {mem : ℕ → ℕ} {a e : ℕ}
    (h : (decodeOrdEdit mem a).1 = .dropEdge e) :
    mem a = 0 ∧ mem (a + 1) = e ∧ (decodeOrdEdit mem a).2 = 2 := by
  unfold decodeOrdEdit at h ⊢
  by_cases h0 : mem a = 0
  · simp [h0] at h ⊢; exact h
  · by_cases h12 : mem a = 1 ∨ mem a = 2
    · simp [h0, h12] at h
    · by_cases h3 : mem a = 3 <;> simp [h0, h12, h3] at h

theorem decodeOrdEdit_moveEnds_info {mem : ℕ → ℕ} {a v v' : ℕ} {sel : Finset End} {c : Bool}
    (h : (decodeOrdEdit mem a).1 = .moveEnds v v' sel c) :
    (mem a = 1 ∨ mem a = 2) ∧ decodeOrdEdit mem a = (.moveEnds v v' sel c, 4 + mem (a + 3)) := by
  unfold decodeOrdEdit at h ⊢
  by_cases h0 : mem a = 0
  · simp [h0] at h
  · by_cases h12 : mem a = 1 ∨ mem a = 2
    · simp only [h0, h12, ↓reduceIte] at h
      exact ⟨h12, by simp only [h0, h12, ↓reduceIte]; exact Prod.ext h rfl⟩
    · by_cases h3 : mem a = 3 <;> simp [h0, h12, h3] at h

theorem decodeOrdEdit_rotateTo_info {mem : ℕ → ℕ} {a v : ℕ} {y : End}
    (h : (decodeOrdEdit mem a).1 = .rotateTo v y) :
    (decodeOrdEdit mem a).2 = 3 := by
  unfold decodeOrdEdit at h ⊢
  by_cases h0 : mem a = 0
  · simp [h0] at h
  · by_cases h12 : mem a = 1 ∨ mem a = 2
    · simp [h0, h12] at h
    · by_cases h3 : mem a = 3
      · simp [h3] at h
      · simp [h0, h12, h3]

theorem ordEditsAt_insert2 {mem mem' : ℕ → ℕ} {ePtr h : ℕ} {a b : ℕ} {x₁ x₂ : End}
    {y₁ y₂ : Option End}
    (h0 : mem' h = 2) (hcp : ∀ i < 8, mem' (h + 1 + i) = mem (ePtr + i))
    (hd1 : (decodeOrdEdit mem ePtr).1 = .insertBefore a x₁ y₁)
    (hd2 : (decodeOrdEdit mem (ePtr + 4)).1 = .insertBefore b x₂ y₂) :
    OrdEditsAt mem' h [.insertBefore a x₁ y₁, .insertBefore b x₂ y₂] 9 := by
  have hi1 := decodeOrdEdit_insertBefore_info hd1
  have hi2 := decodeOrdEdit_insertBefore_info hd2
  have hdec1 : decodeOrdEdit mem' (h + 1) = (.insertBefore a x₁ y₁, 4) := by
    rw [decodeOrdEdit_shift (mem := mem) (src := ePtr) (dst := h + 1) (fun i hi => hcp i (by omega))]
    exact Prod.ext hd1 hi1.2
  have hdec2 : decodeOrdEdit mem' (h + 1 + 4) = (.insertBefore b x₂ y₂, 4) := by
    rw [decodeOrdEdit_shift (mem := mem) (src := ePtr + 4) (dst := h + 1 + 4)
      (fun i hi => by convert hcp (4 + i) (by omega) using 2 <;> omega)]
    exact Prod.ext hd2 hi2.2
  refine ⟨?_, ?_, ?_⟩
  · simp [readOrdEdits, h0, decodeOrdEdits, hdec1, hdec2]
  · simp [h0, decodeOrdEdits, hdec1, hdec2]
  · simp [ordEditsEnc, OrdEdit.enc]

theorem ordEditsAt_drop1 {mem : ℕ → ℕ} {h e : ℕ}
    (h0 : mem h = 1) (h1 : mem (h + 1) = 0) (h2 : mem (h + 2) = e) :
    OrdEditsAt mem h [.dropEdge e] 3 := by
  have hdec : decodeOrdEdit mem (h + 1) = (.dropEdge e, 2) := by
    simp [decodeOrdEdit, h1, h2]
  refine ⟨?_, ?_, ?_⟩
  · simp [readOrdEdits, h0, decodeOrdEdits, hdec]
  · simp [h0, decodeOrdEdits, hdec]
  · simp [ordEditsEnc, OrdEdit.enc]

theorem decodeOrdEdits_rot_sum {mem : ℕ → ℕ} :
    ∀ (k a : ℕ), (∀ d ∈ (decodeOrdEdits mem k a).1, d.IsRotate) →
      (decodeOrdEdits mem k a).2.sum = 3 * k ∧
      ordEditsEnc (decodeOrdEdits mem k a).1 = k
  | 0, _, _ => ⟨rfl, rfl⟩
  | k + 1, a, hrot => by
    simp only [decodeOrdEdits, List.sum_cons, ordEditsEnc, List.map_cons, List.sum_cons] at hrot ⊢
    have h0 : (decodeOrdEdit mem a).1.IsRotate := hrot _ List.mem_cons_self
    cases hd : (decodeOrdEdit mem a).1 with
    | rotateTo v y =>
      have hlen : (decodeOrdEdit mem a).2 = 3 := decodeOrdEdit_rotateTo_info hd
      have ih := decodeOrdEdits_rot_sum k (a + (decodeOrdEdit mem a).2)
        (fun d hd' => hrot d (List.mem_cons_of_mem _ hd'))
      rw [hlen] at ih
      simp only [OrdEdit.enc, hlen]
      exact ⟨by omega, by unfold ordEditsEnc at ih; omega⟩
    | dropEdge _ | moveEnds _ _ _ _ | insertBefore _ _ _ =>
      rw [hd] at h0; cases h0

theorem ordEditsAt_rotTail {mem mem' : ℕ → ℕ} {ePtr h k rotW : ℕ} {rotEds : List OrdEdit}
    (h0 : mem' h = k)
    (hdec : (decodeOrdEdits mem k ePtr).1 = rotEds)
    (hsum : (decodeOrdEdits mem k ePtr).2.sum = rotW)
    (hrot : ∀ d ∈ rotEds, d.IsRotate)
    (hcp : ∀ i < rotW, mem' (h + 1 + i) = mem (ePtr + i)) :
    OrdEditsAt mem' h rotEds (1 + rotW) := by
  have hsh : decodeOrdEdits mem' k (h + 1) = decodeOrdEdits mem k ePtr :=
    decodeOrdEdits_shift k ePtr (h + 1) (fun i hi => hcp i (by omega))
  have hrs := decodeOrdEdits_rot_sum k ePtr (hdec ▸ hrot)
  refine ⟨?_, ?_, ?_⟩
  · simp [readOrdEdits, h0, hsh, hdec]
  · simp [h0, hsh, hsum]
  · rw [← hdec, hrs.2]; omega

/-! ## 2. Parametric cost multiplier and sequential associativity -/

/-- Parametric cost multiplier for one iteration of `asmFirstTourBlockStepStmt`. Kept parametric
so rewriting via `tourBlockCaseMulFn_eq` never unfolds `tourMul` or `outSmallSideMul`. -/
@[expose] def tourBlockCaseMulFn (mTour mOut mSpec mRel mMove : ℕ) : ℕ :=
  5 * mTour + mOut * (mSpec + 1) + mRel + mMove + 500

theorem tourBlockCaseMulFn_eq (mTour mOut mSpec mRel mMove : ℕ) :
    tourBlockCaseMulFn mTour mOut mSpec mRel mMove =
      5 * mTour + mOut * (mSpec + 1) + mRel + mMove + 500 := rfl

noncomputable def tourBlockCaseMul : ℕ :=
  tourBlockCaseMulFn tourMul outSmallSideMul tourOutSpec.mul tourConsumeRelMul tourApplyMoveMul

theorem tourBlockCaseMul_eq :
    tourBlockCaseMul =
      tourBlockCaseMulFn tourMul outSmallSideMul tourOutSpec.mul tourConsumeRelMul tourApplyMoveMul := by
  unfold tourBlockCaseMul; rfl

/-- Right-associativity of normal `Runs` sequential composition (exact same cost). -/
theorem runs_seq_assoc {w : ℕ} {p : Program} {ω : ℕ → Bool} {A B C : Stmt}
    {s0 s1 : State} {c : ℕ}
    (h : Runs w p ω ((A ;; B) ;; C) s0 .normal s1 c) :
    Runs w p ω (A ;; (B ;; C)) s0 .normal s1 c := by
  rcases runs_seq_iff.mp h with ⟨_, _, _, hEq, _⟩ | ⟨sm, cAB, cC, hAB, hC, rfl⟩
  · cases hEq
  · rcases runs_seq_iff.mp hAB with ⟨_, _, _, hEq, _⟩ | ⟨sA, cA, cB, hA, hB, rfl⟩
    · cases hEq
    · have hBC : Runs w p ω (B ;; C) sA .normal s1 (cB + cC + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨sm, cB, cC, hB, hC, rfl⟩)
      have := runs_seq_iff.mpr (Or.inr ⟨sA, cA, cB + cC + 1, hA, hBC, rfl⟩)
      rwa [show cA + (cB + cC + 1) + 1 = cA + cB + 1 + cC + 1 by omega] at this

/-! ## 3. Shared split-entry pop (`tourBlock_popSplitEntry_runs`) -/

/-- Runs the 5-statement split-entry pop shared by forest-delete and vertex-split iterations:
loads `spIdx := mem[statePtr]`, `kept`, `fresh` from `L[spIdx]` at `spPtr`, and stores
`mem[statePtr] := spIdx + 1`. -/
theorem tourBlock_popSplitEntry_runs {w spPtr statePtr spIdx : ℕ} {p : Program} {ω : ℕ → Bool}
    {L : List CompSplitEntry} {st : State}
    (hwide : 18 ≤ 2 ^ w) (hsp_w : spPtr + 1 + 4 * L.length < 2 ^ w) (_hst_w : statePtr + 3 < 2 ^ w)
    (hr5 : st.regs 5 = spPtr) (hr7 : st.regs 7 = statePtr)
    (hspAt : SplitEntriesAt st.mem spPtr L)
    (hspIdx_lt : spIdx < L.length) (hst0 : st.mem statePtr = spIdx) :
    let e := L[spIdx]'hspIdx_lt
    let m1 := Function.update st.mem statePtr (spIdx + 1)
    ∃ st1 c1,
      Runs w p ω
        (.assign 22 (.load (.reg 7)) ;;
         .assign 23 (.bin .add (.bin .add (.reg 5) (.const 1)) (.bin .mul (.const 4) (.reg 22))) ;;
         .assign 24 (.load (.bin .add (.reg 23) (.const 2))) ;;
         .assign 25 (.load (.bin .add (.reg 23) (.const 3))) ;;
         .store (.reg 7) (.bin .add (.reg 22) (.const 1)))
        st .normal st1 c1 ∧
      st1.mem = m1 ∧
      st1.regs 24 = e.kept ∧ st1.regs 25 = e.fresh ∧
      (∀ r, r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → st1.regs r = st.regs r) ∧
      c1 ≤ 45 := by
  intro e m1
  have hent := hspAt.2 spIdx hspIdx_lt
  set ep := spPtr + 1 + 4 * spIdx
  set r1 := Function.update st.regs 22 spIdx
  set r2 := Function.update r1 23 ep
  set r3 := Function.update r2 24 e.kept
  set r4 := Function.update r3 25 e.fresh
  have ha1 : Runs w p ω (.assign 22 (.load (.reg 7))) st .normal { st with regs := r1 } 3 :=
    runs_assign_iff.mpr ⟨spIdx, Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr7) hst0, rfl, rfl, rfl⟩
  have ha2 : Runs w p ω
      (.assign 23 (.bin .add (.bin .add (.reg 5) (.const 1)) (.bin .mul (.const 4) (.reg 22))))
      { st with regs := r1 } .normal { st with regs := r2 } 8 :=
    runs_assign_iff.mpr ⟨ep,
      Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, hr5])) (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [r1])) (by omega))
        (by omega), rfl, rfl, rfl⟩
  have ha3 : Runs w p ω (.assign 24 (.load (.bin .add (.reg 23) (.const 2))))
      { st with regs := r2 } .normal { st with regs := r3 } 5 :=
    runs_assign_iff.mpr ⟨e.kept,
      Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r2])) (Expr.eval_const (by omega)) (by omega))
        hent.2.2.1, rfl, rfl, rfl⟩
  have ha4 : Runs w p ω (.assign 25 (.load (.bin .add (.reg 23) (.const 3))))
      { st with regs := r3 } .normal { st with regs := r4 } 5 :=
    runs_assign_iff.mpr ⟨e.fresh,
      Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3, r2])) (Expr.eval_const (by omega)) (by omega))
        hent.2.2.2, rfl, rfl, rfl⟩
  have hstW : Runs w p ω (.store (.reg 7) (.bin .add (.reg 22) (.const 1)))
      { st with regs := r4 } .normal { st with mem := m1, regs := r4 } 5 :=
    runs_store_iff.mpr ⟨statePtr, spIdx + 1,
      Expr.eval_reg_of_eq (by simp [r4, r3, r2, r1, hr7]),
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [r4, r3, r2, r1])) (Expr.eval_const (by omega))
        (by omega), rfl, rfl, rfl⟩
  refine ⟨{ st with mem := m1, regs := r4 }, _,
    runs_seq_normal ha1 (runs_seq_normal ha2 (runs_seq_normal ha3 (runs_seq_normal ha4 hstW))),
    rfl, by simp [r4, r3], by simp [r4],
    fun r h22 h23 h24 h25 => by simp [r4, r3, r2, r1, h22, h23, h24, h25], by omega⟩

/-! ## 4. Quiet cases (`insert`, `nonForestDel`) and trailing rotation block -/

/-- Case 1 (`.insert e a b`): copies 8 words of two `insertBefore` edits into `[2, ...]` at `hCur`
and applies them via `tourOp 0`. Space `≤ 129`, cost `≤ tourBlockCaseMul * 12 * log eCap + Δφ`. -/
theorem tourBlock_case_insert_runs {w vCap eCap bTour bCopy tourH ePtr hCur : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpT : HasTourProcs p bTour) (hpC : p.HasAt bCopy [copyWords])
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    {s : TourAbs} {tx : (tourAsmRep vCap eCap).τ} {st : State}
    {a b : ℕ} {x₁ x₂ : End} {y₁ y₂ : Option End}
    (hr0 : st.regs 0 = tourH) (hr9 : st.regs 9 = hCur) (hr13 : st.regs 13 = ePtr)
    (hrep : (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s) tx st.mem)
    (hfoot : ∀ x, (tourAsmRep vCap eCap).foot tourH tx x → x < hCur)
    (hzero : ZeroFrom st.mem hCur)
    (hePtr_le : ePtr + 8 ≤ hCur)
    (hd1 : (decodeOrdEdit st.mem ePtr).1 = .insertBefore a x₁ y₁)
    (hd2 : (decodeOrdEdit st.mem (ePtr + 4)).1 = .insertBefore b x₂ y₂)
    (hvalid : TourEditsValid vCap eCap s [.insertBefore a x₁ y₁, .insertBefore b x₂ y₂])
    (hroom : hCur + 129 < 2 ^ w) :
    ∃ hNext st' c tx',
      Runs w p ω
        (.store (.reg 9) (.const 2) ;;
         .call 17 bCopy [.reg 13, .bin .add (.reg 9) (.const 1), .const 8] ;;
         .call 9 (tourOp bTour 0) [.reg 0, .reg 9, .const 9, .bin .add (.reg 9) (.const 9)])
        st .normal st' c ∧
      st'.regs 9 = hNext ∧
      (∀ r, r ≠ 9 → r ≠ 17 → st'.regs r = st.regs r) ∧
      (tourAsmRep vCap eCap).rep tourH
        (tourToAsmTour (tourApplyEdits s [.insertBefore a x₁ y₁, .insertBefore b x₂ y₂])) tx' st'.mem ∧
      hCur + 9 ≤ hNext ∧ hNext ≤ hCur + 129 ∧ ZeroFrom st'.mem hNext ∧
      (∀ x < hCur, ¬ (tourAsmRep vCap eCap).foot tourH tx x → st'.mem x = st.mem x) ∧
      (∀ x, (tourAsmRep vCap eCap).foot tourH tx' x →
        (tourAsmRep vCap eCap).foot tourH tx x ∨ (hCur ≤ x ∧ x < hNext)) ∧
      c + (tourAsmRep vCap eCap).phi tourH tx' st'.mem ≤
        tourBlockCaseMul * 12 * ordStoreLog eCap + (tourAsmRep vCap eCap).phi tourH tx st.mem := by
  change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH s tx st.mem at hrep
  have htl : 1 ≤ ordStoreLog eCap := by rw [ordStoreLog_eq_tourLog]; simp [tourLog]
  have hwide : 18 ≤ 2 ^ w := (tourDS_wide_of_foot hrep hfoot (by omega : hCur + 1 < 2 ^ w)).2
  have htourW : tourH < 2 ^ w :=
    lt_trans (hfoot tourH (tourAsmRep_handle_foot vCap eCap tourH tx)) (by omega)
  set m1 := Function.update st.mem hCur 2
  have hst1 : Runs w p ω (.store (.reg 9) (.const 2)) st .normal { st with mem := m1 } 3 :=
    runs_store_iff.mpr ⟨hCur, 2, Expr.eval_reg_of_eq hr9, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  have hcopy := copyWords_meetsContract (w := w) hpC [ePtr, hCur + 1, 8] m1 st.pos ω
    (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl <;> omega)
    ⟨ePtr, hCur + 1, 8, rfl, by omega, by omega, by omega, Or.inr (by omega)⟩
  obtain ⟨bdC, hbdC, oC, stC, cC, hrunC, hpostC, hcostC⟩ := hcopy
  obtain ⟨_, _, _, hEqC, _, hcpC, hfrC⟩ := hpostC
  simp only [List.cons.injEq, and_true] at hEqC
  rcases hEqC with ⟨rfl, rfl, rfl⟩
  set r1 := Function.update st.regs 17 oC.value
  have hcallC : Runs w p ω (.call 17 bCopy [.reg 13, .bin .add (.reg 9) (.const 1), .const 8])
      { st with mem := m1 } .normal ⟨stC.mem, r1, stC.pos⟩
      (argsSize [.reg 13, .bin .add (.reg 9) (.const 1), .const 8] + cC + 1) :=
    runs_call_iff.mpr ⟨_, bdC, oC, stC, cC,
      evalArgs_cons (Expr.eval_reg_of_eq hr13) <|
      evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq hr9) (Expr.eval_const (by omega)) (by omega)) <|
      evalArgs_cons (Expr.eval_const (by omega)) <|
      evalArgs_nil _ _,
      hbdC, hrunC, rfl, rfl, rfl⟩
  have hmC_lt : ∀ a < hCur, stC.mem a = st.mem a := fun a ha =>
    (hfrC a (Or.inl (by omega))).trans (Function.update_of_ne (by omega) _ _)
  have hlocC := tourAsmRep_local vCap eCap tourH (tourToAsmTour s) tx st.mem stC.mem
    fun a ha => (hmC_lt a (hfoot a ha)).symm
  have hordEd : OrdEditsAt stC.mem hCur [.insertBefore a x₁ y₁, .insertBefore b x₂ y₂] 9 :=
    ordEditsAt_insert2
      ((hfrC hCur (Or.inl (by omega))).trans (Function.update_self hCur 2 st.mem))
      (fun i hi => (hcpC i hi).trans (Function.update_of_ne (by omega) _ _))
      hd1 hd2
  have hImpl := (tourDS_implements w vCap eCap p bTour hpT hw).2
  have hargs0 : ∀ a ∈ [tourH, hCur, 9, hCur + 9], a < 2 ^ w := by
    intro a ha; simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> omega
  have hpre0 : (tourContract vCap eCap tourMul tourAlloc).pre 0 s [tourH, hCur, 9, hCur + 9] stC.mem :=
    ⟨tourH, hCur, 9, hCur + 9, rfl, by rwa [hordEd.1], le_refl _, by rwa [hordEd.1]⟩
  have hsp0 : hCur + 9 + (tourContract vCap eCap tourMul tourAlloc).space 0 s [tourH, hCur, 9, hCur + 9] stC.mem < 2 ^ w := by
    simp only [tourContract, tourAlloc, tourOp0Space]
    rw [show [tourH, hCur, 9, hCur + 9].getD 2 0 = 9 from rfl]; omega
  have hfootC : ∀ x, (tourDSRep vCap eCap).foot tourH tx x → x < heapArg [tourH, hCur, 9, hCur + 9] :=
    fun x hx => lt_trans (hfoot x hx) (by show hCur < hCur + 9; omega)
  have hzeroC : ZeroFrom stC.mem (heapArg [tourH, hCur, 9, hCur + 9]) := fun x hx => by
    change hCur + 9 ≤ x at hx
    exact (hfrC x (Or.inr (by omega))).trans ((Function.update_of_ne (by omega) _ _).trans (hzero x (by omega)))
  obtain ⟨bd0, hbd0, o0, st0, c0, hrun0, s1, tx', hrep', hpost0, hresp0, hcost0⟩ :=
    hImpl.2.2 0 tourH s tx [tourH, hCur, 9, hCur + 9] stC.mem stC.pos ω hargs0 rfl
      (hlocC.1 hrep) hpre0 hfootC hzeroC hsp0
  have hs1_eq : s1 = tourApplyEdits s [.insertBefore a x₁ y₁, .insertBefore b x₂ y₂] := by
    simpa [tourContract, hordEd.1] using hpost0
  subst hs1_eq
  set r2 := Function.update r1 9 o0.value
  have hcall0 : Runs w p ω (.call 9 (tourOp bTour 0) [.reg 0, .reg 9, .const 9, .bin .add (.reg 9) (.const 9)])
      ⟨stC.mem, r1, stC.pos⟩ .normal ⟨st0.mem, r2, st0.pos⟩
      (argsSize [.reg 0, .reg 9, .const 9, .bin .add (.reg 9) (.const 9)] + c0 + 1) :=
    runs_call_iff.mpr ⟨_, bd0, o0, st0, c0,
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r1, hr0])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r1, hr9])) <|
      evalArgs_cons (Expr.eval_const (by omega)) <|
      evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, hr9]))
        (Expr.eval_const (by omega)) (by omega)) <|
      evalArgs_nil _ _,
      hbd0, hrun0, rfl, rfl, rfl⟩
  have hha0 : heapArg [tourH, hCur, 9, hCur + 9] = hCur + 9 := rfl
  rw [hha0] at hresp0
  simp only [tourContract, tourAlloc, tourOp0Space] at hresp0 hcost0
  rw [show [tourH, hCur, 9, hCur + 9].getD 2 0 = 9 from rfl] at hresp0 hcost0
  have ho0_lo : hCur + 9 ≤ o0.value := hresp0.1
  have ho0_hi : o0.value ≤ hCur + 9 + (12 * 9 + 12) := hresp0.2.1
  refine ⟨o0.value, ⟨st0.mem, r2, st0.pos⟩, _, tx',
    runs_seq_normal hst1 (runs_seq_normal hcallC hcall0),
    by simp [r2], fun r h9 h17 => by simp [r2, r1, h9, h17],
    hrep', ho0_lo, by omega, hresp0.2.2.1,
    fun x hx hnf => (hresp0.2.2.2.1 x (by omega) hnf).trans (hmC_lt x hx),
    fun x hx => by
      rcases hresp0.2.2.2.2 x hx with h0 | ⟨hge, hlt⟩
      · exact Or.inl h0
      · exact Or.inr ⟨by omega, hlt⟩, ?_⟩
  have hphiC : (tourDSRep vCap eCap).phi tourH tx st.mem = (tourDSRep vCap eCap).phi tourH tx stC.mem := hlocC.2
  rw [← hphiC, ← ordStoreLog_eq_tourLog] at hcost0
  simp only [copyWordsContract, argsSize, Expr.size] at hcostC ⊢
  have h10 : tourMul * (9 + 1) * ordStoreLog eCap ≤ 5 * tourMul * 12 * ordStoreLog eCap := by
    have hmul : tourMul * (9 + 1) ≤ 5 * tourMul * 12 := by omega
    exact Nat.mul_le_mul_right _ hmul
  have h500 : 250 ≤ 500 * 12 * ordStoreLog eCap :=
    le_trans (by omega) (Nat.le_mul_of_pos_right _ htl)
  have hbm : 5 * tourMul * 12 * ordStoreLog eCap + 500 * 12 * ordStoreLog eCap ≤
      tourBlockCaseMul * 12 * ordStoreLog eCap := by
    rw [tourBlockCaseMul_eq, tourBlockCaseMulFn_eq]
    have : 5 * tourMul + 500 ≤ 5 * tourMul + outSmallSideMul * (tourOutSpec.mul + 1) +
        tourConsumeRelMul + tourApplyMoveMul + 500 := by omega
    rw [← Nat.add_mul, ← Nat.add_mul]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
  have hgoal_phi : (tourAsmRep vCap eCap).phi tourH tx' st0.mem = (tourDSRep vCap eCap).phi tourH tx' st0.mem ∧
      (tourAsmRep vCap eCap).phi tourH tx st.mem = (tourDSRep vCap eCap).phi tourH tx st.mem := ⟨rfl, rfl⟩
  rw [hgoal_phi.1, hgoal_phi.2]
  clear * - hcost0 hcostC h10 h500 hbm
  omega

/-- Case 2 (non-forest `.delete e`, `isOpen = 1`): writes `[1, 0, e]` at `hCur` and calls `tourOp 0`.
Space `≤ 51`, cost `≤ (4 * tourMul + 40) * ordStoreLog eCap + Δφ` (tight so Case 3 can reuse it!). -/
theorem tourBlock_case_nonForestDel_runs {w vCap eCap bTour tourH e hCur : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpT : HasTourProcs p bTour) (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    {s : TourAbs} {tx : (tourAsmRep vCap eCap).τ} {st : State}
    (hr0 : st.regs 0 = tourH) (hr9 : st.regs 9 = hCur) (hr17 : st.regs 17 = e)
    (hrep : (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s) tx st.mem)
    (hfoot : ∀ x, (tourAsmRep vCap eCap).foot tourH tx x → x < hCur)
    (hzero : ZeroFrom st.mem hCur)
    (hvalid : TourEditsValid vCap eCap s [.dropEdge e])
    (hroom : hCur + 51 < 2 ^ w) :
    ∃ hNext st' c tx',
      Runs w p ω
        (.store (.reg 9) (.const 1) ;;
         .store (.bin .add (.reg 9) (.const 1)) (.const 0) ;;
         .store (.bin .add (.reg 9) (.const 2)) (.reg 17) ;;
         .call 9 (tourOp bTour 0) [.reg 0, .reg 9, .const 3, .bin .add (.reg 9) (.const 3)])
        st .normal st' c ∧
      st'.regs 9 = hNext ∧
      (∀ r, r ≠ 9 → st'.regs r = st.regs r) ∧
      (tourAsmRep vCap eCap).rep tourH (tourToAsmTour (tourApplyEdits s [.dropEdge e])) tx' st'.mem ∧
      hCur + 3 ≤ hNext ∧ hNext ≤ hCur + 51 ∧ ZeroFrom st'.mem hNext ∧
      (∀ x < hCur, ¬ (tourAsmRep vCap eCap).foot tourH tx x → st'.mem x = st.mem x) ∧
      (∀ x, (tourAsmRep vCap eCap).foot tourH tx' x →
        (tourAsmRep vCap eCap).foot tourH tx x ∨ (hCur ≤ x ∧ x < hNext)) ∧
      c + (tourAsmRep vCap eCap).phi tourH tx' st'.mem ≤
        (4 * tourMul + 40) * ordStoreLog eCap + (tourAsmRep vCap eCap).phi tourH tx st.mem := by
  change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH s tx st.mem at hrep
  have htl : 1 ≤ ordStoreLog eCap := by rw [ordStoreLog_eq_tourLog]; simp [tourLog]
  have hwide : 18 ≤ 2 ^ w := (tourDS_wide_of_foot hrep hfoot (by omega : hCur + 1 < 2 ^ w)).2
  have htourW : tourH < 2 ^ w :=
    lt_trans (hfoot tourH (tourAsmRep_handle_foot vCap eCap tourH tx)) (by omega)
  set m1 := Function.update st.mem hCur 1
  set m2 := Function.update m1 (hCur + 1) 0
  set m3 := Function.update m2 (hCur + 2) e
  have hst1 : Runs w p ω (.store (.reg 9) (.const 1)) st .normal { st with mem := m1 } 3 :=
    runs_store_iff.mpr ⟨hCur, 1, Expr.eval_reg_of_eq hr9, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  have hst2 : Runs w p ω (.store (.bin .add (.reg 9) (.const 1)) (.const 0))
      { st with mem := m1 } .normal { st with mem := m2 } 5 :=
    runs_store_iff.mpr ⟨hCur + 1, 0,
      Expr.eval_add (Expr.eval_reg_of_eq hr9) (Expr.eval_const (by omega)) (by omega),
      Expr.eval_const (by omega), rfl, rfl, rfl⟩
  have hst3 : Runs w p ω (.store (.bin .add (.reg 9) (.const 2)) (.reg 17))
      { st with mem := m2 } .normal { st with mem := m3 } 5 :=
    runs_store_iff.mpr ⟨hCur + 2, e,
      Expr.eval_add (Expr.eval_reg_of_eq hr9) (Expr.eval_const (by omega)) (by omega),
      Expr.eval_reg_of_eq hr17, rfl, rfl, rfl⟩
  have hm3_lt : ∀ x < hCur, m3 x = st.mem x := fun x hx => by
    simp only [m3, m2, m1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  have hm3_ge : ∀ x, hCur + 3 ≤ x → m3 x = st.mem x := fun x hx => by
    simp only [m3, m2, m1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  have hloc3 := tourAsmRep_local vCap eCap tourH (tourToAsmTour s) tx st.mem m3
    fun x hx => (hm3_lt x (hfoot x hx)).symm
  have hordEd : OrdEditsAt m3 hCur [.dropEdge e] 3 :=
    ordEditsAt_drop1 (by simp [m3, m2, m1]) (by simp [m3, m2]) (by simp [m3])
  have hImpl := (tourDS_implements w vCap eCap p bTour hpT hw).2
  have hargs0 : ∀ a ∈ [tourH, hCur, 3, hCur + 3], a < 2 ^ w := by
    intro a ha; simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> omega
  have hpre0 : (tourContract vCap eCap tourMul tourAlloc).pre 0 s [tourH, hCur, 3, hCur + 3] m3 :=
    ⟨tourH, hCur, 3, hCur + 3, rfl, by rwa [hordEd.1], le_refl _, by rwa [hordEd.1]⟩
  have hsp0 : hCur + 3 + (tourContract vCap eCap tourMul tourAlloc).space 0 s [tourH, hCur, 3, hCur + 3] m3 < 2 ^ w := by
    simp only [tourContract, tourAlloc, tourOp0Space]
    rw [show [tourH, hCur, 3, hCur + 3].getD 2 0 = 3 from rfl]; omega
  have hfoot3 : ∀ x, (tourDSRep vCap eCap).foot tourH tx x → x < heapArg [tourH, hCur, 3, hCur + 3] :=
    fun x hx => lt_trans (hfoot x hx) (by show hCur < hCur + 3; omega)
  have hzero3 : ZeroFrom m3 (heapArg [tourH, hCur, 3, hCur + 3]) := fun x hx => by
    change hCur + 3 ≤ x at hx
    exact (hm3_ge x (by omega)).trans (hzero x (by omega))
  obtain ⟨bd0, hbd0, o0, st0, c0, hrun0, s1, tx', hrep', hpost0, hresp0, hcost0⟩ :=
    hImpl.2.2 0 tourH s tx [tourH, hCur, 3, hCur + 3] m3 st.pos ω hargs0 rfl
      (hloc3.1 hrep) hpre0 hfoot3 hzero3 hsp0
  have hs1_eq : s1 = tourApplyEdits s [.dropEdge e] := by
    simpa [tourContract, hordEd.1] using hpost0
  subst hs1_eq
  set r1 := Function.update st.regs 9 o0.value
  have hcall0 : Runs w p ω (.call 9 (tourOp bTour 0) [.reg 0, .reg 9, .const 3, .bin .add (.reg 9) (.const 3)])
      { st with mem := m3 } .normal ⟨st0.mem, r1, st0.pos⟩
      (argsSize [.reg 0, .reg 9, .const 3, .bin .add (.reg 9) (.const 3)] + c0 + 1) :=
    runs_call_iff.mpr ⟨_, bd0, o0, st0, c0,
      evalArgs_cons (Expr.eval_reg_of_eq hr0) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr9) <|
      evalArgs_cons (Expr.eval_const (by omega)) <|
      evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq hr9) (Expr.eval_const (by omega)) (by omega)) <|
      evalArgs_nil _ _,
      hbd0, hrun0, rfl, rfl, rfl⟩
  have hha0 : heapArg [tourH, hCur, 3, hCur + 3] = hCur + 3 := rfl
  rw [hha0] at hresp0
  simp only [tourContract, tourAlloc, tourOp0Space] at hresp0 hcost0
  rw [show [tourH, hCur, 3, hCur + 3].getD 2 0 = 3 from rfl] at hresp0 hcost0
  have ho0_lo : hCur + 3 ≤ o0.value := hresp0.1
  have ho0_hi : o0.value ≤ hCur + 3 + (12 * 3 + 12) := hresp0.2.1
  refine ⟨o0.value, ⟨st0.mem, r1, st0.pos⟩, _, tx',
    runs_seq_normal hst1 (runs_seq_normal hst2 (runs_seq_normal hst3 hcall0)),
    by simp [r1], fun r h9 => by simp [r1, h9],
    hrep', ho0_lo, by omega, hresp0.2.2.1,
    fun x hx hnf => (hresp0.2.2.2.1 x (by omega) hnf).trans (hm3_lt x hx),
    fun x hx => by
      rcases hresp0.2.2.2.2 x hx with h0 | ⟨hge, hlt⟩
      · exact Or.inl h0
      · exact Or.inr ⟨by omega, hlt⟩, ?_⟩
  have hphi3 : (tourDSRep vCap eCap).phi tourH tx st.mem = (tourDSRep vCap eCap).phi tourH tx m3 := hloc3.2
  rw [← hphi3, ← ordStoreLog_eq_tourLog] at hcost0
  simp only [argsSize, Expr.size]
  have h40 : 40 ≤ 40 * ordStoreLog eCap := Nat.le_mul_of_pos_right 40 htl
  have h4eq : tourMul * (3 + 1) = 4 * tourMul := by omega
  have hdist : (4 * tourMul + 40) * ordStoreLog eCap =
      4 * tourMul * ordStoreLog eCap + 40 * ordStoreLog eCap := Nat.add_mul _ _ _
  rw [h4eq] at hcost0
  have hgoal_phi : (tourAsmRep vCap eCap).phi tourH tx' st0.mem = (tourDSRep vCap eCap).phi tourH tx' st0.mem ∧
      (tourAsmRep vCap eCap).phi tourH tx st.mem = (tourDSRep vCap eCap).phi tourH tx st.mem := ⟨rfl, rfl⟩
  rw [hgoal_phi.1, hgoal_phi.2]
  clear * - hcost0 h40 hdist
  omega

/-- Trailing rotation block (`editRotBlock U ed`): copies `rotW` words of `remRot` trailing
`rotateTo` edits into `[remRot, ...]` at `hCur` and applies them via `tourOp 0` (no-op if `remRot = 0`). -/
theorem tourBlock_tail_rot_runs {w vCap eCap bTour bCopy tourH edCopy editWords ePtr eIdx totalEdits hCur : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpT : HasTourProcs p bTour) (hpC : p.HasAt bCopy [copyWords])
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    {s : TourAbs} {tx : (tourAsmRep vCap eCap).τ} {st : State} {rotEds : List OrdEdit}
    (hr0 : st.regs 0 = tourH) (hr4 : st.regs 4 = editWords) (hr8 : st.regs 8 = edCopy)
    (hr9 : st.regs 9 = hCur) (hr13 : st.regs 13 = ePtr) (hr14 : st.regs 14 = eIdx)
    (hrep : (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s) tx st.mem)
    (hfoot : ∀ x, (tourAsmRep vCap eCap).foot tourH tx x → x < hCur)
    (hzero : ZeroFrom st.mem hCur)
    (htot : st.mem edCopy = totalEdits) (htot_lt : totalEdits < 2 ^ w) (heIdx_le : eIdx ≤ totalEdits)
    (hePtr_le : ePtr ≤ edCopy + editWords) (hedEnd_le : edCopy + editWords ≤ hCur)
    (hdec : (decodeOrdEdits st.mem (totalEdits - eIdx) ePtr).1 = rotEds)
    (hsum : (decodeOrdEdits st.mem (totalEdits - eIdx) ePtr).2.sum = edCopy + editWords - ePtr)
    (hrot : ∀ d ∈ rotEds, d.IsRotate)
    (hvalid : TourEditsValid vCap eCap s rotEds)
    (hroom : hCur + 13 * (edCopy + editWords - ePtr) + 25 < 2 ^ w) :
    let rotW := edCopy + editWords - ePtr
    ∃ hNext st' c tx',
      Runs w p ω
        (.assign 16 (.load (.reg 8)) ;;
         .assign 17 (.bin .sub (.reg 16) (.reg 14)) ;;
         .cond (.bin .lt (.const 0) (.reg 17))
           (.assign 18 (.bin .sub (.bin .add (.reg 8) (.reg 4)) (.reg 13)) ;;
            .store (.reg 9) (.reg 17) ;;
            .call 19 bCopy [.reg 13, .bin .add (.reg 9) (.const 1), .reg 18] ;;
            .assign 20 (.bin .add (.const 1) (.reg 18)) ;;
            .call 9 (tourOp bTour 0) [.reg 0, .reg 9, .reg 20, .bin .add (.reg 9) (.reg 20)])
           .nop)
        st .normal st' c ∧
      st'.regs 9 = hNext ∧
      (∀ r, r ≠ 9 → r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 19 → r ≠ 20 → st'.regs r = st.regs r) ∧
      (tourAsmRep vCap eCap).rep tourH (tourToAsmTour (tourApplyEdits s rotEds)) tx' st'.mem ∧
      hCur ≤ hNext ∧ hNext ≤ hCur + 13 * rotW + 25 ∧ ZeroFrom st'.mem hNext ∧
      (∀ x < hCur, ¬ (tourAsmRep vCap eCap).foot tourH tx x → st'.mem x = st.mem x) ∧
      (∀ x, (tourAsmRep vCap eCap).foot tourH tx' x →
        (tourAsmRep vCap eCap).foot tourH tx x ∨ (hCur ≤ x ∧ x < hNext)) ∧
      c + (tourAsmRep vCap eCap).phi tourH tx' st'.mem ≤
        tourBlockCaseMul * (rotW + 2) * ordStoreLog eCap + (tourAsmRep vCap eCap).phi tourH tx st.mem := by
  intro rotW
  change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH s tx st.mem at hrep
  have htl : 1 ≤ ordStoreLog eCap := by rw [ordStoreLog_eq_tourLog]; simp [tourLog]
  have hwide : 18 ≤ 2 ^ w := (tourDS_wide_of_foot hrep hfoot (by omega : hCur + 1 < 2 ^ w)).2
  have htourW : tourH < 2 ^ w :=
    lt_trans (hfoot tourH (tourAsmRep_handle_foot vCap eCap tourH tx)) (by omega)
  set remRot := totalEdits - eIdx
  set r1 := Function.update st.regs 16 totalEdits
  set r2 := Function.update r1 17 remRot
  have ha16 : Runs w p ω (.assign 16 (.load (.reg 8))) st .normal { st with regs := r1 } 3 :=
    runs_assign_iff.mpr ⟨totalEdits, Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr8) htot, rfl, rfl, rfl⟩
  have ha17 : Runs w p ω (.assign 17 (.bin .sub (.reg 16) (.reg 14)))
      { st with regs := r1 } .normal { st with regs := r2 } 4 :=
    runs_assign_iff.mpr ⟨remRot,
      Expr.eval_sub (Expr.eval_reg_of_eq (by simp [r1])) (Expr.eval_reg_of_eq (by simp [r1, hr14]))
        (by omega),
      rfl, rfl, rfl⟩
  by_cases hrem : remRot = 0
  · have hrot_nil : rotEds = [] := by rw [← hdec, hrem]; rfl
    have hcond : (Expr.bin .lt (.const 0) (.reg 17)).eval w { st with regs := r2 } = some 0 := by
      simp [Expr.eval, r2, hrem, BinOp.eval, (by omega : 0 < 2 ^ w)]
    have hnop : Runs w p ω .nop { st with regs := r2 } .normal { st with regs := r2 } 1 :=
      runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
    have hrc : Runs w p ω
        (.cond (.bin .lt (.const 0) (.reg 17))
          (.assign 18 (.bin .sub (.bin .add (.reg 8) (.reg 4)) (.reg 13)) ;;
           .store (.reg 9) (.reg 17) ;;
           .call 19 bCopy [.reg 13, .bin .add (.reg 9) (.const 1), .reg 18] ;;
           .assign 20 (.bin .add (.const 1) (.reg 18)) ;;
           .call 9 (tourOp bTour 0) [.reg 0, .reg 9, .reg 20, .bin .add (.reg 9) (.reg 20)])
          .nop)
        { st with regs := r2 } .normal { st with regs := r2 } ((Expr.bin .lt (.const 0) (.reg 17)).size + 1 + 1) :=
      runs_cond_iff.mpr ⟨0, 1, hcond, by simpa using hnop, rfl⟩
    refine ⟨hCur, { st with regs := r2 }, _, tx, runs_seq_normal ha16 (runs_seq_normal ha17 hrc),
      by simp [r2, r1, hr9], fun r _ h16 h17 _ _ _ => by simp [r2, r1, h16, h17],
      by rw [hrot_nil]; exact hrep, le_refl _, by omega, hzero,
      fun _ _ _ => rfl, fun _ hx => Or.inl hx, ?_⟩
    simp only [Expr.size]
    have h500 : 30 ≤ tourBlockCaseMul * (rotW + 2) * ordStoreLog eCap := by
      have h1 : 30 ≤ tourBlockCaseMul := by rw [tourBlockCaseMul_eq, tourBlockCaseMulFn_eq]; omega
      exact le_trans (le_trans h1 (Nat.le_mul_of_pos_right _ (by omega))) (Nat.le_mul_of_pos_right _ htl)
    clear * - h500; omega
  · have hrem_pos : 0 < remRot := Nat.pos_of_ne_zero hrem
    have hcond : (Expr.bin .lt (.const 0) (.reg 17)).eval w { st with regs := r2 } = some 1 := by
      simp [Expr.eval, r2, hrem_pos, BinOp.eval, (by omega : 1 < 2 ^ w)]
    set r3 := Function.update r2 18 rotW
    have ha18 : Runs w p ω (.assign 18 (.bin .sub (.bin .add (.reg 8) (.reg 4)) (.reg 13)))
        { st with regs := r2 } .normal { st with regs := r3 } 6 :=
      runs_assign_iff.mpr ⟨rotW,
        Expr.eval_sub
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r2, r1, hr8]))
            (Expr.eval_reg_of_eq (by simp [r2, r1, hr4])) (by omega))
          (Expr.eval_reg_of_eq (by simp [r2, r1, hr13])) (by omega), rfl, rfl, rfl⟩
    set m1 := Function.update st.mem hCur remRot
    have hst1 : Runs w p ω (.store (.reg 9) (.reg 17))
        { st with regs := r3 } .normal { st with mem := m1, regs := r3 } 3 :=
      runs_store_iff.mpr ⟨hCur, remRot, Expr.eval_reg_of_eq (by simp [r3, r2, r1, hr9]),
        Expr.eval_reg_of_eq (by simp [r3, r2]), rfl, rfl, rfl⟩
    have hcopy := copyWords_meetsContract (w := w) hpC [ePtr, hCur + 1, rotW] m1 st.pos ω
      (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl <;> omega)
      ⟨ePtr, hCur + 1, rotW, rfl, by omega, by omega, by omega, Or.inr (by omega)⟩
    obtain ⟨bdC, hbdC, oC, stC, cC, hrunC, hpostC, hcostC⟩ := hcopy
    obtain ⟨_, _, _, hEqC, _, hcpC, hfrC⟩ := hpostC
    simp only [List.cons.injEq, and_true] at hEqC
    rcases hEqC with ⟨rfl, rfl, rfl⟩
    set r4 := Function.update r3 19 oC.value
    have hcallC : Runs w p ω (.call 19 bCopy [.reg 13, .bin .add (.reg 9) (.const 1), .reg 18])
        { st with mem := m1, regs := r3 } .normal ⟨stC.mem, r4, stC.pos⟩
        (argsSize [.reg 13, .bin .add (.reg 9) (.const 1), .reg 18] + cC + 1) :=
      runs_call_iff.mpr ⟨_, bdC, oC, stC, cC,
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [r3, r2, r1, hr13])) <|
        evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3, r2, r1, hr9]))
          (Expr.eval_const (by omega)) (by omega)) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [r3])) <|
        evalArgs_nil _ _,
        hbdC, hrunC, rfl, rfl, rfl⟩
    set r5 := Function.update r4 20 (1 + rotW)
    have ha20 : Runs w p ω (.assign 20 (.bin .add (.const 1) (.reg 18)))
        ⟨stC.mem, r4, stC.pos⟩ .normal ⟨stC.mem, r5, stC.pos⟩ 4 :=
      runs_assign_iff.mpr ⟨1 + rotW,
        Expr.eval_add (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [r4, r3])) (by omega),
        rfl, rfl, rfl⟩
    have hmC_lt : ∀ a < hCur, stC.mem a = st.mem a := fun a ha =>
      (hfrC a (Or.inl (by omega))).trans (Function.update_of_ne (by omega) _ _)
    have hlocC := tourAsmRep_local vCap eCap tourH (tourToAsmTour s) tx st.mem stC.mem
      fun a ha => (hmC_lt a (hfoot a ha)).symm
    have hordEd : OrdEditsAt stC.mem hCur rotEds (1 + rotW) :=
      ordEditsAt_rotTail
        ((hfrC hCur (Or.inl (by omega))).trans (Function.update_self hCur remRot st.mem))
        hdec hsum hrot (fun i hi => (hcpC i hi).trans (Function.update_of_ne (by omega) _ _))
    have hImpl := (tourDS_implements w vCap eCap p bTour hpT hw).2
    have hargs0 : ∀ a ∈ [tourH, hCur, 1 + rotW, hCur + (1 + rotW)], a < 2 ^ w := by
      intro a ha; simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> omega
    have hpre0 : (tourContract vCap eCap tourMul tourAlloc).pre 0 s
        [tourH, hCur, 1 + rotW, hCur + (1 + rotW)] stC.mem :=
      ⟨tourH, hCur, 1 + rotW, hCur + (1 + rotW), rfl, by rwa [hordEd.1], le_refl _, by rwa [hordEd.1]⟩
    have hsp0 : hCur + (1 + rotW) + (tourContract vCap eCap tourMul tourAlloc).space 0 s
        [tourH, hCur, 1 + rotW, hCur + (1 + rotW)] stC.mem < 2 ^ w := by
      simp only [tourContract, tourAlloc, tourOp0Space]
      rw [show [tourH, hCur, 1 + rotW, hCur + (1 + rotW)].getD 2 0 = 1 + rotW from rfl]; omega
    have hfootC : ∀ x, (tourDSRep vCap eCap).foot tourH tx x →
        x < heapArg [tourH, hCur, 1 + rotW, hCur + (1 + rotW)] :=
      fun x hx => lt_trans (hfoot x hx) (by show hCur < hCur + (1 + rotW); omega)
    have hzeroC : ZeroFrom stC.mem (heapArg [tourH, hCur, 1 + rotW, hCur + (1 + rotW)]) := fun x hx => by
      change hCur + (1 + rotW) ≤ x at hx
      exact (hfrC x (Or.inr (by omega))).trans
        ((Function.update_of_ne (by omega) _ _).trans (hzero x (by omega)))
    obtain ⟨bd0, hbd0, o0, st0, c0, hrun0, s1, tx', hrep', hpost0, hresp0, hcost0⟩ :=
      hImpl.2.2 0 tourH s tx [tourH, hCur, 1 + rotW, hCur + (1 + rotW)] stC.mem stC.pos ω hargs0 rfl
        (hlocC.1 hrep) hpre0 hfootC hzeroC hsp0
    have hs1_eq : s1 = tourApplyEdits s rotEds := by simpa [tourContract, hordEd.1] using hpost0
    subst hs1_eq
    set r6 := Function.update r5 9 o0.value
    have hcall0 : Runs w p ω (.call 9 (tourOp bTour 0) [.reg 0, .reg 9, .reg 20, .bin .add (.reg 9) (.reg 20)])
        ⟨stC.mem, r5, stC.pos⟩ .normal ⟨st0.mem, r6, st0.pos⟩
        (argsSize [.reg 0, .reg 9, .reg 20, .bin .add (.reg 9) (.reg 20)] + c0 + 1) :=
      runs_call_iff.mpr ⟨_, bd0, o0, st0, c0,
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [r5, r4, r3, r2, r1, hr0])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [r5, r4, r3, r2, r1, hr9])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [r5])) <|
        evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r5, r4, r3, r2, r1, hr9]))
          (Expr.eval_reg_of_eq (by simp [r5])) (by omega)) <|
        evalArgs_nil _ _,
        hbd0, hrun0, rfl, rfl, rfl⟩
    have hbody := runs_seq_normal ha18 (runs_seq_normal hst1 (runs_seq_normal hcallC
      (runs_seq_normal ha20 hcall0)))
    have hrc : Runs w p ω
        (.cond (.bin .lt (.const 0) (.reg 17))
          (.assign 18 (.bin .sub (.bin .add (.reg 8) (.reg 4)) (.reg 13)) ;;
           .store (.reg 9) (.reg 17) ;;
           .call 19 bCopy [.reg 13, .bin .add (.reg 9) (.const 1), .reg 18] ;;
           .assign 20 (.bin .add (.const 1) (.reg 18)) ;;
           .call 9 (tourOp bTour 0) [.reg 0, .reg 9, .reg 20, .bin .add (.reg 9) (.reg 20)])
          .nop)
        { st with regs := r2 } .normal ⟨st0.mem, r6, st0.pos⟩ _ :=
      runs_cond_iff.mpr ⟨1, _, hcond, by simpa using hbody, rfl⟩
    have hha0 : heapArg [tourH, hCur, 1 + rotW, hCur + (1 + rotW)] = hCur + (1 + rotW) := rfl
    rw [hha0] at hresp0
    simp only [tourContract, tourAlloc, tourOp0Space] at hresp0 hcost0
    rw [show [tourH, hCur, 1 + rotW, hCur + (1 + rotW)].getD 2 0 = 1 + rotW from rfl] at hresp0 hcost0
    have ho0_lo : hCur + (1 + rotW) ≤ o0.value := hresp0.1
    have ho0_hi : o0.value ≤ hCur + (1 + rotW) + (12 * (1 + rotW) + 12) := hresp0.2.1
    refine ⟨o0.value, ⟨st0.mem, r6, st0.pos⟩, _, tx',
      runs_seq_normal ha16 (runs_seq_normal ha17 hrc),
      by simp [r6], fun r h9 h16 h17 h18 h19 h20 => by simp [r6, r5, r4, r3, r2, r1, h9, h16, h17, h18, h19, h20],
      hrep', by omega, by omega, hresp0.2.2.1,
      fun x hx hnf => (hresp0.2.2.2.1 x (by omega) hnf).trans (hmC_lt x hx),
      fun x hx => by
        rcases hresp0.2.2.2.2 x hx with h0 | ⟨hge, hlt⟩
        · exact Or.inl h0
        · exact Or.inr ⟨by omega, hlt⟩, ?_⟩
    have hphiC : (tourDSRep vCap eCap).phi tourH tx st.mem = (tourDSRep vCap eCap).phi tourH tx stC.mem := hlocC.2
    rw [← hphiC, ← ordStoreLog_eq_tourLog] at hcost0
    simp only [copyWordsContract, Expr.size] at hcostC ⊢
    have ht1 : tourMul * (1 + rotW + 1) * ordStoreLog eCap ≤
        5 * tourMul * (rotW + 2) * ordStoreLog eCap := by
      rw [show 1 + rotW + 1 = rotW + 2 by omega]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    have h500 : 17 * rotW + 80 ≤ 500 * (rotW + 2) * ordStoreLog eCap :=
      le_trans (by omega) (Nat.le_mul_of_pos_right _ htl)
    have hbm : 5 * tourMul * (rotW + 2) * ordStoreLog eCap + 500 * (rotW + 2) * ordStoreLog eCap ≤
        tourBlockCaseMul * (rotW + 2) * ordStoreLog eCap := by
      rw [tourBlockCaseMul_eq, tourBlockCaseMulFn_eq]
      have : 5 * tourMul + 500 ≤ 5 * tourMul + outSmallSideMul * (tourOutSpec.mul + 1) +
          tourConsumeRelMul + tourApplyMoveMul + 500 := by omega
      rw [← Nat.add_mul, ← Nat.add_mul]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
    have hgoal_phi : (tourAsmRep vCap eCap).phi tourH tx' st0.mem = (tourDSRep vCap eCap).phi tourH tx' st0.mem ∧
        (tourAsmRep vCap eCap).phi tourH tx st.mem = (tourDSRep vCap eCap).phi tourH tx st.mem := ⟨rfl, rfl⟩
    rw [hgoal_phi.1, hgoal_phi.2]
    clear * - hcost0 hcostC ht1 h500 hbm
    omega

end

end MinCostFlow.SparseCore.Program
