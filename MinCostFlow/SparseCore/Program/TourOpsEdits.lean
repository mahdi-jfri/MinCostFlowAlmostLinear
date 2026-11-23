module

public import MinCostFlow.SparseCore.Program.TourOpsEditsPrep
import Mathlib.Tactic

/-!
# Batch edit operation (`applyEdits`, Op 0)

Implements and verifies `tourOpApplyEditsBody [b, edits, words, heap]` (Op 0 of `tourContract`):
1. Copies `edits[0 .. words)` to `heap + 1 .. heap + 1 + words`, avoiding any aliasing with
   `tourFoot` and leaving `ptr - 1` writable for zero-copy 1-edit forwarding.
2. Iterates over the `count` edits, dispatching each edit to `tourEditDropBody`,
   `tourEditMoveBody`, `tourEditInsertBody`, or `tourEditRotateBody`, and committing the single
   edit to the embedded `ordStore` (`ordOp 0`, deduplicating `moveEnds` keys via `tourDedupSelBody`
   so `OrdEditsAt`'s `words' ≤ 5 * ordEditsEnc [edit] + 1` bound holds unconditionally).
3. Runs in amortized cost `≤ (TOUR_OP0_BASE_MUL + 6 * mul_ord) * (words + 1) * tourLog eCap` and
   linear heap space `tourOp0Space words = 12 * words + 12` (zero dependence on `heap`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.DynSpanner.Program
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Main verified run theorem for Op 0 (`applyEdits`) -/

private theorem decodeOrdEdits_count_le_sum (mem : ℕ → ℕ) :
    ∀ count a, count ≤ (decodeOrdEdits mem count a).2.sum
  | 0, _ => Nat.zero_le _
  | count + 1, a => by
    simp only [decodeOrdEdits, List.sum_cons]
    have h2 := decodeOrdEdit_words_ge_two mem a
    have hih := decodeOrdEdits_count_le_sum mem count (a + (decodeOrdEdit mem a).2)
    omega

private theorem move_cost_combine_nat {cB cM cDed cO pM pC oO oM oC t1 t2 t3 k : ℕ}
    (h0 : cB ≤ cM + cDed + cO + 150)
    (h1 : cM + pM + oM ≤ pC + oC + t1) (h2 : cDed ≤ k) (h3 : cO + oO ≤ t2 + oM)
    (h4 : t1 + k + t2 + 200 ≤ t3) :
    cB + (oO + pM) ≤ (oC + pC) + t3 - 20 := by omega

set_option maxHeartbeats 600000 in
/-- Verified amortized run theorem for Op 0 (`applyEdits [b, edits, words, heap]`), using linear
heap space `tourOp0Space words = 12 * words + 12` (independent of `heap`) and amortized cost
`(TOUR_OP0_MUL + 6 * mul_ord) * (words + 1) * tourLog eCap`. -/
theorem tourOp_applyEdits_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap mul_ord b edits words heap pos ordInit ordOp0 ordOp2 : ℕ}
    {alloc_ord : ℕ → List ℕ → ℕ} {p : Program} {ordOp : ℕ → ℕ}
    (E : TourEditProcs w p ordOp0 ordOp2)
    (hOrdImpl : R_ord.Implements w p ordInit ordOp (ordStoreCapContract vCap eCap mul_ord alloc_ord))
    (hop0 : ordOp 0 = ordOp0) (hop2 : ordOp 2 = ordOp2)
    (halloc : ∀ h e ws h0, alloc_ord 0 [h, e, ws, h0] ≤ 3 * ws + 2)
    (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hEditsAt : OrdEditsAt mem edits (readOrdEdits mem edits) words)
    (hEditsLe : edits + words ≤ heap)
    (hValid : TourEditsValid vCap eCap s (readOrdEdits mem edits))
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 18 ≤ 2 ^ w)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap)
    (hroom : heap + tourOp0Space words < 2 ^ w) :
    ∃ o st' c, Runs w p ω (tourOpApplyEditsBody E.dropProc E.moveProc E.insProc E.rotProc E.dedupProc ordOp0)
        (startState [b, edits, words, heap] mem pos) o st' c ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b (tourApplyEdits s (readOrdEdits mem edits)) x' st'.mem ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap (tourOp0Space words)
          mem o.value b x' st'.mem ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          (TOUR_OP0_MUL + 6 * mul_ord) * (words + 1) * tourLog eCap +
            (tourRep R_ord vCap eCap).phi b x mem := by
  classical
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hord_le : ordHandleOf b vCap eCap ≤ heap := h.fixed_le_heap hfoot
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hwords_ge1 : 1 ≤ words := by have := hEditsAt.2.1; omega
  have hroom_unfold : heap + (12 * words + 12) < 2 ^ w := hroom
  set count := mem edits
  have hcount_lt_words : count < words := by
    have hle := decodeOrdEdits_count_le_sum mem (mem edits) (edits + 1)
    have hweq := hEditsAt.2.1
    dsimp only [count]; omega
  set bufEnd := heap + 1 + words
  set s0 : State := startState [b, edits, words, heap] mem pos
  set r1 := Function.update s0.regs 4 0
  set r2 := Function.update r1 5 (heap + 1)
  have ha4 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 4) (val := 0) (st := s0) (by omega)
  have ha5 : Runs w p ω (.assign 5 (.bin .add (.reg 3) (.const 1))) ⟨mem, r1, pos⟩ .normal ⟨mem, r2, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨heap + 1, by
      simp [Expr.eval, r1, s0, startState, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : heap + 1 < 2 ^ w)], rfl, rfl, rfl⟩
  obtain ⟨stCp, cCp, hrunCp, hCp_ro, hCp_mem, hCp_fr, hcCp⟩ :=
    tourEditsCopyLoop_runs (w := w) (src := edits) (dst := heap + 1) (words := words) (st0 := ⟨mem, r2, pos⟩) ω
      (by simp [r2, r1, s0, startState]) (by simp [r2, r1, s0, startState]) (by simp [r2, r1]) (by simp [r2])
      (by omega) (by omega) (by omega)
  have hCp_lt : ∀ a < heap, stCp.mem a = mem a := fun a ha => hCp_fr a (Or.inl (by omega))
  have hCp_zero : ZeroFrom stCp.mem bufEnd := fun a ha => by
    rw [hCp_fr a (Or.inr (by omega))]; exact hzero a (by omega)
  have hRepCp : TourRepAt R_ord vCap eCap b s x stCp.mem :=
    ((tourRep_local hOrdImpl.1 vCap eCap) b s x mem stCp.mem fun a ha => (hCp_lt a (hfoot a ha)).symm).1 h
  have hPhiCp : tourPhi R_ord vCap eCap b x stCp.mem = tourPhi R_ord vCap eCap b x mem :=
    ((tourRep_local hOrdImpl.1 vCap eCap) b s x mem stCp.mem fun a ha => (hCp_lt a (hfoot a ha)).symm).2.symm
  -- Load `count`, initialize `ptr = heap + 2`, `hCur = bufEnd`, `idx = 0`, `ordH`
  set rP1 := Function.update stCp.regs 4 count
  set rP2 := Function.update rP1 5 (heap + 2)
  set rP3 := Function.update rP2 6 bufEnd
  set rP4 := Function.update rP3 7 0
  set rP5 := Function.update rP4 14 (ordHandleOf b vCap eCap)
  have hp1 : Runs w p ω (.assign 4 (.load (.reg 5))) stCp .normal { stCp with regs := rP1 } 3 :=
    runs_assign_iff.mpr ⟨count, by
      have h0 : stCp.mem (heap + 1) = count := by simpa [count] using hCp_mem 0 (by omega)
      simp [Expr.eval, hCp_ro 5 (by decide) (by decide), r2, h0], rfl, rfl, rfl⟩
  have hp2 : Runs w p ω (.assign 5 (.bin .add (.reg 5) (.const 1))) { stCp with regs := rP1 } .normal { stCp with regs := rP2 } 4 :=
    runs_assign_iff.mpr ⟨heap + 2, by
      simp [Expr.eval, rP1, hCp_ro 5 (by decide) (by decide), r2, BinOp.eval,
        (by omega : 1 < 2 ^ w), (by omega : heap + 1 + 1 < 2 ^ w)], rfl, rfl, rfl⟩
  have hp3 : Runs w p ω (.assign 6 (.bin .add (.bin .add (.reg 3) (.const 1)) (.reg 2)))
      { stCp with regs := rP2 } .normal { stCp with regs := rP3 } 6 :=
    runs_assign_iff.mpr ⟨bufEnd, by
      simp [Expr.eval, rP2, rP1, hCp_ro 3 (by decide) (by decide), hCp_ro 2 (by decide) (by decide),
        r2, r1, s0, startState, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : heap + 1 < 2 ^ w),
        (by omega : heap + 1 + words < 2 ^ w), bufEnd], rfl, rfl, rfl⟩
  have hp4 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 7) (val := 0) (st := { stCp with regs := rP3 }) (by omega)
  have hp5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 14) (rBase := 0) (off := HDR_ORD_H)
    (b := b) (val := ordHandleOf b vCap eCap) (st := { stCp with regs := rP4 })
    (by simp [rP4, rP3, rP2, rP1, hCp_ro 0 (by decide) (by decide), r2, r1, s0, startState])
    (by simp only [HDR_ORD_H]; omega) (by simp only [HDR_ORD_H]; omega) hRepCp.header.2.2.1
  -- Main dispatch loop induction on remaining edit count `rem`
  have hloop : ∀ (rem idx ptr hCur : ℕ) (sC : TourAbs) (xC : TourConcrete R_ord.τ) (stC : State),
      idx + rem = count →
      let dec := decodeOrdEdits stC.mem rem ptr
      let remWords := dec.2.sum
      heap + 2 ≤ ptr → ptr + remWords = bufEnd → bufEnd ≤ hCur →
      hCur + 10 * remWords + 12 ≤ heap + tourOp0Space words →
      stC.regs 0 = b → stC.regs 4 = count → stC.regs 5 = ptr → stC.regs 6 = hCur →
      stC.regs 7 = idx → stC.regs 14 = ordHandleOf b vCap eCap →
      TourRepAt R_ord vCap eCap b sC xC stC.mem →
      TourEditsValid vCap eCap sC dec.1 →
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) xC.ordX a →
        R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (bufEnd ≤ a ∧ a < hCur)) →
      (∀ a < heap, ¬tourFoot R_ord vCap eCap b x a → stC.mem a = mem a) →
      ZeroFrom stC.mem hCur →
      ∃ (hF : ℕ) (xF : TourConcrete R_ord.τ) (stF : State) (cL : ℕ),
        Runs w p ω (tourEditsDispatchLoop E.dropProc E.moveProc E.insProc E.rotProc E.dedupProc ordOp0)
          stC .normal stF cL ∧
        stF.regs 6 = hF ∧ hCur ≤ hF ∧ hF ≤ hCur + 10 * remWords ∧ ZeroFrom stF.mem hF ∧
        TourRepAt R_ord vCap eCap b (tourApplyEdits sC dec.1) xF stF.mem ∧
        (∀ a, R_ord.foot (ordHandleOf b vCap eCap) xF.ordX a →
          R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (bufEnd ≤ a ∧ a < hF)) ∧
        (∀ a < heap, ¬tourFoot R_ord vCap eCap b x a → stF.mem a = mem a) ∧
        cL + tourPhi R_ord vCap eCap b xF stF.mem ≤
          tourPhi R_ord vCap eCap b xC stC.mem + remWords * (TOUR_OP0_BASE_MUL + 6 * mul_ord) * tourLog eCap + 20 := by
    intro rem
    induction rem with
    | zero =>
      intro idx ptr hCur sC xC stC hrem dec remWords _ _ _ _ _ hr4 _ hr6 hr7 _ hRepC _ hFtC hFrC hZC
      have hic : idx = count := by omega
      have hcond : (Expr.bin .lt (.reg 7) (.reg 4)).eval w stC = some 0 := by
        simp [Expr.eval, hr7, hr4, hic, BinOp.eval, (by omega : 0 < 2 ^ w)]
      refine ⟨hCur, xC, stC, _, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
        hr6, le_refl _, by simp [remWords, dec, decodeOrdEdits], hZC,
        by simpa [dec, decodeOrdEdits, tourApplyEdits] using hRepC, hFtC, hFrC, by simp [Expr.size]; omega⟩
    | succ rem ih =>
      intro idx ptr hCur sC xC stC hrem dec remWords hptr_ge hptr_end hh_ge hh_sp
        hr0 hr4 hr5 hr6 hr7 hr14 hRepC hValC hFtC hFrC hZC
      have hilt : idx < count := by omega
      have hcond : (Expr.bin .lt (.reg 7) (.reg 4)).eval w stC = some 1 := by
        simp [Expr.eval, hr7, hr4, hilt, BinOp.eval, (by omega : 1 < 2 ^ w)]
      set d := decodeOrdEdit stC.mem ptr
      set edit := d.1
      set wk := d.2
      set decRest := decodeOrdEdits stC.mem rem (ptr + wk)
      have hremW_eq : remWords = wk + decRest.2.sum := by simp [remWords, dec, decodeOrdEdits, wk, d, decRest]
      have hdec1_eq : dec.1 = edit :: decRest.1 := by simp [dec, decodeOrdEdits, edit, wk, d, decRest]
      have hval_head : TourEditValid vCap eCap sC edit ∧ TourEditsValid vCap eCap (tourApplyEdit sC edit) decRest.1 := by
        simpa [hdec1_eq, TourEditsValid] using hValC
      have hwk_ge2 : 2 ≤ wk := decodeOrdEdit_words_ge_two stC.mem ptr
      have hordFootC : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) xC.ordX a → a < hCur := fun a ha => by
        rcases hFtC a ha with h0 | ⟨_, h2⟩
        · exact lt_of_lt_of_le (hfoot a (Or.inr h0)) (by omega)
        · exact h2
      have hordFootC_notBuf : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) xC.ordX a → a < heap ∨ bufEnd ≤ a := fun a ha => by
        rcases hFtC a ha with h0 | ⟨h1, _⟩
        · exact Or.inl (hfoot a (Or.inr h0))
        · exact Or.inr h1
      have hordU : OrdUniqueWithin vCap eCap sC.ord := ⟨hRepC.valid.ordWithin, hRepC.valid.compat.unique⟩
      have hord_le_hCur : ordHandleOf b vCap eCap ≤ hCur := by omega
      set tag := stC.mem ptr
      set rT := Function.update stC.regs 8 tag
      have ha8 : Runs w p ω (.assign 8 (.load (.reg 5))) stC .normal { stC with regs := rT } 3 :=
        runs_assign_iff.mpr ⟨tag, by simp [Expr.eval, hr5, tag], rfl, rfl, rfl⟩
      -- Unified post-step induction lemma: once one edit runs from `{ stC with regs := rT }` to `st1`
      have hstep_to_ih : ∀ (hNext : ℕ) (x1 : TourConcrete R_ord.τ) (st1 : State) (cBody : ℕ),
          Runs w p ω (.cond (.bin .eq (.reg 8) (.const 0))
            (.assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
             .call 6 E.dropProc [.reg 0, .reg 9, .reg 6] ;;
             .assign 10 (.bin .sub (.reg 5) (.const 1)) ;;
             .store (.reg 10) (.const 1) ;;
             .assign 11 (.const 3) ;;
             .call 6 ordOp0 [.reg 14, .reg 10, .reg 11, .reg 6] ;;
             .assign 5 (.bin .add (.reg 5) (.const 2)))
            (.cond (.bin .lt (.reg 8) (.const 3))
              (.assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
               .assign 10 (.load (.bin .add (.reg 5) (.const 2))) ;;
               .assign 11 (.load (.bin .add (.reg 5) (.const 3))) ;;
               .assign 12 (.bin .add (.reg 5) (.const 4)) ;;
               .call 6 E.moveProc [.reg 0, .reg 5, .reg 6] ;;
               .store (.reg 6) (.const 1) ;;
               .store (.bin .add (.reg 6) (.const 1)) (.reg 8) ;;
               .store (.bin .add (.reg 6) (.const 2)) (.reg 9) ;;
               .store (.bin .add (.reg 6) (.const 3)) (.reg 10) ;;
               .assign 13 (.bin .add (.reg 6) (.const 5)) ;;
               .call 15 E.dedupProc [.reg 0, .reg 12, .reg 11, .reg 13] ;;
               .store (.bin .add (.reg 6) (.const 4)) (.reg 15) ;;
               .assign 13 (.bin .add (.const 5) (.reg 15)) ;;
               .assign 15 (.bin .add (.reg 6) (.reg 13)) ;;
               .call 6 ordOp0 [.reg 14, .reg 6, .reg 13, .reg 15] ;;
               .assign 5 (.bin .add (.reg 12) (.reg 11)))
              (.cond (.bin .eq (.reg 8) (.const 3))
                (.assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
                 .assign 10 (.load (.bin .add (.reg 5) (.const 2))) ;;
                 .assign 11 (.load (.bin .add (.reg 5) (.const 3))) ;;
                 .call 6 E.insProc [.reg 0, .reg 9, .reg 10, .reg 11, .reg 6] ;;
                 .assign 10 (.bin .sub (.reg 5) (.const 1)) ;;
                 .store (.reg 10) (.const 1) ;;
                 .assign 11 (.const 5) ;;
                 .call 6 ordOp0 [.reg 14, .reg 10, .reg 11, .reg 6] ;;
                 .assign 5 (.bin .add (.reg 5) (.const 4)))
                (.assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
                 .assign 10 (.load (.bin .add (.reg 5) (.const 2))) ;;
                 .call 6 E.rotProc [.reg 0, .reg 9, .reg 10, .reg 6] ;;
                 .assign 10 (.bin .sub (.reg 5) (.const 1)) ;;
                 .store (.reg 10) (.const 1) ;;
                 .assign 11 (.const 4) ;;
                 .call 6 ordOp0 [.reg 14, .reg 10, .reg 11, .reg 6] ;;
                 .assign 5 (.bin .add (.reg 5) (.const 3)))))) { stC with regs := rT } .normal st1 cBody →
          hCur ≤ hNext → hNext ≤ hCur + 10 * wk → ZeroFrom st1.mem hNext →
          st1.regs 0 = b → st1.regs 4 = count → st1.regs 5 = ptr + wk → st1.regs 6 = hNext →
          st1.regs 7 = idx → st1.regs 14 = ordHandleOf b vCap eCap →
          TourRepAt R_ord vCap eCap b (tourApplyEdit sC edit) x1 st1.mem →
          (∀ a, R_ord.foot (ordHandleOf b vCap eCap) x1.ordX a →
            R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (bufEnd ≤ a ∧ a < hNext)) →
          (∀ a < heap, ¬tourFoot R_ord vCap eCap b x a → st1.mem a = mem a) →
          (∀ a, ptr + wk ≤ a → a < bufEnd → st1.mem a = stC.mem a) →
          cBody + tourPhi R_ord vCap eCap b x1 st1.mem ≤
            tourPhi R_ord vCap eCap b xC stC.mem + wk * (TOUR_OP0_BASE_MUL + 6 * mul_ord) * tourLog eCap - 20 →
          ∃ (hF : ℕ) (xF : TourConcrete R_ord.τ) (stF : State) (cL : ℕ),
            Runs w p ω (tourEditsDispatchLoop E.dropProc E.moveProc E.insProc E.rotProc E.dedupProc ordOp0)
              stC .normal stF cL ∧
            stF.regs 6 = hF ∧ hCur ≤ hF ∧ hF ≤ hCur + 10 * remWords ∧ ZeroFrom stF.mem hF ∧
            TourRepAt R_ord vCap eCap b (tourApplyEdits sC dec.1) xF stF.mem ∧
            (∀ a, R_ord.foot (ordHandleOf b vCap eCap) xF.ordX a →
              R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (bufEnd ≤ a ∧ a < hF)) ∧
            (∀ a < heap, ¬tourFoot R_ord vCap eCap b x a → stF.mem a = mem a) ∧
            cL + tourPhi R_ord vCap eCap b xF stF.mem ≤
              tourPhi R_ord vCap eCap b xC stC.mem + remWords * (TOUR_OP0_BASE_MUL + 6 * mul_ord) * tourLog eCap + 20 := by
        intro hNext x1 st1 cBody hrunB hhN_ge hhN_le hZ1 h10 h14 h15 h16 h17 h114 hRep1 hFt1 hFr1 hBuf1 hcB
        set rInc := Function.update st1.regs 7 (idx + 1)
        have ha7 : Runs w p ω (.assign 7 (.bin .add (.reg 7) (.const 1))) st1 .normal { st1 with regs := rInc } 4 :=
          runs_assign_iff.mpr ⟨idx + 1, by
            simp [Expr.eval, h17, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : idx + 1 < 2 ^ w)], rfl, rfl, rfl⟩
        have hdec_eq : decodeOrdEdits st1.mem rem (ptr + wk) = decRest :=
          tour_decodeOrdEdits_shift (m₁ := stC.mem) (m₂ := st1.mem) rem (ptr + wk) (ptr + wk)
            fun i hi => hBuf1 _ (by omega) (by change i < decRest.2.sum at hi; omega)
        obtain ⟨hF, xF, stF, cL, hrunL, hF6, hF_ge, hF_le, hZF, hRepF, hFtF, hFrF, hcL⟩ :=
          ih (idx + 1) (ptr + wk) hNext (tourApplyEdit sC edit) x1 { st1 with regs := rInc } (by omega)
            (by omega) (by dsimp only; rw [hdec_eq]; omega) (by omega) (by dsimp only; rw [hdec_eq]; omega)
            (by simp [rInc, h10]) (by simp [rInc, h14]) (by simp [rInc, h15]) (by simp [rInc, h16])
            (by simp [rInc]) (by simp [rInc, h114]) hRep1 (by dsimp only; rw [hdec_eq]; exact hval_head.2)
            hFt1 hFr1 hZ1
        have happ : tourApplyEdits sC dec.1 = tourApplyEdits (tourApplyEdit sC edit) (decodeOrdEdits st1.mem rem (ptr + wk)).1 := by
          rw [hdec1_eq, hdec_eq]; rfl
        refine ⟨hF, xF, stF, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega,
          tour_runs_seq_normal ha8 (tour_runs_seq_normal hrunB ha7), hrunL, rfl⟩)),
          hF6, le_trans hhN_ge hF_ge, by rw [hdec_eq] at hF_le; omega, hZF, happ ▸ hRepF, hFtF, hFrF, ?_⟩
        rw [hdec_eq] at hcL
        have hmul : remWords * (TOUR_OP0_BASE_MUL + 6 * mul_ord) * tourLog eCap =
            wk * (TOUR_OP0_BASE_MUL + 6 * mul_ord) * tourLog eCap +
            decRest.2.sum * (TOUR_OP0_BASE_MUL + 6 * mul_ord) * tourLog eCap := by
          rw [hremW_eq]; ring
        have hge20 : 20 ≤ wk * (TOUR_OP0_BASE_MUL + 6 * mul_ord) * tourLog eCap := by
          clear * - hwk_ge2 htl
          have h1 : 20 ≤ wk * (TOUR_OP0_BASE_MUL + 6 * mul_ord) := by
            unfold TOUR_OP0_BASE_MUL; nlinarith
          exact le_trans (by omega : 20 ≤ 20 * 1) (Nat.mul_le_mul h1 htl)
        clear * - hcB hcL hmul hge20; simp only [Expr.size] at *; omega
      -- Dispatch on `tag` (`0` dropEdge, `1/2` moveEnds, `3` insertBefore, else rotateTo)
      by_cases ht0 : tag = 0
      · -- Case `dropEdge e` (`wk = 2`)
        have hed : edit = .dropEdge (stC.mem (ptr + 1)) ∧ wk = 2 := by
          simp [edit, wk, d, decodeOrdEdit, tag, ht0]
        set e := stC.mem (ptr + 1)
        have heV : e < eCap ∧ e ∉ sC.rf.F.E := by simpa [hed.1, TourEditValid] using hval_head.1
        have hc0 : (Expr.bin .eq (.reg 8) (.const 0)).eval w { stC with regs := rT } = some 1 := by
          simp [Expr.eval, rT, ht0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
        set r1 := Function.update rT 9 e
        have ha9 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 9) (rBase := 5) (off := 1)
          (b := ptr) (val := e) (st := { stC with regs := rT }) (by simp [rT, hr5]) (by omega) (by omega) rfl
        obtain ⟨hMid, stM, cD, xM, hrunD, hhM_ge, hhM_le, hZM, hfrM, hftM, hgeM, hrepM, hcoreM, hcD⟩ :=
          tourEditDropBody_runs (pos := stC.pos) E.toTourSplayQueryProcs hOrdImpl hop2 E.dropOne_body ω
            hRepC.toCore hRepC.ordRep hRepC.ordFootGe hordFootC heV.1 heV.2 hord_le_hCur (by omega) hw hwide hZC
        have hcallD := runs_call_regs3 6 0 9 6 (st := { stC with regs := r1 }) E.drop_body
          (by simp [r1, rT, hr0]) (by simp [r1]) (by simp [r1, rT, hr6]) hrunD
        set r2 := Function.update r1 6 hMid
        set r3 := Function.update r2 10 (ptr - 1)
        set mW := Function.update stM.mem (ptr - 1) 1
        set r4 := Function.update r3 11 3
        have ha10 : Runs w p ω (.assign 10 (.bin .sub (.reg 5) (.const 1))) { stM with regs := r2 } .normal { stM with regs := r3 } 4 :=
          runs_assign_iff.mpr ⟨ptr - 1, by simp [Expr.eval, r2, r1, rT, hr5, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : ptr - 1 < 2 ^ w)], rfl, rfl, rfl⟩
        have hst1 : Runs w p ω (.store (.reg 10) (.const 1)) { stM with regs := r3 } .normal { stM with mem := mW, regs := r3 } 3 :=
          runs_store_iff.mpr ⟨ptr - 1, 1, by simp [Expr.eval, r3], by simp [Expr.eval, (by omega : 1 < 2 ^ w)], rfl, rfl, rfl⟩
        have ha11 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 11) (val := 3) (st := { stM with mem := mW, regs := r3 }) (by omega)
        have hftM_lt : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) xM.ordX a → a < hMid := fun a ha => by
          rcases hftM a ha with h0 | ⟨_, h2⟩; exact lt_of_lt_of_le (hordFootC a h0) hhM_ge; exact h2
        have hftM_notBuf : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) xM.ordX a → a < heap ∨ bufEnd ≤ a := fun a ha => by
          rcases hftM a ha with h0 | ⟨h1, _⟩; exact hordFootC_notBuf a h0; exact Or.inr (by omega)
        have hcoreW : TourCoreAt vCap eCap b (tourApplyEdit sC edit) xM mW := by
          rw [hed.1]; exact hcoreM.congr_fixed fun a _ ha2 => Function.update_of_ne (by omega) _ _
        have hOrdW := hOrdImpl.1 (ordHandleOf b vCap eCap) sC.ord xM.ordX stM.mem mW fun a ha =>
          (Function.update_of_ne (by rcases hftM_notBuf a ha with h1 | h2 <;> omega) _ _).symm
        have hstM_buf : ∀ a, ptr ≤ a → a < bufEnd → stM.mem a = stC.mem a := fun a ha1 ha2 =>
          hfrM a (by omega) (Or.inr (by omega)) (fun hft => by rcases hordFootC_notBuf a hft with h1 | h2 <;> omega)
        have hEdits1 : OrdEditsAt mW (ptr - 1) [edit] 3 := by
          have hdecW : decodeOrdEdit mW (ptr - 1 + 1) = (edit, 2) := by
            have heq : ptr - 1 + 1 = ptr := by omega
            rw [heq]; refine (tour_decodeOrdEdit_shift (m₁ := stC.mem) (m₂ := mW) (a₁ := ptr) (a₂ := ptr) fun i hi => ?_).trans (Prod.ext rfl hed.2)
            have hi2 : i < 2 := by change i < wk at hi; omega
            dsimp only [mW]; rw [Function.update_of_ne (by omega)]; exact hstM_buf _ (by omega) (by omega)
          exact tour_singleEdit_ordEditsAt_simple (by simp [mW]) hdecW (by omega)
        have halloc_le := halloc (ordHandleOf b vCap eCap) (ptr - 1) 3 hMid
        obtain ⟨bodyO, oO, stO, cO, ordXO, hgetO, hrunO, hhO_ge, hhO_le, hZO, hfrO, hftO, hRepO, hcO⟩ :=
          tourCore_commitOrdStore (pos := stM.pos) hOrdImpl hop0 ω hcoreW hordU (hOrdW.1 hrepM) hgeM hftM_lt
            (by omega) hEdits1 (by omega) (tourEditValid_to_ordEditsWithin hval_head.1) (by rw [hed.1]; rfl)
            (fun a ha => by dsimp only [mW]; rw [Function.update_of_ne (by omega)]; exact hZM a ha) (by omega)
        have hcallO := runs_call_regs4 6 14 10 11 6 (st := { stM with mem := mW, regs := r4 }) hgetO
          (by simp [r4, r3, r2, r1, rT, hr14]) (by simp [r4, r3]) (by simp [r4]) (by simp [r4, r3, r2]) hrunO
        set r5 := Function.update r4 6 oO.value
        set r6 := Function.update r5 5 (ptr + 2)
        have ha5 : Runs w p ω (.assign 5 (.bin .add (.reg 5) (.const 2))) { stO with regs := r5 } .normal { stO with regs := r6 } 4 :=
          runs_assign_iff.mpr ⟨ptr + 2, by simp [Expr.eval, r5, r4, r3, r2, r1, rT, hr5, BinOp.eval, (by omega : 2 < 2 ^ w), (by omega : ptr + 2 < 2 ^ w)], rfl, rfl, rfl⟩
        apply hstep_to_ih oO.value { xM with ordX := ordXO } { stO with regs := r6 } _
          (tour_runs_cond_true hc0 (by omega) (tour_runs_seq_normal ha9 (tour_runs_seq_normal hcallD (tour_runs_seq_normal ha10
            (tour_runs_seq_normal hst1 (tour_runs_seq_normal ha11 (tour_runs_seq_normal hcallO ha5)))))))
          (by omega) (by omega) hZO
          (by simp [r6, r5, r4, r3, r2, r1, rT, hr0]) (by simp [r6, r5, r4, r3, r2, r1, rT, hr4])
          (by simp [r6, hed.2]) (by simp [r6, r5])
          (by simp [r6, r5, r4, r3, r2, r1, rT, hr7]) (by simp [r6, r5, r4, r3, r2, r1, rT, hr14])
          hRepO
          (fun a ha => by
            rcases hftO a ha with h1 | ⟨ha1, ha2⟩
            · rcases hftM a h1 with h0 | ⟨hb1, hb2⟩
              · exact (hFtC a h0).imp id fun ⟨hc1, hc2⟩ => ⟨hc1, by omega⟩
              · exact Or.inr ⟨by omega, by omega⟩
            · exact Or.inr ⟨by omega, ha2⟩)
          (fun a ha hnf => by
            have hnfC : ¬R_ord.foot (ordHandleOf b vCap eCap) xC.ordX a := fun hft => by
              rcases hFtC a hft with h0 | ⟨h1, _⟩; exact hnf (Or.inr h0); omega
            have hnfM : ¬R_ord.foot (ordHandleOf b vCap eCap) xM.ordX a := fun hft => by
              rcases hftM a hft with h0 | ⟨h1, _⟩; exact hnfC h0; omega
            have ha_out : a < b ∨ ordHandleOf b vCap eCap ≤ a := by
              by_contra hcon; push Not at hcon; exact hnf (Or.inl hcon)
            rw [hfrO a (by omega) hnfM]; dsimp only [mW]; rw [Function.update_of_ne (by omega), hfrM a (by omega) ha_out hnfC, hFrC a ha hnf])
          (fun a ha1 ha2 => by
            have hnfM : ¬R_ord.foot (ordHandleOf b vCap eCap) xM.ordX a := fun hft => by
              rcases hftM_notBuf a hft with h1 | h2 <;> omega
            rw [hfrO a (by omega) hnfM]; dsimp only [mW]; rw [Function.update_of_ne (by omega), hstM_buf a (by omega) ha2])
          (by
            have hcost := op0_step_cost_drop mul_ord (tourLog eCap) htl
            rw [← hOrdW.2] at hcO
            rw [hed.2]; dsimp only [tourPhi] at hcD hcO ⊢
            clear * - hcD hcO hcost; simp only [Expr.size] at *; norm_num at hcO hcost ⊢; omega)
      · by_cases ht12 : tag = 1 ∨ tag = 2
        · -- Case `moveEnds v v' sel c` (`wk = 4 + len`)
          set v := stC.mem (ptr + 1)
          set v' := stC.mem (ptr + 2)
          set len := stC.mem (ptr + 3)
          set sel := (readList stC.mem (ptr + 4) len).map endOfKey
          set c : Bool := decide (tag = 2)
          have htag_eq : tag = if c then 2 else 1 := by
            rcases ht12 with h1 | h2
            · simp [c, h1]
            · simp [c, h2]
          have hed : edit = .moveEnds v v' sel.toFinset c ∧ wk = 4 + len := by
            rcases ht12 with h1 | h2
            · simp [edit, wk, d, decodeOrdEdit, tag, h1, v, v', len, sel, c]
            · simp [edit, wk, d, decodeOrdEdit, tag, h2, v, v', len, sel, c]
          have hsel_len : sel.length = len := by simp [sel, readList_length]
          have hsel_mem : ∀ i (hi : i < len), stC.mem (ptr + 4 + i) = endKey (sel[i]'(by omega)) := fun i hi => by
            simp only [sel, List.getElem_map, readList_getElem, endKey_endOfKey']
          have hc0 : (Expr.bin .eq (.reg 8) (.const 0)).eval w { stC with regs := rT } = some 0 := by
            simp [Expr.eval, rT, ht0, BinOp.eval, (by omega : 0 < 2 ^ w)]
          have hc12 : (Expr.bin .lt (.reg 8) (.const 3)).eval w { stC with regs := rT } = some 1 := by
            have : tag < 3 := by omega
            simp [Expr.eval, rT, this, BinOp.eval, (by omega : 3 < 2 ^ w), (by omega : 1 < 2 ^ w)]
          set r1 := Function.update rT 9 v
          set r2 := Function.update r1 10 v'
          set r3 := Function.update r2 11 len
          set r4 := Function.update r3 12 (ptr + 4)
          have ha9 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 9) (rBase := 5) (off := 1)
            (b := ptr) (val := v) (st := { stC with regs := rT }) (by simp [rT, hr5]) (by omega) (by omega) rfl
          have ha10 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 10) (rBase := 5) (off := 2)
            (b := ptr) (val := v') (st := { stC with regs := r1 }) (by simp [r1, rT, hr5]) (by omega) (by omega) rfl
          have ha11 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 11) (rBase := 5) (off := 3)
            (b := ptr) (val := len) (st := { stC with regs := r2 }) (by simp [r2, r1, rT, hr5]) (by omega) (by omega) rfl
          have ha12 : Runs w p ω (.assign 12 (.bin .add (.reg 5) (.const 4))) { stC with regs := r3 } .normal { stC with regs := r4 } 4 :=
            runs_assign_iff.mpr ⟨ptr + 4, by simp [Expr.eval, r3, r2, r1, rT, hr5, BinOp.eval, (by omega : 4 < 2 ^ w), (by omega : ptr + 4 < 2 ^ w)], rfl, rfl, rfl⟩
          obtain ⟨hMid, stM, cM, xM, hrunM, hhM_ge, hhM_le, hZM, hfrM, hftM, hgeM, hrepM, hcoreM, hcM⟩ :=
            tourEditMoveBody_runs (pos := stC.pos) E.toTourSplayQueryProcs E.rank_body E.sift_body E.sort_body
              E.collect_body E.rankSort_body E.splitLoop_body E.walkFront_body hOrdImpl hop2 ω
              hRepC.toCore hRepC.ordRep hRepC.ordFootGe hordFootC htag_eq rfl rfl rfl hsel_len hsel_mem
              (by omega) (fun a ha1 _ => Or.inr (by omega)) (hed.1 ▸ hval_head.1) hord_le_hCur (by omega) hw hwide hZC
          set r5 := Function.update r4 6 hMid
          have hcallM : Runs w p ω (.call 6 E.moveProc [.reg 0, .reg 5, .reg 6])
              { stC with regs := r4 } .normal { stM with regs := r5 } (4 + cM) :=
            runs_call_regs3 6 0 5 6 (st := { stC with regs := r4 }) E.move_body
              (by simp [r4, r3, r2, r1, rT, hr0]) (by simp [r4, r3, r2, r1, rT, hr5]) (by simp [r4, r3, r2, r1, rT, hr6]) hrunM
          -- Write `[1, tag, v, v', m', deduped...]` at `hMid`
          set m1 := Function.update stM.mem hMid 1
          set m2 := Function.update m1 (hMid + 1) tag
          set m3 := Function.update m2 (hMid + 2) v
          set m4 := Function.update m3 (hMid + 3) v'
          set r6 := Function.update r5 13 (hMid + 5)
          have hst0 : Runs w p ω (.store (.reg 6) (.const 1)) { stM with regs := r5 } .normal { stM with mem := m1, regs := r5 } 3 :=
            runs_store_iff.mpr ⟨hMid, 1, by simp [Expr.eval, r5], by simp [Expr.eval, (by omega : 1 < 2 ^ w)], rfl, rfl, rfl⟩
          have hst1 : Runs w p ω (.store (.bin .add (.reg 6) (.const 1)) (.reg 8)) { stM with mem := m1, regs := r5 } .normal { stM with mem := m2, regs := r5 } 5 :=
            runs_store_iff.mpr ⟨hMid + 1, tag, by simp [Expr.eval, r5, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : hMid + 1 < 2 ^ w)],
              by simp [Expr.eval, r5, r4, r3, r2, r1, rT], rfl, rfl, rfl⟩
          have hst2 : Runs w p ω (.store (.bin .add (.reg 6) (.const 2)) (.reg 9)) { stM with mem := m2, regs := r5 } .normal { stM with mem := m3, regs := r5 } 5 :=
            runs_store_iff.mpr ⟨hMid + 2, v, by simp [Expr.eval, r5, BinOp.eval, (by omega : 2 < 2 ^ w), (by omega : hMid + 2 < 2 ^ w)],
              by simp [Expr.eval, r5, r4, r3, r2, r1], rfl, rfl, rfl⟩
          have hst3 : Runs w p ω (.store (.bin .add (.reg 6) (.const 3)) (.reg 10)) { stM with mem := m3, regs := r5 } .normal { stM with mem := m4, regs := r5 } 5 :=
            runs_store_iff.mpr ⟨hMid + 3, v', by simp [Expr.eval, r5, BinOp.eval, (by omega : 3 < 2 ^ w), (by omega : hMid + 3 < 2 ^ w)],
              by simp [Expr.eval, r5, r4, r3, r2], rfl, rfl, rfl⟩
          have ha13 : Runs w p ω (.assign 13 (.bin .add (.reg 6) (.const 5))) { stM with mem := m4, regs := r5 } .normal { stM with mem := m4, regs := r6 } 4 :=
            runs_assign_iff.mpr ⟨hMid + 5, by simp [Expr.eval, r5, BinOp.eval, (by omega : 5 < 2 ^ w), (by omega : hMid + 5 < 2 ^ w)], rfl, rfl, rfl⟩
          have hm4_lt : ∀ a < hMid, m4 a = stM.mem a := fun a ha => by
            dsimp only [m4, m3, m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          have hstM_buf : ∀ a, ptr ≤ a → a < bufEnd → stM.mem a = stC.mem a := fun a ha1 ha2 =>
            hfrM a (by omega) (Or.inr (by omega)) (fun hft => by rcases hordFootC_notBuf a hft with h1 | h2 <;> omega)
          have hcore4 : TourCoreAt vCap eCap b (tourApplyEdit sC (.moveEnds v v' sel.toFinset c)) xM m4 :=
            hcoreM.congr_fixed fun a _ ha2 => hm4_lt a (by omega)
          have hsel_cap : ∀ z ∈ sel, z.1 < eCap := fun z hz => by
            have hv := hed.1 ▸ hval_head.1; exact hv.2.2.2.2.2.2 z (List.mem_toFinset.mpr hz)
          obtain ⟨m', stD, cDed, U, hrunDed, hm'_le, hUlen, hUnd, hUfin, hUmem, hDed_fr, hcDed⟩ :=
            tourDedupSelBody_runs (selPtr := ptr + 4) (outPtr := hMid + 5) (pos := stM.pos) ω hcore4 hsel_len
              (fun i hi => by rw [hm4_lt _ (by omega), hstM_buf _ (by omega) (by omega)]; exact hsel_mem i hi)
              hsel_cap (by omega) (by omega) (by omega) hwide
          set r7 := Function.update r6 15 m'
          have hcallDed : Runs w p ω (.call 15 E.dedupProc [.reg 0, .reg 12, .reg 11, .reg 13])
              { stM with mem := m4, regs := r6 } .normal { stD with regs := r7 } (5 + cDed) :=
            runs_call_regs4 15 0 12 11 13 (st := { stM with mem := m4, regs := r6 }) E.dedup_body
              (by simp [r6, r5, r4, r3, r2, r1, rT, hr0]) (by simp [r6, r5, r4])
              (by simp [r6, r5, r4, r3]) (by simp [r6]) hrunDed
          set m5 := Function.update stD.mem (hMid + 4) m'
          set r8 := Function.update r7 13 (5 + m')
          set r9 := Function.update r8 15 (hMid + (5 + m'))
          have hst4 : Runs w p ω (.store (.bin .add (.reg 6) (.const 4)) (.reg 15)) { stD with regs := r7 } .normal { stD with mem := m5, regs := r7 } 5 :=
            runs_store_iff.mpr ⟨hMid + 4, m', by simp [Expr.eval, r7, r6, r5, BinOp.eval, (by omega : 4 < 2 ^ w), (by omega : hMid + 4 < 2 ^ w)],
              by simp [Expr.eval, r7], rfl, rfl, rfl⟩
          have ha13' : Runs w p ω (.assign 13 (.bin .add (.const 5) (.reg 15))) { stD with mem := m5, regs := r7 } .normal { stD with mem := m5, regs := r8 } 4 :=
            runs_assign_iff.mpr ⟨5 + m', by simp [Expr.eval, r7, BinOp.eval, (by omega : 5 < 2 ^ w), (by omega : 5 + m' < 2 ^ w)], rfl, rfl, rfl⟩
          have ha15' : Runs w p ω (.assign 15 (.bin .add (.reg 6) (.reg 13))) { stD with mem := m5, regs := r8 } .normal { stD with mem := m5, regs := r9 } 4 :=
            runs_assign_iff.mpr ⟨hMid + (5 + m'), by simp [Expr.eval, r8, r7, r6, r5, BinOp.eval, (by omega : hMid + (5 + m') < 2 ^ w)], rfl, rfl, rfl⟩
          have hm5_lt : ∀ a < hMid, m5 a = stM.mem a := fun a ha => by
            dsimp only [m5]; rw [Function.update_of_ne (by omega), hDed_fr a (Or.inl (by omega)), hm4_lt a ha]
          have hcore5 : TourCoreAt vCap eCap b (tourApplyEdit sC edit) xM m5 := by
            rw [hed.1]; exact hcoreM.congr_fixed fun a _ ha2 => hm5_lt a (by omega)
          have hftM_lt : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) xM.ordX a → a < hMid := fun a ha => by
            rcases hftM a ha with h0 | ⟨_, h2⟩; exact lt_of_lt_of_le (hordFootC a h0) hhM_ge; exact h2
          have hOrd5 := hOrdImpl.1 (ordHandleOf b vCap eCap) sC.ord xM.ordX stM.mem m5 fun a ha =>
            (hm5_lt a (hftM_lt a ha)).symm
          have hEdits1 : OrdEditsAt m5 hMid [edit] (5 + m') := by
            rw [hed.1, ← hUfin]
            refine tour_singleEdit_ordEditsAt_move (p := hMid) (v := v) (v' := v') (m' := m') (c := c) (U := U)
              (by dsimp only [m5]; rw [Function.update_of_ne (by omega), hDed_fr _ (Or.inl (by omega))]; simp [m4, m3, m2, m1])
              (by dsimp only [m5]; rw [Function.update_of_ne (by omega), hDed_fr _ (Or.inl (by omega))]; simp [m4, m3, m2, htag_eq])
              (by dsimp only [m5]; rw [Function.update_of_ne (by omega), hDed_fr _ (Or.inl (by omega))]; simp [m4, m3])
              (by dsimp only [m5]; rw [Function.update_of_ne (by omega), hDed_fr _ (Or.inl (by omega))]; simp [m4])
              (by simp [m5]) hUlen hUnd
              (fun j hj => by dsimp only [m5]; rw [Function.update_of_ne (by omega)]; exact hUmem j hj)
          have hZ5 : ZeroFrom m5 (hMid + (5 + m')) := fun a ha => by
            dsimp only [m5]; rw [Function.update_of_ne (by omega), hDed_fr a (Or.inr (by omega))]
            dsimp only [m4, m3, m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hZM a (by omega)
          have halloc_le := halloc (ordHandleOf b vCap eCap) hMid (5 + m') (hMid + (5 + m'))
          obtain ⟨bodyO, oO, stO, cO, ordXO, hgetO, hrunO, hhO_ge, hhO_le, hZO, hfrO, hftO, hRepO, hcO⟩ :=
            tourCore_commitOrdStore (pos := stD.pos) hOrdImpl hop0 ω hcore5 hordU (hOrd5.1 hrepM) hgeM
              (fun a ha => lt_of_lt_of_le (hftM_lt a ha) (by omega)) (by omega) hEdits1 (by omega)
              (tourEditValid_to_ordEditsWithin hval_head.1) (by rw [hed.1]; rfl) hZ5 (by omega)
          set r10 := Function.update r9 6 oO.value
          have hcallO : Runs w p ω (.call 6 ordOp0 [.reg 14, .reg 6, .reg 13, .reg 15])
              { stD with mem := m5, regs := r9 } .normal { stO with regs := r10 } (5 + cO) :=
            runs_call_regs4 6 14 6 13 15 (st := { stD with mem := m5, regs := r9 }) hgetO
              (by simp [r9, r8, r7, r6, r5, r4, r3, r2, r1, rT, hr14]) (by simp [r9, r8, r7, r6, r5])
              (by simp [r9, r8]) (by simp [r9]) hrunO
          set r11 := Function.update r10 5 (ptr + 4 + len)
          have ha5 : Runs w p ω (.assign 5 (.bin .add (.reg 12) (.reg 11))) { stO with regs := r10 } .normal { stO with regs := r11 } 4 :=
            runs_assign_iff.mpr ⟨ptr + 4 + len, by
              simp [Expr.eval, r10, r9, r8, r7, r6, r5, r4, r3, BinOp.eval, (by omega : ptr + 4 + len < 2 ^ w)], rfl, rfl, rfl⟩
          have hrunM_inner :=
            tour_runs_seq_normal ha9 (tour_runs_seq_normal ha10 (tour_runs_seq_normal ha11 (tour_runs_seq_normal ha12
              (tour_runs_seq_normal hcallM (tour_runs_seq_normal hst0 (tour_runs_seq_normal hst1 (tour_runs_seq_normal hst2
                (tour_runs_seq_normal hst3 (tour_runs_seq_normal ha13 (tour_runs_seq_normal hcallDed (tour_runs_seq_normal hst4
                  (tour_runs_seq_normal ha13' (tour_runs_seq_normal ha15' (tour_runs_seq_normal hcallO ha5))))))))))))))
          refine hstep_to_ih oO.value { xM with ordX := ordXO } { stO with regs := r11 } _
            (tour_runs_cond_false hc0 (tour_runs_cond_true hc12 (by omega) hrunM_inner))
            (by omega) (by omega) hZO
            (by simp [r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, rT, hr0])
            (by simp [r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, rT, hr4])
            (by simp [r11, hed.2]; omega) (by simp [r11, r10])
            (by simp [r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, rT, hr7])
            (by simp [r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, rT, hr14])
            hRepO
            (fun a ha => by
              rcases hftO a ha with h1 | ⟨ha1, ha2⟩
              · rcases hftM a h1 with h0 | ⟨hb1, hb2⟩
                · exact (hFtC a h0).imp id fun ⟨hc1, hc2⟩ => ⟨hc1, by omega⟩
                · exact Or.inr ⟨by omega, by omega⟩
              · exact Or.inr ⟨by omega, ha2⟩)
            (fun a ha hnf => by
              have hnfC : ¬R_ord.foot (ordHandleOf b vCap eCap) xC.ordX a := fun hft => by
                rcases hFtC a hft with h0 | ⟨h1, _⟩; exact hnf (Or.inr h0); omega
              have hnfM : ¬R_ord.foot (ordHandleOf b vCap eCap) xM.ordX a := fun hft => by
                rcases hftM a hft with h0 | ⟨h1, _⟩; exact hnfC h0; omega
              have ha_out : a < b ∨ ordHandleOf b vCap eCap ≤ a := by
                by_contra hcon; push Not at hcon; exact hnf (Or.inl hcon)
              rw [hfrO a (by omega) hnfM, hm5_lt a (by omega), hfrM a (by omega) ha_out hnfC, hFrC a ha hnf])
            (fun a ha1 ha2 => by
              have hnfM : ¬R_ord.foot (ordHandleOf b vCap eCap) xM.ordX a := fun hft => by
                rcases hftM a hft with h0 | ⟨h1, _⟩
                · rcases hordFootC_notBuf a h0 with h1 | h2 <;> omega
                · omega
              rw [hfrO a (by omega) hnfM, hm5_lt a (by omega), hstM_buf a (by omega) ha2])
            ?_
          have hcost := op0_step_cost_move len m' mul_ord (tourLog eCap) hm'_le htl
          have hcO' : cO + R_ord.phi (ordHandleOf b vCap eCap) ordXO stO.mem ≤
              mul_ord * (5 + m' + 1) * tourLog eCap + R_ord.phi (ordHandleOf b vCap eCap) xM.ordX stM.mem := by
            rwa [← hOrd5.2] at hcO
          have hcM' : cM + TOUR_PHI_MULT * forestPhi xM.trees + R_ord.phi (ordHandleOf b vCap eCap) xM.ordX stM.mem ≤
              TOUR_PHI_MULT * forestPhi xC.trees + R_ord.phi (ordHandleOf b vCap eCap) xC.ordX stC.mem +
                (len + 1) * (TOUR_MOVE_MUL + mul_ord) * tourLog eCap := hcM
          rw [hed.2]; unfold tourPhi; dsimp only
          exact move_cost_combine_nat (by clear * -; simp only [Expr.size]; omega) hcM' hcDed hcO' hcost
        · by_cases ht3 : tag = 3
          · -- Case `insertBefore v keyX yWord` (`wk = 4`)
            set v := stC.mem (ptr + 1)
            set keyX := stC.mem (ptr + 2)
            set yWord := stC.mem (ptr + 3)
            set yOpt : Option End := if yWord = 0 then none else some (endOfKey (yWord - 1))
            have hed : edit = .insertBefore v (endOfKey keyX) yOpt ∧ wk = 4 := by
              simp [edit, wk, d, decodeOrdEdit, tag, ht3, v, keyX, yWord, yOpt]
            have hkeyLt : keyX < 2 * eCap := by
              have hv := hed.1 ▸ hval_head.1; exact key_lt_two_mul_of_endOfKey hv.2.2.1
            have hc0 : (Expr.bin .eq (.reg 8) (.const 0)).eval w { stC with regs := rT } = some 0 := by
              simp [Expr.eval, rT, ht0, BinOp.eval, (by omega : 0 < 2 ^ w)]
            have hc12 : (Expr.bin .lt (.reg 8) (.const 3)).eval w { stC with regs := rT } = some 0 := by
              simp [Expr.eval, rT, ht3, BinOp.eval, (by omega : 3 < 2 ^ w), (by omega : 0 < 2 ^ w)]
            have hc3 : (Expr.bin .eq (.reg 8) (.const 3)).eval w { stC with regs := rT } = some 1 := by
              simp [Expr.eval, rT, ht3, BinOp.eval, (by omega : 3 < 2 ^ w), (by omega : 1 < 2 ^ w)]
            set r1 := Function.update rT 9 v
            set r2 := Function.update r1 10 keyX
            set r3 := Function.update r2 11 yWord
            have ha9 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 9) (rBase := 5) (off := 1)
              (b := ptr) (val := v) (st := { stC with regs := rT }) (by simp [rT, hr5]) (by omega) (by omega) rfl
            have ha10 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 10) (rBase := 5) (off := 2)
              (b := ptr) (val := keyX) (st := { stC with regs := r1 }) (by simp [r1, rT, hr5]) (by omega) (by omega) rfl
            have ha11 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 11) (rBase := 5) (off := 3)
              (b := ptr) (val := yWord) (st := { stC with regs := r2 }) (by simp [r2, r1, rT, hr5]) (by omega) (by omega) rfl
            obtain ⟨stI, cI, xI, hrunI, hxI_ord, hZI, hfrI, hcoreI, hcI⟩ :=
              tourEditInsertBody_runs (pos := stC.pos) E.toTourSplayQueryProcs ω hRepC.toCore hkeyLt
                (hed.1 ▸ hval_head.1) hord_le_hCur (by omega) hw hwide hZC
            have hcallI := runs_call_regs5 6 0 9 10 11 6 (st := { stC with regs := r3 }) E.ins_body
              (by simp [r3, r2, r1, rT, hr0]) (by simp [r3, r2, r1]) (by simp [r3, r2]) (by simp [r3])
              (by simp [r3, r2, r1, rT, hr6]) hrunI
            set r4 := Function.update r3 6 hCur
            set r5 := Function.update r4 10 (ptr - 1)
            set mW := Function.update stI.mem (ptr - 1) 1
            set r6 := Function.update r5 11 5
            have ha10' : Runs w p ω (.assign 10 (.bin .sub (.reg 5) (.const 1))) { stI with regs := r4 } .normal { stI with regs := r5 } 4 :=
              runs_assign_iff.mpr ⟨ptr - 1, by simp [Expr.eval, r4, r3, r2, r1, rT, hr5, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : ptr - 1 < 2 ^ w)], rfl, rfl, rfl⟩
            have hst1 : Runs w p ω (.store (.reg 10) (.const 1)) { stI with regs := r5 } .normal { stI with mem := mW, regs := r5 } 3 :=
              runs_store_iff.mpr ⟨ptr - 1, 1, by simp [Expr.eval, r5], by simp [Expr.eval, (by omega : 1 < 2 ^ w)], rfl, rfl, rfl⟩
            have ha11' := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 11) (val := 5) (st := { stI with mem := mW, regs := r5 }) (by omega)
            have hcoreW : TourCoreAt vCap eCap b (tourApplyEdit sC edit) xI mW := by
              rw [hed.1]; exact hcoreI.congr_fixed fun a _ ha2 => Function.update_of_ne (by omega) _ _
            have hOrdW := hOrdImpl.1 (ordHandleOf b vCap eCap) sC.ord xC.ordX stC.mem mW fun a ha => by
              dsimp only [mW]; rw [Function.update_of_ne (by rcases hordFootC_notBuf a ha with h1 | h2 <;> omega)]
              exact (hfrI a (Or.inr (hRepC.ordFootGe a ha)) (hordFootC a ha)).symm
            have hEdits1 : OrdEditsAt mW (ptr - 1) [edit] 5 := by
              have hdecW : decodeOrdEdit mW (ptr - 1 + 1) = (edit, 4) := by
                have heq : ptr - 1 + 1 = ptr := by omega
                rw [heq]; refine (tour_decodeOrdEdit_shift (m₁ := stC.mem) (m₂ := mW) (a₁ := ptr) (a₂ := ptr) fun i hi => ?_).trans (Prod.ext rfl hed.2)
                have hi4 : i < 4 := by change i < wk at hi; omega
                dsimp only [mW]; rw [Function.update_of_ne (by omega)]; exact hfrI _ (Or.inr (by omega)) (by omega)
              exact tour_singleEdit_ordEditsAt_simple (by simp [mW]) hdecW (by omega)
            have halloc_le := halloc (ordHandleOf b vCap eCap) (ptr - 1) 5 hCur
            obtain ⟨bodyO, oO, stO, cO, ordXO, hgetO, hrunO, hhO_ge, hhO_le, hZO, hfrO, hftO, hRepO, hcO⟩ :=
              tourCore_commitOrdStore (pos := stI.pos) hOrdImpl hop0 ω hcoreW hordU
                (hxI_ord ▸ hOrdW.1 hRepC.ordRep) (hxI_ord ▸ hRepC.ordFootGe) (hxI_ord ▸ hordFootC)
                hord_le_hCur hEdits1 (by omega) (tourEditValid_to_ordEditsWithin hval_head.1) (by rw [hed.1]; rfl)
                (fun a ha => by dsimp only [mW]; rw [Function.update_of_ne (by omega)]; exact hZI a ha) (by omega)
            have hcallO := runs_call_regs4 6 14 10 11 6 (st := { stI with mem := mW, regs := r6 }) hgetO
              (by simp [r6, r5, r4, r3, r2, r1, rT, hr14]) (by simp [r6, r5]) (by simp [r6]) (by simp [r6, r5, r4]) hrunO
            set r7 := Function.update r6 6 oO.value
            set r8 := Function.update r7 5 (ptr + 4)
            have ha5 : Runs w p ω (.assign 5 (.bin .add (.reg 5) (.const 4))) { stO with regs := r7 } .normal { stO with regs := r8 } 4 :=
              runs_assign_iff.mpr ⟨ptr + 4, by simp [Expr.eval, r7, r6, r5, r4, r3, r2, r1, rT, hr5, BinOp.eval, (by omega : 4 < 2 ^ w), (by omega : ptr + 4 < 2 ^ w)], rfl, rfl, rfl⟩
            apply hstep_to_ih oO.value { xI with ordX := ordXO } { stO with regs := r8 } _
              (tour_runs_cond_false hc0 (tour_runs_cond_false hc12 (tour_runs_cond_true hc3 (by omega)
                (tour_runs_seq_normal ha9 (tour_runs_seq_normal ha10 (tour_runs_seq_normal ha11 (tour_runs_seq_normal hcallI
                  (tour_runs_seq_normal ha10' (tour_runs_seq_normal hst1 (tour_runs_seq_normal ha11' (tour_runs_seq_normal hcallO ha5)))))))))))
              hhO_ge (by omega) hZO
              (by simp [r8, r7, r6, r5, r4, r3, r2, r1, rT, hr0]) (by simp [r8, r7, r6, r5, r4, r3, r2, r1, rT, hr4])
              (by simp [r8, hed.2]) (by simp [r8, r7])
              (by simp [r8, r7, r6, r5, r4, r3, r2, r1, rT, hr7]) (by simp [r8, r7, r6, r5, r4, r3, r2, r1, rT, hr14])
              hRepO
              (fun a ha => by
                rcases hftO a ha with h1 | ⟨ha1, ha2⟩
                · exact (hFtC a (hxI_ord ▸ h1)).imp id fun ⟨hc1, hc2⟩ => ⟨hc1, by omega⟩
                · exact Or.inr ⟨by omega, ha2⟩)
              (fun a ha hnf => by
                have hnfC : ¬R_ord.foot (ordHandleOf b vCap eCap) xC.ordX a := fun hft => by
                  rcases hFtC a hft with h0 | ⟨h1, _⟩; exact hnf (Or.inr h0); omega
                have ha_out : a < b ∨ ordHandleOf b vCap eCap ≤ a := by
                  by_contra hcon; push Not at hcon; exact hnf (Or.inl hcon)
                rw [hfrO a (by omega) (hxI_ord ▸ hnfC)]; dsimp only [mW]; rw [Function.update_of_ne (by omega), hfrI a ha_out (by omega), hFrC a ha hnf])
              (fun a ha1 ha2 => by
                have hnfC : ¬R_ord.foot (ordHandleOf b vCap eCap) xC.ordX a := fun hft => by
                  rcases hordFootC_notBuf a hft with h1 | h2 <;> omega
                rw [hfrO a (by omega) (hxI_ord ▸ hnfC)]; dsimp only [mW]; rw [Function.update_of_ne (by omega), hfrI a (Or.inr (by omega)) (by omega)])
              (by
                have hcost := op0_step_cost_simple 4 mul_ord (tourLog eCap) (by decide) (by decide) htl
                rw [hxI_ord, ← hOrdW.2] at hcO
                rw [hed.2]; dsimp only [tourPhi] at hcI hcO ⊢
                clear * - hcI hcO hcost; simp only [Expr.size] at *; norm_num at hcO hcost ⊢; omega)
          · -- Case `rotateTo v keyY` (`wk = 3`)
            set v := stC.mem (ptr + 1)
            set keyY := stC.mem (ptr + 2)
            have hed : edit = .rotateTo v (endOfKey keyY) ∧ wk = 3 := by
              simp [edit, wk, d, decodeOrdEdit, tag, ht0, ht12, ht3, v, keyY]
            have hrotV : v < vCap ∧ keyY < 2 * eCap := by
              have hv := hed.1 ▸ hval_head.1; exact ⟨hv.1, key_lt_two_mul_of_endOfKey hv.2⟩
            have hc0 : (Expr.bin .eq (.reg 8) (.const 0)).eval w { stC with regs := rT } = some 0 := by
              simp [Expr.eval, rT, ht0, BinOp.eval, (by omega : 0 < 2 ^ w)]
            have hc12 : (Expr.bin .lt (.reg 8) (.const 3)).eval w { stC with regs := rT } = some 0 := by
              have : ¬(tag < 3) := by omega
              simp [Expr.eval, rT, this, BinOp.eval, (by omega : 3 < 2 ^ w), (by omega : 0 < 2 ^ w)]
            have hc3 : (Expr.bin .eq (.reg 8) (.const 3)).eval w { stC with regs := rT } = some 0 := by
              simp [Expr.eval, rT, ht3, BinOp.eval, (by omega : 3 < 2 ^ w), (by omega : 0 < 2 ^ w)]
            set r1 := Function.update rT 9 v
            set r2 := Function.update r1 10 keyY
            have ha9 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 9) (rBase := 5) (off := 1)
              (b := ptr) (val := v) (st := { stC with regs := rT }) (by simp [rT, hr5]) (by omega) (by omega) rfl
            have ha10 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 10) (rBase := 5) (off := 2)
              (b := ptr) (val := keyY) (st := { stC with regs := r1 }) (by simp [r1, rT, hr5]) (by omega) (by omega) rfl
            obtain ⟨stR, cR, xR, hrunR, hxR_ord, hZR, hfrR, hcoreR, hcR⟩ :=
              tourEditRotateBody_runs (pos := stC.pos) E.toTourSplayQueryProcs ω hRepC.toCore hrotV.1 hrotV.2
                hord_le_hCur hw (by omega) hZC (by omega)
            have hcallR := runs_call_regs4 6 0 9 10 6 (st := { stC with regs := r2 }) E.rot_body
              (by simp [r2, r1, rT, hr0]) (by simp [r2, r1]) (by simp [r2]) (by simp [r2, r1, rT, hr6]) hrunR
            set r3 := Function.update r2 6 hCur
            set r4 := Function.update r3 10 (ptr - 1)
            set mW := Function.update stR.mem (ptr - 1) 1
            set r5 := Function.update r4 11 4
            have ha10' : Runs w p ω (.assign 10 (.bin .sub (.reg 5) (.const 1))) { stR with regs := r3 } .normal { stR with regs := r4 } 4 :=
              runs_assign_iff.mpr ⟨ptr - 1, by simp [Expr.eval, r3, r2, r1, rT, hr5, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : ptr - 1 < 2 ^ w)], rfl, rfl, rfl⟩
            have hst1 : Runs w p ω (.store (.reg 10) (.const 1)) { stR with regs := r4 } .normal { stR with mem := mW, regs := r4 } 3 :=
              runs_store_iff.mpr ⟨ptr - 1, 1, by simp [Expr.eval, r4], by simp [Expr.eval, (by omega : 1 < 2 ^ w)], rfl, rfl, rfl⟩
            have ha11' := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 11) (val := 4) (st := { stR with mem := mW, regs := r4 }) (by omega)
            have hcoreW : TourCoreAt vCap eCap b (tourApplyEdit sC edit) xR mW := by
              rw [hed.1]; exact hcoreR.congr_fixed fun a _ ha2 => Function.update_of_ne (by omega) _ _
            have hOrdW := hOrdImpl.1 (ordHandleOf b vCap eCap) sC.ord xC.ordX stC.mem mW fun a ha => by
              dsimp only [mW]; rw [Function.update_of_ne (by rcases hordFootC_notBuf a ha with h1 | h2 <;> omega)]
              exact (hfrR a (Or.inr (hRepC.ordFootGe a ha)) (hordFootC a ha)).symm
            have hEdits1 : OrdEditsAt mW (ptr - 1) [edit] 4 := by
              have hdecW : decodeOrdEdit mW (ptr - 1 + 1) = (edit, 3) := by
                have heq : ptr - 1 + 1 = ptr := by omega
                rw [heq]; refine (tour_decodeOrdEdit_shift (m₁ := stC.mem) (m₂ := mW) (a₁ := ptr) (a₂ := ptr) fun i hi => ?_).trans (Prod.ext rfl hed.2)
                have hi3 : i < 3 := by change i < wk at hi; omega
                dsimp only [mW]; rw [Function.update_of_ne (by omega)]; exact hfrR _ (Or.inr (by omega)) (by omega)
              exact tour_singleEdit_ordEditsAt_simple (by simp [mW]) hdecW (by omega)
            have halloc_le := halloc (ordHandleOf b vCap eCap) (ptr - 1) 4 hCur
            obtain ⟨bodyO, oO, stO, cO, ordXO, hgetO, hrunO, hhO_ge, hhO_le, hZO, hfrO, hftO, hRepO, hcO⟩ :=
              tourCore_commitOrdStore (pos := stR.pos) hOrdImpl hop0 ω hcoreW hordU
                (hxR_ord ▸ hOrdW.1 hRepC.ordRep) (hxR_ord ▸ hRepC.ordFootGe) (hxR_ord ▸ hordFootC)
                hord_le_hCur hEdits1 (by omega) (tourEditValid_to_ordEditsWithin hval_head.1) (by rw [hed.1]; rfl)
                (fun a ha => by dsimp only [mW]; rw [Function.update_of_ne (by omega)]; exact hZR a ha) (by omega)
            have hcallO := runs_call_regs4 6 14 10 11 6 (st := { stR with mem := mW, regs := r5 }) hgetO
              (by simp [r5, r4, r3, r2, r1, rT, hr14]) (by simp [r5, r4]) (by simp [r5]) (by simp [r5, r4, r3]) hrunO
            set r6 := Function.update r5 6 oO.value
            set r7 := Function.update r6 5 (ptr + 3)
            have ha5 : Runs w p ω (.assign 5 (.bin .add (.reg 5) (.const 3))) { stO with regs := r6 } .normal { stO with regs := r7 } 4 :=
              runs_assign_iff.mpr ⟨ptr + 3, by simp [Expr.eval, r6, r5, r4, r3, r2, r1, rT, hr5, BinOp.eval, (by omega : 3 < 2 ^ w), (by omega : ptr + 3 < 2 ^ w)], rfl, rfl, rfl⟩
            apply hstep_to_ih oO.value { xR with ordX := ordXO } { stO with regs := r7 } _
              (tour_runs_cond_false hc0 (tour_runs_cond_false hc12 (tour_runs_cond_false hc3
                (tour_runs_seq_normal ha9 (tour_runs_seq_normal ha10 (tour_runs_seq_normal hcallR
                  (tour_runs_seq_normal ha10' (tour_runs_seq_normal hst1 (tour_runs_seq_normal ha11' (tour_runs_seq_normal hcallO ha5))))))))))
              hhO_ge (by omega) hZO
              (by simp [r7, r6, r5, r4, r3, r2, r1, rT, hr0]) (by simp [r7, r6, r5, r4, r3, r2, r1, rT, hr4])
              (by simp [r7, hed.2]) (by simp [r7, r6])
              (by simp [r7, r6, r5, r4, r3, r2, r1, rT, hr7]) (by simp [r7, r6, r5, r4, r3, r2, r1, rT, hr14])
              hRepO
              (fun a ha => by
                rcases hftO a ha with h1 | ⟨ha1, ha2⟩
                · exact (hFtC a (hxR_ord ▸ h1)).imp id fun ⟨hc1, hc2⟩ => ⟨hc1, by omega⟩
                · exact Or.inr ⟨by omega, ha2⟩)
              (fun a ha hnf => by
                have hnfC : ¬R_ord.foot (ordHandleOf b vCap eCap) xC.ordX a := fun hft => by
                  rcases hFtC a hft with h0 | ⟨h1, _⟩; exact hnf (Or.inr h0); omega
                have ha_out : a < b ∨ ordHandleOf b vCap eCap ≤ a := by
                  by_contra hcon; push Not at hcon; exact hnf (Or.inl hcon)
                rw [hfrO a (by omega) (hxR_ord ▸ hnfC)]; dsimp only [mW]; rw [Function.update_of_ne (by omega), hfrR a ha_out (by omega), hFrC a ha hnf])
              (fun a ha1 ha2 => by
                have hnfC : ¬R_ord.foot (ordHandleOf b vCap eCap) xC.ordX a := fun hft => by
                  rcases hordFootC_notBuf a hft with h1 | h2 <;> omega
                rw [hfrO a (by omega) (hxR_ord ▸ hnfC)]; dsimp only [mW]; rw [Function.update_of_ne (by omega), hfrR a (Or.inr (by omega)) (by omega)])
              (by
                have hcost := op0_step_cost_simple 3 mul_ord (tourLog eCap) (by decide) (by decide) htl
                rw [hxR_ord, ← hOrdW.2] at hcO
                rw [hed.2]; dsimp only [tourPhi] at hcR hcO ⊢
                clear * - hcR hcO hcost; simp only [Expr.size] at *; norm_num at hcO hcost ⊢; omega)
  -- Invoke `hloop` on the copied edit buffer at `heap + 2`
  have hdecCp : decodeOrdEdits stCp.mem count (heap + 2) = decodeOrdEdits mem count (edits + 1) :=
    tour_decodeOrdEdits_shift (m₁ := mem) (m₂ := stCp.mem) count (edits + 1) (heap + 2) fun i hi => by
      have hweq := hEditsAt.2.1; dsimp only [count] at hi
      have h1 := hCp_mem (1 + i) (by omega)
      have heq1 : heap + 2 + i = heap + 1 + (1 + i) := by omega
      have heq2 : edits + 1 + i = edits + (1 + i) := by omega
      rw [heq1, heq2]; exact h1
  have hremW0 : (decodeOrdEdits stCp.mem count (heap + 2)).2.sum = words - 1 := by
    rw [hdecCp]; have hweq := hEditsAt.2.1; dsimp only [count]; omega
  have hdec1_0 : (decodeOrdEdits stCp.mem count (heap + 2)).1 = readOrdEdits mem edits := by
    rw [hdecCp]; rfl
  obtain ⟨hF, xF, stF, cL, hrunL, hF6, hF_ge, hF_le, hZF, hRepF, hFtF, hFrF, hcL⟩ :=
    hloop count 0 (heap + 2) bufEnd s x { stCp with regs := rP5 } (by omega) (le_refl _)
      (by dsimp only; omega) (le_refl _) (by dsimp only [tourOp0Space]; omega)
      (by simp [rP5, rP4, rP3, rP2, rP1, hCp_ro 0 (by decide) (by decide), r2, r1, s0, startState])
      (by simp [rP5, rP4, rP3, rP2, rP1]) (by simp [rP5, rP4, rP3, rP2])
      (by simp [rP5, rP4, rP3]) (by simp [rP5, rP4]) (by simp [rP5])
      hRepCp (by dsimp only; rw [hdec1_0]; exact hValid) (fun _ ha => Or.inl ha)
      (fun a ha _ => hCp_lt a ha) hCp_zero
  dsimp only at hF_le hRepF hcL
  rw [hremW0] at hF_le hcL
  rw [hPhiCp] at hcL
  have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := stF) (r := 6) (v := hF) hF6
  refine ⟨.returned hF, stF, _,
    tour_runs_seq_normal ha4 (tour_runs_seq_normal ha5 (tour_runs_seq_normal hrunCp (tour_runs_seq_normal hp1
      (tour_runs_seq_normal hp2 (tour_runs_seq_normal hp3 (tour_runs_seq_normal hp4 (tour_runs_seq_normal hp5
        (tour_runs_seq_normal hrunL hret)))))))),
    xF, by simpa [tourRep, hdec1_0] using hRepF,
    ⟨by simp [Outcome.value]; omega, by simp [Outcome.value, tourOp0Space]; omega,
     by simpa [Outcome.value] using hZF, hFrF,
     fun a ha => by
       rcases ha with h1 | h2
       · exact Or.inl (Or.inl h1)
       · rcases hFtF a h2 with h0 | ⟨hb1, hb2⟩
         · exact Or.inl (Or.inr h0)
         · exact Or.inr ⟨by omega, hb2⟩⟩, ?_⟩
  have hw_le : (words - 1) * (TOUR_OP0_BASE_MUL + 6 * mul_ord) * tourLog eCap ≤
      (words + 1) * (TOUR_OP0_BASE_MUL + 6 * mul_ord) * tourLog eCap :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  have hsplit : (TOUR_OP0_MUL + 6 * mul_ord) * (words + 1) * tourLog eCap =
      (words + 1) * (TOUR_OP0_BASE_MUL + 6 * mul_ord) * tourLog eCap +
      200 * (words + 1) * tourLog eCap := by
    unfold TOUR_OP0_MUL; ring
  have h200 : 25 * words + 120 ≤ 200 * (words + 1) * tourLog eCap := by
    clear * - htl; nlinarith
  dsimp only [tourRep] at hcL ⊢
  clear * - hcCp hcL hw_le hsplit h200; omega

end MinCostFlow.SparseCore.Program
