module

public import MinCostFlow.DynSpanner.Program.DynSpannerUpdateLoopInv
import Mathlib.Tactic.Ring

/-!
# Verification of the dynamic spanner batch update loop (`DynSpannerUpdateLoop`)

Proves `dsUpdateLoop_meetsContract`: the deterministic Word-RAM procedure `dsUpdateLoopStmt`
(`DynSpannerUpdateLoopDefs.lean`) implements Algorithm 6's `update` batch loop (Theorem 8.2,
page 64; model `DynSpanner.update` in `MinCostFlow/DynSpanner/Defs.lean`), meeting
`dsUpdateLoopContract` by induction over the batch updates (`updateLoop_forRange_triple`) followed
by linear-time `D`-collection, `U_H`-packing, and header emission (`updateLoop_tail_runs`).

The positive-level step `dsStepPosFullStmt` is taken via `dsStepPosFull_meetsContract`, whose post
bounds the number of words of `U_H` (`stepPosFullUHWordsBound`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

/-! ## For-loop verification over the batch -/

private lemma updateLoop_forRange_triple (c : UpdateLoopCtx) {p : Program} {bs : UpdateLoopBases}
    (hps : HasUpdateLoopProcs c.impl p bs) :
    Triple c.w p
      (fun st => st.mem = c.mem0 ∧ st.regs 0 = c.b ∧ st.regs 1 = c.batchPtr ∧
        st.regs 2 = c.heapStart ∧ st.regs 3 = c.U.length ∧ st.regs 4 = c.heapStart + 7 ∧
        st.regs 5 = c.heapStart + 7 + c.U.length ∧ st.regs 6 = c.batchPtr + 1)
      (forRange 7 (.const 0) (.reg 3) (updateLoopBody bs.sz.bAux bs.bUL))
      (normalPost (UpdateLoopInv c c.U.length))
      (fun _ => rangeCost c.loopCost_per_iter_def 0 c.U.length + c.U.length * 9 + 7) := by
  have h16 := c.hw16
  have hm_w : c.U.length < 2 ^ c.w := by
    have hsp := c.hspace
    dsimp only [dsUpdateLoopSpace] at hsp
    clear * - hsp; omega
  refine (Triple.forRange_le c.loopCost_per_iter_def 0 c.U.length (Nat.zero_le _) (by omega)
    (fun _ => hm_w) (Inv := UpdateLoopInv c)
    (fun st ⟨hm, r0, r1, r2, r3, r4, r5, r6⟩ => ⟨Expr.eval_const (by omega), by
      refine ⟨c.heapStart + 7 + c.U.length, c.x₀, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
        Fin.elim0,
        by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4], by simp [r5],
        by simp [r6], by simp, le_refl _, le_of_eq c.cursorBound_zero.symm,
        fun a ha => hm ▸ c.hz₀ a (by omega), c.hState₀.1, c.hState₀.2.1,
        fun a ha => lt_of_lt_of_le (c.hfoot₀ a ha) (by omega),
        fun a ha => Or.inl (c.hfoot₀ a ha),
        fun _ _ => Iff.rfl,
        by simpa [UpdateLoopCtx.stAt, hm] using c.hState₀,
        by simpa using c.hRev₀,
        by simpa using c.hPref₀,
        by simp [hm],
        fun _ _ _ => hm ▸ rfl,
        fun s => Fin.elim0 s⟩⟩)
    (fun _ _ _ _ h => by rcases h with ⟨_, _, _, _, _, _, _, h⟩; exact h.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ h => by rcases h with ⟨_, _, _, _, _, _, _, h⟩; exact Expr.eval_reg_of_eq h.2.2.2.1)
    (fun i _ hi => updateLoop_step_triple c hps hi)).conseq
    (fun _ h => h) (fun _ _ h => h) (fun _ _ => by simp [Expr.size])

/-! ## Tail after the loop: `CollectD`, `PackUH`, and batch output header -/

private def updateLoopTailStmt (bUL : ℕ) : Stmt :=
  .assign 9 (.reg 5) ;;
  .call 10 (bUL + updateLoopIdxCollectD) [.reg 0, .reg 4, .reg 3, .reg 9, .const 0] ;;
  .assign 15 (.bin .add (.reg 9) (.reg 10)) ;;
  .call 16 (bUL + updateLoopIdxCollectD) [.reg 0, .reg 4, .reg 3, .reg 15, .const 1] ;;
  .assign 11 (.bin .add (.reg 15) (.reg 16)) ;;
  .call 12 (bUL + updateLoopIdxPackUH) [.reg 4, .reg 3, .reg 11] ;;
  .assign 13 (.load (.reg 11)) ;;
  .assign 14 (.bin .add (.bin .add (.reg 11) (.const 1)) (.reg 12)) ;;
  .store (.reg 2) (.reg 11) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 13) ;;
  .store (.bin .add (.reg 2) (.const 2)) (.bin .add (.reg 12) (.const 1)) ;;
  .store (.bin .add (.reg 2) (.const 3)) (.reg 9) ;;
  .store (.bin .add (.reg 2) (.const 4)) (.reg 10) ;;
  .store (.bin .add (.reg 2) (.const 5)) (.reg 15) ;;
  .store (.bin .add (.reg 2) (.const 6)) (.reg 16) ;;
  .ret (.reg 14)

private lemma rangeCost_loop_eq (c : UpdateLoopCtx) :
    rangeCost c.loopCost_per_iter_def 0 c.U.length =
      (∑ r ∈ Finset.range c.U.length, (c.stepCost r + 35 * c.L + 510)) +
      30 * (∑ r ∈ Finset.range c.U.length, (c.resAt r).D.card) +
      30 * (∑ r ∈ Finset.range c.U.length, (c.reembAt r).card) +
      30 * (c.lens.sum + 4 * ∑ r ∈ Finset.range c.U.length, (c.resAt r).UH.length) := by
  rw [rangeCost_eq_sum_range c.loopCost_per_iter_def c.U.length 0 c.U.length (by omega)]
  have hcongr : (∑ r ∈ Finset.range c.U.length, c.loopCost_per_iter_def (0 + r)) =
      ∑ r ∈ Finset.range c.U.length,
        ((c.stepCost r + 35 * c.L + 510) + 30 * (c.resAt r).D.card +
          30 * (c.reembAt r).card +
          (30 * c.lens.getD r 0 + 30 * (4 * (c.resAt r).UH.length))) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrm : r < c.U.length := Finset.mem_range.mp hr
    simp only [Nat.zero_add, UpdateLoopCtx.loopCost_per_iter_def, hrm, ↓reduceIte]
    ring
  rw [hcongr]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, list_sum_range_lens c.lens_length]
  ring

private lemma updateLoop_writeHdr_triple {w : ℕ} {p : Program}
    {heapStart heapCursor dLen rOutPtr rLen uhOutPtr uhLen uhOutWords : ℕ} {memP : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hhdrs_w : heapStart + 7 < 2 ^ w)
    (hretFinal_w : uhOutPtr + 1 + uhOutWords < 2 ^ w)
    (huhLen_eq : memP uhOutPtr = uhLen) :
    Triple w p
      (fun st => st.mem = memP ∧ st.regs 2 = heapStart ∧ st.regs 9 = heapCursor ∧
        st.regs 10 = dLen ∧ st.regs 15 = rOutPtr ∧ st.regs 16 = rLen ∧
        st.regs 11 = uhOutPtr ∧ st.regs 12 = uhOutWords)
      (.assign 13 (.load (.reg 11)) ;;
       .assign 14 (.bin .add (.bin .add (.reg 11) (.const 1)) (.reg 12)) ;;
       .store (.reg 2) (.reg 11) ;;
       .store (.bin .add (.reg 2) (.const 1)) (.reg 13) ;;
       .store (.bin .add (.reg 2) (.const 2)) (.bin .add (.reg 12) (.const 1)) ;;
       .store (.bin .add (.reg 2) (.const 3)) (.reg 9) ;;
       .store (.bin .add (.reg 2) (.const 4)) (.reg 10) ;;
       .store (.bin .add (.reg 2) (.const 5)) (.reg 15) ;;
       .store (.bin .add (.reg 2) (.const 6)) (.reg 16) ;;
       .ret (.reg 14))
      (fun o st' => o = .returned (uhOutPtr + 1 + uhOutWords) ∧
        st'.mem =
          Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update
                    (Function.update
                      (Function.update memP heapStart uhOutPtr)
                      (heapStart + 1) uhLen)
                    (heapStart + 2) (uhOutWords + 1))
                  (heapStart + 3) heapCursor)
                (heapStart + 4) dLen)
              (heapStart + 5) rOutPtr)
            (heapStart + 6) rLen)
      (fun _ => 60) := by
  intro st ω ⟨hm, r2, r9, r10, r15, r16, r11, r12⟩
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := uhLen)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq r11) (hm ▸ huhLen_eq)) ?_
  refine runs_seq_assign_le (v := uhOutPtr + 1 + uhOutWords)
    (Expr.eval_add
      (Expr.eval_add (Expr.eval_reg_of_eq (v := uhOutPtr) (by simp [r11]))
        (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (v := uhOutWords) (by simp [r12])) hretFinal_w) ?_
  refine runs_seq_store_le (x := heapStart) (v := uhOutPtr)
    (Expr.eval_reg_of_eq (v := heapStart) (by simp [r2]))
    (Expr.eval_reg_of_eq (v := uhOutPtr) (by simp [r11])) ?_
  refine runs_seq_store_le (x := heapStart + 1) (v := uhLen)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := heapStart) (by simp [r2]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := uhLen) (by simp)) ?_
  refine runs_seq_store_le (x := heapStart + 2) (v := uhOutWords + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := heapStart) (by simp [r2]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_add (Expr.eval_reg_of_eq (v := uhOutWords) (by simp [r12]))
      (Expr.eval_const (by omega)) (by omega)) ?_
  refine runs_seq_store_le (x := heapStart + 3) (v := heapCursor)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := heapStart) (by simp [r2]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := heapCursor) (by simp [r9])) ?_
  refine runs_seq_store_le (x := heapStart + 4) (v := dLen)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := heapStart) (by simp [r2]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := dLen) (by simp [r10])) ?_
  refine runs_seq_store_le (x := heapStart + 5) (v := rOutPtr)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := heapStart) (by simp [r2]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := rOutPtr) (by simp [r15])) ?_
  refine runs_seq_store_le (x := heapStart + 6) (v := rLen)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := heapStart) (by simp [r2]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := rLen) (by simp [r16])) ?_
  refine runs_ret_le (v := uhOutPtr + 1 + uhOutWords)
    (Expr.eval_reg_of_eq (v := uhOutPtr + 1 + uhOutWords) (by simp)) ⟨rfl, by simp [hm]⟩ ?_
  simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

private lemma updateLoop_tail_triple (c : UpdateLoopCtx) {p : Program} {bs : UpdateLoopBases}
    (hps : HasUpdateLoopProcs c.impl p bs) :
    Triple c.w p
      (UpdateLoopInv c c.U.length)
      (updateLoopTailStmt bs.bUL)
      (fun o st' => ∃ ret, o = .returned ret ∧
        BatchUpdateOutPost c.G₀ c.L c.q c.vCap c.eCap c.b c.k₀ c.impl c.us c.U c.mem0 c.x₀
          c.heapStart st'.mem ret ∧
        c.heapStart + 7 ≤ ret ∧
        ret ≤ c.heapStart + dsUpdateLoopSpace c.G₀ c.impl c.mMax c.L c.q c.vCap c.eCap c.us c.U c.lens c.k₀ ∧
        st'.mem (c.b + dsGenOff) ≤ c.mem0 (c.b + dsGenOff) + dsUpdateLoopGen c.G₀ c.impl c.L c.q c.us c.U.length c.k₀)
      (fun _ =>
        60 * (∑ r ∈ Finset.range c.U.length, (c.resAt r).D.card) +
        60 * (∑ r ∈ Finset.range c.U.length, (c.reembAt r).card) +
        30 * (c.lens.sum + 4 * ∑ r ∈ Finset.range c.U.length, (c.resAt r).UH.length) +
        240 * c.U.length + 760) := by
  intro st1 ω ⟨heapCursor, x, savedHdrs, dLists, rLists, uhLists, uhWords,
    r0, r1, r2, r3, r4, r5, _, _, hcur_ge, hcur_le, hzCur, hxv, hxe, hfoot_lt, hfoot_gap,
    hmeta_lt, hState1, hRev1, hPref1, hgen_le, hframe0, hSaved⟩
  have h16 := c.hw16
  have hsp_tot := c.hspace
  have hend_eq := c.cursorBound_end_eq
  -- Aggregate bounds on `dLists`, `rLists`, `uhLists`, `uhWords`
  have hdLen_sum : ∑ i : Fin c.U.length, (dLists i).length =
      ∑ r ∈ Finset.range c.U.length, (c.resAt r).D.card := by
    refine sum_fin_eq_sum_range _ _ fun i => ?_
    have hs := hSaved i
    rw [← List.toFinset_card_of_nodup hs.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have hrLen_sum : ∑ i : Fin c.U.length, (rLists i).length =
      ∑ r ∈ Finset.range c.U.length, (c.reembAt r).card := by
    refine sum_fin_eq_sum_range _ _ fun i => ?_
    have hs := hSaved i
    rw [← List.toFinset_card_of_nodup hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have huhLen_sum : ∑ i : Fin c.U.length, (uhLists i).length =
      ∑ r ∈ Finset.range c.U.length, (c.resAt r).UH.length := by
    refine sum_fin_eq_sum_range _ _ fun i =>
      (hSaved i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.length_eq
  have huhW_sum_le : ∑ i : Fin c.U.length, uhWords i ≤
      c.lens.sum + 4 * ∑ r ∈ Finset.range c.U.length, (c.resAt r).UH.length := by
    have h1 : ∑ i : Fin c.U.length, uhWords i ≤
        ∑ r ∈ Finset.range c.U.length, (c.lens.getD r 0 + 4 * (c.resAt r).UH.length) :=
      sum_fin_le_sum_range _ _ fun i =>
        (hSaved i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, list_sum_range_lens c.lens_length] at h1
    exact h1
  -- Word bounds from `hend_eq` and `c.hspace`
  have hfix_w : c.b + dsFixedSize c.L c.vCap c.eCap < 2 ^ c.w := by
    have := c.hfix; clear * - this hsp_tot; omega
  have hhdrs_w : c.heapStart + 7 + c.U.length < 2 ^ c.w := by
    dsimp only [dsUpdateLoopSpace] at hsp_tot; clear * - hsp_tot; omega
  have hdOut_w : heapCursor + ∑ i : Fin c.U.length, (dLists i).length < 2 ^ c.w := by
    rw [hdLen_sum]; clear * - hcur_le hend_eq hsp_tot; omega
  have hgen_w2 : st1.mem (c.b + dsGenOff) + 2 < 2 ^ c.w := by
    have hg := c.hgen
    dsimp only [dsUpdateLoopGen, UpdateLoopCtx.stepGen] at hg hgen_le
    clear * - hg hgen_le; omega
  have hgen_w1 : st1.mem (c.b + dsGenOff) + 1 < 2 ^ c.w := by omega
  -- Construct `CollectDCtx` for `D` (`isReemb := false`)
  have hH_pres : ∀ e < c.eCap, st1.mem (dgEPresBase (dsHPtr c.b c.vCap c.eCap) c.vCap + e) ≠ 0 ↔
      e ∈ (c.stAt c.U.length).H.E := fun e he => by
    have h := hState1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1 e he
    rw [h]; split_ifs <;> simp_all
  let cD : CollectDCtx := {
    w := c.w, L := c.L, vCap := c.vCap, eCap := c.eCap, b := c.b,
    stepHdrsPtr := c.heapStart + 7, m := c.U.length, dOutPtr := heapCursor,
    isReemb := false,
    H := (c.stAt c.U.length).H, dLists := dLists, mem0 := st1.mem,
    hw16 := c.hw16, hfix_w := hfix_w, hgen_w := hgen_w1,
    hhdrs_w := hhdrs_w, hdOut_w := hdOut_w,
    hfix_hdrs := le_trans c.hfix (by omega),
    hfix_out := le_trans c.hfix (by omega),
    hhdrs_out := hcur_ge,
    hL := hState1.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hvC := hState1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    heC := hState1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hH := hH_pres,
    hES := fun e he => (hState1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 e he).1,
    hSteps := fun i => by
      have hs := hSaved i
      rcases hs with ⟨hSlot, hHge, hHend, _, _, _, _, hm3, hm4, _, _, hdAt, _, _, hdCap, _, _, _, _, _, _, _⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hSlot, hm3, hm4]
      exact ⟨le_trans c.hfix (by omega), by omega, le_trans c.hfix (by omega), by omega,
        rfl, hdAt, hdCap⟩
  }
  -- Execute `updateLoopTailStmt`
  dsimp only [updateLoopTailStmt]
  refine runs_start_le ?_
  -- 1. `r9 := r5` (`dOutPtr := heapCursor`)
  refine runs_seq_assign_le (v := heapCursor) (Expr.eval_reg_of_eq r5) ?_
  -- 2. `dsCollectBatchD [b, heapStart + 7, c.U.length, heapCursor, 0]` (collect `D`)
  refine runs_seq_call_le (vs := [c.b, c.heapStart + 7, c.U.length, heapCursor, 0])
    (dsCollectBatchD_meetsContract cD hps.hpUL)
    (by simp [evalArgs, Expr.eval, r0, r3, r4, show (0 : ℕ) < 2 ^ c.w by omega])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨rfl, rfl⟩ ?_
  rintro dOutLen memD _ ⟨dOut, hdOutLen_eq, hdOut_le, hdOut_nd, hdOut_mem, hdOut_at, hgenD,
    heStD, hFrD⟩
  subst dOutLen
  dsimp only [cD] at hdOut_le hdOut_mem hdOut_at hgenD heStD hFrD
  -- Transfer `DynSpannerStateAt` across `dsCollectBatchD` (pass 1)
  have hStateD : DynSpannerStateAt c.L c.vCap c.eCap c.b memD x (c.stAt c.U.length) := by
    refine dynSpannerStateAt_of_collectD hState1 (by rw [hgenD]; exact Nat.le_succ _) heStD ?_
    intro a ha1 ha2 hdom
    refine hFrD a ha1 ha2 (Or.inl ?_)
    rcases hdom with hltF | hhf
    · exact lt_of_lt_of_le hltF (le_trans c.hfix (by omega))
    · exact hfoot_lt a hhf
  have hmemD_eq_st1 : ∀ a, c.b + dsFixedSize c.L c.vCap c.eCap ≤ a → a < heapCursor →
      memD a = st1.mem a := fun a h1 h2 => by
    have hcb := collectD_lt_eStamp_bounds c.b c.L c.vCap c.eCap
    have hlt_gen := (stepZero_fixed_lt c.b c.L c.vCap c.eCap).1 dsGenOff (by decide)
    have heSt_top : dsEStampBase c.b c.L c.vCap c.eCap + c.eCap ≤
        c.b + dsFixedSize c.L c.vCap c.eCap :=
      hcb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm ▸
        ((Nat.le_add_right _ _).trans hcb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    exact hFrD a (by omega) (Or.inr (le_trans heSt_top h1)) (Or.inl h2)
  set rOutPtr := heapCursor + dOut.length
  have hrOut_w : rOutPtr + ∑ i : Fin c.U.length, (rLists i).length < 2 ^ c.w := by
    dsimp only [rOutPtr]
    rw [hdLen_sum] at hdOut_le
    rw [hrLen_sum]
    clear * - hcur_le hdOut_le hend_eq hsp_tot; omega
  have hrOutPtr_w : rOutPtr < 2 ^ c.w := by omega
  -- 3. `r15 := r9 + r10` (`rOutPtr := heapCursor + dOut.length`)
  refine runs_seq_assign_le (v := rOutPtr)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := heapCursor) (by simp))
      (Expr.eval_reg_of_eq (v := dOut.length) (by simp)) hrOutPtr_w) ?_
  -- Construct `CollectDCtx` for `R` (`isReemb := true`)
  have hG_pres : ∀ e < c.eCap, memD (dgEPresBase (dsGPtr c.b) c.vCap + e) ≠ 0 ↔
      e ∈ (c.stAt c.U.length).G.E := fun e he => by
    have h := hStateD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1 e he
    rw [h]; split_ifs <;> simp_all
  let cR : CollectDCtx := {
    w := c.w, L := c.L, vCap := c.vCap, eCap := c.eCap, b := c.b,
    stepHdrsPtr := c.heapStart + 7, m := c.U.length, dOutPtr := rOutPtr,
    isReemb := true,
    H := (c.stAt c.U.length).G, dLists := rLists, mem0 := memD,
    hw16 := c.hw16, hfix_w := hfix_w, hgen_w := by rw [hgenD]; omega,
    hhdrs_w := hhdrs_w, hdOut_w := hrOut_w,
    hfix_hdrs := le_trans c.hfix (by omega),
    hfix_out := le_trans c.hfix (by omega),
    hhdrs_out := le_trans hcur_ge (Nat.le_add_right _ _),
    hL := hStateD.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hvC := hStateD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    heC := hStateD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hH := hG_pres,
    hES := heStD,
    hSteps := fun i => by
      have hs := hSaved i
      rcases hs with ⟨hSlot, hHge, hHend, _, _, _, _, _, _, hm5, hm6, _, _, _, _, hrAt, _, _, hrCap, _, _, _⟩
      dsimp only
      have hS_ag : memD (c.heapStart + 7 + i.1) = savedHdrs i :=
        (hmemD_eq_st1 _ (le_trans c.hfix (by omega)) (by omega)).trans hSlot
      have hm5' : memD (savedHdrs i + 5) = savedHdrs i + 7 + (dLists i).length :=
        (hmemD_eq_st1 _ (le_trans c.hfix (by omega)) (by omega)).trans hm5
      have hm6' : memD (savedHdrs i + 6) = (rLists i).length :=
        (hmemD_eq_st1 _ (le_trans c.hfix (by omega)) (by omega)).trans hm6
      simp only [↓reduceIte]
      rw [hS_ag, hm5', hm6']
      refine ⟨le_trans c.hfix (by omega), by omega, le_trans c.hfix (by omega), by omega, rfl,
        fun idx hidx => (hmemD_eq_st1 _ (le_trans c.hfix (by omega)) (by omega)).trans (hrAt idx hidx),
        hrCap⟩
  }
  -- 4. `dsCollectBatchD [b, heapStart + 7, c.U.length, rOutPtr, 1]` (collect `R`)
  refine runs_seq_call_le (vs := [c.b, c.heapStart + 7, c.U.length, rOutPtr, 1])
    (dsCollectBatchD_meetsContract cR hps.hpUL)
    (by simp [evalArgs, Expr.eval, r0, r3, r4, show (1 : ℕ) < 2 ^ c.w by omega])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨rfl, rfl⟩ ?_
  rintro rOutLen memR _ ⟨rOut, hrOutLen_eq, hrOut_le, hrOut_nd, hrOut_mem, hrOut_at, hgenR,
    heStR, hFrR⟩
  subst rOutLen
  dsimp only [cR] at hrOut_le hrOut_mem hrOut_at hgenR heStR hFrR
  -- Transfer `DynSpannerStateAt` across `dsCollectBatchD` (pass 2)
  have hStateR : DynSpannerStateAt c.L c.vCap c.eCap c.b memR x (c.stAt c.U.length) := by
    refine dynSpannerStateAt_of_collectD hStateD (by rw [hgenR]; exact Nat.le_succ _) heStR ?_
    intro a ha1 ha2 hdom
    refine hFrR a ha1 ha2 (Or.inl ?_)
    rcases hdom with hltF | hhf
    · exact lt_of_lt_of_le hltF (le_trans c.hfix (by omega))
    · exact lt_of_lt_of_le (hfoot_lt a hhf) (Nat.le_add_right _ _)
  have hmemR_eq_memD : ∀ a, c.b + dsFixedSize c.L c.vCap c.eCap ≤ a → a < rOutPtr →
      memR a = memD a := fun a h1 h2 => by
    have hcb := collectD_lt_eStamp_bounds c.b c.L c.vCap c.eCap
    have hlt_gen := (stepZero_fixed_lt c.b c.L c.vCap c.eCap).1 dsGenOff (by decide)
    have heSt_top : dsEStampBase c.b c.L c.vCap c.eCap + c.eCap ≤
        c.b + dsFixedSize c.L c.vCap c.eCap :=
      hcb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm ▸
        ((Nat.le_add_right _ _).trans hcb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    exact hFrR a (by omega) (Or.inr (le_trans heSt_top h1)) (Or.inl h2)
  have hmemR_eq_st1 : ∀ a, c.b + dsFixedSize c.L c.vCap c.eCap ≤ a → a < heapCursor →
      memR a = st1.mem a := fun a h1 h2 =>
    (hmemR_eq_memD a h1 (lt_of_lt_of_le h2 (Nat.le_add_right _ _))).trans (hmemD_eq_st1 a h1 h2)
  set uhOutPtr := rOutPtr + rOut.length
  have huhOut_w : uhOutPtr < 2 ^ c.w := lt_of_le_of_lt (Nat.add_le_add_left hrOut_le _) hrOut_w
  -- 5. `r11 := r15 + r16` (`uhOutPtr := rOutPtr + rOut.length`)
  refine runs_seq_assign_le (v := uhOutPtr)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := rOutPtr) (by simp))
      (Expr.eval_reg_of_eq (v := rOut.length) (by simp)) huhOut_w) ?_
  -- Word bounds and `PackUHCtx`
  have htotLen_w : ∑ i : Fin c.U.length, (uhLists i).length < 2 ^ c.w := by
    rw [huhLen_sum]; clear * - hend_eq hsp_tot; omega
  have htotW_le_end : uhOutPtr + 1 + ∑ i : Fin c.U.length, uhWords i ≤
      c.heapStart + dsUpdateLoopSpace c.G₀ c.impl c.mMax c.L c.q c.vCap c.eCap c.us c.U c.lens c.k₀ := by
    dsimp only [uhOutPtr, rOutPtr]
    rw [hdLen_sum] at hdOut_le
    rw [hrLen_sum] at hrOut_le
    clear * - hcur_le hdOut_le hrOut_le huhW_sum_le hend_eq
    omega
  have htotW_w : uhOutPtr + 1 + ∑ i : Fin c.U.length, uhWords i < 2 ^ c.w :=
    lt_of_le_of_lt htotW_le_end hsp_tot
  let cP : PackUHCtx := {
    w := c.w, stepHdrsPtr := c.heapStart + 7, m := c.U.length, uhOutPtr := uhOutPtr,
    Hs := fun i => (c.stAt i).H, uhLists := uhLists, uhWords := uhWords, mem0 := memR,
    hw16 := c.hw16, hhdrs_w := hhdrs_w, htotLen_w := htotLen_w, htotW_w := htotW_w,
    hhdrs_out := le_trans hcur_ge (by dsimp only [uhOutPtr, rOutPtr]; omega),
    hstepH := fun i => by
      have hi_lt : i.1 < c.U.length := i.2
      have hu_i : c.us[c.k₀ + i.1]? = some (c.U[i.1]'hi_lt) := c.hslice i.1 hi_lt
      have hperm_i : (uhLists i).Perm
          (step (runState (L := c.L) c.G₀ c.q (canonicalSparsify c.impl) c.us (c.k₀ + i.1))
            (c.U[i.1]'hi_lt) (canonicalSparsify c.impl)).UH := by
        simpa [UpdateLoopCtx.resAt, runStepOut, hu_i] using
          (hSaved i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hPref_i : ∀ s ≤ c.k₀ + i.1, SnapInv c.G₀ c.L c.q c.mMax
          (canonicalSparsifyParams c.impl c.mMax).absorbTime (canonicalSparsify c.impl) c.us s :=
        fun s hs => hPref1 s (by omega)
      have hab := applyBatch_perm_step_UH c.hVG₀ c.hL1 c.hq1 c.hGm₀
        (canonicalSparsify_spec_absorb c.impl c.mMax) c.hBV c.hds hu_i hPref_i hperm_i
      have hst_next : (step (c.stAt i.1) (c.U[i.1]'hi_lt) (canonicalSparsify c.impl)).state =
          c.stAt (i.1 + 1) := by
        dsimp only [UpdateLoopCtx.stAt]
        rw [show c.k₀ + (i.1 + 1) = c.k₀ + i.1 + 1 by omega]
        simp only [runState, hu_i]
      rw [← hst_next]
      exact hab.symm,
    hSteps := fun i => by
      have hs := hSaved i
      rcases hs with ⟨hSlot, hHge, hHend, _, hm0, hm1, hm2, _, _, _, _, _, _, _, _, _, _, _, _, huhBat, _, _⟩
      dsimp only
      have hS_ag : memR (c.heapStart + 7 + i.1) = savedHdrs i :=
        (hmemR_eq_st1 _ (le_trans c.hfix (by omega)) (by omega)).trans hSlot
      have hm0' : memR (savedHdrs i) = savedHdrs i + 7 + (dLists i).length + (rLists i).length :=
        (hmemR_eq_st1 _ (le_trans c.hfix (by omega)) (by omega)).trans hm0
      have hm1' : memR (savedHdrs i + 1) = (uhLists i).length :=
        (hmemR_eq_st1 _ (le_trans c.hfix (by omega)) (by omega)).trans hm1
      have hm2' : memR (savedHdrs i + 2) = uhWords i :=
        (hmemR_eq_st1 _ (le_trans c.hfix (by omega)) (by omega)).trans hm2
      rw [hS_ag, hm0', hm1', hm2']
      refine ⟨by omega, by omega, rfl, rfl,
        huhBat.of_agree fun k hk => hmemR_eq_st1 _ (le_trans c.hfix (by omega)) (by omega)⟩
  }
  -- 6. `dsPackBatchUH [heapStart + 7, c.U.length, uhOutPtr]`
  refine runs_seq_call_le (vs := [c.heapStart + 7, c.U.length, uhOutPtr])
    (dsPackBatchUH_meetsContract cP hps.hpSZ.hpAux hps.hpUL)
    (by simp [evalArgs, Expr.eval, r3, r4])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> omega)
    ⟨rfl, rfl⟩ ?_
  rintro uhOutWords memP _ ⟨huhW_eq, hBatP, hFrP⟩
  dsimp only [cP] at huhW_eq hBatP hFrP
  set uhActualAll := (List.finRange c.U.length).flatMap uhLists
  set retFinal := uhOutPtr + 1 + uhOutWords
  have hretFinal_le : retFinal ≤
      c.heapStart + dsUpdateLoopSpace c.G₀ c.impl c.mMax c.L c.q c.vCap c.eCap c.us c.U c.lens c.k₀ := by
    dsimp only [retFinal]; rw [huhW_eq]; exact htotW_le_end
  have hretFinal_w : retFinal < 2 ^ c.w := lt_of_le_of_lt hretFinal_le hsp_tot
  -- 7-10. Write 7-word batch output header at `heapStart..heapStart+6` and return `retFinal`
  refine runs_triple_le
    (updateLoop_writeHdr_triple (w := c.w) (p := p) (heapStart := c.heapStart)
      (heapCursor := heapCursor) (dLen := dOut.length) (rOutPtr := rOutPtr) (rLen := rOut.length)
      (uhOutPtr := uhOutPtr) (uhLen := uhActualAll.length) (uhOutWords := uhOutWords) (memP := memP)
      c.hw16 (by clear * - hhdrs_w; omega) hretFinal_w hBatP.2.1)
    ⟨rfl, by simp [r2], by simp, by simp, by simp, by simp, by simp, by simp⟩
    (fun o stF ⟨hoF, hmemF_eq⟩ => ?_) ?_
  · rw [hoF]
    set memF := stF.mem
    have hmemF_outside_hdr : ∀ a, a < c.heapStart ∨ c.heapStart + 7 ≤ a → memF a = memP a :=
      fun a ha => by
        rw [show memF = _ from hmemF_eq]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
    have hmemF_eq_memR_lt : ∀ a < uhOutPtr, a < c.heapStart ∨ c.heapStart + 7 ≤ a →
        memF a = memR a := fun a h1 h2 =>
      (hmemF_outside_hdr a h2).trans (hFrP a (Or.inl h1))
    have hsliceSpec := update_slice_spec (L := c.L) c.G₀ c.q (canonicalSparsify c.impl) c.us c.U c.k₀ c.hslice
    have hStateF : DynSpannerStateAt c.L c.vCap c.eCap c.b memF x
        (update (runState (L := c.L) c.G₀ c.q (canonicalSparsify c.impl) c.us c.k₀) c.U
          (canonicalSparsify c.impl)).state := by
      rw [hsliceSpec.1]
      have hlt_gen := (stepZero_fixed_lt c.b c.L c.vCap c.eCap).1 dsGenOff (by decide)
      have hgen_eq : memF (c.b + dsGenOff) = memR (c.b + dsGenOff) :=
        hmemF_eq_memR_lt _ (lt_of_lt_of_le hlt_gen.2 (le_trans c.hfix (by omega)))
          (Or.inl (lt_of_lt_of_le hlt_gen.2 c.hfix))
      refine dynSpannerStateAt_of_collectD hStateR (le_of_eq hgen_eq.symm) (fun e he => ?_)
        (fun a _ _ hdom => ?_)
      · have hlt_e := (stepZero_fixed_lt c.b c.L c.vCap c.eCap).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he
        rw [hmemF_eq_memR_lt _ (lt_of_lt_of_le hlt_e.2 (le_trans c.hfix (by omega)))
            (Or.inl (lt_of_lt_of_le hlt_e.2 c.hfix)), hgen_eq]
        exact heStR e he
      · rcases hdom with hltF | hhf
        · exact hmemF_eq_memR_lt a (lt_of_lt_of_le hltF (le_trans c.hfix (by omega)))
            (Or.inl (lt_of_lt_of_le hltF c.hfix))
        · refine hmemF_eq_memR_lt a (lt_of_lt_of_le (hfoot_lt a hhf) (by dsimp only [uhOutPtr, rOutPtr]; omega)) ?_
          rcases hfoot_gap a hhf with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (by omega)
    have hgenF : memF (c.b + dsGenOff) ≤
        c.mem0 (c.b + dsGenOff) + dsUpdateLoopGen c.G₀ c.impl c.L c.q c.us c.U.length c.k₀ := by
      have hlt_gen := (stepZero_fixed_lt c.b c.L c.vCap c.eCap).1 dsGenOff (by decide)
      rw [hmemF_eq_memR_lt _ (lt_of_lt_of_le hlt_gen.2 (le_trans c.hfix (by omega)))
          (Or.inl (lt_of_lt_of_le hlt_gen.2 c.hfix)), hgenR, hgenD]
      dsimp only [dsUpdateLoopGen, UpdateLoopCtx.stepGen] at hgen_le ⊢
      clear * - hgen_le; omega
    have hzF : ZeroFrom memF retFinal := fun a ha => by
      have ha_ge : c.heapStart + 7 ≤ a := by clear * - hcur_ge ha; omega
      have ha_r : rOutPtr + rOut.length ≤ a := by clear * - ha; omega
      have ha_d : heapCursor + dOut.length ≤ a := by clear * - ha; omega
      have hcb := collectD_lt_eStamp_bounds c.b c.L c.vCap c.eCap
      have hlt_gen := (stepZero_fixed_lt c.b c.L c.vCap c.eCap).1 dsGenOff (by decide)
      have heSt_top : dsEStampBase c.b c.L c.vCap c.eCap + c.eCap ≤
          c.b + dsFixedSize c.L c.vCap c.eCap :=
        hcb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm ▸
          ((Nat.le_add_right _ _).trans hcb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
      rw [hmemF_outside_hdr a (Or.inr ha_ge), hFrP a (Or.inr ha),
        hFrR a (by have := c.hfix; omega) (Or.inr (le_trans heSt_top (le_trans c.hfix (by omega))))
          (Or.inr ha_r),
        hFrD a (by have := c.hfix; omega) (Or.inr (le_trans heSt_top (le_trans c.hfix (by omega))))
          (Or.inr ha_d)]
      exact hzCur a (by clear * - ha_d; omega)
    have hBatF : BatchAt memF uhOutPtr
        (runState (L := c.L) c.G₀ c.q (canonicalSparsify c.impl) c.us c.k₀).H
        uhActualAll (1 + uhOutWords) := by
      have h1 : memF uhOutPtr = memP uhOutPtr := hmemF_outside_hdr _ (Or.inr (by omega))
      have h2 : BatchBodyAt memF (uhOutPtr + 1) (c.stAt 0).H uhActualAll uhOutWords := by
        have hbody := hBatP.2.2
        simp only [Nat.add_sub_cancel_left] at hbody
        exact hbody.of_agree fun k _ => hmemF_outside_hdr _ (Or.inr (by omega))
      exact ⟨by omega, h1.trans hBatP.2.1,
        by simpa only [Nat.add_sub_cancel_left, UpdateLoopCtx.stAt, Nat.add_zero] using h2⟩
    have hPermF : uhActualAll.Perm
        (update (runState (L := c.L) c.G₀ c.q (canonicalSparsify c.impl) c.us c.k₀) c.U
          (canonicalSparsify c.impl)).UH := by
      rw [hsliceSpec.2.1]
      exact perm_flatMap_finRange_range uhLists (fun r => (c.resAt r).UH)
        (fun i => (hSaved i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    have hAppF : (runState (L := c.L) c.G₀ c.q (canonicalSparsify c.impl) c.us c.k₀).H.applyBatch
        uhActualAll =
        (update (runState (L := c.L) c.G₀ c.q (canonicalSparsify c.impl) c.us c.k₀) c.U
          (canonicalSparsify c.impl)).state.H := by
      rw [hsliceSpec.1]
      exact applyBatch_flatMap_finRange (fun i => (c.stAt i).H) uhLists cP.hstepH
    have hdFinF : dOut.toFinset =
        (update (runState (L := c.L) c.G₀ c.q (canonicalSparsify c.impl) c.us c.k₀) c.U
          (canonicalSparsify c.impl)).D := by
      rw [hsliceSpec.2.2.1]
      ext e
      simp only [List.mem_toFinset, hdOut_mem, Finset.mem_inter, Finset.mem_biUnion,
        Finset.mem_range]
      refine and_congr ?_ Iff.rfl
      constructor
      · rintro ⟨i, hi⟩
        have hmem_D : e ∈ (c.resAt i.1).D := by
          rw [← (hSaved i).2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact List.mem_toFinset.mpr hi
        exact ⟨i.1, i.2, hmem_D⟩
      · rintro ⟨r, hr, heD⟩
        have hmem_L : e ∈ dLists ⟨r, hr⟩ := by
          rw [← List.mem_toFinset, (hSaved ⟨r, hr⟩).2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact heD
        exact ⟨⟨r, hr⟩, hmem_L⟩
    have hdAtF : ListAt memF heapCursor dOut := fun idx hidx => by
      rw [hmemF_eq_memR_lt _ (by dsimp only [uhOutPtr, rOutPtr]; clear * - hidx; omega)
            (Or.inr (by clear * - hcur_ge; omega)),
          hmemR_eq_memD _ (le_trans c.hfix (by clear * - hcur_ge; omega))
            (by dsimp only [rOutPtr]; clear * - hidx; omega)]
      exact hdOut_at idx hidx
    have hrFinF : rOut.toFinset =
        updateReembSet (runState (L := c.L) c.G₀ c.q (canonicalSparsify c.impl) c.us c.k₀) c.U
          (canonicalSparsify c.impl) := by
      rw [updateReembSet_run_eq c.G₀ c.us c.U c.k₀ c.hslice]
      ext e
      simp only [List.mem_toFinset, hrOut_mem, Finset.mem_inter, Finset.mem_biUnion,
        Finset.mem_range]
      refine and_congr ?_ Iff.rfl
      constructor
      · rintro ⟨i, hi⟩
        have hmem_R : e ∈ c.reembAt i.1 := by
          rw [← (hSaved i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact List.mem_toFinset.mpr hi
        exact ⟨i.1, i.2, hmem_R⟩
      · rintro ⟨r, hr, heR⟩
        have hmem_L : e ∈ rLists ⟨r, hr⟩ := by
          rw [← List.mem_toFinset, (hSaved ⟨r, hr⟩).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
          exact heR
        exact ⟨⟨r, hr⟩, hmem_L⟩
    have hrAtF : ListAt memF rOutPtr rOut := fun idx hidx => by
      rw [hmemF_eq_memR_lt _ (by dsimp only [uhOutPtr]; clear * - hidx; omega)
            (Or.inr (by clear * - hcur_ge; omega))]
      exact hrOut_at idx hidx
    have hFrameF : ∀ a < c.heapStart, ¬ metaFoot c.b c.x₀ a → memF a = c.mem0 a :=
      fun a ha hnf => by
        have hnot_fix : ¬ (c.b ≤ a ∧ a < c.b + dsFixedSize c.L c.vCap c.eCap) := by
          intro h; apply hnf; left; rw [c.hState₀.1, c.hState₀.2.1]; exact h
        have hcb := collectD_lt_eStamp_bounds c.b c.L c.vCap c.eCap
        have hlt_gen := (stepZero_fixed_lt c.b c.L c.vCap c.eCap).1 dsGenOff (by decide)
        have heSt_top : dsEStampBase c.b c.L c.vCap c.eCap + c.eCap ≤
            c.b + dsFixedSize c.L c.vCap c.eCap :=
          hcb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm ▸
            ((Nat.le_add_right _ _).trans hcb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
        have ha_ne_gen : a ≠ c.b + dsGenOff := fun heq =>
          hnot_fix ⟨by omega, heq ▸ hlt_gen.2⟩
        have ha_out_eSt : a < dsEStampBase c.b c.L c.vCap c.eCap ∨
            dsEStampBase c.b c.L c.vCap c.eCap + c.eCap ≤ a := by
          by_cases h1 : a < c.b
          · left; have := hcb.1; have := hcb.2.2.1; omega
          · by_cases h2 : c.b + dsFixedSize c.L c.vCap c.eCap ≤ a
            · right; exact le_trans heSt_top h2
            · exact (hnot_fix ⟨by omega, by omega⟩).elim
        rw [hmemF_eq_memR_lt a (lt_of_lt_of_le ha (by omega)) (Or.inl ha),
          hFrR a ha_ne_gen ha_out_eSt (Or.inl (lt_of_lt_of_le ha (by omega))),
          hFrD a ha_ne_gen ha_out_eSt (Or.inl (lt_of_lt_of_le ha (by omega)))]
        exact hframe0 a ha hnf
    refine ⟨retFinal, rfl, ⟨uhOutPtr, uhOutWords, heapCursor, rOutPtr, uhActualAll, dOut, rOut, x,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, rfl, rfl, rfl, hBatF, hPermF, hAppF,
      hdOut_nd, hdFinF, hdAtF, hrOut_nd, hrFinF, hrAtF, hzF,
      hxv, hxe, fun a ha => lt_of_lt_of_le (hfoot_lt a ha) (by omega), hStateF, hRev1, hFrameF,
      hmeta_lt⟩,
      by clear * - hcur_ge; omega, hretFinal_le, hgenF⟩
    · rw [show memF = _ from hmemF_eq]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · rw [show memF = _ from hmemF_eq]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
    · rw [show memF = _ from hmemF_eq]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_self, Nat.add_comm]
    · rw [show memF = _ from hmemF_eq]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
    · rw [show memF = _ from hmemF_eq]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · rw [show memF = _ from hmemF_eq]
      rw [Function.update_of_ne (by omega), Function.update_self]
    · rw [show memF = _ from hmemF_eq]
      rw [Function.update_self]
  · -- Tail cost bound
    simp only [dsCollectBatchDContract, dsPackBatchUHContract, Expr.size_const, Expr.size_reg,
      Expr.size_bin, argsSize_cons, argsSize_nil]
    dsimp only [cD, cR, cP]
    rw [hdLen_sum, hrLen_sum]
    clear * - huhW_sum_le
    omega

/-! ## Top-level batch update loop theorem -/

public section

/-- The batch update loop `dsUpdateLoopStmt` meets `dsUpdateLoopContract`: executes Algorithm 6's
`step` (dispatching between `dsStepZeroStmt` for `j = 0` and `dsStepPosFullStmt` for `0 < j`) on
every update of the batch `U` in order, packs `D` and `U_H`, and terminates in at most
`dsUpdateLoopCost` steps (Theorem 8.2, page 64). -/
theorem dsUpdateLoop_meetsContract {G₀ : MGraph} {impl : SparsifyImpl}
    {mMax w L q vCap eCap b k₀ : ℕ} {us U : List Update} {lens : List ℕ}
    {x₀ : DynSpannerMeta L} {p : Program} {bs : UpdateLoopBases}
    (hps : HasUpdateLoopProcs impl p bs) :
    MeetsContract w p (bs.bUL + updateLoopIdxUpdate)
      (dsUpdateLoopContract G₀ impl mMax w L q vCap eCap b k₀ us U lens x₀) := by
  refine meetsContract_of_runs
    (hps.hpUL.get (i := updateLoopIdxUpdate) (by simp [updateLoopProcs, updateLoopIdxUpdate])) ?_
  rintro args mem0 pos ω _ ⟨batchPtr, heapStart, rfl, hw16, hL1, hq1, hVG₀, hGm₀, hE₀_cap, hBV,
    hds, hslice, hPref₀, hState₀, hRev₀, hfix, hfoot₀, hz₀, hspace, hgen, hk_w, hq_w, hWOK,
    hfixB, hbatch_le, hbatch_foot, hbatch_w, hbatch_len, hbatch_body, hbatch_cap⟩
  let c : UpdateLoopCtx := {
    G₀, impl, mMax, w, L, q, vCap, eCap, b, k₀, us, U, lens, x₀, batchPtr, heapStart, mem0,
    hw16, hL1, hq1, hVG₀, hGm₀, hE₀_cap, hBV, hds, hslice, hPref₀, hState₀, hRev₀, hfix, hfoot₀,
    hz₀, hspace, hgen, hk_w, hq_w, hWOK, hfixB, hbatch_le, hbatch_foot, hbatch_w, hbatch_len,
    hbatch_body, hbatch_cap
  }
  have hhs7_w : heapStart + 7 < 2 ^ w := by
    dsimp only [dsUpdateLoopSpace] at hspace; clear * - hspace; omega
  have hhs7m_w : heapStart + 7 + U.length < 2 ^ w := by
    dsimp only [dsUpdateLoopSpace] at hspace; clear * - hspace; omega
  have hbp1_w : batchPtr + 1 < 2 ^ w := by clear * - hbatch_le hhs7_w; omega
  simp only [updateLoopProcs, updateLoopIdxUpdate, List.getElem_cons_succ, List.getElem_cons_zero]
  dsimp only [dsUpdateLoopStmt]
  refine runs_start_le ?_
  -- 1. Setup registers `r3..r6`
  refine runs_seq_assign_le (v := U.length)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (v := batchPtr) (by simp [startState])) hbatch_len) ?_
  refine runs_seq_assign_le (v := heapStart + 7)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := heapStart) (by simp [startState]))
      (Expr.eval_const (by omega)) hhs7_w) ?_
  refine runs_seq_assign_le (v := heapStart + 7 + U.length)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := heapStart + 7) (by simp))
      (Expr.eval_reg_of_eq (v := U.length) (by simp)) hhs7m_w) ?_
  refine runs_seq_assign_le (v := batchPtr + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := batchPtr) (by simp [startState]))
      (Expr.eval_const (by omega)) hbp1_w) ?_
  -- 2. Execute the `forRange` loop over all `U.length` updates
  refine runs_seq_triple_le (updateLoop_forRange_triple c hps)
    ⟨rfl, by simp [startState, c], by simp [startState, c], by simp [startState, c],
      by simp [c], by simp [c], by simp [c], by simp [c]⟩ ?_
  rintro st1 hInv1
  -- 3. Execute the tail (`CollectD` for `D` and `R`, `PackUH`, 7 header stores, return)
  refine runs_triple_le (updateLoop_tail_triple c hps) hInv1
    (fun o st' ⟨ret, hret, hPost, hge7, hleSp, hgenF⟩ => by
      rw [hret]; exact ⟨batchPtr, heapStart, rfl, hPost, hge7, hleSp, hgenF⟩) ?_
  -- 4. Total cost bound against `dsUpdateLoopCost`
  have hrc := rangeCost_loop_eq c
  have hsum_add : (∑ r ∈ Finset.range U.length, (c.stepCost r + 35 * L + 510)) + U.length * 9 ≤
      ∑ r ∈ Finset.range U.length, (c.stepCost r + 35 * L + 520) := by
    have hcard : U.length * 9 = ∑ _r ∈ Finset.range U.length, 9 := by
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [hcard, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun r _ => by omega
  dsimp only [dsUpdateLoopContract, dsUpdateLoopCost]
  simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
  rw [hrc]
  dsimp only [c, UpdateLoopCtx.stepCost, UpdateLoopCtx.resAt, UpdateLoopCtx.reembAt] at hsum_add ⊢
  clear * - hsum_add
  omega

end

end MinCostFlow.DynSpanner.Program
