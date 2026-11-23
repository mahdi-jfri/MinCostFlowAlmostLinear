module

public import MinCostFlow.DynSpanner.Program.DynSpannerUpdateLoopAux
import Mathlib.Tactic.Ring

/-!
# Verification of step-output saving and batch `U_H` packing (`DynSpannerUpdateLoopPack`)

Proves the Word-RAM contracts for `dsSaveStepOutStmt` and `dsPackBatchUHStmt`:

* `dsSaveStepOut_meetsContract`: copies a single step's `D` list and `U_H` body into a fresh
  5-word saved descriptor + lists starting at `retPtr` (outside `metaFoot b x'`), in
  `30 * dLen + 30 * uhWords + 120` steps.
* `dsPackBatchUH_meetsContract`: concatenates the `m` saved per-step `U_H` bodies into a single
  `BatchAt` encoding at `uhOutPtr`, in `30 * (∑ i, uhWords i) + 80 * m + 60` steps.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

public section

/-! ## 1. Verification of `dsSaveStepOutStmt` -/

/-- `dsSaveStepOutStmt` meets `dsSaveStepOutContract`. -/
theorem dsSaveStepOut_meetsContract {w stepHdr retPtr uhPtr uhLen uhWords dPtr dLen rPtr rLen : ℕ}
    {p : Program} {bAux bPhase bSZ bPosFull bUL : ℕ}
    (hpAux : p.HasAt bAux stepAuxProcs)
    (hpUL : p.HasAt bUL (updateLoopProcs bAux bPhase bSZ bPosFull bUL)) :
    MeetsContract w p (bUL + updateLoopIdxSaveStep)
      (dsSaveStepOutContract w stepHdr retPtr uhPtr uhLen uhWords dPtr dLen rPtr rLen) := by
  refine meetsContract_of_runs
    (hpUL.get (i := updateLoopIdxSaveStep) (by simp [updateLoopProcs, updateLoopIdxSaveStep])) ?_
  rintro args mem0 pos ω _ ⟨rfl, hw16, h5d, hdU, huR, hrR, hR_w, hm0, hm1, hm2, hm3, hm4, hmr0, hmr1⟩
  simp only [updateLoopProcs, updateLoopIdxSaveStep, List.getElem_cons_succ, List.getElem_cons_zero]
  dsimp only [dsSaveStepOutStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := uhPtr)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState])) hm0) ?_
  refine runs_seq_assign_le (v := uhLen)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := stepHdr) (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) hm1) ?_
  refine runs_seq_assign_le (v := uhWords)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := stepHdr) (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) hm2) ?_
  refine runs_seq_assign_le (v := dPtr)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := stepHdr) (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) hm3) ?_
  refine runs_seq_assign_le (v := dLen)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := stepHdr) (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) hm4) ?_
  refine runs_seq_assign_le (v := rPtr)
    (Expr.eval_load_of_eq (Expr.eval_sub (Expr.eval_reg_of_eq (v := retPtr) (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) hmr0) ?_
  refine runs_seq_assign_le (v := rLen)
    (Expr.eval_load_of_eq (Expr.eval_sub (Expr.eval_reg_of_eq (v := retPtr) (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) hmr1) ?_
  refine runs_seq_assign_le (v := retPtr + 7)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := retPtr) (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) ?_
  refine runs_seq_call_le (vs := [dPtr, retPtr + 7, dLen])
    (dsCopyWords_meetsContract (w := w) (n := dLen) hpAux)
    (by simp [evalArgs, Expr.eval])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> omega)
    ⟨dPtr, retPtr + 7, rfl, hw16, by omega, by omega, by unfold IvlDisj; omega⟩ ?_
  rintro _ mem1 _ ⟨_, _, hEq1, _, hcpD, hfr1⟩
  simp only [List.cons.injEq, and_true] at hEq1
  rcases hEq1 with ⟨rfl, rfl⟩
  dsimp only [startState] at hcpD hfr1
  refine runs_seq_assign_le (v := retPtr + 7 + dLen)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := retPtr + 7) (by simp))
      (Expr.eval_reg_of_eq (v := dLen) (by simp)) (by omega)) ?_
  refine runs_seq_call_le (vs := [rPtr, retPtr + 7 + dLen, rLen])
    (dsCopyWords_meetsContract (w := w) (n := rLen) hpAux)
    (by simp [evalArgs, Expr.eval])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> omega)
    ⟨rPtr, retPtr + 7 + dLen, rfl, hw16, by omega, by omega, by unfold IvlDisj; omega⟩ ?_
  rintro _ mem2 _ ⟨_, _, hEq2, _, hcpR, hfr2⟩
  simp only [List.cons.injEq, and_true] at hEq2
  rcases hEq2 with ⟨rfl, rfl⟩
  dsimp only at hcpR hfr2
  refine runs_seq_assign_le (v := retPtr + 7 + dLen + rLen)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := retPtr + 7 + dLen) (by simp))
      (Expr.eval_reg_of_eq (v := rLen) (by simp)) (by omega)) ?_
  refine runs_seq_call_le (vs := [uhPtr, retPtr + 7 + dLen + rLen, uhWords])
    (dsCopyWords_meetsContract (w := w) (n := uhWords) hpAux)
    (by simp [evalArgs, Expr.eval])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> omega)
    ⟨uhPtr, retPtr + 7 + dLen + rLen, rfl, hw16, by omega, by omega, by unfold IvlDisj; omega⟩ ?_
  rintro _ mem3 _ ⟨_, _, hEq3, _, hcpU, hfr3⟩
  simp only [List.cons.injEq, and_true] at hEq3
  rcases hEq3 with ⟨rfl, rfl⟩
  dsimp only at hcpU hfr3
  refine runs_seq_store_le (x := retPtr) (v := retPtr + 7 + dLen + rLen)
    (Expr.eval_reg_of_eq (v := retPtr) (by simp [startState]))
    (Expr.eval_reg_of_eq (v := retPtr + 7 + dLen + rLen) (by simp)) ?_
  refine runs_seq_store_le (x := retPtr + 1) (v := uhLen)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := retPtr) (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := uhLen) (by simp)) ?_
  refine runs_seq_store_le (x := retPtr + 2) (v := uhWords)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := retPtr) (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := uhWords) (by simp)) ?_
  refine runs_seq_store_le (x := retPtr + 3) (v := retPtr + 7)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := retPtr) (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := retPtr + 7) (by simp)) ?_
  refine runs_seq_store_le (x := retPtr + 4) (v := dLen)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := retPtr) (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := dLen) (by simp)) ?_
  refine runs_seq_store_le (x := retPtr + 5) (v := retPtr + 7 + dLen)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := retPtr) (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := retPtr + 7 + dLen) (by simp)) ?_
  refine runs_seq_store_le (x := retPtr + 6) (v := rLen)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := retPtr) (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := rLen) (by simp)) ?_
  refine runs_ret_le (v := retPtr + 7 + dLen + rLen + uhWords)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := retPtr + 7 + dLen + rLen) (by simp))
      (Expr.eval_reg_of_eq (v := uhWords) (by simp)) (by omega)) ?_ ?_
  · dsimp only [Outcome.value]
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_self]
    · intro i hi
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), hfr3 _ (Or.inl (by omega)), hfr2 _ (Or.inl (by omega)),
        hcpD i hi]
    · intro i hi
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), hfr3 _ (Or.inl (by omega)), hcpR i hi,
        hfr1 _ (Or.inl (by omega))]
    · intro i hi
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), hcpU i hi, hfr2 _ (Or.inl (by omega)),
        hfr1 _ (Or.inl (by omega))]
    · intro a ha
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), hfr3 a (by omega), hfr2 a (by omega), hfr1 a (by omega)]
  · simp only [dsSaveStepOutContract, dsCopyWordsContract, Expr.size_const, Expr.size_reg,
      Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil]; omega

/-! ## 2. Verification of `dsPackBatchUHStmt` -/

private lemma applyBatch_flatMap_take (c : PackUHCtx) :
    ∀ i ≤ c.m, (c.Hs 0).applyBatch (((List.finRange c.m).take i).flatMap c.uhLists) = c.Hs i := by
  intro i
  induction i with
  | zero => intro _; simp [MGraph.applyBatch]
  | succ i ih =>
    intro hi
    have hilt : i < c.m := Nat.lt_of_succ_le hi
    rw [flatMap_finRange_take_succ hilt]
    simp only [MGraph.applyBatch, List.foldl_append]
    rw [show List.foldl MGraph.applyUpdate (c.Hs 0)
        (((List.finRange c.m).take i).flatMap c.uhLists) = c.Hs i from ih (Nat.le_of_lt hilt)]
    exact (c.hstepH ⟨i, hilt⟩).symm

private def PackUHInv (c : PackUHCtx) (i : ℕ) (st : State) : Prop :=
  let totLen := (((List.finRange c.m).take i).map fun r => (c.uhLists r).length).sum
  let curW := (((List.finRange c.m).take i).map c.uhWords).sum
  st.regs 0 = c.stepHdrsPtr ∧ st.regs 1 = c.m ∧ st.regs 2 = c.uhOutPtr ∧
  st.regs 3 = totLen ∧ st.regs 4 = curW ∧ st.regs 5 = i ∧
  BatchBodyAt st.mem (c.uhOutPtr + 1) (c.Hs 0) (((List.finRange c.m).take i).flatMap c.uhLists) curW ∧
  ∀ a, a < c.uhOutPtr + 1 ∨ c.uhOutPtr + 1 + curW ≤ a → st.mem a = c.mem0 a

/-- `dsPackBatchUHStmt` meets `dsPackBatchUHContract`. -/
theorem dsPackBatchUH_meetsContract (c : PackUHCtx) {p : Program}
    {bAux bPhase bSZ bPosFull bUL : ℕ}
    (hpAux : p.HasAt bAux stepAuxProcs)
    (hpUL : p.HasAt bUL (updateLoopProcs bAux bPhase bSZ bPosFull bUL)) :
    MeetsContract c.w p (bUL + updateLoopIdxPackUH) (dsPackBatchUHContract c) := by
  refine meetsContract_of_runs
    (hpUL.get (i := updateLoopIdxPackUH) (by simp [updateLoopProcs, updateLoopIdxPackUH])) ?_
  rintro args mem0 pos ω _ ⟨rfl, rfl⟩
  have h16 := c.hw16
  set loopBody : Stmt :=
    .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
    .assign 7 (.load (.reg 6)) ;;
    .assign 8 (.load (.bin .add (.reg 6) (.const 1))) ;;
    .assign 9 (.load (.bin .add (.reg 6) (.const 2))) ;;
    .assign 10 (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 4)) ;;
    .call 11 (bAux + stepAuxIdxCopyWords) [.reg 7, .reg 10, .reg 9] ;;
    .assign 3 (.bin .add (.reg 3) (.reg 8)) ;;
    .assign 4 (.bin .add (.reg 4) (.reg 9))
  set stepCost : ℕ → ℕ := fun i =>
    if hi : i < c.m then 30 * c.uhWords ⟨i, hi⟩ + 70 else 70
  have hloop : Triple c.w p
      (fun st => st.mem = c.mem0 ∧ st.regs 0 = c.stepHdrsPtr ∧ st.regs 1 = c.m ∧
        st.regs 2 = c.uhOutPtr ∧ st.regs 3 = 0 ∧ st.regs 4 = 0)
      (forRange 5 (.const 0) (.reg 1) loopBody)
      (normalPost (PackUHInv c c.m))
      (fun _ => rangeCost stepCost 0 c.m + c.m * 9 + 7) := by
    refine (Triple.forRange_le stepCost 0 c.m (Nat.zero_le _) (by omega)
      (fun _ => by have := c.hhdrs_w; omega) (Inv := PackUHInv c)
      (fun st ⟨hm, r0, r1, r2, r3, r4⟩ => ⟨Expr.eval_const (by omega),
        ⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4], by simp,
          by simp [BatchBodyAt], fun _ _ => hm ▸ rfl⟩⟩)
      (fun _ _ _ _ h => h.2.2.2.2.2.1)
      (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.1)
      (fun i _ hi => ?_)).conseq (fun _ h => h) (fun _ _ h => h)
      (fun _ _ => by simp [Expr.size])
    intro st ω' ⟨r0, r1, r2, r3, r4, r5, hBat, hFr⟩
    have hstep := c.hSteps ⟨i, hi⟩
    dsimp only at hstep
    obtain ⟨hh_out, huP_out, hlen_m, hW_m, hBat_i⟩ := hstep
    set h_i := c.mem0 (c.stepHdrsPtr + i)
    set uPtr_i := c.mem0 h_i
    set curLen := (((List.finRange c.m).take i).map fun r => (c.uhLists r).length).sum
    set curW := (((List.finRange c.m).take i).map c.uhWords).sum
    have hlen_next : curLen + (c.uhLists ⟨i, hi⟩).length =
        (((List.finRange c.m).take (i + 1)).map fun r => (c.uhLists r).length).sum :=
      (sum_finRange_take_succ hi fun r => (c.uhLists r).length).symm
    have hW_next : curW + c.uhWords ⟨i, hi⟩ =
        (((List.finRange c.m).take (i + 1)).map c.uhWords).sum :=
      (sum_finRange_take_succ hi c.uhWords).symm
    have hlen_le : curLen + (c.uhLists ⟨i, hi⟩).length ≤ ∑ r : Fin c.m, (c.uhLists r).length :=
      hlen_next ▸ sum_finRange_take_le fun r => (c.uhLists r).length
    have hW_le : curW + c.uhWords ⟨i, hi⟩ ≤ ∑ r : Fin c.m, c.uhWords r :=
      hW_next ▸ sum_finRange_take_le c.uhWords
    have hstep_eq : stepCost i = 30 * c.uhWords ⟨i, hi⟩ + 70 := by simp [stepCost, hi]
    dsimp only [loopBody]
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := h_i)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r5)
        (by have := c.hhdrs_w; omega))
        (hFr _ (Or.inl (by have := c.hhdrs_out; omega)))) ?_
    refine runs_seq_assign_le (v := uPtr_i)
      (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (v := h_i) (by simp))
        (hFr _ (Or.inl (by omega)))) ?_
    refine runs_seq_assign_le (v := (c.uhLists ⟨i, hi⟩).length)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := h_i) (by simp))
        (Expr.eval_const (by omega)) (by have := c.htotW_w; omega))
        ((hFr _ (Or.inl (by omega))).trans hlen_m)) ?_
    refine runs_seq_assign_le (v := c.uhWords ⟨i, hi⟩)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := h_i) (by simp))
        (Expr.eval_const (by omega)) (by have := c.htotW_w; omega))
        ((hFr _ (Or.inl (by omega))).trans hW_m)) ?_
    refine runs_seq_assign_le (v := c.uhOutPtr + 1 + curW)
      (Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (v := c.uhOutPtr) (by simp [r2]))
          (Expr.eval_const (by omega)) (by have := c.htotW_w; omega))
        (Expr.eval_reg_of_eq (v := curW) (by simp [r4]))
        (by have := c.htotW_w; omega)) ?_
    refine runs_seq_call_le (vs := [uPtr_i, c.uhOutPtr + 1 + curW, c.uhWords ⟨i, hi⟩])
      (dsCopyWords_meetsContract (w := c.w) (n := c.uhWords ⟨i, hi⟩) hpAux)
      (by simp [evalArgs, Expr.eval])
      (fun z hz => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> (have := c.htotW_w; omega))
      ⟨uPtr_i, c.uhOutPtr + 1 + curW, rfl, h16, by have := c.htotW_w; omega,
        by have := c.htotW_w; omega, by unfold IvlDisj; omega⟩ ?_
    rintro _ mem1 _ ⟨_, _, hEq, _, hcp, hfr1⟩
    simp only [List.cons.injEq, and_true] at hEq
    rcases hEq with ⟨rfl, rfl⟩
    refine runs_seq_assign_le (v := curLen + (c.uhLists ⟨i, hi⟩).length)
      (Expr.eval_add (Expr.eval_reg_of_eq (v := curLen) (by simp [r3]))
        (Expr.eval_reg_of_eq (v := (c.uhLists ⟨i, hi⟩).length) (by simp))
        (by have := c.htotLen_w; omega)) ?_
    refine runs_assign_le (v := curW + c.uhWords ⟨i, hi⟩)
      (Expr.eval_add (Expr.eval_reg_of_eq (v := curW) (by simp [r4]))
        (Expr.eval_reg_of_eq (v := c.uhWords ⟨i, hi⟩) (by simp))
        (by have := c.htotW_w; omega)) ?_ ?_
    · refine ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [hlen_next], by simp [hW_next],
        by simp, ?_, ?_⟩, by simp [r5]⟩
      · rw [flatMap_finRange_take_succ hi, ← hW_next]
        have hBat_prev : BatchBodyAt mem1 (c.uhOutPtr + 1) (c.Hs 0)
            (((List.finRange c.m).take i).flatMap c.uhLists) curW :=
          hBat.of_agree fun k hk => hfr1 _ (Or.inl (by omega))
        have hBat_cur : BatchBodyAt mem1 (c.uhOutPtr + 1 + curW) (c.Hs i)
            (c.uhLists ⟨i, hi⟩) (c.uhWords ⟨i, hi⟩) :=
          hBat_i.copy fun k hk =>
            (hcp k hk).trans (hFr _ (Or.inl (by omega)))
        rw [← applyBatch_flatMap_take c i (Nat.le_of_lt hi)] at hBat_cur
        exact batchBodyAt_append hBat_prev hBat_cur
      · intro a ha
        rw [← hW_next] at ha
        exact (hfr1 a (by omega)).trans (hFr a (by omega))
    · rw [hstep_eq]; dsimp only [dsCopyWordsContract, Expr.size, argsSize]; omega
  simp only [updateLoopProcs, updateLoopIdxPackUH, List.getElem_cons_succ, List.getElem_cons_zero]
  dsimp only [dsPackBatchUHStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop
    ⟨rfl, by simp [startState], by simp [startState], by simp [startState], by simp, by simp⟩ ?_
  rintro st1 ⟨_, _, s2, s3, s4, _, hBat1, hFr1⟩
  have hlen_all : (((List.finRange c.m).take c.m).map fun r => (c.uhLists r).length).sum =
      ((List.finRange c.m).flatMap c.uhLists).length := by
    rw [List.take_of_length_le (by simp), List.length_flatMap]
  have hW_all : (((List.finRange c.m).take c.m).map c.uhWords).sum = ∑ i : Fin c.m, c.uhWords i := by
    rw [List.take_of_length_le (by simp), sum_finRange_eq_finset_sum]
  refine runs_seq_store_le (x := c.uhOutPtr) (v := ((List.finRange c.m).flatMap c.uhLists).length)
    (Expr.eval_reg_of_eq s2) (Expr.eval_reg_of_eq (s3.trans hlen_all)) ?_
  refine runs_ret_le (v := ∑ i : Fin c.m, c.uhWords i) (Expr.eval_reg_of_eq (s4.trans hW_all)) ?_ ?_
  · refine ⟨rfl, ⟨by omega, by simp [Function.update], ?_⟩, ?_⟩
    · dsimp only [Outcome.value]
      simp only [Nat.add_sub_cancel_left]
      have hBat1' : BatchBodyAt st1.mem (c.uhOutPtr + 1) (c.Hs 0)
          ((List.finRange c.m).flatMap c.uhLists) (∑ i : Fin c.m, c.uhWords i) := by
        rw [hW_all] at hBat1
        simpa [List.take_of_length_le (show (List.finRange c.m).length ≤ c.m by simp)] using hBat1
      exact hBat1'.of_agree fun k hk => by rw [Function.update_of_ne (by omega)]
    · intro a ha
      dsimp only
      rw [Function.update_of_ne (by dsimp only [Outcome.value] at ha; omega)]
      exact hFr1 a (by dsimp only [Outcome.value] at ha; rw [hW_all]; omega)
  · have hrc : rangeCost stepCost 0 c.m = 30 * (∑ i : Fin c.m, c.uhWords i) + 70 * c.m := by
      rw [rangeCost_eq_sum_range stepCost c.m 0 c.m (by omega)]
      have h1 : (∑ r ∈ Finset.range c.m, stepCost (0 + r)) =
          ∑ r ∈ Finset.range c.m, (30 * (if hr : r < c.m then c.uhWords ⟨r, hr⟩ else 0) + 70) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        have hrm : r < c.m := Finset.mem_range.mp hr
        simp [stepCost, hrm]
      have h2 : (∑ r ∈ Finset.range c.m, if hr : r < c.m then c.uhWords ⟨r, hr⟩ else 0) =
          ∑ i : Fin c.m, c.uhWords i := by
        rw [← Fin.sum_univ_eq_sum_range (fun r => if hr : r < c.m then c.uhWords ⟨r, hr⟩ else 0)]
        refine Finset.sum_congr rfl fun i _ => by simp
      rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, h2, Finset.sum_const,
        Finset.card_range, smul_eq_mul]; ring
    dsimp only [dsPackBatchUHContract, Expr.size]
    omega

end

end MinCostFlow.DynSpanner.Program
