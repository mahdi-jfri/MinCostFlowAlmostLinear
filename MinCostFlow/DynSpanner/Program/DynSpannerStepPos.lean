module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosCtx
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNonEmpty
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosEmpty
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosEpilogue

/-!
# The step of Algorithm 6 for `0 < j`: the contract theorem

Proves `dsStepPos_meetsContract`: `dsStepPosStmt` (`DynSpannerStepPosDefs.lean`) runs the branch
that fits `E_aff` and then the epilogue, ends in the post `StepOutPost` of a step, and runs
within `dsStepPosCost`.

The proof has three parts. `stepPos_epilogue_run` runs the epilogue and the return, from any
memory where a branch has ended in `StepPosMidPost`. The main theorem runs the branch, using
`dsStepPosNonEmpty_meetsContract` on `StepPosCtx.toNE` when `eAff` is not empty and
`dsStepPosEmpty_meetsContract` on `StepPosCtx.toEmpty` when it is, and then calls the first part.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

public section

/-- The procedures of the empty branch are among those of `dsStepPosStmt`. -/
lemma HasStepPosProcs.toEmpty {impl : SparsifyImpl} {p : Program} {bs : StepPosNEBases}
    {bEm bEp bPos : ℕ} (hp : HasStepPosProcs impl p bs bEm bEp bPos) :
    HasStepPosEmptyProcs p bs bEm :=
  ⟨hp.hNE.hpOps, hp.hNE.hpEdge, hp.hNE.hpSplit, hp.hNE.hpBatch, hp.hNE.hpDR, hp.hNE.hpDA,
    hp.hNE.hpIR, hp.hNE.hpUT, hp.hNE.hpAU, hp.hNE.hpUE, hp.hNE.hpCB, hp.hNE.hpPhase,
    hp.hNE.hpFL, hp.hNE.hpRB, hp.hNE.hpSE, hp.hNE.hpZ, hp.hNE.hpClrA, hp.hNE.hpST,
    hp.hNE.hpRev, hp.hNE.hpLW, hp.hNE.hpFin, hp.hEm⟩

private lemma stepPos_cost_start {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {T : ℕ} {Post : Outcome → State → Prop}
    (h : ∃ o st' c, Runs w p ω s st o st' c ∧ Post o st' ∧ 0 + c ≤ T) :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Post o st' ∧ c ≤ T := by
  simpa using h

/-- The epilogue and the return of `dsStepPosStmt`, from a memory `mem1` where a branch has
ended in `StepPosMidPost` with next free word `ret1`, held in register `20`. -/
lemma stepPos_epilogue_run (ctx : StepPosCtx) {p : Program} {bs : StepPosNEBases}
    {bEm bEp bPos : ℕ} (hp : HasStepPosProcs ctx.impl p bs bEm bEp bPos) {ω : ℕ → Bool}
    {regs mem1 : ℕ → ℕ} {pos1 ret1 k T : ℕ} {A : List ℕ} {M : ℕ → ℕ}
    (hMid : StepPosMidPost ctx.G₀ ctx.L ctx.q ctx.vCap ctx.eCap ctx.b ctx.k ctx.impl ctx.us ctx.u
      ctx.mem0 ctx.mem2 ctx.x ctx.headHeap ctx.r₁ ctx.heapStep ctx.heapAff ctx.sPrevList
      ctx.prefWords mem1 ret1)
    (hNext : ret1 ≤ ctx.midEnd)
    (hAffAt : ListAt mem1 ctx.eAffPtr ctx.eAff)
    (hAffLe : ctx.eAffPtr + ctx.eAff.length ≤ ret1)
    (hr0 : regs 0 = ctx.b) (hr1 : regs 1 = ctx.j) (hr6 : regs 6 = ctx.heapStep)
    (hr7 : regs 7 = ctx.prefWords) (hr8 : regs 8 = ctx.heapAff)
    (hr9 : regs 9 = ctx.sPrevList.length) (hr20 : regs 20 = ret1)
    (hW : ctx.b < 2 ^ ctx.w ∧ ctx.j < 2 ^ ctx.w ∧ ctx.prefWords < 2 ^ ctx.w ∧
      ctx.heapStep < 2 ^ ctx.w ∧ ctx.heapAff < 2 ^ ctx.w ∧ ctx.sPrevList.length < 2 ^ ctx.w)
    (hk : k + dsStepPosEpilogueCost ctx.sPrevList.length ctx.J.m ctx.J.n ctx.prefWords
      ctx.res.UH.length + 20 ≤ T) :
    ∃ o st' c, Runs ctx.w p ω
      (.call 21 (bEp + stepPosEpilogueIdx)
        [.reg 0, .reg 1, .reg 7, .reg 6, .reg 8, .reg 9, .reg 20] ;; .ret (.reg 21))
      { mem := mem1, regs := regs, pos := pos1 } o st' c ∧
      (dsStepPosContract ctx).post A M o.value st'.mem ∧ k + c ≤ T := by
  have hEnd := ctx.hEnd_ep hNext
  have hret1 : ret1 < 2 ^ ctx.w := by omega
  refine runs_seq_call_le
    (vs := [ctx.b, ctx.j, ctx.prefWords, ctx.heapStep, ctx.heapAff, ctx.sPrevList.length, ret1])
    (dsStepPosEpilogue_meetsContract (ctx.toEp mem1 ret1 hMid hNext) hp.hNE.hpAux
      hp.hNE.hpPhase hp.hNE.hpEdge hp.hNE.hpOps hp.hEp)
    (evalArgs_cons (Expr.eval_reg_of_eq hr0) <| evalArgs_cons (Expr.eval_reg_of_eq hr1) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr7) <| evalArgs_cons (Expr.eval_reg_of_eq hr6) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr8) <| evalArgs_cons (Expr.eval_reg_of_eq hr9) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr20) <| evalArgs_nil _ _)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hW.1
      · exact hW.2.1
      · exact hW.2.2.1
      · exact hW.2.2.2.1
      · exact hW.2.2.2.2.1
      · exact hW.2.2.2.2.2
      · exact hret1)
    ⟨rfl, rfl⟩ ?_
  rintro ret2 mem2' pos2 ⟨hOut, hret2, hgen2, huh2, hFheap, hret1_le⟩
  have hAffAt2 : ListAt mem2' ctx.eAffPtr ctx.eAff :=
    listAt_of_agree (fun i hi =>
      hFheap (ctx.eAffPtr + i)
        (by have := ctx.hhead_in; dsimp only [StepPosCtx.toEp, StepPosCtx.eAffPtr]; omega)
        (lt_of_lt_of_le (Nat.add_lt_add_left hi _) hAffLe))
      hAffAt
  refine runs_ret_le (v := ret2) (Expr.eval_reg_of_eq (by simp))
    ⟨hOut, ?_, hgen2, huh2, hAffAt2, le_trans hAffLe hret1_le⟩ ?_
  · have h2 : ret2 ≤ ret1 + ctx.prefWords + 4 * ctx.res.UH.length := hret2
    show ret2 ≤ _
    omega
  · have hc : (dsStepPosEpilogueContract (ctx.toEp mem1 ret1 hMid hNext)).cost
        [ctx.b, ctx.j, ctx.prefWords, ctx.heapStep, ctx.heapAff, ctx.sPrevList.length, ret1]
        mem1 =
        dsStepPosEpilogueCost ctx.sPrevList.length ctx.J.m ctx.J.n ctx.prefWords
          ctx.res.UH.length := rfl
    rw [hc]
    simp only [Expr.size_reg, argsSize_cons, argsSize_nil]
    omega

/-- `dsStepPosStmt` meets `dsStepPosContract`: from the memory after `dsAffStage`, one step of
Algorithm 6 with `0 < j` (Theorem 8.2, page 64) ends in `StepOutPost` within `dsStepPosCost`. -/
theorem dsStepPos_meetsContract (ctx : StepPosCtx) {p : Program} {bs : StepPosNEBases}
    {bEm bEp bPos : ℕ} (hp : HasStepPosProcs ctx.impl p bs bEm bEp bPos) :
    MeetsContract ctx.w p (bPos + stepPosIdx) (dsStepPosContract ctx) := by
  refine meetsContract_of_runs
    (hp.hPos.get (i := stepPosIdx) (by simp [stepPosProcs, stepPosIdx])) ?_
  rintro args mem pos ω hW ⟨rfl, rfl⟩
  simp only [stepPosProcs, stepPosIdx, List.getElem_cons_zero]
  dsimp only [dsStepPosStmt]
  have hw : ∀ i (hi : i < 10), [ctx.b, ctx.j, ctx.eAffPtr, ctx.eAff.length, ctx.cand.length,
      ctx.oldBucketsSum, ctx.heapStep, ctx.prefWords, ctx.heapAff, ctx.sPrevList.length][i] <
      2 ^ ctx.w := fun i hi => hW _ (List.getElem_mem _)
  have hWep : ctx.b < 2 ^ ctx.w ∧ ctx.j < 2 ^ ctx.w ∧ ctx.prefWords < 2 ^ ctx.w ∧
      ctx.heapStep < 2 ^ ctx.w ∧ ctx.heapAff < 2 ^ ctx.w ∧ ctx.sPrevList.length < 2 ^ ctx.w :=
    ⟨hw 0 (by decide), hw 1 (by decide), hw 7 (by decide), hw 6 (by decide), hw 8 (by decide),
      hw 9 (by decide)⟩
  refine stepPos_cost_start ?_
  refine runs_seq_cond_le (v := ctx.eAff.length) (Expr.eval_reg_of_eq (by simp [startState]))
    ?_ ?_
  · -- The nonempty branch.
    intro hne
    have hpos : 0 < ctx.eAff.length := Nat.pos_of_ne_zero hne
    have hwp : ctx.wpPtr < 2 ^ ctx.w :=
      lt_of_le_of_lt (Nat.le_add_right _ _) (stepPosNE_word_bounds (ctx.toNE hpos)).2.2.1
    refine runs_seq_call_le
      (vs := [ctx.b, ctx.j, ctx.eAffPtr, ctx.eAff.length, ctx.wpPtr, ctx.cand.length,
        ctx.oldBucketsSum, ctx.heapStep])
      (dsStepPosNonEmpty_meetsContract (ctx.toNE hpos) hp.hNE)
      (evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
        evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
          (Expr.eval_reg_of_eq (by simp [startState])) hwp) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <| evalArgs_nil _ _)
      (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hw 0 (by decide)
        · exact hw 1 (by decide)
        · exact hw 2 (by decide)
        · exact hw 3 (by decide)
        · exact hwp
        · exact hw 4 (by decide)
        · exact hw 5 (by decide)
        · exact hw 6 (by decide))
      ⟨rfl, rfl⟩ ?_
    rintro ret1 mem1 pos1 ⟨hMid, hret1, hAffAt, hAffLe⟩
    have hNext : ret1 ≤ ctx.midEnd := by
      simp only [StepPosCtx.midEnd, hpos, ↓reduceIte]
      exact hret1
    refine stepPos_epilogue_run ctx hp hMid hNext hAffAt hAffLe (by simp [startState]) (by simp [startState])
      (by simp [startState]) (by simp [startState]) (by simp [startState])
      (by simp [startState]) (by simp) hWep ?_
    have hc : (dsStepPosNonEmptyContract (ctx.toNE hpos)).cost
        [ctx.b, ctx.j, ctx.eAffPtr, ctx.eAff.length, ctx.wpPtr, ctx.cand.length,
          ctx.oldBucketsSum, ctx.heapStep] ctx.memAff =
        dsStepPosNonEmptyCost ctx.impl ctx.mMax ctx.L ctx.vCap ctx.eCap ctx.j ctx.G' ctx.J
          ctx.piLt_mid ctx.embJH ctx.S_prev ctx.eAff ctx.oldBucketsSum := rfl
    rw [show (startState _ ctx.memAff pos).mem = ctx.memAff from rfl, hc]
    simp only [dsStepPosContract, dsStepPosCost, hpos, ↓reduceIte, Expr.size_reg, Expr.size_bin,
      argsSize_cons, argsSize_nil]
    omega
  · -- The empty branch.
    intro h0
    have hnil : ctx.eAff = [] := List.eq_nil_of_length_eq_zero h0
    have hn : ¬ 0 < ctx.eAff.length := by omega
    have hEm := ctx.hEnd_em hnil
    have hret : ctx.retAffE < 2 ^ ctx.w := by omega
    refine runs_seq_call_le
      (vs := [ctx.b, ctx.j, ctx.eAffPtr, ctx.retAffE, ctx.oldBucketsSum, ctx.heapStep])
      (dsStepPosEmpty_meetsContract (ctx.toEmpty hnil) hp.toEmpty)
      (evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
        evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
          (Expr.eval_reg_of_eq (by simp [startState])) hret) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState])) <| evalArgs_nil _ _)
      (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hw 0 (by decide)
        · exact hw 1 (by decide)
        · exact hw 2 (by decide)
        · exact hret
        · exact hw 5 (by decide)
        · exact hw 6 (by decide))
      ⟨rfl, rfl⟩ ?_
    rintro ret1 mem1 pos1 ⟨hMid, hret1⟩
    have hNext : ret1 ≤ ctx.midEnd := by
      simp only [StepPosCtx.midEnd, hn, ↓reduceIte]
      exact le_of_eq hret1
    refine stepPos_epilogue_run ctx hp hMid hNext
      (by rw [hnil]; intro i hi; exact absurd hi (Nat.not_lt_zero _))
      (by rw [hnil, List.length_nil, Nat.add_zero, hret1]; show ctx.eAffPtr ≤ _; dsimp only [StepPosCtx.toEmpty, StepPosEmptyCtx.dPtr, StepPosEmptyCtx.uhTailHdr, StepPosCtx.retAffE]; omega)
      (by simp [startState]) (by simp [startState])
      (by simp [startState]) (by simp [startState]) (by simp [startState])
      (by simp [startState]) (by simp) hWep ?_
    have hc : (dsStepPosEmptyContract (ctx.toEmpty hnil)).cost
        [ctx.b, ctx.j, ctx.eAffPtr, ctx.retAffE, ctx.oldBucketsSum, ctx.heapStep] ctx.memAff =
        dsStepPosEmptyCost ctx.L ctx.j ctx.oldBucketsSum := rfl
    rw [show (startState _ ctx.memAff pos).mem = ctx.memAff from rfl, hc]
    simp only [dsStepPosContract, dsStepPosCost, hn, ↓reduceIte, Expr.size_reg, Expr.size_bin,
      argsSize_cons, argsSize_nil]
    omega

end

end MinCostFlow.DynSpanner.Program
