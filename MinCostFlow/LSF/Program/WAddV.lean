module

public import MinCostFlow.LSF.Program.WScanMath
public import MinCostFlow.LSF.Program.FAncFill

/-!
# Adding a vertex to the current group

The scan of the `W` block (`WScan.lean`) keeps a stamp array: the stamp of an index `y` is the
number of the group that last added `y`. `wAddVProc` adds the vertex of index `y` to the
current group `g` when its stamp is not `g`: it sets the stamp to `g`, writes the vertex
`vList[y]` at position `tv` of the vertex list, and returns `tv + 1`. Otherwise it returns `tv`
and changes nothing. The result is `wAddV_meetsContract`, at constant cost.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Args: `[stPtr, vListPtr, vsPtr, y, g, tv]`. -/
def wAddVProc : Stmt :=
  .assign 6 (.load (.bin .add (.reg 1) (.reg 3))) ;;
  .assign 7 (.reg 5) ;;
  .cond (.bin .eq (.load (.bin .add (.reg 0) (.reg 3))) (.reg 4)) .nop
    (.store (.bin .add (.reg 0) (.reg 3)) (.reg 4) ;;
     .store (.bin .add (.reg 2) (.reg 5)) (.reg 6) ;;
     .assign 7 (.bin .add (.reg 5) (.const 1))) ;;
  .ret (.reg 7)

lemma wAddVProc_noRand : wAddVProc.NoRand := by
  simp [wAddVProc, Stmt.NoRand]

/-- The memory after adding `y`. -/
def wAddVMem (mem : ℕ → ℕ) (stPtr vListPtr vsPtr y g tv : ℕ) : ℕ → ℕ :=
  if mem (stPtr + y) = g then mem
  else Function.update (Function.update mem (stPtr + y) g) (vsPtr + tv) (mem (vListPtr + y))

/-- The contract of `wAddVProc`. -/
def wAddVContract (w : ℕ) : Contract where
  pre args _ := ∃ (stPtr vListPtr vsPtr y g tv : ℕ),
    args = [stPtr, vListPtr, vsPtr, y, g, tv] ∧ 2 < 2 ^ w ∧
    stPtr + y < 2 ^ w ∧ vListPtr + y < 2 ^ w ∧ vsPtr + tv < 2 ^ w ∧ tv + 1 < 2 ^ w
  post args mem ret mem' := ∃ (stPtr vListPtr vsPtr y g tv : ℕ),
    args = [stPtr, vListPtr, vsPtr, y, g, tv] ∧
    ret = (if mem (stPtr + y) = g then tv else tv + 1) ∧
    mem' = wAddVMem mem stPtr vListPtr vsPtr y g tv
  cost _ _ := 40

theorem wAddV_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some wAddVProc) :
    MeetsContract w p b (wAddVContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨stPtr, vListPtr, vsPtr, y, g, tv, rfl, hw2, hsy, hvy, hvs, htv⟩ := hpre
  set args := [stPtr, vListPtr, vsPtr, y, g, tv] with hargs
  have hst : ∀ i < 6, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have r0 := hst 0 (by omega)
  have r1 := hst 1 (by omega)
  have r2 := hst 2 (by omega)
  have r3 := hst 3 (by omega)
  have r4 := hst 4 (by omega)
  have r5 := hst 5 (by omega)
  simp only [hargs, List.getD_cons_zero, List.getD_cons_succ] at r0 r1 r2 r3 r4 r5
  have hgw : g < 2 ^ w := hwords g (by simp [hargs])
  have htw : tv < 2 ^ w := hwords tv (by simp [hargs])
  have hm0 : (startState args mem pos).mem = mem := rfl
  obtain ⟨v, hv⟩ : ∃ v, mem (vListPtr + y) = v := ⟨_, rfl⟩
  refine runs_start_le ?_
  unfold wAddVProc
  refine runs_seq_assign_le (v := v) (by rw [← hv]; eval_expr) ?_
  refine runs_seq_assign_le (v := tv) (by eval_expr) ?_
  refine runs_seq_cond_le (v := if mem (stPtr + y) = g then 1 else 0) (by eval_expr)
    (fun hb => ?_) (fun hb => ?_)
  · have hs : mem (stPtr + y) = g := by by_contra hc; simp [hc] at hb
    refine runs_seq_nop_le ?_
    refine runs_ret_le (v := tv) (by eval_expr)
      ⟨stPtr, vListPtr, vsPtr, y, g, tv, rfl, by simp [hs, Outcome.value],
        by simp [wAddVMem, hs, startState]⟩ ?_
    simp only [wAddVContract, Expr.size_reg, Expr.size_bin, Expr.size_load, Expr.size_const]
    omega
  · have hs : mem (stPtr + y) ≠ g := by intro hc; simp [hc] at hb
    refine runs_seq_assoc_le ?_
    refine runs_seq_store_le (x := stPtr + y) (v := g) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_assoc_le ?_
    refine runs_seq_store_le (x := vsPtr + tv) (v := v) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_assign_le (v := tv + 1) (by eval_expr) ?_
    refine runs_ret_le (v := tv + 1) (by eval_expr)
      ⟨stPtr, vListPtr, vsPtr, y, g, tv, rfl, by simp [hs, Outcome.value],
        by simp [wAddVMem, hs, hv, startState]⟩ ?_
    simp only [wAddVContract, Expr.size_reg, Expr.size_bin, Expr.size_load, Expr.size_const]
    omega

end

end MinCostFlow.LSF.Program
