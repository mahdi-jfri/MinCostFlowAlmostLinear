module

public import MinCostFlow.HierPaths.BuildTopScheduleGeometry
public import WordRAM.Logic

/-! # Writing the geometric fields of a depth row -/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Write the child size, branching factor, and parent count in consecutive cells. -/
def buildTopScheduleGeometry : Stmt :=
  .store (.reg 3) (queryGroupSizeExpr (.reg 0) (.reg 1) (.bin .add (.reg 2) (.const 1))) ;;
  .store (.bin .add (.reg 3) (.const 1)) (buildTopBranchingExpr (.reg 0) (.reg 1) (.reg 2)) ;;
  .store (.bin .add (.reg 3) (.const 2)) (buildTopCountExpr (.reg 0) (.reg 1) (.reg 2)) ;;
  .ret (.reg 3)

theorem buildTopScheduleGeometry_noRand : buildTopScheduleGeometry.NoRand := by
  simp [buildTopScheduleGeometry, Stmt.NoRand]

/-- The geometry writer updates exactly three cells in constant time. -/
theorem buildTopScheduleGeometry_meetsContract {w f x b j dst : ℕ} {p : Program}
    (hf : p.procs[f]? = some buildTopScheduleGeometry) :
    MeetsContract w p f {
      pre := fun args _ => args = [x,b,j,dst] ∧ 2 ^ x < 2 ^ w ∧
        j + 1 < 2 ^ w ∧ (j + 1) * b < 2 ^ w ∧ dst + 2 < 2 ^ w
      post := fun _ mem v mem' => v = dst ∧
        mem' = Function.update (Function.update (Function.update mem dst
          (groupSize x b (j + 1))) (dst + 1) (branching x b j)) (dst + 2) (numGroups x b j)
      cost := fun _ _ => 100 } := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hpre => ?_
  obtain ⟨rfl, hw, hj, hm, hd⟩ := hpre
  have h1 : 1 < 2 ^ w := lt_of_le_of_lt (Nat.two_pow_pos x) hw
  have hnow := (Nat.mul_le_mul_right b (Nat.le_succ j)).trans_lt hm
  refine runs_start_le ?_
  unfold buildTopScheduleGeometry
  refine runs_seq_store_le (x := dst) (Expr.eval_reg_of_eq rfl)
    (eval_queryGroupSizeExpr (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl)
      (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const h1) hj) hw hm) ?_
  refine runs_seq_store_le (x := dst + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const h1) (by omega))
    (eval_buildTopBranchingExpr (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl)
      (Expr.eval_reg_of_eq rfl) hw hj hm) ?_
  refine runs_seq_store_le (x := dst + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) hd)
    (eval_buildTopCountExpr (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl)
      (Expr.eval_reg_of_eq rfl) hw hnow) ?_
  refine runs_ret_le (v := dst) (Expr.eval_reg_of_eq rfl) ⟨rfl, rfl⟩ ?_
  simp [Expr.size, queryGroupSizeExpr, buildTopBranchingExpr, buildTopCountExpr]

end MinCostFlow.HierPaths

end
