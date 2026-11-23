module

public import MinCostFlow.HierPaths.BuildTopScheduleAddress

/-!
# Recording the player parameters in a schedule row

The terminal table and the six player parameters are passed in registers.
Their word encodings are copied into the columns used by the depth driver.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Arguments are the row address, terminal table, scale, rank, degree, two
logarithmic parameters, and denominator. -/
def buildTopSchedulePlayers : Stmt :=
  .store (.bin .add (.reg 0) (.const 2)) (.reg 1) ;;
  .store (.bin .add (.reg 0) (.const 6)) (.reg 2) ;;
  .store (.bin .add (.reg 0) (.const 7)) (.reg 3) ;;
  .store (.bin .add (.reg 0) (.const 8)) (.reg 4) ;;
  .store (.bin .add (.reg 0) (.const 9)) (.reg 5) ;;
  .store (.bin .add (.reg 0) (.const 10)) (.reg 6) ;;
  .store (.bin .add (.reg 0) (.const 11)) (.reg 7) ;;
  .ret (.reg 0)

theorem buildTopSchedulePlayers_noRand : buildTopSchedulePlayers.NoRand := by
  simp [buildTopSchedulePlayers, Stmt.NoRand]

/-- The player writer updates the terminal pointer and six parameter columns. -/
theorem buildTopSchedulePlayers_meetsContract {w f row : ℕ} {p : Program} {D : BuildTopDepthInput}
    (hf : p.procs[f]? = some buildTopSchedulePlayers) :
    MeetsContract w p f {
      pre := fun args _ => args = [row,D.termBase,D.scale,D.rank,D.degree,D.pathLog,
        D.coreLog,D.denominator] ∧ row + 11 < 2 ^ w
      post := fun _ mem v mem' => v = row ∧
        mem' = Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update mem (row + 2) D.termBase)
            (row + 6) D.scale) (row + 7) D.rank) (row + 8) D.degree)
          (row + 9) D.pathLog) (row + 10) D.coreLog) (row + 11) D.denominator
      cost := fun _ _ => 50 } := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hpre => ?_
  obtain ⟨rfl, h⟩ := hpre
  refine runs_start_le ?_
  unfold buildTopSchedulePlayers
  refine runs_seq_store_le (x := row + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := D.termBase) rfl) ?_
  refine runs_seq_store_le (x := row + 6)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := D.scale) rfl) ?_
  refine runs_seq_store_le (x := row + 7)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := D.rank) rfl) ?_
  refine runs_seq_store_le (x := row + 8)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := D.degree) rfl) ?_
  refine runs_seq_store_le (x := row + 9)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := D.pathLog) rfl) ?_
  refine runs_seq_store_le (x := row + 10)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := D.coreLog) rfl) ?_
  refine runs_seq_store_le (x := row + 11)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) h)
    (Expr.eval_reg_of_eq (v := D.denominator) rfl) ?_
  refine runs_ret_le (v := row) (Expr.eval_reg_of_eq rfl) ⟨rfl,rfl⟩ ?_
  simp [Expr.size]

end MinCostFlow.HierPaths

end
