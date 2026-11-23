module

public import MinCostFlow.HierPaths.BuildTopPlayerWords

/-!
# Writing a row of the player table

The terminal table and the six player parameters are passed in registers.
Their word encodings are copied into seven consecutive cells for the schedule pass.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Arguments are the row address, terminal table, scale, rank, degree, two
logarithmic parameters, and denominator. -/
def buildTopPlayerTableRow : Stmt :=
  .store (.bin .add (.reg 0) (.const 0)) (.reg 1) ;;
  .store (.bin .add (.reg 0) (.const 1)) (.reg 2) ;;
  .store (.bin .add (.reg 0) (.const 2)) (.reg 3) ;;
  .store (.bin .add (.reg 0) (.const 3)) (.reg 4) ;;
  .store (.bin .add (.reg 0) (.const 4)) (.reg 5) ;;
  .store (.bin .add (.reg 0) (.const 5)) (.reg 6) ;;
  .store (.bin .add (.reg 0) (.const 6)) (.reg 7) ;;
  .ret (.reg 0)

theorem buildTopPlayerTableRow_noRand : buildTopPlayerTableRow.NoRand := by
  simp [buildTopPlayerTableRow, Stmt.NoRand]

/-- The player writer writes the terminal pointer and six parameter words. -/
theorem buildTopPlayerTableRow_meetsContract {w f row : ℕ} {p : Program} {D : BuildTopDepthInput}
    (hf : p.procs[f]? = some buildTopPlayerTableRow) :
    MeetsContract w p f {
      pre := fun args _ => args = [row,D.termBase,D.scale,D.rank,D.degree,D.pathLog,
        D.coreLog,D.denominator] ∧ row + 6 < 2 ^ w
      post := fun _ mem v mem' => v = row ∧ ListAt mem' row D.playerWords ∧
        ∀ y, y < row ∨ row + 7 ≤ y → mem' y = mem y
      cost := fun _ _ => 50 } := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hpre => ?_
  obtain ⟨rfl, h⟩ := hpre
  refine runs_start_le ?_
  unfold buildTopPlayerTableRow
  refine runs_seq_store_le (x := row + 0)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := D.termBase) rfl) ?_
  refine runs_seq_store_le (x := row + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := D.scale) rfl) ?_
  refine runs_seq_store_le (x := row + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := D.rank) rfl) ?_
  refine runs_seq_store_le (x := row + 3)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := D.degree) rfl) ?_
  refine runs_seq_store_le (x := row + 4)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := D.pathLog) rfl) ?_
  refine runs_seq_store_le (x := row + 5)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := D.coreLog) rfl) ?_
  refine runs_seq_store_le (x := row + 6)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) h)
    (Expr.eval_reg_of_eq (v := D.denominator) rfl) ?_
  refine runs_ret_le (v := row) (Expr.eval_reg_of_eq rfl) ⟨rfl,?_,?_⟩ ?_
  · intro k hk
    have hk' : k < 7 := by simpa [BuildTopDepthInput.playerWords] using hk
    interval_cases k <;> simp [BuildTopDepthInput.playerWords, startState, Function.update_of_ne]
  · intro y hy
    dsimp only
    repeat rw [Function.update_of_ne (by omega)]
    rfl
  · simp [Expr.size]

end MinCostFlow.HierPaths

end
