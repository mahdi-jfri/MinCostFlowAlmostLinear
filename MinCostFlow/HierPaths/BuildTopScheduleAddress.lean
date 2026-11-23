module

public import MinCostFlow.HierPaths.BuildTopScheduleLayout

/-!
# Computing schedule addresses

The padded terminal count is the stride of the reply directories.
Boundary pointers occupy consecutive cells immediately after the rows.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

def buildTopPointerExpr (table n j : Expr) : Expr :=
  .bin .add (.bin .add table (.bin .mul (.const 13) n)) j

def buildTopRepliesExpr (table n x j : Expr) : Expr :=
  .bin .add (buildTopPointerExpr table n (.bin .add n (.const 1)))
    (.bin .mul j (.bin .shiftLeft (.const 1) x))

/-- The pointer address and its intermediate sums fit if the address fits. -/
theorem eval_buildTopPointerExpr {w table n j : ℕ} {s : State} {te ne je : Expr}
    (ht : te.eval w s = some table) (hn : ne.eval w s = some n)
    (hj : je.eval w s = some j) (h13 : 13 < 2 ^ w)
    (hw : buildTopSchedulePointer table n j < 2 ^ w) :
    (buildTopPointerExpr te ne je).eval w s = some (buildTopSchedulePointer table n j) := by
  unfold buildTopSchedulePointer at hw
  exact Expr.eval_add
    (Expr.eval_add ht (Expr.eval_mul (Expr.eval_const h13) hn (by omega)) (by omega)) hj hw

/-- A row can compute its reply-directory address using the same stride as the model. -/
theorem eval_buildTopRepliesExpr {w table n x j : ℕ} {s : State} {te ne xe je : Expr}
    (ht : te.eval w s = some table) (hn : ne.eval w s = some n)
    (hx : xe.eval w s = some x) (hj : je.eval w s = some j)
    (h13 : 13 < 2 ^ w) (hP : 2 ^ x < 2 ^ w)
    (hw : buildTopScheduleReplies table n x j < 2 ^ w) :
    (buildTopRepliesExpr te ne xe je).eval w s = some (buildTopScheduleReplies table n x j) := by
  have h1 : 1 < 2 ^ w := by omega
  have hshift : (.bin .shiftLeft (.const 1) xe : Expr).eval w s = some (2 ^ x) := by
    simpa [Nat.shiftLeft_eq] using Expr.eval_shiftLeft (Expr.eval_const h1) hx
      (by simpa [Nat.shiftLeft_eq] using hP)
  unfold buildTopScheduleReplies buildTopSchedulePointer at hw
  exact Expr.eval_add (eval_buildTopPointerExpr ht hn
    (Expr.eval_add hn (Expr.eval_const h1) (by omega)) h13
    (by unfold buildTopSchedulePointer; omega))
    (Expr.eval_mul hj hshift (by omega)) hw

/-- Fill the input pointer, reply directory, and output pointer columns of a row. -/
def buildTopScheduleAddresses : Stmt :=
  .store (.reg 4) (buildTopPointerExpr (.reg 0) (.reg 1) (.reg 3)) ;;
  .store (.bin .add (.reg 4) (.const 1)) (buildTopRepliesExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)) ;;
  .store (.bin .add (.reg 4) (.const 12))
    (buildTopPointerExpr (.reg 0) (.reg 1) (.bin .add (.reg 3) (.const 1))) ;;
  .ret (.reg 4)

theorem buildTopScheduleAddresses_noRand : buildTopScheduleAddresses.NoRand := by
  simp [buildTopScheduleAddresses, Stmt.NoRand]

/-- The address writer changes only the three pointer columns and uses constant time. -/
theorem buildTopScheduleAddresses_meetsContract {w f table n x j : ℕ} {p : Program}
    (hf : p.procs[f]? = some buildTopScheduleAddresses) :
    MeetsContract w p f {
      pre := fun args _ => args = [table,n,x,j,table + 13 * j] ∧ j < n ∧
        2 ^ x < 2 ^ w ∧ buildTopScheduleEnd table n x < 2 ^ w
      post := fun _ mem v mem' =>
        let row := table + 13 * j
        v = row ∧ mem' = Function.update
          (Function.update (Function.update mem row (buildTopSchedulePointer table n j))
            (row + 1) (buildTopScheduleReplies table n x j))
          (row + 12) (buildTopSchedulePointer table n (j + 1))
      cost := fun _ _ => 100 } := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hpre => ?_
  obtain ⟨rfl,hj,hP,hend⟩ := hpre
  obtain ⟨hrow,hnext,hrep,hspan⟩ :=
    buildTopSchedule_disjoint (table := table) (x := x) (b := 0) hj
  have hre : buildTopScheduleReplies table n x j < 2 ^ w :=
    (Nat.le_add_right _ _).trans_lt (hspan.trans_lt hend)
  have hnxt : buildTopSchedulePointer table n (j + 1) < 2 ^ w := hrep.trans hre
  have hptr : buildTopSchedulePointer table n j < 2 ^ w := by omega
  have h13 : 13 < 2 ^ w := by omega
  have hj' : j + 1 < 2 ^ w := by
    unfold buildTopSchedulePointer at hnxt
    omega
  refine runs_start_le ?_
  unfold buildTopScheduleAddresses
  refine runs_seq_store_le (x := table + 13 * j) (Expr.eval_reg_of_eq rfl)
    (eval_buildTopPointerExpr (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl)
      (Expr.eval_reg_of_eq rfl) h13 hptr) ?_
  refine runs_seq_store_le (x := table + 13 * j + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
    (eval_buildTopRepliesExpr (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl)
      (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) h13 hP hre) ?_
  refine runs_seq_store_le (x := table + 13 * j + 12)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
    (eval_buildTopPointerExpr (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl)
      (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) hj') h13 hnxt) ?_
  refine runs_ret_le (v := table + 13 * j) (Expr.eval_reg_of_eq rfl) ⟨rfl,rfl⟩ ?_
  simp [Expr.size, buildTopPointerExpr, buildTopRepliesExpr]

/-- Adding the address columns completes a row after the other columns were filled. -/
theorem buildTopScheduleAddress_completesRow {mem : ℕ → ℕ} {table n x j : ℕ}
    {D : BuildTopDepthInput} (hd : D.replyDir = buildTopScheduleReplies table n x j)
    (hdata : ∀ k (hk : k < (D.scheduleWords (buildTopSchedulePointer table n j)
        (buildTopSchedulePointer table n (j + 1))).length), 2 ≤ k → k < 12 →
      mem (table + 13 * j + k) =
        (D.scheduleWords (buildTopSchedulePointer table n j)
          (buildTopSchedulePointer table n (j + 1)))[k]'hk) :
    let row := table + 13 * j
    let initial := buildTopSchedulePointer table n j
    let next := buildTopSchedulePointer table n (j + 1)
    let mem' := Function.update
      (Function.update (Function.update mem row initial)
        (row + 1) (buildTopScheduleReplies table n x j)) (row + 12) next
    ListAt mem' row (D.scheduleWords initial next) := by
  dsimp only
  intro k hk
  have hcol : k < 13 := by simpa [BuildTopDepthInput.scheduleWords] using hk
  by_cases h2 : 2 ≤ k ∧ k < 12
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hdata k hk h2.1 h2.2
  · have h : k = 0 ∨ k = 1 ∨ k = 12 := by omega
    rcases h with rfl | rfl | rfl <;> simp [BuildTopDepthInput.scheduleWords, hd, Function.update_of_ne]

end MinCostFlow.HierPaths

end
