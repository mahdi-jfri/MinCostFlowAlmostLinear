module

public import MinCostFlow.HierPaths.QueryProgGroupSize

/-!
# Word expressions for the depth schedule

Compute the three geometric inputs of a depth advance from the padded
root exponent, the branching exponent, and the loop index.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The parent count is the total terminal count divided by the parent size. -/
def buildTopCountExpr (x b j : Expr) : Expr :=
  .bin .div (.bin .shiftLeft (.const 1) x) (queryGroupSizeExpr x b j)

/-- The size ratio gives the number of children even at the last split. -/
def buildTopBranchingExpr (x b j : Expr) : Expr :=
  .bin .div (queryGroupSizeExpr x b j)
    (queryGroupSizeExpr x b (.bin .add j (.const 1)))

/-- Evaluate the schedule's parent-count expression. -/
theorem eval_buildTopCountExpr {w x b j : ℕ} {t : State} {xe be je : Expr}
    (hx : xe.eval w t = some x) (hb : be.eval w t = some b) (hj : je.eval w t = some j)
    (hw : 2 ^ x < 2 ^ w) (hm : j * b < 2 ^ w) :
    (buildTopCountExpr xe be je).eval w t = some (numGroups x b j) := by
  have h1 : 1 < 2 ^ w := lt_of_le_of_lt (Nat.two_pow_pos x) hw
  have hs : 1 <<< x < 2 ^ w := by simpa [Nat.shiftLeft_eq] using hw
  have htotal : (.bin .shiftLeft (.const 1) xe : Expr).eval w t = some (2 ^ x) := by
    simpa [Nat.shiftLeft_eq] using Expr.eval_shiftLeft (Expr.eval_const h1) hx hs
  have he : 2 ^ x / groupSize x b j = numGroups x b j := by
    rw [← numGroups_mul_groupSize (b := b) (j := j)]
    exact Nat.mul_div_cancel _ groupSize_pos
  rw [← he]
  exact Expr.eval_div htotal (eval_queryGroupSizeExpr hx hb hj hw hm) hw

/-- Evaluate the schedule's branching expression at a depth above the leaves. -/
theorem eval_buildTopBranchingExpr {w x b j : ℕ} {t : State} {xe be je : Expr}
    (hx : xe.eval w t = some x) (hb : be.eval w t = some b) (hj : je.eval w t = some j)
    (hw : 2 ^ x < 2 ^ w) (hnext : j + 1 < 2 ^ w)
    (hm : (j + 1) * b < 2 ^ w) :
    (buildTopBranchingExpr xe be je).eval w t = some (branching x b j) := by
  have h1 : 1 < 2 ^ w := lt_of_le_of_lt (Nat.two_pow_pos x) hw
  have hnow := (Nat.mul_le_mul_right b (Nat.le_succ j)).trans_lt hm
  have hsize : groupSize x b j < 2 ^ w := by
    unfold groupSize
    exact (Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)).trans_lt hw
  exact Expr.eval_div (eval_queryGroupSizeExpr hx hb hj hw hnow)
    (eval_queryGroupSizeExpr hx hb (Expr.eval_add hj (Expr.eval_const h1) hnext) hw hm) hsize

/-- The driver stops at the first singleton depth. -/
def buildTopDepthCountExpr (x b : Expr) : Expr :=
  .bin .div (.bin .sub (.bin .add x b) (.const 1)) b

/-- Evaluate the number of scheduled depths using the capped branching exponent. -/
theorem eval_buildTopDepthCountExpr {w x b : ℕ} {t : State} {xe be : Expr}
    (hx : xe.eval w t = some x) (hb : be.eval w t = some b)
    (h1 : 1 < 2 ^ w) (hadd : x + b < 2 ^ w) :
    (buildTopDepthCountExpr xe be).eval w t = some (leafDepth x b) := by
  exact Expr.eval_div
    (Expr.eval_sub (Expr.eval_add hx hb hadd) (Expr.eval_const h1) hadd) hb
    ((Nat.sub_le _ _).trans_lt hadd)

/-- With the branching exponent capped at the root, the schedule's depth
arithmetic fits whenever the padded terminal count fits. -/
theorem buildTopScheduleWords_fit {x b w : ℕ} (hb : 0 < b) (hbx : b ≤ x)
    (hw : 2 ^ x < 2 ^ w) :
    x + b < 2 ^ w ∧
    ∀ j < leafDepth x b, j + 1 < 2 ^ w ∧ (j + 1) * b < 2 ^ w := by
  have hx : 2 * x ≤ 2 ^ x := by
    cases x with
    | zero => decide
    | succ x =>
      rw [pow_succ, Nat.mul_comm 2]
      exact Nat.mul_le_mul_right 2 x.lt_two_pow_self
  have hsum : x + b < 2 ^ w := (show x + b ≤ 2 * x by omega).trans_lt (hx.trans_lt hw)
  refine ⟨hsum, fun j hj => ?_⟩
  have hm := queryDepth_mul_lt hb hj hw (hbx.trans_lt (x.lt_two_pow_self.trans hw))
  have hjm : j + 1 ≤ (j + 1) * b := Nat.le_mul_of_pos_right _ hb
  exact ⟨hjm.trans_lt hm, hm⟩

end MinCostFlow.HierPaths

end
