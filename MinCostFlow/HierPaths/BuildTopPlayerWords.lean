module

public import MinCostFlow.HierPaths.BuildTopPlayerModel
import MinCostFlow.HierPaths.InitProgNumbers

/-! # Word arithmetic for the root scale and branch exponent -/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Round the inverse conductance up before computing the root routing scale. -/
def buildTopRootScaleExpr (num den : Expr) : Expr :=
  .bin .mul (.const 100)
    (.bin .add (.bin .div (.bin .sub den (.const 1)) num) (.const 1))

/-- Compute the branch exponent from the logarithm and the core rank. -/
def buildTopBranchBitsExpr (log rank : Expr) : Expr :=
  .bin .div (.bin .sub (.bin .add log rank) (.const 1)) rank

theorem eval_buildTopRootScaleExpr {w num den : ℕ} {s : State} {ne de : Expr}
    (en : ne.eval w s = some num) (ed : de.eval w s = some den)
    (hn : 0 < num) (hd : 0 < den) (hdw : den < 2 ^ w)
    (hw : 100 * dOf num den < 2 ^ w) :
    (buildTopRootScaleExpr ne de).eval w s = some (100 * dOf num den) := by
  rw [dOf_eq_div_pred num den hn hd] at hw ⊢
  have h100 : 100 < 2 ^ w := (Nat.le_mul_of_pos_right 100 (Nat.succ_pos _)).trans_lt hw
  have h1 : 1 < 2 ^ w := by omega
  have hp := (Nat.sub_le den 1).trans_lt hdw
  have hdiv := (Nat.div_le_self (den - 1) num).trans_lt hp
  have hd' : (den - 1) / num + 1 < 2 ^ w :=
    (Nat.le_mul_of_pos_left _ (by decide : 0 < 100)).trans_lt hw
  exact Expr.eval_mul (Expr.eval_const h100)
    (Expr.eval_add (Expr.eval_div (Expr.eval_sub ed (Expr.eval_const h1) hdw) en hp)
      (Expr.eval_const h1) hd') hw

theorem eval_buildTopBranchBitsExpr {w m : ℕ} {s : State} {le re : Expr}
    (el : le.eval w s = some (xOf m)) (er : re.eval w s = some (depthOf m))
    (hw : xOf m + depthOf m < 2 ^ w) :
    (buildTopBranchBitsExpr le re).eval w s = some (branchBits m) := by
  have h1 : 1 < 2 ^ w := lt_of_lt_of_le (by decide : 1 < 2) (le_trans (two_le_depthOf m)
    ((Nat.le_add_left _ _).trans_lt hw).le)
  exact Expr.eval_div (Expr.eval_sub (Expr.eval_add el er hw) (Expr.eval_const h1) hw) er
    ((Nat.sub_le _ _).trans_lt hw)

end MinCostFlow.HierPaths

end
