module

public import MinCostFlow.HierPaths.Groups
public import WordRAM.Expr

/-!
# Group sizes in the query program

The hierarchy header gives the two exponents. At depth `j` the group size is
one shifted left by the exponent left after subtracting `j * b` from `x`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Compute a group size from the two exponents and the depth. Word subtraction stops at zero. -/
def queryGroupSizeExpr (x b j : Expr) : Expr :=
  .bin .shiftLeft (.const 1) (.bin .sub x (.bin .mul j b))

/-- The group size expression needs only the product and the largest group size to fit. -/
theorem eval_queryGroupSizeExpr {w x b j : ℕ} {s : State} {xe be je : Expr}
    (hx : xe.eval w s = some x) (hb : be.eval w s = some b) (hj : je.eval w s = some j)
    (hxw : 2 ^ x < 2 ^ w) (hm : j * b < 2 ^ w) :
    (queryGroupSizeExpr xe be je).eval w s = some (groupSize x b j) := by
  have h1 : 1 < 2 ^ w := lt_of_le_of_lt (Nat.two_pow_pos x) hxw
  have hs : x < 2 ^ w := x.lt_two_pow_self.trans hxw
  have hsub : x - min x (j * b) = x - j * b := by omega
  have hpow : 2 ^ (x - j * b) < 2 ^ w :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (show 0 < 2 by decide) (Nat.sub_le ..)) hxw
  unfold queryGroupSizeExpr groupSize
  rw [hsub, ← Nat.one_mul (2 ^ (x - j * b)), ← Nat.shiftLeft_eq]
  exact Expr.eval_shiftLeft (Expr.eval_const h1)
    (Expr.eval_sub hx (Expr.eval_mul hj hb hm) hs) (by simpa [Nat.shiftLeft_eq] using hpow)

/-- A depth at or above the leaves can multiply the branching exponent in one word. -/
theorem queryDepth_mul_lt {x b j w : ℕ} (hb : 0 < b) (hj : j ≤ leafDepth x b)
    (hxw : 2 ^ x < 2 ^ w) (hbw : b < 2 ^ w) : j * b < 2 ^ w := by
  by_cases h : j ≤ 1
  · exact (Nat.mul_le_mul_right b h).trans_lt (by simpa using hbw)
  unfold leafDepth at hj
  have hm := (Nat.le_div_iff_mul_le hb).mp hj
  have hb' : b < x := by
    have h2 := Nat.mul_le_mul_right b (show 2 ≤ j by omega)
    omega
  have hx : 2 * x ≤ 2 ^ x := by
    cases x with
    | zero => decide
    | succ x =>
      rw [pow_succ, Nat.mul_comm 2]
      exact Nat.mul_le_mul_right 2 x.lt_two_pow_self
  exact (hm.trans (by omega : x + b - 1 ≤ 2 * x)).trans_lt (hx.trans_lt hxw)

/-- Capping the branching exponent at the root exponent leaves all group sizes unchanged. -/
theorem groupSize_query_min_branch (x b j : ℕ) :
    groupSize x (min x b) j = groupSize x b j := by
  by_cases h : b ≤ x
  · rw [min_eq_right h]
  cases j with
  | zero => simp [groupSize]
  | succ j =>
    have hb : x ≤ b := by omega
    have hx : x ≤ (j + 1) * x := by
      simpa using Nat.mul_le_mul_right x (Nat.succ_le_succ (Nat.zero_le j))
    have hxb : x ≤ (j + 1) * b := hx.trans (Nat.mul_le_mul_left _ hb)
    simp [groupSize, min_eq_left hb, min_eq_left hx, min_eq_left hxb]

/-- The capped branching exponent also gives a word product at every query depth. -/
theorem queryDepth_mul_min_lt {x b j w : ℕ} (hb : 0 < b) (hj : j ≤ leafDepth x b)
    (hxw : 2 ^ x < 2 ^ w) : j * min x b < 2 ^ w := by
  by_cases h : b ≤ x
  · rw [min_eq_right h]
    exact queryDepth_mul_lt hb hj hxw (h.trans_lt (x.lt_two_pow_self.trans hxw))
  have hxb : x ≤ b := by omega
  have hd : leafDepth x b ≤ 1 := by
    unfold leafDepth
    apply Nat.lt_succ_iff.mp
    apply (Nat.div_lt_iff_lt_mul hb).mpr
    omega
  rw [min_eq_left hxb]
  exact ((Nat.mul_le_mul_right x (hj.trans hd)).trans (Nat.one_mul x).le).trans_lt
    (x.lt_two_pow_self.trans hxw)

/-- This version of the branching exponent fits in a word whenever the root size does. -/
def queryBranchExpr (x b : Expr) : Expr :=
  .bin .sub x (.bin .sub x b)

/-- Saturating subtraction implements `min x b`, even for a large raw value of `b`. -/
theorem eval_queryBranchExpr {w x b : ℕ} {s : State} {xe be : Expr}
    (hx : xe.eval w s = some x) (hb : be.eval w s = some b) (hxw : x < 2 ^ w) :
    (queryBranchExpr xe be).eval w s = some (min x b) := by
  have h : x - (x - b) = min x b := by omega
  rw [← h]
  exact Expr.eval_sub hx (Expr.eval_sub hx hb hxw) hxw

end MinCostFlow.HierPaths
