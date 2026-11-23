module

public import MinCostFlow.HierPaths.BuildTopPlayerModel
import Mathlib.Tactic.Ring

/-! # Computing the core expansion-loss base from the root exponent -/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

def buildTopCoreFactorConst : ℕ := 1920 * 12 * 4096 ^ 3 * 1600 * 4
def buildTopCoreLengthConst : ℕ := 3200 * 4096 * 4

/-- The loss is a constant times the fourth power of the logarithm
times the core path-length factor. -/
theorem buildTopCoreFactor (x : ℕ) (hx : 0 < x) :
    FParam ParamConfig.default (2 ^ x) =
      buildTopCoreFactorConst * (x + 2) ^ 4 * (buildTopCoreLengthConst * (x + 2) ^ 2 + 1) := by
  unfold FParam RCore dCore deltaParam tParam LParam
  rw [buildTopCoreEll x hx]
  change 1920 * 12 * (1024 * (4 * (x + 2))) ^ 2 *
    (1600 * (1024 * (4 * (x + 2))) *
      (3200 * (1024 * (4 * (x + 2))) * (4 * (x + 2)) + 1) *
      (4 * (x + 2))) = _
  unfold buildTopCoreFactorConst buildTopCoreLengthConst
  ring

def buildTopBaseMul (l r : Expr) : Expr := .bin .mul l r
def buildTopBaseSquare (e : Expr) : Expr := buildTopBaseMul e e

/-- Evaluate the loss base once before building the inner rows. -/
def buildTopCoreBaseExpr (x : Expr) : Expr :=
  let ell := Expr.bin .add x (.const 2)
  let sq := buildTopBaseSquare ell
  buildTopBaseMul (buildTopBaseMul (.const buildTopCoreFactorConst) (buildTopBaseSquare sq))
    (.bin .add (buildTopBaseMul (.const buildTopCoreLengthConst) sq) (.const 1))

/-- All intermediate values fit whenever the loss itself fits. -/
theorem eval_buildTopCoreBaseExpr {w x : ℕ} {s : State} {e : Expr}
    (he : e.eval w s = some x) (hx : 0 < x)
    (hw : FParam ParamConfig.default (2 ^ x) < 2 ^ w) :
    (buildTopCoreBaseExpr e).eval w s = some (FParam ParamConfig.default (2 ^ x)) := by
  rw [buildTopCoreFactor x hx] at hw ⊢
  let L := x + 2
  have hp : 0 < L := by dsimp [L]; omega
  have hc : 0 < buildTopCoreFactorConst := by decide
  have hlen : 0 < buildTopCoreLengthConst := by decide
  have h4 : 0 < L ^ 4 := Nat.pow_pos hp
  have h2 : 0 < L ^ 2 := Nat.pow_pos hp
  have hf : buildTopCoreFactorConst * L ^ 4 < 2 ^ w := (Nat.le_mul_of_pos_right (buildTopCoreFactorConst * L ^ 4) (Nat.succ_pos (buildTopCoreLengthConst * L ^ 2))).trans_lt hw
  have hterm : buildTopCoreLengthConst * L ^ 2 + 1 < 2 ^ w :=
    (Nat.le_mul_of_pos_left _ (Nat.mul_pos hc h4)).trans_lt hw
  have hL4 : L ^ 4 < 2 ^ w := (Nat.le_mul_of_pos_left _ hc).trans_lt hf
  have hL2 : L ^ 2 < 2 ^ w := by
    exact (Nat.pow_le_pow_right hp (by decide : 2 ≤ 4)).trans_lt hL4
  have hL : L < 2 ^ w := (Nat.le_self_pow (by decide : 2 ≠ 0) _).trans_lt hL2
  have hconst : buildTopCoreFactorConst < 2 ^ w := (Nat.le_mul_of_pos_right _ h4).trans_lt hf
  have hlenw : buildTopCoreLengthConst < 2 ^ w := (Nat.le_mul_of_pos_right _ h2).trans_lt
    ((Nat.le_succ _).trans_lt hterm)
  have heL : (Expr.bin .add e (.const 2)).eval w s = some L :=
    Expr.eval_add he (Expr.eval_const (by dsimp [L] at hL; omega)) hL
  have hesq : (buildTopBaseSquare (Expr.bin .add e (.const 2))).eval w s = some (L ^ 2) := by
    have hmul : L * L < 2 ^ w := by rw [← pow_two]; exact hL2
    simpa only [pow_two, buildTopBaseSquare, buildTopBaseMul] using Expr.eval_mul heL heL hmul
  have he4 : (buildTopBaseSquare (buildTopBaseSquare (Expr.bin .add e (.const 2)))).eval w s = some (L ^ 4) := by
    have eq : L ^ 2 * L ^ 2 = L ^ 4 := by rw [← pow_add]
    rw [← eq]
    exact Expr.eval_mul hesq hesq (eq ▸ hL4)
  exact Expr.eval_mul (Expr.eval_mul (Expr.eval_const hconst) he4 hf)
    (Expr.eval_add (Expr.eval_mul (Expr.eval_const hlenw) hesq ((Nat.le_succ _).trans_lt hterm))
      (Expr.eval_const (by dsimp [L] at hL; omega)) hterm) hw

end MinCostFlow.HierPaths

end
