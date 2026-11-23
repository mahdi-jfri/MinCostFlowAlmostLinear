module

public import MinCostFlow.Scaling.CanonicalCallArguments
import WordRAM.Link
import WordRAM.Logic

/-!
# Expressions for the canonical solver arguments

The enclosing wrapper keeps the input length in register one, the guest
word bound in register two, and the relocated base in register four.
These expressions pass the canonical guest arguments and the two relocation
parameters through an ordinary call, for every guest register bound.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Canonical argument expressions for the wrapper's register layout. -/
def canonicalCallExprs (Q : Program) : List Expr :=
  ((List.range Q.regBound).map fun r => if r = 1 then .reg 1 else .const 0) ++
    [.reg 4, .reg 2]

private theorem pair_getD (len r : ℕ) :
    [0, len].getD r 0 = if r = 1 then len else 0 := by
  rcases r with _ | r
  · rfl
  · rcases r with _ | r
    · rfl
    · simp

private theorem prefix_eval {w : ℕ} (st : State) (len : ℕ)
    (hlen : st.regs 1 = len) (_hword : len < 2 ^ w) (rs : List ℕ) :
    evalArgs w st (rs.map fun r => if r = 1 then .reg 1 else .const 0) =
      some (rs.map fun r => [0, len].getD r 0) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [pair_getD] at ih
    simp only [List.map_cons, evalArgs, pair_getD]
    by_cases hr : r = 1
    · simp only [hr, ↓reduceIte, Expr.eval_reg, hlen, ih]
    · simp only [hr, ↓reduceIte, Expr.eval_const, Nat.two_pow_pos, ↓reduceIte, ih]

/-- The wrapper's expressions evaluate to the canonical relocated arguments. -/
theorem canonicalCallExprs_eval {w guestWidth h : ℕ} (Q : Program) (J : Circulation)
    (st : State) (hlen : st.regs 1 = J.solverWords.length)
    (hbase : st.regs 4 = h + 1) (hW : st.regs 2 = 2 ^ guestWidth)
    (hlenword : J.solverWords.length < 2 ^ w) :
    evalArgs w st (canonicalCallExprs Q) = some (canonicalCallArgs Q J guestWidth h) := by
  unfold canonicalCallExprs canonicalCallArgs
  apply Link.evalArgs_append
  · exact prefix_eval st _ hlen hlenword _
  · simp only [evalArgs, Expr.eval_reg, hbase, hW]

/-- Each canonical call argument expression has size one. -/
theorem canonicalCallExprs_size (Q : Program) :
    argsSize (canonicalCallExprs Q) = Q.regBound + 2 := by
  have hprefix : ∀ rs : List ℕ,
      argsSize (rs.map fun r => if r = 1 then .reg 1 else .const 0) = rs.length := by
    intro rs
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      simp only [List.map_cons, argsSize_cons, List.length_cons]
      by_cases hr : r = 1 <;> simp only [hr, ↓reduceIte, Expr.size_reg, Expr.size_const, ih] <;> omega
  simp only [canonicalCallExprs, Link.argsSize_append, hprefix, List.length_range,
    argsSize_cons, argsSize_nil, Expr.size_reg]

end MinCostFlow.Scaling.Machine
