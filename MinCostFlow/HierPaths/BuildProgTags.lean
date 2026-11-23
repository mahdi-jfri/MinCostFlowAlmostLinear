module

public import MinCostFlow.HierPaths.BuildProgContracts
public import WordRAM.Tactic

/-!
# Reading the player outcomes

The core uses two sections and the router uses three. In each block the first section
contains a single word identifying the outcome.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- The router uses zero for a matching and one for a cut. -/
def routeTag : RouteResult → ℕ
  | .matched _ _ => 0
  | .cut _ => 1

/-- The router result contains the tag cell. -/
theorem routeTag_lt_length (res : RouteResult) : 4 < (routeResultWords res).length := by
  cases res <;> simp [routeResultWords, layoutList, csrList, csrOffsets, csrData, List.range_succ]

/-- The router result's tag is at offset four. -/
theorem routeTag_at {res : RouteResult} {mem : ℕ → ℕ} {h : ℕ}
    (hAt : ListAt mem h (routeResultWords res)) :
    mem (h + 4) = routeTag res := by
  apply (hAt 4 (routeTag_lt_length res)).trans
  cases res <;> rfl

/-- Read the router tag using the checked end of its output block. -/
theorem eval_routeTag {w h r : ℕ} {st : State} {res : RouteResult}
    (hReg : st.regs r = h) (hAt : ListAt st.mem h (routeResultWords res))
    (hEnd : h + (routeResultWords res).length < 2 ^ w) :
    (Expr.load (.bin .add (.reg r) (.const 4))).eval w st = some (routeTag res) := by
  have := routeTag_lt_length res
  exact Expr.eval_load_of_eq
    (Expr.eval_add (Expr.eval_reg_of_eq hReg) (Expr.eval_const (by omega)) (by omega))
    (routeTag_at hAt)

/-- A cut block consists of four offsets, its tag and the cut members. -/
theorem routeCutWords_length (U : Finset ℕ) :
    (routeResultWords (.cut U)).length = U.card + 5 := by
  simp [routeResultWords, layoutList, csrList, csrOffsets, csrData, List.range_succ, finsetWords]

/-- The core always uses two sections, and the first contains the outcome tag. -/
def coreTag : CoreResult → ℕ
  | .cut _ => 0
  | .expander _ => 1

/-- The core result's tag is at offset three. -/
theorem coreTag_at {res : CoreResult} {mem : ℕ → ℕ} {h : ℕ}
    (hAt : ListAt mem h (coreResultWords res)) :
    mem (h + 3) = coreTag res := by
  apply (hAt 3 (by cases res <;> simp [coreResultWords, layoutList,
    csrList, csrOffsets, csrData, List.range_succ])).trans
  cases res <;> rfl

/-- The core result contains the tag cell. -/
theorem coreTag_lt_length (res : CoreResult) : 3 < (coreResultWords res).length := by
  cases res <;> simp [coreResultWords, layoutList, csrList, csrOffsets, csrData, List.range_succ]

/-- An address in a core result can be read once its end fits in a word. -/
theorem eval_coreTag {w h r : ℕ} {st : State} {res : CoreResult}
    (hReg : st.regs r = h) (hAt : ListAt st.mem h (coreResultWords res))
    (hEnd : h + (coreResultWords res).length < 2 ^ w) :
    (Expr.load (.bin .add (.reg r) (.const 3))).eval w st = some (coreTag res) := by
  have := coreTag_lt_length res
  exact Expr.eval_load_of_eq
    (Expr.eval_add (Expr.eval_reg_of_eq hReg) (Expr.eval_const (by omega)) (by omega))
    (coreTag_at hAt)

end MinCostFlow.HierPaths
