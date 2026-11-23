module

public import MinCostFlow.Basic.Forest
public import MinCostFlow.Basic.Embedding
public import MinCostFlow.Basic.Hidden

/-!
# Checks of the shared graph notions on small examples

These examples test the graphs, walks, flow vectors, updates and encoding sizes of
`MinCostFlow/Basic/` on a path with two edges.
-/

namespace MinCostFlow

/-- The path `0 → 1 → 2`, with edges `0 = (0, 1)` and `1 = (1, 2)`. -/
def path2 : MGraph :=
  ⟨{0, 1, 2}, {0, 1}, fun e => if e = 0 then 0 else 1, fun e => if e = 0 then 1 else 2⟩

example : path2.IsValid := by
  intro e he; simp [path2] at he ⊢; rcases he with rfl | rfl <;> simp

/-- Along both edges from `0` to `2`. -/
example : path2.IsWalk 0 2 [(0, true), (1, true)] :=
  .cons (by decide) (by decide) (.cons (by decide) (by decide) (.nil 2))

/-- Back from `2` to `0`, against both edges. -/
example : path2.IsWalk 2 0 (walkRev [(0, true), (1, true)]) :=
  .cons (by decide) (by decide) (.cons (by decide) (by decide) (.nil 0))

/-- The walk from `0` to `2` is a path. -/
example : path2.IsPath 0 2 [(0, true), (1, true)] :=
  ⟨.cons (by decide) (by decide) (.cons (by decide) (by decide) (.nil 2)), by decide⟩

/-- A walk along edge `0` and back has flow `0` on edge `0`. -/
example : walkFlow [(0, true), (0, false)] 0 = 0 := by
  norm_num [walkFlow]

/-- Degrees: the middle vertex has degree `2`. -/
example : path2.deg 0 = 1 ∧ path2.deg 1 = 2 ∧ path2.deg 2 = 1 := by
  decide

/-- Splitting vertex `1` into `1` and `3`, with edge `1` moving to `3`: the edge `1` now starts at
`3`, and the split costs `min(1, 1) + 1 = 2`. -/
example : (path2.applyUpdate (.split 1 3 {1} {1})).tail 1 = 3 ∧
    (path2.applyUpdate (.split 1 3 {1} {1})).head 0 = 1 ∧
    path2.updateEnc (.split 1 3 {1} {1}) = 2 := by
  decide

/-- Deleting edge `0` and inserting edge `5 = (2, 0)`. -/
example : (path2.applyBatch [.delete 0, .insert 5 2 0]).E = {1, 5} := by
  decide

end MinCostFlow
