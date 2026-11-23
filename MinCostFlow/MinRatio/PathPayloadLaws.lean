module

public import MinCostFlow.MinRatio.PathPayload

/-!
# Remaining path payload laws

These are the identity, reversal, and single-node laws required by the
link-cut payload interface for Section 6 (pages 29–30). Together with
`PathPayload`'s composition laws, they let lazy updates and reversals
preserve the gradient, length, and detection summary of every path.
-/

public section

namespace MinCostFlow.MinRatio

/-- The empty path is a left identity. -/
theorem PathSummary.empty_combine (s : PathSummary) : PathSummary.empty.combine s = s := by
  cases s
  simp [PathSummary.combine, PathSummary.empty, detectorMax]

/-- The empty path is a right identity. -/
theorem PathSummary.combine_empty (s : PathSummary) : s.combine PathSummary.empty = s := by
  cases s with
  | mk g l d => cases d <;> simp [PathSummary.combine, PathSummary.empty, detectorMax]

/-- Summary reversal is an involution. -/
theorem PathSummary.reverse_reverse (s : PathSummary) : s.reverse.reverse = s := by
  ext <;> simp [PathSummary.reverse]

/-- Reversing an empty path gives an empty path. -/
theorem PathSummary.reverse_empty : PathSummary.empty.reverse = PathSummary.empty := by
  simp [PathSummary.reverse, PathSummary.empty]

/-- Single-node summaries respect directional reversal. -/
theorem PathSummary.reverse_single (v : Option PathEdgeValue) :
    (PathSummary.single v).reverse = PathSummary.single (v.map PathEdgeValue.reverse) := by
  cases v <;> simp [PathSummary.single, PathSummary.reverse, PathSummary.empty, PathEdgeValue.reverse]

/-- The identity tag leaves an edge unchanged. -/
theorem PathEdgeValue.shift_zero (v : PathEdgeValue) : v.shift PathTag.zero = v := by
  ext <;> simp [PathEdgeValue.shift, PathTag.zero]

/-- The identity tag leaves a path summary unchanged. -/
theorem PathSummary.shift_zero (s : PathSummary) : s.shift PathTag.zero = s := by
  cases s with
  | mk g l d => cases d <;> simp [PathSummary.shift, PathTag.zero]

/-- Zero is a left identity for composition. -/
theorem PathTag.zero_compose (t : PathTag) : PathTag.zero.compose t = t := by
  ext <;> simp [PathTag.compose, PathTag.zero]

/-- Zero is a right identity for composition. -/
theorem PathTag.compose_zero (t : PathTag) : t.compose PathTag.zero = t := by
  ext <;> simp [PathTag.compose, PathTag.zero]

/-- A lazy update has no effect on the empty path. -/
theorem PathSummary.empty_shift (t : PathTag) : PathSummary.empty.shift t = PathSummary.empty := rfl

/-- Updating a single edge agrees with updating its summary. -/
theorem PathSummary.shift_single (t : PathTag) (v : Option PathEdgeValue) :
    (PathSummary.single v).shift t = PathSummary.single (v.map (PathEdgeValue.shift t)) := by
  cases v <;> rfl

/-- The identity tag has no direction. -/
theorem PathTag.reverse_zero : PathTag.zero.reverse = PathTag.zero := by
  simp [PathTag.reverse, PathTag.zero]

/-- Reversing composed tags reverses their signed parts. -/
theorem PathTag.reverse_compose (a b : PathTag) :
    (a.compose b).reverse = a.reverse.compose b.reverse := by
  ext <;> simp [PathTag.reverse, PathTag.compose, add_comm]

/-- Summary updates commute with reversal after reversing the tag. -/
theorem PathSummary.reverse_shift (t : PathTag) (s : PathSummary) :
    (s.shift t).reverse = s.reverse.shift t.reverse := rfl

/-- The Boolean identity test used by the payload has no false positives. -/
theorem PathTag.isZero_iff (t : PathTag) : decide (t = PathTag.zero) = true ↔ t = PathTag.zero := by
  exact decide_eq_true_iff

end MinCostFlow.MinRatio
