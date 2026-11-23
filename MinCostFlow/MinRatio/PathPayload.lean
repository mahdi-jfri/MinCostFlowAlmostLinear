module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.MinMax

/-!
# Path values for the dynamic trees of Section 6

The proof of Theorem 5.1 (pages 29–30) keeps flow and detection accounts
on tree edges, sums signed gradients and lengths along a path, and finds
edges with nonnegative detection accounts. These definitions give the
fixed-point integer data for that payload. Vertex nodes use `none`.

A reversal negates the directional gradient and flow, but preserves
length and the detection account. A path tag has two entries: signed flow
and an independent change to the detection account. Keeping them separate
is necessary for composition: absolute values are not additive when
successive signed flow updates cancel. Actual flow updates use the
absolute value of their signed change as the detection change.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

/-- Fixed-point integers of one edge in the current path direction.
The direction bit converts the stored flow back to its original direction. -/
@[ext] structure PathEdgeValue where
  forward : Bool
  gradient : ℤ
  length : ℤ
  flow : ℤ
  detector : ℤ
  deriving DecidableEq

/-- A lazy path update. Both coordinates use the flow's fixed-point scale. -/
@[ext] structure PathTag where
  flow : ℤ
  detector : ℤ
  deriving DecidableEq

/-- A constant-size path summary. `none` is the maximum of an empty path. -/
@[ext] structure PathSummary where
  gradient : ℤ
  length : ℤ
  detector : Option ℤ
  deriving DecidableEq

/-- Flow in the original edge direction. -/
def PathEdgeValue.originalFlow (v : PathEdgeValue) : ℤ := if v.forward then v.flow else -v.flow

/-- Reverse the path direction at an edge. -/
def PathEdgeValue.reverse (v : PathEdgeValue) : PathEdgeValue :=
  ⟨!v.forward, -v.gradient, v.length, -v.flow, v.detector⟩

/-- Apply a signed flow change and a detection-account change. -/
def PathEdgeValue.shift (t : PathTag) (v : PathEdgeValue) : PathEdgeValue :=
  { v with flow := v.flow + t.flow, detector := v.detector + t.detector }

/-- Identity lazy update. -/
def PathTag.zero : PathTag := ⟨0, 0⟩

/-- Compose updates in the order used by the generic link-cut payload. -/
def PathTag.compose (outer inner : PathTag) : PathTag :=
  ⟨outer.flow + inner.flow, outer.detector + inner.detector⟩

/-- Reverse a directional update. Detection is independent of direction. -/
def PathTag.reverse (t : PathTag) : PathTag := ⟨-t.flow, t.detector⟩

/-- The lazy tag for one actual flow change. -/
def PathTag.ofFlow (delta : ℤ) : PathTag := ⟨delta, |delta|⟩

/-- Maximum with an empty segment allowed. -/
def detectorMax : Option ℤ → Option ℤ → Option ℤ
  | none, b => b
  | a, none => a
  | some a, some b => some (max a b)

/-- Empty segment. -/
def PathSummary.empty : PathSummary := ⟨0, 0, none⟩

/-- Summary of a vertex or an edge. Node identity is supplied by the tree. -/
def PathSummary.single : Option PathEdgeValue → PathSummary
  | none => .empty
  | some v => ⟨v.gradient, v.length, some v.detector⟩

/-- Combine adjacent path segments. -/
def PathSummary.combine (a b : PathSummary) : PathSummary :=
  ⟨a.gradient + b.gradient, a.length + b.length, detectorMax a.detector b.detector⟩

/-- Reverse a segment summary. -/
def PathSummary.reverse (s : PathSummary) : PathSummary := ⟨-s.gradient, s.length, s.detector⟩

/-- Apply a lazy update to a segment summary. -/
def PathSummary.shift (t : PathTag) (s : PathSummary) : PathSummary :=
  { s with detector := s.detector.map fun z => z + t.detector }

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

/-- Lazy detection increments add separately from signed flow increments. -/
theorem PathEdgeValue.shift_compose (a b : PathTag) (v : PathEdgeValue) :
    v.shift (a.compose b) = (v.shift b).shift a := by
  ext <;> simp [PathEdgeValue.shift, PathTag.compose, add_comm, add_left_comm]

/-- The two tag coordinates form an additive composition law. -/
theorem PathTag.compose_assoc (a b c : PathTag) :
    (a.compose b).compose c = a.compose (b.compose c) := by
  ext <;> simp [PathTag.compose, add_assoc]

/-- Reversal preserves the original-direction flow exposed by Query. -/
theorem PathEdgeValue.originalFlow_reverse (v : PathEdgeValue) :
    v.reverse.originalFlow = v.originalFlow := by
  cases h : v.forward <;> simp [PathEdgeValue.originalFlow, PathEdgeValue.reverse, h]

/-- Edge reversal is an involution. -/
theorem PathEdgeValue.reverse_reverse (v : PathEdgeValue) : v.reverse.reverse = v := by
  ext <;> simp [PathEdgeValue.reverse]

/-- Tag reversal is an involution. -/
theorem PathTag.reverse_reverse (t : PathTag) : t.reverse.reverse = t := by
  ext <;> simp [PathTag.reverse]

/-- A lazy update commutes with reversal after reversing its signed part. -/
theorem PathEdgeValue.reverse_shift (t : PathTag) (v : PathEdgeValue) :
    (v.shift t).reverse = v.reverse.shift t.reverse := by
  ext <;> simp [PathEdgeValue.reverse, PathEdgeValue.shift, PathTag.reverse, add_comm]

/-- The optional maximum is associative, including empty segments. -/
theorem detectorMax_assoc (a b c : Option ℤ) :
    detectorMax (detectorMax a b) c = detectorMax a (detectorMax b c) := by
  cases a <;> cases b <;> cases c <;> simp [detectorMax, max_assoc]

/-- The optional maximum does not depend on segment order. -/
theorem detectorMax_comm (a b : Option ℤ) : detectorMax a b = detectorMax b a := by
  cases a <;> cases b <;> simp [detectorMax, max_comm]

/-- A uniform detector change preserves the maximum. -/
theorem detectorMax_shift (a b : Option ℤ) (delta : ℤ) :
    detectorMax (a.map fun z => z + delta) (b.map fun z => z + delta) =
      (detectorMax a b).map (fun z => z + delta) := by
  cases a <;> cases b <;> simp [detectorMax, max_add_add_right]

/-- Segment combination is associative. -/
theorem PathSummary.combine_assoc (a b c : PathSummary) :
    (a.combine b).combine c = a.combine (b.combine c) := by
  ext <;> simp [PathSummary.combine, add_assoc, detectorMax_assoc]

/-- Reversal reverses the order of adjacent segments. -/
theorem PathSummary.reverse_combine (a b : PathSummary) :
    (a.combine b).reverse = b.reverse.combine a.reverse := by
  ext <;> simp [PathSummary.reverse, PathSummary.combine, add_comm, detectorMax_comm]

/-- Lazy updates preserve segment combination. -/
theorem PathSummary.shift_combine (t : PathTag) (a b : PathSummary) :
    (a.combine b).shift t = (a.shift t).combine (b.shift t) := by
  ext <;> simp [PathSummary.shift, PathSummary.combine, detectorMax_shift]

/-- Summary updates compose with the same tag operation as edge updates. -/
theorem PathSummary.shift_compose (a b : PathTag) (s : PathSummary) :
    s.shift (a.compose b) = (s.shift b).shift a := by
  ext <;> simp [PathSummary.shift, PathTag.compose, Option.map_map,
    Function.comp_def, add_comm, add_left_comm]

/-- Opposite signed updates retain their total absolute change in Detect. -/
theorem PathTag.canceling_updates (delta : ℤ) :
    (PathTag.ofFlow (-delta)).compose (PathTag.ofFlow delta) = ⟨0, 2 * |delta|⟩ := by
  ext <;> simp [PathTag.compose, PathTag.ofFlow, two_mul]

end MinCostFlow.MinRatio
