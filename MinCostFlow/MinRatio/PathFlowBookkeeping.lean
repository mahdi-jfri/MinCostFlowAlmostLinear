module

public import MinCostFlow.MinRatio.DetectorThreshold
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Flow and detection accounts under one path update

Algorithm 2 (page 29) adds the signed circulation increment to the flow
and counts its absolute change for detection. On a path, the payload tag
adds the signed increment in the traversal direction. This gives the
correct original-direction flow and residual at each edge of a path
that uses it once. The pointwise statement leaves the decomposition of
a whole circulation into paths to the calling procedure.
-/

public section

namespace MinCostFlow.MinRatio

/-- In original edge coordinates, a path update changes the sign only
when the path goes against the edge. -/
theorem PathEdgeValue.originalFlow_shift (value : PathEdgeValue) (tag : PathTag) :
    (value.shift tag).originalFlow =
      value.originalFlow + if value.forward then tag.flow else -tag.flow := by
  cases hf : value.forward <;>
    simp [PathEdgeValue.shift, PathEdgeValue.originalFlow, hf, add_comm]

/-- The same path update adds the absolute flow change to the detector
residual, in either traversal direction. -/
theorem PathEdgeValue.detector_shift_ofFlow (value : PathEdgeValue) (delta : ℤ) :
    (value.shift (PathTag.ofFlow delta)).detector =
      value.detector + |if value.forward then delta else -delta| := by
  cases hf : value.forward <;> simp [PathEdgeValue.shift, PathTag.ofFlow, hf]

/-- A flow addition along one path preserves the exact residual used by
the Detect test. Here the path uses the edge once and its length is fixed. -/
theorem PathEdgeValue.detector_shift_threshold (value : PathEdgeValue)
    (P : ℕ) (epsilon length : ℝ) (account delta : ℤ)
    (hvalue : value.detector = account - detectorThreshold P epsilon length) :
    (value.shift (PathTag.ofFlow delta)).detector =
      account + |delta| - detectorThreshold P epsilon length := by
  change value.detector + |delta| = _
  rw [hvalue]
  exact detectorThreshold_add_flow P epsilon length account delta

/-- Scaling the integer residual update gives exactly the Detect condition
after accounting for this edge's absolute flow increment. -/
theorem PathEdgeValue.detector_shift_ready (value : PathEdgeValue)
    (P : ℕ) (epsilon length : ℝ) (account delta : ℤ) (hLength : 0 < length)
    (hvalue : value.detector = account - detectorThreshold P epsilon length) :
    0 ≤ (value.shift (PathTag.ofFlow delta)).detector ↔
      epsilon ≤ length * (((account + |delta| : ℤ) : ℝ) / (2 : ℝ) ^ P) := by
  rw [value.detector_shift_threshold P epsilon length account delta hvalue]
  exact (detectorThreshold_test P epsilon length (account + |delta|) hLength).symm

end MinCostFlow.MinRatio

public section

namespace MinCostFlow.MinRatio

/-- Applying the signed changes of several path tags gives the net flow
change. The detector instead adds each tag's own absolute change. -/
theorem PathEdgeValue.shift_paths (edge : PathEdgeValue) (changes : List ℤ) :
    (changes.foldl (fun value delta => value.shift (PathTag.ofFlow delta)) edge).flow =
        edge.flow + changes.sum ∧
    (changes.foldl (fun value delta => value.shift (PathTag.ofFlow delta)) edge).detector =
        edge.detector + (changes.map fun z => |z|).sum := by
  induction changes generalizing edge with
  | nil => simp
  | cons delta rest ih =>
    simp only [List.foldl_cons, List.sum_cons, List.map_cons]
    obtain ⟨hf, hd⟩ := ih (edge.shift (PathTag.ofFlow delta))
    rw [hf, hd]
    simp only [PathEdgeValue.shift, PathTag.ofFlow, add_assoc, and_self]

private theorem sum_nonpos_int (changes : List ℤ) (h : ∀ z ∈ changes, z ≤ 0) :
    changes.sum ≤ 0 := by
  induction changes with
  | nil => exact le_rfl
  | cons z rest ih =>
    exact add_nonpos (h z List.mem_cons_self)
      (ih fun t ht => h t (List.mem_cons_of_mem _ ht))

/-- For a route with no cancellation on this edge, separate absolute
changes add up to the absolute value of the net change. -/
theorem abs_path_change_sum (changes : List ℤ)
    (h : (∀ z ∈ changes, 0 ≤ z) ∨ (∀ z ∈ changes, z ≤ 0)) :
    (changes.map fun z => |z|).sum = |changes.sum| := by
  rcases h with hp | hn
  · induction changes with
    | nil => simp
    | cons z rest ih =>
      have hz := hp z List.mem_cons_self
      have hr : ∀ t ∈ rest, 0 ≤ t := fun t ht => hp t (List.mem_cons_of_mem _ ht)
      have hs : 0 ≤ rest.sum := List.sum_nonneg hr
      simp [abs_of_nonneg hz, abs_of_nonneg hs, abs_of_nonneg (add_nonneg hz hs), ih hr]
  · induction changes with
    | nil => simp
    | cons z rest ih =>
      have hz := hn z List.mem_cons_self
      have hr : ∀ t ∈ rest, t ≤ 0 := fun t ht => hn t (List.mem_cons_of_mem _ ht)
      have hs : rest.sum ≤ 0 := sum_nonpos_int rest hr
      simp [abs_of_nonpos hz, abs_of_nonpos hs, abs_of_nonpos (add_nonpos hz hs), ih hr, add_comm]

/-- A route whose traversals agree in direction on this edge therefore
has the detector update specified by Algorithm 2. -/
theorem PathEdgeValue.shift_paths_account (edge : PathEdgeValue) (changes : List ℤ)
    (h : (∀ z ∈ changes, 0 ≤ z) ∨ (∀ z ∈ changes, z ≤ 0)) :
    (changes.foldl (fun value delta => value.shift (PathTag.ofFlow delta)) edge).detector =
      edge.detector + |changes.sum| := by
  rw [(edge.shift_paths changes).2, abs_path_change_sum changes h]

end MinCostFlow.MinRatio
