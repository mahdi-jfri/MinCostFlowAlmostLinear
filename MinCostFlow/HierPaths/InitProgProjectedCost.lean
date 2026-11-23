module

public import MinCostFlow.HierPaths.InitProgProjectedSec
public import MinCostFlow.HierPaths.InitProgConnCost

/-!
# Work and scratch of the projected walk writers

Summing over the static connector addresses gives the same flattening and
projection work as the initialization model. The remaining work is bounded
by the connector count, pair count, and size of the projected section.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited

private theorem list_sum_affine {α : Type} (xs : List α) (f g : α → ℕ) (a b c : ℕ) :
    (xs.map (fun x => a * f x + b * g x + c)).sum =
      a * (xs.map f).sum + b * (xs.map g).sum + c * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.mul_add]
    omega

private theorem loc_flatSteps_sum (S : StaticData) :
    ((initConnLocs S).map (fun q =>
      flatSteps S.H S.x S.b q.depth q.group (q.record S).1 (q.record S).2.2)).sum =
      flattenSteps S.H S.x S.b := by
  rw [flattenSteps, ← initConnLocs_local S, List.map_map]
  rfl

private theorem loc_root_lengths (S : StaticData) :
    ((initConnLocs S).map (fun q => (q.flat S).hwalk.length)).sum =
      projSteps S.H S.x S.b := by
  rw [projSteps, ← initConnLocs_flat S, List.map_map]
  rfl

/-- The section reserves space linear in the modeled edge work and connector count. -/
theorem initProjectedWriterScratch_le (S : StaticData) (verts : Bool)
    (hb : 0 < S.b) (hH : S.H.IsValid S.x S.b) :
    initProjectedWriterScratch S verts ≤ 3 * flattenSteps S.H S.x S.b +
      2 * projSteps S.H S.x S.b + 4 * S.numConn + 12 := by
  have h := List.sum_le_sum (l := initConnLocs S)
    (f := fun q => initConnProjectRoom S verts q.depth q.group (q.record S).1 (q.record S).2.2)
    (g := fun q => 3 * flatSteps S.H S.x S.b q.depth q.group (q.record S).1 (q.record S).2.2 +
      2 * (q.flat S).hwalk.length + 2) (fun q hq => by
      obtain ⟨hj, hg, _, _, _, _⟩ := initConnLoc_spec hq
      obtain ⟨_, _, hne, _, hw⟩ := initConnLoc_record_data hq hb hH
      exact initConnProjectRoom_le S verts q.depth q.group _ _ _ hH (initGroupSize_gt_one hb hj)
        hg hne hw)
  rw [list_sum_affine, loc_flatSteps_sum, loc_root_lengths, initConnLocs_length] at h
  unfold initProjectedWriterScratch initProjectedScratch
  omega

/-- Each projected section writer uses a fixed amount of work per pair slot,
input or output word, and connector. -/
theorem initProjectedWriterCost_le (S : StaticData) (G : Graph) (verts : Bool)
    (hb : 0 < S.b) (hH : S.H.IsValid S.x S.b) :
    initProjectedWriterCost S G verts ≤
      1100 * numPairsOf S.x S.b + 640 * (flattenSteps S.H S.x S.b + projSteps S.H S.x S.b) +
      1800 * S.numConn + 17 * (initProjectedSection S verts).length + 1300 := by
  let xs := initConnLocs S
  let F := fun q : InitConnLoc => initProjectAtCost 0 S G verts q + 100
  have hr : rangeCost (initProjectedRowCost S G verts) 0 S.numConn = (xs.map F).sum := by
    rw [rangeCost_zero_eq_range, ← initConnLocs_length S]
    change ((List.range xs.length).map (F ∘ fun i => xs.getD i default)).sum = _
    rw [← List.map_map, initConnLoc_map_range_getD_eq]
  have h := List.sum_le_sum (l := xs) (f := F)
    (g := fun q => 640 * flatSteps S.H S.x S.b q.depth q.group (q.record S).1 (q.record S).2.2 +
      640 * (q.flat S).hwalk.length + 1640) (fun q hq => by
      obtain ⟨hj, hg, _, _, _, _⟩ := initConnLoc_spec hq
      obtain ⟨_, _, hne, _, hw⟩ := initConnLoc_record_data hq hb hH
      have h := initConnProject_cost_le 0 S G verts q.depth q.group _ _ _ [] (fun _ => 0) hH
        (initGroupSize_gt_one hb hj) hg hne hw
      dsimp only [F, initProjectAtCost]
      change _ ≤ 640 * _ + 640 * (flatWalk S.H S.x S.b q.depth q.group
        (q.record S).1 (q.record S).2.2).length + 1640
      omega)
  change (xs.map F).sum ≤ _ at h
  dsimp only [xs] at h
  rw [list_sum_affine, loc_flatSteps_sum, loc_root_lengths, initConnLocs_length] at h
  have he := initEndpointSectionCost_le S hb hH
  unfold initProjectedWriterCost
  rw [hr]
  dsimp only [xs] at *
  omega

end MinCostFlow.HierPaths

end
