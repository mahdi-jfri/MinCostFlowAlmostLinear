module

public import MinCostFlow.HierPaths.InitProgPairBuckets
public import MinCostFlow.HierPaths.InitProgKnownCost

/-!
# Cost of traversing the connector table

Within one pair row the number of connectors is the size of a child.
At a given depth the child sizes sum to the number of terminals, so
the cost of copying a column is linear in the number of pair slots.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

private theorem initSlot_matching_length_le (S : StaticData) {j g c i : ℕ}
    (hH : S.H.IsValid S.x S.b)
    (hg : g < numGroups S.x S.b j) (hc : c ∈ childGroups S.x S.b j g)
    (hs : 1 < groupSize S.x S.b j)
    (hlo : firstChildSlotStart S.x S.b j g c ≤ i)
    (hhi : i < firstChildSlotEnd S.x S.b j g c) :
    (staticConnMatching S i).length ≤ groupSize S.x S.b (j + 1) := by
  let br := branching S.x S.b j
  let L := g * br
  let base := firstChildSlot S.x S.b j g c
  let z := i - base
  let c' := L + z
  have hcI := hc
  rw [childGroups_eq_Ico, Finset.mem_Ico] at hcI
  change L ≤ c ∧ c < L + br at hcI
  change base + (c - L + 1) ≤ i at hlo
  change i < base + br at hhi
  have hz : z < br := by dsimp [z]; omega
  have hcc : c < c' := by dsimp [c', z]; omega
  have hc' : c' ∈ childGroups S.x S.b j g := by
    rw [childGroups_eq_Ico, Finset.mem_Ico]
    change L ≤ L + z ∧ L + z < L + br
    omega
  have hi : pairIdxOf S.x S.b j c c' = i := by
    rw [show c' = g * branching S.x S.b j + z from rfl,
      pairIdxOf_eq_firstChildSlot_add hs hz hcc.le]
    change base + z = i
    dsimp only [z]
    omega
  have hsmall := (childGroups_lt_numGroups hg hc).trans_le (numGroups_le_pow (j + 1))
  rw [← hi, staticConnMatching, pairOfIdx_pairIdxOf hc hc' hcc hsmall]
  obtain ⟨hn, hset, _, _⟩ := hH.conn_perfect j g hs hg c hc c' hc' hcc
  rw [← List.length_map (f := Prod.fst), ← List.toFinset_card_of_nodup hn, hset, card_members]

private theorem initLevelChildCost_le (S : StaticData) {j c : ℕ}
    (hH : S.H.IsValid S.x S.b) (hs : 1 < groupSize S.x S.b j)
    (hc : c < numGroups S.x S.b (j + 1)) :
    initLevelChildCost S j c ≤
      branching S.x S.b j * (60 * groupSize S.x S.b (j + 1) + 166) + 110 := by
  let g := parentGroup S.x S.b j c
  let br := branching S.x S.b j
  let lo := firstChildSlotStart S.x S.b j g c
  let hi := firstChildSlotEnd S.x S.b j g c
  have hgc : g < numGroups S.x S.b j := parentGroup_lt_numGroups hc
  have hchild : c ∈ childGroups S.x S.b j g := by
    exact mem_childGroups_iff.mpr rfl
  have hlen : hi - lo ≤ br := by
    dsimp [lo, hi, firstChildSlotStart, firstChildSlotEnd, br]
    omega
  let C := 60 * groupSize S.x S.b (j + 1) + 157
  have hsum : rangeCost (fun i => 60 * (staticConnMatching S i).length + 157) lo hi ≤
      (hi - lo) * C := by
    apply rangeCost_le_mul
    intro i hlo hhi
    have h := initSlot_matching_length_le S hH hgc hchild hs hlo hhi
    dsimp [C]
    omega
  have hmul := Nat.mul_le_mul_right C hlen
  simp only [initLevelChildCost, initEndpointChildContract]
  change rangeCost _ lo hi + 9 * (hi - lo) + 100 + 10 ≤ _
  calc
    _ ≤ br * C + 9 * br + 110 := by omega
    _ = _ := by dsimp [C, br]; ring

private theorem initDepthLevelCost_le (S : StaticData) {j : ℕ}
    (hH : S.H.IsValid S.x S.b) (hs : 1 < groupSize S.x S.b j) :
    initDepthLevelCost S j ≤ 500 * (2 ^ S.x * 2 ^ S.b) := by
  let P := 2 ^ S.x
  let B := 2 ^ S.b
  let k := numGroups S.x S.b (j + 1)
  let br := branching S.x S.b j
  let sz := groupSize S.x S.b (j + 1)
  let C := br * (60 * sz + 166) + 110
  have hsum : rangeCost (initLevelChildCost S j) 0 k ≤ k * C := by
    simpa only [Nat.sub_zero] using
      (rangeCost_le_mul (lo := 0) (hi := k) (c := C)
        (fun i _ hi => initLevelChildCost_le S hH hs hi))
  have hp : k * sz = P := numGroups_mul_groupSize
  have hk : k ≤ P := numGroups_le_pow _
  have hbr : br ≤ B := branching_le_pow _
  have hPB : P ≤ P * B := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have hPB' : 1 ≤ P * B := Nat.le_trans (Nat.two_pow_pos S.x) hPB
  have hkbr : k * br ≤ P * B := Nat.mul_le_mul hk hbr
  have hPbr : P * br ≤ P * B := Nat.mul_le_mul_left P hbr
  have he : k * C = 60 * (k * sz) * br + 166 * (k * br) + 110 * k := by dsimp [C]; ring
  simp only [initDepthLevelCost, initEndpointLevelContract]
  change rangeCost _ 0 k + 9 * k + 12 + 70 ≤ _
  rw [he, hp] at hsum
  have hm : 60 * P * br = 60 * (P * br) := Nat.mul_assoc ..
  change _ ≤ 500 * (P * B)
  omega

/-- The writer visits at most a constant number of cells per pair slot across all depths. -/
theorem initEndpointSectionCost_le (S : StaticData) (hb : 0 < S.b)
    (hH : S.H.IsValid S.x S.b) :
    initEndpointSectionCost S ≤ 520 * numPairsOf S.x S.b + 120 := by
  let D := leafDepth S.x S.b
  let C := 2 ^ S.x * 2 ^ S.b
  have hsum : rangeCost (initDepthLevelCost S) 0 D ≤ D * (500 * C) := by
    simpa only [Nat.sub_zero] using
      (rangeCost_le_mul (lo := 0) (hi := D) (c := 500 * C) (fun j _ hj =>
        initDepthLevelCost_le S hH (initGroupSize_gt_one hb hj)))
  have hDC : D * C = numPairsOf S.x S.b := by
    simp [D, C, numPairsOf, Nat.mul_assoc]
  have hD : D ≤ numPairsOf S.x S.b := by
    rw [← hDC]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
  have he : D * (500 * C) = 500 * numPairsOf S.x S.b := by
    rw [← hDC, Nat.mul_left_comm]
  rw [he] at hsum
  simp only [initEndpointSectionCost, initEndpointDepthContract]
  change rangeCost _ 0 D + 9 * D + 12 + 100 ≤ _
  omega

end MinCostFlow.HierPaths

end
