module

public import MinCostFlow.HierPaths.InitProgConnWriter
public import MinCostFlow.HierPaths.InitModelCost

/-!
# Direct addresses for connectors

A connector's pair number and position in the matching identify its static
record. Both address columns are available from the ordered endpoint
traversal, so later calls need only constant-time row lookups.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.ExpanderDecomp

/-- The record coordinates of one connector in the static hierarchy. -/
structure InitConnLoc where
  depth : ℕ
  group : ℕ
  child : ℕ
  sibling : ℕ
  index : ℕ
  deriving Inhabited

namespace InitConnLoc

/-- The compressed row's index. -/
def slot (S : StaticData) (q : InitConnLoc) : ℕ :=
  pairIdxOf S.x S.b q.depth q.child q.sibling

/-- The local matching record at this position. -/
def record (S : StaticData) (q : InitConnLoc) : ℕ × ℕ × List ℕ :=
  (S.H.conn q.depth q.child q.sibling).getD q.index (0, 0, [])

/-- The corresponding connector of the flat model. -/
def flat (S : StaticData) (q : InitConnLoc) : ConnRec :=
  let r := q.record S
  ⟨q.depth, q.group, q.child, q.sibling, r.1, r.2.1,
    flatWalk S.H S.x S.b q.depth q.group r.1 r.2.2⟩

end InitConnLoc

/-- Connector coordinates in the order of the initialized arrays. -/
def initConnLocs (S : StaticData) : List InitConnLoc :=
  (List.range (leafDepth S.x S.b)).flatMap fun j =>
    (List.range (numGroups S.x S.b j)).flatMap fun g =>
    (childList S.x S.b j g).flatMap fun c =>
    (childList S.x S.b j g).flatMap fun c' =>
      if c < c' then (List.range (S.H.conn j c c').length).map (fun i => ⟨j, g, c, c', i⟩)
      else []

theorem initConnLoc_map_range_getD_eq {α : Type} (xs : List α) (d : α) :
    (List.range xs.length).map (fun i => xs.getD i d) = xs := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp [List.getElem?_eq_getElem hj]

/-- The two traversals agree connector by connector. -/
theorem initConnLocs_flat (S : StaticData) :
    (initConnLocs S).map (InitConnLoc.flat S) = connRecs S.H S.x S.b := by
  unfold initConnLocs connRecs
  simp only [List.map_flatMap]
  congr 1; funext j; congr 1; funext g; congr 1; funext c; congr 1; funext c'
  unfold pairRecs
  by_cases h : c < c'
  · simp only [h, ↓reduceIte, List.map_map]
    let F : ℕ × ℕ × List ℕ → ConnRec := fun q =>
      ⟨j, g, c, c', q.1, q.2.1, flatWalk S.H S.x S.b j g q.1 q.2.2⟩
    change (List.range (S.H.conn j c c').length).map
      (F ∘ (fun i => (S.H.conn j c c').getD i (0, 0, []))) = _
    rw [← List.map_map, initConnLoc_map_range_getD_eq]
  · simp [h]

theorem initConnLocs_length (S : StaticData) : (initConnLocs S).length = S.numConn := by
  change _ = (connRecs S.H S.x S.b).length
  rw [← initConnLocs_flat S, List.length_map]

/-- Field 2 of the traversal writes the pair numbers. -/
theorem initConnLocs_slots (S : StaticData) :
    (initConnLocs S).map (InitConnLoc.slot S) = initEndpointWords S 2 := by
  rw [initEndpointWords_pairs_eq_map, ← initConnLocs_flat S, List.map_map]
  apply List.map_congr_left
  intro q hq
  unfold initConnLocs at hq
  simp only [List.mem_flatMap] at hq
  obtain ⟨j, _, g, _, c, _, c', _, hq⟩ := hq
  by_cases hc : c < c'
  · simp only [hc, ↓reduceIte, List.mem_map] at hq
    obtain ⟨i, _, rfl⟩ := hq
    simp [InitConnLoc.slot, InitConnLoc.flat, pairIdxOf, pairNum, min_eq_left hc.le, max_eq_right hc.le]
  · simp [hc] at hq

/-- Field 3 of the traversal writes the record indices. -/
theorem initConnLocs_indices (S : StaticData) :
    (initConnLocs S).map InitConnLoc.index = initEndpointWords S 3 := by
  unfold initConnLocs initEndpointWords
  simp only [List.map_flatMap]
  congr 1; funext j; congr 1; funext g; congr 1; funext c; congr 1; funext c'
  unfold initPairEndpointWords
  by_cases hc : c < c'
  · simp [hc, List.map_map, Function.comp_def]
  · simp [hc]

theorem initConnLoc_spec {S : StaticData} {q : InitConnLoc} (hq : q ∈ initConnLocs S) :
    q.depth < leafDepth S.x S.b ∧ q.group < numGroups S.x S.b q.depth ∧
    q.child ∈ childGroups S.x S.b q.depth q.group ∧
    q.sibling ∈ childGroups S.x S.b q.depth q.group ∧ q.child < q.sibling ∧
    q.index < (S.H.conn q.depth q.child q.sibling).length := by
  unfold initConnLocs at hq
  simp only [List.mem_flatMap, List.mem_range, mem_childList] at hq
  obtain ⟨j, hj, g, hg, c, hc, c', hc', hq⟩ := hq
  by_cases h : c < c'
  · simp only [h, ↓reduceIte, List.mem_map, List.mem_range] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    exact ⟨hj, hg, hc, hc', h, hi⟩
  · simp [h] at hq

theorem initConnLoc_slot_lt {S : StaticData} {q : InitConnLoc} (hq : q ∈ initConnLocs S) :
    q.slot S < numPairsOf S.x S.b := by
  obtain ⟨hj, hg, hc, _, hcc, _⟩ := initConnLoc_spec hq
  exact staticConnRow_index_lt S hj hg hc hcc

theorem initConnLoc_pairOfIdx {S : StaticData} {q : InitConnLoc} (hq : q ∈ initConnLocs S) :
    pairOfIdx S.x S.b (q.slot S) = (q.depth, q.child, q.sibling) := by
  obtain ⟨_, hg, hc, hc', hcc, _⟩ := initConnLoc_spec hq
  exact pairOfIdx_pairIdxOf hc hc' hcc
    ((childGroups_lt_numGroups hg hc).trans_le (numGroups_le_pow _))

theorem initConnLoc_matching_length {S : StaticData} {q : InitConnLoc}
    (hq : q ∈ initConnLocs S) (hb : 0 < S.b) (hH : S.H.IsValid S.x S.b) :
    (staticConnMatching S (q.slot S)).length = groupSize S.x S.b (q.depth + 1) := by
  obtain ⟨hj, hg, hc, hc', hcc, _⟩ := initConnLoc_spec hq
  rw [staticConnMatching, initConnLoc_pairOfIdx hq]
  obtain ⟨hn, hF, _, _⟩ := hH.conn_perfect q.depth q.group (initGroupSize_gt_one hb hj)
    hg q.child hc q.sibling hc' hcc
  change (S.H.conn q.depth q.child q.sibling).length = _
  rw [← List.length_map (f := Prod.fst), ← List.toFinset_card_of_nodup hn, hF, card_members]

theorem initConnLoc_record_data {S : StaticData} {q : InitConnLoc}
    (hq : q ∈ initConnLocs S) (hb : 0 < S.b) (hH : S.H.IsValid S.x S.b) :
    let r := q.record S
    r.1 < S.numTerm ∧ r.2.1 < S.numTerm ∧ r.1 ≠ r.2.1 ∧
      groupOf S.x S.b q.depth r.1 = q.group ∧
      IsEdgeWalk (S.H.host q.depth q.group).edges r.1 r.2.1 r.2.2 := by
  let r := q.record S
  obtain ⟨hj, hg, hc, hc', hcc, hi⟩ := initConnLoc_spec hq
  have hs := initGroupSize_gt_one hb hj
  have hr : r ∈ S.H.conn q.depth q.child q.sibling := by
    dsimp only [r, InitConnLoc.record]
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hspec := connRec_spec hb hH (show q.flat S ∈ connRecs S.H S.x S.b from by
    rw [← initConnLocs_flat S]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩)
  obtain ⟨ha, hb', _, hu, hv, _⟩ := hspec
  refine ⟨hu, hv, ?_, ?_, hH.conn_walk q.depth q.group hs hg q.child hc q.sibling hc' hcc r hr⟩
  · intro he
    have h1 := mem_members_iff.mp ha
    have h2 := mem_members_iff.mp hb'
    change groupOf S.x S.b (q.depth + 1) r.1 = q.child at h1
    change groupOf S.x S.b (q.depth + 1) r.2.1 = q.sibling at h2
    exact (Nat.ne_of_lt hcc) (h1.symm.trans ((congrArg _ he).trans h2))
  · exact (mem_members_iff.mp (members_succ_subset q.child ha)).trans (mem_childGroups_iff.mp hc)

theorem initConnLocs_local (S : StaticData) :
    (initConnLocs S).map (fun q => (q.depth, q.group, q.child, q.sibling, q.record S)) =
      connLocal S.H S.x S.b := by
  unfold initConnLocs connLocal
  simp only [List.map_flatMap]
  congr 1; funext j; congr 1; funext g; congr 1; funext c; congr 1; funext c'
  by_cases h : c < c'
  · simp only [h, ↓reduceIte, List.map_map]
    let F : ℕ × ℕ × List ℕ → ℕ × ℕ × ℕ × ℕ × (ℕ × ℕ × List ℕ) :=
      fun q => (j, g, c, c', q)
    change (List.range (S.H.conn j c c').length).map
      (F ∘ (fun i => (S.H.conn j c c').getD i (0, 0, []))) = _
    rw [← List.map_map, initConnLoc_map_range_getD_eq]
  · simp [h]

end MinCostFlow.HierPaths

end
