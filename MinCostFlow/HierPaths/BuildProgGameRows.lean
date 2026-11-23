module

public import MinCostFlow.HierPaths.BuildProgGameModel

/-!
# Walk rows in the model of one game round

The scan stores one row of the router reply at a time. The model filters a
flattened reply by the first endpoint. Disjoint child intervals identify the
same row and preserve the order of both its edges and its walks.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

private theorem rawEntries_append (F G : List (ℕ × ℕ)) (emb : ℕ → List ℕ) :
    rawEntries (F ++ G) emb = rawEntries F emb ++ rawEntries G (fun j => emb (F.length + j)) := by
  unfold rawEntries
  rw [List.length_append, List.range_add, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro j hj
    exact Prod.ext (List.getD_append _ _ _ _ (List.mem_range.mp hj)) rfl
  · rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    have h : F.length ≤ F.length + j := by omega
    have he : edgeAt (F ++ G) (F.length + j) = edgeAt G j := by
      unfold edgeAt
      rw [List.getD_append_right _ _ _ _ h]
      simp
    exact Prod.ext he rfl

private theorem rawEntries_filter_row {Ms : List (List (ℕ × ℕ))} {P : (ℕ × ℕ) → Bool}
    {i : ℕ} (hi : i < Ms.length)
    (hP : ∀ a (ha : a < Ms.length), ∀ e ∈ Ms[a], P e = true ↔ a = i) (emb : ℕ → List ℕ) :
    (rawEntries Ms.flatten emb).filter (fun en => P en.1) =
      rawEntries Ms[i] (fun j => emb (flatIndex Ms i j)) := by
  induction Ms generalizing i emb with
  | nil => simp at hi
  | cons F Ms ih =>
    rw [List.flatten_cons,rawEntries_append,List.filter_append]
    cases i with
    | zero =>
      have hLeft : (rawEntries F emb).filter (fun en => P en.1) = rawEntries F emb := by
        apply List.filter_eq_self.mpr
        intro en hen
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hen
        have hj' := List.mem_range.mp hj
        change P (edgeAt F j) = true
        apply (hP 0 (by simp) _ _).mpr rfl
        exact edgeAt_mem hj'
      have hRight : (rawEntries Ms.flatten (fun j => emb (F.length + j))).filter
          (fun en => P en.1) = [] := by
        rw [List.filter_eq_nil_iff]
        intro en hen hEn
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hen
        have hh := edgeAt_mem (List.mem_range.mp hj)
        obtain ⟨G,hG,hEg⟩ := List.mem_flatten.mp hh
        obtain ⟨a,ha,rfl⟩ := List.getElem_of_mem hG
        have hFalse := (hP (a+1) (by simp; omega) _ hEg).mp hEn
        omega
      rw [hLeft,hRight,List.append_nil]
      simp [flatIndex]
    | succ i =>
      have hLeft : (rawEntries F emb).filter (fun en => P en.1) = [] := by
        rw [List.filter_eq_nil_iff]
        intro en hen hEn
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hen
        have hFalse := (hP 0 (by simp) _ (edgeAt_mem (List.mem_range.mp hj))).mp hEn
        omega
      rw [hLeft,List.nil_append]
      have hi' : i < Ms.length := by simpa using hi
      have hP' : ∀ a (ha : a < Ms.length), ∀ e ∈ Ms[a], P e = true ↔ a = i := by
        intro a ha e he
        simpa using hP (a+1) (by simp; omega) e he
      rw [ih hi' hP']
      apply congrArg (rawEntries Ms[i])
      funext j
      congr 1
      simp [flatIndex,List.take_succ_cons,Nat.add_assoc]

/-- The model's filtered entries are exactly the row edges with their shortened walks
as written by the common batch. -/
theorem takeEntries_eq_matchingRow {G : Graph} {Ms : List (List (ℕ × ℕ))}
    {emb : ℕ → List ℕ} {i s off : ℕ} (hi : i < Ms.length)
    (hP : ∀ a (ha : a < Ms.length), ∀ e ∈ Ms[a], e.1 ∈ shiftSet off (Finset.range s) ↔ a = i) :
    takeEntries s off (callEntries G.edges (.matched Ms emb)) =
      (List.range (Ms.getD i []).length).map fun j =>
        let row := matchingWalkRow Ms emb i
        ((row.u j - off,row.v j - off),erase G.edges (row.u j) (row.raw j)) := by
  have hp : ∀ a (ha : a < Ms.length), ∀ e ∈ Ms[a],
      decide (e.1 ∈ shiftSet off (Finset.range s)) = true ↔ a = i := by
    intro a ha e he
    simpa using hP a ha e he
  unfold takeEntries callEntries
  rw [rawEntries_filter_row hi hp]
  unfold rawEntries
  rw [List.map_map, List.getD_eq_getElem _ _ hi]
  apply List.map_congr_left
  intro j hj
  have hj' : j < Ms[i].length := List.mem_range.mp hj
  have hD : Ms.getD i [] = Ms[i] := List.getD_eq_getElem _ _ hi
  have h := (getD_flatten_flatIndex Ms (0,0) hi (show j < (Ms.getD i []).length by rw [hD]; exact hj')).2
  change edgeAt Ms.flatten (flatIndex Ms i j) = edgeAt (Ms.getD i []) j at h
  simp only [Function.comp_apply, matchingWalkRow, BuildWalkRow.raw]
  rw [h,hD]
  rfl

end MinCostFlow.HierPaths
