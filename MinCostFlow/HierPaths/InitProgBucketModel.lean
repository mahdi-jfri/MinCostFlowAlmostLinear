module

public import MinCostFlow.HierPaths.InitProgAppend
public import MinCostFlow.HierPaths.InitProgCSR
public import MinCostFlow.HierPaths.IndexArrays
public import MinCostFlow.LowStretch.ProgCSR

/-!
# Stable buckets and compressed rows

The counting sort returns the record numbers for each key in input order.
Reading the payloads in that order gives the buckets of the record stream.
The prefix counts are exactly the offsets of the resulting compressed rows.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.LowStretch

/-- The key of a record addressed by its position in the input stream. -/
def initBucketKey (rs : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  (rs.getD i (0, 0)).1

/-- The payload of a record addressed by its position in the input stream. -/
def initBucketValue (rs : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  (rs.getD i (0, 0)).2

theorem initBucket_group (rs : List (ℕ × ℕ)) (k : ℕ) :
    (grp (initBucketKey rs) rs.length k).map (initBucketValue rs) = buckets rs k := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [grp, List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map,
      buckets, List.filter_cons]
    have h : ((List.range rs.length).filter fun i => initBucketKey (r :: rs) (i + 1) = k).map
        (fun i => initBucketValue (r :: rs) (i + 1)) = buckets rs k := ih
    simp only [Function.comp_def, decide_eq_true_eq]
    by_cases hr : r.1 = k
    · simp only [show initBucketKey (r :: rs) 0 = r.1 from rfl, hr, ↓reduceIte,
        List.map_cons, List.map_map, show initBucketValue (r :: rs) 0 = r.2 from rfl]
      congr 1
    · simp only [show initBucketKey (r :: rs) 0 = r.1 from rfl, hr, ↓reduceIte, List.map_map]
      exact h

/-- The counting sort prefix count equals the number of payload words in earlier buckets. -/
theorem initBucket_offset (rs : List (ℕ × ℕ)) (k : ℕ) :
    offOf (initBucketKey rs) rs.length k = initCSRPrefix (buckets rs) k := by
  induction k with
  | zero => simp [offOf_zero, initCSRPrefix]
  | succ k ih =>
    rw [offOf_succ, initCSRPrefix_succ, ih]
    have h := congrArg List.length (initBucket_group rs k)
    simp only [List.length_map] at h
    rw [h]

/-- The final offset counts all records when every key lies in range. -/
theorem initBucket_data_length (rs : List (ℕ × ℕ)) (k : ℕ)
    (hk : ∀ i < rs.length, initBucketKey rs i < k) :
    (csrData k (buckets rs)).length = rs.length := by
  rw [csrData, List.length_flatMap]
  change initCSRPrefix (buckets rs) k = rs.length
  rw [← initBucket_offset]
  exact offOf_all (initBucketKey rs) hk

open WordRAM in
/-- A flat data array is determined by its rows and their start offsets. -/
theorem initBucket_listAt_from_rows {mem : ℕ → ℕ} {base k : ℕ} {f : ℕ → List ℕ}
    (h : ∀ u < k, ListAt mem (base + initCSRPrefix f u) (f u)) :
    ListAt mem base (csrData k f) := by
  induction k with
  | zero => simp [csrData, ListAt]
  | succ k ih =>
    have hk : (csrData k f).length = initCSRPrefix f k := by
      rw [csrData, List.length_flatMap, initCSRPrefix]
    have he : csrData (k + 1) f = csrData k f ++ f k := by
      simp [csrData, List.range_succ, List.flatMap_append]
    rw [he, listAt_append, hk]
    exact ⟨ih (fun i hi => h i (hi.trans (Nat.lt_succ_self _))), h k (Nat.lt_succ_self _)⟩

/-- The stable record indices emitted by counting sort. -/
def initBucketOrder (rs : List (ℕ × ℕ)) (k : ℕ) : List ℕ :=
  csrData k (grp (initBucketKey rs) rs.length)

theorem initBucketOrder_values (rs : List (ℕ × ℕ)) (k : ℕ) :
    (initBucketOrder rs k).map (initBucketValue rs) = csrData k (buckets rs) := by
  simp [initBucketOrder, csrData, List.map_flatMap, initBucket_group]

theorem initBucketOrder_length (rs : List (ℕ × ℕ)) (k : ℕ)
    (hk : ∀ i < rs.length, initBucketKey rs i < k) :
    (initBucketOrder rs k).length = rs.length := by
  rw [← List.length_map (f := initBucketValue rs), initBucketOrder_values]
  exact initBucket_data_length rs k hk

theorem initBucketOrder_lt (rs : List (ℕ × ℕ)) (k : ℕ) {i : ℕ}
    (hi : i ∈ initBucketOrder rs k) : i < rs.length := by
  obtain ⟨u, _, hi⟩ := List.mem_flatMap.mp hi
  rw [grp, List.mem_filter, List.mem_range] at hi
  exact hi.1

theorem initBucket_prefix_group (rs : List (ℕ × ℕ)) (k : ℕ) :
    initCSRPrefix (grp (initBucketKey rs) rs.length) k = offOf (initBucketKey rs) rs.length k := by
  induction k with
  | zero => simp [initCSRPrefix, offOf_zero]
  | succ k ih => rw [initCSRPrefix_succ, offOf_succ, ih]

end MinCostFlow.HierPaths

end
