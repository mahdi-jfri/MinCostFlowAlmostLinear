module

public import MinCostFlow.HierPaths.InitProgPairBuckets

/-!
# Records for the terminal connector lists

Each connector produces two records, one keyed by each of its endpoints.
The connectors are visited in connector order. The endpoints lie in
different children, so they cannot give two records to the same bucket.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited

/-- One connector contributes its index to its two terminal buckets. -/
def initTermRecord (S : StaticData) (i : ℕ) : List (ℕ × ℕ) :=
  let r := (connRecs S.H S.x S.b).getD i default
  [(r.endA, i), (r.endB, i)]

/-- Endpoint records in the order retained by stable bucketing. -/
def initTermRecords (S : StaticData) : List (ℕ × ℕ) :=
  (List.range S.numConn).flatMap (initTermRecord S)

theorem initTermRecords_length (S : StaticData) : (initTermRecords S).length = 2 * S.numConn := by
  simp [initTermRecords, initTermRecord, List.length_flatMap, List.map_const', Nat.mul_comm]

private theorem initTermRecord_endpoints {S : StaticData} (hb : 0 < S.b)
    (hH : S.H.IsValid S.x S.b) {i : ℕ} (hi : i < S.numConn) :
    let r := (connRecs S.H S.x S.b).getD i default
    r.endA ≠ r.endB ∧ r.endA < S.numTerm ∧ r.endB < S.numTerm := by
  let r := (connRecs S.H S.x S.b).getD i default
  obtain ⟨ha, hb', hlt, hu, hv, _⟩ := connRec_spec hb hH (getD_mem_connRecs hi)
  refine ⟨?_, hu, hv⟩
  intro he
  have h1 := mem_members_iff.mp ha
  have h2 := mem_members_iff.mp hb'
  rw [he, h2] at h1
  exact (Nat.ne_of_lt hlt) h1.symm

theorem initTermRecords_key_lt {S : StaticData} (hb : 0 < S.b)
    (hH : S.H.IsValid S.x S.b) {i : ℕ} (hi : i < (initTermRecords S).length) :
    initBucketKey (initTermRecords S) i < S.numTerm := by
  have hmem := List.getElem_mem hi
  unfold initTermRecords at hmem
  obtain ⟨j, hj, hrec⟩ := List.mem_flatMap.mp hmem
  obtain ⟨_, ha, hb'⟩ := initTermRecord_endpoints hb hH (List.mem_range.mp hj)
  simp only [initTermRecord, List.mem_cons, List.not_mem_nil, or_false] at hrec
  rw [initBucketKey, List.getD_eq_getElem _ _ hi]
  unfold initTermRecords
  rcases hrec with h | h
  · rw [h]
    exact ha
  · rw [h]
    exact hb'

/-- The records give each terminal its connectors in increasing order. -/
theorem initTermRecords_buckets {S : StaticData} (hb : 0 < S.b)
    (hH : S.H.IsValid S.x S.b) (u : ℕ) :
    buckets (initTermRecords S) u = termConns S.H S.x S.b u := by
  unfold buckets initTermRecords termConns
  rw [List.filter_flatMap, List.map_flatMap]
  let r := fun i => (connRecs S.H S.x S.b).getD i default
  have he (l : List ℕ) :
      l.filter (fun i => (r i).endA = u ∨ (r i).endB = u) =
        l.flatMap (fun i => if (r i).endA = u ∨ (r i).endB = u then [i] else []) := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.filter_cons, List.flatMap_cons, ← ih]
      by_cases h : (r i).endA = u ∨ (r i).endB = u <;> simp [h]
  rw [show (List.range (connRecs S.H S.x S.b).length) = List.range S.numConn from rfl, he]
  apply List.flatMap_congr
  intro i hi
  obtain ⟨hne, _, _⟩ := initTermRecord_endpoints hb hH (List.mem_range.mp hi)
  change ([( (r i).endA, i), ((r i).endB, i)].filter (fun p => p.1 = u)).map Prod.snd =
    if (r i).endA = u ∨ (r i).endB = u then [i] else []
  by_cases ha : (r i).endA = u
  · have hb' : (r i).endB ≠ u := fun he => hne (ha.trans he.symm)
    simp [ha, hb']
  · by_cases hb' : (r i).endB = u <;> simp [ha, hb']

/-- The terminal lists in compressed form. -/
def initTermSection (S : StaticData) : List ℕ :=
  csrList S.numTerm (buckets (initTermRecords S))

theorem initTermSection_length {S : StaticData} (hb : 0 < S.b)
    (hH : S.H.IsValid S.x S.b) :
    (initTermSection S).length = S.numTerm + 1 + 2 * S.numConn := by
  rw [initTermSection, csrList, List.length_append, length_csrOffsets,
    initBucket_data_length _ _ (fun _ hi => initTermRecords_key_lt hb hH hi), initTermRecords_length]

end MinCostFlow.HierPaths

end
