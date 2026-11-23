module

public import MinCostFlow.HierPaths.InitProgSupportRows

/-!
# Columns of the support records

The terminal part reads the owner section. The walk part scans the
projected vertex rows in connector order. These columns are exactly
the inputs to stable bucketing by vertex.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

/-- The owner words in the static layout. -/
def initSupportOwners (S : StaticData) : List ℕ :=
  S.sections.getD 1 []

@[simp] theorem initSupportOwners_length (S : StaticData) :
    (initSupportOwners S).length = S.numTerm :=
  length_sections_one S

private theorem initSupportOwners_getD (S : StaticData) {i : ℕ} (hi : i < S.numTerm) :
    (initSupportOwners S).getD i 0 = S.owner i := by
  change ((List.range S.numTerm).map S.owner).getD i 0 = _
  rw [List.getD_eq_getElem _ _ (by simpa), List.getElem_map, List.getElem_range]

theorem initSupportVerts_eq (S : StaticData) (i : ℕ) (hi : i < S.numConn) :
    initProjectedRow S true i = ((connSystem S.H S.x S.b S.owner S.label).walk i).verts := by
  have hi' : i < (initConnLocs S).length := by rwa [initConnLocs_length]
  have he : (connRecs S.H S.x S.b).getD i default = ((initConnLocs S).getD i default).flat S := by
    rw [← initConnLocs_flat S, List.getD_eq_getElem _ _ (by simpa using hi'),
      List.getD_eq_getElem _ _ hi', List.getElem_map]
  dsimp [initProjectedRow, initProjectAtWords, initProjectedColumn, connSystem]
  rw [he]

/-- One of the two columns that the support builder emits. -/
def initSupportColumn (S : StaticData) (keys : Bool) : List ℕ :=
  initAppendPrefix (initSupportWords keys false ((initSupportOwners S).getD · 0) 0) S.numTerm ++
  initAppendPrefix (initSupportRowWords keys (initProjectedRow S true)) S.numConn

theorem initSupportRecords_column (S : StaticData) (keys : Bool) :
    (initSupportRecords S).map (if keys then Prod.fst else Prod.snd) =
      initSupportColumn S keys := by
  simp only [initSupportRecords, initSupportColumn, List.map_append, List.map_flatMap,
    initAppendPrefix]
  congr 1
  · apply List.flatMap_congr
    intro i hi
    have h := initSupportOwners_getD S (List.mem_range.mp hi)
    cases keys <;> simp [initSupportWords, entryWords, connSystem, ← List.getD_eq_getElem?_getD, h]
  · apply List.flatMap_congr
    intro i hi
    rw [initSupportRowWords, initSupportVerts_eq S i (List.mem_range.mp hi), initAppendPrefix]
    apply List.flatMap_congr
    intro j _
    cases keys <;> simp [initSupportWords, entryWords]

theorem initSupportRows_length (k : ℕ) (keys : Bool) (f : ℕ → List ℕ) :
    (initAppendPrefix (initSupportRowWords keys f) k).length = 3 * (csrData k f).length := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [initAppendPrefix_succ, List.length_append, ih, csrData_succ, List.length_append]
    simp [initSupportRowWords, initSupportPrefix_length, Nat.mul_add]

theorem initSupportRecords_length (S : StaticData) :
    (initSupportRecords S).length =
      3 * S.numTerm + 3 * (csrData S.numConn (initProjectedRow S true)).length := by
  have h := congrArg List.length (initSupportRecords_column S true)
  rw [List.length_map] at h
  exact h.trans (by simp [initSupportColumn, initSupportPrefix_length, initSupportRows_length])

theorem initSupportRecords_key_lt {S : StaticData} {G : Graph} {a d M : ℕ}
    (hgood : S.Good a d M G) {i : ℕ} (hi : i < (initSupportRecords S).length) :
    initBucketKey (initSupportRecords S) i < G.n := by
  let r := (initSupportRecords S)[i]
  have he : r ∈ initSupportRecords S := List.getElem_mem hi
  rw [initBucketKey, List.getD_eq_getElem _ _ hi]
  change r.1 < G.n
  rw [initSupportRecords, List.mem_append] at he
  rcases he with he | he
  · obtain ⟨t, ht, ht'⟩ := List.mem_flatMap.mp he
    obtain ⟨_, _, h⟩ := List.mem_map.mp ht'
    rw [← h]
    exact hgood.owner_lt t (List.mem_range.mp ht)
  · obtain ⟨c, hc, hc'⟩ := List.mem_flatMap.mp he
    obtain ⟨pos, hp, hp'⟩ := List.mem_flatMap.mp hc'
    obtain ⟨_, _, h⟩ := List.mem_map.mp hp'
    rw [← h]
    have hc' := List.mem_range.mp hc
    have hrec := connRec_spec hgood.b_pos hgood.valid (getD_mem_connRecs hc')
    have hpos := List.mem_range.mp hp
    rw [List.getD_eq_getElem _ _ hpos]
    have hmem := List.getElem_mem hpos
    rcases mem_verts_projectWalk hmem with hv | ⟨e, hem, hv | hv⟩
    · rw [hv]
      exact hgood.owner_lt _ hrec.2.2.2.1
    · rw [hv]
      exact (hgood.proj e (hrec.2.2.2.2.2.lt_length e hem)).1
    · rw [hv]
      exact (hgood.proj e (hrec.2.2.2.2.2.lt_length e hem)).2.1

end MinCostFlow.HierPaths

end
