module

public import MinCostFlow.HierPaths.InitProgRepeatRows
public import MinCostFlow.HierPaths.InitProgBucketMove

/-!
# Record streams for the reverse index

The edge data of the compressed walk section are the keys. Repeating
each designated endpoint once per edge gives the payloads in exactly
the same order as the occurrence model.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

def initReverseRecords (S : StaticData) : List (ℕ × ℕ) :=
  occRecs S.H S.x S.b S.owner S.label

def initReversePayload (S : StaticData) (i : ℕ) : ℕ :=
  ((connRecs S.H S.x S.b).getD i default).endA

private theorem initProjectedEdges_eq (S : StaticData) (i : ℕ) (hi : i < S.numConn) :
    initProjectedRow S false i = ((connSystem S.H S.x S.b S.owner S.label).walk i).edges := by
  have he : (connRecs S.H S.x S.b).getD i default = ((initConnLocs S).getD i default).flat S := by
    have hi' := hi
    rw [← initConnLocs_length S] at hi'
    rw [← initConnLocs_flat S, List.getD_eq_getElem _ _ (by simpa using hi'),
      List.getD_eq_getElem _ _ hi', List.getElem_map]
  dsimp [initProjectedRow, initProjectAtWords, initProjectedColumn, connSystem]
  rw [he]

theorem initReverseRecords_eq (S : StaticData) :
    initReverseRecords S = (List.range S.numConn).flatMap fun i =>
      (initProjectedRow S false i).map (fun e => (e, initReversePayload S i)) := by
  unfold initReverseRecords occRecs
  let xs := connRecs S.H S.x S.b
  change xs.flatMap _ = _
  rw [← initConnLoc_map_range_getD_eq xs default, List.flatMap_map]
  apply List.flatMap_congr
  intro i hi
  have hi' : i < S.numConn := by
    have hx : xs.length = S.numConn := rfl
    exact hx ▸ List.mem_range.mp hi
  rw [initProjectedEdges_eq S i hi']
  rfl

theorem initReverseRecords_keys (S : StaticData) :
    (initReverseRecords S).map Prod.fst = csrData S.numConn (initProjectedRow S false) := by
  rw [initReverseRecords_eq, csrData, List.map_flatMap]
  apply List.flatMap_congr
  intro i _
  simp [List.map_map, Function.comp_def]

theorem initReverseRecords_vals (S : StaticData) :
    (initReverseRecords S).map Prod.snd =
      initRepeatRowsWords S.numConn (initProjectedRow S false) (initReversePayload S) := by
  rw [initReverseRecords_eq, initRepeatRowsWords, initAppendPrefix, List.map_flatMap]
  apply List.flatMap_congr
  intro i _
  simp [List.map_map, Function.comp_def, List.map_const']

theorem initReverseData_length (S : StaticData) :
    (csrData S.numConn (initProjectedRow S false)).length = (initReverseRecords S).length := by
  rw [← initReverseRecords_keys, List.length_map]

theorem initReverseRecords_key_lt {S : StaticData} {G : Graph} {a d M : ℕ}
    (hgood : S.Good a d M G) {i : ℕ} (hi : i < (initReverseRecords S).length) :
    initBucketKey (initReverseRecords S) i < G.m := by
  let r := (initReverseRecords S)[i]
  have he : r ∈ initReverseRecords S := List.getElem_mem hi
  rw [initReverseRecords_eq] at he
  obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
  obtain ⟨e, hem, heq⟩ := List.mem_map.mp he
  have hj' := List.mem_range.mp hj
  rw [initProjectedEdges_eq S j hj'] at hem
  have h := connRec_spec hgood.b_pos hgood.valid (getD_mem_connRecs hj')
  have hp := projectWalk_isWalk hgood.proj h.2.2.2.2.2 (hgood.owner_lt _ h.2.2.2.1)
  rw [initBucketKey, List.getD_eq_getElem _ _ hi]
  change r.1 < G.m
  rw [← heq]
  obtain ⟨_, _, hnil | hwalk⟩ := hp
  · exact (List.not_mem_nil (hnil.2.1 ▸ hem)).elim
  · exact hwalk.2.2.2.2.1 e hem

/-- The reverse index in compressed form. -/
def initReverseSection (S : StaticData) (G : Graph) : List ℕ :=
  csrList G.m (buckets (initReverseRecords S))

theorem initReverseSection_eq (S : StaticData) (G : Graph) (a pn pd M : ℕ) :
    (initConcrete S a (initAbs pn pd M G)).sections.getD 6 [] = initReverseSection S G := by
  change csrList G.m (revIdx S.H S.x S.b S.owner S.label) = _
  unfold initReverseSection
  congr 1
  funext e
  exact revIdx_eq_buckets e

theorem initReverseSection_length {S : StaticData} {G : Graph} {a d M : ℕ}
    (hgood : S.Good a d M G) :
    (initReverseSection S G).length = G.m + 1 + (initReverseRecords S).length := by
  rw [initReverseSection, csrList, List.length_append, length_csrOffsets,
    initBucket_data_length _ _ (fun _ hi => initReverseRecords_key_lt hgood hi)]

end MinCostFlow.HierPaths

end
