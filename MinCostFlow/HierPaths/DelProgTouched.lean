module

public import MinCostFlow.HierPaths.DelProgWalkPass
public import MinCostFlow.HierPaths.DelProgOwnerPass
public import MinCostFlow.HierPaths.DelProgPairPass

/-!
# The entries visited by the cursor passes

The work lists use first-visit order. The model uses deduplicated lists. The same vertices
and pairs occur in both, so they cause the same cursor changes.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

private theorem StaticArrays.delCollect_newInelig_aux (A : StaticArrays) (st : DelState) (e : ℕ) :
    ∀ c, c ∈ delCollect st.inelig ((A.newLost st e).flatMap A.termConns) ↔
      c ∈ A.newInelig st e := by
  intro c
  simpa only [List.mem_toFinset] using
    (Finset.ext_iff.mp (delCollect_newInelig A st e) c)

/-- The vertices visited by the owner pass followed by the connector walk pass. -/
def StaticArrays.delSupportVisits (A : StaticArrays) (st : DelState) (e : ℕ) : List ℕ :=
  (A.newLost st e).map A.C.owner ++
    (delCollect st.inelig ((A.newLost st e).flatMap A.termConns)).flatMap (fun c => (A.C.walk c).verts)

/-- The machine's support passes visit exactly the vertices in the model's touched set. -/
theorem StaticArrays.mem_delSupportVisits (A : StaticArrays) (st : DelState) (e v : ℕ) :
    v ∈ A.delSupportVisits st e ↔ v ∈ A.touchedVerts st e := by
  have h := A.delCollect_newInelig_aux st e
  simp only [delSupportVisits, touchedVerts, List.mem_dedup, List.mem_append, List.mem_flatMap]
  simp only [h]

/-- The pairs visited by the connector pass. -/
def StaticArrays.delPairVisits (A : StaticArrays) (st : DelState) (e : ℕ) : List ℕ :=
  (delCollect st.inelig ((A.newLost st e).flatMap A.termConns)).map A.pairOf

/-- The machine's pair pass visits exactly the pairs in the model's touched set. -/
theorem StaticArrays.mem_delPairVisits (A : StaticArrays) (st : DelState) (e q : ℕ) :
    q ∈ A.delPairVisits st e ↔ q ∈ A.touchedPairs st e := by
  have h := A.delCollect_newInelig_aux st e
  simp only [delPairVisits, touchedPairs, List.mem_dedup, List.mem_map, h]

end MinCostFlow.HierPaths

end
