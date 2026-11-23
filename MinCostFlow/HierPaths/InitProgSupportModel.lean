module

public import MinCostFlow.HierPaths.InitProgReverseModel

/-!
# Records for the support index

The records list terminal owners before walk vertices. Each support
contributes three words with the same key, so stable bucketing gives
word offsets and keeps the order of positions.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

/-- Records of the support index, before bucketing by vertex. -/
def initSupportRecords (S : StaticData) : List (ℕ × ℕ) :=
  let C := connSystem S.H S.x S.b S.owner S.label
  ((List.range S.numTerm).flatMap fun t =>
    (entryWords (.term t)).map (fun word => (C.owner t, word))) ++
  (List.range S.numConn).flatMap fun c =>
    ((List.range (C.walk c).verts.length).flatMap fun pos =>
      (entryWords (.onWalk c pos)).map (fun word => ((C.walk c).verts.getD pos 0, word)))

private theorem bucket_map_words (words : List ℕ) (key v : ℕ) :
    buckets (words.map (fun word => (key, word))) v = if key = v then words else [] := by
  induction words with
  | nil => simp [buckets]
  | cons a l ih =>
    by_cases h : key = v <;> simp_all [buckets]

private theorem bucket_flatMap_words (xs : List ℕ) (key : ℕ → ℕ) (words : ℕ → List ℕ)
    (v : ℕ) :
    buckets (xs.flatMap fun i => (words i).map (fun word => (key i, word))) v =
      (xs.filter (fun i => key i = v)).flatMap words := by
  induction xs with
  | nil => rfl
  | cons i l ih =>
    simp only [List.flatMap_cons]
    have hApp (a b : List (ℕ × ℕ)) :
        buckets (a ++ b) v = buckets a v ++ buckets b v := by
      simp [buckets, List.filter_append]
    rw [hApp, ih, bucket_map_words]
    by_cases h : key i = v <;> simp [h]

theorem initSupportRecords_bucket (S : StaticData) (v : ℕ) :
    buckets (initSupportRecords S) v =
      ((connSystem S.H S.x S.b S.owner S.label).supportArray v).flatMap entryWords := by
  simp only [initSupportRecords, ConnectorSystem.supportArray, ConnectorSystem.positionsOn,
    List.flatMap_append, List.flatMap_map]
  rw [show ∀ a b : List (ℕ × ℕ), buckets (a ++ b) v = buckets a v ++ buckets b v by
    intros; simp [buckets, List.filter_append]]
  rw [bucket_flatMap_words]
  congr 1
  rw [show ∀ l : List ℕ, ∀ f : ℕ → List (ℕ × ℕ),
    buckets (l.flatMap f) v = l.flatMap (fun i => buckets (f i) v) by
      intros; simp [buckets, List.filter_flatMap, List.map_flatMap]]
  rw [List.flatMap_assoc]
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro c _
  rw [bucket_flatMap_words]

/-- Bucketing the support records gives exactly section 9 of the layout. -/
theorem initSupportSection_eq (S : StaticData) (G : Graph) (a pn pd M : ℕ) :
    (initConcrete S a (initAbs pn pd M G)).sections.getD 9 [] =
      csrList G.n (buckets (initSupportRecords S)) := by
  change csrList G.n _ = _
  congr 1
  funext v
  exact (initSupportRecords_bucket S v).symm

end MinCostFlow.HierPaths

end
