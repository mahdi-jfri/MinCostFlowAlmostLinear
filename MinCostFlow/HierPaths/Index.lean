module

public import MinCostFlow.HierPaths.Flat
public import MinCostFlow.HierPaths.Live

/-!
# The connector system and the reverse index

At the end of `Init`, the data structure numbers all connectors of all depths above the leaves
(`connRecs`), stores for each its two terminals and its walk in the input graph (the projection of
its root walk, `HierPaths/Flat.lean`), and builds the arrays used by `Delete` and `GetPath`. This
file gives the connectors as a `ConnectorSystem` (`HierPaths/Live.lean`) and the *reverse index*:
for each input edge `e`, the designated endpoints of the connector occurrences on `e`.

* `connSystem_fitsGraph`: the connectors fit the input graph: endpoints are terminals and each
  walk is a walk of `G` between the owners of its endpoints;
* `mem_revIdx`, `reverseIndexRule_of_revIdx`: if every terminal listed for a deleted edge is lost,
  the reverse-index rule of `Live.lean` holds;
* `length_revIdx_le`: a reverse list has at most `ξ` entries (by `load_le_xiOf`).

The designated endpoint of a connector is its first endpoint, the smaller terminal number: the
first endpoint lies in the child `c` and the second in `c'`, with `c < c'`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- A stored connector: its depth `t`, the group `g` at depth `t`, the children `c < c'`, its
endpoints `endA ∈ c` and `endB ∈ c'`, and its walk in the root host. -/
structure ConnRec where
  depth : ℕ
  group : ℕ
  child : ℕ
  child' : ℕ
  endA : ℕ
  endB : ℕ
  hwalk : List ℕ
  deriving Inhabited

/-- The connectors of the children `c < c'` of group `g` at depth `t`. -/
def pairRecs (H : HierData) (x b t g c c' : ℕ) : List ConnRec :=
  if c < c' then
    (H.conn t c c').map fun q => ⟨t, g, c, c', q.1, q.2.1, flatWalk H x b t g q.1 q.2.2⟩
  else []

/-- All connectors, in the order: depth, group, first child, second child, matching. -/
def connRecs (H : HierData) (x b : ℕ) : List ConnRec :=
  (List.range (leafDepth x b)).flatMap fun t => (List.range (numGroups x b t)).flatMap fun g =>
    (childList x b t g).flatMap fun c => (childList x b t g).flatMap fun c' =>
      pairRecs H x b t g c c'

/-- The connector system of the hierarchy, for the owners and labels of the root host. -/
def connSystem (H : HierData) (x b : ℕ) (owner : ℕ → ℕ) (label : ℕ → Option ℕ) :
    ConnectorSystem where
  numTerm := 2 ^ x
  owner := owner
  numConn := (connRecs H x b).length
  endA k := ((connRecs H x b).getD k default).endA
  endB k := ((connRecs H x b).getD k default).endB
  desigB _ := false
  walk k := projectWalk (H.host 0 0).edges owner label ((connRecs H x b).getD k default).endA
    ((connRecs H x b).getD k default).hwalk

/-- The reverse list of the input edge `e`: the designated endpoint of a connector once for each
occurrence of `e` on its walk. -/
def revIdx (H : HierData) (x b : ℕ) (owner : ℕ → ℕ) (label : ℕ → Option ℕ) (e : ℕ) : List ℕ :=
  (connRecs H x b).flatMap fun r =>
    List.replicate ((projectWalk (H.host 0 0).edges owner label r.endA r.hwalk).edges.count e)
      r.endA

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner HierData

variable {x b : ℕ} {H : HierData}

/-- The stored connectors, read as start vertices and root walks, are the family `flatConnFam`. -/
theorem map_connRecs : (connRecs H x b).map (fun r => (r.endA, r.hwalk)) = flatConnFam H x b := by
  simp only [connRecs, flatConnFam, flatFam, connFam, List.map_flatMap]
  congr 1; funext t; congr 1; funext g; congr 1; funext c; congr 1; funext c'
  unfold pairRecs pairFam
  split_ifs <;> simp

theorem childGroups_lt_numGroups {t a c : ℕ} (ha : a < numGroups x b t)
    (hc : c ∈ childGroups x b t a) : c < numGroups x b (t + 1) := by
  have hm : c * groupSize x b (t + 1) ∈ members x b t a := by
    rw [members_eq_biUnion_childGroups]
    refine Finset.mem_biUnion.mpr ⟨c, hc, ?_⟩
    simp only [members, Finset.mem_Ico, Nat.succ_mul]
    exact ⟨le_rfl, Nat.lt_add_of_pos_right groupSize_pos⟩
  have hlt := Finset.mem_range.mp (members_subset_range ha hm)
  have hg : groupOf x b (t + 1) (c * groupSize x b (t + 1)) = c := by
    unfold groupOf
    exact Nat.mul_div_cancel _ groupSize_pos
  rw [← hg]
  exact groupOf_lt_numGroups hlt

/-- What a stored connector is. -/
theorem mem_connRecs {r : ConnRec} : r ∈ connRecs H x b ↔
    ∃ t < leafDepth x b, ∃ g < numGroups x b t, ∃ c ∈ childGroups x b t g,
      ∃ c' ∈ childGroups x b t g, c < c' ∧ ∃ q ∈ H.conn t c c',
        r = ⟨t, g, c, c', q.1, q.2.1, flatWalk H x b t g q.1 q.2.2⟩ := by
  simp only [connRecs, List.mem_flatMap, List.mem_range, mem_childList]
  constructor
  · rintro ⟨t, ht, g, hg, c, hc, c', hc', hr⟩
    unfold pairRecs at hr
    split_ifs at hr with hcc
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      exact ⟨t, ht, g, hg, c, hc, c', hc', hcc, q, hq, rfl⟩
    · simp at hr
  · rintro ⟨t, ht, g, hg, c, hc, c', hc', hcc, q, hq, rfl⟩
    refine ⟨t, ht, g, hg, c, hc, c', hc', ?_⟩
    unfold pairRecs
    simp only [eq_true hcc, ↓reduceIte]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩

/-- The facts about one stored connector: its endpoints are matched terminals of the two
children, and its root walk is a walk of the root host between them. -/
theorem connRec_spec (hb : 0 < b) (hH : H.IsValid x b) {r : ConnRec}
    (hr : r ∈ connRecs H x b) :
    r.endA ∈ members x b (r.depth + 1) r.child ∧ r.endB ∈ members x b (r.depth + 1) r.child' ∧
      r.child < r.child' ∧ r.endA < 2 ^ x ∧ r.endB < 2 ^ x ∧
      IsEdgeWalk (H.host 0 0).edges r.endA r.endB r.hwalk := by
  obtain ⟨t, ht, g, hg, c, hc, c', hc', hcc, q, hq, rfl⟩ := mem_connRecs.mp hr
  have hs := one_lt_groupSize_of_lt_leafDepth hb ht
  obtain ⟨_, h1, _, h2⟩ := hH.conn_perfect t g hs hg c hc c' hc' hcc
  have hA : q.1 ∈ members x b (t + 1) c := by
    rw [← h1]; exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨q, hq, rfl⟩)
  have hB' : q.2.1 ∈ members x b (t + 1) c' := by
    rw [← h2]; exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨q, hq, rfl⟩)
  exact ⟨hA, hB', hcc,
    Finset.mem_range.mp (members_subset_range (childGroups_lt_numGroups hg hc) hA),
    Finset.mem_range.mp (members_subset_range (childGroups_lt_numGroups hg hc') hB'),
    flat_connector_isEdgeWalk hH hs hg hc hc' hcc hq⟩

theorem getD_mem_connRecs {k : ℕ} (hk : k < (connRecs H x b).length) :
    (connRecs H x b).getD k default ∈ connRecs H x b := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

/-- **The connectors fit the input graph.** When the owners and labels project the root host onto
`G` and every terminal has an owner in `G`, each connector joins two terminals and its stored
walk is a walk of `G` between their owners. -/
theorem connSystem_fitsGraph (hb : 0 < b) (hH : H.IsValid x b) {G : Graph} {owner : ℕ → ℕ}
    {label : ℕ → Option ℕ} (hproj : IsProjection G (H.host 0 0).edges owner label)
    (hown : ∀ p < 2 ^ x, owner p < G.n) : (connSystem H x b owner label).FitsGraph G := by
  refine ⟨hown, fun k hk => ?_⟩
  obtain ⟨_, _, _, hA, hB', hW⟩ := connRec_spec hb hH (getD_mem_connRecs hk)
  exact ⟨hA, hB', projectWalk_isWalk hproj hW (hown _ hA)⟩

/-- The designated endpoint of every connector whose walk uses `e` is on the reverse list of
`e`. -/
theorem mem_revIdx {owner : ℕ → ℕ} {label : ℕ → Option ℕ} {k : ℕ}
    (hk : k < (connSystem H x b owner label).numConn) {e : ℕ}
    (he : e ∈ ((connSystem H x b owner label).walk k).edges) :
    (connSystem H x b owner label).desig k ∈ revIdx H x b owner label e := by
  simp only [ConnectorSystem.desig, connSystem, Bool.false_eq_true, ↓reduceIte, revIdx,
    List.mem_flatMap]
  refine ⟨_, getD_mem_connRecs hk, List.mem_replicate.mpr ⟨?_, rfl⟩⟩
  exact (List.count_pos_iff.mpr he).ne'

/-- **The reverse-index rule.** If every terminal on the reverse list of a deleted edge is lost,
the connector system meets the reverse-index rule of `HierPaths/Live.lean`. -/
theorem reverseIndexRule_of_revIdx {owner : ℕ → ℕ} {label : ℕ → Option ℕ} {D surv : Finset ℕ}
    (h : ∀ e ∈ D, ∀ t ∈ revIdx H x b owner label e, t ∉ surv) :
    (connSystem H x b owner label).ReverseIndexRule D surv :=
  fun _ hk e he heD => h e heD _ (mem_revIdx hk he)

/-- The length of a reverse list is the total number of occurrences of `e` on connector walks. -/
theorem length_revIdx {owner : ℕ → ℕ} {label : ℕ → Option ℕ} (e : ℕ) :
    (revIdx H x b owner label e).length =
      walkLoad (projectFamily (H.host 0 0).edges owner label (flatConnFam H x b)) e := by
  rw [← map_connRecs]
  unfold revIdx walkLoad projectFamily
  rw [List.length_flatMap, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro r _
  simp

/-- **A reverse list has at most `ξ` entries** (`load_le_xiOf`, with the numbers of
`HierPaths/Params.lean`). -/
theorem length_revIdx_le (hb : 0 < b) (hH : H.IsValid x b) {a dd m : ℕ}
    (hB : H.Bounds x b (lvlBound (hOf dd) (uOf a m)) (lvlBound (hOf dd) (uOf a m))
      (lvlBound (hOf dd) (uOf a m)))
    (hh : leafDepth x b ≤ depthOf m) (hBb : 2 ^ b ≤ branchOf m) {owner : ℕ → ℕ}
    {label : ℕ → Option ℕ} (hinj : ∀ j j' e, label j = some e → label j' = some e → j = j')
    (e : ℕ) : (revIdx H x b owner label e).length ≤ xiOf a dd m := by
  rw [length_revIdx]
  exact load_le_xiOf hb hH hB hh hBb hinj e

end MinCostFlow.HierPaths
