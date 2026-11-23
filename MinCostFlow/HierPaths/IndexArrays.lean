module

public import MinCostFlow.HierPaths.IndexTerm
public import MinCostFlow.HierPaths.LiveSupport
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The arrays built at the end of `Init`, and their cost

The end of `Init` builds four kinds of arrays from the stored connectors (`HierPaths/Index.lean`):

* the reverse list of each input edge (`revIdx`);
* the connectors of each terminal (`termConns`, `HierPaths/IndexTerm.lean`);
* the support array of each input vertex (`ConnectorSystem.supportArray`,
  `HierPaths/LiveSupport.lean`);
* the connector array of each pair of children (`pairConns`).

Each is a bucketing of a list of keyed records: a record `(key, value)` goes to the bucket of its
key. On a word RAM this is done by counting the records of each key, taking prefix sums, and
filling: `bucketSteps N K = 2 N + K` steps for `N` records and `K` keys. `buckets` gives the result
as a function, and `revIdx_eq_buckets` shows that the reverse lists are the buckets of the list
of occurrences (`occRecs`). The sizes:

* `length_occRecs`: the occurrence records number the total length of the connector walks;
* `sum_length_supportArray_le`: the support arrays together have at most
  `numTerm + ∑_k |verts k|` entries;
* `exists_pairConns`: every matched pair of children is in the connector array of its pair, so
  `exists_surviving_matching_edge` gives an eligible connector there.

`initIndexSteps` adds the four bucketings; `initIndexSteps_le` bounds it by three times the
stored records plus the keys.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

/-- The buckets of the keyed records `recs`: the values of the records with key `key`, in order. -/
def buckets (recs : List (ℕ × ℕ)) (key : ℕ) : List ℕ :=
  (recs.filter fun r => r.1 = key).map Prod.snd

/-- The steps of bucketing `N` records with keys below `K`: count, prefix sums, fill. -/
def bucketSteps (N K : ℕ) : ℕ := 2 * N + K

/-- The occurrence records of the reverse index: `(e, designated endpoint)` for every occurrence
of an input edge `e` on a connector walk. -/
def occRecs (H : HierData) (x b : ℕ) (owner : ℕ → ℕ) (label : ℕ → Option ℕ) : List (ℕ × ℕ) :=
  (connRecs H x b).flatMap fun r =>
    (projectWalk (H.host 0 0).edges owner label r.endA r.hwalk).edges.map fun e => (e, r.endA)

/-- The connector array of the pair of children `c < c'` at depth `t + 1`. -/
def pairConns (H : HierData) (x b t c c' : ℕ) : List ℕ :=
  (List.range (connRecs H x b).length).filter fun k =>
    ((connRecs H x b).getD k default).depth = t ∧ ((connRecs H x b).getD k default).child = c ∧
      ((connRecs H x b).getD k default).child' = c'

/-- The steps of building all arrays at the end of `Init`, for an input graph with `n` vertices
and `m` edges: the reverse lists, the terminal lists (two records per connector), the support
arrays (one record per terminal and per walk vertex) and the pair arrays (one pass). -/
def initIndexSteps (H : HierData) (x b : ℕ) (owner : ℕ → ℕ) (label : ℕ → Option ℕ) (n m : ℕ) : ℕ :=
  bucketSteps (occRecs H x b owner label).length m +
    bucketSteps (2 * (connRecs H x b).length) (2 ^ x) +
    bucketSteps (2 ^ x + ∑ k ∈ Finset.range (connRecs H x b).length,
      ((connSystem H x b owner label).walk k).verts.length) n +
    (connRecs H x b).length

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner HierData

variable {x b : ℕ} {H : HierData}

theorem mem_buckets {recs : List (ℕ × ℕ)} {key v : ℕ} : v ∈ buckets recs key ↔ (key, v) ∈ recs := by
  simp only [buckets, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨r, ⟨hr, rfl⟩, rfl⟩; exact hr
  · intro h; exact ⟨_, ⟨h, rfl⟩, rfl⟩

/-- **The reverse lists are buckets.** The reverse list of `e` is the bucket of `e` in the list of
occurrence records. -/
theorem revIdx_eq_buckets {owner : ℕ → ℕ} {label : ℕ → Option ℕ} (e : ℕ) :
    revIdx H x b owner label e = buckets (occRecs H x b owner label) e := by
  unfold revIdx buckets occRecs
  rw [List.filter_flatMap, List.map_flatMap]
  congr 1
  funext r
  rw [List.filter_map, List.map_map]
  induction (projectWalk (H.host 0 0).edges owner label r.endA r.hwalk).edges with
  | nil => rfl
  | cons a l ih =>
    rw [List.count_cons, List.filter_cons]
    by_cases ha : a = e
    · subst ha
      simp only [beq_self_eq_true, ↓reduceIte, Function.comp, decide_true, List.map_cons]
      rw [List.replicate_succ, ih]
    · simp only [Function.comp, ha, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [show (a == e) = false from beq_eq_false_iff_ne.mpr ha]
      simpa using ih

/-- The occurrence records number the total length of the connector walks. -/
theorem length_occRecs {owner : ℕ → ℕ} {label : ℕ → Option ℕ} :
    (occRecs H x b owner label).length =
      ((connRecs H x b).map fun r =>
        (projectWalk (H.host 0 0).edges owner label r.endA r.hwalk).edges.length).sum := by
  unfold occRecs
  rw [List.length_flatMap]
  simp

theorem mem_pairConns {t c c' k : ℕ} : k ∈ pairConns H x b t c c' ↔
    k < (connRecs H x b).length ∧ ((connRecs H x b).getD k default).depth = t ∧
      ((connRecs H x b).getD k default).child = c ∧
        ((connRecs H x b).getD k default).child' = c' := by
  simp [pairConns]

/-- **Every matched pair is in its pair array.** For a matched pair `q` of the children
`c < c'` of a group at depth `t < leafDepth`, some connector of the array of `(c, c')` has the
endpoints of `q`. -/
theorem exists_pairConns {t g c c' : ℕ} (ht : t < leafDepth x b) (hg : g < numGroups x b t)
    (hc : c ∈ childGroups x b t g) (hc' : c' ∈ childGroups x b t g) (hcc : c < c')
    {q : ℕ × ℕ × List ℕ} (hq : q ∈ H.conn t c c') :
    ∃ k ∈ pairConns H x b t c c', ((connRecs H x b).getD k default).endA = q.1 ∧
      ((connRecs H x b).getD k default).endB = q.2.1 := by
  have hr : (⟨t, g, c, c', q.1, q.2.1, flatWalk H x b t g q.1 q.2.2⟩ : ConnRec) ∈
      connRecs H x b := mem_connRecs.mpr ⟨t, ht, g, hg, c, hc, c', hc', hcc, q, hq, rfl⟩
  obtain ⟨k, hk, hkr⟩ := List.mem_iff_getElem.mp hr
  have hget : (connRecs H x b).getD k default =
      ⟨t, g, c, c', q.1, q.2.1, flatWalk H x b t g q.1 q.2.2⟩ := by
    rw [List.getD_eq_getElem _ _ hk, hkr]
  refine ⟨k, mem_pairConns.mpr ⟨hk, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> rw [hget]

/-- A sum over keys of the sizes of the fibers of `f` in `R` is at most `|R|`. -/
private theorem sum_card_fiber_le (R W : Finset ℕ) (f : ℕ → ℕ) :
    ∑ w ∈ W, (R.filter fun r => f r = w).card ≤ R.card := by
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_card (Finset.biUnion_subset.mpr fun w _ => Finset.filter_subset _ _)
  · intro w _ w' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro r hr hr'
    rw [Finset.mem_filter] at hr hr'
    exact hne (hr.2.symm.trans hr'.2)

private theorem length_filter_range (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((List.range n).filter fun k => p k).length = ((Finset.range n).filter fun k => p k).card := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _), List.toFinset_filter,
    List.toFinset_range]
  rfl

/-- **The size of the support arrays.** Together they have at most `numTerm + ∑_k |verts k|`
entries, one per terminal and one per vertex occurrence on a connector walk. -/
theorem sum_length_supportArray_le (C : ConnectorSystem) (n : ℕ) :
    ∑ w ∈ Finset.range n, (C.supportArray w).length ≤
      C.numTerm + ∑ k ∈ Finset.range C.numConn, (C.walk k).verts.length := by
  have hlen : ∀ w, (C.supportArray w).length =
      ((Finset.range C.numTerm).filter fun t => C.owner t = w).card +
        ∑ k ∈ Finset.range C.numConn,
          ((Finset.range (C.walk k).verts.length).filter
            fun pos => (C.walk k).verts.getD pos 0 = w).card := by
    intro w
    simp only [ConnectorSystem.supportArray, List.length_append, List.length_map,
      List.length_flatMap, ConnectorSystem.positionsOn]
    rw [length_filter_range]
    congr 1
  simp only [hlen, Finset.sum_add_distrib]
  apply Nat.add_le_add
  · exact (sum_card_fiber_le _ _ _).trans (Finset.card_range _).le
  · rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun k _ =>
      (sum_card_fiber_le _ _ _).trans (Finset.card_range _).le

/-- **The cost of building the arrays is linear in the stored records.** -/
theorem initIndexSteps_le {owner : ℕ → ℕ} {label : ℕ → Option ℕ} (n m : ℕ) :
    initIndexSteps H x b owner label n m ≤
      3 * ((occRecs H x b owner label).length + 2 * (connRecs H x b).length +
        (2 ^ x + ∑ k ∈ Finset.range (connRecs H x b).length,
          ((connSystem H x b owner label).walk k).verts.length)) + (m + 2 ^ x + n) := by
  unfold initIndexSteps bucketSteps
  omega

/-- **Every stored walk has at most `λ` edges** (`length_le_lamOf`, with the numbers of
`HierPaths/Params.lean`). -/
theorem connSystem_walk_length_le (hb : 0 < b) (hH : H.IsValid x b) {a dd m : ℕ}
    (hB : H.Bounds x b (lvlBound (hOf dd) (uOf a m)) (lvlBound (hOf dd) (uOf a m))
      (lvlBound (hOf dd) (uOf a m)))
    (hh : leafDepth x b ≤ depthOf m) {owner : ℕ → ℕ} {label : ℕ → Option ℕ} {k : ℕ}
    (hk : k < (connSystem H x b owner label).numConn) :
    ((connSystem H x b owner label).walk k).edges.length ≤ lamOf a dd m := by
  have hr := getD_mem_connRecs (H := H) (x := x) (b := b) hk
  obtain ⟨t, ht, g, hg, c, hc, c', hc', hcc, q, hq, hrq⟩ := mem_connRecs.mp hr
  have hs := one_lt_groupSize_of_lt_leafDepth hb ht
  change (projectWalk (H.host 0 0).edges owner label ((connRecs H x b).getD k default).endA
    ((connRecs H x b).getD k default).hwalk).edges.length ≤ _
  rw [hrq]
  exact (length_projectWalk_le _ _ _ _ _).trans
    (length_le_lamOf hH hB (by omega) hs hg hc hc' hcc hq)

end MinCostFlow.HierPaths
