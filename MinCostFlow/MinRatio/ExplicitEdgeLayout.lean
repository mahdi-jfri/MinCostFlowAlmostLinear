module

public import MinCostFlow.MinRatio.PathSwapWords
import MinCostFlow.MinRatio.CycleDetectorAccounting

/-!
# Packed explicit cycle edges

Algorithm 2 (page 29) uses a scaled cycle to update signed flow and
its absolute-value account. Each explicit occurrence uses two words:
the edge name and its direction. Reading these words lets a scan count
each direction without storing a circulation vector.
-/

public section

namespace MinCostFlow.MinRatio

/-- Consecutive words store the explicit name and direction bit. -/
@[expose] def ExplicitEdgesAt (mem : ℕ → ℕ) (base : ℕ) (edges : List (ℕ × Bool)) : Prop :=
  PathPairsAt mem base (edges.map fun row => (row.1, if row.2 then 1 else 0))

/-- The two words of a row recover the name and traversal direction. -/
theorem ExplicitEdgesAt.read {mem : ℕ → ℕ} {base i : ℕ} {edges : List (ℕ × Bool)}
    (h : ExplicitEdgesAt mem base edges) (hi : i < edges.length) :
    mem (base + 2 * i) = edges[i].1 ∧
      mem (base + 2 * i + 1) = (if edges[i].2 then 1 else 0) := by
  have hw := h i (by simpa only [List.length_map] using hi)
  simpa only [List.getElem_map] using hw

/-- Counting the next packed row extends the exact directional count
for the scanned prefix. -/
theorem ExplicitEdgesAt.count_step {mem : ℕ → ℕ} {base i : ℕ} {edges : List (ℕ × Bool)}
    (h : ExplicitEdgesAt mem base edges) (hi : i < edges.length) (e : ℕ) (dir : Bool) :
    (edges.take (i + 1)).count (e, dir) =
      (edges.take i).count (e, dir) +
        if mem (base + 2 * i) = e ∧ mem (base + 2 * i + 1) = (if dir then 1 else 0)
        then 1 else 0 := by
  rw [List.take_succ_eq_append_getElem hi, explicitEdge_count_snoc, (h.read hi).1, (h.read hi).2]
  obtain ⟨name, direction⟩ := edges[i]
  cases direction <;> cases dir <;> simp [Prod.mk.injEq]

/-- Memory agreement on the packed slice preserves all explicit occurrences. -/
theorem ExplicitEdgesAt.congr {mem mem' : ℕ → ℕ} {base : ℕ} {edges : List (ℕ × Bool)}
    (h : ExplicitEdgesAt mem base edges)
    (hframe : ∀ x, base ≤ x → x < base + 2 * edges.length → mem' x = mem x) :
    ExplicitEdgesAt mem' base edges := by
  intro i hi
  have hi' : i < edges.length := by simpa only [List.length_map] using hi
  exact ⟨(hframe _ (by omega) (by omega)).trans (h i hi).1,
    (hframe _ (by omega) (by omega)).trans (h i hi).2⟩

/-- A scan of a prefix uses the original route address and layout. -/
theorem ExplicitEdgesAt.take {mem : ℕ → ℕ} {base : ℕ} {edges : List (ℕ × Bool)}
    (h : ExplicitEdgesAt mem base edges) (n : ℕ) :
    ExplicitEdgesAt mem base (edges.take n) := by
  intro i hi
  simp only [List.length_map, List.length_take] at hi
  have hlen := lt_of_lt_of_le hi (Nat.min_le_right _ _)
  simpa only [List.getElem_map, List.getElem_take] using h.read hlen

/-- Both directional counters vanish exactly when the prefix has no
occurrence of the edge's name. -/
theorem explicitEdge_counts_zero_iff (edges : List (ℕ × Bool)) (e : ℕ) :
    edges.count (e, true) = 0 ∧ edges.count (e, false) = 0 ↔ e ∉ edges.map Prod.fst := by
  simp only [List.count_eq_zero]
  constructor
  · rintro ⟨ht, hf⟩ hm
    obtain ⟨⟨name, dir⟩, hmem, rfl⟩ := List.mem_map.mp hm
    cases dir
    · exact hf hmem
    · exact ht hmem
  · intro hn
    exact ⟨fun hm => hn (List.mem_map.mpr ⟨(e, true), hm, rfl⟩),
      fun hm => hn (List.mem_map.mpr ⟨(e, false), hm, rfl⟩)⟩

/-- At the next row, the set of scanned names gains only that row's name. -/
theorem explicitEdge_mem_prefix_succ (edges : List (ℕ × Bool)) {i e : ℕ}
    (hi : i < edges.length) :
    e ∈ (edges.take (i + 1)).map Prod.fst ↔
      e ∈ (edges.take i).map Prod.fst ∨ e = edges[i].1 := by
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.mem_append]
  simp

/-- The prefix test selects exactly one indexed row per explicit edge.
This connects the machine predicate to the first-occurrence invariant. -/
theorem explicitEdge_unique_prefix_row (edges : List (ℕ × Bool)) (e : ℕ)
    (he : e ∈ edges.map Prod.fst) :
    ∃! i : ℕ, ∃ hi : i < edges.length,
      edges[i].1 = e ∧ e ∉ (edges.take i).map Prod.fst := by
  have hprefix (i : ℕ) (hi : i < edges.length) :
      e ∉ (edges.take i).map Prod.fst ↔
        ∀ j : ℕ, ∀ hj : j < i, (edges[j]'(lt_trans hj hi)).1 ≠ e := by
    constructor
    · intro h j hj heq
      have hj' : j < (edges.take i).length := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
        exact hj
      apply h
      exact List.mem_map.mpr ⟨(edges.take i)[j], List.getElem_mem hj',
        by simpa only [List.getElem_take] using heq⟩
    · intro h hm
      obtain ⟨row, hr, hn⟩ := List.mem_map.mp hm
      obtain ⟨j, hj, hjr⟩ := List.mem_iff_getElem.mp hr
      have hj' : j < i := by
        rwa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] at hj
      exact h j hj' (by simpa only [List.getElem_take] using (congrArg Prod.fst hjr).trans hn)
  obtain ⟨i, ⟨hi, hn, hp⟩, hu⟩ := explicitEdge_unique_first edges e he
  refine ⟨i, ⟨hi, hn, (hprefix i hi).2 hp⟩, ?_⟩
  rintro j ⟨hj, hjn, hjp⟩
  exact hu j ⟨hj, hjn, (hprefix j hj).1 hjp⟩

end MinCostFlow.MinRatio
