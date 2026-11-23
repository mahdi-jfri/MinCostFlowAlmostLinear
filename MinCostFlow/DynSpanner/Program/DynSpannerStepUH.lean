module

public import MinCostFlow.DynSpanner.Defs

/-!
# The new edge set of `H` in a step with `0 < j`

In `step` with `0 < j`, the levels below `j` stay (after the update), level `j` becomes `H_j`
with the edges of `J̃`, and the levels above `j` become empty. So the new edge set of `H` is the
union of the old levels below `j` and the edges of `J̃` (`unionEdgesLt_rebuild`). Hence an edge
of `H` is deleted when its smallest level is at least `j` and it is not in `J̃`
(`mem_rebuild_del`), and an edge of `J̃` is inserted when it is not in `H` (`mem_rebuild_ins`).
These are the sets that `dsDelAllStmt` and `dsInsRecordsStmt` write.
-/

namespace MinCostFlow.DynSpanner.Program

open MinCostFlow.DynSpanner

@[expose] public section

/-- The levels after a rebuild of level `j`. -/
def rebuildLevels {L : ℕ} (H_mid : Fin (L + 1) → MGraph) (Hj G' : MGraph) (j : ℕ) :
    Fin (L + 1) → MGraph := fun i =>
  if i.1 < j then H_mid i else if i.1 = j then Hj else emptyGraphOn G'

lemma unionEdgesLt_rebuild {L : ℕ} (H_mid : Fin (L + 1) → MGraph) (Hj G' : MGraph) {j : ℕ}
    (hj : j ≤ L) :
    unionEdgesLt (rebuildLevels H_mid Hj G' j) (L + 1) = unionEdgesLt H_mid j ∪ Hj.E := by
  ext e
  simp only [unionEdgesLt, rebuildLevels, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨i, hi, he⟩
    by_cases h1 : i.1 < j
    · exact Or.inl ⟨i, h1, by simpa [h1] using he⟩
    · by_cases h2 : i.1 = j
      · exact Or.inr (by simpa [h1, h2] using he)
      · simp [h1, h2, emptyGraphOn] at he
  · rintro (⟨i, hi, he⟩ | he)
    · exact ⟨i, i.2, by simpa [hi] using he⟩
    · exact ⟨⟨j, by omega⟩, by omega, by simpa using he⟩

/-- The deleted edges: in `H` but neither in a level below `j` nor in `J̃`. -/
lemma mem_rebuild_del {L : ℕ} (H_mid : Fin (L + 1) → MGraph) (Hj G' : MGraph) {j : ℕ}
    (hj : j ≤ L) (E : Finset ℕ) (e : ℕ) :
    e ∈ E \ unionEdgesLt (rebuildLevels H_mid Hj G' j) (L + 1) ↔
      e ∈ E ∧ e ∉ unionEdgesLt H_mid j ∧ e ∉ Hj.E := by
  rw [unionEdgesLt_rebuild H_mid Hj G' hj]
  simp [not_or]

/-- The inserted edges: in `J̃` (or a level below `j`) but not in `H`. When the levels below `j`
are in `H`, these are the edges of `J̃` outside `H`. -/
lemma mem_rebuild_ins {L : ℕ} (H_mid : Fin (L + 1) → MGraph) (Hj G' : MGraph) {j : ℕ}
    (hj : j ≤ L) (E : Finset ℕ) (hsub : unionEdgesLt H_mid j ⊆ E) (e : ℕ) :
    e ∈ unionEdgesLt (rebuildLevels H_mid Hj G' j) (L + 1) \ E ↔ e ∈ Hj.E ∧ e ∉ E := by
  rw [unionEdgesLt_rebuild H_mid Hj G' hj]
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨h | h, hE⟩
    · exact absurd (hsub h) hE
    · exact ⟨h, hE⟩
  · rintro ⟨h, hE⟩
    exact ⟨Or.inr h, hE⟩

end

end MinCostFlow.DynSpanner.Program
