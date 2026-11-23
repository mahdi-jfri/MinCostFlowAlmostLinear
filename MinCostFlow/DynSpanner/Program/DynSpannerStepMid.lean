module

public import MinCostFlow.DynSpanner.Defs

/-!
# Edge sets after the update `u`, before the rebuild

The first part of `step` applies the update `u` to `G` and to each level:
`G' = G.applyUpdate u` and `H_mid i = (H_level i).applyBatch (restrictUpdate u (H_level i))`.
Theorem 8.2 only uses deletions and splits (`isDelOrSplit u`). For these, no edge is added, and a
level loses exactly the edges that `G` loses. So the levels need no stored copies: the edge set
of `H_mid i` is `E(H_i) ∩ E(G')` (`applyBatch_restrict_E_inter`), and the same holds for the
union of the levels below `j` (`unionEdgesLt_mid`). The program uses this to update only the
buckets of `minH` (one `dsLevelsDeleteStmt` for a deletion, nothing for a split).
-/

namespace MinCostFlow.DynSpanner.Program

open MinCostFlow.DynSpanner

@[expose] public section

/-- For a deletion or a split, the restricted update changes the edge set of `H` in the same way
as `u` itself. A deletion of an edge outside `H` is dropped by `restrictUpdate`, and erasing an
edge that is not there changes nothing. A split keeps all edges. -/
theorem applyBatch_restrict_E {u : Update} (hu : isDelOrSplit u) (H : MGraph) :
    (H.applyBatch (restrictUpdate u H)).E = (H.applyUpdate u).E := by
  cases u with
  | insert _ _ _ => exact absurd hu (by simp [isDelOrSplit])
  | delete e =>
    by_cases he : e ∈ H.E
    · simp [restrictUpdate, he, MGraph.applyBatch, MGraph.applyUpdate]
    · simp [restrictUpdate, he, MGraph.applyBatch, MGraph.applyUpdate]
  | split v v' St Sh => simp [restrictUpdate, MGraph.applyBatch, MGraph.applyUpdate]

/-- A deletion or a split does not add edges. -/
theorem applyUpdate_E_subset {u : Update} (hu : isDelOrSplit u) (G : MGraph) :
    (G.applyUpdate u).E ⊆ G.E := by
  cases u with
  | insert _ _ _ => exact absurd hu (by simp [isDelOrSplit])
  | delete e => exact Finset.erase_subset e G.E
  | split v v' St Sh => exact subset_rfl

/-- For a subgraph `H` of `G` (on edges), the level after the update keeps the edges of `H`
that are still in `G'`. -/
theorem applyBatch_restrict_E_inter {u : Update} (hu : isDelOrSplit u) {G H : MGraph}
    (hHG : H.E ⊆ G.E) :
    (H.applyBatch (restrictUpdate u H)).E = H.E ∩ (G.applyUpdate u).E := by
  rw [applyBatch_restrict_E hu]
  cases u with
  | insert _ _ _ => exact absurd hu (by simp [isDelOrSplit])
  | delete e =>
    ext f
    simp only [MGraph.applyUpdate, Finset.mem_erase, Finset.mem_inter]
    constructor
    · rintro ⟨hne, hf⟩; exact ⟨hf, hne, hHG hf⟩
    · rintro ⟨hf, hne, _⟩; exact ⟨hne, hf⟩
  | split v v' St Sh =>
    simp only [MGraph.applyUpdate]
    exact (Finset.inter_eq_left.mpr hHG).symm

/-- The union of the levels below `j` after the update is the old union intersected with
`E(G')`, when every level is a subgraph of `G` on edges. -/
theorem unionEdgesLt_mid {L : ℕ} {u : Update} (hu : isDelOrSplit u) {G : MGraph}
    (H_level : Fin (L + 1) → MGraph) (hsub : ∀ i, (H_level i).E ⊆ G.E) (j : ℕ) :
    unionEdgesLt (fun i => (H_level i).applyBatch (restrictUpdate u (H_level i))) j =
      unionEdgesLt H_level j ∩ (G.applyUpdate u).E := by
  ext f
  simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_inter, applyBatch_restrict_E_inter hu (hsub _)]
  constructor
  · rintro ⟨i, hi, hf, hG⟩; exact ⟨⟨i, hi, hf⟩, hG⟩
  · rintro ⟨⟨i, hi, hf⟩, hG⟩; exact ⟨i, hi, hf, hG⟩

/-- The words `minH` after the deletion of an edge `e`. Before, the word of an edge `e' < eCap`
is `0` exactly off `E(H)`, and otherwise one plus the smallest level holding `e'`; bucket `i`
holds the edges of `H` whose word is `i + 1`, without repeats. `dsLevelsDeleteStmt` sets the word of `e` to `0`,
keeps the other words, and erases `e` from its bucket. The levels lose `e` too. Then the same
facts hold for `E(H) \ {e}`, the new levels and the new buckets. -/
theorem minH_after_delete {L eCap e : ℕ} {E : Finset ℕ} {m m' : ℕ → ℕ}
    {H_level H_mid : Fin (L + 1) → MGraph} {B : ℕ → List ℕ}
    (hm0 : ∀ e' < eCap, m e' = 0 ↔ e' ∉ E)
    (hmin : ∀ e' < eCap, e' ∈ E → ∃ i : Fin (L + 1), m e' = i.1 + 1 ∧ e' ∈ (H_level i).E ∧
      ∀ k : Fin (L + 1), k.1 < i.1 → e' ∉ (H_level k).E)
    (hB : ∀ i : Fin (L + 1), ∀ e', e' ∈ B i.1 ↔ e' ∈ E ∧ m e' = i.1 + 1)
    (hnd : ∀ i : Fin (L + 1), (B i.1).Nodup) (he0 : m' e = 0) (hfr : ∀ e' < eCap, e' ≠ e → m' e' = m e')
    (hmid : ∀ i, (H_mid i).E = (H_level i).E.erase e) :
    (∀ e' < eCap,
      (m' e' = 0 ↔ e' ∉ E.erase e) ∧
      (e' ∈ E.erase e → ∃ i : Fin (L + 1), m' e' = i.1 + 1 ∧ e' ∈ (H_mid i).E ∧
        ∀ k : Fin (L + 1), k.1 < i.1 → e' ∉ (H_mid k).E)) ∧
    (∀ i : Fin (L + 1), ∀ e', e' < eCap →
      (e' ∈ (B i.1).erase e ↔ e' ∈ E.erase e ∧ m' e' = i.1 + 1)) := by
  refine ⟨fun e' he' => ?_, fun i e' he' => ?_⟩
  · by_cases hee : e' = e
    · subst hee
      simp only [he0, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true,
        IsEmpty.forall_iff, and_true]
    · rw [hfr e' he' hee]
      simp only [Finset.mem_erase, hee, ne_eq, not_false_eq_true, true_and]
      refine ⟨hm0 e' he', fun hE => ?_⟩
      obtain ⟨i, hi, hiE, hfirst⟩ := hmin e' he' hE
      refine ⟨i, hi, ?_, fun k hk => ?_⟩
      · rw [hmid]; exact Finset.mem_erase.mpr ⟨hee, hiE⟩
      · rw [hmid]; exact fun h => hfirst k hk (Finset.mem_erase.mp h).2
  · by_cases hee : e' = e
    · subst hee
      simp [(hnd i).mem_erase_iff]
    · rw [hfr e' he' hee, List.mem_erase_of_ne hee, hB i e']
      simp [hee]

end

end MinCostFlow.DynSpanner.Program
