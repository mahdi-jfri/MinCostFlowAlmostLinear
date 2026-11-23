module

public import MinCostFlow.DynSpanner.Program.DynSpannerApplyU
public import MinCostFlow.DynSpanner.Program.DynSpannerStepMid

/-!
# The words `minH` and the buckets after the update `u`

`dsApplyUStmt` changes the words `minH` by `minHAfter u` and the buckets by `delErase u`. This
file shows that the result describes the levels after the update, for a deletion and for a split
(`minH_after_update`). The edge sets after the update are given by `delSet u`: a deletion of `e`
erases `e`, and a split keeps all edges (`applyUpdate_E_delSet`).
-/

namespace MinCostFlow.DynSpanner.Program

open MinCostFlow.DynSpanner

@[expose] public section

/-- The edge set after a deletion or a split, from the edge set before. -/
def delSet : Update → Finset ℕ → Finset ℕ
  | .delete e, S => S.erase e
  | _, S => S

/-- For a deletion or a split, `u` changes the edge set of a graph by `delSet u`. -/
theorem applyUpdate_E_delSet {u : Update} (hu : isDelOrSplit u) (G : MGraph) :
    (G.applyUpdate u).E = delSet u G.E := by
  cases u with
  | insert _ _ _ => exact absurd hu (by simp [isDelOrSplit])
  | delete e => rfl
  | split v v' St Sh => rfl

/-- The level `H_mid i` of `step` has the edge set `delSet u E(H_i)`. -/
theorem mid_E_delSet {u : Update} (hu : isDelOrSplit u) (H : MGraph) :
    (H.applyBatch (restrictUpdate u H)).E = delSet u H.E := by
  rw [applyBatch_restrict_E hu, applyUpdate_E_delSet hu]

/-- After the update, the words `minH` and the buckets describe the new levels. The hypotheses
are the facts of `DynSpannerStateAt` about `minH` and the buckets before the update, with the
words `m` and `m'` before and after; the levels after the update have the edge sets
`delSet u E(H_i)`, and a deleted edge is below `eCap` (it is an edge of `G`). -/
theorem minH_after_update {u : Update} (hu : isDelOrSplit u) {L eCap : ℕ} {E : Finset ℕ}
    {m m' : ℕ → ℕ} {H_level H_mid : Fin (L + 1) → MGraph} {B : ℕ → List ℕ}
    (hm0 : ∀ e' < eCap, m e' = 0 ↔ e' ∉ E)
    (hmin : ∀ e' < eCap, e' ∈ E → ∃ i : Fin (L + 1), m e' = i.1 + 1 ∧ e' ∈ (H_level i).E ∧
      ∀ k : Fin (L + 1), k.1 < i.1 → e' ∉ (H_level k).E)
    (hB : ∀ i : Fin (L + 1), ∀ e', e' ∈ B i.1 ↔ e' ∈ E ∧ m e' = i.1 + 1)
    (hnd : ∀ i : Fin (L + 1), (B i.1).Nodup)
    (hm' : ∀ e' < eCap, m' e' = minHAfter u (m e') e')
    (hmid : ∀ i, (H_mid i).E = delSet u (H_level i).E)
    (hcap : ∀ e, u = .delete e → e < eCap) :
    (∀ e' < eCap,
      (m' e' = 0 ↔ e' ∉ delSet u E) ∧
      (e' ∈ delSet u E → ∃ i : Fin (L + 1), m' e' = i.1 + 1 ∧ e' ∈ (H_mid i).E ∧
        ∀ k : Fin (L + 1), k.1 < i.1 → e' ∉ (H_mid k).E)) ∧
    (∀ i : Fin (L + 1), ∀ e', e' < eCap →
      (e' ∈ delErase u (B i.1) ↔ e' ∈ delSet u E ∧ m' e' = i.1 + 1)) := by
  cases u with
  | insert _ _ _ => exact absurd hu (by simp [isDelOrSplit])
  | delete e =>
    -- `minHAfter` sets the word of `e` to `0` and keeps the others.
    refine minH_after_delete hm0 hmin hB hnd ?_ ?_ hmid
    · simpa [minHAfter] using hm' e (hcap e rfl)
    · intro e' he' hne
      simpa [minHAfter, hne] using hm' e' he'
  | split v v' St Sh =>
    refine ⟨fun e' he' => ?_, fun i e' he' => ?_⟩
    · have hw : m' e' = m e' := by simpa [minHAfter] using hm' e' he'
      simp only [delSet, hw]
      refine ⟨hm0 e' he', fun hE => ?_⟩
      obtain ⟨i, hi, hiE, hfirst⟩ := hmin e' he' hE
      exact ⟨i, hi, by rw [hmid]; exact hiE, fun k hk => by rw [hmid]; exact hfirst k hk⟩
    · have hw : m' e' = m e' := by simpa [minHAfter] using hm' e' he'
      simp only [delErase, delSet, hw]
      exact hB i e'

end

end MinCostFlow.DynSpanner.Program
