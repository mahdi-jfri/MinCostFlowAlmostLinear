module

public import MinCostFlow.LSF.Lemma54
public import MinCostFlow.Bundle.TourSplit
public import MinCostFlow.SparseCore.QuotientStepBound
import MinCostFlow.SparseCore.CoreModel
import MinCostFlow.LSF.Lemma54Split

/-!
# Forest edits in one LSF update

Apply the input edit first, including a cut if the input deletes a
forest edge. The remaining changes are cuts of released edges.
-/

public section

namespace MinCostFlow.Bundle

open MinCostFlow.LSF MinCostFlow.SparseCore

/-- The forest after the input edit and before the additional root cuts. -/
@[expose] def forestAfterInput (F : MGraph) (u : Update) : MGraph :=
  match u with
  | .insert .. => F
  | .delete e => eraseForestEdge F e
  | .split v v' St Sh => F.applyUpdate (.split v v' St Sh)

/-- Applying a list of forest cuts erases exactly the listed edges. -/
theorem foldl_eraseForestEdge (F : MGraph) (es : List ℕ) :
    es.foldl eraseForestEdge F = { F with E := F.E \ es.toFinset } := by
  induction es generalizing F with
  | nil => simp
  | cons e es ih =>
    rw [List.foldl_cons, ih]
    have he : (F.E.erase e) \ es.toFinset = F.E \ (e :: es).toFinset := by
      ext f
      simp [and_assoc, and_left_comm]
    change { F with E := (F.E.erase e) \ es.toFinset } = _
    rw [he]

/-- An LSF update consists of the input edit followed by releases of
forest edges (Lemma 5.4, page 17). -/
theorem applyLSFUpdate_factor {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState} {u : Update}
    (hI : LSFInv C_lsst ℓ₀ S) (hu : S.G.UpdateIsValid u) :
    let F := forestAfterInput S.RF.F u
    let S' := applyLSFUpdate S u
    F.IsForest ∧ S'.G.IsSubgraph F ∧ S'.RF.F.E ⊆ F.E ∧
      (F.E \ S'.RF.F.E).toList.foldl eraseForestEdge F = S'.RF.F := by
  have ⟨hI', hG, _, _, _, _, _, _, _, hEdges, _⟩ := applyLSFUpdate_inv hI hu
  have hOld := lsfInv_to_RS hI
  have hNew := lsfInv_to_RS hI'
  intro F S'
  have hGraph : S'.G = S.G.applyUpdate u := hG
  have hSub : S'.RF.F.E ⊆ F.E := by
    cases u with
    | insert => exact hEdges
    | split => exact hEdges
    | delete e =>
      intro f hf
      have hg := hNew.2.2.2.2.2.1 hf
      rw [hG] at hg
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hg).1, hEdges hf⟩
  have hForest : F.IsForest := by
    cases u with
    | insert => exact hOld.1
    | delete e => exact isForest_eraseEdge hOld.1 e
    | split v v' St Sh =>
      exact applyUpdate_split_isForest hOld.1 (hOld.2.1.symm ▸ hu.1)
        (by rw [hOld.2.1]; exact hu.2.1) St Sh
  refine ⟨hForest, ?_, hSub, ?_⟩
  · rw [hGraph]
    cases u with
    | insert e a b =>
      refine ⟨hOld.2.2.2.2.1, fun _ hf => Finset.mem_insert_of_mem (hOld.2.2.2.2.2.1 hf), ?_⟩
      intro f hf
      have hn : f ≠ e := fun h => hu.1 (h ▸ hOld.2.2.2.2.2.1 hf)
      simpa [F, forestAfterInput, MGraph.applyUpdate, Function.update_of_ne hn] using hOld.2.2.2.2.2.2 f hf
    | delete e =>
      exact ⟨hOld.2.2.2.2.1, fun _ hf => Finset.mem_erase.mpr
        ⟨(Finset.mem_erase.mp hf).1, hOld.2.2.2.2.2.1 (Finset.mem_erase.mp hf).2⟩,
        fun f hf => hOld.2.2.2.2.2.2 f (Finset.mem_erase.mp hf).2⟩
    | split v v' St Sh => exact applySplit_subgraph hOld.2.2.2.2 v v' St Sh
  · rw [foldl_eraseForestEdge, Finset.toList_toFinset]
    have he : F.E \ (F.E \ S'.RF.F.E) = S'.RF.F.E := by
      ext f
      constructor
      · intro hf
        by_contra hn
        exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hf).1, hn⟩)
      · intro hf
        exact Finset.mem_sdiff.mpr ⟨hSub hf, fun h => (Finset.mem_sdiff.mp h).2 hf⟩
    rw [he]
    cases u <;> rfl


/-- An input split and the forest cuts in the ordered factorization each
create one core vertex. Their count equals the number of newly marked roots
(Lemmas 5.4 and 5.14, pages 17 and 22). -/
theorem applyLSFUpdate_ordered_split_count {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    {u : Update} (hI : LSFInv C_lsst ℓ₀ S) (hu : S.G.UpdateIsValid u) :
    let S' := applyLSFUpdate S u
    updateSplitTag u + (S.RF.F.E \ S'.RF.F.E).card = (S'.R \ S.R).card := by
  obtain ⟨hI', hG, _, _, _, _, _, _, hR, hE, _⟩ := applyLSFUpdate_inv hI hu
  let S' := applyLSFUpdate S u
  have hOld : S.RF.IsRootedSpanningForestOf S.G := lsfInv_to_RS hI
  have hNew : S'.RF.IsRootedSpanningForestOf S'.G := lsfInv_to_RS hI'
  have hVC : S'.G.V.card = S.G.V.card + updateSplitTag u := by
    change (applyLSFUpdate S u).G.V.card = _
    rw [hG]
    cases u with
    | insert => simp [MGraph.applyUpdate, updateSplitTag]
    | delete => simp [MGraph.applyUpdate, updateSplitTag]
    | split v v' St Sh =>
      exact Finset.card_insert_of_notMem hu.2.1
  have ho := forest_components_add_edges S.RF.F hOld.1
  have hn := forest_components_add_edges S'.RF.F hNew.1
  rw [rootedForest_components_card hOld, hOld.2.1] at ho
  rw [rootedForest_components_card hNew, hNew.2.1] at hn
  have hf : (S.RF.F.E \ S'.RF.F.E).card = S.RF.F.E.card - S'.RF.F.E.card :=
    Finset.card_sdiff_of_subset hE
  have hr : (S'.R \ S.R).card = S'.R.card - S.R.card := Finset.card_sdiff_of_subset hR
  have hlE : S'.RF.F.E.card ≤ S.RF.F.E.card := Finset.card_le_card hE
  have hlR : S.R.card ≤ S'.R.card := Finset.card_le_card hR
  change S.R.card + S.RF.F.E.card = S.G.V.card at ho
  change S'.R.card + S'.RF.F.E.card = S'.G.V.card at hn
  change updateSplitTag u + (S.RF.F.E \ S'.RF.F.E).card = (S'.R \ S.R).card
  rw [hf, hr]
  omega

end MinCostFlow.Bundle
