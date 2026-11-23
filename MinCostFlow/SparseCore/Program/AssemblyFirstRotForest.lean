module

public import MinCostFlow.SparseCore.CanonCoreRelease
public import MinCostFlow.SparseCore.CompLSFBridge

/-!
# Two facts on the forest of a batch

The list `T₀` of a branch step holds the roots of the trees that the step touches. Two facts on
the forest of the LSF bound and justify it.

* `compLSFBatch_RF_E_not_deleted`: the batch deletes no edge of the forest after the batch. The
  forest only loses edges in a batch, and it never holds an edge that is not in the graph. So an
  edge that the batch deletes leaves the forest at that time and does not come back.
* `card_RF_E_sdiff_le_canon`: the number of forest edges that the batch removes is at most the
  number of splits of the canonical core batch `canonCoreBatch`. In one update, the input edit
  removes at most one forest edge, and when it does, its core edit is one split. Every other
  removed edge is a release, and each release adds one core split (`releasesBatch_splitCount`).
-/

public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.Bundle MinCostFlow.DynSpanner
open MinCostFlow.SparseCore

/-- **The batch deletes no edge of the final forest.** -/
theorem compLSFBatch_RF_E_not_deleted {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ (U : List Update) {cs : CompLSFState}, CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U →
      ∀ e ∈ (compLSFBatch cs U).RF.F.E, ∀ u ∈ U, u ≠ .delete e
  | [], _, _, _, _, _, _, hu => absurd hu List.not_mem_nil
  | u :: U, cs, hI, hU, e, he, u', hu' => by
    have hG₁ : (compLSFStepSingle cs u).G = cs.G.applyUpdate u := compLSFBatch_G cs [u]
    have hI₁ := compLSFInv_step hI hU.1
    have hU₁ : (compLSFStepSingle cs u).G.BatchIsValid U := hG₁ ▸ hU.2
    -- the batch `u :: U` is `u`, then `U`
    have he₁ : e ∈ (compLSFBatch (compLSFStepSingle cs u) U).RF.F.E := he
    rcases List.mem_cons.mp hu' with rfl | hu'
    · rintro rfl
      -- the final forest edge `e` is in the forest after `u`, so in the graph after `u`
      have h₁ := (compLSFBatch_decremental hI₁ hU₁).1 he₁
      have h₂ := (compLSF_RF_isRSF hI₁).2.2.2.2.2.1 h₁
      rw [hG₁] at h₂
      exact Finset.notMem_erase e _ h₂
    · exact compLSFBatch_RF_E_not_deleted U hI₁ hU₁ e he₁ u' hu'

private theorem card_sdiff_le_add (A B C : Finset ℕ) :
    (A \ C).card ≤ (A \ B).card + (B \ C).card := by
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro x hx
  rw [Finset.mem_sdiff] at hx
  by_cases hB : x ∈ B
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hB, hx.2⟩)
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx.1, hB⟩)

theorem batchSplitCount_append (U V : List Update) :
    batchSplitCount (U ++ V) = batchSplitCount U + batchSplitCount V :=
  List.countP_append ..

/-- The input edit of an update removes a forest edge only when its core edit is a split. -/
private theorem card_sdiff_forestAfterInput_le (cs : CompLSFState) (u : Update) :
    (cs.RF.F.E \ (forestAfterInput cs.RF.F u).E).card ≤ batchSplitCount (inputCoreBatch cs u) := by
  cases u with
  | insert e a b => simp [forestAfterInput]
  | delete e =>
    by_cases he : e ∈ cs.RF.F.E
    · -- one forest edge goes, and the core edit is one split
      have hsub : cs.RF.F.E \ (forestAfterInput cs.RF.F (.delete e)).E ⊆ {e} := by
        intro x hx
        change x ∈ cs.RF.F.E \ cs.RF.F.E.erase e at hx
        rw [Finset.mem_sdiff, Finset.mem_erase] at hx
        rw [Finset.mem_singleton]
        by_contra hne
        exact hx.2 ⟨hne, hx.1⟩
      have h₁ : batchSplitCount (inputCoreBatch cs (.delete e)) = 1 := by
        simp [inputCoreBatch, he, batchSplitCount, refineSplit, isSplit]
      rw [h₁]
      exact (Finset.card_le_card hsub).trans (Finset.card_singleton e).le
    · -- the input edit keeps the forest
      have hK : (forestAfterInput cs.RF.F (.delete e)).E = cs.RF.F.E :=
        Finset.erase_eq_of_notMem he
      rw [hK, Finset.sdiff_self, Finset.card_empty]
      exact Nat.zero_le _
  | split v v' St Sh => simp [forestAfterInput, MGraph.applyUpdate]

/-- One update removes at most as many forest edges as its canonical core batch has splits. -/
private theorem card_sdiff_step_le (cs : CompLSFState) (u : Update) :
    (cs.RF.F.E \ (compLSFStepSingle cs u).RF.F.E).card ≤ batchSplitCount (canonStepCore cs u) := by
  have h₁ := card_sdiff_le_add cs.RF.F.E (forestAfterInput cs.RF.F u).E
    (compLSFStepSingle cs u).RF.F.E
  have h₂ := card_sdiff_forestAfterInput_le cs u
  -- each release adds one split
  rw [canonStepCore, batchSplitCount_append, releasesBatch_splitCount, Finset.length_sort]
  omega

/-- **The forest edges that a batch removes are paid by core splits.** -/
theorem card_RF_E_sdiff_le_canon : ∀ (U : List Update) (cs : CompLSFState),
    (cs.RF.F.E \ (compLSFBatch cs U).RF.F.E).card ≤ batchSplitCount (canonCoreBatch cs U)
  | [], cs => by
    change (cs.RF.F.E \ cs.RF.F.E).card ≤ _
    simp
  | u :: U, cs => by
    have ih := card_RF_E_sdiff_le_canon U (compLSFStepSingle cs u)
    have hs := card_sdiff_step_le cs u
    have h := card_sdiff_le_add cs.RF.F.E (compLSFStepSingle cs u).RF.F.E
      (compLSFBatch (compLSFStepSingle cs u) U).RF.F.E
    change (cs.RF.F.E \ (compLSFBatch (compLSFStepSingle cs u) U).RF.F.E).card ≤
      batchSplitCount (canonStepCore cs u ++ canonCoreBatch (compLSFStepSingle cs u) U)
    rw [batchSplitCount_append]
    omega

end MinCostFlow.SparseCore.Program
