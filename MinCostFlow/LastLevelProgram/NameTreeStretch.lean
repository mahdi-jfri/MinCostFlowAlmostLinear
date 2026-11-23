module

public import MinCostFlow.LastLevelProgram.NameTree
import MinCostFlow.LSF.Walks
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Transporting the LSST guarantee to named edges

Theorem 2.2 (page 7) bounds the weighted stretch on compact indices.
Restoring names preserves each original edge's path length and
reindexes the sum without changing its terms.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WideWord LSF
open scoped BigOperators

private theorem image_edgeName (G : MGraph) : (Finset.range G.m).image (edgeName G) = G.E := by
  ext e
  constructor
  · intro he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    exact edgeName_mem (Finset.mem_range.mp hi)
  · intro he
    let iso : Fin G.m ≃o G.E := G.E.orderIsoOfFin rfl
    let i := iso.symm ⟨e, he⟩
    refine Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, ?_⟩
    rw [edgeName, dite_eq_left i.isLt]
    exact congrArg Subtype.val (iso.apply_symm_apply ⟨e, he⟩)

private theorem restoreTreeNames_path {G T : MGraph} {ℓ v : ℕ → ℝ} {γ : ℝ}
    (hG : G.IsValid)
    (hT : IsLSST (indexedGraph G).toMGraph (ℓ ∘ edgeName G) (v ∘ edgeName G) γ T)
    (i : ℕ) (hi : i < G.m) :
    (restoreTreeNames G T).forestPath (G.tail (edgeName G i)) (G.head (edgeName G i)) =
      restoreWalkNames G (T.forestPath ((indexedGraph G).tail i) ((indexedGraph G).head i)) := by
  let I := indexedGraph G
  have hs : T.IsSpanningTreeOn (Finset.range G.n) := hT.1
  have hrs := restoreTreeNames_spanning hs
  obtain ⟨ht, hh⟩ := (indexedGraph_valid hG
    ⟨_, (hG _ (edgeName_mem hi)).1⟩).2 i hi
  have htV : I.tail i ∈ T.V := hs.2.1.symm ▸ Finset.mem_range.mpr ht
  have hhV : I.head i ∈ T.V := hs.2.1.symm ▸ Finset.mem_range.mpr hh
  have hp := forestPath_isPath hs.1
    (hs.2.2 _ (Finset.mem_range.mpr ht) _ (Finset.mem_range.mpr hh))
  have hp' := restoreWalkNames_isPath hs.1.1 hs.2.1.le htV hp
  rw [(indexedGraph_endpoints hG hi).1, (indexedGraph_endpoints hG hi).2] at hp'
  exact forestPath_eq_of_isPath hrs.1 hp'

/-- Theorem 2.2 (page 7). Restoring the names preserves each original
edge's stretch, so an individual rounded output is unchanged. -/
theorem restoreTreeNames_treeStretch {G T : MGraph} {ℓ v : ℕ → ℝ} {γ : ℝ}
    (hG : G.IsValid)
    (hT : IsLSST (indexedGraph G).toMGraph (ℓ ∘ edgeName G) (v ∘ edgeName G) γ T)
    (i : ℕ) (hi : i < G.m) :
    treeStretch G (restoreTreeNames G T) ℓ (edgeName G i) =
      treeStretch (indexedGraph G).toMGraph T (ℓ ∘ edgeName G) i := by
  let I := indexedGraph G
  let R := restoreTreeNames G T
  have hs : T.IsSpanningTreeOn (Finset.range G.n) := hT.1
  let P := T.forestPath (I.tail i) (I.head i)
  obtain ⟨ht, hh⟩ := (indexedGraph_valid hG
    ⟨_, (hG _ (edgeName_mem hi)).1⟩).2 i hi
  have hp := forestPath_isPath hs.1
    (hs.2.2 _ (Finset.mem_range.mpr ht) _ (Finset.mem_range.mpr hh))
  have hp' := restoreWalkNames_isPath hs.1.1 hs.2.1.le
    (hs.2.1.symm ▸ Finset.mem_range.mpr ht) hp
  have hlen : walkLength ℓ (restoreWalkNames G P) = walkLength (ℓ ∘ edgeName G) P := by
    rw [walkLength_eq_sum_of_isPath ℓ hp', walkLength_eq_sum_of_isPath _ hp,
      restoreWalkNames_edges, Finset.sum_image (restoreTreeNames_injective G).2.injOn]
    apply Finset.sum_congr rfl
    intro f hf
    have hf' := hT.2.2.1 i (Finset.mem_range.mpr hi) f hf
    exact congrArg ℓ (ite_eq_left (Finset.mem_range.mp hf'))
  unfold treeStretch
  change 1 + walkLength ℓ (R.forestPath _ _) / ℓ (edgeName G i) =
    1 + walkLength (ℓ ∘ edgeName G) P / ℓ (edgeName G i)
  rw [restoreTreeNames_path hG hT i hi, hlen]

/-- The tree returned by Theorem 2.2 retains its low-stretch guarantee
under the canonical maps back to the named graph. -/
theorem restoreTreeNames_isLSST {G T : MGraph} {ℓ v : ℕ → ℝ} {γ : ℝ}
    (hG : G.IsValid)
    (hT : IsLSST (indexedGraph G).toMGraph (ℓ ∘ edgeName G) (v ∘ edgeName G) γ T) :
    IsLSST G ℓ v γ (restoreTreeNames G T) := by
  have hs : T.IsSpanningTreeOn (Finset.range G.n) := hT.1
  have hrs := restoreTreeNames_spanning hs
  have hinj : Set.InjOn (edgeName G) (↑(Finset.range G.m) : Set ℕ) := by
    intro i hi j hj e
    exact ((edgeIndex_name (Finset.mem_range.mp hi)).symm.trans
      (congrArg (edgeIndex G) e)).trans (edgeIndex_name (Finset.mem_range.mp hj))
  refine ⟨hrs, ?_, ?_, ?_⟩
  · intro e he hmem
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    have hi' := (treeEdgeName_mem_iff G i).1 hmem
    simpa only [treeEdgeName, ite_eq_left hi'] using restoreTreeNames_endpoints hG hT hi' hi
  · intro e he f hf
    rw [← image_edgeName G] at he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    rw [restoreTreeNames_path hG hT i (Finset.mem_range.mp hi), restoreWalkNames_edges] at hf
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hf
    exact (treeEdgeName_mem_iff G j).2 (Finset.mem_range.mp (hT.2.2.1 i hi j hj))
  · unfold MGraph.norm1
    rw [← image_edgeName G, Finset.sum_image hinj, Finset.sum_image hinj]
    convert hT.2.2.2 using 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [restoreTreeNames_treeStretch hG hT i (Finset.mem_range.mp hi)]
      rfl

    · rfl

end MinCostFlow.LastLevelProgram
