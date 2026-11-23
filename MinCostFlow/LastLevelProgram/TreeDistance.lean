module

public import MinCostFlow.LSF.TreeOps
import MinCostFlow.Chain.WalkFlow
import Mathlib.Tactic.Linarith

/-!
# Computing stretch from root distances

For the last-level rebuild of Definition 5.8 (pages 19–20), subtract
the common root path from both endpoint distances. The remaining
two lengths add to the path length required by the stretch formula.
-/

public section

namespace MinCostFlow.LastLevelProgram

open LSF

private theorem length_split {T : MGraph} {a b c : ℕ} (hT : T.IsForest)
    (hab : T.Connected a b) (hbc : T.Connected b c) (ℓ : ℕ → ℝ)
    (hsplit : T.forestPath a c = T.forestPath a b ++ T.forestPath b c)
    (hdisjoint : Disjoint (walkEdges (T.forestPath a b)) (walkEdges (T.forestPath b c))) :
    walkLength ℓ (T.forestPath a c) =
      walkLength ℓ (T.forestPath a b) + walkLength ℓ (T.forestPath b c) := by
  rw [walkLength_eq_sum_of_isPath ℓ (forestPath_isPath hT (MGraph.connected_trans hab hbc)),
    walkLength_eq_sum_of_isPath ℓ (forestPath_isPath hT hab),
    walkLength_eq_sum_of_isPath ℓ (forestPath_isPath hT hbc),
    hsplit, walkEdges_append, Finset.sum_union hdisjoint]

/-- Two root distances and the lowest common ancestor distance give the
length between the endpoints, as used in computing a last-level stretch. -/
theorem treeDistance_eq_rootDistances {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) (ℓ : ℕ → ℝ) :
    let z := lca T r u v
    walkLength ℓ (T.forestPath u v) =
      walkLength ℓ (T.forestPath u r) + walkLength ℓ (T.forestPath v r) -
        2 * walkLength ℓ (T.forestPath z r) := by
  intro z
  have hz : z ∈ T.V := lca_mem hT hu hv
  have ⟨hleft, hdleft⟩ := forestPath_eq_of_isAncestor hT hu (lca_isAncestor_left hT hu hv)
  have ⟨hright, hdright⟩ := forestPath_eq_of_isAncestor hT hv (lca_isAncestor_right hT hu hv)
  have ha := length_split hT.isForest (hT.connected hu hz) (hT.connected_root hz) ℓ hleft hdleft
  have hb := length_split hT.isForest (hT.connected hv hz) (hT.connected_root hz) ℓ hright hdright
  have hc := length_split hT.isForest (hT.connected hu hz) (hT.connected hz hv) ℓ
    (forestPath_eq_lca hT hu hv) (disjoint_walkEdges_lca hT hu hv)
  rw [forestPath_rev hT.isForest (hT.connected hv hz), walkLength_walkRev] at hc
  linarith only [ha, hb, hc]

/-- The root starts the traversal with depth zero and a zero distance. -/
theorem rootDistance_at_root {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) (ℓ : ℕ → ℝ) :
    depth T r r = 0 ∧ walkLength ℓ (T.forestPath r r) = 0 := by
  simp [depth,walkLength,walkEdges,forestPath_self hT.isForest]

/-- A child receives its parent's distance plus the length of its parent edge. -/
theorem rootDistance_parent_step {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hne : u ≠ r) (ℓ : ℕ → ℝ) :
    walkLength ℓ (T.forestPath u r) =
      ℓ (parentEdge T r u) + walkLength ℓ (T.forestPath (parent T r u) r) := by
  obtain ⟨x,hpath,_,he,_,_⟩ := forestPath_parent hT hu hne
  have hp := forestPath_isPath hT.isForest (hT.connected_root hu)
  have hpp := forestPath_isPath hT.isForest (hT.connected_root (parent_mem hT hu))
  have hn := MGraph.isPath_edges_nodup hp
  rw [hpath, List.map_cons, List.nodup_cons] at hn
  have hn' : x.1 ∉ walkEdges (T.forestPath (parent T r u) r) := by
    simpa [walkEdges] using hn.1
  rw [walkLength_eq_sum_of_isPath ℓ hp, walkLength_eq_sum_of_isPath ℓ hpp,
    hpath, walkEdges_cons, Finset.sum_insert hn', he]

/-- A tree of `n` vertices has depth below `n` at every vertex. -/
theorem depth_lt_card_vertices {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) : depth T r u < T.V.card := by
  have hsub : ancestors T r u ⊆ T.V :=
    fun _ ha => isAncestor_mem hT hu (mem_ancestors_iff.mp ha)
  have hcard := Finset.card_le_card hsub
  rw [ancestors_card_eq hT hu] at hcard
  exact hcard

end MinCostFlow.LastLevelProgram
