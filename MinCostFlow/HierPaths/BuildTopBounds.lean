module

public import MinCostFlow.HierPaths.BuildTopValid
import MinCostFlow.HierPaths.BuildHierAux

/-!
# Local path bounds of the assembled hierarchy

Each parent reply bounds a single sibling matching and all its child
embeddings. Reindexing the child sum preserves the aggregate bound.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp
open scoped BigOperators

private theorem hostAtChild {x b j c : ℕ} (root : Graph) (reply : ℕ → ℕ → BuildLevelData)
    (hc : c < numGroups x b (j + 1)) :
    (buildTopHierarchy x b root reply).host (j + 1) c =
      (reply j (parentGroup x b j c)).host (c % branching x b j) := by
  simp [buildTopHierarchy, hc]

private theorem embAtChild {x b j c : ℕ} (root : Graph) (reply : ℕ → ℕ → BuildLevelData)
    (hc : c < numGroups x b (j + 1)) :
    (buildTopHierarchy x b root reply).emb j c =
      (reply j (parentGroup x b j c)).emb (c % branching x b j) := by
  simp [buildTopHierarchy, hc]

/-- The hierarchy uses the actual per-parent dilation and load bounds of the level contract. -/
theorem buildTopHierarchy_bounds {x b M r Δ L L' : ℕ} {root : Graph}
    {reply : ℕ → ℕ → BuildLevelData} {bh : ℕ → ℕ}
    (hgood : buildTopRepliesGood x b root reply M r Δ L L' bh) :
    (buildTopHierarchy x b root reply).Bounds x b
      (fun j => routePathLen Δ (bh j) L)
      (fun j => buildLevelDegree L' * routeCong Δ (bh j) L)
      (fun j => routeCong Δ (bh j) L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j c hs hc e he
    rw [hostAtChild root reply hc] at he
    rw [embAtChild root reply hc]
    exact (hgood j _ (hs.trans_le (groupSize_succ_le j)) (parentGroup_lt_numGroups hc)).embedLength
      _ (Nat.mod_lt c branching_pos) e he
  · intro j g hs hg c hc c' hc' hlt q hq
    rw [(buildTopHierarchy_rows x b j g c c' root reply hg hc hc' hlt).2.2] at hq
    exact ((hgood j g hs hg).connWalk _ (Nat.mod_lt c branching_pos)
      _ (Nat.mod_lt c' branching_pos) (buildTopChild_mod_lt_mod hc hc' hlt) q hq).2
  · intro j g hs hg e he
    have hh := (hgood j g (hs.trans_le (groupSize_succ_le j)) hg).embedLoad e he
    rw [childGroups_eq_Ico, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    convert hh using 1
    apply Finset.sum_congr rfl
    intro a ha
    have ha' := Finset.mem_range.mp ha
    let c := g * branching x b j + a
    have hc : c ∈ childGroups x b j g := buildTopChild_mem g a ha'
    have hc' := buildTopChild_global_lt hg hc
    have hp := mem_childGroups_iff.mp hc
    have hm : c % branching x b j = a := by
      change (g * branching x b j + a) % branching x b j = a
      simp [Nat.add_comm, Nat.mod_eq_of_lt ha']
    change (∑ t ∈ Finset.range ((buildTopHierarchy x b root reply).host (j + 1) c).m,
      ((buildTopHierarchy x b root reply).emb j c t).count e) = _
    rw [hostAtChild root reply hc', embAtChild root reply hc', hp, hm]
  · intro j g hs hg c hc c' hc' hlt e he
    rw [(buildTopHierarchy_rows x b j g c c' root reply hg hc hc' hlt).2.2]
    exact (hgood j g hs hg).connLoad _ (Nat.mod_lt c branching_pos)
      _ (Nat.mod_lt c' branching_pos) (buildTopChild_mod_lt_mod hc hc' hlt) e he

end MinCostFlow.HierPaths

end
