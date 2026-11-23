module

public import MinCostFlow.HierPaths.BuildTopModel

/-!
# Validity of the hierarchy assembled from certified replies

At each parent the reply gives the embedded child graphs and the
perfect sibling matchings. The group arithmetic translates these
guarantees to global numbering.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The reply at each nontrivial parent is certified for its actual host. -/
@[expose] def buildTopRepliesGood (x b : ℕ) (root : Graph) (reply : ℕ → ℕ → BuildLevelData)
    (M r Δ L L' : ℕ) (bh : ℕ → ℕ) : Prop :=
  ∀ j g, 1 < groupSize x b j → g < numGroups x b j →
    (reply j g).Good ((buildTopHierarchy x b root reply).host j g)
      (g * groupSize x b j) (groupSize x b (j + 1)) (branching x b j)
      M r Δ L L' (bh j)

private theorem childMembers {x b j g c : ℕ} (hc : parentGroup x b j c = g) :
    buildLevelChild (g * groupSize x b j) (groupSize x b (j + 1)) (c % branching x b j) =
      members x b (j + 1) c := by
  rw [buildTopLevelChild_eq, ← hc, buildTopChild_decompose]

/-- The certified replies give a valid hierarchy. -/
theorem buildTopHierarchy_isValid {x b M r Δ L L' : ℕ} {root : Graph}
    {reply : ℕ → ℕ → BuildLevelData} {bh : ℕ → ℕ}
    (hroot : ∀ e ∈ root.edges, e.1 ∈ members x b 0 0 ∧ e.2 ∈ members x b 0 0)
    (hgood : buildTopRepliesGood x b root reply M r Δ L L' bh) :
    (buildTopHierarchy x b root reply).IsValid x b := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j g hs hg i hi
    cases j with
    | zero =>
      have hg' : g = 0 := by simpa [numGroups] using hg
      subst g
      change i < root.m at hi
      change insideB (members x b 0 0) (edgeAt root.edges i) = true
      simpa [insideB] using hroot _ (edgeAt_mem hi)
    | succ j =>
      have hp := parentGroup_lt_numGroups hg
      have hs' := hs.trans_le (groupSize_succ_le (x := x) (b := b) j)
      have h := (hgood j _ hs' hp).graph _ (Nat.mod_lt g branching_pos)
      simp only [buildTopHierarchy, if_pos hg] at hi ⊢
      have he := h.2.2.2.1 _ (edgeAt_mem hi)
      rw [childMembers rfl] at he
      simpa [insideB] using he
  · intro j c hs hc
    have h := (hgood j _ (hs.trans_le (groupSize_succ_le (x := x) (b := b) j)) (parentGroup_lt_numGroups hc)).embeds
      _ (Nat.mod_lt c branching_pos)
    rw [buildTopLevelVerts_eq] at h
    simpa only [show (buildTopHierarchy x b root reply).host (j + 1) c =
        (reply j (parentGroup x b j c)).host (c % branching x b j) by simp [buildTopHierarchy, hc],
      show (buildTopHierarchy x b root reply).emb j c =
        (reply j (parentGroup x b j c)).emb (c % branching x b j) by simp [buildTopHierarchy, hc]] using h
  · intro j g hs hg c hc c' hc' hlt
    have h := (hgood j g hs hg).connMatch _ (Nat.mod_lt c branching_pos)
      _ (Nat.mod_lt c' branching_pos) (buildTopChild_mod_lt_mod hc hc' hlt)
    rw [childMembers (mem_childGroups_iff.mp hc), childMembers (mem_childGroups_iff.mp hc')] at h
    unfold HierData.IsPerfectOn
    rw [(buildTopHierarchy_rows x b j g c c' root reply hg hc hc' hlt).2.2]
    exact h
  · intro j g hs hg c hc c' hc' hlt q hq
    rw [(buildTopHierarchy_rows x b j g c c' root reply hg hc hc' hlt).2.2] at hq
    exact ((hgood j g hs hg).connWalk _ (Nat.mod_lt c branching_pos)
      _ (Nat.mod_lt c' branching_pos) (buildTopChild_mod_lt_mod hc hc' hlt) q hq).1

end MinCostFlow.HierPaths

end
