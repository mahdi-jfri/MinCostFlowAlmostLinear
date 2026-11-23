module

public import MinCostFlow.Bundle.CoreRelease
public import MinCostFlow.Bundle.ForestStep

/-!
# Ordering a list of forest releases

After each cut, choose the additional root from the final roots. The
previous root names remain in their components. Releasing all the
listed edges therefore ends with the specified rooted forest.
-/

public section

namespace MinCostFlow.Bundle

open MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.DynSpanner

private theorem ordered_core_nil {G : MGraph} {L L' : LSF} {β : ℕ}
    (ρ : Rotation G) (hG : G.IsValid) (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf G) (h : L.F = L'.F) :
    OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation ρ hG hF') [] := by
  obtain ⟨T, F, w⟩ := L
  obtain ⟨T', F', w'⟩ := L'
  change F = F' at h
  subst F'
  exact ⟨trivial, graphEq_refl _, .refl _⟩

/-- Releasing distinct forest edges in succession gives an ordered batch
with exactly one split per cut. -/
theorem orderedCore_releases {G : MGraph} (ρ : Rotation G) (hG : G.IsValid)
    {L L' : LSF} (cuts : List ℕ) (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf G) (hR : L.F.R ⊆ L'.F.R)
    (hCut : cuts.foldl eraseForestEdge L.F.F = L'.F.F)
    (hMem : ∀ e ∈ cuts, e ∈ L.F.F.E) (hn : cuts.Nodup) {β : ℕ} (hβ : 2 ≤ β) :
    ∃ U, OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation ρ hG hF') U ∧
      batchSplitCount U = cuts.length ∧ U.countP deleteTag = 0 := by
  induction cuts generalizing L with
  | nil =>
    have hFE : L.F.F = L'.F.F := hCut
    have hRC : L.F.R.card = L'.F.R.card := by
      rw [← rootedForest_components_card hF, ← rootedForest_components_card hF', hFE]
    have hRE := Finset.eq_of_subset_of_card_le hR hRC.ge
    have hRF' (A B : RootedForest) (hf : A.F = B.F) (hr : A.R = B.R) : A = B := by
      cases A
      cases B
      exact congrArg₂ RootedForest.mk hf hr
    have hRF := hRF' L.F L'.F hFE hRE
    exact ⟨[], ordered_core_nil ρ hG hF hF' hRF, rfl, rfl⟩
  | cons e cuts ih =>
    let K := eraseForestEdge L.F.F e
    have he := hMem e List.mem_cons_self
    have hKn := isForest_eraseEdge hF.1 e
    have hKV : K.V = G.V := hF.2.1
    have hKsub : L.F.F.IsSubgraph K := eraseForestEdge_subgraph _ _
    have hKG : G.IsSubgraph K :=
      ⟨hF.2.2.2.2.1, fun _ hf => hF.2.2.2.2.2.1 (Finset.mem_of_mem_erase hf),
        fun f hf => hF.2.2.2.2.2.2 f (Finset.mem_of_mem_erase hf)⟩
    have hrest : cuts.foldl eraseForestEdge K = L'.F.F := hCut
    have hFinalK : K.IsSubgraph L'.F.F := by
      rw [← hrest, foldl_eraseForestEdge]
      exact ⟨Finset.Subset.rfl, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
    have hsep : ∀ a ∈ L.F.R, ∀ b ∈ L.F.R, K.Connected a b → a = b := by
      intro a ha b hb hConn
      have hr := root_eq_of_connected hF (hF.2.2.1 ha) (hF.2.2.1 hb)
        (connected_of_subgraph hKsub hConn)
      rwa [root_eq_of_mem_R hF ha, root_eq_of_mem_R hF hb] at hr
    obtain ⟨R, hIncl, hSub, hMid⟩ := exists_roots_refinement hKn hKV hKG hF' hFinalK hR hsep
    let Lmid : LSF := ⟨L.T, ⟨K, R⟩, L.wstr⟩
    have hComp := forest_eraseEdge_components_card hF.1 he
    change (components K).card = _ at hComp
    have hRc : R.card = L.F.R.card + 1 := by
      rw [← rootedForest_components_card hMid, ← rootedForest_components_card hF]
      exact hComp
    obtain ⟨fresh, hf, heq⟩ := roots_insert_of_card hIncl hRc
    obtain ⟨U₀, h₀, hcount₀, hd₀⟩ := orderedCore_release (L' := Lmid) ρ hG hF hMid he rfl heq hf hβ
    have hMemRest : ∀ f ∈ cuts, f ∈ K.E := by
      intro f hf
      exact Finset.mem_erase.mpr ⟨fun h => (List.nodup_cons.mp hn).1 (h ▸ hf),
        hMem f (List.mem_cons_of_mem _ hf)⟩
    obtain ⟨U₁, h₁, hcount₁, hd₁⟩ := ih (L := Lmid) hMid hSub hrest hMemRest
      (List.nodup_cons.mp hn).2
    refine ⟨U₀ ++ U₁, h₀.append h₁, ?_, ?_⟩
    · rw [batchSplitCount_append, hcount₀, hcount₁, List.length_cons, Nat.add_comm]
    · simp [List.countP_append, hd₀, hd₁]

end MinCostFlow.Bundle
