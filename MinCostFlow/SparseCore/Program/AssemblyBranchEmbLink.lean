module

public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartModel

/-!
# The walks of the model after a restart (`AssemblyBranchEmbLink`)

The restart of a branch refreshes its embedding table by the walks in the new spanners
(`EmbView.refresh`). The table then holds the walks of the restarted state when the model fact
`AsmBrEmbLink` holds (`refresh_emb_eq`). This file proves `AsmBrEmbLink` from two invariants of
the bundles (`BunDisjointInv`, which the bundle side keeps): the bundles of distinct active pairs
have no common edge, and no bundle edge is a cross edge of the LSF state.

The walk of an edge `e` (`BundleTreeState.emb`) is `[(e, true)]` when `e` is an edge of `S_cur`,
and otherwise its walk in the spanner of the bundle that holds `e`. After a restart, `S_cur` holds
the edges of the new spanners, the edges of the components outside the bundles, and the cross
edges (`RestartScurModelInv`). For an edge `e` of the bundle of an active pair `q`:
* `e` is a cross edge of no kind, by the second invariant;
* `e` is not an edge of a component outside its bundles: in the component of `q` it lies in a
  bundle, and two components share no edge that is not a cross edge (`comp_edge_disjoint`);
* `e` is an edge of the new spanner of a pair `p` only if `p = q`, since the spanner of `p` has its
  edges in the bundle of `p`, by the first invariant.
So `e` is in the new `S_cur` exactly when it is an edge of the new spanner of `q`, and the bundle
that holds `e` is the bundle of `q`. For an edge in no active bundle, the restart changes neither
the edges of `S_cur` around it nor its walk.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read MinCostFlow.LSF

/-- Two distinct components share no edge that is not a cross edge, since their vertex sets are
disjoint and such an edge has the same tail in both components and in the input graph. -/
theorem comp_edge_disjoint {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C₁ C₂ : Finset ℕ}
    (hC₁ : C₁ ∈ components cs.G₀) (hC₂ : C₂ ∈ components cs.G₀) (hne : C₁ ≠ C₂)
    {e : ℕ} (he₁ : e ∈ (cs.compSt C₁).G.E) (he₂ : e ∈ (cs.compSt C₂).G.E)
    (hnc : e ∉ cs.crossEdges) : False := by
  have ht₁ : cs.G.tail e ∈ (cs.compSt C₁).G.V := by
    rw [← (hI.hNonCross_ends C₁ hC₁ e he₁ hnc).1]
    exact ((hI.hCompLSF C₁ hC₁).1.hG_val e he₁).1
  have ht₂ : cs.G.tail e ∈ (cs.compSt C₂).G.V := by
    rw [← (hI.hNonCross_ends C₂ hC₂ e he₂ hnc).1]
    exact ((hI.hCompLSF C₂ hC₂).1.hG_val e he₂).1
  exact Finset.disjoint_left.mp (hI.hV_disj C₁ hC₁ C₂ hC₂ hne) ht₁ ht₂

/-- **The walks of the model after a restart** (`AsmBrEmbLink`), from `RestartScurModelInv`
before and after the restart and `BunDisjointInv`. -/
theorem asmBrEmbLink_of_inv {L : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState L} {ord cord : ℕ → List End} (hcord : CoreCordOf tr.cs ord cord)
    (hMod : RestartScurModelInv tr)
    (hMod' : RestartScurModelInv (restartBundleTree L sparsify tr ord))
    (hBD : BunDisjointInv tr) : AsmBrEmbLink sparsify tr ord := by
  classical
  have ⟨_, _, hI, _, _, _⟩ := hcord
  set tr' := restartBundleTree L sparsify tr ord with htr'
  have hEq : ∀ q ∈ activePairs tr, (tr'.bun q).edges = (tr.bun q).edges := by
    intro q hq
    have hC := (mem_activePairs.mp hq).1
    simp only [htr', restartBundleTree, hC, ↓reduceIte]
    exact restartBucketBundle_edges_of_coreCord hcord q.1 q.2
  have hH' : ∀ q ∈ activePairs tr, (tr'.dyn q).H.E ⊆ (tr.bun q).edges := by
    intro q hq
    rw [← hEq q hq]
    exact (hMod'.2.2.2.2 q.1 (mem_activePairs.mp hq).1 q.2 (mem_activePairs.mp hq).2).2.2.2
  have hH : ∀ q ∈ activePairs tr, (tr.dyn q).H.E ⊆ (tr.bun q).edges := fun q hq =>
    (hMod.2.2.2.2 q.1 (mem_activePairs.mp hq).1 q.2 (mem_activePairs.mp hq).2).2.2.2
  have hX : ∀ C ∈ tr.activeComps, tr'.extraEdges C = tr.extraEdges C := by
    intro C hC
    unfold BundleTreeState.extraEdges
    congr 1
    exact Finset.biUnion_congr rfl fun b hb => hEq (C, b) (mem_activePairs.mpr ⟨hC, hb⟩)
  have hSE' := hMod'.2.2.1
  have hSE := hMod.2.2.1
  -- the bundle of an active pair that holds `e`
  have huniq : ∀ e, ∀ p ∈ activePairs tr, ∀ q ∈ activePairs tr, e ∈ (tr.bun p).edges →
      e ∈ (tr.bun q).edges → p = q := by
    intro e p hp q hq hep heq
    by_contra hne
    exact Finset.disjoint_left.mp (hBD.1 p hp q hq hne) hep heq
  intro e he
  refine ⟨fun q hq heq => ?_, fun hnone => ?_⟩
  · have hq' := mem_activePairs.mp hq
    have hS'iff : e ∈ tr'.S_cur.E ↔ e ∈ (tr'.dyn q).H.E := by
      rw [hSE']
      simp only [Finset.mem_union, Finset.mem_biUnion]
      constructor
      · rintro ((⟨C, hC, b, hb, heH⟩ | ⟨C, hC, heX⟩) | hcr)
        · have hp : (C, b) ∈ activePairs tr := mem_activePairs.mpr ⟨hC, hb⟩
          rw [huniq e _ hp q hq (hH' _ hp heH) heq] at heH
          exact heH
        · exfalso
          rw [hX C hC] at heX
          unfold BundleTreeState.extraEdges at heX
          obtain ⟨heC, hnb⟩ := Finset.mem_sdiff.mp heX
          by_cases hCq : C = q.1
          · subst hCq
            exact hnb (Finset.mem_biUnion.mpr ⟨q.2, hq'.2, heq⟩)
          · exact comp_edge_disjoint hI (hMod.1 hC) (hMod.1 hq'.1) hCq
              (Finset.mem_sdiff.mp heC).1
              ((hMod.2.2.2.2 q.1 hq'.1 q.2 hq'.2).2.1 heq)
              (Finset.disjoint_left.mp (hBD.2 q hq) heq)
        · exact absurd hcr (Finset.disjoint_left.mp (hBD.2 q hq) heq)
      · intro heH
        exact Or.inl (Or.inl ⟨q.1, hq'.1, q.2, hq'.2, heH⟩)
    have hex : ∃ p : Finset ℕ × ℤ, p.1 ∈ tr'.activeComps ∧ p.2 ∈ tr'.activeBuckets p.1 ∧
        e ∈ (tr'.bun p).edges := ⟨q, hq'.1, hq'.2, by rw [hEq q hq]; exact heq⟩
    unfold BundleTreeState.emb
    rw [← htr']
    by_cases hS : e ∈ tr'.S_cur.E
    · simp only [hS, hS'iff.mp hS, ↓reduceIte]
    · have hH'' : e ∉ (tr'.dyn q).H.E := fun h => hS (hS'iff.mpr h)
      simp only [hS, hH'', ↓reduceIte]
      rw [dite_eq_left_of_eq_true (eq_true hex)]
      obtain ⟨h1, h2, h3⟩ := hex.choose_spec
      have hp : hex.choose ∈ activePairs tr := mem_activePairs.mpr ⟨h1, h2⟩
      rw [hEq _ hp] at h3
      rw [huniq e _ hp q hq h3 heq]
  · have hnone' : ∀ p ∈ activePairs tr, e ∉ (tr'.bun p).edges := fun p hp => by
      rw [hEq p hp]; exact hnone p hp
    have hS'iff : e ∈ tr'.S_cur.E ↔ e ∈ tr.S_cur.E := by
      rw [hSE', hSE]
      simp only [Finset.mem_union, Finset.mem_biUnion]
      constructor
      · rintro ((⟨C, hC, b, hb, heH⟩ | ⟨C, hC, heX⟩) | hcr)
        · have hp : (C, b) ∈ activePairs tr := mem_activePairs.mpr ⟨hC, hb⟩
          exact absurd (hH' _ hp heH) (hnone _ hp)
        · exact Or.inl (Or.inr ⟨C, hC, by rw [← hX C hC]; exact heX⟩)
        · exact Or.inr hcr
      · rintro ((⟨C, hC, b, hb, heH⟩ | ⟨C, hC, heX⟩) | hcr)
        · have hp : (C, b) ∈ activePairs tr := mem_activePairs.mpr ⟨hC, hb⟩
          exact absurd (hH _ hp heH) (hnone _ hp)
        · exact Or.inl (Or.inr ⟨C, hC, by rw [hX C hC]; exact heX⟩)
        · exact Or.inr hcr
    have hno' : ¬ ∃ p : Finset ℕ × ℤ, p.1 ∈ tr'.activeComps ∧ p.2 ∈ tr'.activeBuckets p.1 ∧
        e ∈ (tr'.bun p).edges := fun ⟨p, h1, h2, h3⟩ =>
      hnone' p (mem_activePairs.mpr ⟨h1, h2⟩) h3
    have hno : ¬ ∃ p : Finset ℕ × ℤ, p.1 ∈ tr.activeComps ∧ p.2 ∈ tr.activeBuckets p.1 ∧
        e ∈ (tr.bun p).edges := fun ⟨p, h1, h2, h3⟩ =>
      hnone p (mem_activePairs.mpr ⟨h1, h2⟩) h3
    unfold BundleTreeState.emb
    rw [← htr']
    by_cases hS : e ∈ tr.S_cur.E
    · simp only [hS, (hS'iff.mpr hS), ↓reduceIte]
    · have hS' : e ∉ tr'.S_cur.E := fun h => hS (hS'iff.mp h)
      simp only [hS, hS', ↓reduceIte]
      rw [dite_eq_right_of_eq_false (eq_false hno'),
        dite_eq_right_of_eq_false (eq_false hno)]

end MinCostFlow.SparseCore.Program
