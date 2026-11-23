module

public import MinCostFlow.MinRatio.WireChainAlgebra
public import MinCostFlow.MinRatio.WireSuffixEditsBase

/-!
# The split of the forest of Branch B before Sync 2a (`WireChainCoreBranchBSplitKFBL`)

After Sync 1 the tree state holds the chain tree of the old chain `c0` without the deleted edges
`Del`. Sync 2a then cuts, for each finished level `j < min fr d`, the edges `fDel j` that leave
the forest of the level (those still in the new root graph `G0'`), and Sync 2b swaps the old
forests of the levels from `fr` on for the new ones. `wireBranchBSuffixKFBL_runs` asks for the
split `F \ Y = Fp ∪ (oldE ∩ G0'.E)` of the forest before Sync 2a, and for the facts on `Fp`.

`branchBSplit` gives them with `Fp` the union of the new forests of the levels below `fr`. The
reason is the following. The forests of the levels of a chain are disjoint. A finished level `j`
only loses edges (its new forest lies in its old one) and loses exactly `fDel j`. When `fr = d + 1`
the last level is not rebuilt and keeps its forest. So an old forest edge of a finished level that
is not deleted is either cut by Sync 2a or kept in the new forest of the level. The union of `Fp`
and the new forests from `fr` on is the new chain tree.
-/

public section

namespace MinCostFlow.MinRatio

open Chain

/-- An edge of `graphListEdgeUnion` of the suffix forests from `fr` (none when `fr = d + 1`) is
an edge of the forest of a level `fr ≤ j ≤ d`. -/
theorem mem_suffixUnion_iff {T : SparseCoreRestartTool} {P : ChainParams} (c : ChainState T P)
    (fr e : ℕ) :
    e ∈ graphListEdgeUnion (if fr ≤ P.d then chainSuffixForests c fr else []) ↔
      ∃ j, fr ≤ j ∧ j ≤ P.d ∧ e ∈ (c.toTreeChain.activeLSF j).F.F.E := by
  split_ifs with h
  · rw [graphListEdgeUnion_chainSuffixForests c h, Finset.mem_biUnion]
    constructor
    · rintro ⟨j, hj, he⟩
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hj
      exact ⟨j, h1, by omega, he⟩
    · rintro ⟨j, h1, h2, he⟩
      exact ⟨j, Finset.mem_Ico.mpr ⟨h1, by omega⟩, he⟩
  · simp only [graphListEdgeUnion, List.foldl_nil, Finset.notMem_empty, false_iff]
    rintro ⟨j, h1, h2, _⟩
    omega

theorem mem_chainTree_iff {T : SparseCoreRestartTool} {P : ChainParams} (c : ChainState T P)
    (e : ℕ) :
    e ∈ c.toTreeChain.chainTree.E ↔ ∃ j ≤ P.d, e ∈ (c.toTreeChain.activeLSF j).F.F.E := by
  simp only [TreeChain.chainTree, TreeChain.chainTreeEdges, Finset.mem_biUnion, Finset.mem_range]
  exact ⟨fun ⟨j, hj, he⟩ => ⟨j, by change j < P.d + 1 at hj; omega, he⟩,
    fun ⟨j, hj, he⟩ => ⟨j, by change j < P.d + 1; omega, he⟩⟩

/-- **The split before Sync 2a.** `c0` is the old chain, `c1` the new one, `fr` the first rebuilt
level, `G0` and `G0'` the old and new root graphs, and `Del` the deleted edges. The hypotheses:
the forests of the levels of each chain are disjoint (`hDisj0`, `hDisj1`); the old chain tree lies
in `G0` and the new one in `G0'`; an edge of `G0` that is not deleted is in `G0'`, and a deleted
edge is not; at a finished level the new forest lies in the old one and `fDel j` lists the
difference (`hPlain`); when `fr = d + 1`, the last level keeps its forest (`hSame`). With
`Fp` the union of the new forests of the levels below `fr`, the conclusions are the split, the
place of the entries of `fDel j` that are in `G0'`, the two disjointness facts of `Fp`, the new
chain tree as `Fp ∪ newE`, and the lists `fDel j` without repeats across the levels. -/
theorem branchBSplit {T : SparseCoreRestartTool} {P : ChainParams} (c0 c1 : ChainState T P)
    {fr : ℕ} {G0 G0' : MGraph} {Del : Finset ℕ} {fDel : ℕ → List ℕ}
    (hDisj0 : ∀ j₁ ≤ P.d, ∀ j₂ ≤ P.d, j₁ ≠ j₂ →
      Disjoint (c0.toTreeChain.activeLSF j₁).F.F.E (c0.toTreeChain.activeLSF j₂).F.F.E)
    (hDisj1 : ∀ j₁ ≤ P.d, ∀ j₂ ≤ P.d, j₁ ≠ j₂ →
      Disjoint (c1.toTreeChain.activeLSF j₁).F.F.E (c1.toTreeChain.activeLSF j₂).F.F.E)
    (hSub0 : c0.toTreeChain.chainTree.E ⊆ G0.E) (hSub1 : c1.toTreeChain.chainTree.E ⊆ G0'.E)
    (hKeepE : ∀ e ∈ G0.E, e ∉ Del → e ∈ G0'.E) (hDelOut : ∀ e ∈ Del, e ∉ G0'.E)
    (hPlain : ∀ j < min fr P.d,
      (c1.toTreeChain.activeLSF j).F.F.E ⊆ (c0.toTreeChain.activeLSF j).F.F.E ∧
      (fDel j).toFinset = (c0.toTreeChain.activeLSF j).F.F.E \ (c1.toTreeChain.activeLSF j).F.F.E)
    (hSame : fr = P.d + 1 →
      (c1.toTreeChain.activeLSF P.d).F.F.E = (c0.toTreeChain.activeLSF P.d).F.F.E)
    (hfr : fr ≤ P.d + 1) (hNd : ∀ j < min fr P.d, (fDel j).Nodup) :
    let Fp := (Finset.range fr).biUnion fun j => (c1.toTreeChain.activeLSF j).F.F.E
    let oldE := graphListEdgeUnion (if fr ≤ P.d then chainSuffixForests c0 fr else [])
    let newE := graphListEdgeUnion (if fr ≤ P.d then chainSuffixForests c1 fr else [])
    (∀ Y : Finset ℕ, (∀ e, e ∈ Y ↔ (∃ j < min fr P.d, e ∈ fDel j) ∧ e ∈ G0'.E) →
      (c0.toTreeChain.chainTree.E \ Del) \ Y = Fp ∪ (oldE ∩ G0'.E)) ∧
    (∀ j < min fr P.d, ∀ e ∈ fDel j, e ∈ G0'.E → e ∈ c0.toTreeChain.chainTree.E \ Del) ∧
    (∀ e ∈ Fp, e ∉ oldE) ∧ (∀ e ∈ Fp, e ∉ newE) ∧
    Fp ∪ newE = c1.toTreeChain.chainTree.E ∧
    ((List.range (min fr P.d)).flatMap fDel).Nodup := by
  intro Fp oldE newE
  have hFp (e : ℕ) : e ∈ Fp ↔ ∃ j < fr, e ∈ (c1.toTreeChain.activeLSF j).F.F.E := by
    simp only [Fp, Finset.mem_biUnion, Finset.mem_range]
  have hOld (e : ℕ) : e ∈ oldE ↔ ∃ j, fr ≤ j ∧ j ≤ P.d ∧ e ∈ (c0.toTreeChain.activeLSF j).F.F.E :=
    mem_suffixUnion_iff c0 fr e
  have hNew (e : ℕ) : e ∈ newE ↔ ∃ j, fr ≤ j ∧ j ≤ P.d ∧ e ∈ (c1.toTreeChain.activeLSF j).F.F.E :=
    mem_suffixUnion_iff c1 fr e
  -- the new forest of a level below `fr` lies in the old one
  have hLow : ∀ j < fr, ∀ e ∈ (c1.toTreeChain.activeLSF j).F.F.E,
      e ∈ (c0.toTreeChain.activeLSF j).F.F.E := fun j hj e he => by
    by_cases hn : j < min fr P.d
    · exact (hPlain j hn).1 he
    · have h1 : fr = P.d + 1 := by omega
      have h2 : j = P.d := by omega
      subst h2
      rwa [← hSame h1]
  -- an entry of `fDel j` is an old forest edge of level `j` off the new one
  have hDelMem : ∀ j < min fr P.d, ∀ e ∈ fDel j, e ∈ (c0.toTreeChain.activeLSF j).F.F.E ∧
      e ∉ (c1.toTreeChain.activeLSF j).F.F.E := fun j hj e he => by
    have := (hPlain j hj).2 ▸ List.mem_toFinset.mpr he
    exact Finset.mem_sdiff.mp this
  have hDis0 {j₁ j₂ e : ℕ} (h1 : j₁ ≤ P.d) (h2 : j₂ ≤ P.d) (hne : j₁ ≠ j₂)
      (he1 : e ∈ (c0.toTreeChain.activeLSF j₁).F.F.E)
      (he2 : e ∈ (c0.toTreeChain.activeLSF j₂).F.F.E) : False :=
    Finset.disjoint_left.mp (hDisj0 j₁ h1 j₂ h2 hne) he1 he2
  refine ⟨fun Y hY => ?_, fun j hj e he hG => ?_, fun e he ho => ?_, fun e he hn => ?_, ?_, ?_⟩
  · ext e
    constructor
    · intro h
      obtain ⟨h1, hYn⟩ := Finset.mem_sdiff.mp h
      obtain ⟨hC, hD⟩ := Finset.mem_sdiff.mp h1
      obtain ⟨j, hj, he⟩ := (mem_chainTree_iff c0 e).mp hC
      have hYn' : ∀ j' < min fr P.d, e ∈ fDel j' → e ∉ G0'.E := fun j' hj' hd hG =>
        hYn ((hY e).mpr ⟨⟨j', hj', hd⟩, hG⟩)
      have hG' : e ∈ G0'.E := hKeepE e (hSub0 hC) hD
      by_cases hjf : fr ≤ j
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr
          ⟨(hOld e).mpr ⟨j, hjf, hj, he⟩, hG'⟩))
      · refine Finset.mem_union.mpr (Or.inl ((hFp e).mpr ⟨j, by omega, ?_⟩))
        by_cases hn : j < min fr P.d
        · have hnd : e ∉ fDel j := fun h => hYn' j hn h hG'
          by_contra hc
          exact hnd (List.mem_toFinset.mp ((hPlain j hn).2 ▸ Finset.mem_sdiff.mpr ⟨he, hc⟩))
        · have h1 : fr = P.d + 1 := by omega
          have h2 : j = P.d := by omega
          subst h2
          rwa [hSame h1]
    · intro h
      have hYn : ∀ (hG : e ∈ G0'.E), (∀ j' < min fr P.d, e ∈ fDel j' → False) → e ∉ Y :=
        fun _ hf hy => by
          obtain ⟨⟨j', hj', hd⟩, _⟩ := (hY e).mp hy
          exact hf j' hj' hd
      rcases Finset.mem_union.mp h with hp | hi
      · obtain ⟨j, hj, he⟩ := (hFp e).mp hp
        have he0 := hLow j hj e he
        have hG' : e ∈ G0'.E :=
          hSub1 ((mem_chainTree_iff c1 e).mpr ⟨j, by omega, he⟩)
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨(mem_chainTree_iff c0 e).mpr
          ⟨j, by omega, he0⟩, fun hD => hDelOut e hD hG'⟩, hYn hG' fun j' hj' hd => ?_⟩
        obtain ⟨h0, h1⟩ := hDelMem j' hj' e hd
        by_cases hjj : j' = j
        · subst hjj; exact h1 he
        · exact hDis0 (by omega) (by omega) hjj h0 he0
      · obtain ⟨ho, hG'⟩ := Finset.mem_inter.mp hi
        obtain ⟨j, hj1, hj2, he⟩ := (hOld e).mp ho
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨(mem_chainTree_iff c0 e).mpr
          ⟨j, hj2, he⟩, fun hD => hDelOut e hD hG'⟩, hYn hG' fun j' hj' hd => ?_⟩
        exact hDis0 (by omega) hj2 (by omega) (hDelMem j' hj' e hd).1 he
  · obtain ⟨h0, _⟩ := hDelMem j hj e he
    exact Finset.mem_sdiff.mpr ⟨(mem_chainTree_iff c0 e).mpr ⟨j, by omega, h0⟩,
      fun hD => hDelOut e hD hG⟩
  · obtain ⟨j, hj, he1⟩ := (hFp e).mp he
    obtain ⟨j', hj1, hj2, he2⟩ := (hOld e).mp ho
    exact hDis0 (by omega) hj2 (by omega) (hLow j hj e he1) he2
  · obtain ⟨j, hj, he1⟩ := (hFp e).mp he
    obtain ⟨j', hj1, hj2, he2⟩ := (hNew e).mp hn
    exact Finset.disjoint_left.mp (hDisj1 j (by omega) j' hj2 (by omega)) he1 he2
  · ext e
    rw [Finset.mem_union, hFp, hNew, mem_chainTree_iff]
    constructor
    · rintro (⟨j, hj, he⟩ | ⟨j, _, hj, he⟩)
      · exact ⟨j, by omega, he⟩
      · exact ⟨j, hj, he⟩
    · rintro ⟨j, hj, he⟩
      by_cases hjf : j < fr
      · exact Or.inl ⟨j, hjf, he⟩
      · exact Or.inr ⟨j, by omega, hj, he⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun j hj => hNd j (List.mem_range.mp hj), ?_⟩
    refine List.Pairwise.imp_of_mem ?_ (List.nodup_range)
    intro a b ha hb hab e hea heb
    have ha' := List.mem_range.mp ha
    have hb' := List.mem_range.mp hb
    exact hDis0 (by omega) (by omega) hab (hDelMem a ha' e hea).1 (hDelMem b hb' e heb).1

end MinCostFlow.MinRatio
