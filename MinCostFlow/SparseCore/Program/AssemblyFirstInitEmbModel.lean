module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitEmb
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitS0Model
public import MinCostFlow.SparseCore.Program.AssemblyBranchFacts
public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartIface

/-!
# The embedding table at the init and the model (`AssemblyFirstInitEmbModel`)

The build makes the embedding table in two steps: the start table, in which each edge of `G` has
the empty walk (`asmFirstInitEmbTbl_runs`), and then the refresh of the restart
(`embRefresh_runs`), which gives each edge of the graph of a listed slot its walk in the spanner of
the slot. Here we show that the table then holds the walk `tr₀.emb e` of every core edge `e`
(`asmFirstInit_refresh_emb_eq`), as the build must.

The walk of the model (`BundleTreeState.emb`) is the edge itself on `S_cur`, the walk in the
spanner of its pair on the other edges of the active bundles, and the empty walk elsewhere. Two
facts make this match the refresh.
* The edges of `S_cur` are the `H` edges of the spanners of the active pairs, and the `H` edges of
  a spanner are edges of its bundle. Bundles of distinct active pairs share no edge
  (`BunDisjointInv`). So an edge `e` of the bundle of `q` lies in `S_cur` exactly when it lies in
  the `H` of `q`, and the pair that the model picks for `e` is `q` (`initTree_emb_of_mem`).
* An edge in no active bundle is not in `S_cur`, so its walk in the model is empty
  (`initTree_emb_of_not_mem`), as in the start table.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

variable {L : ℕ} {tr : BundleTreeState L}

/-- An edge lies in the bundle of at most one active pair. -/
theorem eq_of_mem_bun_of_mem_bun (hBD : BunDisjointInv tr) {p q : Finset ℕ × ℤ} (hp : p ∈ activePairs tr) (hq : q ∈ activePairs tr) {e : ℕ}
    (hep : e ∈ (tr.bun p).edges) (heq : e ∈ (tr.bun q).edges) : p = q := by
  by_contra hne
  exact Finset.disjoint_left.mp (hBD.1 p hp q hq hne) hep heq

/-- **The walk of the model on an edge of an active bundle.** If `S_cur` has the `H` edges of the
active pairs, these lie in their bundles, and distinct active bundles share no edge, then the walk
of an edge `e` of the bundle of an active pair `q` is `e` itself when `e` is an `H` edge of `q`,
and its walk in the spanner of `q` otherwise. -/
theorem initTree_emb_of_mem (hBD : BunDisjointInv tr)
    (hSE : tr.S_cur.E = (activePairs tr).biUnion fun q => (tr.dyn q).H.E)
    (hHB : ∀ q ∈ activePairs tr, (tr.dyn q).H.E ⊆ (tr.bun q).edges)
    {q : Finset ℕ × ℤ} (hq : q ∈ activePairs tr) {e : ℕ} (he : e ∈ (tr.bun q).edges) :
    tr.emb e = if e ∈ (tr.dyn q).H.E then [(e, true)] else piTotal (tr.dyn q) e := by
  classical
  unfold BundleTreeState.emb
  by_cases hH : e ∈ (tr.dyn q).H.E
  · have hS : e ∈ tr.S_cur.E := by
      rw [hSE]
      exact Finset.mem_biUnion.mpr ⟨q, hq, hH⟩
    simp only [hS, hH, ↓reduceIte]
  · have hS : e ∉ tr.S_cur.E := by
      rw [hSE]
      intro hS
      obtain ⟨p, hp, hpH⟩ := Finset.mem_biUnion.mp hS
      have hpq := eq_of_mem_bun_of_mem_bun hBD hp hq (hHB p hp hpH) he
      exact hH (hpq ▸ hpH)
    have hex : ∃ p : Finset ℕ × ℤ, p.1 ∈ tr.activeComps ∧ p.2 ∈ tr.activeBuckets p.1 ∧
        e ∈ (tr.bun p).edges := ⟨q, (mem_activePairs.mp hq).1, (mem_activePairs.mp hq).2, he⟩
    rw [ite_eq_right hS, dite_eq_left hex, ite_eq_right hH]
    have hch := hex.choose_spec
    have hpq := eq_of_mem_bun_of_mem_bun hBD (mem_activePairs.mpr ⟨hch.1, hch.2.1⟩) hq
      hch.2.2 he
    rw [hpq]

/-- **The walk of the model on an edge in no active bundle** is empty, when `S_cur` has the `H`
edges of the active pairs and these lie in their bundles. -/
theorem initTree_emb_of_not_mem
    (hSE : tr.S_cur.E = (activePairs tr).biUnion fun q => (tr.dyn q).H.E)
    (hHB : ∀ q ∈ activePairs tr, (tr.dyn q).H.E ⊆ (tr.bun q).edges) {e : ℕ}
    (hnone : ∀ q ∈ activePairs tr, e ∉ (tr.bun q).edges) : tr.emb e = [] := by
  classical
  unfold BundleTreeState.emb
  have hS : e ∉ tr.S_cur.E := by
    rw [hSE]
    intro hS
    obtain ⟨p, hp, hpH⟩ := Finset.mem_biUnion.mp hS
    exact hnone p hp (hHB p hp hpH)
  have hex : ¬ ∃ p : Finset ℕ × ℤ, p.1 ∈ tr.activeComps ∧ p.2 ∈ tr.activeBuckets p.1 ∧
      e ∈ (tr.bun p).edges := fun ⟨p, hC, hb, hp⟩ => hnone p (mem_activePairs.mpr ⟨hC, hb⟩) hp
  rw [ite_eq_right hS, dite_eq_right hex]

/-- **The table after the refresh holds the walks of the model.** Start from a table in which a
superset `E` of the core edges has the empty walk. Let the slots hold the active pairs
(`SlotMapOK`), and let the slot of each active pair hold a spanner with the state `tr.dyn q`. Let
the graph of that spanner have the edges of the bundle of `q`, let its `H` edges lie in the
bundle, let `S_cur` have the `H` edges of the active pairs, and let distinct active bundles share
no edge. Then after the refresh every core edge is in the table, with its walk in the model. -/
theorem asmFirstInit_refresh_emb_eq (P : DSParams) {tr : BundleTreeState P.L}
    {slotCap cap : ℕ} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ} {S6 : BucketSpannerState cap}
    (hMap : SlotMapOK tr slotCap cap slots slotOf)
    (hslots : ∀ q ∈ activePairs tr, ∃ (hs : slotOf q < cap) (d : DSHist),
      S6 ⟨slotOf q, hs⟩ = some d ∧ d.state P = tr.dyn q)
    (hGE : ∀ q ∈ activePairs tr, (tr.dyn q).G.E = (tr.bun q).edges)
    (hHB : ∀ q ∈ activePairs tr, (tr.dyn q).H.E ⊆ (tr.bun q).edges)
    (hSE : tr.S_cur.E = (activePairs tr).biUnion fun q => (tr.dyn q).H.E)
    (hBD : BunDisjointInv tr) {E : Finset ℕ} (hcore : (coreGraph tr.cs.G tr.cs.lsf).E ⊆ E) :
    (coreGraph tr.cs.G tr.cs.lsf).E ⊆ ((⟨fun _ => [], E⟩ : EmbView).refresh P S6 slots).dom ∧
      ∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E,
        ((⟨fun _ => [], E⟩ : EmbView).refresh P S6 slots).emb e = tr.emb e := by
  classical
  -- the graph and the walks of the slot of an active pair
  have hslot : ∀ q ∈ activePairs tr, slotGE P S6 (slotOf q) = (tr.bun q).edges ∧
      slotWalk P S6 (slotOf q) = fun e =>
        if e ∈ (tr.dyn q).H.E then [(e, true)] else piTotal (tr.dyn q) e := by
    intro q hq
    obtain ⟨hs, d, hd, hst⟩ := hslots q hq
    refine ⟨?_, ?_⟩
    · unfold slotGE
      simp only [hs, ↓reduceDIte, hd, hst]
      exact hGE q hq
    · funext e
      unfold slotWalk
      simp only [hs, ↓reduceDIte, hd, hst]
  refine ⟨fun e he => Finset.mem_union_left _ (hcore he), fun e _ => ?_⟩
  show (if h : ∃ s ∈ slots, e ∈ slotGE P S6 s then slotWalk P S6 h.choose e else []) = _
  split
  · rename_i h
    obtain ⟨hs, heS⟩ := h.choose_spec
    obtain ⟨q, hq, hqs⟩ := hMap.2.2.1 _ hs
    obtain ⟨hGE', hW⟩ := hslot q hq
    rw [← hqs] at heS ⊢
    rw [hGE'] at heS
    rw [hW]
    exact (initTree_emb_of_mem hBD hSE hHB hq heS).symm
  · rename_i h
    have hnone : ∀ q ∈ activePairs tr, e ∉ (tr.bun q).edges := by
      intro q hq heq
      refine h ⟨slotOf q, hMap.2.1 q hq, ?_⟩
      rw [(hslot q hq).1]
      exact heq
    exact (initTree_emb_of_not_mem hSE hHB hnone).symm

/-- **The facts of the spanners at the init.** In the init state, the spanner of each pair is the
empty history on the start graph of the pair. So its graph has the edges of the bundle, and its
`H` edges lie in the bundle, when the start graph is valid with at most `mMax` edges. -/
theorem initTree_dyn_GE_HE (P : DSParams) (lsfInit : LSFInit) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ)
    (hSB : P.splitBound = bundleSplitBudget k M) (q : Finset ℕ × ℤ)
    (hok : SpanGraphOK P ((initBundleTreeWithParams lsfInit P.L
      (fun _ => canonicalSparsify P.impl) params spanConst k M N G₀ ℓ₀ ord j).initBunG q)) :
    let tr := initBundleTreeWithParams lsfInit P.L (fun _ => canonicalSparsify P.impl) params
      spanConst k M N G₀ ℓ₀ ord j
    (tr.dyn q).G.E = (tr.bun q).edges ∧ (tr.dyn q).H.E ⊆ (tr.bun q).edges := by
  intro tr
  have hdyn := initTree_dyn P lsfInit params spanConst k M N G₀ ℓ₀ ord j hSB q
  refine ⟨?_, ?_⟩
  · rw [hdyn, dsHist_init_G_eq]
    rfl
  · rw [hdyn]
    exact dsHist_init_H_sub_E P hok.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.1

end

end MinCostFlow.SparseCore.Program
