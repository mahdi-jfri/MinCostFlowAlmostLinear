module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitS0
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSpanModel

/-!
# The output graph of the init and the model (`AssemblyFirstInitS0Model`)

`asmFirstInitS0_runs` leaves the graph `((asmFirstInitView G lsf R).rebuild SP S6 slots).S`: the
roots `R`, and each edge of the spanner graphs `H` of the listed slots that lies in `G` and whose
core ends are roots, at its core ends. Here we show that it is `tr.S_cur` up to the ends of the
edges it does not have, which is all that `DynGraphAt` sees (`asmFirstInit_S0_dynGraphAt`).

The reason has two parts.
* The `H` edges of the listed slots are the `H` edges of the spanners of the active pairs
  (`slotsHE_eq_activePairs`), since the slot map is one to one onto the slots and each slot holds
  the spanner of its pair (`asmFirstInit_spanMatch`). At the init these are the edges of `S_cur`
  (`initTree_S_cur_E`).
* `S_cur` is a subgraph of the core graph (`RestartScurModelInv`), and its ends are roots, since
  `S_cur` is valid with the roots as its vertices. So each edge of `S_cur` lies in `G`, its core
  ends are roots, and the restart puts it at the ends it has in `S_cur`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

/-- The `H` edges of the listed slots are the `H` edges of the spanners of the active pairs, when
the slot map is good and each slot of an active pair holds the spanner of the pair. -/
theorem slotsHE_eq_activePairs (SP : DSParams) {slotCap cap : ℕ} {tr : BundleTreeState SP.L}
    {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ} {S6 : BucketSpannerState cap}
    (hMap : SlotMapOK tr slotCap cap slots slotOf)
    (hsp : ∀ q ∈ activePairs tr, ∃ (hs : slotOf q < cap) (d : DSHist),
      S6 ⟨slotOf q, hs⟩ = some d ∧ d.state SP = tr.dyn q) :
    slotsHE SP S6 slots = (activePairs tr).biUnion fun q => (tr.dyn q).H.E := by
  have hslot : ∀ q ∈ activePairs tr, slotHE SP S6 (slotOf q) = (tr.dyn q).H.E := by
    intro q hq
    obtain ⟨hs, d, hd, hst⟩ := hsp q hq
    simp [slotHE, hs, hd, hst]
  ext e
  simp only [slotsHE, Finset.mem_biUnion, List.mem_toFinset]
  constructor
  · rintro ⟨s, hs, he⟩
    obtain ⟨q, hq, rfl⟩ := hMap.2.2.1 s hs
    exact ⟨q, hq, hslot q hq ▸ he⟩
  · rintro ⟨q, hq, he⟩
    exact ⟨slotOf q, hMap.2.1 q hq, (hslot q hq).symm ▸ he⟩

/-- The `H` edges of the active pairs, written over the components and their buckets. -/
theorem activePairs_biUnion_H {L : ℕ} (tr : BundleTreeState L) :
    ((activePairs tr).biUnion fun q => (tr.dyn q).H.E) =
      tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b => (tr.dyn (C, b)).H.E := by
  ext e
  simp only [Finset.mem_biUnion, mem_activePairs]
  constructor
  · rintro ⟨⟨C, b⟩, ⟨hC, hb⟩, he⟩
    exact ⟨C, hC, b, hb, he⟩
  · rintro ⟨C, hC, b, hb, he⟩
    exact ⟨(C, b), ⟨hC, hb⟩, he⟩

/-- At the init, the edges of `S_cur` are the `H` edges of the spanners of the active pairs. -/
theorem initTree_S_cur_E (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) :
    let tr := initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G₀ ℓ₀ ord j
    tr.S_cur.E = tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
      (tr.dyn (C, b)).H.E :=
  rfl

/-- **The graph of the restart at the init is `S_cur`**: same vertices, same edges, and the same
ends on the edges. The hypotheses: `S_cur` is valid and meets `RestartScurModelInv`, the vertex
set `R` is that of `S_cur`, and the `H` edges of the listed slots are the edges of `S_cur`. -/
theorem asmFirstInit_S0_graph {L : ℕ} {tr : BundleTreeState L} (SP : DSParams) {cap : ℕ}
    {S6 : BucketSpannerState cap} {slots : List ℕ} {R : Finset ℕ}
    (hinv : RestartScurModelInv tr) (hval : tr.S_cur.IsValid) (hR : R = tr.S_cur.V)
    (hHE : slotsHE SP S6 slots = tr.S_cur.E) :
    let S := ((asmFirstInitView tr.cs.G tr.cs.lsf R).rebuild SP S6 slots).S
    S.V = tr.S_cur.V ∧ S.E = tr.S_cur.E ∧
      ∀ e ∈ S.E, S.tail e = tr.S_cur.tail e ∧ S.head e = tr.S_cur.head e := by
  classical
  intro S
  obtain ⟨-, -, -, hsub, -⟩ := hinv
  obtain ⟨-, hsubE, hends⟩ := hsub
  -- each edge of `S_cur` is an edge of `G` whose core ends are roots
  have hin : ∀ e ∈ tr.S_cur.E, e ∈ tr.cs.G.E ∧
      (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ R ∧ (coreGraph tr.cs.G tr.cs.lsf).head e ∈ R := by
    intro e he
    have heC := hsubE he
    have hG : e ∈ tr.cs.G.E := (Finset.mem_sdiff.mp heC).1
    obtain ⟨ht, hh⟩ := hends e he
    obtain ⟨hvt, hvh⟩ := hval e he
    rw [hR, ← ht, ← hh]
    exact ⟨hG, hvt, hvh⟩
  have hmemE : ∀ e, e ∈ S.E ↔ e ∈ tr.S_cur.E := by
    intro e
    simp only [S, ReadView.rebuild, ReadView.rebuildS, asmFirstInitView, asmFirstInitEmptyOn,
      Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_inter, hHE]
    constructor
    · rintro (⟨h0, -⟩ | ⟨⟨he, -⟩, -⟩)
      · simp at h0
      · exact he
    · intro he
      obtain ⟨hG, ht, hh⟩ := hin e he
      exact Or.inr ⟨⟨he, hG⟩, ht, hh⟩
  refine ⟨by show R = tr.S_cur.V; exact hR, Finset.ext hmemE, fun e he => ?_⟩
  have he' := (hmemE e).mp he
  obtain ⟨ht, hh⟩ := hends e he'
  obtain ⟨hG, hrt, hrh⟩ := hin e he'
  constructor
  · simp only [S, ReadView.rebuild, ReadView.rebuildS, asmFirstInitView, asmFirstInitEmptyOn,
      Finset.mem_filter, Finset.mem_inter, hHE, he', hG, hrt, hrh, and_self, ite_true]
    exact ht.symm
  · simp only [S, ReadView.rebuild, ReadView.rebuildS, asmFirstInitView, asmFirstInitEmptyOn,
      Finset.mem_filter, Finset.mem_inter, hHE, he', hG, hrt, hrh, and_self, ite_true]
    exact hh.symm

/-- **The output graph at the init.** Under the hypotheses of `asmFirstInit_S0_graph`, the memory
form of the graph of the restart is a memory form of `S_cur`. -/
theorem asmFirstInit_S0_dynGraphAt {L : ℕ} {tr : BundleTreeState L} (SP : DSParams) {cap : ℕ}
    {S6 : BucketSpannerState cap} {slots : List ℕ} {R : Finset ℕ} {mem : ℕ → ℕ}
    {a vCap eCap : ℕ}
    (hinv : RestartScurModelInv tr) (hval : tr.S_cur.IsValid) (hR : R = tr.S_cur.V)
    (hHE : slotsHE SP S6 slots = tr.S_cur.E)
    (hS : DynGraphAt mem a vCap eCap
      ((asmFirstInitView tr.cs.G tr.cs.lsf R).rebuild SP S6 slots).S) :
    DynGraphAt mem a vCap eCap tr.S_cur := by
  obtain ⟨hV, hE, hends⟩ := asmFirstInit_S0_graph SP hinv hval hR hHE
  exact DynGraphAt.congr_ends hV hE hends hS

end

end MinCostFlow.SparseCore.Program
