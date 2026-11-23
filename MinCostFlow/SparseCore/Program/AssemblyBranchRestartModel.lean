module

public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartIface
public import MinCostFlow.SparseCore.Program.RestartModelInv
import MinCostFlow.SparseCore.Program.AssemblyBranchSideGapS8

/-!
# Model facts for the restart of a branch (`AssemblyBranchRestartModel`)

The restart of a branch (`AssemblyBranchRestart.lean`) turns the posts of the pieces into the
representation of the branch at the model state `restartBundleTree depth sparsify tr ord`. This
file proves the facts about the model that it uses.

* **The tour.** The lists of the tour are the core rotation lists `outCoreOrder tr ord`. A
  restart keeps the LSF state `tr.cs`, so it keeps these lists
  (`outCoreOrder_restartBundleTree`). When some rotation of the input graph has the order `ord`,
  the lists are the core rotation that the bundle piece reads (`coreCordOf_outCoreOrder`), and
  each end of a core edge lies in the list of a root (`exists_mem_outCoreOrder`).
* **The embedding table.** After a restart, the walk of a core edge is its walk in the new spanner
  of its bundle, or the old walk when the edge is in no active bundle. `AsmBrEmbLink` states this
  of the model, and `refresh_emb_eq` turns it into the table that the refresh leaves
  (`EmbView.refresh`), through the slot of each active pair.
* **The restarted bundle graphs.** The new bundle graph of a slot depends only on the edges of the
  slot (`restartSlotGraph_congr`), so the conditions of the spanner initializations still hold
  after a restart.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## The tour -/

/-- A restart keeps the core rotation lists, since it keeps the LSF state. -/
theorem outCoreOrder_restartBundleTree {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (tr : BundleTreeState L)
    (ord ord' : ℕ → List End) :
    outCoreOrder (restartBundleTree L sparsify tr ord) ord' = outCoreOrder tr ord' :=
  rfl

/-- Some rotation of the input graph of `st` has the order `ord`, and `st.cs` meets the LSF
invariant. -/
def HasRotOrder {L : ℕ} (st : BundleTreeState L) (ord : ℕ → List End) : Prop :=
  ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (_ : CompLSFInv C_lsst ℓ₀ st.cs) (ρ : Rotation st.cs.G),
    ρ.order = ord

/-- The core rotation lists are the rotation of the core graph built from a rotation with the
order `ord`. -/
theorem coreCordOf_outCoreOrder {L : ℕ} {st : BundleTreeState L} {ord : ℕ → List End}
    (h : HasRotOrder st ord) : CoreCordOf st.cs ord (outCoreOrder st ord) := by
  classical
  refine ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose_spec, ?_⟩
  unfold outCoreOrder
  split
  · rfl
  · exact absurd h ‹_›

/-- An end lies in the core rotation list at `v` exactly when its edge is a core edge whose
end in the core graph is `v`. -/
theorem mem_outCoreOrder_iff {L : ℕ} {st : BundleTreeState L} {ord : ℕ → List End}
    (h : HasRotOrder st ord) (v : ℕ) (x : End) :
    x ∈ outCoreOrder st ord v ↔
      x.1 ∈ (coreGraph st.cs.G st.cs.lsf).E ∧ (coreGraph st.cs.G st.cs.lsf).src x = v := by
  classical
  unfold outCoreOrder
  split
  · exact Rotation.mem_order _ v x
  · exact absurd h ‹_›

/-- Each end of a core edge lies in the core rotation list of a root, and roots are below `vCap`
when the vertices of the input graph are. -/
theorem exists_mem_outCoreOrder {L : ℕ} {st : BundleTreeState L} {ord : ℕ → List End}
    (h : HasRotOrder st ord) {vCap : ℕ} (hV : ∀ u ∈ st.cs.G.V, u < vCap) {e : ℕ}
    (he : e ∈ (coreGraph st.cs.G st.cs.lsf).E) (t : Bool) :
    ∃ v < vCap, (e, t) ∈ outCoreOrder st ord v := by
  obtain ⟨_, _, hI, _, _⟩ := id h
  have hF := compLSF_RF_isRSF hI
  have heG : e ∈ st.cs.G.E := (Finset.mem_sdiff.mp he).1
  have hsrc : st.cs.G.src (e, t) ∈ st.cs.G.V := by
    have hv := hI.hG_val e heG
    cases t
    · exact hv.2
    · exact hv.1
  refine ⟨(coreGraph st.cs.G st.cs.lsf).src (e, t), ?_, (mem_outCoreOrder_iff h _ _).mpr ⟨he, rfl⟩⟩
  have hroot : (coreGraph st.cs.G st.cs.lsf).src (e, t) = st.cs.RF.root (st.cs.G.src (e, t)) := by
    cases t <;> rfl
  rw [hroot]
  exact hV _ (hF.2.2.1 (root_mem_R hF hsrc).1)

/-! ## The bundle graphs of a restart -/

/-- The new bundle graph of a slot depends only on the edges of the bundles of the slot. -/
theorem restartSlotGraph_congr {slotCap : ℕ} {S S' : Fin slotCap → Option BundleState}
    {cs : CompLSFState} {ord : ℕ → List End} {k s : ℕ} (hs : s < slotCap) {B B' : BundleState}
    (hB : S ⟨s, hs⟩ = some B) (hB' : S' ⟨s, hs⟩ = some B') (hE : B'.edges = B.edges) :
    restartSlotGraph S' cs ord k s = restartSlotGraph S cs ord k s := by
  unfold restartSlotGraph restartSlotBundle
  simp only [hs, ↓reduceDIte, hB, hB', hE]

/-! ## The embedding table after a restart -/

/-- **The walks of the model after a restart.** For every core edge `e` of `tr`: if `e` is an
edge of the bundles of an active pair `q`, its walk after the restart is the edge itself when `e`
is an edge of the new spanner of `q`, and its walk in that spanner otherwise; if `e` is in no
active bundle, its walk does not change. This holds since the new `S_cur` has the new spanner
edges, the edges outside the bundles and the cross edges (`restartBundleTree`), and bundles of
distinct active pairs have no common edge. -/
def AsmBrEmbLink {L : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (ord : ℕ → List End) : Prop :=
  ∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E,
    (∀ q ∈ activePairs tr, e ∈ (tr.bun q).edges →
      (restartBundleTree L sparsify tr ord).emb e =
        if e ∈ ((restartBundleTree L sparsify tr ord).dyn q).H.E then [(e, true)]
        else piTotal ((restartBundleTree L sparsify tr ord).dyn q) e) ∧
    ((∀ q ∈ activePairs tr, e ∉ (tr.bun q).edges) →
      (restartBundleTree L sparsify tr ord).emb e = tr.emb e)

/-- The edges of the spanner graph of the slot of an active pair after a restart are the edges of
the bundles of the pair. -/
theorem slotGE_restart {cap : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding →
      SparsifyOut) {P : DSParams} {tr : BundleTreeState P.L} {ord cord : ℕ → List End}
    (hcord : CoreCordOf tr.cs ord cord) {slotOf : Finset ℕ × ℤ → ℕ}
    {S6' : BucketSpannerState cap} {q : Finset ℕ × ℤ} (hq : q ∈ activePairs tr)
    (hslot : ∃ (hs : slotOf q < cap) (d : DSHist), S6' ⟨slotOf q, hs⟩ = some d ∧
      d = ⟨(restartBundleTree P.L sparsify tr ord).initBunG q, []⟩ ∧
      d.state P = (restartBundleTree P.L sparsify tr ord).dyn q) :
    slotGE P S6' (slotOf q) = (tr.bun q).edges ∧
      slotWalk P S6' (slotOf q) = fun e =>
        if e ∈ ((restartBundleTree P.L sparsify tr ord).dyn q).H.E then [(e, true)]
        else piTotal ((restartBundleTree P.L sparsify tr ord).dyn q) e := by
  classical
  obtain ⟨hs, d, hSd, hd, hdyn⟩ := hslot
  have hC := (mem_activePairs.mp hq).1
  have hG : (d.state P).G.E = (tr.bun q).edges := by
    rw [hdyn]
    simp only [restartBundleTree, hC, ↓reduceIte]
    show (SparseCore.normGraph (restartBucketBundle tr ord q.1 q.2).graph).E = _
    rw [show (SparseCore.normGraph (restartBucketBundle tr ord q.1 q.2).graph).E =
      (restartBucketBundle tr ord q.1 q.2).graph.E from rfl]
    exact restartBucketBundle_edges_of_coreCord hcord q.1 q.2
  refine ⟨?_, ?_⟩
  · unfold slotGE
    simp only [hs, ↓reduceDIte, hSd]
    exact hG
  · funext e
    unfold slotWalk
    simp only [hs, ↓reduceDIte, hSd]
    rw [hdyn]

/-- **The table after the refresh holds the walks of the model.** Let the table hold the walk
`tr.emb e` of every core edge, let the slots hold the active pairs (`SlotMapOK`), and let the slot
of each active pair hold the new spanner of the pair (the post of the restart of P8). Then after
the refresh (`EmbView.refresh`) the table holds the walk of every core edge after the restart,
by `AsmBrEmbLink`. -/
theorem refresh_emb_eq {cap slotCap : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) {P : DSParams}
    {tr : BundleTreeState P.L} {ord cord : ℕ → List End} (hcord : CoreCordOf tr.cs ord cord)
    {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ} (hMap : SlotMapOK tr slotCap cap slots slotOf)
    {S6' : BucketSpannerState cap}
    (hslots : ∀ q ∈ activePairs tr, ∃ (hs : slotOf q < cap) (d : DSHist),
      S6' ⟨slotOf q, hs⟩ = some d ∧ d = ⟨(restartBundleTree P.L sparsify tr ord).initBunG q, []⟩ ∧
      d.state P = (restartBundleTree P.L sparsify tr ord).dyn q)
    (hlink : AsmBrEmbLink sparsify tr ord) {v : EmbView}
    (hdom : (coreGraph tr.cs.G tr.cs.lsf).E ⊆ v.dom)
    (hemb : ∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E, v.emb e = tr.emb e) :
    (coreGraph tr.cs.G tr.cs.lsf).E ⊆ (v.refresh P S6' slots).dom ∧
      ∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E,
        (v.refresh P S6' slots).emb e = (restartBundleTree P.L sparsify tr ord).emb e := by
  classical
  refine ⟨fun e he => Finset.mem_union_left _ (hdom he), fun e he => ?_⟩
  show (if h : ∃ s ∈ slots, e ∈ slotGE P S6' s then slotWalk P S6' h.choose e else v.emb e) = _
  split
  · rename_i h
    obtain ⟨hs, heS⟩ := h.choose_spec
    obtain ⟨q, hq, hqs⟩ := hMap.2.2.1 _ hs
    obtain ⟨hGE, hW⟩ := slotGE_restart sparsify hcord hq (hslots q hq)
    rw [← hqs] at heS ⊢
    rw [hGE] at heS
    rw [hW]
    exact ((hlink e he).1 q hq heS).symm
  · rename_i h
    have hnone : ∀ q ∈ activePairs tr, e ∉ (tr.bun q).edges := by
      intro q hq heq
      refine h ⟨slotOf q, hMap.2.1 q hq, ?_⟩
      rw [(slotGE_restart sparsify hcord hq (hslots q hq)).1]
      exact heq
    rw [hemb e he]
    exact ((hlink e he).2 hnone).symm

/-! ## The bundle side after a restart -/

/-- **The slot-capacity and sequential-allocation invariant survives a restart.** A restart keeps
the components of `G₀`, `activeBuckets`, `slotCap`, `cap`, and `slots`, and leaves every slot
outside `y.slots` unchanged in both the bundle table and the spanner table. -/
theorem asmFirstSideSlotInv_restart
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {depth : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {ord : ℕ → List End} {wp : ℕ} {y : AsmBrSide B5 depth}
    {S' : Fin y.slotCap → Option BundleState} {x' : (B5 y.kB y.slotCap y.vCap5 y.eCap5).τ}
    {S6' : BucketSpannerState y.cap} {x6' : BucketSpannerMeta depth y.cap}
    (hSlot : AsmFirstSideSlotInv tr y)
    (hBunKeep : ∀ j : Fin y.slotCap, j.1 ∉ y.slots → S' j = y.bunS j)
    (hSpanKeep : ∀ j : Fin y.cap, j.1 ∉ y.slots → S6' j = y.spanS j) :
    AsmFirstSideSlotInv (restartBundleTree depth sparsify tr ord)
      { y with bunS := S', xBun := x', spanS := S6', xSpan := x6', walkPot := wp } :=
  ⟨hSlot.1, hSlot.2.1,
    fun j hj => (hBunKeep j hj).trans (hSlot.2.2.1 j hj),
    fun j hj => (hSpanKeep j hj).trans (hSlot.2.2.2 j hj)⟩

/-- **The inactive-component invariant survives a restart.** A restart keeps `cs`, `activeComps`,
`activeBuckets`, `origBucket`, `k`, the spanner parameters `asmBrSP`, and the lazy `bun` and
`initBunG` of every inactive component. -/
theorem asmFirstInactiveCompInv_restart
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {ord : ℕ → List End} {wp : ℕ} {y : AsmBrSide B5 depth}
    {S' : Fin y.slotCap → Option BundleState} {x' : (B5 y.kB y.slotCap y.vCap5 y.eCap5).τ}
    {S6' : BucketSpannerState y.cap} {x6' : BucketSpannerMeta depth y.cap}
    (hInact : AsmFirstInactiveCompInv impl w depth tr ord y) :
    AsmFirstInactiveCompInv impl w depth (restartBundleTree depth sparsify tr ord) ord
      { y with bunS := S', xBun := x', spanS := S6', xSpan := x6', walkPot := wp } := by
  intro C hC hnotA
  obtain ⟨hR1, hAB, hCoreG0, hSmall, hBuns⟩ := hInact C hC hnotA
  refine ⟨hR1, hAB, hCoreG0, hSmall, fun b hb => ?_⟩
  obtain ⟨hAg, hInitG, hSpOK⟩ := hBuns b hb
  have hC' : C ∉ tr.activeComps := hnotA
  have hbun_eq : (restartBundleTree depth sparsify tr ord).bun (C, b) = tr.bun (C, b) := by
    simp only [restartBundleTree, hC', ↓reduceIte]
  have hinit_eq : (restartBundleTree depth sparsify tr ord).initBunG (C, b) = tr.initBunG (C, b) := by
    simp only [restartBundleTree, hC', ↓reduceIte]
  rw [hbun_eq, hinit_eq]
  exact ⟨hAg, hInitG, hSpOK⟩

/-- **The bundle side keeps its model facts across a restart.** Let the bundle side meet
`AsmBrSideModel` at `tr`, and let the restart of P8 leave a bundle table `S'` that matches the
restarted state (and keeps slots outside `y.slots`) and a spanner table `S6'` whose slot of each
active pair holds a fresh spanner on the new bundle graph of the pair (and keeps slots outside
`y.slots`). Then the bundle side with the new tables meets `AsmBrSideModel` at the restarted state.
The invariant `RestartScurModelInv` carries over by `restartScurModelInv_of_restartBundleTree`,
since a fresh spanner has its edges in its input graph (`dsHist_init_H_sub_E`). The new bundle
graphs of the slots are the old ones, and `BunDisjointInv` carries over, since a restart keeps the
edges of the bundles (`restartSlotGraph_congr`). P5's invariant `bunRestartInv` on the new table
is a hypothesis (the post of P5's restart); the core lists are the same, since a restart keeps the
LSF state (`outCoreOrder_restartBundleTree`). The new bundle side holds the walk potential of the
restarted state. The lazy init charges, `AsmFirstSideSlotInv` (`asmFirstSideSlotInv_restart`), and
`AsmFirstInactiveCompInv` (`asmFirstInactiveCompInv_restart`) carry over, since a restart keeps the
unused slots and all fields of inactive components. The other facts are about fields of the state
that a restart keeps. -/
theorem asmBrSideModel_restart
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl}
    {w depth L capExp limbMul vCap eCap : ℕ} {Ψ : BundleTreeState depth → ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End} {y : AsmBrSide B5 depth}
    (hmod : AsmBrSideModel impl w depth L capExp limbMul Ψ ⟨tr, ord, vCap, eCap⟩ y)
    {S' : Fin y.slotCap → Option BundleState} {x' : (B5 y.kB y.slotCap y.vCap5 y.eCap5).τ}
    {S6' : BucketSpannerState y.cap} {x6' : BucketSpannerMeta depth y.cap}
    (hMatch' : BunTableMatches (restartBundleTree depth (fun _ => canonicalSparsify impl) tr ord)
      y.slotOf S')
    (hSpan' : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      ∃ (hs : y.slotOf (C, b) < y.cap) (d : DSHist), S6' ⟨y.slotOf (C, b), hs⟩ = some d ∧
        d = ⟨(restartBundleTree depth (fun _ => canonicalSparsify impl) tr ord).initBunG (C, b),
          []⟩ ∧
        d.state (asmBrSP impl w depth y) =
          (restartBundleTree depth (fun _ => canonicalSparsify impl) tr ord).dyn (C, b))
    (hinv' : bunRestartInv vCap eCap S' (outCoreOrder tr ord))
    (hBunKeep : ∀ j : Fin y.slotCap, j.1 ∉ y.slots → S' j = y.bunS j)
    (hSpanKeep : ∀ j : Fin y.cap, j.1 ∉ y.slots → S6' j = y.spanS j) :
    AsmBrSideModel impl w depth L capExp limbMul Ψ
      ⟨restartBundleTree depth (fun _ => canonicalSparsify impl) tr ord, ord, vCap, eCap⟩
      { y with
        bunS := S', xBun := x', spanS := S6', xSpan := x6'
        walkPot := Ψ (restartBundleTree depth (fun _ => canonicalSparsify impl) tr ord) } := by
  obtain ⟨hMap, hMatch, -, hMod, hok, hk, hrot, hPle, hC, hSB, hCap, hBD, -, -, hLazy, hspV, hspE,
    hkB, hSlotInv, hInactInv, hCrossInv, hInactDynInv, hBunPartInv, -, hLg, hmMax, hspV_ge,
    hspE_ge⟩ := hmod
  have hcord := coreCordOf_outCoreOrder (st := tr) (ord := ord) hrot
  set tr' := restartBundleTree depth (fun _ => canonicalSparsify impl) tr ord with htr'
  have hact : ∀ q, q ∈ activePairs tr' ↔ q ∈ activePairs tr := fun q => by
    rw [mem_activePairs, mem_activePairs]
    rfl
  -- the edges of the new bundles of the slots are the old ones
  have hEdges : ∀ q ∈ activePairs tr, (tr'.bun q).edges = (tr.bun q).edges := by
    intro q hq
    have hC := (mem_activePairs.mp hq).1
    simp only [htr', restartBundleTree, hC, ↓reduceIte]
    exact restartBucketBundle_edges_of_coreCord hcord q.1 q.2
  have hGraph : ∀ s ∈ y.slots, restartSlotGraph S' tr'.cs ord tr'.k s =
      restartSlotGraph y.bunS tr.cs ord tr.k s := by
    intro s hs
    obtain ⟨q, hq, rfl⟩ := hMap.2.2.1 s hs
    obtain ⟨hs1, B, hB, hag⟩ := hMatch q hq
    obtain ⟨hs2, B', hB', hag'⟩ := hMatch' q ((hact q).mpr hq)
    exact restartSlotGraph_congr hs1 hB hB' (by rw [hag'.2.1, hag.2.1, hEdges q hq])
  -- a fresh spanner has its edges in its input graph
  have hInitSub : ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      (tr'.dyn (C, b)).H.E ⊆ (restartBucketBundle tr ord C b).edges := by
    intro C hC b hb
    obtain ⟨_, d, _, hd, hdyn⟩ := hSpan' C hC b hb
    have hq : (C, b) ∈ activePairs tr := mem_activePairs.mpr ⟨hC, hb⟩
    have hok' := hok _ (hMap.2.1 _ hq)
    rw [restartSlotGraph_eq_initBunG (fun _ => canonicalSparsify impl) hMatch ord hC hb] at hok'
    rw [← hdyn, hd]
    have hsub := dsHist_init_H_sub_E (asmBrSP impl w depth y) hok'.2.2.2.2.2.2.1
      hok'.2.2.2.2.2.2.2.1
    refine hsub.trans (fun e he => ?_)
    simp only [restartBundleTree, hC, ↓reduceIte] at he
    exact he
  refine ⟨hMap, hMatch', ?_, restartScurModelInv_of_restartBundleTree _ hcord hMod hInitSub,
    ?_, hk, hrot, hPle, hC, hSB, hCap, ⟨?_, ?_⟩, hinv', rfl, ?_, hspV, hspE, hkB,
    asmFirstSideSlotInv_restart (fun _ => canonicalSparsify impl) hSlotInv hBunKeep hSpanKeep,
    asmFirstInactiveCompInv_restart (fun _ => canonicalSparsify impl) hInactInv,
    asmFirstCrossInactiveInv_restart depth (fun _ => canonicalSparsify impl) hCrossInv,
    asmFirstInactiveDynInv_restart (fun _ => canonicalSparsify impl) hInactDynInv,
    asmFirstActiveBunPartInv_restart depth (fun _ => canonicalSparsify impl) hk hBunPartInv,
    asmFirstActiveDynGraphInv_restart depth (fun _ => canonicalSparsify impl),
    hLg, hmMax, hspV_ge, hspE_ge⟩
  · intro q hq
    have hq' := (hact q).mp hq
    obtain ⟨hs, d, hd, hdG, hdyn⟩ := hSpan' q.1 (mem_activePairs.mp hq').1 q.2
      (mem_activePairs.mp hq').2
    exact ⟨hs, d, hd, hdyn, by rw [hdG], by simp [hdG, DSHist.flat],
      by simp [hdG, DSHist.flat, MGraph.BatchIsValid], by simp [hdG]⟩
  · intro s hs
    show SpanGraphOK (asmBrSP impl w depth y) (restartSlotGraph S' tr'.cs ord tr'.k s)
    rw [hGraph s hs]
    exact hok s hs
  · intro p₁ hp₁ p₂ hp₂ hne
    have hp₁' := (hact p₁).mp hp₁
    have hp₂' := (hact p₂).mp hp₂
    rw [hEdges p₁ hp₁', hEdges p₂ hp₂']
    exact hBD.1 p₁ hp₁' p₂ hp₂' hne
  · intro p hp
    have hp' := (hact p).mp hp
    rw [hEdges p hp']
    exact hBD.2 p hp'
  · intro C hC
    have hC' : C ∉ tr.activeComps := hC
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) (hLazy C hC')
    simp only [htr', restartBundleTree, hC', ↓reduceIte]

/-! ## The cost of the reset of the output graph -/

/-- **The reset of the output graph costs at most a constant times the restart cost of the
model.** The reset costs `1000 (mul + 1) (S_old.m + S_new.m + 1) · ordStoreLog eCap`
(`outReset_body_runs`). Both graphs have their edges among the edges of the input graph, so
`S_old.m + S_new.m + 1 ≤ 2 (G.m + 1)`. The cap hypothesis gives
`ordStoreLog eCap ≤ (capExp + 1) · bundleLogFactor m₀ n₀` (`ordStoreLog_le_of_capHyp`), and the
restart cost of the model is at least `(G.m + 1) · bundleLogFactor m₀ n₀`. -/
theorem outResetCost_le_restartMachCost {depth : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) {tr : BundleTreeState depth}
    {ord : ℕ → List End} {Sold Snew : MGraph} {mul capExp limbMul L vCap eCap : ℕ}
    (hold : Sold.E ⊆ tr.cs.G.E) (hnew : Snew.E ⊆ tr.cs.G.E)
    (hcap : SparseCoreCapHyp capExp limbMul L tr.m₀ tr.n₀ vCap eCap) :
    1000 * (mul + 1) * (Sold.m + Snew.m + 1) * ordStoreLog eCap ≤
      2000 * (mul + 1) * (capExp + 1) * singleBundleRestartMachCost depth sparsify tr ord := by
  have h1 : Sold.m ≤ tr.cs.G.m := Finset.card_le_card hold
  have h2 : Snew.m ≤ tr.cs.G.m := Finset.card_le_card hnew
  have hlog := ordStoreLog_le_of_capHyp hcap
  have hM : (tr.cs.G.m + 1) * bundleLogFactor tr.m₀ tr.n₀ ≤
      singleBundleRestartMachCost depth sparsify tr ord := by
    unfold singleBundleRestartMachCost
    exact Nat.mul_le_mul_right _ (by omega)
  calc 1000 * (mul + 1) * (Sold.m + Snew.m + 1) * ordStoreLog eCap
      ≤ 1000 * (mul + 1) * (2 * (tr.cs.G.m + 1)) *
          ((capExp + 1) * bundleLogFactor tr.m₀ tr.n₀) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hlog
    _ = 2000 * (mul + 1) * (capExp + 1) * ((tr.cs.G.m + 1) * bundleLogFactor tr.m₀ tr.n₀) := by
        ring
    _ ≤ 2000 * (mul + 1) * (capExp + 1) * singleBundleRestartMachCost depth sparsify tr ord :=
        Nat.mul_le_mul_left _ hM

end MinCostFlow.SparseCore.Program
