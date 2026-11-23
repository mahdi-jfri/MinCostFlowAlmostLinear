module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue6
public import MinCostFlow.SparseCore.BundleStepLocal
public import MinCostFlow.SparseCore.BundleConstantsLemmas
public import MinCostFlow.SparseCore.BundleRunInvBase

import Mathlib.Tactic

/-!
# The model premises of Phase 4 of the first step (`AssemblyFirstStepGlue7`)

Phase 4 (`asmFirstP4Sel_runs`) updates the spanners of the touched slots and builds the output
batch. It asks for facts on the bundles and the spanners of the active pairs, before and after
the step. This file proves those that follow from the side model of the state before the step.

* `asmFirstStep_bunReady_all`: the bundle of every active pair of the new state is ready for the
  step. Its component was active before or is newly active, so the bundle is a partition
  (`asmFirstStep_mid_isPartition`), and the batch is ordered.
* `asmFirstStep_bunEdges`: so the step removes from each such bundle exactly the edges that the
  batch deletes (`bundleCompStep_edges_eq`; `hBunEdges` of Phase 4).
* `asmFirstStep_dynG_old` and `asmFirstStep_dynG_new`: the graph of the spanner of an active pair
  has the edges of its bundle, before the step (`AsmFirstActiveDynGraphInv`) and after it
  (`asmFirstActiveDynGraphInv_step`; `hDynG` and `hDynG'` of Phase 4).
* `asmFirstStep_lazy_cover`: every edge of a bundle of a newly active component is in the lazy
  list that Phase 2 wrote for that component (`hN` of Phase 4), and the lazy lists hold only
  such edges (`asmFirstStep_lazy_iff`, `hLazyIff` of Phase 4).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

/-- **Every bundle of the new state is ready for the step.** An active pair of the new state has
a component that was active or that the batch touches and was inactive. In both cases its bundle
is a partition (`asmFirstStep_mid_isPartition`), and the batch is ordered, so the bundle meets
`BundleStepReady`. -/
theorem asmFirstStep_bunReady_all
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ} {y : AsmBrSide B5 depth} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hk : 1 ≤ tr.k) (hBU : tr.cs.G.BatchIsValid U)
    (hOB : OrderedBatch tr.cs.G U ord ord')
    (hPart : AsmFirstActiveBunPartInv tr ord)
    (hInact : AsmFirstInactiveCompInv impl w depth tr ord y) :
    ∀ p ∈ activePairs (stepBundleTree sp tr U ord ord').state,
      BundleStepReady tr.cs (tr.bun p) tr.k ord ord' U := by
  rintro ⟨C, b⟩ hp
  obtain ⟨hC, hb⟩ := mem_activePairs.mp hp
  obtain ⟨ρ, σ, hρ, hσ, hRB⟩ := hOB
  exact ⟨C_lsst, ℓ₀, hI, ρ, σ, hρ, hσ, hRB, hBU,
    asmFirstStep_mid_isPartition (newSet := touchedCompsBatch tr.cs U \ tr.activeComps) hI hk
      hPart hInact (fun C hC => ⟨touchedCompsBatch_subset _ _ (Finset.mem_sdiff.mp hC).1,
        (Finset.mem_sdiff.mp hC).2⟩) C hC b hb ρ hρ⟩

/-- **The step removes the deleted edges from the bundles** (`hBunEdges` of Phase 4). The bundle
of an active pair of the new state is the second part of the bundle step on its old bundle, which
is ready (`asmFirstStep_bunReady_all`), so `bundleCompStep_edges_eq` applies. -/
theorem asmFirstStep_bunEdges
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ} {y : AsmBrSide B5 depth} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hk : 1 ≤ tr.k) (hBU : tr.cs.G.BatchIsValid U)
    (hOB : OrderedBatch tr.cs.G U ord ord')
    (hPart : AsmFirstActiveBunPartInv tr ord)
    (hInact : AsmFirstInactiveCompInv impl w depth tr ord y) :
    ∀ p ∈ activePairs (stepBundleTree sp tr U ord ord').state,
      ((stepBundleTree sp tr U ord ord').state.bun p).edges = (tr.bun p).edges \ batchDeletes U :=
  fun p hp => bundleCompStep_edges_eq (asmFirstStep_bunReady_all sp hI hk hBU hOB hPart hInact p hp)

/-- **The spanners have the edges of the bundles, before the step** (`hDynG` of Phase 4), by
`AsmFirstActiveDynGraphInv`:
the two graphs agree (`GraphEq`), so they have the same edges. -/
theorem asmFirstStep_dynG_old {depth : ℕ} {tr : BundleTreeState depth}
    (hDynG : AsmFirstActiveDynGraphInv tr) :
    ∀ p ∈ activePairs tr, (tr.dyn p).G.E = (tr.bun p).edges := by
  rintro ⟨C, b⟩ hp
  obtain ⟨hC, hb⟩ := mem_activePairs.mp hp
  exact (hDynG C hC b hb).2.1

/-- **The spanners have the edges of the bundles, after the step** (`hDynG'` of Phase 4):
`AsmFirstActiveDynGraphInv` holds for the new state (`asmFirstActiveDynGraphInv_step`). -/
theorem asmFirstStep_dynG_new
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ} {y : AsmBrSide B5 depth} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hBU : tr.cs.G.BatchIsValid U)
    (hOB : OrderedBatch tr.cs.G U ord ord') (hk : 1 ≤ tr.k)
    (hInact : AsmFirstInactiveCompInv impl w depth tr ord y)
    (hInactDyn : AsmFirstInactiveDynInv impl w depth tr y)
    (hPart : AsmFirstActiveBunPartInv tr ord) (hDynG : AsmFirstActiveDynGraphInv tr) :
    ∀ p ∈ activePairs (stepBundleTree sp tr U ord ord').state,
      ((stepBundleTree sp tr U ord ord').state.dyn p).G.E =
        ((stepBundleTree sp tr U ord ord').state.bun p).edges :=
  asmFirstStep_dynG_old
    (asmFirstActiveDynGraphInv_step sp hI hBU hOB hk hInact hInactDyn hPart hDynG)

/-- **The lazy lists cover the bundles of the new components** (`hN` of Phase 4). Phase 2 writes
for the `k`-th new component the list of its core edges (`hlazy`), and the new components are the
newly active ones (`hset`). A bundle of a newly active component agrees with its start bundle
(`AsmFirstInactiveCompInv`), whose edges are core edges with tail in the component
(`initBundleFor_edges_subset`). -/
theorem asmFirstStep_lazy_cover
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ} {y : AsmBrSide B5 depth}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    {comps : List (Finset ℕ)} {newComps : List (ℕ × ℕ)} {lazyE : Fin newComps.length → List ℕ}
    (hInact : AsmFirstInactiveCompInv impl w depth tr ord y)
    (hset : (newComps.map fun q => comps.getD q.1 ∅).toFinset =
      touchedCompsBatch tr.cs U \ tr.activeComps)
    (hlazy : ∀ k (hk : k < newComps.length), (lazyE ⟨k, hk⟩).toFinset =
      compCoreEdges tr (comps.getD (newComps.getD k (0, 0)).1 ∅)) :
    ∀ e ∈ (stepBundleTree sp tr U ord ord').newlyActive.biUnion (fun C =>
        (tr.activeBuckets C).biUnion fun b => (tr.bun (C, b)).edges),
      ∃ i : Fin newComps.length, e ∈ lazyE i := by
  intro e he
  simp only [Finset.mem_biUnion] at he
  obtain ⟨C, hC, b, hb, he⟩ := he
  have hC' : C ∈ touchedCompsBatch tr.cs U \ tr.activeComps := hC
  have hC0 : C ∈ components tr.cs.G₀ := touchedCompsBatch_subset _ _ (Finset.mem_sdiff.mp hC').1
  obtain ⟨-, -, -, -, hB⟩ := hInact C hC0 (Finset.mem_sdiff.mp hC').2
  have heE : e ∈ compCoreEdges tr C := by
    have h1 : e ∈ (initBundleFor tr.cs ord
        (bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket C b) tr.k).edges := by
      rw [(hB b hb).1.2.1]
      exact he
    have h2 := initBundleFor_edges_subset _ _ _ _ h1
    unfold bucketCoreEdges at h2
    unfold compCoreEdges
    simp only [Finset.mem_filter] at h2 ⊢
    exact ⟨h2.1, h2.2.1⟩
  rw [← hset] at hC'
  obtain ⟨q, hq, hqC⟩ := List.mem_map.mp (List.mem_toFinset.mp hC')
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq
  refine ⟨⟨k, hk⟩, List.mem_toFinset.mp ?_⟩
  rw [hlazy k hk, List.getD_eq_getElem _ _ hk, hqC]
  exact heE

/-- **The lazy lists are the edges of the bundles of the new components** (`hLazyIff` of
Phase 4). One way is `asmFirstStep_lazy_cover`. For the other, an edge of the `k`-th lazy list is a
core edge with tail in the `k`-th new component `C`, which is newly active (`hset`). Its bucket
is an active bucket of `C`, and the start bundle of that bucket has exactly the core edges of the
bucket (`initBundleFor_edges`), so the edge is an edge of the bundle (`AsmFirstInactiveCompInv`). -/
theorem asmFirstStep_lazy_iff
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ} {y : AsmBrSide B5 depth} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    {comps : List (Finset ℕ)} {newComps : List (ℕ × ℕ)} {lazyE : Fin newComps.length → List ℕ}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) {ρ : Rotation tr.cs.G} (hρ : ρ.order = ord)
    (hInact : AsmFirstInactiveCompInv impl w depth tr ord y)
    (hset : (newComps.map fun q => comps.getD q.1 ∅).toFinset =
      touchedCompsBatch tr.cs U \ tr.activeComps)
    (hlazy : ∀ k (hk : k < newComps.length), (lazyE ⟨k, hk⟩).toFinset =
      compCoreEdges tr (comps.getD (newComps.getD k (0, 0)).1 ∅)) :
    ∀ e, (∃ i : Fin newComps.length, e ∈ lazyE i) ↔
      e ∈ (stepBundleTree sp tr U ord ord').newlyActive.biUnion (fun C =>
        (tr.activeBuckets C).biUnion fun b => (tr.bun (C, b)).edges) := by
  intro e
  refine ⟨?_, asmFirstStep_lazy_cover sp hInact hset hlazy e⟩
  rintro ⟨⟨k, hk⟩, he⟩
  obtain ⟨C, hCdef⟩ : ∃ C, C = comps.getD (newComps.getD k (0, 0)).1 ∅ := ⟨_, rfl⟩
  have heC : e ∈ compCoreEdges tr C := by
    rw [hCdef, ← hlazy k hk]
    exact List.mem_toFinset.mpr he
  have hCmem : C ∈ touchedCompsBatch tr.cs U \ tr.activeComps := by
    rw [← hset]
    refine List.mem_toFinset.mpr (List.mem_map.mpr ⟨newComps[k], List.getElem_mem hk, ?_⟩)
    rw [hCdef, List.getD_eq_getElem _ _ hk]
  have hC0 : C ∈ components tr.cs.G₀ :=
    touchedCompsBatch_subset _ _ (Finset.mem_sdiff.mp hCmem).1
  obtain ⟨-, hAB, -, -, hB⟩ := hInact C hC0 (Finset.mem_sdiff.mp hCmem).2
  have heCore : e ∈ (coreGraph tr.cs.G tr.cs.lsf).E ∧ (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ C := by
    unfold compCoreEdges at heC
    exact Finset.mem_filter.mp heC
  have hb : tr.origBucket e ∈ tr.activeBuckets C := by
    rw [hAB]
    exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr heCore, rfl⟩
  simp only [Finset.mem_biUnion]
  refine ⟨C, hCmem, tr.origBucket e, hb, ?_⟩
  rw [← (hB _ hb).1.2.1, initBundleFor_edges hI hρ]
  unfold bucketCoreEdges
  exact Finset.mem_filter.mpr ⟨heCore.1, heCore.2, rfl⟩

end

end MinCostFlow.SparseCore.Program
