module

public import MinCostFlow.SparseCore.Program.AssemblyBranchSide
public import MinCostFlow.SparseCore.Program.AssemblyInputRun

import MinCostFlow.Chain.Cycles
import MinCostFlow.DynSpanner.Correctness
import MinCostFlow.DynSpanner.Program.CanonicalSparsify

/-!
# Facts for the driver of the first step (`AssemblyFirstStepPhase5Facts`)

The driver of the first step (Phase 5) reads the maps of the bundle side and hands the component
map to the scan of Phase 1 (`asmFirstScanBatch_runs`). The scan asks two things of the map: it is
in range on every vertex of the current graph, and it sends each vertex of a component graph to
the index of its component. This file proves both from the maps of the side (`AsmSdMapsAt`).
It also proves the fact `hWalkNew` of Phase 4 (`p4_hWalkNew`).
* `asmSdMaps_cmp_ok`: the map sends each vertex of a component graph to the index of its
  component. This is a field of `AsmSdMapsAt`.
* `asmSdMaps_cmp_lt`: the map is in range on every vertex of the current graph. A vertex of the
  graph is a vertex of some component graph (`CompLSFInv.hV_eq`), and the map sends it to the
  index of that component.
* `walk_mem_H_of_updatesBelow` and `p4_hWalkNew`: in the spanner of a pair, the walk of each
  edge of the graph uses only edges of the spanner. The state of the spanner is a run of the
  dynamic spanner from its first graph (`BranchUpdatesBelow`), so the embedding clause of
  Lemma 5.6 (`DynSpanner.lemma_5_6`) holds for it. This is how
  `AssemblyContractLayoutTopEmb.lean` (line 196) uses the lemma.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.LSF MinCostFlow.Bundle MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

public section

/-- The component map of the side sends each vertex of a component graph to the index of its
component in the list of components. -/
theorem asmSdMaps_cmp_ok
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {w depth s : ℕ} {a : AsmBranchAbs depth} {y : AsmBrSide B5 depth} {mem : ℕ → ℕ}
    (hS : AsmSdMapsAt w s a y mem) :
    ∀ c (hc : c < y.comps.length), ∀ v ∈ (a.tr.cs.compSt y.comps[c]).G.V,
      mem (y.cmpH + v) = c :=
  fun c hc v hv => (hS.2.2.2.2.2.2.1 c hc v hv).2

/-- **The component map is in range.** The component map of the side is in range on every vertex of
the current graph. Such a vertex lies in the graph of some component (`CompLSFInv.hV_eq`), and the
map sends it to the index of that component (`asmSdMaps_cmp_ok`). -/
theorem asmSdMaps_cmp_lt
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {w depth s : ℕ} {a : AsmBranchAbs depth} {y : AsmBrSide B5 depth} {mem : ℕ → ℕ}
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} (hI : CompLSFInv C_lsst ℓ₀ a.tr.cs)
    (hS : AsmSdMapsAt w s a y mem) :
    ∀ v ∈ a.tr.cs.G.V, mem (y.cmpH + v) < y.comps.length := by
  intro v hv
  rw [← hI.hV_eq, Finset.mem_biUnion] at hv
  obtain ⟨C, hC, hvC⟩ := hv
  obtain ⟨c, hc, rfl⟩ := List.mem_iff_getElem.mp ((hS.2.2.2.2.2.1 C).mpr hC)
  rw [asmSdMaps_cmp_ok hS c hc v hvC]
  exact hc

/-- In the spanner of a pair `(C, b)` with `C` a component of the first graph, the walk of each
edge of the graph uses only edges of the spanner. The state is the run of the dynamic spanner on
the list `us` of `BranchUpdatesBelow`, so `DynSpanner.lemma_5_6` applies; its graph is the first
graph after `us` (`runState_t_and_G`). -/
theorem walk_mem_H_of_updatesBelow {depth : ℕ} {impl : SparsifyImpl} {tr : BundleTreeState depth}
    {n : ℕ} (hdepth : 1 ≤ depth) (hB : BranchUpdatesBelow impl tr n)
    {C : Finset ℕ} (hC : C ∈ components tr.cs.G₀) (b : ℤ) :
    ∀ g ∈ (tr.dyn (C, b)).G.E, ∀ x ∈ walkEdges (piTotal (tr.dyn (C, b)) g),
      x ∈ (tr.dyn (C, b)).H.E := by
  obtain ⟨hV, hm, -, -, -, -, -, -, -, us, hBV, hds, -, -, -, -, hst⟩ := hB.2 C hC b
  have hEmb := (DynSpanner.lemma_5_6 hV hdepth
    (le_trans (by decide) (two_le_phaseBase ((tr.initBunG (C, b)).n + tr.splitBound) depth))
    hm (canonicalSparsify_spec_absorb impl tr.m₀) hBV hds (k := us.length) le_rfl).2
  obtain ⟨-, hG_run⟩ := runState_t_and_G (L := depth) (tr.initBunG (C, b))
    (phaseBase ((tr.initBunG (C, b)).n + tr.splitBound) depth) (canonicalSparsify impl) us
    us.length le_rfl
  rw [← hG_run, ← hst] at hEmb
  intro g hg x hx
  exact MinCostFlow.Chain.mem_E_of_mem_walkEdges (hEmb.2 g hg) hx

/-- **`hWalkNew`** (a hypothesis of `p4SpanWV_cover` and `asmFirstP4Sel_runs`), for every active
pair of a state `tr'`. The components of the active pairs are components of the first graph
(`RestartScurModelInv`), so `walk_mem_H_of_updatesBelow` applies. The driver of the step takes
`tr' = info.state`, with `BranchUpdatesBelow` of the new state (a hypothesis of
`AsmBrCoreStepAt.runs`). -/
theorem p4_hWalkNew {depth : ℕ} {impl : SparsifyImpl} {tr' : BundleTreeState depth} {n : ℕ}
    (hdepth : 1 ≤ depth) (hB : BranchUpdatesBelow impl tr' n) (hMod : RestartScurModelInv tr') :
    ∀ p ∈ activePairs tr', ∀ g ∈ (tr'.dyn p).G.E, ∀ x ∈ walkEdges (piTotal (tr'.dyn p) g),
      x ∈ (tr'.dyn p).H.E := by
  classical
  intro p hp
  simp only [activePairs, Finset.mem_biUnion, Finset.mem_image] at hp
  obtain ⟨C, hC, b, -, rfl⟩ := hp
  exact walk_mem_H_of_updatesBelow hdepth hB (hMod.1 hC) b

end

end MinCostFlow.SparseCore.Program
