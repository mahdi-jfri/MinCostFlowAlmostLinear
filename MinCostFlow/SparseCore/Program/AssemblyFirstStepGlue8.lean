module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue7
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4SlotTasks
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase5Facts
public import MinCostFlow.DynSpanner.Program.DynSpannerDSPrefix
public import MinCostFlow.DynSpanner.Correctness

import Mathlib.Tactic

/-!
# The spanners of the step apply their own batches (`AssemblyFirstStepGlue8`)

Phase 4 asks (`hHApply` of `asmFirstP4Sel_runs`) that the spanner of each active pair of the new
state is the spanner before the step with the batch `U_H` of the step applied. This holds for the
dynamic spanner of Theorem 8.2 on every run from its first graph (`DynSpanner.batchTrace_spec`).
The state of the spanner of a pair before the step is such a run, on the list `us` of
`BranchUpdatesBelow`. The step feeds it the bundle batch `U_B` of the pair, which is valid on the
bundle graph (`bundleCompStep_spec`), hence on the graph of the spanner, which agrees with it
(`p4_dynGraphEq`). So the trace of the two batches `[us, U_B]` gives the claim
(`asmFirstStep_hHApply`). This is the route of `hDyn_UH` in `Chain/BundleRestartSCur.lean`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

/-- **The spanners apply their batches** (`hHApply` of Phase 4). For each active pair `p` of the
new state, the spanner of `p` after the step is the old spanner with the batch `U_H` of the step
of `p` applied. -/
theorem asmFirstStep_hHApply
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth n : ℕ} {y : AsmBrSide B5 depth} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    (hdepth : 1 ≤ depth) (hB : BranchUpdatesBelow impl tr n)
    (hMod : RestartScurModelInv tr)
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hk : 1 ≤ tr.k) (hBU : tr.cs.G.BatchIsValid U)
    (hOB : OrderedBatch tr.cs.G U ord ord')
    (hPart : AsmFirstActiveBunPartInv tr ord)
    (hInact : AsmFirstInactiveCompInv impl w depth tr ord y)
    (hInactDyn : AsmFirstInactiveDynInv impl w depth tr y)
    (hDynG : AsmFirstActiveDynGraphInv tr) :
    ∀ p ∈ activePairs (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').state,
      (tr.dyn p).H.applyBatch
          ((stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').stepOut p).UH =
        ((stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').state.dyn p).H := by
  rintro ⟨C, b⟩ hp
  have sp_def : (fun _ => canonicalSparsify impl :
      ℕ → MGraph → MGraph → Embedding → SparsifyOut) = fun _ => canonicalSparsify impl := rfl
  obtain ⟨hC, -⟩ := mem_activePairs.mp hp
  have hC0 : C ∈ components tr.cs.G₀ := by
    rcases Finset.mem_union.mp hC with hOld | hNew
    · exact hMod.1 hOld
    · exact touchedCompsBatch_subset _ _ (Finset.mem_sdiff.mp hNew).1
  obtain ⟨hV, hm, -, -, -, -, -, -, -, us, hBV, hds, -, -, -, -, hst⟩ := hB.2 C hC0 b
  have hReady := asmFirstStep_bunReady_all (fun _ => canonicalSparsify impl) hI hk hBU hOB hPart
    hInact (C, b) hp
  have hspec := bundleCompStep_spec hReady
  have hGE := p4_dynGraphEq (fun _ => canonicalSparsify impl) hInact hInactDyn hDynG (C, b) hp
  set UB := (bundleCompStep tr.cs (tr.bun (C, b)) tr.k ord ord' U).1 with hUB
  have hUBv : (tr.dyn (C, b)).G.BatchIsValid UB := (graphEq_batchIsValid hGE UB).mpr hspec.2.1
  have hUBds : ∀ u ∈ UB, isDelOrSplit u := hspec.2.2.2.1
  set G₀ := tr.initBunG (C, b) with hG₀
  set q := phaseBase (G₀.n + tr.splitBound) depth with hq
  have hq1 : 1 ≤ q := le_trans (by decide) (two_le_phaseBase _ _)
  have hSpec := canonicalSparsify_spec_absorb impl tr.m₀
  have hGeq : (tr.dyn (C, b)).G = G₀.applyBatch us := by
    have h := (runInv_all (L := depth) hV hdepth hq1 hm hSpec hBV hds us.length le_rfl).1.G_eq
    rw [hst]
    simpa [List.take_length] using h
  have hBV2 : G₀.BatchIsValid [us, UB].flatten := by
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    exact batchIsValid_append.mpr ⟨hBV, hGeq ▸ hUBv⟩
  have hds2 : ∀ u ∈ [us, UB].flatten, isDelOrSplit u := by
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    intro u hu
    rcases List.mem_append.mp hu with h1 | h2
    · exact hds u h1
    · exact hUBds u h2
  have hTr := batchTrace_spec (L := depth) hV hdepth hq1 hm hSpec hBV2 hds2
  have hk₀ : batchPrefixLen [us, UB] 1 = us.length := by simp [batchPrefixLen]
  have hfl : [us, UB].flatten = us ++ UB := by simp
  have hS1 := (hTr.1 1 (by simp)).1
  have hR := hTr.2 1 (by simp) UB (by simp)
  dsimp only at hR
  obtain ⟨hres, -, -, hH, -⟩ := hR
  rw [hk₀, hfl, runState_append G₀ q (canonicalSparsify impl) us UB us.length le_rfl,
    ← hst] at hres
  rw [hS1, hk₀, hfl, runState_append G₀ q (canonicalSparsify impl) us UB us.length le_rfl,
    ← hst, hres] at hH
  exact hH

end

end MinCostFlow.SparseCore.Program
