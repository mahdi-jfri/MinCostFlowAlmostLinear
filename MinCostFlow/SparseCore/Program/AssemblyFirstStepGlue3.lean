module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue2
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActProof

import Mathlib.Tactic

/-!
# The premises of Phase 2 of the first step (`AssemblyFirstStepGlue3`)

Phase 2 (`asmFirstNewAct_runs`) starts where the scan of Phase 1 ends. Its premises come from
three places: the side record of the branch before the step, the tour before the step, and the
memory that the scan leaves (`ScanMemAt`). This file collects them in one lemma,
`asmFirstStep_phase2_pre`, for the scan state `asmFirstScanStart` that Phase 1 starts from
(`asmFirstStep_phase1_runs`).

The side model gives the start spanner states of the inactive components (`hInactiveDyn`). The list
of the new components sits above `h + 6`, so it is apart from the side and the tour, which lie below
`h`. The rest comes from `AssemblyFirstStepGlue2`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

@[expose] public section

/-- **The state of the scan before the batch**: the component map read from the cells
`cmpH + v`, the active flags of the components `comps` (active when they lie in `act`), and
nothing else. -/
def asmFirstScanStart (mem : ℕ → ℕ) (cmpH : ℕ) (comps : List (Finset ℕ))
    (act : Finset (Finset ℕ)) : ScanBatchState :=
  { cmpMap := fun v => mem (cmpH + v)
    actFlag := fun c => if hc : c < comps.length then decide (comps[c] ∈ act) else false
    insFlag := fun _ => false
    delFlag := fun _ => false
    origVert := fun _ => 0
    newComps := []
    delEdges := []
    insEdges := [] }

end

public section

/-- **The premises of Phase 2.** Take the side record `y` of the branch before the step, the
tour at `tourH`, both below `h` and apart, and the memory `mem₁` that the scan of Phase 1 leaves
at `h + 6`. Then Phase 2 can run on the side, the tour and the list of the new components at
`h + 9 + 2 eCap + vCap`:
* the side keeps its cells but the component map and the active flags (`hAgree`);
* the inactive components hold their start spanner states (`hInactiveDyn`, from the side model);
* the tour holds the same state, with the same potential;
* the list of the new components is in place, ends below the end of the scan, is apart from the
  side and the tour, lists each component once, and names inactive components with a vertex of
  their graph (`hNC_*`);
* the memory is zero from the end of the scan.
It also gives the set of the new components, `touchedCompsBatch \ activeComps`, and the deleted
edges of the scan, which Phase 3 reads. -/
theorem asmFirstStep_phase2_pre {TR : ℕ → ℕ → DSRep AsmTourAbs} (hTR_loc : ∀ v e, (TR v e).Local)
    {impl : SparsifyImpl} {w depth L capExp limbMul : ℕ} {Ψ : BundleTreeState depth → ℕ}
    {restH tourH words h : ℕ} {tr : BundleTreeState depth} {ord : ℕ → List End}
    {mk : Finset End} {U : List Update}
    {y : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth}
    {tx₀ : (TR y.vCap5 y.eCap5).τ} {mem mem₁ : ℕ → ℕ}
    (hSide : AsmBrSideAt (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w depth L capExp limbMul Ψ restH ⟨tr, ord, y.vCap5, y.eCap5⟩ y mem)
    (hrepT : (TR y.vCap5 y.eCap5).rep tourH ⟨ord, tr.cs.RF, mk⟩ tx₀ mem)
    (hfootSide : ∀ a, asmSdFoot restH y a → a < h)
    (hfootT : ∀ a, (TR y.vCap5 y.eCap5).foot tourH tx₀ a → a < h)
    (hdisjST : ∀ a, asmSdFoot restH y a → ¬ (TR y.vCap5 y.eCap5).foot tourH tx₀ a)
    (hU : tr.cs.G.BatchIsValid U) (hUW : 2 * U.length ≤ words - 1)
    (hM : ScanMemAt mem mem₁ y.cmpH y.ctH y.comps.length y.vCap5 y.eCap5 words (h + 6)
      (scanBatchFold tr.cs.G (asmFirstScanStart mem y.cmpH y.comps tr.activeComps) U)) :
    let sbF := scanBatchFold tr.cs.G (asmFirstScanStart mem y.cmpH y.comps tr.activeComps) U
    let ncPtr := h + 9 + 2 * y.eCap5 + y.vCap5
    let hScan := h + 6 + asmFirstScanBatchSpace y.vCap5 y.eCap5 words
    (∀ a, asmSdFoot restH y a → (∀ c < y.comps.length, a ≠ y.ctH + 3 * c) →
      (∀ v < y.vCap5, a ≠ y.cmpH + v) → mem₁ a = mem a) ∧
    (∀ C ∈ components tr.cs.G₀, C ∉ tr.activeComps →
      ∀ b ∈ tr.activeBuckets C,
        tr.dyn (C, b) = DSHist.state (asmBrSP impl w depth y) ⟨tr.initBunG (C, b), []⟩) ∧
    (TR y.vCap5 y.eCap5).rep tourH ⟨ord, tr.cs.RF, mk⟩ tx₀ mem₁ ∧
    (TR y.vCap5 y.eCap5).phi tourH tx₀ mem₁ = (TR y.vCap5 y.eCap5).phi tourH tx₀ mem ∧
    (∀ i (hi : i < sbF.newComps.length),
      mem₁ (ncPtr + 2 * i) = (sbF.newComps[i]'hi).1 ∧
      mem₁ (ncPtr + 2 * i + 1) = (sbF.newComps[i]'hi).2) ∧
    ncPtr + 2 * sbF.newComps.length ≤ hScan ∧
    (∀ a, ncPtr ≤ a → a < ncPtr + 2 * sbF.newComps.length →
      ¬ asmSdFoot restH y a ∧ ¬ (TR y.vCap5 y.eCap5).foot tourH tx₀ a) ∧
    (sbF.newComps.map Prod.fst).Nodup ∧
    (∀ q ∈ sbF.newComps, ∃ hc : q.1 < y.comps.length,
      y.comps[q.1]'hc ∉ tr.activeComps ∧ q.2 ∈ (tr.cs.compSt (y.comps[q.1]'hc)).G.V) ∧
    ZeroFrom mem₁ hScan ∧
    (sbF.newComps.map fun q => y.comps.getD q.1 ∅).toFinset =
      touchedCompsBatch tr.cs U \ tr.activeComps ∧
    sbF.newComps.length ≤ 2 * U.length ∧
    sbF.delEdges.toFinset = batchDeletes U ∧ sbF.delEdges.length ≤ U.length := by
  intro sbF ncPtr hScan
  have hSide' := hSide
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMaps, hMod⟩ := hSide'
  obtain ⟨-, -, -, -, -, -, hLSF, -, -, -, -, -, -, -, -, -, -, -, -, -, hCross, hDyn, -⟩ := hMod
  obtain ⟨C_lsst, ℓ₀, hI, -⟩ := hLSF
  have hMaps' := hMaps
  obtain ⟨-, -, -, -, hCnd, hCiff, -⟩ := hMaps'
  obtain ⟨hnd, hok, hset, hlen, hdel, hdlen⟩ :=
    asmFirstStep_newComps_ok (cmpMap₀ := fun v => mem (y.cmpH + v)) hI hU hCnd hCiff
      (asmSdMaps_cmp_ok hMaps) hCross
  obtain ⟨hat, hlt⟩ := asmFirstStep_newComps_at hM hlen hUW
  obtain ⟨hT1, hT2⟩ := asmFirstStep_tour_after_scan (hTR_loc _ _) hrepT hfootT
    (fun a ha hs => hdisjST a hs ha) hM
  refine ⟨asmFirstStep_side_agree hfootSide hM, hDyn, hT1, hT2, hat, hlt, ?_, hnd, hok,
    hM.2.2.2.2.2.2.2.2.2, hset, hlen, hdel, hdlen⟩
  intro a ha _
  exact ⟨fun hs => by have := hfootSide a hs; omega,
    fun hs => by have := hfootT a hs; omega⟩

end

end MinCostFlow.SparseCore.Program
