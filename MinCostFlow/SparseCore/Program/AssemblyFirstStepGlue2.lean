module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue1
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase1Model
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepDriverModel

import Mathlib.Tactic

/-!
# From Phase 1 to Phase 2 of the first step (`AssemblyFirstStepGlue2`)

Phase 2 of the first step of a branch (`asmFirstNewAct_runs`) makes the components that the batch
touches active. The driver calls it on the side record, the tour, and the list of the new
components that Phase 1 wrote. This file proves the premises of Phase 2 that come from Phase 1
(`ScanMemAt`, `scanBatchFold_correct`) and from the side record.

* `asmFirstStep_scan_frame`: the scan keeps every cell below `h + 6` outside the component map
  and the active flags. So the side record keeps all its cells but these
  (`asmFirstStep_side_agree`, the premise `hAgree` of Phase 2), and the tour keeps all its cells
  and its state (`asmFirstStep_tour_after_scan`).
* `asmFirstStep_newComps_at`: the list of the new components at `h + 9 + 2 eCap + vCap`, two
  words per entry (`hNC_at`), and its end below the heap pointer of Phase 2 (`hNC_lt`).
* `asmFirstStep_newComps_ok`: the new components are listed once each (`hNC_nd`), and each entry
  names an inactive component and a vertex of its graph (`hNC_ok`). Their set is the set of the
  newly active components of the step (`newSet_eq_newlyActive`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

/-- **The frame of the scan.** The scan of Phase 1 at `h + 6` keeps every cell below `h + 6` that
is not a cell of the component map `[cmpH, cmpH + vCap)` and not an active flag `ctH + 3 c`. -/
theorem asmFirstStep_scan_frame {mem mem₁ : ℕ → ℕ} {cmpH ctH nComp vCap eCap words h : ℕ}
    {sb : ScanBatchState}
    (hM : ScanMemAt mem mem₁ cmpH ctH nComp vCap eCap words (h + 6) sb) :
    ∀ a < h + 6, (∀ v < vCap, a ≠ cmpH + v) → (∀ c < nComp, a ≠ ctH + 3 * c) → mem₁ a = mem a := by
  intro a ha hv hc
  refine hM.2.2.2.2.2.2.2.2.1 a ha ?_ hc
  by_contra hcon
  exact hv (a - cmpH) (by omega) (by omega)

/-- **The side record after the scan** (`hAgree` of Phase 2): the cells of the side below `h`
are kept, except the component map and the active flags. -/
theorem asmFirstStep_side_agree
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {depth : ℕ}
    {y : AsmBrSide B5 depth} {restH words h : ℕ} {mem mem₁ : ℕ → ℕ} {sb : ScanBatchState}
    (hfootS : ∀ a, asmSdFoot restH y a → a < h)
    (hM : ScanMemAt mem mem₁ y.cmpH y.ctH y.comps.length y.vCap5 y.eCap5 words (h + 6) sb) :
    ∀ a, asmSdFoot restH y a → (∀ c < y.comps.length, a ≠ y.ctH + 3 * c) →
      (∀ v < y.vCap5, a ≠ y.cmpH + v) → mem₁ a = mem a := fun a ha hc hv =>
  asmFirstStep_scan_frame hM a (by have := hfootS a ha; omega) hv hc

/-- **The new components after the scan** (`hNC_at` and `hNC_lt` of Phase 2). The scan at
`h + 6` writes them from `h + 9 + 2 eCap + vCap`, two words each, and there are at most
`2 |U|` of them, below the end `h + 6 + asmFirstScanBatchSpace vCap eCap words` of the scan,
since `2 |U| ≤ words - 1` for a batch of `words` words. -/
theorem asmFirstStep_newComps_at {mem mem₁ : ℕ → ℕ} {cmpH ctH nComp vCap eCap words h : ℕ}
    {sb : ScanBatchState} {U : List Update}
    (hM : ScanMemAt mem mem₁ cmpH ctH nComp vCap eCap words (h + 6) sb)
    (hlen : sb.newComps.length ≤ 2 * U.length) (hUW : 2 * U.length ≤ words - 1) :
    (∀ i (hi : i < sb.newComps.length),
      mem₁ (h + 9 + 2 * eCap + vCap + 2 * i) = (sb.newComps[i]'hi).1 ∧
      mem₁ (h + 9 + 2 * eCap + vCap + 2 * i + 1) = (sb.newComps[i]'hi).2) ∧
    h + 9 + 2 * eCap + vCap + 2 * sb.newComps.length ≤
      h + 6 + asmFirstScanBatchSpace vCap eCap words := by
  have hb : scanNewCompsBase (h + 6) vCap eCap = h + 9 + 2 * eCap + vCap := by
    unfold scanNewCompsBase; omega
  refine ⟨fun i hi => ?_, ?_⟩
  · have := hM.2.2.2.2.2.1 i hi
    rw [hb] at this
    exact this
  · unfold asmFirstScanBatchSpace; omega

/-- **The new components are those the step activates** (`hNC_nd`, `hNC_ok` of Phase 2, and the
set of the new components). By `scanBatchFold_correct`, the scan lists each new component once,
with an index in range, a vertex of its graph, and exactly when the batch touches it and it is not
active. So the set it lists is `touchedCompsBatch \ activeComps` (`newSet_eq_newlyActive`), the
set of the newly active components of the step. -/
theorem asmFirstStep_newComps_ok {depth : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {tr : BundleTreeState depth} {U : List Update} {comps : List (Finset ℕ)} {cmpMap₀ : ℕ → ℕ}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hU : tr.cs.G.BatchIsValid U)
    (hCnd : comps.Nodup) (hCiff : ∀ C, C ∈ comps ↔ C ∈ components tr.cs.G₀)
    (hCmp0 : ∀ c (hc : c < comps.length), ∀ v ∈ (tr.cs.compSt comps[c]).G.V, cmpMap₀ v = c)
    (hCross : AsmFirstCrossInactiveInv tr) :
    let st0 : ScanBatchState :=
      { cmpMap := cmpMap₀
        actFlag := fun c => if hc : c < comps.length then decide (comps[c] ∈ tr.activeComps) else false
        insFlag := fun _ => false
        delFlag := fun _ => false
        origVert := fun _ => 0
        newComps := []
        delEdges := []
        insEdges := [] }
    let sbF := scanBatchFold tr.cs.G st0 U
    (sbF.newComps.map Prod.fst).Nodup ∧
    (∀ q ∈ sbF.newComps, ∃ hc : q.1 < comps.length,
      comps[q.1]'hc ∉ tr.activeComps ∧ q.2 ∈ (tr.cs.compSt (comps[q.1]'hc)).G.V) ∧
    (sbF.newComps.map fun q => comps.getD q.1 ∅).toFinset =
      touchedCompsBatch tr.cs U \ tr.activeComps ∧
    sbF.newComps.length ≤ 2 * U.length ∧
    sbF.delEdges.toFinset = batchDeletes U ∧ sbF.delEdges.length ≤ U.length := by
  intro st0 sbF
  obtain ⟨-, -, -, -, hnd, hlt, hiff, hV, hdel, -, -, hlen, hdlen, -⟩ :=
    scanBatchFold_correct (cmpMap₀ := cmpMap₀) hI hU hCnd hCiff hCmp0 hCross
  refine ⟨hnd, fun q hq => ⟨hlt q hq, ?_, hV q hq (hlt q hq)⟩,
    newSet_eq_newlyActive hlt hiff
      (fun C hC => (hCiff C).mpr (touchedCompsBatch_subset tr.cs U hC)), hlen, hdel, hdlen⟩
  have h := (hiff q.1 (hlt q hq)).mp (List.mem_map.mpr ⟨q, hq, rfl⟩)
  exact (Finset.mem_sdiff.mp h).2

/-- **The tour after the scan.** The cells of the tour lie below `h` and apart from the side, so
the scan keeps them (`asmFirstStep_scan_frame`), and the tour holds the same state after it,
since it is local. -/
theorem asmFirstStep_tour_after_scan {T : DSRep AsmTourAbs} (hT : T.Local)
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {depth : ℕ}
    {y : AsmBrSide B5 depth} {restH tourH words h : ℕ} {A : AsmTourAbs} {tx : T.τ}
    {mem mem₁ : ℕ → ℕ} {sb : ScanBatchState}
    (hrep : T.rep tourH A tx mem) (hfootT : ∀ a, T.foot tourH tx a → a < h)
    (hdisj : ∀ a, T.foot tourH tx a → ¬ asmSdFoot restH y a)
    (hM : ScanMemAt mem mem₁ y.cmpH y.ctH y.comps.length y.vCap5 y.eCap5 words (h + 6) sb) :
    T.rep tourH A tx mem₁ ∧ T.phi tourH tx mem₁ = T.phi tourH tx mem := by
  have hag : ∀ a, T.foot tourH tx a → mem a = mem₁ a := fun a ha =>
    (asmFirstStep_scan_frame hM a (by have := hfootT a ha; omega)
      (fun v hv heq => hdisj a ha ⟨3, by decide, Or.inr ⟨0, by omega, by omega⟩⟩)
      (fun c hc heq => hdisj a ha ⟨3, by decide, Or.inr ⟨2, by omega, by omega⟩⟩)).symm
  have h := hT tourH A tx mem mem₁ hag
  exact ⟨h.1 hrep, h.2.symm⟩

end

end MinCostFlow.SparseCore.Program
