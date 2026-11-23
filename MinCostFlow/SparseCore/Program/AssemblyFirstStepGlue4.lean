module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue3
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase3Proof
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGroupsModel
public import MinCostFlow.SparseCore.Program.AssemblyBranchSideGapS8

import Mathlib.Tactic

/-!
# The model premises of Phase 3 of the first step (`AssemblyFirstStepGlue4`)

Phase 3 (`asmFirstPhase3_runs`) runs the step of the bundle table and the step of the tour. It
asks for facts on the slots of the table that Phase 2 leaves, on the bundles in them, and on the
marks of the tour. This file proves them from the post of Phase 2 and from the side model of the
state before the step.

* `asmFirstStep_mid_isPartition`: after Phase 2, every bundle of an active pair is a partition of
  the ends of its core edges. For a pair that was active before, the side model says so
  (`AsmFirstActiveBunPartInv`). For a pair of a newly active component, the bundle agrees with
  the start bundle `initBundleFor` (`AsmFirstInactiveCompInv`), which is a partition
  (`initBundleFor_isPartition`).
* `asmFirstStep_phase3_slots`: the slots of the table after Phase 2 hold the bundles of the active
  pairs of the new state, the full slots are slots of such pairs, and two pairs never share a
  slot (`hMatch0`, `hBunNone`, `hSlotInj`).
* `asmFirstStep_phase3_ready`: every bundle in the table is ready for the step (`hBReady`).
* `asmFirstStep_marks_old`: the marks of the tour before the step, on the core lists
  `coreTour ord RF` (`hMarks`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

/-- **The bundles after Phase 2 are partitions.** Let `newSet` hold only components of the first
graph that are not active. Then for every component active after Phase 2, every active bucket,
and every rotation of the order `ord`, the bundle of the pair is a partition. -/
theorem asmFirstStep_mid_isPartition
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ} {y : AsmBrSide B5 depth} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {tr : BundleTreeState depth} {ord : ℕ → List End} {newSet : Finset (Finset ℕ)}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hk : 1 ≤ tr.k)
    (hPart : AsmFirstActiveBunPartInv tr ord)
    (hInact : AsmFirstInactiveCompInv impl w depth tr ord y)
    (hNew : ∀ C ∈ newSet, C ∈ components tr.cs.G₀ ∧ C ∉ tr.activeComps) :
    ∀ C ∈ tr.activeComps ∪ newSet, ∀ b ∈ tr.activeBuckets C,
      ∀ (ρ : Rotation tr.cs.G), ρ.order = ord →
        (tr.bun (C, b)).IsPartition
          (coreRotation (L := tr.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) tr.k := by
  intro C hC b hb ρ hρ
  rcases Finset.mem_union.mp hC with hC | hC
  · exact hPart C hC b hb C_lsst ℓ₀ hI ρ hρ
  · obtain ⟨hC0, hna⟩ := hNew C hC
    obtain ⟨-, -, -, -, hB⟩ := hInact C hC0 hna
    exact (bunAgree_isPartition_iff (hB b hb).1).mp
      (initBundleFor_isPartition hI ρ hρ (Finset.filter_subset _ _) hk)

/-- **The slots after Phase 2.** Let the state `trA` after Phase 2 have the active pairs of the
new state `tr'` and the bundles of the old state `tr`. If its slot map is fine, its table matches
it, and the slots outside the list are empty, then the table holds a bundle that agrees with the
old bundle at the slot of each active pair of `tr'`, each full slot is the slot of such a pair,
and the slot map is one to one on these pairs. -/
theorem asmFirstStep_phase3_slots {L slotCap cap : ℕ} {tr trA tr' : BundleTreeState L}
    {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ} {S : Fin slotCap → Option BundleState}
    (hAP : activePairs trA = activePairs tr') (hbun : trA.bun = tr.bun)
    (hSlot : SlotMapOK trA slotCap cap slots slotOf) (hMatch : BunTableMatches trA slotOf S)
    (hFree : ∀ j : Fin slotCap, j.1 ∉ slots → S j = none) :
    (∀ q ∈ activePairs tr', ∃ (hs : slotOf q < slotCap) (B : BundleState),
      S ⟨slotOf q, hs⟩ = some B ∧ BunAgree B (tr.bun q)) ∧
    (∀ j : Fin slotCap, S j ≠ none → ∃ q ∈ activePairs tr', slotOf q = j.1) ∧
    (∀ q₁ ∈ activePairs tr', ∀ q₂ ∈ activePairs tr', slotOf q₁ = slotOf q₂ → q₁ = q₂) := by
  refine ⟨fun q hq => ?_, fun j hj => ?_, fun q₁ h₁ q₂ h₂ => hSlot.2.2.2.1 q₁ (hAP ▸ h₁) q₂
    (hAP ▸ h₂)⟩
  · obtain ⟨hs, B, hB, hag⟩ := hMatch q (hAP ▸ hq)
    exact ⟨hs, B, hB, hbun ▸ hag⟩
  · have hjs : j.1 ∈ slots := by
      by_contra hn
      exact hj (hFree j hn)
    obtain ⟨q, hq, hqj⟩ := hSlot.2.2.1 j.1 hjs
    exact ⟨q, hAP ▸ hq, hqj⟩

/-- **The bundles in the table are ready for the step** (`hBReady` of Phase 3). The table after
Phase 2 matches the state `tr_mid` with the new components active. Its bundles are partitions
(`asmFirstStep_mid_isPartition`), so `bundleStepReady_of_active_slot` applies. -/
theorem asmFirstStep_phase3_ready
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth slotCap cap : ℕ} {y : AsmBrSide B5 depth} {C_lsst : ℝ}
    {ℓ₀ : ℕ → ℝ} {tr : BundleTreeState depth} {ord ord' : ℕ → List End} {U : List Update}
    {newSet : Finset (Finset ℕ)} {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S : BundleTableState slotCap}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hk : 1 ≤ tr.k) (hBU : tr.cs.G.BatchIsValid U)
    (hOB : OrderedBatch tr.cs.G U ord ord')
    (hPart : AsmFirstActiveBunPartInv tr ord)
    (hInact : AsmFirstInactiveCompInv impl w depth tr ord y)
    (hNew : ∀ C ∈ newSet, C ∈ components tr.cs.G₀ ∧ C ∉ tr.activeComps)
    (hSlot : SlotMapOK { tr with activeComps := tr.activeComps ∪ newSet } slotCap cap slots slotOf)
    (hMatch : BunTableMatches { tr with activeComps := tr.activeComps ∪ newSet } slotOf S)
    (hFree : ∀ j : Fin slotCap, j.1 ∉ slots → S j = none) :
    ∀ j B₀, S j = some B₀ → BundleStepReady tr.cs B₀ tr.k ord ord' U :=
  bundleStepReady_of_active_slot (tr := { tr with activeComps := tr.activeComps ∪ newSet })
    hI hBU hOB (asmFirstStep_mid_isPartition hI hk hPart hInact hNew) hSlot hMatch hFree

/-- **The marks of the tour before the step** (`hMarks` of Phase 3). The core lists of the view
are `coreTour ord RF` (`tourCordOK_eq_coreTour`), so the marks of the view are marks on these
lists. -/
theorem asmFirstStep_marks_old {depth : ℕ} {tr : BundleTreeState depth} {ord : ℕ → List End}
    {s : OutTourAbs} (hok : TourCordOK ord tr.cs.RF (outCoreOrder tr ord))
    (hM : OutMarksOf s (outCoreOrder tr ord) tr.S_cur.E) :
    OutMarksOf ⟨coreTour ord tr.cs.RF, s.marked⟩ (outCoreOrder tr ord) tr.S_cur.E :=
  ⟨funext fun r => (tourCordOK_eq_coreTour hok r).symm, hM.2⟩

end

end MinCostFlow.SparseCore.Program
