module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue10
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue8
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue4
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepDriverModel

import MinCostFlow.SparseCore.CompLSFBridge
import Mathlib.Tactic

/-!
# The tasks of Phase 4 and small facts of the model (`AssemblyFirstStepGlue11`)

Phase 4 (`asmFirstP4Sel_runs`) asks that the tasks that Phase 3 wrote are the tasks of the slots
(`P4SlotTasks`), that the edges of the batch and the deleted forest edges are below the edge cap,
and that the tasks lie in the cells that Phase 3 wrote. This file proves these facts from the
posts of Phases 2 and 3.

* `asmFirstStep_capsMatch`: the edges of the batch are below the edge cap. An inserted edge is
  by `BatchWithinCaps`, and a deleted edge is a deleted edge of the scan.
* `asmFirstStep_fDel_cap`: the forest edges that the change deletes are old forest edges, hence
  old edges, hence below the edge cap.
* `asmFirstStep_touched_len`: there are at most `slotCap` touched slots, since they are distinct
  and below `slotCap`.
* `asmFirstStep_p4_taskCells`: the batch of each task lies after the descriptors and before the
  end of Phase 3.
* `asmFirstStep_p4_slotTasks`: the tasks are those of the slots (`p4SlotTasks_of_phases`). The
  slots of the active pairs come from Phase 2, the new slots are those after the old ones
  (`p4_newSlots`), and the descriptors come from Phase 3.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

/-- **The edges of the batch are below the edge cap.** An inserted edge is below it by
`BatchWithinCaps`. A deleted edge lies in the list `delEdges` of the deleted edges
(`mem_batchDeletes_iff`, `hdel`), whose edges are below it (`hD`). -/
theorem asmFirstStep_capsMatch {vCap eCap : ℕ} {U : List Update} {delEdges : List ℕ}
    (hCaps : BatchWithinCaps vCap eCap U) (hdel : delEdges.toFinset = batchDeletes U)
    (hD : ∀ e ∈ delEdges, e < eCap) :
    ∀ u ∈ U, match u with
      | .insert e _ _ => e < eCap | .delete e => e < eCap | .split _ _ _ _ => True := by
  intro u hu
  match u, hu with
  | .insert e a b, hu => exact hCaps _ hu
  | .delete e, hu =>
    have he : e ∈ batchDeletes U := (mem_batchDeletes_iff U e).mpr ⟨_, hu, rfl⟩
    rw [← hdel, List.mem_toFinset] at he
    exact hD e he
  | .split _ _ _ _, _ => trivial

/-- **The deleted forest edges are below the edge cap.** The change is exact (`hcEx`), so a
deleted forest edge is an old forest edge. The forest of a valid state is a subgraph of its graph
(`compLSF_RF_isRSF`), whose edges are below the edge cap (`hE`). -/
theorem asmFirstStep_fDel_cap {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {L eCap : ℕ} {tr : BundleTreeState L}
    {U : List Update} {c : LSFChange} (hI : CompLSFInv C_lsst ℓ₀ tr.cs)
    (hcEx : c.Exact tr.cs.lsf (compLSFBatch tr.cs U).lsf) (hE : ∀ e ∈ tr.cs.G.E, e < eCap) :
    ∀ e ∈ c.fDel, e < eCap := by
  intro e he
  rw [← List.mem_toFinset, hcEx.2.2.2] at he
  have he' : e ∈ tr.cs.RF.F.E \ (compLSFBatch tr.cs U).RF.F.E := he
  exact hE e ((compLSF_RF_isRSF hI).2.2.2.2.2.1 (Finset.mem_sdiff.mp he').1)

/-- **There are at most `slotCap` touched slots**: the list has no repeats, and its entries lie
in `[0, slotCap)`. -/
theorem asmFirstStep_touched_len {l : List ℕ} {n : ℕ} (hnd : l.Nodup) (hlt : ∀ s ∈ l, s < n) :
    l.length ≤ n := by
  rw [← List.toFinset_card_of_nodup hnd]
  calc l.toFinset.card ≤ (Finset.range n).card :=
        Finset.card_le_card fun s hs => Finset.mem_range.mpr (hlt s (List.mem_toFinset.mp hs))
    _ = n := Finset.card_range n

/-- **The batches of the tasks lie in the cells of Phase 3.** A task is the descriptor at some
index `i` (`mem_p4TasksOf`), and Phase 3 put the batch of descriptor `i` after the descriptors and
before its end (`hdesc`). -/
theorem asmFirstStep_p4_taskCells {mem : ℕ → ℕ} {outDescPtr slotCap hEnd : ℕ}
    {touched : List ℕ}
    (hdesc : ∀ i (_hi : i < touched.length), ∃ (batchPtr totalWords : ℕ),
      mem (outDescPtr + 1 + 3 * i + 1) = batchPtr ∧
      mem (outDescPtr + 1 + 3 * i + 2) = totalWords ∧
      outDescPtr + 1 + 3 * slotCap ≤ batchPtr ∧ batchPtr + totalWords ≤ hEnd) :
    ∀ t ∈ p4TasksOf mem (outDescPtr + 1) touched.length,
      outDescPtr + 1 + 3 * slotCap ≤ t.batchPtr ∧ t.batchPtr + t.W ≤ hEnd := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := mem_p4TasksOf ht
  obtain ⟨bp, tw, h1, h2, h3, h4⟩ := hdesc i hi
  dsimp only
  rw [h1, h2]
  exact ⟨h3, h4⟩

set_option maxHeartbeats 800000 in
/-- **The tasks of Phase 4 are those of the slots** (`P4SlotTasks`), for the state `tr_mid` with
the new components `newSet` made active.
* The active pairs after the step are those of `tr_mid` (`activePairs_mid_eq`, `hset`).
* Phase 2 gives each pair of `tr_mid` a spanner with the right state (`hspan`), keeps the slots
  of the old pairs (`hkeep`) and puts the slots `[0, n₁)` in one to one use (`hNew`, `hNewRange`).
  So the new pairs sit in `[|oldSlots|, n₁)`, and each of these slots is the slot of a pair
  (`p4_newSlots`, with the old slot map `hOld`).
* The bundle table after Phase 2 matches the pairs (`hMatch`), and its unused slots are empty
  (`hFree`). So it has the bundle of each pair in its slot, each used slot is the slot of a pair,
  and the slot map is one to one on the pairs (`asmFirstStep_phase3_slots`).
* The descriptors of Phase 3 (`hdesc`, `hnone`, `huntouched`) and the graphs of the dynamic
  spanners (`hDynG`) are the rest of the premises of `p4SlotTasks_of_phases`. -/
theorem asmFirstStep_p4_slotTasks {P : DSParams} {cap slotCap slotCapO capO slotCapN capN n₁ : ℕ}
    {tr : BundleTreeState P.L} {U : List Update} {ord ord' : ℕ → List End}
    {newSet : Finset (Finset ℕ)} {slotOfOld slotOf : Finset ℕ × ℤ → ℕ}
    {oldSlots newSlots : List ℕ} {S6 : BucketSpannerState cap} {S₀ : BundleTableState slotCap}
    {mem₀ : ℕ → ℕ} {outDescPtr hEnd : ℕ} {touched : List ℕ}
    (hset : newSet = touchedCompsBatch tr.cs U \ tr.activeComps)
    (hspan : ∀ q ∈ activePairs { tr with activeComps := tr.activeComps ∪ newSet },
      ∃ (hs : slotOf q < cap) (d : DSHist), S6 ⟨slotOf q, hs⟩ = some d ∧ d.state P = tr.dyn q)
    (hOld : SlotMapOK tr slotCapO capO oldSlots slotOfOld)
    (hOldRange : oldSlots = List.range oldSlots.length)
    (hNew : SlotMapOK { tr with activeComps := tr.activeComps ∪ newSet } slotCapN capN newSlots
      slotOf)
    (hNewRange : newSlots = List.range n₁)
    (hkeep : ∀ q ∈ activePairs tr, slotOf q = slotOfOld q)
    (hSlot : SlotMapOK { tr with activeComps := tr.activeComps ∪ newSet } slotCap cap newSlots
      slotOf)
    (hMatch : BunTableMatches { tr with activeComps := tr.activeComps ∪ newSet } slotOf S₀)
    (hFree : ∀ j : Fin slotCap, j.1 ∉ newSlots → S₀ j = none)
    (hReady : ∀ j B₀, S₀ j = some B₀ → BundleStepReady tr.cs B₀ tr.k ord ord' U)
    (hDynG : ∀ q ∈ activePairs
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
      GraphEq (tr.dyn q).G (tr.bun q).graph)
    (hnd : touched.Nodup)
    (hdesc : ∀ i (hi : i < touched.length),
      let s := touched[i]'hi
      ∃ (hs : s < slotCap) (batchPtr totalWords : ℕ),
        mem₀ (outDescPtr + 1 + 3 * i) = s ∧
        mem₀ (outDescPtr + 1 + 3 * i + 1) = batchPtr ∧
        mem₀ (outDescPtr + 1 + 3 * i + 2) = totalWords ∧
        outDescPtr + 1 + 3 * slotCap ≤ batchPtr ∧ batchPtr + totalWords ≤ hEnd ∧
        ∀ B₀, S₀ ⟨s, hs⟩ = some B₀ →
          SmallBatchAt mem₀ batchPtr B₀.graph (bundleCompStep tr.cs B₀ tr.k ord ord' U).1
            totalWords)
    (huntouched : ∀ j B₀, S₀ j = some B₀ → j.1 ∉ touched →
      (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 = [])
    (hnone : ∀ j : Fin slotCap, S₀ j = none → j.1 ∉ touched) :
    P4SlotTasks P tr (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord') slotOf S6
      mem₀ (p4TasksOf mem₀ (outDescPtr + 1) touched.length) oldSlots.length n₁ := by
  have hAP := activePairs_mid_eq (fun _ => canonicalSparsify P.impl) tr U ord ord' hset
  obtain ⟨hMatch0, hBunNone, hinj⟩ := asmFirstStep_phase3_slots
    (tr' := (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state)
    hAP rfl hSlot hMatch hFree
  have hmono : ∀ q ∈ activePairs tr,
      q ∈ activePairs { tr with activeComps := tr.activeComps ∪ newSet } := by
    intro q hq
    rw [mem_activePairs] at hq ⊢
    exact ⟨Finset.mem_union_left _ hq.1, hq.2⟩
  obtain ⟨hnew, hnewSlot⟩ := p4_newSlots hOld hOldRange hNew hNewRange hkeep hmono
  rw [hAP] at hspan hnew hnewSlot
  refine p4SlotTasks_of_phases hspan hinj hMatch0 hBunNone hReady hDynG hnd (fun i hi => ?_)
    hnone huntouched hnew hnewSlot
  obtain ⟨hs, bp, tw, h0, h1, h2, -, -, hB⟩ := hdesc i hi
  refine ⟨hs, h0, fun B₀ hB₀ => ?_⟩
  rw [h1, h2]
  exact (hB B₀ hB₀).1

end

end MinCostFlow.SparseCore.Program
