module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4SelHyps
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSplitEnds
public import MinCostFlow.SparseCore.Program.AssemblyBranchSideInv

import MinCostFlow.SparseCore.Program.AssemblyBranchSideGapS8
import MinCostFlow.SparseCore.Program.BundleModelBridgeStep
import MinCostFlow.SparseCore.BundleSpanCharge
import Mathlib.Tactic

/-!
# The tasks of Phase 4 follow the slot model (`AssemblyFirstStepP4SlotTasks`)

Phase 4 updates the bucket spanner of each slot that Phase 3 touched, with the batch that Phase 3
wrote for it. Its run lemma (`asmFirstP4Sel_runs`) asks that these tasks follow the slot model
(`P4SlotTasks`): each task is the slot of an active pair of the new state and carries the bundle
batch `info.U_B` of that pair, every pair with a nonempty batch has a task, and the new slots
`[lo, hi)` are exactly the slots of the newly active pairs. This file proves these facts from
what Phases 2 and 3 leave.

* `p4TasksOf mem descPtr n`: the `n` descriptors `[slot, batchPtr, W]` at `descPtr`, read as a
  list of tasks (`p4TasksOf_at`).
* `p4_newSlots`: Phase 2 gives the new pairs the slots after the old ones. With the slot maps
  before and after (`SlotMapOK`), the new slots `[|old slots|, n₁)` are exactly the slots of the
  newly active pairs.
* `p4_dynGraphEq`: the graph of the spanner of each active pair of the new state agrees with the
  graph of its bundle before the step.
* `p4SlotTasks_of_phases`: the slot model on the tasks. A touched slot holds a bundle, so it is
  the slot of an active pair. Its batch was written on the graph of the bundle, which agrees with
  the graph of the spanner of the pair. The batch names only live ends at each split vertex
  (`bundleCompStep_splitEndsExact`), so the spanner reads back exactly `info.U_B`. A slot
  that Phase 3 did not touch has the empty batch.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

@[expose] public section

/-- The `n` update descriptors `[slot, batchPtr, W]` stored at `descPtr`, read as a list of
tasks. -/
def p4TasksOf (mem : ℕ → ℕ) (descPtr n : ℕ) : List SpanUpdTask :=
  (List.range n).map fun i =>
    ⟨mem (descPtr + 3 * i), mem (descPtr + 3 * i + 1), mem (descPtr + 3 * i + 2)⟩

end

public section

theorem p4TasksOf_length (mem : ℕ → ℕ) (descPtr n : ℕ) : (p4TasksOf mem descPtr n).length = n := by
  simp [p4TasksOf]

/-- The descriptors at `descPtr` are the tasks they are read as. -/
theorem p4TasksOf_at (mem : ℕ → ℕ) (descPtr n : ℕ) :
    SpanUpdTasksAt mem descPtr (p4TasksOf mem descPtr n) := by
  intro i hi
  simp [p4TasksOf]

/-- A task of the list is the descriptor at one index. -/
theorem mem_p4TasksOf {mem : ℕ → ℕ} {descPtr n : ℕ} {t : SpanUpdTask}
    (ht : t ∈ p4TasksOf mem descPtr n) :
    ∃ i < n, t = ⟨mem (descPtr + 3 * i), mem (descPtr + 3 * i + 1), mem (descPtr + 3 * i + 2)⟩ := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
  exact ⟨i, List.mem_range.mp hi, rfl⟩

/-- **The new slots of Phase 2.** Before Phase 2 the active pairs of `tr` occupy the slots
`[0, |oldSlots|)`, and after it the active pairs of `trA` occupy `[0, n₁)`, with the old pairs
in their old slots. Then the slots of the newly active pairs are exactly `[|oldSlots|, n₁)`: a
new pair can not sit in an old slot, since that slot is the slot of an old pair and the slot map
after Phase 2 is one to one. -/
theorem p4_newSlots {L slotCap cap slotCap' cap' n₁ : ℕ} {tr trA : BundleTreeState L}
    {oldSlots newSlots : List ℕ} {slotOfOld slotOf : Finset ℕ × ℤ → ℕ}
    (hOld : SlotMapOK tr slotCap cap oldSlots slotOfOld)
    (hOldRange : oldSlots = List.range oldSlots.length)
    (hNew : SlotMapOK trA slotCap' cap' newSlots slotOf)
    (hNewRange : newSlots = List.range n₁)
    (hkeep : ∀ q ∈ activePairs tr, slotOf q = slotOfOld q)
    (hmono : ∀ q ∈ activePairs tr, q ∈ activePairs trA) :
    (∀ p ∈ activePairs trA, p ∉ activePairs tr → oldSlots.length ≤ slotOf p ∧ slotOf p < n₁) ∧
    (∀ s, oldSlots.length ≤ s → s < n₁ → ∃ p ∈ activePairs trA, s = slotOf p) := by
  refine ⟨fun p hp hpn => ⟨?_, ?_⟩, fun s _ hs => ?_⟩
  · by_contra hlt
    have hmem : slotOf p ∈ oldSlots := by
      rw [hOldRange]
      exact List.mem_range.mpr (by omega)
    obtain ⟨q, hq, hqs⟩ := hOld.2.2.1 _ hmem
    have hpq := hNew.2.2.2.1 q (hmono q hq) p hp ((hkeep q hq).trans hqs)
    exact hpn (hpq ▸ hq)
  · have hmem := hNew.2.1 p hp
    rw [hNewRange] at hmem
    exact List.mem_range.mp hmem
  · have hmem : s ∈ newSlots := by
      rw [hNewRange]
      exact List.mem_range.mpr hs
    obtain ⟨p, hp, hps⟩ := hNew.2.2.1 s hmem
    exact ⟨p, hp, hps.symm⟩

/-- **The graphs of the spanners before the step.** For each active pair of the new state, the
graph of its spanner agrees with the graph of its bundle (`GraphEq`). For an old pair this is
`AsmFirstActiveDynGraphInv`. A newly active pair was inactive before the step, so its
spanner is fresh on the initial bundle graph (`AsmFirstInactiveDynInv`), which is the bundle
graph with `0` at the names that are not edges (`AsmFirstInactiveCompInv`). -/
theorem p4_dynGraphEq
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    {y : AsmBrSide B5 depth}
    (hInact : AsmFirstInactiveCompInv impl w depth tr ord y)
    (hInactDyn : AsmFirstInactiveDynInv impl w depth tr y)
    (hDynG : AsmFirstActiveDynGraphInv tr) :
    ∀ q ∈ activePairs (stepBundleTree sparsify tr U ord ord').state,
      GraphEq (tr.dyn q).G (tr.bun q).graph := by
  rintro ⟨C, b⟩ hq
  obtain ⟨hC', hb⟩ := mem_activePairs.mp hq
  rcases Finset.mem_union.mp hC' with hOld | hNew
  · exact hDynG C hOld b hb
  · obtain ⟨hT, hNotA⟩ := Finset.mem_sdiff.mp hNew
    have hC0 : C ∈ components tr.cs.G₀ := (Finset.mem_filter.mp hT).1
    obtain ⟨-, hInitG, -⟩ := (hInact C hC0 hNotA).2.2.2.2 b hb
    rw [hInactDyn C hC0 hNotA b hb, dsHist_init_G_eq, hInitG]
    exact normGraph_graphEq _

/-- The bundle batch of an active pair is the batch of the bundle in its slot: the two bundles
agree, so the step gives the same batch. -/
private theorem p4_batch_eq {cs : CompLSFState} {B₀ B : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (hag : BunAgree B₀ B)
    (hr : BundleStepReady cs B₀ k ord ord' U) :
    (bundleCompStep cs B₀ k ord ord' U).1 = (bundleCompStep cs B k ord ord' U).1 :=
  (bunAgree_bundleCompStep_eq hag hr).1

set_option maxHeartbeats 800000 in
/-- **The slot model on the tasks of Phase 4** (`P4SlotTasks`). The tasks are the descriptors
that Phase 3 wrote at `descPtr`, one per touched slot. The hypotheses are:
* the slot maps of the bundle table `S₀` before Phase 3 and of the spanner table `S6` after
  Phase 2 (`hslot`, `hinj`, `hMatch`, `hBunNone`), each holding the active pairs of the new
  state `info.state`;
* the input of each bundle in `S₀` is ordered (`hReady`), and the graph of the spanner of each
  active pair agrees with the graph of its bundle (`hDynG`);
* what Phase 3 leaves: the touched slots, once each, holding bundles, with at descriptor `i`
  the touched slot and the batch of its bundle step on the graph of the bundle, and the empty
  batch at every untouched slot;
* the new slots `[lo, hi)` (from `p4_newSlots`). -/
theorem p4SlotTasks_of_phases {P : DSParams} {cap slotCap : ℕ} {tr : BundleTreeState P.L}
    {U : List Update} {ord ord' : ℕ → List End} {slotOf : Finset ℕ × ℤ → ℕ}
    {S6 : BucketSpannerState cap} {S₀ : Fin slotCap → Option BundleState} {mem₀ : ℕ → ℕ}
    {descPtr lo hi : ℕ} {touched : List ℕ}
    (hslot : ∀ q ∈ activePairs
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
      ∃ (hs : slotOf q < cap) (d : DSHist), S6 ⟨slotOf q, hs⟩ = some d ∧ d.state P = tr.dyn q)
    (hinj : ∀ q₁ ∈ activePairs
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
      ∀ q₂ ∈ activePairs (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
        slotOf q₁ = slotOf q₂ → q₁ = q₂)
    (hMatch : ∀ q ∈ activePairs
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
      ∃ (hs : slotOf q < slotCap) (B : BundleState), S₀ ⟨slotOf q, hs⟩ = some B ∧
        BunAgree B (tr.bun q))
    (hBunNone : ∀ j : Fin slotCap, S₀ j ≠ none → ∃ q ∈ activePairs
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state, slotOf q = j.1)
    (hReady : ∀ j B₀, S₀ j = some B₀ → BundleStepReady tr.cs B₀ tr.k ord ord' U)
    (hDynG : ∀ q ∈ activePairs
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
      GraphEq (tr.dyn q).G (tr.bun q).graph)
    (hnd : touched.Nodup)
    (hdesc : ∀ i (hi : i < touched.length), ∃ (hs : touched[i] < slotCap),
      mem₀ (descPtr + 3 * i) = touched[i] ∧
      ∀ B₀, S₀ ⟨touched[i], hs⟩ = some B₀ →
        BatchAt mem₀ (mem₀ (descPtr + 3 * i + 1)) B₀.graph
          (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 (mem₀ (descPtr + 3 * i + 2)))
    (hnone : ∀ j : Fin slotCap, S₀ j = none → j.1 ∉ touched)
    (huntouched : ∀ j B₀, S₀ j = some B₀ → j.1 ∉ touched →
      (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 = [])
    (hnew : ∀ p ∈ activePairs
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
      p ∉ activePairs tr → lo ≤ slotOf p ∧ slotOf p < hi)
    (hnewSlot : ∀ s, lo ≤ s → s < hi → ∃ p ∈ activePairs
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state, s = slotOf p) :
    P4SlotTasks P tr (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord') slotOf S6
      mem₀ (p4TasksOf mem₀ descPtr touched.length) lo hi := by
  classical
  set info := stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord' with hinfo
  have hUB : ∀ q, info.U_B q = (bundleCompStep tr.cs (tr.bun q) tr.k ord ord' U).1 :=
    fun _ => rfl
  have hmapSlot : (p4TasksOf mem₀ descPtr touched.length).map SpanUpdTask.slot = touched := by
    apply List.ext_getElem (by simp [p4TasksOf])
    intro i h1 h2
    obtain ⟨-, hm, -⟩ := hdesc i h2
    simpa [p4TasksOf] using hm
  refine ⟨hslot, hinj, fun t ht => ?_, fun q hq hne => ?_, by rw [hmapSlot]; exact hnd, hnew, hnewSlot⟩
  · -- A task is the slot of an active pair, with the batch of that pair.
    obtain ⟨i, hi, rfl⟩ := mem_p4TasksOf ht
    obtain ⟨hs, hm, hbat⟩ := hdesc i hi
    cases hS₀ : S₀ ⟨touched[i], hs⟩ with
    | none => exact absurd (List.getElem_mem hi) (hnone _ hS₀)
    | some B₀ =>
      obtain ⟨q, hq, hqs⟩ := hBunNone ⟨touched[i], hs⟩ (by rw [hS₀]; exact Option.some_ne_none _)
      refine ⟨q, hq, by rw [hm]; exact hqs.symm, fun hs' d hd => ?_⟩
      obtain ⟨hsq, d', hd', hst⟩ := hslot q hq
      have hdd : d = d' := by
        have hfin : (⟨mem₀ (descPtr + 3 * i), hs'⟩ : Fin cap) = ⟨slotOf q, hsq⟩ :=
          Fin.ext (hm.trans hqs.symm)
        rw [hfin, hd'] at hd
        exact (Option.some.inj hd).symm
      subst hdd
      obtain ⟨hs2, B, hB, hag⟩ := hMatch q hq
      have hBB : B = B₀ := by
        have hfin : (⟨slotOf q, hs2⟩ : Fin slotCap) = ⟨touched[i], hs⟩ := Fin.ext hqs
        rw [hfin, hS₀] at hB
        exact (Option.some.inj hB).symm
      subst hBB
      have hbeq := p4_batch_eq hag (hReady _ B hS₀)
      have hG : GraphEq B.graph (d.state P).G := by
        rw [hst]
        exact graphEq_trans (bunAgree_graphEq hag) (graphEq_symm (hDynG q hq))
      have hBat : BatchAt mem₀ (mem₀ (descPtr + 3 * i + 1)) (d.state P).G (info.U_B q)
          (mem₀ (descPtr + 3 * i + 2)) := by
        rw [hUB, ← hbeq]
        exact batchAt_of_graphEq hG (hbat B hS₀)
      have hEnds : BatchSplitEndsExact (d.state P).G (info.U_B q) := by
        rw [hUB, ← hbeq]
        exact batchSplitEndsExact_congr hG (bundleCompStep_splitEndsExact _ _ _ _ _ _)
      refine ⟨decodeBatch_eq_of_batchAt hBat hEnds, ?_⟩
      rw [hBat.2.1, List.length_eq_zero_iff]
  · -- A pair with a nonempty batch has a task.
    obtain ⟨hs, B, hB, hag⟩ := hMatch q hq
    have htq : slotOf q ∈ touched := by
      by_contra hnt
      have h0 := huntouched ⟨slotOf q, hs⟩ B hB hnt
      rw [p4_batch_eq hag (hReady _ B hB)] at h0
      exact hne ((hUB q).trans h0)
    obtain ⟨i, hi, hiq⟩ := List.mem_iff_getElem.mp htq
    refine ⟨⟨mem₀ (descPtr + 3 * i), mem₀ (descPtr + 3 * i + 1), mem₀ (descPtr + 3 * i + 2)⟩,
      List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, ?_⟩
    obtain ⟨-, hm, -⟩ := hdesc i hi
    exact hm.trans hiq

end

end MinCostFlow.SparseCore.Program
