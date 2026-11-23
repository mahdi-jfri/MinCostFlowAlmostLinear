module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Cover

import Mathlib.Tactic

/-!
# From the workspace facts to the selectors of Phase 4 (`AssemblyFirstStepP4SelHyps`)

`asmFirstMarkOutSel_runs` computes the selectors of the leaving and entering edges from the lists
`delSup` and `insSup` and from the flags of the workspace. It asks that the lists contain these
edges and that the test it runs on each listed edge decides membership. This file gets both from
`p4SpanWV_cover` and the seeds of the front of Phase 4.

* `P4SlotTasks`: the slot model on the tasks alone, before the outputs are known; with the
  outputs and the new slots that the front of Phase 4 returns, it gives `P4SlotModel`
  (`P4SlotTasks.model`).
* `p4Sel_hyps`: the four hypotheses `hDS_cov`, `hIS_cov`, `hDel_iff`, `hIns_iff` of
  `asmFirstMarkOutSel_runs`, for the lists `Ld = delSup ∪ batchDeletes U` and
  `Li = insSup ∪ seeds`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart
open MinCostFlow.SparseCore.Program.Read

/-! ## The slot model on the tasks -/

@[expose] public section

/-- **The slot model on the tasks** `tasks` and the new slots `[lo, hi)`. The fields are those
of `P4SlotModel` that do not mention the outputs of the tasks or the edge lists of the new
slots: the newly active pairs are those whose slot lies in `[lo, hi)`, and each slot there is the
slot of an active pair. -/
structure P4SlotTasks (P : DSParams) {cap : ℕ} (tr : BundleTreeState P.L)
    (info : BundleTreeStepInfo P.L) (slotOf : Finset ℕ × ℤ → ℕ) (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (tasks : List SpanUpdTask) (lo hi : ℕ) : Prop where
  hslot : ∀ p ∈ activePairs info.state, ∃ (hs : slotOf p < cap) (d : DSHist),
    S6 ⟨slotOf p, hs⟩ = some d ∧ d.state P = tr.dyn p
  hinj : ∀ p₁ ∈ activePairs info.state, ∀ p₂ ∈ activePairs info.state,
    slotOf p₁ = slotOf p₂ → p₁ = p₂
  htask : ∀ t ∈ tasks, ∃ p ∈ activePairs info.state, t.slot = slotOf p ∧
    ∀ (hs : t.slot < cap) (d : DSHist), S6 ⟨t.slot, hs⟩ = some d →
      (decodeBatch mem₀ t.batchPtr (d.state P).G).1 = info.U_B p ∧
      (mem₀ t.batchPtr = 0 ↔ info.U_B p = [])
  hcover : ∀ p ∈ activePairs info.state, info.U_B p ≠ [] → ∃ t ∈ tasks, t.slot = slotOf p
  hnd : (tasks.map SpanUpdTask.slot).Nodup
  hnew : ∀ p ∈ activePairs info.state, p ∉ activePairs tr → lo ≤ slotOf p ∧ slotOf p < hi
  hnewSlot : ∀ s, lo ≤ s → s < hi → ∃ p ∈ activePairs info.state, s = slotOf p

end

public section

/-- With the outputs `qs` of the tasks and the edge lists `ns` of the new slots, as the front of
Phase 4 returns them (`P4FrontPost`), the slot model on the tasks is the full slot model. -/
theorem P4SlotTasks.model {P : DSParams} {cap : ℕ} {tr : BundleTreeState P.L}
    {info : BundleTreeStepInfo P.L} {slotOf : Finset ℕ × ℤ → ℕ} {S6 : BucketSpannerState cap}
    {mem₀ : ℕ → ℕ} {tasks : List SpanUpdTask} {lo hi : ℕ}
    (hT : P4SlotTasks P tr info slotOf S6 mem₀ tasks lo hi)
    {qs : List (SpanUpdTask × P4TaskOut)} {ns : List (ℕ × List ℕ)}
    (hqs : qs.map Prod.fst = tasks) (hok : ∀ q ∈ qs, P4OutOK P S6 mem₀ q)
    (hns : ns.map Prod.fst = List.range' lo (hi - lo))
    (hnsOK : ∀ q ∈ ns, ∀ (hs : q.1 < cap) (d : DSHist),
      p4SpanAfter P S6 mem₀ tasks ⟨q.1, hs⟩ = some d → q.2.Nodup ∧ q.2.toFinset = (d.state P).G.E) :
    P4SlotModel P tr info slotOf S6 mem₀ qs ns := by
  subst hqs
  have hrange : ∀ s, s ∈ ns.map Prod.fst ↔ lo ≤ s ∧ s < hi := fun s => by
    rw [hns, List.mem_range'_1]; omega
  refine ⟨hT.hslot, hT.hinj, fun q hq => hT.htask q.1 (List.mem_map_of_mem hq),
    fun p hp hne => ?_, hT.hnd, fun p hp hp0 => ?_, fun q hq => ?_,
    fun q hq hs d hd => (hnsOK q hq hs d hd).2, hok⟩
  · obtain ⟨t, ht, hts⟩ := hT.hcover p hp hne
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    exact ⟨q, hq, hts⟩
  · obtain ⟨q, hq, hq1⟩ := List.mem_map.mp ((hrange _).mpr (hT.hnew p hp hp0))
    exact ⟨q, hq, hq1⟩
  · have h := (hrange q.1).mp (List.mem_map_of_mem hq)
    exact hT.hnewSlot q.1 h.1 h.2

/-! ## The hypotheses of the selectors -/

/-- **The hypotheses of `asmFirstMarkOutSel_runs` from `p4SpanWV_cover`.** Here `W` is the workspace after the
spanner part, `Ld` and `Li` are its lists `delSup` and `insSup` with the seeds added, `F` is the
set of removed forest edges, and `N` holds the edges of the bundles of the newly active pairs.
The five facts `hF1` to `hF5` are the conclusions of `p4SpanWV_cover`. -/
theorem p4Sel_hyps {L : ℕ} {tr : BundleTreeState L} {U : List Update} {ord ord' : ℕ → List End}
    {sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut} {W : Phase4WS} {Ld Li : List ℕ}
    {F N : Finset ℕ} {fDel : List ℕ} {nNew : ℕ} {lazyE : Fin nNew → List ℕ}
    (hF1 : ∀ e, tgtEDec tr.S_cur.E F W.inAct W.inTgt (batchLastOp U) e ↔
      e ∈ (stepBundleTree sp tr U ord ord').state.S_cur.E)
    (hF2 : ∀ e ∈ tr.S_cur.E, e ∈ W.inDtot ↔ e ∈ (stepBundleTree sp tr U ord ord').D_total)
    (hF3 : ∀ e ∈ outDelSet sp tr U ord ord', e ∈ batchDeletes U ∨ e ∈ W.delSup)
    (hF4 : ∀ e ∈ outInsSet sp tr U ord ord', e ∈ batchDeletes U ∨ e ∈ batchInsEdges U ∨
      e ∈ F ∨ e ∈ N ∨ e ∈ W.insSup)
    (hLd : ∀ e, e ∈ Ld ↔ e ∈ W.delSup ∨ e ∈ batchDeletes U)
    (hLi : ∀ e, e ∈ Li ↔ e ∈ W.insSup ∨ e ∈ batchDeletes U ∨ e ∈ batchInsEdges U ∨
      (∃ i : Fin nNew, e ∈ lazyE i) ∨ e ∈ fDel)
    (hfDel : ∀ e ∈ F, e ∈ fDel) (hN : ∀ e ∈ N, ∃ i : Fin nNew, e ∈ lazyE i) :
    (∀ e ∈ outDelSet sp tr U ord ord', e ∈ Ld) ∧
    (∀ e ∈ outInsSet sp tr U ord ord', e ∈ Li) ∧
    (∀ e ∈ Ld, e ∈ outDelSet sp tr U ord ord' ↔ e ∈ tr.S_cur.E ∧
      (¬ tgtEDec tr.S_cur.E F W.inAct W.inTgt (batchLastOp U) e ∨ e ∈ batchDeletes U ∨
        e ∈ W.inDtot)) ∧
    (∀ e ∈ Li, e ∈ outInsSet sp tr U ord ord' ↔
      tgtEDec tr.S_cur.E F W.inAct W.inTgt (batchLastOp U) e ∧
        (e ∉ tr.S_cur.E ∨ e ∈ batchDeletes U ∨ e ∈ W.inDtot)) := by
  refine ⟨fun e he => ?_, fun e he => ?_, fun e _ => ?_, fun e _ => ?_⟩
  · rcases hF3 e he with h | h
    · exact (hLd e).mpr (Or.inr h)
    · exact (hLd e).mpr (Or.inl h)
  · rcases hF4 e he with h | h | h | h | h
    · exact (hLi e).mpr (Or.inr (Or.inl h))
    · exact (hLi e).mpr (Or.inr (Or.inr (Or.inl h)))
    · exact (hLi e).mpr (Or.inr (Or.inr (Or.inr (Or.inr (hfDel e h)))))
    · exact (hLi e).mpr (Or.inr (Or.inr (Or.inr (Or.inl (hN e h)))))
    · exact (hLi e).mpr (Or.inl h)
  · rw [mem_outDelSet_iff, hF1 e]
    constructor
    · rintro ⟨hS, h⟩
      exact ⟨hS, by rwa [hF2 e hS]⟩
    · rintro ⟨hS, h⟩
      exact ⟨hS, by rwa [← hF2 e hS]⟩
  · rw [mem_outInsSet_iff, hF1 e]
    by_cases hS : e ∈ tr.S_cur.E
    · rw [hF2 e hS]
    · simp only [hS, not_false_eq_true, true_or, and_true]

end

end MinCostFlow.SparseCore.Program
