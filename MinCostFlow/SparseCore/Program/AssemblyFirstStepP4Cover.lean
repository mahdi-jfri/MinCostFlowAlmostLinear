module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Folds
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepOutSel
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Front

import MinCostFlow.SparseCore.SplitSpannerBase
import Mathlib.Tactic

/-!
# The workspace of Phase 4 holds the sets of the model (`AssemblyFirstStepP4Cover`)

After the spanner part of Phase 4 (`p4SpanWV`), the workspace must let the later builders compute
the output batch of the branch step. This file proves that it does, against the model
`stepBundleTree`:

1. the marks decide the new output graph: `tgtEDec` on the flags `inAct` and `inTgt`, with the
   old output graph, the removed forest edges and `batchLastOp`, holds exactly for the edges of
   the new output graph (`asmFirstMarkOutSel_runs` asks this);
2. on the old output graph, `inDtot` holds exactly the edges of `D_total`;
3. `delSup`, with the deleted edges of the batch, holds the leaving edges `outDelSet`;
4. `insSup`, with the seeds of `asmFirstP4Seed_runs`, holds the entering edges `outInsSet`;
5. `reemb` holds exactly the sets `updateReembSet` of the spanner updates.

The proof follows each edge of these sets to the slot of its pair. The slot model
`P4SlotModel` says how the slots of Phase 4 stand for the pairs of the model. The marks are right
because the graphs of distinct active pairs are disjoint and each spanner lies in its graph. An
edge of the graph of an old pair that Phase 4 did not mark was not changed by the spanner, so the
rule of `tgtEDec` for unmarked edges (the old output graph, since no batch touches the edge)
gives the right answer. The edges of a newly active pair are all marked, by the scan of the new
slots. An edge of the bundle of a newly active pair is not in the old output graph
(`p4NewBun_not_mem_scur`), so the walks that Phase 4 does not scan, those of newly active pairs,
do not matter on the old output graph.

The walks of the spanners of newly active pairs lie in their spanners (`hWalkNew`); this is the
embedding clause of Theorem 8.2 for these spanners.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart
open MinCostFlow.SparseCore.Program.Read

/-! ## The slot model -/

@[expose] public section

/-- **The slots of Phase 4 and the model of the step** `info` of the branch `tr`. `slotOf` gives
the slot of each pair; `S6` is the table of the spanners before Phase 4, and the tasks read their
batches in `mem₀`; `qs` are the tasks with their outputs, `ns` the new slots with their edge
lists.
1. each active pair of the new state has its slot, which holds a history whose state is the
   spanner of the pair before the step;
2. distinct active pairs have distinct slots;
3. each task is on the slot of an active pair, and its batch reads as the bundle batch of that
   pair, with first word `0` exactly when that batch is empty;
4. each active pair with a nonempty bundle batch has a task;
5. the slots of the tasks are distinct;
6. each newly active pair has a new slot, each new slot is the slot of an active pair, and its
   list holds the edges of its graph in the spanners after the tasks;
7. the outputs of the tasks are those of the updates (`P4OutOK`). -/
structure P4SlotModel (P : DSParams) {cap : ℕ} (tr : BundleTreeState P.L)
    (info : BundleTreeStepInfo P.L) (slotOf : Finset ℕ × ℤ → ℕ) (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ)) : Prop where
  hslot : ∀ p ∈ activePairs info.state, ∃ (hs : slotOf p < cap) (d : DSHist),
    S6 ⟨slotOf p, hs⟩ = some d ∧ d.state P = tr.dyn p
  hinj : ∀ p₁ ∈ activePairs info.state, ∀ p₂ ∈ activePairs info.state,
    slotOf p₁ = slotOf p₂ → p₁ = p₂
  htask : ∀ q ∈ qs, ∃ p ∈ activePairs info.state, q.1.slot = slotOf p ∧
    ∀ (hs : q.1.slot < cap) (d : DSHist), S6 ⟨q.1.slot, hs⟩ = some d →
      (decodeBatch mem₀ q.1.batchPtr (d.state P).G).1 = info.U_B p ∧
      (mem₀ q.1.batchPtr = 0 ↔ info.U_B p = [])
  hcover : ∀ p ∈ activePairs info.state, info.U_B p ≠ [] → ∃ q ∈ qs, q.1.slot = slotOf p
  hnd : ((qs.map Prod.fst).map SpanUpdTask.slot).Nodup
  hnew : ∀ p ∈ activePairs info.state, p ∉ activePairs tr → ∃ q ∈ ns, q.1 = slotOf p
  hnewSlot : ∀ q ∈ ns, ∃ p ∈ activePairs info.state, q.1 = slotOf p
  hnewList : ∀ q ∈ ns, ∀ (hs : q.1 < cap) (d : DSHist),
    p4SpanAfter P S6 mem₀ (qs.map Prod.fst) ⟨q.1, hs⟩ = some d → q.2.toFinset = (d.state P).G.E
  hok : ∀ q ∈ qs, P4OutOK P S6 mem₀ q

end

/-! ## Facts of the model -/

public section

/-- Two orders of the same batch insert the same edges. -/
theorem uhInsFinset_perm {l₁ l₂ : List Update} (h : l₁.Perm l₂) :
    uhInsFinset l₁ = uhInsFinset l₂ := by
  unfold uhInsFinset
  exact List.toFinset_eq_of_perm _ _ (h.filterMap _)

/-- The edges of `D_total`: the outputs `D` of the spanners of the active pairs, and the walks of
the edges that leave a spanner but stay in its graph. -/
theorem mem_D_total_iff {L : ℕ} (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) (x : ℕ) :
    x ∈ (stepBundleTree sp tr U ord ord').D_total ↔
      ∃ p ∈ activePairs (stepBundleTree sp tr U ord ord').state,
        x ∈ ((stepBundleTree sp tr U ord ord').stepOut p).D ∨
        ∃ g ∈ ((tr.dyn p).H.E ∩ ((stepBundleTree sp tr U ord ord').stepOut p).state.G.E) \
            ((stepBundleTree sp tr U ord ord').stepOut p).state.H.E,
          x ∈ walkEdges (piTotal ((stepBundleTree sp tr U ord ord').stepOut p).state g) := by
  change x ∈ (((stepBundleTree sp tr U ord ord').state.activeComps.biUnion fun C =>
      (tr.activeBuckets C).biUnion fun b => ((stepBundleTree sp tr U ord ord').stepOut (C, b)).D) ∪
    ((stepBundleTree sp tr U ord ord').state.activeComps.biUnion fun C =>
      (tr.activeBuckets C).biUnion fun b =>
        (((tr.dyn (C, b)).H.E ∩ ((stepBundleTree sp tr U ord ord').stepOut (C, b)).state.G.E) \
          ((stepBundleTree sp tr U ord ord').stepOut (C, b)).state.H.E).biUnion
          fun e => walkEdges (piTotal ((stepBundleTree sp tr U ord ord').stepOut (C, b)).state e))) ↔ _
  simp only [Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro (⟨C, hC, b, hb, hx⟩ | ⟨C, hC, b, hb, g, hg, hx⟩)
    · exact ⟨(C, b), mem_activePairs.mpr ⟨hC, hb⟩, Or.inl hx⟩
    · exact ⟨(C, b), mem_activePairs.mpr ⟨hC, hb⟩, Or.inr ⟨g, hg, hx⟩⟩
  · rintro ⟨⟨C, b⟩, hp, hx | ⟨g, hg, hx⟩⟩
    · exact Or.inl ⟨C, (mem_activePairs.mp hp).1, b, (mem_activePairs.mp hp).2, hx⟩
    · exact Or.inr ⟨C, (mem_activePairs.mp hp).1, b, (mem_activePairs.mp hp).2, g, hg, hx⟩

/-- **An edge of the bundle of a newly active pair is not in the old output graph**, unless the
batch deletes it. The bundle lies in the graph of its component, which was not active, and the
old output graph holds only edges of active components and cross edges. -/
theorem p4NewBun_not_mem_scur {depth : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {P : DSParams}
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    {info : BundleTreeStepInfo depth}
    (hinfo : info = stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord')
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hU : tr.cs.G.BatchIsValid U)
    (hMod : RestartScurModelInv tr) (hMod' : RestartScurModelInv info.state)
    (hBD' : BunDisjointInv info.state) {p : Finset ℕ × ℤ} (hp : p ∈ activePairs info.state)
    (hp0 : p ∉ activePairs tr) {e : ℕ} (heB : e ∈ (info.state.bun p).edges)
    (heS : e ∈ tr.S_cur.E) (hdel : e ∉ batchDeletes U) : False := by
  have hcs : info.state.cs = compLSFBatch tr.cs U := by subst hinfo; rfl
  have hbkt : info.state.activeBuckets = tr.activeBuckets := by subst hinfo; rfl
  have heG0 : e ∈ tr.cs.G.E := (Finset.mem_sdiff.mp (hMod.2.2.2.1.2.1 heS)).1
  have hl0 : batchLastOp U e = 0 := lastOp_zero_of_mem_not_del hU heG0 hdel
  have hI' := compLSFBatch_inv hI hU
  have hG0' : (compLSFBatch tr.cs U).G₀ = tr.cs.G₀ := compLSFBatch_G₀ tr.cs U
  have hC0' : p.1 ∈ components (compLSFBatch tr.cs U).G₀ := by
    rw [← hcs]; exact hMod'.1 (mem_activePairs.mp hp).1
  have hnotAct : p.1 ∉ tr.activeComps := fun ha =>
    hp0 (mem_activePairs.mpr ⟨ha, by rw [← hbkt]; exact (mem_activePairs.mp hp).2⟩)
  have heCp : e ∈ ((compLSFBatch tr.cs U).compSt p.1).G.E := by
    rw [← hcs]
    exact (hMod'.2.2.2.2 p.1 (mem_activePairs.mp hp).1 p.2 (mem_activePairs.mp hp).2).2.1 heB
  have hnc' : e ∉ (compLSFBatch tr.cs U).crossEdges := fun hc =>
    Finset.disjoint_left.mp (hBD'.2 p hp) heB (by rw [hcs]; exact hc)
  rw [hMod.2.2.1] at heS
  simp only [Finset.mem_union, Finset.mem_biUnion, BundleTreeState.extraEdges,
    Finset.mem_sdiff] at heS
  rcases heS with (⟨C', hC', b', hb', heH'⟩ | ⟨C', hC', ⟨heC0, _⟩, _⟩) | hcr0
  · exact comp_edge_disj_inv hI' (hG0'.symm ▸ hMod.1 hC') hC0' (fun h => hnotAct (h ▸ hC'))
      (comp_edge_stay_of_lastOp_zero hI hU (hMod.1 hC')
        ((hMod.2.2.2.2 C' hC' b' hb').2.1 ((hMod.2.2.2.2 C' hC' b' hb').2.2.2 heH')) hl0) heCp
  · exact comp_edge_disj_inv hI' (hG0'.symm ▸ hMod.1 hC') hC0' (fun h => hnotAct (h ▸ hC'))
      (comp_edge_stay_of_lastOp_zero hI hU (hMod.1 hC') heC0 hl0) heCp
  · exact hnc' (cross_edge_stay_of_lastOp_zero hI hU hcr0 hl0)

/-- The graph and the spanner of an active pair fit the marks: the sets `A` (the bundles) and `T`
(the spanners) of all active pairs. The bundles are disjoint, and each spanner lies in its
bundle. -/
theorem p4_pair_fits {depth : ℕ} {tr' : BundleTreeState depth} (hMod' : RestartScurModelInv tr')
    (hBD' : BunDisjointInv tr')
    (hDynG' : ∀ p ∈ activePairs tr', (tr'.dyn p).G.E = (tr'.bun p).edges)
    {p : Finset ℕ × ℤ} (hp : p ∈ activePairs tr') :
    P4SlotFits ((activePairs tr').biUnion fun p => (tr'.bun p).edges)
      ((activePairs tr').biUnion fun p => (tr'.dyn p).H.E) (tr'.dyn p).G.E (tr'.dyn p).H.E := by
  rw [hDynG' p hp]
  refine ⟨fun e he => Finset.mem_biUnion.mpr ⟨p, hp, he⟩,
    fun e he => ⟨fun h => Finset.mem_biUnion.mpr ⟨p, hp, h⟩, fun h => ?_⟩⟩
  obtain ⟨q, hq, heq⟩ := Finset.mem_biUnion.mp h
  have hqB : e ∈ (tr'.bun q).edges :=
    (hMod'.2.2.2.2 q.1 (mem_activePairs.mp hq).1 q.2 (mem_activePairs.mp hq).2).2.2.2 heq
  by_cases hpq : q = p
  · subst hpq; exact heq
  · exact absurd hqB (Finset.disjoint_left.mp (hBD'.1 p hp q hq (Ne.symm hpq)) he)

variable {P : DSParams} {cap : ℕ} {tr : BundleTreeState P.L} {U : List Update}
  {ord ord' : ℕ → List End} {info : BundleTreeStepInfo P.L} {slotOf : Finset ℕ × ℤ → ℕ}
  {S6 : BucketSpannerState cap} {mem₀ : ℕ → ℕ} {qs : List (SpanUpdTask × P4TaskOut)}
  {ns : List (ℕ × List ℕ)}

/-- An updated slot stands for an active pair with a nonempty bundle batch: the new state of the
slot is the spanner of the pair after the step, and the outputs of the task are those of the
update of the pair. -/
theorem P4SlotModel.eff_pair
    (hinfo : info = stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord')
    (hM : P4SlotModel P tr info slotOf S6 mem₀ qs ns) {q : SpanUpdTask × P4TaskOut}
    (hq : q ∈ qs) {d : DSHist} (hd : P4Eff S6 mem₀ q d) :
    ∃ p ∈ activePairs info.state, q.1.slot = slotOf p ∧ info.U_B p ≠ [] ∧
      p4St P mem₀ q d = info.state.dyn p ∧ q.2.UH.Perm (info.stepOut p).UH ∧
      q.2.dL.toFinset = (info.stepOut p).D ∧
      q.2.rL.toFinset = updateReembSet (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl) := by
  obtain ⟨hs, hS6, hb⟩ := hd
  obtain ⟨p, hp, hsl, hbat⟩ := hM.htask q hq
  obtain ⟨hdec, hzero⟩ := hbat hs d hS6
  obtain ⟨hs', d', hd', hst⟩ := hM.hslot p hp
  have hdd : d' = d := by
    rw [show (⟨slotOf p, hs'⟩ : Fin cap) = ⟨q.1.slot, hs⟩ from Fin.ext hsl.symm] at hd'
    exact Option.some.inj (hd'.symm.trans hS6)
  subst hdd
  have hne : info.U_B p ≠ [] := fun h => hb (hzero.mpr h)
  have hstep : info.stepOut p =
      DynSpanner.update (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl) := by
    subst hinfo; rfl
  have hdyn : info.state.dyn p = (info.stepOut p).state := by subst hinfo; rfl
  have hF := hM.hok q hq hs d' hS6 hb
  rw [hdec] at hF
  obtain ⟨hUH, -, -, hD, -, hR, -⟩ := hF
  rw [hst, ← hstep] at hUH hD
  rw [hst] at hR
  refine ⟨p, hp, hsl, hne, ?_, hUH, hD, hR⟩
  show (⟨d'.G₀, d'.Us ++ [(decodeBatch mem₀ q.1.batchPtr (d'.state P).G).1]⟩ : DSHist).state P = _
  rw [dsHist_append_state_eq_update, hdec, hst, hdyn, hstep]

/-- An active pair with a nonempty bundle batch has an updated slot. -/
theorem P4SlotModel.pair_eff (hM : P4SlotModel P tr info slotOf S6 mem₀ qs ns)
    {p : Finset ℕ × ℤ} (hp : p ∈ activePairs info.state) (hne : info.U_B p ≠ []) :
    ∃ q ∈ qs, ∃ d, P4Eff S6 mem₀ q d ∧ q.1.slot = slotOf p := by
  obtain ⟨q, hq, hsl⟩ := hM.hcover p hp hne
  obtain ⟨hs, d, hd, -⟩ := hM.hslot p hp
  obtain ⟨p', hp', hsl', hbat⟩ := hM.htask q hq
  have hpp : p' = p := hM.hinj p' hp' p hp (hsl'.symm.trans hsl)
  subst hpp
  have hs' : q.1.slot < cap := hsl ▸ hs
  have hd' : S6 ⟨q.1.slot, hs'⟩ = some d := by
    rw [show (⟨q.1.slot, hs'⟩ : Fin cap) = ⟨slotOf p', hs⟩ from Fin.ext hsl]; exact hd
  exact ⟨q, hq, d, ⟨hs', hd', fun h => hne ((hbat hs' d hd').2.mp h)⟩, hsl⟩

/-- **After the tasks**, the slot of each active pair holds a history whose state is the spanner
of the pair after the step. -/
theorem P4SlotModel.after
    (hinfo : info = stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord')
    (hM : P4SlotModel P tr info slotOf S6 mem₀ qs ns) {p : Finset ℕ × ℤ}
    (hp : p ∈ activePairs info.state) :
    ∃ (hs : slotOf p < cap) (d : DSHist),
      p4SpanAfter P S6 mem₀ (qs.map Prod.fst) ⟨slotOf p, hs⟩ = some d ∧
        d.state P = info.state.dyn p := by
  obtain ⟨hs, d₀, hd₀, hst⟩ := hM.hslot p hp
  have hstep : info.stepOut p =
      DynSpanner.update (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl) := by
    subst hinfo; rfl
  have hdyn : info.state.dyn p = (info.stepOut p).state := by subst hinfo; rfl
  have hkeep : info.U_B p = [] → d₀.state P = info.state.dyn p := fun h => by
    rw [hdyn, hstep, h, update_nil, hst]
  refine ⟨hs, ?_⟩
  by_cases hT : ∃ q ∈ qs, q.1.slot = slotOf p
  · obtain ⟨q, hq, hsl⟩ := hT
    have hs' : q.1.slot < cap := hsl ▸ hs
    have hfin : (⟨slotOf p, hs⟩ : Fin cap) = ⟨q.1.slot, hs'⟩ := Fin.ext hsl.symm
    have hd₀' : S6 ⟨q.1.slot, hs'⟩ = some d₀ := by rw [← hfin]; exact hd₀
    have hat := p4SpanAfter_at_task P S6 mem₀ hs' hM.hnd (List.mem_map_of_mem hq) S6
    obtain ⟨p', hp', hsl', hbat⟩ := hM.htask q hq
    have hpp : p' = p := hM.hinj p' hp' p hp (hsl'.symm.trans hsl)
    subst hpp
    rw [hfin, show p4SpanAfter P S6 mem₀ (qs.map Prod.fst) =
      (qs.map Prod.fst).foldl (p4SpanStep P S6 mem₀) S6 from rfl, hat]
    by_cases hb : mem₀ q.1.batchPtr = 0
    · rw [p4OnTask_empty hs' hd₀' hb, hd₀']
      exact ⟨d₀, rfl, hkeep ((hbat hs' d₀ hd₀').2.mp hb)⟩
    · rw [p4OnTask_of hs' hd₀' hb]
      obtain ⟨p'', hp'', hsl'', -, hst'', -⟩ := hM.eff_pair hinfo hq ⟨hs', hd₀', hb⟩
      have hpp : p'' = p' := hM.hinj p'' hp'' p' hp (hsl''.symm.trans hsl)
      subst hpp
      exact ⟨_, rfl, hst''⟩
  · have hnot : slotOf p ∉ (qs.map Prod.fst).map SpanUpdTask.slot := fun h => by
      obtain ⟨t, ht, hts⟩ := List.mem_map.mp h
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
      exact hT ⟨q, hq, hts⟩
    have hun := p4SpanAfter_unchanged P S6 mem₀ (j := ⟨slotOf p, hs⟩) hnot S6
    refine ⟨d₀, (show p4SpanAfter P S6 mem₀ (qs.map Prod.fst) ⟨slotOf p, hs⟩ = _ from hun).trans hd₀,
      hkeep ?_⟩
    by_contra hne
    obtain ⟨q, hq, hsl⟩ := hM.hcover p hp hne
    exact hT ⟨q, hq, hsl⟩

/-! ## The workspace holds the sets of the model -/

set_option maxHeartbeats 1600000 in
/-- **The workspace after the spanner part of Phase 4 holds the sets of the model.** See the
module docstring for the five facts. The hypotheses on the model are those of
`outDelSet_subset_sup`, and `hWalkNew` (the walks of the spanners of newly active pairs lie in
their spanners). The slot model `hM` ties the slots to the pairs. -/
theorem p4SpanWV_cover {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (hinfo : info = stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord')
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hU : tr.cs.G.BatchIsValid U)
    (hMod : RestartScurModelInv tr) (hBD : BunDisjointInv tr)
    (hMod' : RestartScurModelInv info.state) (hBD' : BunDisjointInv info.state)
    (hDynG' : ∀ p ∈ activePairs info.state, (info.state.dyn p).G.E = (info.state.bun p).edges)
    (hInactiveBkts : ∀ C ∈ components tr.cs.G₀, C ∉ tr.activeComps →
      ∀ e ∈ (tr.cs.compSt C).G.E \ (tr.cs.compSt C).RF.F.E,
        ∃ b ∈ tr.activeBuckets C, e ∈ (tr.bun (C, b)).edges)
    (hBunEdges : ∀ p ∈ activePairs info.state,
      (info.state.bun p).edges = (tr.bun p).edges \ batchDeletes U)
    (hHApply : ∀ p ∈ activePairs info.state,
      (tr.dyn p).H.applyBatch (info.stepOut p).UH = (info.state.dyn p).H)
    (hDynG : ∀ p ∈ activePairs tr, (tr.dyn p).G.E = (tr.bun p).edges)
    (hWalkNew : ∀ p ∈ activePairs info.state, p ∉ activePairs tr →
      ∀ g ∈ (info.state.dyn p).G.E, ∀ x ∈ walkEdges (piTotal (info.state.dyn p) g),
        x ∈ (info.state.dyn p).H.E)
    (v : EmbView) (hM : P4SlotModel P tr info slotOf S6 mem₀ qs ns) :
    let W := (p4SpanWV P S6 mem₀ tr.S_cur.E v (qs.map Prod.fst) qs ns).1
    (∀ e, tgtEDec tr.S_cur.E (tr.cs.RF.F.E \ info.state.cs.RF.F.E) W.inAct W.inTgt
      (batchLastOp U) e ↔ e ∈ info.state.S_cur.E) ∧
    (∀ e ∈ tr.S_cur.E, e ∈ W.inDtot ↔ e ∈ info.D_total) ∧
    (∀ e ∈ outDelSet (fun _ => canonicalSparsify P.impl) tr U ord ord',
      e ∈ batchDeletes U ∨ e ∈ W.delSup) ∧
    (∀ e ∈ outInsSet (fun _ => canonicalSparsify P.impl) tr U ord ord',
      e ∈ batchDeletes U ∨ e ∈ batchInsEdges U ∨ e ∈ tr.cs.RF.F.E \ info.state.cs.RF.F.E ∨
        e ∈ (info.newlyActive.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
          (tr.bun (C, b)).edges) ∨ e ∈ W.insSup) ∧
    (∀ e, e ∈ W.reemb ↔ e ∈ info.state.activeComps.biUnion fun C =>
      (tr.activeBuckets C).biUnion fun b =>
        updateReembSet (tr.dyn (C, b)) (info.U_B (C, b)) (canonicalSparsify P.impl)) := by
  classical
  intro W
  -- Facts of the model, before any local definition.
  have hstep : ∀ p, info.stepOut p =
      DynSpanner.update (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl) := by
    subst hinfo; intro p; rfl
  have hdyn : ∀ p, info.state.dyn p = (info.stepOut p).state := by subst hinfo; intro p; rfl
  have hbkt : info.state.activeBuckets = tr.activeBuckets := by subst hinfo; rfl
  have hdec : ∀ e, (∀ p ∈ activePairs info.state, e ∈ (info.state.bun p).edges →
      (e ∈ info.state.S_cur.E ↔ e ∈ (info.state.dyn p).H.E)) ∧
      ((∀ p ∈ activePairs info.state, e ∉ (info.state.bun p).edges) →
        (e ∈ info.state.S_cur.E ↔ batchLastOp U e = 1 ∨ (batchLastOp U e = 0 ∧
          (e ∈ tr.S_cur.E ∨ e ∈ tr.cs.RF.F.E \ info.state.cs.RF.F.E)))) := by
    subst hinfo
    exact fun e => mem_targetE'_iff_dec (P := P) hI hU hMod hMod' hBD' hDynG' hInactiveBkts
      hBunEdges e
  have hoDel : outDelSet (fun _ => canonicalSparsify P.impl) tr U ord ord' ⊆
      batchDeletes U ∪ info.D_total ∪
        (activePairs info.state).biUnion fun p => uhDelFinset (info.stepOut p).UH := by
    subst hinfo
    exact outDelSet_subset_sup (P := P) hI hU hMod hBD hMod' hBD' hDynG' hInactiveBkts hBunEdges
      hHApply hDynG
  have hoIns : outInsSet (fun _ => canonicalSparsify P.impl) tr U ord ord' ⊆
      batchDeletes U ∪ batchInsEdges U ∪ (tr.cs.RF.F.E \ info.state.cs.RF.F.E) ∪ info.D_total ∪
        (info.newlyActive.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
          (tr.bun (C, b)).edges) ∪
        (activePairs info.state).biUnion fun p => uhInsFinset (info.stepOut p).UH := by
    subst hinfo
    exact outInsSet_subset_sup (P := P) hI hU hMod hBD hMod' hBD' hDynG' hInactiveBkts hBunEdges
      hHApply hDynG
  have hDT : ∀ x, x ∈ info.D_total ↔ ∃ p ∈ activePairs info.state,
      x ∈ (info.stepOut p).D ∨ ∃ g ∈ ((tr.dyn p).H.E ∩ (info.stepOut p).state.G.E) \
        (info.stepOut p).state.H.E, x ∈ walkEdges (piTotal (info.stepOut p).state g) := by
    subst hinfo; exact mem_D_total_iff _ tr U ord ord'
  have hnewly : ∀ p ∈ activePairs info.state, p ∉ activePairs tr → p.1 ∈ info.newlyActive := by
    subst hinfo
    intro p hp hp0
    exact (Finset.mem_union.mp (mem_activePairs.mp hp).1).resolve_left fun ha =>
      hp0 (mem_activePairs.mpr ⟨ha, (mem_activePairs.mp hp).2⟩)
  have hkeep : ∀ p, info.U_B p = [] → info.stepOut p = ⟨tr.dyn p, [], ∅, 0⟩ := fun p h => by
    rw [hstep, h, update_nil]
  have hHsub : ∀ p ∈ activePairs tr, ∀ e ∈ (tr.dyn p).H.E, e ∈ tr.S_cur.E := fun p hp e he => by
    rw [hMod.2.2.1]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨p.1, (mem_activePairs.mp hp).1, Finset.mem_biUnion.mpr ⟨p.2, (mem_activePairs.mp hp).2, he⟩⟩))
  have hBdel : ∀ p ∈ activePairs info.state, ∀ e ∈ (info.state.bun p).edges,
      e ∈ (tr.bun p).edges ∧ e ∉ batchDeletes U := fun p hp e he => by
    rw [hBunEdges p hp] at he; exact Finset.mem_sdiff.mp he
  -- The sets of the marks.
  set A := (activePairs info.state).biUnion fun p => (info.state.bun p).edges with hA
  set T := (activePairs info.state).biUnion fun p => (info.state.dyn p).H.E with hT
  -- The loop over the tasks.
  have hfitT : ∀ q ∈ qs, ∀ d, P4Eff S6 mem₀ q d →
      P4SlotFits A T (p4St P mem₀ q d).G.E (p4St P mem₀ q d).H.E := by
    intro q hq d hd
    obtain ⟨p, hp, -, -, hst, -⟩ := hM.eff_pair hinfo hq hd
    rw [hst]; exact p4_pair_fits hMod' hBD' hDynG' hp
  have hslots : qs.Pairwise fun a b => a.1.slot ≠ b.1.slot := by
    have h := hM.hnd
    rw [List.map_map] at h
    exact List.pairwise_map.mp h
  have hpw : qs.Pairwise (fun q₁ q₂ => ∀ d₁ d₂, P4Eff S6 mem₀ q₁ d₁ → P4Eff S6 mem₀ q₂ d₂ →
      Disjoint (p4St P mem₀ q₁ d₁).G.E (p4St P mem₀ q₂ d₂).G.E) := by
    refine List.Pairwise.imp_of_mem ?_ hslots
    intro q₁ q₂ hq₁ hq₂ hne d₁ d₂ hd₁ hd₂
    obtain ⟨p₁, hp₁, hsl₁, -, hst₁, -⟩ := hM.eff_pair hinfo hq₁ hd₁
    obtain ⟨p₂, hp₂, hsl₂, -, hst₂, -⟩ := hM.eff_pair hinfo hq₂ hd₂
    have hpne : p₁ ≠ p₂ := fun h => hne (by rw [hsl₁, hsl₂, h])
    rw [hst₁, hst₂, hDynG' p₁ hp₁, hDynG' p₂ hp₂]
    exact hBD'.1 p₁ hp₁ p₂ hp₂ hpne
  have hS₀ : P4MarkOK A T ⟨∅, ∅, ∅, [], [], [], ∅, []⟩ :=
    ⟨Finset.empty_subset _, fun e he => absurd he (Finset.notMem_empty e)⟩
  obtain ⟨tg, tmk, tin, tdt, trm⟩ := p4TaskLoop_facts P S6 mem₀ tr.S_cur.E A T qs
    ⟨∅, ∅, ∅, [], [], [], ∅, []⟩ v hfitT hpw (fun _ _ _ _ => Finset.disjoint_empty_left _) hS₀
  set Wt := qs.foldl (p4WVStep P S6 mem₀ tr.S_cur.E) (⟨∅, ∅, ∅, [], [], [], ∅, []⟩, v) with hWt
  -- The loop over the new slots.
  have hfitN : ∀ q ∈ ns, ∀ (hs : q.1 < cap) (d : DSHist),
      p4SpanAfter P S6 mem₀ (qs.map Prod.fst) ⟨q.1, hs⟩ = some d →
      P4SlotFits A T (d.state P).G.E (d.state P).H.E ∧ ∀ e ∈ q.2, e ∈ (d.state P).G.E := by
    intro q hq hs d hd
    obtain ⟨p, hp, hsl⟩ := hM.hnewSlot q hq
    obtain ⟨hs', d', hd', hst⟩ := hM.after hinfo hp
    have hdd : d' = d := by
      rw [show (⟨slotOf p, hs'⟩ : Fin cap) = ⟨q.1, hs⟩ from Fin.ext hsl.symm] at hd'
      exact Option.some.inj (hd'.symm.trans hd)
    subst hdd
    refine ⟨by rw [hst]; exact p4_pair_fits hMod' hBD' hDynG' hp, fun e he => ?_⟩
    rw [← hM.hnewList q hq hs d' hd]; exact List.mem_toFinset.mpr he
  obtain ⟨ng, nmk, nin, ndt, nrm⟩ := p4NewLoop_facts P (p4SpanAfter P S6 mem₀ (qs.map Prod.fst))
    A T ns Wt.1 Wt.2 hfitN tmk
  have hW : W = (ns.foldl (p4NewStep P (p4SpanAfter P S6 mem₀ (qs.map Prod.fst)))
      (Wt.1, Wt.2)).1 := rfl
  rw [← hW] at ng nmk nin ndt nrm
  -- An active pair with a nonempty batch: its task, and what the task left.
  have hpairIn : ∀ p ∈ activePairs info.state, info.U_B p ≠ [] → ∃ q ∈ qs, ∃ d,
      P4Eff S6 mem₀ q d ∧ p4St P mem₀ q d = info.state.dyn p ∧
      q.2.UH.Perm (info.stepOut p).UH ∧ q.2.dL.toFinset = (info.stepOut p).D ∧
      q.2.rL.toFinset = updateReembSet (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl) ∧
      P4TaskIn P mem₀ tr.S_cur.E q d Wt.1 := by
    intro p hp hne
    obtain ⟨q, hq, d, hd, hsl⟩ := hM.pair_eff hp hne
    obtain ⟨p', hp', hsl', -, hst, hUH, hD, hR⟩ := hM.eff_pair hinfo hq hd
    have hpp : p' = p := hM.hinj p' hp' p hp (hsl'.symm.trans hsl)
    subst hpp
    exact ⟨q, hq, d, hd, hst, hUH, hD, hR, tin q hq d hd⟩
  -- An unmarked edge of the bundle of a pair is in its old spanner exactly when it is in its new
  -- spanner.
  have hHH : ∀ p ∈ activePairs info.state, ∀ e ∈ (info.state.bun p).edges, e ∉ W.inAct →
      (e ∈ (tr.dyn p).H.E ↔ e ∈ (info.state.dyn p).H.E) := by
    intro p hp e heB hnA
    by_cases hne : info.U_B p = []
    · rw [hdyn, hkeep p hne]
    · obtain ⟨q, hq, d, hd, hst, hUH, -, -, hin⟩ := hpairIn p hp hne
      have hin' := hin.mono ng
      have hGE : e ∈ (p4St P mem₀ q d).G.E := by rw [hst, hDynG' p hp]; exact heB
      constructor
      · intro hH
        by_contra hH'
        have hdel : e ∈ uhDelFinset q.2.UH := by
          rw [uhDelFinset_perm hUH]
          refine sdiff_subset_uhDelFinset (tr.dyn p).H _ ?_
          rw [hHApply p hp]; exact Finset.mem_sdiff.mpr ⟨hH, hH'⟩
        exact hnA ((hin'.2.1 e hdel).2 hGE)
      · intro hH'
        by_contra hH
        have hins : e ∈ uhInsFinset q.2.UH := by
          rw [uhInsFinset_perm hUH]
          refine sdiff_subset_uhInsFinset (tr.dyn p).H _ ?_
          rw [hHApply p hp]; exact Finset.mem_sdiff.mpr ⟨hH', hH⟩
        exact hnA ((hin'.2.2.1 e hins).2 hGE)
  -- (1) The marks decide the new output graph.
  have hC1 : ∀ e, tgtEDec tr.S_cur.E (tr.cs.RF.F.E \ info.state.cs.RF.F.E) W.inAct W.inTgt
      (batchLastOp U) e ↔ e ∈ info.state.S_cur.E := by
    intro e
    unfold tgtEDec
    by_cases hAct : e ∈ W.inAct
    · obtain ⟨p, hp, heB⟩ := Finset.mem_biUnion.mp (nmk.1 hAct)
      have hfit := p4_pair_fits hMod' hBD' hDynG' hp
      have heG : e ∈ (info.state.dyn p).G.E := by rw [hDynG' p hp]; exact heB
      have hsimp : ((e ∈ W.inAct ∧ e ∈ W.inTgt) ∨ (e ∉ W.inAct ∧ (batchLastOp U e = 1 ∨
          (batchLastOp U e = 0 ∧ (e ∈ tr.S_cur.E ∨ e ∈ tr.cs.RF.F.E \ info.state.cs.RF.F.E))))) ↔
          e ∈ W.inTgt := by
        simp only [hAct, true_and, not_true_eq_false, false_and, or_false]
      rw [hsimp, nmk.2 e hAct, ← hfit.2 e heG, (hdec e).1 p hp heB]
    · simp only [hAct, false_and, not_false_eq_true, true_and, false_or]
      by_cases hB : ∃ p ∈ activePairs info.state, e ∈ (info.state.bun p).edges
      · obtain ⟨⟨C, b⟩, hp, heB⟩ := hB
        rw [(hdec e).1 _ hp heB]
        by_cases hp0 : (C, b) ∈ activePairs tr
        · obtain ⟨heB0, hnd⟩ := hBdel _ hp e heB
          have hcore := Finset.mem_sdiff.mp
            ((hMod.2.2.2.2 C (mem_activePairs.mp hp0).1 b (mem_activePairs.mp hp0).2).1 heB0)
          have hl0 : batchLastOp U e = 0 := lastOp_zero_of_mem_not_del hU hcore.1 hnd
          have hnF : e ∉ tr.cs.RF.F.E \ info.state.cs.RF.F.E := fun h =>
            hcore.2 (Finset.mem_sdiff.mp h).1
          have hOSH : e ∈ tr.S_cur.E ↔ e ∈ (tr.dyn (C, b)).H.E := by
            rw [← scur_inter_dynG_eq_dynH hI hMod hBD (mem_activePairs.mp hp0).1
              (mem_activePairs.mp hp0).2 (hDynG _ hp0), Finset.mem_inter]
            exact ⟨fun h => ⟨h, by rw [hDynG _ hp0]; exact heB0⟩, fun h => h.1⟩
          rw [← hHH _ hp e heB hAct, ← hOSH]
          simp [hl0, hnF]
        · exfalso
          obtain ⟨q, hq, hq1⟩ := hM.hnew _ hp hp0
          obtain ⟨hs, d, hd, hst⟩ := hM.after hinfo hp
          have hs' : q.1 < cap := hq1 ▸ hs
          have hd' : p4SpanAfter P S6 mem₀ (qs.map Prod.fst) ⟨q.1, hs'⟩ = some d := by
            rw [show (⟨q.1, hs'⟩ : Fin cap) = ⟨slotOf (C, b), hs⟩ from Fin.ext hq1]; exact hd
          have hl : e ∈ q.2 := by
            rw [← List.mem_toFinset, hM.hnewList q hq hs' d hd', hst, hDynG' _ hp]; exact heB
          exact hAct (nin q hq hs' d hd' e hl)
      · push_neg at hB
        exact ((hdec e).2 hB).symm
  -- The edges of `D_total` are scanned, or are edges of newly active bundles outside the old
  -- output graph.
  have hDTcov : ∀ x ∈ info.D_total, (x ∈ Wt.1.inDtot ∧ x ∈ Wt.1.delSup ∧ x ∈ Wt.1.insSup) ∨
      (x ∉ tr.S_cur.E ∧ x ∈ (info.newlyActive.biUnion fun C => (tr.activeBuckets C).biUnion
        fun b => (tr.bun (C, b)).edges)) := by
    intro x hx
    obtain ⟨⟨C, b⟩, hp, h⟩ := (hDT x).mp hx
    by_cases hne : info.U_B (C, b) = []
    · exfalso
      rw [hkeep _ hne] at h
      rcases h with h | ⟨g, hg, -⟩
      · simp at h
      · exact (Finset.mem_sdiff.mp hg).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hg).1).1
    · obtain ⟨q, hq, d, hd, hst, hUH, hD, -, hin⟩ := hpairIn _ hp hne
      rcases h with h | ⟨g, hg, hxw⟩
      · obtain ⟨h1, h2, h3, -⟩ := hin.1 x (List.mem_toFinset.mp (hD ▸ h))
        exact Or.inl ⟨h1, h2, h3⟩
      · obtain ⟨hgHG, hgH'⟩ := Finset.mem_sdiff.mp hg
        obtain ⟨hgH, hgG'⟩ := Finset.mem_inter.mp hgHG
        by_cases hp0 : (C, b) ∈ activePairs tr
        · have hgdel : g ∈ uhDelFinset q.2.UH := by
            rw [uhDelFinset_perm hUH]
            refine sdiff_subset_uhDelFinset (tr.dyn (C, b)).H _ ?_
            rw [hHApply _ hp, hdyn]; exact Finset.mem_sdiff.mpr ⟨hgH, hgH'⟩
          obtain ⟨h1, h2, h3, -⟩ := hin.2.2.2.2 g hgdel (by rw [hst, hdyn]; exact hgG')
            (by rw [hst, hdyn]; exact hgH') (hHsub _ hp0 g hgH) x (by rw [hst, hdyn]; exact hxw)
          exact Or.inl ⟨h1, h2, h3⟩
        · have hxH' : x ∈ (info.state.dyn (C, b)).H.E := hWalkNew _ hp hp0 g
            (by rw [hdyn]; exact hgG') x (by rw [hdyn]; exact hxw)
          have hxB' : x ∈ (info.state.bun (C, b)).edges :=
            (hMod'.2.2.2.2 C (mem_activePairs.mp hp).1 b (mem_activePairs.mp hp).2).2.2.2 hxH'
          obtain ⟨hxB, hxnd⟩ := hBdel _ hp x hxB'
          refine Or.inr ⟨fun hxO => p4NewBun_not_mem_scur hinfo hI hU hMod hMod' hBD' hp hp0 hxB'
            hxO hxnd, Finset.mem_biUnion.mpr ⟨C, hnewly _ hp hp0, Finset.mem_biUnion.mpr
              ⟨b, by rw [← hbkt]; exact (mem_activePairs.mp hp).2, hxB⟩⟩⟩
  -- (2) `inDtot` on the old output graph.
  have hC2 : ∀ e ∈ tr.S_cur.E, e ∈ W.inDtot ↔ e ∈ info.D_total := by
    intro x hxO
    rw [ndt]
    constructor
    · intro hx
      rcases tdt x hx with h | ⟨q, hq, d, hd, h⟩
      · exact absurd h (Finset.notMem_empty x)
      · obtain ⟨⟨C, b⟩, hp, -, -, hst, -, hD, -⟩ := hM.eff_pair hinfo hq hd
        refine (hDT x).mpr ⟨(C, b), hp, ?_⟩
        rcases h with h | ⟨g, hg, hxw⟩
        · exact Or.inl (hD ▸ List.mem_toFinset.mpr h)
        · right
          rw [hst] at hg hxw
          obtain ⟨hgGH, hgO⟩ := Finset.mem_inter.mp hg
          obtain ⟨hgG', hgH'⟩ := Finset.mem_sdiff.mp hgGH
          have hgB' : g ∈ (info.state.bun (C, b)).edges := by rw [← hDynG' _ hp]; exact hgG'
          obtain ⟨hgB, hgnd⟩ := hBdel _ hp g hgB'
          by_cases hp0 : (C, b) ∈ activePairs tr
          · have hgH : g ∈ (tr.dyn (C, b)).H.E := by
              rw [← scur_inter_dynG_eq_dynH hI hMod hBD (mem_activePairs.mp hp0).1
                (mem_activePairs.mp hp0).2 (hDynG _ hp0)]
              exact Finset.mem_inter.mpr ⟨hgO, by rw [hDynG _ hp0]; exact hgB⟩
            rw [hdyn] at hgG' hgH' hxw
            exact ⟨g, Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hgH, hgG'⟩, hgH'⟩, hxw⟩
          · exact absurd (p4NewBun_not_mem_scur hinfo hI hU hMod hMod' hBD' hp hp0 hgB' hgO hgnd)
              not_false
    · intro hx
      rcases hDTcov x hx with h | h
      · exact h.1
      · exact absurd hxO h.1
  -- (3) The leaving edges.
  have hUHdel : ∀ x, (∃ p ∈ activePairs info.state, x ∈ uhDelFinset (info.stepOut p).UH) →
      x ∈ W.delSup := by
    rintro x ⟨p, hp, hx⟩
    by_cases hne : info.U_B p = []
    · rw [hkeep p hne] at hx; simp [uhDelFinset] at hx
    · obtain ⟨q, hq, d, hd, -, hUH, -, -, hin⟩ := hpairIn p hp hne
      exact ng.2.2.2.1 x (hin.2.1 x (by rw [uhDelFinset_perm hUH]; exact hx)).1
  have hC3 : ∀ e ∈ outDelSet (fun _ => canonicalSparsify P.impl) tr U ord ord',
      e ∈ batchDeletes U ∨ e ∈ W.delSup := by
    intro e he
    have heO : e ∈ tr.S_cur.E := (Finset.mem_sdiff.mp he).1
    rcases Finset.mem_union.mp (hoDel he) with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact Or.inl h
      · rcases hDTcov e h with h' | h'
        · exact Or.inr (ng.2.2.2.1 e h'.2.1)
        · exact absurd heO h'.1
    · obtain ⟨p, hp, hx⟩ := Finset.mem_biUnion.mp h
      exact Or.inr (hUHdel e ⟨p, hp, hx⟩)
  -- (4) The entering edges.
  have hC4 : ∀ e ∈ outInsSet (fun _ => canonicalSparsify P.impl) tr U ord ord',
      e ∈ batchDeletes U ∨ e ∈ batchInsEdges U ∨ e ∈ tr.cs.RF.F.E \ info.state.cs.RF.F.E ∨
        e ∈ (info.newlyActive.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
          (tr.bun (C, b)).edges) ∨ e ∈ W.insSup := by
    intro e he
    rcases Finset.mem_union.mp (hoIns he) with h | h
    · rcases Finset.mem_union.mp h with h | h
      · rcases Finset.mem_union.mp h with h | h
        · rcases Finset.mem_union.mp h with h | h
          · rcases Finset.mem_union.mp h with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
        · rcases hDTcov e h with h' | h'
          · exact Or.inr (Or.inr (Or.inr (Or.inr (ng.2.2.2.2.1 e h'.2.2))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h'.2)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · obtain ⟨p, hp, hx⟩ := Finset.mem_biUnion.mp h
      by_cases hne : info.U_B p = []
      · rw [hkeep p hne] at hx; simp [uhInsFinset] at hx
      · obtain ⟨q, hq, d, hd, -, hUH, -, -, hin⟩ := hpairIn p hp hne
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (ng.2.2.2.2.1 e (hin.2.2.1 e (by rw [uhInsFinset_perm hUH]; exact hx)).1))))
  -- (5) The list `reemb`.
  have hC5 : ∀ e, e ∈ W.reemb ↔ e ∈ info.state.activeComps.biUnion fun C =>
      (tr.activeBuckets C).biUnion fun b =>
        updateReembSet (tr.dyn (C, b)) (info.U_B (C, b)) (canonicalSparsify P.impl) := by
    intro x
    rw [nrm]
    constructor
    · intro hx
      rcases trm x hx with h | ⟨q, hq, d, hd, h⟩
      · simp at h
      · obtain ⟨⟨C, b⟩, hp, -, -, -, -, -, hR⟩ := hM.eff_pair hinfo hq hd
        refine Finset.mem_biUnion.mpr ⟨C, (mem_activePairs.mp hp).1, Finset.mem_biUnion.mpr
          ⟨b, by rw [← hbkt]; exact (mem_activePairs.mp hp).2, ?_⟩⟩
        rw [← hR]; exact List.mem_toFinset.mpr h
    · intro hx
      obtain ⟨C, hC, hx⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨b, hb, hx⟩ := Finset.mem_biUnion.mp hx
      have hp : (C, b) ∈ activePairs info.state :=
        mem_activePairs.mpr ⟨hC, by rw [hbkt]; exact hb⟩
      by_cases hne : info.U_B (C, b) = []
      · rw [hne, updateReembSet_nil] at hx; simp at hx
      · obtain ⟨q, hq, d, hd, -, -, -, hR, hin⟩ := hpairIn _ hp hne
        exact hin.2.2.2.1 x (List.mem_toFinset.mp (hR ▸ hx))
  exact ⟨hC1, hC2, hC3, hC4, hC5⟩

end

end MinCostFlow.SparseCore.Program
