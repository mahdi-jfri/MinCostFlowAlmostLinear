module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepEmbFold
public import MinCostFlow.SparseCore.Program.AssemblyFirstEmbModel

import Mathlib.Tactic

/-!
# The embedding table after Phase 4 holds the new embedding (`AssemblyFirstStepEmbStep`)

After Phase 4 the view of the embedding table must hold, on every core edge of the new state, the
walk of that edge in the new state (`BundleTreeState.emb`). This file proves it against the model
(`p4Emb_model`), from the slot model of Phase 4 (`P4SlotModel`) and the facts of the model that
the selection part of Phase 4 already uses (those of `p4SpanWV_cover`).

By `AssemblyFirstStepEmbFold.lean`, the view is the old view with the walks written on the seen
edges and on the entering edges. Every written walk is the new one: a task writes the walk of its
new spanner at an edge of its new graph outside its new spanner, and such an edge is outside the
new sparsified core, so its new walk is that walk. A new slot does the same, and an entering edge
is in the new sparsified core, so its walk is the edge itself.

So it is left to see that a core edge of the new state that was not written was a core edge
before, with the same walk. There are three cases, by `mem_targetE'_iff_dec`:
* the edge is in the new sparsified core: it is not entering, so it was in the old one;
* the edge is in the bundle of an active pair and outside the new spanner: the pair is old (a new
  pair writes all such edges), the edge was not in the old sparsified core (else the spanner
  deleted it, and the task wrote it), and the spanner did not embed it again (else the task wrote
  it), so its walk did not change (`dsHist_piTotal_eq_of_not_mem_updateReembSet`);
* the edge is in no active bundle and outside the new sparsified core: the batch did not touch
  it, so it was a core edge before, outside the sparsified core and every active bundle, and its
  walk is empty before and after.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart
open MinCostFlow.SparseCore.Program.Read

public section

/-- An edge that a batch deletes is touched by the batch. -/
theorem batchLastOp_ne_zero_of_delete :
    ∀ (U : List Update) {e : ℕ}, Update.delete e ∈ U → batchLastOp U e ≠ 0
  | [], _, h => absurd h List.not_mem_nil
  | u :: rest, e, h => by
    rw [batchLastOp_cons]
    by_cases hr : batchLastOp rest e ≠ 0
    · rw [if_pos hr]; exact hr
    · rw [if_neg hr]
      rcases List.mem_cons.mp h with rfl | h
      · simp
      · exact absurd (batchLastOp_ne_zero_of_delete rest h) hr

/-- An edge that leaves a graph under a batch is deleted by the batch. -/
theorem delete_mem_of_mem_sdiff_applyBatch :
    ∀ (G : MGraph) (U : List Update) {e : ℕ}, e ∈ G.E → e ∉ (G.applyBatch U).E →
      Update.delete e ∈ U
  | _, [], _, he, hne => by simp [MGraph.applyBatch] at hne; exact absurd he hne
  | G, u :: rest, e, he, hne => by
    by_cases hd : u = Update.delete e
    · subst hd; exact List.mem_cons_self
    refine List.mem_cons_of_mem _
      (delete_mem_of_mem_sdiff_applyBatch (G.applyUpdate u) rest ?_ hne)
    rcases u with ⟨e', a, b⟩ | e' | ⟨v, v', St, Sh⟩
    · exact Finset.mem_insert_of_mem he
    · exact Finset.mem_erase.mpr ⟨fun h => hd (by rw [h]), he⟩
    · exact he

set_option maxHeartbeats 1600000 in
/-- **The embedding table after Phase 4 holds the new embedding on the new core edges.** The
view `v` before Phase 4 holds the old embedding on the old core edges. The hypotheses on the
model are those of `p4SpanWV_cover`, and `hValid` (the histories of the spanners after the tasks
are valid, as their rep says) is for `dsHist_piTotal_eq_of_not_mem_updateReembSet`. -/
theorem p4Emb_model {P : DSParams} {cap : ℕ} {tr : BundleTreeState P.L} {U : List Update}
    {ord ord' : ℕ → List End} {info : BundleTreeStepInfo P.L} {slotOf : Finset ℕ × ℤ → ℕ}
    {S6 : BucketSpannerState cap} {mem₀ : ℕ → ℕ} {qs : List (SpanUpdTask × P4TaskOut)}
    {ns : List (ℕ × List ℕ)} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
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
    (hDynG : ∀ p ∈ activePairs tr, (tr.dyn p).G.E = (tr.bun p).edges) (hL : 1 ≤ P.L)
    (hValid : ∀ (j : Fin cap) (d : DSHist), p4SpanAfter P S6 mem₀ (qs.map Prod.fst) j = some d →
      d.G₀.IsValid ∧ d.G₀.m ≤ P.mMax ∧ d.G₀.BatchIsValid d.flat ∧ ∀ u ∈ d.flat, isDelOrSplit u)
    (hM : P4SlotModel P tr info slotOf S6 mem₀ qs ns) {v : EmbView}
    (hdom : (coreGraph tr.cs.G tr.cs.lsf).E ⊆ v.dom)
    (hemb : ∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E, v.emb e = tr.emb e) :
    (coreGraph info.state.cs.G info.state.cs.lsf).E ⊆
        ((p4SpanWV P S6 mem₀ tr.S_cur.E v (qs.map Prod.fst) qs ns).2.apply
          (insSelfChange ((outInsSet (fun _ => canonicalSparsify P.impl) tr U ord ord').sort
            (· ≤ ·)))).dom ∧
      ∀ e ∈ (coreGraph info.state.cs.G info.state.cs.lsf).E,
        ((p4SpanWV P S6 mem₀ tr.S_cur.E v (qs.map Prod.fst) qs ns).2.apply
          (insSelfChange ((outInsSet (fun _ => canonicalSparsify P.impl) tr U ord ord').sort
            (· ≤ ·)))).emb e = info.state.emb e := by
  classical
  -- facts of the model
  have hdec : ∀ e, (∀ p ∈ activePairs info.state, e ∈ (info.state.bun p).edges →
      (e ∈ info.state.S_cur.E ↔ e ∈ (info.state.dyn p).H.E)) ∧
      ((∀ p ∈ activePairs info.state, e ∉ (info.state.bun p).edges) →
        (e ∈ info.state.S_cur.E ↔ batchLastOp U e = 1 ∨ (batchLastOp U e = 0 ∧
          (e ∈ tr.S_cur.E ∨ e ∈ tr.cs.RF.F.E \ info.state.cs.RF.F.E)))) := by
    subst hinfo
    exact fun e => mem_targetE'_iff_dec (P := P) hI hU hMod hMod' hBD' hDynG' hInactiveBkts
      hBunEdges e
  have hstep : ∀ p, info.stepOut p =
      DynSpanner.update (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl) := by
    subst hinfo; intro p; rfl
  have hdyn : ∀ p, info.state.dyn p = (info.stepOut p).state := by subst hinfo; intro p; rfl
  have hG' : info.state.cs.G = tr.cs.G.applyBatch U := by
    subst hinfo; exact compLSFBatch_G tr.cs U
  have hOldNew : ∀ p ∈ activePairs tr, p ∈ activePairs info.state := by
    intro p hp
    have ⟨hC, hb⟩ := mem_activePairs.mp hp
    subst hinfo
    exact mem_activePairs.mpr ⟨Finset.mem_union.mpr (Or.inl hC), hb⟩
  have hOutIns : ∀ e, e ∈ outInsSet (fun _ => canonicalSparsify P.impl) tr U ord ord' ↔
      e ∈ info.state.S_cur.E ∧ (e ∉ tr.S_cur.E ∨ e ∈ batchDeletes U ∨ e ∈ info.D_total) := by
    subst hinfo; exact fun e => mem_outInsSet_iff _ tr U ord ord' e
  -- the new walk of an edge of the graph of an active pair outside its spanner
  have hW : ∀ p ∈ activePairs info.state, ∀ e ∈ (info.state.dyn p).G.E,
      e ∉ (info.state.dyn p).H.E → piTotal (info.state.dyn p) e = info.state.emb e := by
    intro p hp e heG heH
    have heB : e ∈ (info.state.bun p).edges := (hDynG' p hp) ▸ heG
    have heS : e ∉ info.state.S_cur.E := fun h => heH (((hdec e).1 p hp heB).mp h)
    exact (bundleTree_emb_eq_piTotal hBD' hp heS heB).symm
  -- the new history of a task
  have hNH : ∀ q ∈ qs, ∀ (hs : q.1.slot < cap) (d : DSHist), S6 ⟨q.1.slot, hs⟩ = some d →
      mem₀ q.1.batchPtr ≠ 0 → ∃ p ∈ activePairs info.state, q.1.slot = slotOf p ∧
        d.state P = tr.dyn p ∧
        (decodeBatch mem₀ q.1.batchPtr (d.state P).G).1 = info.U_B p ∧
        (p4NewHist P mem₀ d q.1).state P = info.state.dyn p := by
    intro q hq hs d hd hb
    obtain ⟨p, hp, hsl, hbat⟩ := hM.htask q hq
    obtain ⟨hs₂, d₂, hd₂, hst₂⟩ := hM.hslot p hp
    have hdd : d₂ = d := by
      have : S6 ⟨slotOf p, hs₂⟩ = S6 ⟨q.1.slot, hs⟩ := by
        rw [show (⟨slotOf p, hs₂⟩ : Fin cap) = ⟨q.1.slot, hs⟩ from Fin.ext hsl.symm]
      rw [hd₂, hd] at this
      exact Option.some.inj this
    subst hdd
    have hU' := (hbat hs d₂ hd).1
    refine ⟨p, hp, hsl, hst₂, hU', ?_⟩
    show (⟨d₂.G₀, d₂.Us ++ [(decodeBatch mem₀ q.1.batchPtr (d₂.state P).G).1]⟩ : DSHist).state P = _
    rw [hU', dsHist_append_state_eq_update, hst₂, hdyn, hstep]
  -- the written walks are the new ones
  have hT : ∀ q ∈ qs, ∀ (hs : q.1.slot < cap) (d : DSHist), S6 ⟨q.1.slot, hs⟩ = some d →
      mem₀ q.1.batchPtr ≠ 0 → ∀ e ∈ ((p4NewHist P mem₀ d q.1).state P).G.E,
        e ∉ ((p4NewHist P mem₀ d q.1).state P).H.E →
        piTotal ((p4NewHist P mem₀ d q.1).state P) e = info.state.emb e := by
    intro q hq hs d hd hb e heG heH
    obtain ⟨p, hp, -, -, -, hnh⟩ := hNH q hq hs d hd hb
    rw [hnh] at heG heH ⊢
    exact hW p hp e heG heH
  have hN : ∀ q ∈ ns, ∀ (hs : q.1 < cap) (d : DSHist),
      p4SpanAfter P S6 mem₀ (qs.map Prod.fst) ⟨q.1, hs⟩ = some d →
      ∀ e ∈ q.2, e ∉ (d.state P).H.E → piTotal (d.state P) e = info.state.emb e := by
    intro q hq hs d hd e he heH
    obtain ⟨p, hp, hq1⟩ := hM.hnewSlot q hq
    obtain ⟨hs₂, d₂, hd₂, hst₂⟩ := hM.after hinfo hp
    have hdd : d₂ = d := by
      have : p4SpanAfter P S6 mem₀ (qs.map Prod.fst) ⟨slotOf p, hs₂⟩ =
          p4SpanAfter P S6 mem₀ (qs.map Prod.fst) ⟨q.1, hs⟩ := by
        rw [show (⟨slotOf p, hs₂⟩ : Fin cap) = ⟨q.1, hs⟩ from Fin.ext hq1.symm]
      rw [hd₂, hd] at this
      exact Option.some.inj this
    subst hdd
    have heG : e ∈ (d₂.state P).G.E := by
      rw [← hM.hnewList q hq hs d₂ hd]; exact List.mem_toFinset.mpr he
    rw [hst₂] at heG heH ⊢
    exact hW p hp e heG heH
  have hIns : ∀ e ∈ (outInsSet (fun _ => canonicalSparsify P.impl) tr U ord ord').sort (· ≤ ·),
      info.state.emb e = [(e, true)] := by
    intro e he
    have hS := ((hOutIns e).mp ((Finset.mem_sort _).mp he)).1
    simp [BundleTreeState.emb, hS]
  have hInv := (p4SpanWV_viewInv P S6 mem₀ tr.S_cur.E v info.state.emb qs ns hT hN).insSelf hIns
  -- an edge that is not written keeps its walk
  have hkey : ∀ e ∈ (coreGraph info.state.cs.G info.state.cs.lsf).E,
      e ∉ (p4SpanWV P S6 mem₀ tr.S_cur.E v (qs.map Prod.fst) qs ns).1.seenCopy →
      e ∉ outInsSet (fun _ => canonicalSparsify P.impl) tr U ord ord' →
      e ∈ (coreGraph tr.cs.G tr.cs.lsf).E ∧ tr.emb e = info.state.emb e := by
    intro e he hseen hins
    have he' : e ∈ info.state.cs.G.E ∧ e ∉ info.state.cs.RF.F.E := Finset.mem_sdiff.mp he
    by_cases heS' : e ∈ info.state.S_cur.E
    · -- the edge is in the new sparsified core
      have heS : e ∈ tr.S_cur.E := by
        by_contra hS
        exact hins ((hOutIns e).mpr ⟨heS', Or.inl hS⟩)
      refine ⟨hMod.2.2.2.1.2.1 heS, ?_⟩
      simp [BundleTreeState.emb, heS, heS']
    · by_cases hB : ∃ p ∈ activePairs info.state, e ∈ (info.state.bun p).edges
      · obtain ⟨⟨C, b⟩, hp, heB⟩ := hB
        have heH' : e ∉ (info.state.dyn (C, b)).H.E := fun h => heS' (((hdec e).1 _ hp heB).mpr h)
        have heG' : e ∈ (info.state.dyn (C, b)).G.E := (hDynG' _ hp).symm ▸ heB
        by_cases hp0 : (C, b) ∈ activePairs tr
        · -- an old pair
          have heB0 : e ∈ (tr.bun (C, b)).edges :=
            (Finset.mem_sdiff.mp ((hBunEdges _ hp) ▸ heB)).1
          obtain ⟨hC, hb⟩ := mem_activePairs.mp hp0
          have hcore : e ∈ (coreGraph tr.cs.G tr.cs.lsf).E := (hMod.2.2.2.2 C hC b hb).1 heB0
          have hSH : e ∈ tr.S_cur.E → e ∈ (tr.dyn (C, b)).H.E := fun hS => by
            rw [← scur_inter_dynG_eq_dynH hI hMod hBD hC hb (hDynG _ hp0)]
            exact Finset.mem_inter.mpr ⟨hS, (hDynG _ hp0).symm ▸ heB0⟩
          -- the walk of the edge does not change, and it is not in the old sparsified core
          have hsame : e ∉ tr.S_cur.E ∧
              piTotal (info.state.dyn (C, b)) e = piTotal (tr.dyn (C, b)) e := by
            by_cases hUB : info.U_B (C, b) = []
            · have hst : info.state.dyn (C, b) = tr.dyn (C, b) := by
                rw [hdyn, hstep, hUB]; rfl
              exact ⟨fun hS => heH' (hst ▸ hSH hS), by rw [hst]⟩
            · obtain ⟨q, hq, hqs⟩ := hM.hcover _ hp hUB
              obtain ⟨hs, d, hd, hst⟩ := hM.hslot _ hp
              have hs' : q.1.slot < cap := hqs ▸ hs
              have hd' : S6 ⟨q.1.slot, hs'⟩ = some d := by
                rw [show (⟨q.1.slot, hs'⟩ : Fin cap) = ⟨slotOf (C, b), hs⟩ from Fin.ext hqs]
                exact hd
              obtain ⟨p', hp', hsl', hbat⟩ := hM.htask q hq
              have hpp : p' = (C, b) := hM.hinj p' hp' _ hp (hsl'.symm.trans hqs)
              subst hpp
              obtain ⟨hdecU, hzero⟩ := hbat hs' d hd'
              have hb0 : mem₀ q.1.batchPtr ≠ 0 := fun h0 => hUB (hzero.mp h0)
              obtain ⟨p₁, hp₁, hsl₁, -, -, hnh⟩ := hNH q hq hs' d hd' hb0
              have hp1 : p₁ = (C, b) := hM.hinj p₁ hp₁ _ hp (hsl₁.symm.trans hqs)
              subst hp1
              have hOK := hM.hok q hq hs' d hd' hb0
              rw [hdecU] at hOK
              obtain ⟨-, hHap, -, -, -, hRL, -⟩ := hOK
              have hGn : e ∈ ((p4NewHist P mem₀ d q.1).state P).G.E := by rw [hnh]; exact heG'
              have hHn : e ∉ ((p4NewHist P mem₀ d q.1).state P).H.E := by rw [hnh]; exact heH'
              have hnS : e ∉ tr.S_cur.E := by
                intro hS
                have hH0 : e ∈ (d.state P).H.E := by rw [hst]; exact hSH hS
                have hH1 : e ∉ ((d.state P).H.applyBatch q.2.UH).E := by
                  rw [hHap, ← dsHist_append_state_eq_update]
                  show e ∉ ((⟨d.G₀, d.Us ++ [info.U_B (C, b)]⟩ : DSHist).state P).H.E
                  rw [← hdecU]
                  exact hHn
                exact hseen (p4SpanWV_seen_task P S6 mem₀ tr.S_cur.E v qs ns hq hs' hd' hb0 hGn
                  hHn (Or.inr ⟨delete_mem_of_mem_sdiff_applyBatch _ _ hH0 hH1, hS⟩))
              have hnR : e ∉ updateReembSet (d.state P) (info.U_B (C, b)) (canonicalSparsify P.impl) :=
                fun hR => hseen (p4SpanWV_seen_task P S6 mem₀ tr.S_cur.E v qs ns hq hs' hd' hb0
                  hGn hHn (Or.inl (List.mem_toFinset.mp (hRL ▸ hR))))
              have hafter : p4SpanAfter P S6 mem₀ (qs.map Prod.fst) ⟨q.1.slot, hs'⟩ =
                  some (p4NewHist P mem₀ d q.1) := by
                rw [show p4SpanAfter P S6 mem₀ (qs.map Prod.fst) =
                  (qs.map Prod.fst).foldl (p4SpanStep P S6 mem₀) S6 from rfl,
                  p4SpanAfter_at_task P S6 mem₀ hs' hM.hnd (List.mem_map_of_mem hq) S6,
                  p4OnTask_of hs' hd' hb0]
              obtain ⟨hVG, hGm, hBV, hds⟩ := hValid _ _ hafter
              have hfl : (p4NewHist P mem₀ d q.1).flat = d.flat ++ info.U_B (C, b) := by
                simp [p4NewHist, DSHist.flat, hdecU]
              rw [hfl] at hBV hds
              have hnh' : (⟨d.G₀, d.Us ++ [info.U_B (C, b)]⟩ : DSHist).state P =
                  info.state.dyn (C, b) := by
                rw [← hnh]; show _ = (⟨d.G₀, d.Us ++ _⟩ : DSHist).state P; rw [hdecU]
              have heG'' : e ∈ ((⟨d.G₀, d.Us ++ [info.U_B (C, b)]⟩ : DSHist).state P).G.E := by
                rw [hnh']; exact heG'
              have hpi := dsHist_piTotal_eq_of_not_mem_updateReembSet P d (info.U_B (C, b)) hVG hL hGm
                hBV hds e heG'' hnR
              rw [hnh', hst] at hpi
              exact ⟨hnS, hpi⟩
          refine ⟨hcore, ?_⟩
          rw [bundleTree_emb_eq_piTotal hBD hp0 hsame.1 heB0,
            bundleTree_emb_eq_piTotal hBD' hp heS' heB, hsame.2]
        · -- a new pair: all its edges outside its spanner are written
          exfalso
          obtain ⟨q, hq, hq1⟩ := hM.hnew _ hp hp0
          obtain ⟨hs, d, hd, hst⟩ := hM.after hinfo hp
          have hs' : q.1 < cap := hq1 ▸ hs
          have hd' : p4SpanAfter P S6 mem₀ (qs.map Prod.fst) ⟨q.1, hs'⟩ = some d := by
            rw [show (⟨q.1, hs'⟩ : Fin cap) = ⟨slotOf (C, b), hs⟩ from Fin.ext hq1]; exact hd
          have heq : e ∈ q.2 := by
            rw [← List.mem_toFinset, hM.hnewList q hq hs' d hd', hst]; exact heG'
          exact hseen (p4SpanWV_seen_new P S6 mem₀ tr.S_cur.E v qs ns hq hs' hd' heq
            (by rw [hst]; exact heH'))
      · -- the edge is in no active bundle
        have hnone : ∀ p ∈ activePairs info.state, e ∉ (info.state.bun p).edges :=
          fun p hp heB => hB ⟨p, hp, heB⟩
        have hd2 := (hdec e).2 hnone
        have heG : e ∈ (tr.cs.G.applyBatch U).E := hG' ▸ he'.1
        rcases (mem_applyBatch_E_iff_lastOp _ _ _).mp heG with h1 | ⟨h0, heG0⟩
        · exact absurd (hd2.mpr (Or.inl h1)) heS'
        · have heNS : e ∉ tr.S_cur.E := fun h => heS' (hd2.mpr (Or.inr ⟨h0, Or.inl h⟩))
          have heNF : e ∉ tr.cs.RF.F.E := fun h =>
            heS' (hd2.mpr (Or.inr ⟨h0, Or.inr (Finset.mem_sdiff.mpr ⟨h, he'.2⟩)⟩))
          refine ⟨Finset.mem_sdiff.mpr ⟨heG0, heNF⟩, ?_⟩
          rw [bundleTree_emb_eq_nil_of_not_mem heS' hnone]
          refine bundleTree_emb_eq_nil_of_not_mem heNS (fun p hp heB0 => ?_)
          have hnd : e ∉ batchDeletes U := fun hdel => by
            obtain ⟨u, hu, rfl⟩ := (mem_batchDeletes_iff U e).mp hdel
            exact batchLastOp_ne_zero_of_delete U hu h0
          exact hnone p (hOldNew p hp) ((hBunEdges p (hOldNew p hp)).symm ▸
            Finset.mem_sdiff.mpr ⟨heB0, hnd⟩)
  -- the two conjuncts
  obtain ⟨hI1, hI2, hI3⟩ := hInv
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · by_cases hw : e ∈ (p4SpanWV P S6 mem₀ tr.S_cur.E v (qs.map Prod.fst) qs ns).1.seenCopy ∪
        ((outInsSet (fun _ => canonicalSparsify P.impl) tr U ord ord').sort (· ≤ ·)).toFinset
    · exact (hI3 e hw).1
    · simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_sort, not_or] at hw
      exact hI1 (hdom (hkey e he hw.1 hw.2).1)
  · by_cases hw : e ∈ (p4SpanWV P S6 mem₀ tr.S_cur.E v (qs.map Prod.fst) qs ns).1.seenCopy ∪
        ((outInsSet (fun _ => canonicalSparsify P.impl) tr U ord ord').sort (· ≤ ·)).toFinset
    · exact (hI3 e hw).2
    · rw [hI2 e hw]
      simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_sort, not_or] at hw
      obtain ⟨hc, heq⟩ := hkey e he hw.1 hw.2
      rw [hemb e hc, heq]

end

end MinCostFlow.SparseCore.Program
