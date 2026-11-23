module

public import MinCostFlow.SparseCore.SparseCoreHelpers

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Single-step invariants for `stepTreeCoreAuxWith`

Proves the single-step `S_cur` preservation, empty-batch triviality, no-reinsert propagation
(`stepTreeCoreAux_stage_stepWith`), and per-step `U_S` length decomposition
(`stepTreeCoreAux_US_lenWith`) for `SparseCoreBounds.lean`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

lemma stepTreeCoreAux_stage_stepWith (reinsertD : Bool) {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs₀ : CompLSFState} {G₀ : MGraph}
    (hI₀ : CompLSFInv C_lsst ℓ₀ cs₀) (hcs₀_G₀ : cs₀.G₀ = G₀)
    (hCov₀ : ∀ C ∈ components G₀,
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) = (cs₀.compSt C).RF.F.E)
    (stPrev : TreeCoreState L) (U : List Update) (actB : Finset ℕ → Finset ℤ)
    (hactB : stPrev.activeBuckets = actB)
    (hG₀_eq : stPrev.cs.G₀ = G₀)
    (hI_prev : CompLSFInv C_lsst ℓ₀ stPrev.cs)
    (hAct_prev : stPrev.activeComps ⊆ components G₀)
    (_hUnt : ∀ C ∈ components G₀, C ∉ stPrev.activeComps →
      stPrev.cs.compSt C = cs₀.compSt C ∧ stPrev.ts C = initTildeState (cs₀.compSt C))
    (hHist : ∀ C ∈ components G₀, LSFDerivedFrom (cs₀.compSt C) (stPrev.cs.compSt C))
    (hT : ∀ C ∈ components G₀, TildeInv (cs₀.compSt C) (stPrev.cs.compSt C) (stPrev.ts C))
    (hU : stPrev.cs.G.BatchIsValid U)
    (hS_val : stPrev.S_cur.IsValid)
    (hS_V : stPrev.S_cur.V = stPrev.cs.RF.R)
    (hS_E : stPrev.S_cur.E =
      (stPrev.activeComps.biUnion fun C => (actB C).biUnion fun b => (stPrev.dyn (C, b)).H.E) ∪
        (stPrev.activeComps.biUnion fun C => extraSet (stPrev.cs.compSt C) (stPrev.ts C)) ∪
        stPrev.cs.crossEdges)
    (hS_sub : (coreGraph stPrev.cs.G stPrev.cs.lsf).IsSubgraph stPrev.S_cur)
    (hDyn_sub : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      ((stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.dyn (C, b)).H.E ⊆
        ((stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.dyn (C, b)).G.E)
    (hDyn_G_sub : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      ((stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.dyn (C, b)).G.E ⊆
        ((stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.ts C).C.E)
    (hDyn_nil : U = [] → ∀ C ∈ components G₀, ∀ b : ℤ,
      (stepTreeCoreAuxWith reinsertD sparsify stPrev U).stepOut (C, b) = ⟨stPrev.dyn (C, b), [], ∅, 0⟩) :
    let info := stepTreeCoreAuxWith reinsertD sparsify stPrev U
    let stCur := info.state
    let D_reins : Finset ℕ := if reinsertD then info.D_total else ∅
    let keepSet := ((stPrev.S_cur.E ∩ stCur.S_cur.E) \ batchDeletes U) \ D_reins
    stCur.S_cur.IsValid ∧
    stCur.S_cur.V = stCur.cs.RF.R ∧
    stCur.S_cur.E =
      (stCur.activeComps.biUnion fun C => (actB C).biUnion fun b => (stCur.dyn (C, b)).H.E) ∪
        (stCur.activeComps.biUnion fun C => extraSet (stCur.cs.compSt C) (stCur.ts C)) ∪
        stCur.cs.crossEdges ∧
    (coreGraph stCur.cs.G stCur.cs.lsf).IsSubgraph stCur.S_cur ∧
    stPrev.S_cur.BatchIsValid info.U_S ∧
    stCur.S_cur = stPrev.S_cur.applyBatch info.U_S ∧
    (U = [] → info.U_S = [] ∧ stCur.cost = stPrev.cost) ∧
    ((reinsertD = false → NoBatchReinsert stPrev.cs.G U → NoBatchReinsert stPrev.S_cur info.U_S) ∧
      (∀ e ∈ stPrev.S_cur.E, e ∈ stCur.S_cur.E → (∀ u ∈ info.U_S, ¬ u.Inserts e) →
        (reinsertD = true → e ∉ info.D_total) ∧ ∀ u ∈ U, ¬ u.Inserts e)) ∧
    info.U_S.length =
      (stPrev.S_cur.E \ keepSet).card + (stCur.cs.RF.R \ stPrev.cs.RF.R).card +
        (stCur.S_cur.E \ keepSet).card := by
  set info := stepTreeCoreAuxWith reinsertD sparsify stPrev U
  set stCur := info.state
  set D_reins : Finset ℕ := if reinsertD then info.D_total else ∅
  have hcs_eq : stCur.cs = compLSFBatch stPrev.cs U := rfl
  have hI_cur : CompLSFInv C_lsst ℓ₀ stCur.cs := hcs_eq ▸ compLSFBatch_inv hI_prev hU
  have hG₀_cur : stCur.cs.G₀ = G₀ := by rw [hcs_eq, compLSFBatch_G₀, hG₀_eq]
  have hAct_cur : stCur.activeComps ⊆ components G₀ := by
    intro C hC
    change C ∈ stPrev.activeComps ∪ (touchedCompsBatch stPrev.cs U \ stPrev.activeComps) at hC
    rcases Finset.mem_union.mp hC with h1 | h2
    · exact hAct_prev h1
    · have ht := Finset.mem_filter.mp (Finset.mem_sdiff.mp h2).1
      exact hG₀_eq ▸ ht.1
  have hT_cur : ∀ C ∈ components G₀, TildeInv (cs₀.compSt C) (stCur.cs.compSt C) (stCur.ts C) := by
    intro C hC
    have hsp := compLSFBatch_compSt hI_prev hU (hG₀_eq ▸ hC)
    have htd := tildeStepBatch_spec (hI₀.hCompLSF C (hcs₀_G₀ ▸ hC)).1 (hCov₀ C hC)
      (hI_prev.hCompLSF C (hG₀_eq ▸ hC)).1 (hHist C hC) (hT C hC) hsp.2.2.1
    exact (hsp.1.trans htd.1.symm) ▸ htd.2.2.2.1
  set targetE : Finset ℕ :=
    (stCur.activeComps.biUnion fun C => (actB C).biUnion fun b => (stCur.dyn (C, b)).H.E) ∪
      (stCur.activeComps.biUnion fun C => extraSet (stCur.cs.compSt C) (stCur.ts C)) ∪
      stCur.cs.crossEdges
  have hTgt_sub : targetE ⊆ stCur.cs.G.E \ stCur.cs.RF.F.E := by
    intro e he
    rcases Finset.mem_union.mp he with he12 | heX
    · rcases Finset.mem_union.mp he12 with heD | heEx
      · rw [Finset.mem_biUnion] at heD
        rcases heD with ⟨C, hCA, heB⟩
        have hC := hAct_cur hCA
        rw [Finset.mem_biUnion] at heB
        rcases heB with ⟨b, hb, heb⟩
        have heC := (hT_cur C hC).hCE_sub (hDyn_G_sub C hC b hb (hDyn_sub C hC b hb heb))
        exact compLSF_comp_sdiff_sub hI_cur (hG₀_cur ▸ hC) heC
      · rw [Finset.mem_biUnion] at heEx
        rcases heEx with ⟨C, hCA, heExC⟩
        have hC := hAct_cur hCA
        exact compLSF_comp_sdiff_sub hI_cur (hG₀_cur ▸ hC) (Finset.mem_sdiff.mp heExC).1
    · exact compLSF_crossEdges_sub hI_cur heX
  have hUS_eq : info.U_S = buildUSReinsert stPrev.cs U stCur.cs stPrev.S_cur targetE D_reins := by
    dsimp only [info, stepTreeCoreAuxWith, targetE, stCur, D_reins]
    rw [hactB]
    rfl
  have hS_next_eq : stCur.S_cur = stPrev.S_cur.applyBatch info.U_S := rfl
  have hUS_sp := buildUSReinsert_spec hI_prev hU hS_val hS_V hS_sub (targetE := targetE)
    (by rw [← hcs_eq]; exact hTgt_sub) D_reins
  dsimp only at hUS_sp
  rw [← hcs_eq, ← hUS_eq, ← hS_next_eq] at hUS_sp
  have hlen_US : info.U_S.length =
      (stPrev.S_cur.E \ (((stPrev.S_cur.E ∩ stCur.S_cur.E) \ batchDeletes U) \ D_reins)).card +
        (stCur.cs.RF.R \ stPrev.cs.RF.R).card +
        (stCur.S_cur.E \ (((stPrev.S_cur.E ∩ stCur.S_cur.E) \ batchDeletes U) \ D_reins)).card := by
    have h := hUS_sp.2.2.2.2.2.2.1
    rw [← hUS_sp.2.2.2.1] at h
    exact h
  have hEmpty : U = [] → info.U_S = [] ∧ stCur.cost = stPrev.cost := by
    intro hUnil
    have htouch_nil : touchedCompsBatch stPrev.cs U = ∅ := by
      simp [touchedCompsBatch, hUnil, projCompBatchG]
    have hnew_nil : info.newlyActive = ∅ := by
      change touchedCompsBatch stPrev.cs U \ stPrev.activeComps = ∅
      rw [htouch_nil, Finset.empty_sdiff]
    have hact_cur_eq : stCur.activeComps = stPrev.activeComps := by
      change stPrev.activeComps ∪ info.newlyActive = stPrev.activeComps
      rw [hnew_nil, Finset.union_empty]
    have hcs_nil : stCur.cs = stPrev.cs := by rw [hcs_eq, hUnil]; rfl
    have hproj_nil : ∀ C, projCompBatchG stPrev.cs.G (stPrev.cs.compSt C).G U = [] := fun C => by
      rw [hUnil]; rfl
    have hts_nil : ∀ C, stCur.ts C = stPrev.ts C := fun C => by
      change (tildeStepBatch (stPrev.cs.compSt C) (stPrev.ts C)
        (projCompBatchG stPrev.cs.G (stPrev.cs.compSt C).G U)).2.1 = stPrev.ts C
      rw [hproj_nil C]; rfl
    have hdyn_E_nil : ∀ C ∈ components G₀, ∀ b : ℤ,
        (stCur.dyn (C, b)).H.E = (stPrev.dyn (C, b)).H.E := fun C hC b => by
      change (info.stepOut (C, b)).state.H.E = _
      rw [hDyn_nil hUnil C hC b]
    have hD_reins_nil : D_reins = ∅ := by
      dsimp only [D_reins]
      cases reinsertD
      · rfl
      · simp only [↓reduceIte]
        have hDs : info.D_spanner = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro e he
          change e ∈ stCur.activeComps.biUnion (fun C => (stPrev.activeBuckets C).biUnion fun b =>
            (info.stepOut (C, b)).D) at he
          rw [Finset.mem_biUnion] at he
          rcases he with ⟨C, hCA, heB⟩
          rw [Finset.mem_biUnion] at heB
          rcases heB with ⟨b, _, heb⟩
          rw [hDyn_nil hUnil C (hAct_cur hCA) b] at heb
          exact Finset.notMem_empty e heb
        have hDl : info.D_leftS = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro e he
          change e ∈ stCur.activeComps.biUnion (fun C => (stPrev.activeBuckets C).biUnion fun b =>
            (((stPrev.dyn (C, b)).H.E ∩ (info.stepOut (C, b)).state.G.E) \
              (info.stepOut (C, b)).state.H.E).biUnion
              (fun e₀ => walkEdges (piTotal (info.stepOut (C, b)).state e₀))) at he
          simp only [Finset.mem_biUnion] at he
          rcases he with ⟨C, hCA, b, _, e₀, he₀, _⟩
          rw [hDyn_nil hUnil C (hAct_cur hCA) b] at he₀
          simp only [Finset.mem_sdiff, Finset.mem_inter] at he₀
          exact he₀.2 he₀.1.1
        change info.D_spanner ∪ info.D_leftS = ∅
        rw [hDs, hDl, Finset.union_empty]
    have hTgt_nil : targetE = stPrev.S_cur.E := by
      rw [hS_E]
      dsimp only [targetE]
      rw [hact_cur_eq, hcs_nil]
      congr 1; congr 1
      · refine Finset.biUnion_congr rfl fun C hC => Finset.biUnion_congr rfl fun b _ => ?_
        exact hdyn_E_nil C (hAct_prev hC) b
      · exact Finset.biUnion_congr rfl fun C _ => by rw [hts_nil C]
    have hkeep_nil : (stPrev.S_cur.E ∩ targetE) \ batchDeletes U = stPrev.S_cur.E := by
      rw [hTgt_nil, Finset.inter_self, hUnil, batchDeletes]
      simp
    have hUS_nil : info.U_S = [] := by
      rw [hUS_eq]
      dsimp only [buildUSReinsert]
      rw [hD_reins_nil, hkeep_nil, Finset.sdiff_empty, hTgt_nil, hcs_nil]
      simp
    have hCost_nil : stCur.cost = stPrev.cost := by
      have hqC_zero : (stCur.activeComps.sum fun C =>
          (tildeStepBatch (stPrev.cs.compSt C) (stPrev.ts C)
            (projCompBatchG stPrev.cs.G (stPrev.cs.compSt C).G U)).1.length) = 0 :=
        Finset.sum_eq_zero fun C _ => by rw [hproj_nil C]; rfl
      have hdynC_zero : (stCur.activeComps.sum fun C =>
          (stPrev.activeBuckets C).sum fun b => (info.stepOut (C, b)).cost) = 0 :=
        Finset.sum_eq_zero fun C hCA => Finset.sum_eq_zero fun b _ => by
          rw [hDyn_nil hUnil C (hAct_cur hCA) b]
      have hlazy_zero : info.newlyActive.sum (fun C => stPrev.lazyInitCost C) = 0 := by
        rw [hnew_nil, Finset.sum_empty]
      change stPrev.cost + (U.length +
        stCur.activeComps.sum (fun C => (tildeStepBatch (stPrev.cs.compSt C) (stPrev.ts C)
          (projCompBatchG stPrev.cs.G (stPrev.cs.compSt C).G U)).1.length) +
        info.U_S.length +
        stCur.activeComps.sum (fun C => (stPrev.activeBuckets C).sum fun b => (info.stepOut (C, b)).cost) +
        info.newlyActive.sum (fun C => stPrev.lazyInitCost C)) = stPrev.cost
      rw [hqC_zero, hdynC_zero, hlazy_zero, hUS_nil, hUnil]
      simp
    exact ⟨hUS_nil, hCost_nil⟩
  have hNoReins :
      (reinsertD = false → NoBatchReinsert stPrev.cs.G U → NoBatchReinsert stPrev.S_cur info.U_S) ∧
      (∀ e ∈ stPrev.S_cur.E, e ∈ stCur.S_cur.E → (∀ u ∈ info.U_S, ¬ u.Inserts e) →
        (reinsertD = true → e ∉ info.D_total) ∧ ∀ u ∈ U, ¬ u.Inserts e) := by
    refine ⟨fun hr => hUS_sp.2.2.2.2.2.2.2 (by simp [D_reins, hr]), fun e hePrev heCur hNoIns => ?_⟩
    have heTgt : e ∈ targetE := hUS_sp.2.2.2.1 ▸ heCur
    have hP := buildUSReinsert_noReinsertPropagates hU hS_sub hePrev heTgt (hUS_eq ▸ hNoIns)
    refine ⟨fun hr => ?_, hP.2⟩
    have hDreins_eq : D_reins = info.D_total := by simp [D_reins, hr]
    exact hDreins_eq ▸ hP.1
  exact ⟨hUS_sp.2.1, hUS_sp.2.2.1, hUS_sp.2.2.2.1, hUS_sp.2.2.2.2.2.1,
    hUS_sp.1, hS_next_eq, hEmpty, hNoReins, hlen_US⟩

lemma stepTreeCoreAux_US_lenWith (reinsertD : Bool) {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs₀ : CompLSFState} {G₀ : MGraph}
    (hI₀ : CompLSFInv C_lsst ℓ₀ cs₀) (hcs₀_G₀ : cs₀.G₀ = G₀)
    (hCov₀ : ∀ C ∈ components G₀,
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) = (cs₀.compSt C).RF.F.E)
    (stPrev : TreeCoreState L) (U : List Update) (actB : Finset ℕ → Finset ℤ)
    (hG₀_eq : stPrev.cs.G₀ = G₀)
    (hI_prev : CompLSFInv C_lsst ℓ₀ stPrev.cs)
    (hAct_prev : stPrev.activeComps ⊆ components G₀)
    (hAct_cur : (stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.activeComps ⊆ components G₀)
    (hUnt : ∀ C ∈ components G₀, C ∉ stPrev.activeComps →
      stPrev.cs.compSt C = cs₀.compSt C ∧ stPrev.ts C = initTildeState (cs₀.compSt C))
    (hHist : ∀ C ∈ components G₀, LSFDerivedFrom (cs₀.compSt C) (stPrev.cs.compSt C))
    (hT : ∀ C ∈ components G₀, TildeInv (cs₀.compSt C) (stPrev.cs.compSt C) (stPrev.ts C))
    (hU : stPrev.cs.G.BatchIsValid U)
    (hS_E_prev : stPrev.S_cur.E =
      (stPrev.activeComps.biUnion fun C => (actB C).biUnion fun b => (stPrev.dyn (C, b)).H.E) ∪
        (stPrev.activeComps.biUnion fun C => extraSet (stPrev.cs.compSt C) (stPrev.ts C)) ∪
        stPrev.cs.crossEdges)
    (hS_E_cur : (stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.S_cur.E =
      ((stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.activeComps.biUnion fun C =>
        (actB C).biUnion fun b => ((stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.dyn (C, b)).H.E) ∪
        ((stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.activeComps.biUnion fun C =>
          extraSet ((stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.cs.compSt C)
            ((stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.ts C)) ∪
        (stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.cs.crossEdges)
    (hUS_card : (stepTreeCoreAuxWith reinsertD sparsify stPrev U).U_S.length =
      (stPrev.S_cur.E \ (((stPrev.S_cur.E ∩ (stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.S_cur.E) \
        batchDeletes U) \ (if reinsertD then (stepTreeCoreAuxWith reinsertD sparsify stPrev U).D_total else ∅))).card +
      ((stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.cs.RF.R \ stPrev.cs.RF.R).card +
      ((stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.S_cur.E \
        (((stPrev.S_cur.E ∩ (stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.S_cur.E) \
          batchDeletes U) \ (if reinsertD then (stepTreeCoreAuxWith reinsertD sparsify stPrev U).D_total else ∅))).card)
    (hDyn_UH : ∀ C ∈ (stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.activeComps, ∀ b ∈ actB C,
      (stPrev.dyn (C, b)).H.applyBatch ((stepTreeCoreAuxWith reinsertD sparsify stPrev U).stepOut (C, b)).UH =
        ((stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.dyn (C, b)).H) :
    let info := stepTreeCoreAuxWith reinsertD sparsify stPrev U
    let stCur := info.state
    info.U_S.length ≤
      (stCur.activeComps.sum fun C => (actB C).sum fun b => (info.stepOut (C, b)).UH.length) +
      (info.newlyActive.sum fun C => (actB C).sum fun b => (stPrev.dyn (C, b)).H.E.card) +
      7 * U.length +
      2 * (stCur.cs.RF.R \ stPrev.cs.RF.R).card +
      2 * (if reinsertD then info.D_total.card else 0) := by
  set info := stepTreeCoreAuxWith reinsertD sparsify stPrev U
  set stCur := info.state
  set D_reins : Finset ℕ := if reinsertD then info.D_total else ∅
  set keepSet := ((stPrev.S_cur.E ∩ stCur.S_cur.E) \ batchDeletes U) \ D_reins
  have hcs_eq : stCur.cs = compLSFBatch stPrev.cs U := rfl
  have hI_cur : CompLSFInv C_lsst ℓ₀ stCur.cs := hcs_eq ▸ compLSFBatch_inv hI_prev hU
  have hdel_sub : stPrev.S_cur.E \ keepSet ⊆ (stPrev.S_cur.E \ stCur.S_cur.E) ∪ batchDeletes U ∪ D_reins := by
    intro e he
    rw [Finset.mem_sdiff] at he
    by_cases hD : e ∈ D_reins
    · exact Finset.mem_union_right _ hD
    · refine Finset.mem_union_left _ ?_
      by_cases hc : e ∈ stCur.S_cur.E
      · refine Finset.mem_union_right _ ?_
        by_contra hnot
        exact he.2 (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨he.1, hc⟩, hnot⟩, hD⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he.1, hc⟩)
  have hins_sub : stCur.S_cur.E \ keepSet ⊆ (stCur.S_cur.E \ stPrev.S_cur.E) ∪ batchDeletes U ∪ D_reins := by
    intro e he
    rw [Finset.mem_sdiff] at he
    by_cases hD : e ∈ D_reins
    · exact Finset.mem_union_right _ hD
    · refine Finset.mem_union_left _ ?_
      by_cases hp : e ∈ stPrev.S_cur.E
      · refine Finset.mem_union_right _ ?_
        by_contra hnot
        exact he.2 (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hp, he.1⟩, hnot⟩, hD⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he.1, hp⟩)
  have hprev_act_sub_cur : stPrev.activeComps ⊆ stCur.activeComps := by
    intro C hC; change C ∈ stPrev.activeComps ∪ info.newlyActive; exact Finset.mem_union_left _ hC
  have hprev_cur : stPrev.S_cur.E \ stCur.S_cur.E ⊆
      (stCur.activeComps.biUnion fun C => (actB C).biUnion fun b =>
        (stPrev.dyn (C, b)).H.E \ (stCur.dyn (C, b)).H.E) ∪
      ((components G₀).biUnion fun C =>
        extraSet (stPrev.cs.compSt C) (stPrev.ts C) \ extraSet (stCur.cs.compSt C) (stCur.ts C)) ∪
      batchDeletes U := by
    rw [hS_E_prev, hS_E_cur]
    intro e he
    simp only [Finset.mem_sdiff, Finset.mem_union] at he ⊢
    rcases he.1 with (heD | heEx) | heX
    · left; left
      rw [Finset.mem_biUnion] at heD
      rcases heD with ⟨C, hCA, heB⟩
      rw [Finset.mem_biUnion] at heB
      rcases heB with ⟨b, hb, heb⟩
      refine Finset.mem_biUnion.mpr ⟨C, hprev_act_sub_cur hCA,
        Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_sdiff.mpr ⟨heb, fun h => he.2 ?_⟩⟩⟩
      exact Or.inl (Or.inl
        (Finset.mem_biUnion.mpr ⟨C, hprev_act_sub_cur hCA, Finset.mem_biUnion.mpr ⟨b, hb, h⟩⟩))
    · left; right
      rw [Finset.mem_biUnion] at heEx
      rcases heEx with ⟨C, hCA, heExC⟩
      refine Finset.mem_biUnion.mpr ⟨C, hAct_prev hCA, Finset.mem_sdiff.mpr ⟨heExC, fun h => he.2 ?_⟩⟩
      exact Or.inl (Or.inr (Finset.mem_biUnion.mpr ⟨C, hprev_act_sub_cur hCA, h⟩))
    · right
      exact compLSF_crossEdges_sdiff_prev stPrev.cs U (Finset.mem_sdiff.mpr ⟨heX, fun h =>
        he.2 (Or.inr h)⟩)
  have hcur_prev : stCur.S_cur.E \ stPrev.S_cur.E ⊆
      ((stCur.activeComps.biUnion fun C => (actB C).biUnion fun b =>
        (stCur.dyn (C, b)).H.E \ (stPrev.dyn (C, b)).H.E) ∪
       (info.newlyActive.biUnion fun C => (actB C).biUnion fun b =>
        (stPrev.dyn (C, b)).H.E)) ∪
      ((components G₀).biUnion fun C =>
        extraSet (stCur.cs.compSt C) (stCur.ts C) \ extraSet (stPrev.cs.compSt C) (stPrev.ts C)) ∪
      (stCur.cs.crossEdges \ stPrev.cs.crossEdges) := by
    rw [hS_E_prev, hS_E_cur]
    intro e he
    simp only [Finset.mem_sdiff, Finset.mem_union] at he ⊢
    rcases he.1 with (heD | heEx) | heX
    · left; left
      rw [Finset.mem_biUnion] at heD
      rcases heD with ⟨C, hCA, heB⟩
      rw [Finset.mem_biUnion] at heB
      rcases heB with ⟨b, hb, heb⟩
      by_cases hCP : C ∈ stPrev.activeComps
      · left
        refine Finset.mem_biUnion.mpr ⟨C, hCA, Finset.mem_biUnion.mpr ⟨b, hb,
          Finset.mem_sdiff.mpr ⟨heb, fun h => he.2 ?_⟩⟩⟩
        exact Or.inl (Or.inl (Finset.mem_biUnion.mpr ⟨C, hCP, Finset.mem_biUnion.mpr ⟨b, hb, h⟩⟩))
      · have hCN : C ∈ info.newlyActive := by
          change C ∈ stPrev.activeComps ∪ info.newlyActive at hCA
          exact (Finset.mem_union.mp hCA).resolve_left hCP
        by_cases hep : e ∈ (stPrev.dyn (C, b)).H.E
        · right
          exact Finset.mem_biUnion.mpr ⟨C, hCN, Finset.mem_biUnion.mpr ⟨b, hb, hep⟩⟩
        · left
          exact Finset.mem_biUnion.mpr ⟨C, hCA, Finset.mem_biUnion.mpr ⟨b, hb,
            Finset.mem_sdiff.mpr ⟨heb, hep⟩⟩⟩
    · left; right
      rw [Finset.mem_biUnion] at heEx
      rcases heEx with ⟨C, hCA, heExC⟩
      refine Finset.mem_biUnion.mpr ⟨C, hAct_cur hCA, Finset.mem_sdiff.mpr ⟨heExC, fun h => he.2 ?_⟩⟩
      by_cases hCP : C ∈ stPrev.activeComps
      · exact Or.inl (Or.inr (Finset.mem_biUnion.mpr ⟨C, hCP, h⟩))
      · exfalso
        obtain ⟨hcs_u, hts_u⟩ := hUnt C (hAct_cur hCA) hCP
        rw [hcs_u, hts_u, extraSet_init] at h
        exact Finset.notMem_empty e h
    · right; exact ⟨heX, fun h => he.2 (Or.inr h)⟩
  have hUH_symm : ∀ C ∈ stCur.activeComps, ∀ b ∈ actB C,
      ((stPrev.dyn (C, b)).H.E \ (stCur.dyn (C, b)).H.E).card +
        ((stCur.dyn (C, b)).H.E \ (stPrev.dyn (C, b)).H.E).card ≤
          (info.stepOut (C, b)).UH.length :=
    fun C hC b hb => symmDiff_applyBatch_UH (hDyn_UH C hC b hb)
  have hex_diff : ∀ C ∈ components G₀,
      (extraSet (stCur.cs.compSt C) (stCur.ts C) \ extraSet (stPrev.cs.compSt C) (stPrev.ts C)).card ≤
        projCompBatchWeight stPrev.cs.G (stPrev.cs.compSt C).G U +
          ((stCur.cs.compSt C).R \ (stPrev.cs.compSt C).R).card ∧
      (extraSet (stPrev.cs.compSt C) (stPrev.ts C) \ extraSet (stCur.cs.compSt C) (stCur.ts C)).card ≤
        projCompBatchWeight stPrev.cs.G (stPrev.cs.compSt C).G U := by
    intro C hC
    set U_proj := projCompBatchG stPrev.cs.G (stPrev.cs.compSt C).G U
    have hsp := compLSFBatch_compSt hI_prev hU (hG₀_eq ▸ hC)
    have hcsC : stCur.cs.compSt C = applyLSFBatch (stPrev.cs.compSt C) U_proj := by
      rw [hcs_eq]; exact hsp.1
    have htsC : stCur.ts C = (tildeStepBatch (stPrev.cs.compSt C) (stPrev.ts C) U_proj).2.1 := rfl
    have htd := tildeStepBatch_spec (hI₀.hCompLSF C (hcs₀_G₀ ▸ hC)).1 (hCov₀ C hC)
      (hI_prev.hCompLSF C (hG₀_eq ▸ hC)).1 (hHist C hC) (hT C hC) hsp.2.2.1
    have htw := tildeStepBatch_projCompBatchG_spec (hI₀.hCompLSF C (hcs₀_G₀ ▸ hC)).1 (hCov₀ C hC)
      U hI_prev (hG₀_eq ▸ hC) (hHist C hC) (hT C hC) hU
    dsimp only at htw
    rw [htd.1] at htw
    exact ⟨by simpa only [hcsC, htsC] using htw.2.2.1, by simpa only [hcsC, htsC] using htw.2.2.2⟩
  have hsum_proj : ((components G₀).sum fun C =>
      projCompBatchWeight stPrev.cs.G (stPrev.cs.compSt C).G U) ≤ 2 * U.length := by
    rw [← hG₀_eq]
    exact sum_projCompBatchWeight_le U hI_prev hU
  have hsum_R : ((components G₀).sum fun C =>
      ((stCur.cs.compSt C).R \ (stPrev.cs.compSt C).R).card) =
      (stCur.cs.RF.R \ stPrev.cs.RF.R).card := by
    have hR_m : ∀ C ∈ components stPrev.cs.G₀, (stPrev.cs.compSt C).R ⊆ (stCur.cs.compSt C).R :=
      fun C hC => (compLSFBatch_compSt hI_prev hU hC).2.2.2.1
    rw [← hG₀_eq]
    exact compLSF_sum_R_sdiff_eq hI_prev hI_cur (by rw [hcs_eq, compLSFBatch_G₀]) hR_m
  have hdel_le : (batchDeletes U).card ≤ U.length := batchDeletes_card_le U
  have hcross_le : (stCur.cs.crossEdges \ stPrev.cs.crossEdges).card ≤ U.length := by
    rw [hcs_eq]; exact compLSF_crossEdges_sdiff_cur U stPrev.cs
  have hbi_card_le : ∀ (S : Finset (Finset ℕ)) (f : Finset ℕ → ℤ → Finset ℕ),
      (S.biUnion fun C => (actB C).biUnion fun b => f C b).card ≤
        S.sum fun C => (actB C).sum fun b => (f C b).card := fun S f =>
    le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
  have hdel_sub' : stPrev.S_cur.E \ keepSet ⊆
      (stCur.activeComps.biUnion fun C => (actB C).biUnion fun b =>
        (stPrev.dyn (C, b)).H.E \ (stCur.dyn (C, b)).H.E) ∪
      ((components G₀).biUnion fun C =>
        extraSet (stPrev.cs.compSt C) (stPrev.ts C) \ extraSet (stCur.cs.compSt C) (stCur.ts C)) ∪
      batchDeletes U ∪ D_reins := fun e he => by
    rcases Finset.mem_union.mp (hdel_sub he) with h12 | h3
    · rcases Finset.mem_union.mp h12 with h1 | h2
      · exact Finset.mem_union_left _ (hprev_cur h1)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h2)
    · exact Finset.mem_union_right _ h3
  have hc1 : (stPrev.S_cur.E \ keepSet).card ≤
      (stCur.activeComps.sum fun C => (actB C).sum fun b =>
        ((stPrev.dyn (C, b)).H.E \ (stCur.dyn (C, b)).H.E).card) +
      ((components G₀).sum fun C =>
        projCompBatchWeight stPrev.cs.G (stPrev.cs.compSt C).G U) +
      (batchDeletes U).card + D_reins.card := by
    have hpc := le_trans (Finset.card_le_card hdel_sub') (le_trans (Finset.card_union_le _ _)
      (Nat.add_le_add_right (le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
    have h1 := hbi_card_le stCur.activeComps (fun C b => (stPrev.dyn (C, b)).H.E \ (stCur.dyn (C, b)).H.E)
    have h2 : ((components G₀).biUnion fun C =>
        extraSet (stPrev.cs.compSt C) (stPrev.ts C) \ extraSet (stCur.cs.compSt C) (stCur.ts C)).card ≤
        (components G₀).sum fun C => projCompBatchWeight stPrev.cs.G (stPrev.cs.compSt C).G U :=
      le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun C hC => (hex_diff C hC).2)
    exact le_trans hpc (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add h1 h2) _) _)
  have hc2 : (stCur.S_cur.E \ keepSet).card ≤
      (stCur.activeComps.sum fun C => (actB C).sum fun b =>
        ((stCur.dyn (C, b)).H.E \ (stPrev.dyn (C, b)).H.E).card) +
      (info.newlyActive.sum fun C => (actB C).sum fun b => (stPrev.dyn (C, b)).H.E.card) +
      ((components G₀).sum fun C =>
        projCompBatchWeight stPrev.cs.G (stPrev.cs.compSt C).G U) +
      ((components G₀).sum fun C =>
        ((stCur.cs.compSt C).R \ (stPrev.cs.compSt C).R).card) +
      (stCur.cs.crossEdges \ stPrev.cs.crossEdges).card + (batchDeletes U).card + D_reins.card := by
    have hins_c := le_trans (Finset.card_le_card hins_sub)
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    have hcp1 := le_trans (Finset.card_le_card hcur_prev) (Finset.card_union_le _ _)
    have h1 := hbi_card_le stCur.activeComps (fun C b => (stCur.dyn (C, b)).H.E \ (stPrev.dyn (C, b)).H.E)
    have h1n := hbi_card_le info.newlyActive (fun C b => (stPrev.dyn (C, b)).H.E)
    have h2 : ((components G₀).biUnion fun C =>
        extraSet (stCur.cs.compSt C) (stCur.ts C) \ extraSet (stPrev.cs.compSt C) (stPrev.ts C)).card ≤
        ((components G₀).sum fun C =>
          projCompBatchWeight stPrev.cs.G (stPrev.cs.compSt C).G U) +
        ((components G₀).sum fun C =>
          ((stCur.cs.compSt C).R \ (stPrev.cs.compSt C).R).card) := by
      rw [← Finset.sum_add_distrib]
      exact le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun C hC => (hex_diff C hC).1)
    refine le_trans hins_c ?_
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right hcp1 _) _) ?_
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _) ?_
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add (Finset.card_union_le _ _) h2) _) _) _) ?_
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add h1 h1n) le_rfl) _) _) _) ?_
    omega
  have hsum_add : (stCur.activeComps.sum fun C => (actB C).sum fun b =>
        ((stPrev.dyn (C, b)).H.E \ (stCur.dyn (C, b)).H.E).card) +
      (stCur.activeComps.sum fun C => (actB C).sum fun b =>
        ((stCur.dyn (C, b)).H.E \ (stPrev.dyn (C, b)).H.E).card) ≤
      stCur.activeComps.sum fun C => (actB C).sum fun b => (info.stepOut (C, b)).UH.length := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun C hC => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun b hb => hUH_symm C hC b hb
  rw [hsum_R] at hc2
  have hcomb : (stPrev.S_cur.E \ keepSet).card + (stCur.cs.RF.R \ stPrev.cs.RF.R).card +
      (stCur.S_cur.E \ keepSet).card ≤
      (stCur.activeComps.sum fun C => (actB C).sum fun b => (info.stepOut (C, b)).UH.length) +
      (info.newlyActive.sum fun C => (actB C).sum fun b => (stPrev.dyn (C, b)).H.E.card) +
      2 * ((components G₀).sum fun C =>
        projCompBatchWeight stPrev.cs.G (stPrev.cs.compSt C).G U) +
      (stCur.cs.crossEdges \ stPrev.cs.crossEdges).card +
      2 * (batchDeletes U).card +
      2 * (stCur.cs.RF.R \ stPrev.cs.RF.R).card +
      2 * D_reins.card := by
    have hsum12 := Nat.add_le_add hc1 hc2
    omega
  dsimp only
  rw [hUS_card]
  have hD_card_eq : D_reins.card = if reinsertD then info.D_total.card else 0 := by
    cases reinsertD <;> simp [D_reins]
  rw [hD_card_eq] at hcomb
  change (stPrev.S_cur.E \ keepSet).card + (stCur.cs.RF.R \ stPrev.cs.RF.R).card +
      (stCur.S_cur.E \ keepSet).card ≤
    (stCur.activeComps.sum fun C => (actB C).sum fun b => (info.stepOut (C, b)).UH.length) +
    (info.newlyActive.sum fun C => (actB C).sum fun b => (stPrev.dyn (C, b)).H.E.card) +
    7 * U.length + 2 * (stCur.cs.RF.R \ stPrev.cs.RF.R).card +
    2 * (if reinsertD then info.D_total.card else 0)
  omega


end

end MinCostFlow.SparseCore
