module

public import MinCostFlow.SparseCore.BundleRun
public import MinCostFlow.SparseCore.SparseCoreHelpers
import MinCostFlow.SparseCore.BundleOutBatchSpec

/-!
# One step of a branch on bundle graphs

This file proves what one step of `stepBundleTree` does to the sparsified core, the analogue of
`stepTreeCoreAux_stage_stepWith` for the quotient branch. The main result is
`stepBundleTree_stage_step`. If before the step the sparsified core `S_cur` is the union of the
spanners of the active bundle graphs, the extra edges of the active components and the cross
edges, then the same holds after the step, and the output batch `U_S` moves the old core to the
new one.

The proof follows the old one. The output batch is `buildUSOrd` on the target edge set of the
step, so its specification (`buildUSOrd_spec`) gives the new core. The new part is the target set.
The step removes from the extra edges of a component every bundle edge of *any* active
component, while `BundleTreeState.extraEdges` removes only the bundle edges of the component
itself. The two agree up to cross edges: an edge that lies in the component graph of `C` and in a
bundle of another component `C'` has its tail root both in the roots of `C` and in the roots of
`C'`, and these are disjoint unless the edge is a cross edge.

For the empty batch the core batch has no split (`coreBatchOf_nil_splitCount`), and the bundle
batches are empty by hypothesis, so the output batch is empty.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.Bundle

/-- A list of deletions and splits with no deletion and no split is empty. -/
theorem eq_nil_of_delOrSplit {UB : List Update} (hds : ∀ op ∈ UB, isDelOrSplit op)
    (hs : batchSplitCount UB = 0) (hd : UB.countP deleteTag = 0) : UB = [] := by
  rcases UB with _ | ⟨u, rest⟩
  · rfl
  · exfalso
    have hu := hds u List.mem_cons_self
    rcases u with ⟨e, a, b⟩ | e | ⟨v, v', St, Sh⟩
    · exact hu
    · rw [List.countP_cons] at hd
      simp [deleteTag] at hd
    · simp only [batchSplitCount, List.countP_cons] at hs
      simp [isSplit] at hs

/-- The splits of a batch without splits, restricted to any set, are empty. -/
private theorem restrictSplits_eq_nil (keep : Finset ℕ) :
    ∀ UC : List Update, batchSplitCount UC = 0 → restrictSplits keep UC = []
  | [], _ => rfl
  | .insert _ _ _ :: UC, h => by
    simp only [restrictSplits]
    exact restrictSplits_eq_nil keep UC (by simpa [batchSplitCount, isSplit] using h)
  | .delete _ :: UC, h => by
    simp only [restrictSplits]
    exact restrictSplits_eq_nil keep UC (by simpa [batchSplitCount, isSplit] using h)
  | .split _ _ _ _ :: UC, h => by
    simp [batchSplitCount, isSplit] at h

/-- For the empty batch the core batch is empty, so it has no split. -/
theorem coreBatchOf_nil_splitCount (cs : CompLSFState) (ord ord' : ℕ → List End) :
    batchSplitCount (coreBatchOf cs ord ord' []) = 0 :=
  rfl

/-- An edge of the old core that the output batch does not insert again is not in `D_reins` and
is not inserted by the input batch. -/
theorem buildUSOrd_noReinsert {cs_old : CompLSFState} {U UC : List Update}
    (hBU : cs_old.G.BatchIsValid U)
    {S_prev : MGraph} (hS_sub : (coreGraph cs_old.G cs_old.lsf).IsSubgraph S_prev)
    {targetE D_reins : Finset ℕ} {e : ℕ} (cs_new : CompLSFState)
    (hePrev : e ∈ S_prev.E) (heTgt : e ∈ targetE)
    (hNoIns : ∀ u ∈ buildUSOrd UC U cs_new S_prev targetE D_reins, ¬ u.Inserts e) :
    e ∉ D_reins ∧ ∀ u ∈ U, ¬ u.Inserts e := by
  classical
  let keepSet := ((S_prev.E ∩ targetE) \ batchDeletes U) \ D_reins
  have hmem_of_notKeep : e ∉ keepSet → False := by
    intro hnk
    have heIns : e ∈ targetE \ keepSet := Finset.mem_sdiff.mpr ⟨heTgt, hnk⟩
    have heMem : Update.insert e (cs_new.RF.root (cs_new.G.tail e))
        (cs_new.RF.root (cs_new.G.head e)) ∈ buildUSOrd UC U cs_new S_prev targetE D_reins := by
      unfold buildUSOrd
      simp only [List.mem_append, List.mem_map]
      right
      exact ⟨e, (Finset.mem_sort (· ≤ ·)).mpr heIns, rfl⟩
    exact hNoIns _ heMem rfl
  refine ⟨fun hD => hmem_of_notKeep (fun h => (Finset.mem_sdiff.mp h).2 hD), fun u hu hIu => ?_⟩
  have heOldG : e ∈ cs_old.G.E := (Finset.mem_sdiff.mp (hS_sub.2.1 hePrev)).1
  have heDel : e ∈ batchDeletes U := mem_batchDeletes_of_inserts hBU heOldG ⟨u, hu, hIu⟩
  exact hmem_of_notKeep (fun h => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).2 heDel)

/-- An edge of the component graph of `C` that is not a cross edge, and whose tail root is a root
of the component `C'`, lies in `C' = C`. -/
theorem compLSF_comp_eq_of_root {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C C' : Finset ℕ} (hC : C ∈ components cs.G₀)
    (hC' : C' ∈ components cs.G₀) {e : ℕ} (heC : e ∈ (cs.compSt C).G.E)
    (hX : e ∉ cs.crossEdges) (hr : cs.RF.root (cs.G.tail e) ∈ (cs.compSt C').R) : C = C' := by
  by_contra hne
  have hIC := (hI.hCompLSF C hC).1
  have htail : (cs.compSt C).G.tail e = cs.G.tail e := (hI.hNonCross_ends C hC e heC hX).1
  have hv : cs.G.tail e ∈ (cs.compSt C).G.V := htail ▸ (hIC.hG_val e heC).1
  have hroot := compLSF_RF_root_eq hI hC hv
  have hrC : cs.RF.root (cs.G.tail e) ∈ (cs.compSt C).G.V := by
    rw [hroot]
    exact lsfInv_R_sub_V hIC (rootedForest_root_spec (lsfInv_to_RS hIC) hv).1
  have hrC' : cs.RF.root (cs.G.tail e) ∈ (cs.compSt C').G.V :=
    lsfInv_R_sub_V (hI.hCompLSF C' hC').1 hr
  exact Finset.disjoint_left.mp (hI.hV_disj C hC C' hC' hne) hrC hrC'

/-- One step of a branch on bundle graphs keeps the form of the sparsified core and moves it by
the output batch (the analogue of `stepTreeCoreAux_stage_stepWith`). Besides the hypotheses of
the old step lemma, it needs that every new bundle edge of a component `C` is a core edge whose
tail root is a root of `C` (`hBun_core`, from the bundle partition after the step), and that on
the empty batch the bundle batches are empty and the bundles keep their edges (`hBun_nil`). -/
theorem stepBundleTree_stage_step {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs₀ : CompLSFState} {G₀ : MGraph}
    (_hI₀ : CompLSFInv C_lsst ℓ₀ cs₀) (_hcs₀_G₀ : cs₀.G₀ = G₀)
    (_hCov₀ : ∀ C ∈ components G₀,
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) = (cs₀.compSt C).RF.F.E)
    (stPrev : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (actB : Finset ℕ → Finset ℤ)
    (hactB : stPrev.activeBuckets = actB)
    (hG₀_eq : stPrev.cs.G₀ = G₀)
    (hI_prev : CompLSFInv C_lsst ℓ₀ stPrev.cs)
    (hAct_prev : stPrev.activeComps ⊆ components G₀)
    (_hHist : ∀ C ∈ components G₀, LSFDerivedFrom (cs₀.compSt C) (stPrev.cs.compSt C))
    (hU : stPrev.cs.G.BatchIsValid U)
    (ρ : Rotation stPrev.cs.G) (σ : Rotation (stPrev.cs.G.applyBatch U)) (hρ : ρ.order = ord)
    (hσ : σ.order = ord') (hrot : RotationBatch 2 U ρ σ)
    (hS_val : stPrev.S_cur.IsValid)
    (hS_V : stPrev.S_cur.V = stPrev.cs.RF.R)
    (hS_E : stPrev.S_cur.E =
      (stPrev.activeComps.biUnion fun C => (actB C).biUnion fun b => (stPrev.dyn (C, b)).H.E) ∪
        (stPrev.activeComps.biUnion fun C => stPrev.extraEdges C) ∪
        stPrev.cs.crossEdges)
    (hS_sub : (coreGraph stPrev.cs.G stPrev.cs.lsf).IsSubgraph stPrev.S_cur)
    (hDyn_sub : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      ((stepBundleTree sparsify stPrev U ord ord').state.dyn (C, b)).H.E ⊆
        ((stepBundleTree sparsify stPrev U ord ord').state.dyn (C, b)).G.E)
    (hDyn_G_sub : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      ((stepBundleTree sparsify stPrev U ord ord').state.dyn (C, b)).G.E ⊆
        ((stepBundleTree sparsify stPrev U ord ord').state.bun (C, b)).edges)
    (hBun_core : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      ∀ e ∈ ((stepBundleTree sparsify stPrev U ord ord').state.bun (C, b)).edges,
        e ∈ (stepBundleTree sparsify stPrev U ord ord').state.cs.G.E \
            (stepBundleTree sparsify stPrev U ord ord').state.cs.RF.F.E ∧
          (stepBundleTree sparsify stPrev U ord ord').state.cs.RF.root
              ((stepBundleTree sparsify stPrev U ord ord').state.cs.G.tail e) ∈
            ((stepBundleTree sparsify stPrev U ord ord').state.cs.compSt C).R)
    (hBun_nil : U = [] → ∀ C ∈ components G₀, ∀ b ∈ actB C,
      (stepBundleTree sparsify stPrev U ord ord').U_B (C, b) = [] ∧
        ((stepBundleTree sparsify stPrev U ord ord').state.bun (C, b)).edges =
          (stPrev.bun (C, b)).edges)
    (hDyn_nil : U = [] → ∀ C ∈ components G₀, ∀ b : ℤ,
      (stepBundleTree sparsify stPrev U ord ord').stepOut (C, b) = ⟨stPrev.dyn (C, b), [], ∅, 0⟩) :
    let info := stepBundleTree sparsify stPrev U ord ord'
    let stCur := info.state
    let D_reins : Finset ℕ := info.D_total
    let keepSet := ((stPrev.S_cur.E ∩ stCur.S_cur.E) \ batchDeletes U) \ D_reins
    stCur.S_cur.IsValid ∧
    stCur.S_cur.V = stCur.cs.RF.R ∧
    stCur.S_cur.E =
      (stCur.activeComps.biUnion fun C => (actB C).biUnion fun b => (stCur.dyn (C, b)).H.E) ∪
        (stCur.activeComps.biUnion fun C => stCur.extraEdges C) ∪
        stCur.cs.crossEdges ∧
    (coreGraph stCur.cs.G stCur.cs.lsf).IsSubgraph stCur.S_cur ∧
    stPrev.S_cur.BatchIsValid info.U_S ∧
    stCur.S_cur = stPrev.S_cur.applyBatch info.U_S ∧
    (U = [] → info.U_S = [] ∧ stCur.cost = stPrev.cost) ∧
    (∀ e ∈ stPrev.S_cur.E, e ∈ stCur.S_cur.E → (∀ u ∈ info.U_S, ¬ u.Inserts e) →
      e ∉ info.D_total ∧ ∀ u ∈ U, ¬ u.Inserts e) ∧
    info.U_S.length =
      (stPrev.S_cur.E \ keepSet).card + (stCur.cs.RF.R \ stPrev.cs.RF.R).card +
        (stCur.S_cur.E \ keepSet).card := by
  classical
  subst hactB
  set info := stepBundleTree sparsify stPrev U ord ord' with hinfo
  set stCur := info.state with hstCur
  have hcs_eq : stCur.cs = compLSFBatch stPrev.cs U := rfl
  have hI_cur : CompLSFInv C_lsst ℓ₀ stCur.cs := hcs_eq ▸ compLSFBatch_inv hI_prev hU
  have hG₀_cur : stCur.cs.G₀ = G₀ := by rw [hcs_eq, compLSFBatch_G₀, hG₀_eq]
  have hact_cur : stCur.activeComps = stPrev.activeComps ∪ info.newlyActive := rfl
  have hnew : info.newlyActive = touchedCompsBatch stPrev.cs U \ stPrev.activeComps := rfl
  have hAct_cur : stCur.activeComps ⊆ components G₀ := by
    intro C hC
    rw [hact_cur, hnew] at hC
    rcases Finset.mem_union.mp hC with h1 | h2
    · exact hAct_prev h1
    · have ht := Finset.mem_filter.mp (Finset.mem_sdiff.mp h2).1
      exact hG₀_eq ▸ ht.1
  have hAB : stCur.activeBuckets = stPrev.activeBuckets := rfl
  set actB := stPrev.activeBuckets with hactB
  set bunE : Finset ℕ := stCur.activeComps.biUnion fun C =>
    (actB C).biUnion fun b => (stCur.bun (C, b)).edges with hbunE
  set dynE : Finset ℕ := stCur.activeComps.biUnion fun C =>
    (actB C).biUnion fun b => (stCur.dyn (C, b)).H.E with hdynE
  set targetD : Finset ℕ := dynE ∪
      (stCur.activeComps.biUnion fun C =>
        ((stCur.cs.compSt C).G.E \ (stCur.cs.compSt C).RF.F.E) \ bunE) ∪
      stCur.cs.crossEdges with htargetD
  set targetF : Finset ℕ := dynE ∪ (stCur.activeComps.biUnion fun C => stCur.extraEdges C) ∪
      stCur.cs.crossEdges with htargetF
  -- The two forms of the target set agree.
  have hTgt_eq : targetD = targetF := by
    ext e
    simp only [htargetD, htargetF, Finset.mem_union, Finset.mem_biUnion]
    constructor
    · rintro ((hD | ⟨C, hCA, heX⟩) | hX)
      · exact Or.inl (Or.inl hD)
      · refine Or.inl (Or.inr ⟨C, hCA, ?_⟩)
        rw [Finset.mem_sdiff] at heX
        refine Finset.mem_sdiff.mpr ⟨heX.1, fun hB => heX.2 ?_⟩
        rw [Finset.mem_biUnion] at hB
        obtain ⟨b, hb, heb⟩ := hB
        exact Finset.mem_biUnion.mpr ⟨C, hCA, Finset.mem_biUnion.mpr ⟨b, hb, heb⟩⟩
      · exact Or.inr hX
    · rintro ((hD | ⟨C, hCA, heX⟩) | hX)
      · exact Or.inl (Or.inl hD)
      · by_cases hXe : e ∈ stCur.cs.crossEdges
        · exact Or.inr hXe
        refine Or.inl (Or.inr ⟨C, hCA, ?_⟩)
        unfold BundleTreeState.extraEdges at heX
        rw [hAB, Finset.mem_sdiff] at heX
        refine Finset.mem_sdiff.mpr ⟨heX.1, fun hB => heX.2 ?_⟩
        rw [hbunE, Finset.mem_biUnion] at hB
        obtain ⟨C', hC'A, hB'⟩ := hB
        rw [Finset.mem_biUnion] at hB'
        obtain ⟨b', hb', heb'⟩ := hB'
        have hC := hAct_cur hCA
        have hC' := hAct_cur hC'A
        have hroot := (hBun_core C' hC' b' hb' e heb').2
        have hCC' : C = C' := compLSF_comp_eq_of_root hI_cur (hG₀_cur ▸ hC) (hG₀_cur ▸ hC')
          (Finset.mem_sdiff.mp heX.1).1 hXe hroot
        subst hCC'
        exact Finset.mem_biUnion.mpr ⟨b', hb', heb'⟩
      · exact Or.inr hX
  -- The target set lies in the new core.
  have hTgt_sub : targetD ⊆ stCur.cs.G.E \ stCur.cs.RF.F.E := by
    intro e he
    simp only [htargetD, Finset.mem_union] at he
    rcases he with (heD | heEx) | heX
    · rw [hdynE, Finset.mem_biUnion] at heD
      obtain ⟨C, hCA, heB⟩ := heD
      rw [Finset.mem_biUnion] at heB
      obtain ⟨b, hb, heb⟩ := heB
      have hC := hAct_cur hCA
      exact (hBun_core C hC b hb e (hDyn_G_sub C hC b hb (hDyn_sub C hC b hb heb))).1
    · rw [Finset.mem_biUnion] at heEx
      obtain ⟨C, hCA, heExC⟩ := heEx
      have hC := hAct_cur hCA
      exact compLSF_comp_sdiff_sub hI_cur (hG₀_cur ▸ hC) (Finset.mem_sdiff.mp heExC).1
    · exact compLSF_crossEdges_sub hI_cur heX
  have hUS_eq : info.U_S = buildUSOrd (coreBatchOf stPrev.cs ord ord' U) U stCur.cs stPrev.S_cur
      targetD info.D_total := rfl
  have hS_next_eq : stCur.S_cur = stPrev.S_cur.applyBatch info.U_S := rfl
  have hUS_sp := buildUSOrd_spec hI_prev hU ρ σ hρ hσ hrot hS_val hS_V hS_sub
    (targetE := targetD) hTgt_sub info.D_total
  dsimp only at hUS_sp
  rw [← hcs_eq, ← hUS_eq, ← hS_next_eq] at hUS_sp
  obtain ⟨hBV, hVal, hV, hE, -, hSub, hLen, -⟩ := hUS_sp
  have hlen_US : info.U_S.length =
      (stPrev.S_cur.E \ (((stPrev.S_cur.E ∩ stCur.S_cur.E) \ batchDeletes U) \
        info.D_total)).card + (stCur.cs.RF.R \ stPrev.cs.RF.R).card +
        (stCur.S_cur.E \ (((stPrev.S_cur.E ∩ stCur.S_cur.E) \ batchDeletes U) \
          info.D_total)).card := by
    rw [hE]
    exact hLen
  have hNoReins : ∀ e ∈ stPrev.S_cur.E, e ∈ stCur.S_cur.E → (∀ u ∈ info.U_S, ¬ u.Inserts e) →
      e ∉ info.D_total ∧ ∀ u ∈ U, ¬ u.Inserts e := by
    intro e hePrev heCur hNoIns
    rw [hE] at heCur
    exact buildUSOrd_noReinsert hU hS_sub stCur.cs hePrev heCur (hUS_eq ▸ hNoIns)
  have hEmpty : U = [] → info.U_S = [] ∧ stCur.cost = stPrev.cost := by
    intro hUnil
    have htouch_nil : touchedCompsBatch stPrev.cs U = ∅ := by
      simp [touchedCompsBatch, hUnil, projCompBatchG]
    have hnew_nil : info.newlyActive = ∅ := by
      rw [hnew, htouch_nil, Finset.empty_sdiff]
    have hact_eq : stCur.activeComps = stPrev.activeComps := by
      rw [hact_cur, hnew_nil, Finset.union_empty]
    have hcs_nil : stCur.cs = stPrev.cs := by rw [hcs_eq, hUnil]; rfl
    have hdyn_E_nil : ∀ C ∈ components G₀, ∀ b : ℤ,
        (stCur.dyn (C, b)).H.E = (stPrev.dyn (C, b)).H.E := fun C hC b => by
      change (info.stepOut (C, b)).state.H.E = _
      rw [hDyn_nil hUnil C hC b]
    have hDs : info.D_total = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      change e ∈ (stCur.activeComps.biUnion fun C => (actB C).biUnion fun b =>
          (info.stepOut (C, b)).D) ∪
        (stCur.activeComps.biUnion fun C => (actB C).biUnion fun b =>
          (((stPrev.dyn (C, b)).H.E ∩ (info.stepOut (C, b)).state.G.E) \
            (info.stepOut (C, b)).state.H.E).biUnion
            fun e₀ => walkEdges (piTotal (info.stepOut (C, b)).state e₀)) at he
      simp only [Finset.mem_union, Finset.mem_biUnion] at he
      rcases he with ⟨C, hCA, b, _, heb⟩ | ⟨C, hCA, b, _, e₀, he₀, _⟩
      · rw [hDyn_nil hUnil C (hAct_cur hCA) b] at heb
        exact Finset.notMem_empty e heb
      · rw [hDyn_nil hUnil C (hAct_cur hCA) b] at he₀
        simp only [Finset.mem_sdiff, Finset.mem_inter] at he₀
        exact he₀.2 he₀.1.1
    have hTgt_nil : targetD = stPrev.S_cur.E := by
      rw [hTgt_eq, hS_E, htargetF, hdynE, hact_eq, hcs_nil]
      congr 1; congr 1
      · refine Finset.biUnion_congr rfl fun C hC => Finset.biUnion_congr rfl fun b _ => ?_
        exact hdyn_E_nil C (hAct_prev hC) b
      · refine Finset.biUnion_congr rfl fun C hC => ?_
        unfold BundleTreeState.extraEdges
        rw [hcs_nil, hAB]
        congr 1
        exact Finset.biUnion_congr rfl fun b hb => (hBun_nil hUnil C (hAct_prev hC) b hb).2
    have hUC_nil : restrictSplits (((stPrev.S_cur.E ∩ targetD) \ batchDeletes U) \ info.D_total)
        (coreBatchOf stPrev.cs ord ord' U) = [] := by
      apply restrictSplits_eq_nil
      rw [hUnil]
      exact coreBatchOf_nil_splitCount stPrev.cs ord ord'
    have hkeep_nil : ((stPrev.S_cur.E ∩ targetD) \ batchDeletes U) \ info.D_total =
        stPrev.S_cur.E := by
      rw [hTgt_nil, Finset.inter_self, hDs, Finset.sdiff_empty, hUnil]
      simp [batchDeletes]
    have hUS_nil : info.U_S = [] := by
      rw [hUS_eq]
      unfold buildUSOrd
      dsimp only
      rw [hUC_nil, hkeep_nil, hTgt_nil]
      simp
    have hCost_nil : stCur.cost = stPrev.cost := by
      have hbun_zero : (stCur.activeComps.sum fun C =>
          (stPrev.activeBuckets C).sum fun b => (info.U_B (C, b)).length) = 0 :=
        Finset.sum_eq_zero fun C hCA => Finset.sum_eq_zero fun b hb => by
          rw [(hBun_nil hUnil C (hAct_cur hCA) b hb).1]; rfl
      have hdynC_zero : (stCur.activeComps.sum fun C =>
          (stPrev.activeBuckets C).sum fun b => (info.stepOut (C, b)).cost) = 0 :=
        Finset.sum_eq_zero fun C hCA => Finset.sum_eq_zero fun b _ => by
          rw [hDyn_nil hUnil C (hAct_cur hCA) b]
      have hlazy_zero : info.newlyActive.sum (fun C => stPrev.lazyInitCost C) = 0 := by
        rw [hnew_nil, Finset.sum_empty]
      have hc := stepBundleTree_cost sparsify stPrev U ord ord'
      dsimp only at hc
      rw [← hinfo, ← hstCur] at hc
      rw [hc, hbun_zero, hdynC_zero, hlazy_zero, hUS_nil, hUnil]
      simp
    exact ⟨hUS_nil, hCost_nil⟩
  refine ⟨hVal, hV, ?_, hSub, hBV, hS_next_eq, hEmpty, hNoReins, hlen_US⟩
  rw [hE, hTgt_eq]

/-- A batch of the LSF loses at most as many forest edges as it adds roots. -/
theorem lsfBatch_forest_diff_le {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ (U : List Update) {S : LSFState}, LSFInvWith thresh K_σ ℓ₀ S → S.G.BatchIsValid U →
      S.R ⊆ (applyLSFBatch S U).R ∧ (applyLSFBatch S U).RF.F.E ⊆ S.RF.F.E ∧
      (S.RF.F.E \ (applyLSFBatch S U).RF.F.E).card ≤ ((applyLSFBatch S U).R \ S.R).card
  | [], S, _, _ => by simp [applyLSFBatch]
  | u :: rest, S, hI, ⟨hu, hrest⟩ => by
    have h1 := applyLSFUpdate_inv_with hI hu
    set S₁ := applyLSFUpdate S u
    have hR1 : S.R ⊆ S₁.R := h1.2.2.2.2.2.2.2.2.1
    have hF1 : S₁.RF.F.E ⊆ S.RF.F.E := h1.2.2.2.2.2.2.2.2.2.1
    have hc1 : (S.RF.F.E \ S₁.RF.F.E).card ≤ (S₁.R \ S.R).card :=
      lsf_forest_diff_le_R_diff (lsfInv_to_RS hI) (lsfInv_to_RS h1.1) h1.2.1 hu hR1 hF1
    have ih := lsfBatch_forest_diff_le rest h1.1 (h1.2.1 ▸ hrest)
    have hS2 : applyLSFBatch S (u :: rest) = applyLSFBatch S₁ rest := rfl
    rw [hS2]
    set S₂ := applyLSFBatch S₁ rest
    obtain ⟨hR2, hF2, hc2⟩ := ih
    refine ⟨hR1.trans hR2, hF2.trans hF1, ?_⟩
    have hsub : S.RF.F.E \ S₂.RF.F.E ⊆ (S.RF.F.E \ S₁.RF.F.E) ∪ (S₁.RF.F.E \ S₂.RF.F.E) := by
      intro e he
      rw [Finset.mem_sdiff] at he
      by_cases h : e ∈ S₁.RF.F.E
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h, he.2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he.1, h⟩)
    have hR_eq : (S₂.R \ S.R).card = (S₂.R \ S₁.R).card + (S₁.R \ S.R).card := by
      rw [Finset.card_sdiff_of_subset (hR1.trans hR2), Finset.card_sdiff_of_subset hR2,
        Finset.card_sdiff_of_subset hR1]
      have h12 := Finset.card_le_card hR2
      have h01 := Finset.card_le_card hR1
      omega
    calc (S.RF.F.E \ S₂.RF.F.E).card
        ≤ (S.RF.F.E \ S₁.RF.F.E).card + (S₁.RF.F.E \ S₂.RF.F.E).card :=
          (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      _ ≤ (S₁.R \ S.R).card + (S₂.R \ S₁.R).card := Nat.add_le_add hc1 hc2
      _ = (S₂.R \ S.R).card := by rw [hR_eq, Nat.add_comm]

/-- The non-forest edges of one component change by at most the effective projection weight and
the new roots: the new ones are new edges or old forest edges, and the lost ones are deleted
edges (a cross-insert `[insert e a a, delete e]` leaves `G_C.E` unchanged). -/
theorem compLSF_comp_core_diff_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ {U : List Update} {cs : CompLSFState} {C : Finset ℕ},
      CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U → C ∈ components cs.G₀ →
      let X := (cs.compSt C).G.E \ (cs.compSt C).RF.F.E
      let X' := ((compLSFBatch cs U).compSt C).G.E \ ((compLSFBatch cs U).compSt C).RF.F.E
      (X' \ X).card + (X \ X').card ≤
        projCompBatchWeight cs.G (cs.compSt C).G U +
          (((compLSFBatch cs U).compSt C).R \ (cs.compSt C).R).card := by
  intro U
  induction U with
  | nil =>
    intro cs C _ _ _
    simp [compLSFBatch, projCompBatchWeight]
  | cons u rest ih =>
    intro cs C hI ⟨hu, hrest⟩ hC
    have hcs1_I := compLSFInv_step hI hu
    have hBV1 := projCompUpdateG_valid hI hu hC
    have hB1 := applyLSFBatch_inv_with (projCompUpdateG cs.G (cs.compSt C).G u) (hI.hCompLSF C hC).1 hBV1
    set S := cs.compSt C
    set S₁ := (compLSFStepSingle cs u).compSt C
    set S₂ := (compLSFBatch cs (u :: rest)).compSt C
    set X := S.G.E \ S.RF.F.E
    set X₁ := S₁.G.E \ S₁.RF.F.E
    set X₂ := S₂.G.E \ S₂.RF.F.E
    have hS1G : S₁.G = S.G.applyBatch (projCompUpdateG cs.G S.G u) := hB1.2.1
    have h2 : (X₂ \ X₁).card + (X₁ \ X₂).card ≤
        projCompBatchWeight (cs.G.applyUpdate u)
          (S.G.applyBatch (projCompUpdateG cs.G S.G u)) rest + (S₂.R \ S₁.R).card := by
      have h := ih hcs1_I hrest hC
      dsimp only at h
      exact h.trans_eq (congrArg (· + (S₂.R \ S₁.R).card) (by
        change projCompBatchWeight (cs.G.applyUpdate u) S₁.G rest = _
        rw [hS1G]))
    have hR01 : S.R ⊆ S₁.R := hB1.2.2.2.2.2.2.2.2.1
    have hR12 : S₁.R ⊆ S₂.R := (compLSFBatch_compSt hcs1_I hrest hC).2.2.2.1
    have hR02 : S.R ⊆ S₂.R := hR01.trans hR12
    have hR_tel : (S₁.R \ S.R).card + (S₂.R \ S₁.R).card = (S₂.R \ S.R).card := by
      rw [Finset.card_sdiff_of_subset hR01, Finset.card_sdiff_of_subset hR12,
        Finset.card_sdiff_of_subset hR02]
      have c1 := Finset.card_le_card hR01
      have c2 := Finset.card_le_card hR12
      omega
    have h1_step : (X₁ \ X).card + (X \ X₁).card ≤
        projCompUpdateWeight cs.G S.G u + (S₁.R \ S.R).card := by
      have hfd := lsfBatch_forest_diff_le (projCompUpdateG cs.G S.G u) (hI.hCompLSF C hC).1 hBV1
      have hF' : S₁.RF.F.E ⊆ S.RF.F.E := hB1.2.2.2.2.2.2.2.2.2.1
      have h1sub : X₁ \ X ⊆ (S₁.G.E \ S.G.E) ∪ (S.RF.F.E \ S₁.RF.F.E) := fun e he => by
        simp only [X, X₁, Finset.mem_sdiff] at he
        by_cases heG : e ∈ S.G.E
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
            ⟨by by_contra hF; exact he.2 ⟨heG, hF⟩, he.1.2⟩)
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he.1.1, heG⟩)
      have h2sub : X \ X₁ ⊆ S.G.E \ S₁.G.E := fun e he => by
        simp only [X, X₁, Finset.mem_sdiff] at he
        exact Finset.mem_sdiff.mpr ⟨he.1.1, fun heG' => he.2 ⟨heG', fun hF => he.1.2 (hF' hF)⟩⟩
      have hc1 := (Finset.card_le_card h1sub).trans (Finset.card_union_le _ _)
      have hc2 := Finset.card_le_card h2sub
      have hc3 : (S.RF.F.E \ S₁.RF.F.E).card ≤ (S₁.R \ S.R).card := hfd.2.2
      by_cases hnil : projCompUpdateG cs.G S.G u = []
      · have hGE : S₁.G = S.G := by rw [hS1G, hnil]; rfl
        have hSym : (S₁.G.E \ S.G.E).card + (S.G.E \ S₁.G.E).card = 0 := by rw [hGE]; simp
        omega
      · have hw1 : projCompUpdateWeight cs.G S.G u = 1 := by
          unfold projCompUpdateWeight; simp [hnil]
        rw [hw1]
        by_cases hlen1 : (projCompUpdateG cs.G S.G u).length = 1
        · have hsym := symmDiff_applyBatch_card_le S.G (projCompUpdateG cs.G S.G u)
          rw [← hS1G, hlen1] at hsym
          omega
        · cases u with
          | delete e =>
            simp only [projCompUpdateG] at hnil hlen1
            split_ifs at hnil hlen1 <;> simp at hnil hlen1
          | split v v' Lt Lh =>
            simp only [projCompUpdateG] at hnil hlen1
            split_ifs at hnil hlen1 <;> simp at hnil hlen1
          | insert e a b =>
            have he_not : e ∉ S.G.E := fun heC => hu.1 (hI.hCE_sub C hC heC)
            have hGE : S₁.G.E = S.G.E := by
              change (applyLSFBatch S (projCompUpdateG cs.G S.G (.insert e a b))).G.E = S.G.E
              simp only [projCompUpdateG] at hnil hlen1 ⊢
              split_ifs at hnil hlen1 ⊢ with hab ha hb
              · simp at hlen1
              · exact (applyLSFBatch_insert_delete_selfLoop (hI.hCompLSF C hC).1 he_not ha).2.2.1
              · exact (applyLSFBatch_insert_delete_selfLoop (hI.hCompLSF C hC).1 he_not hb).2.2.1
              · simp at hnil
            rw [hGE, Finset.sdiff_self, Finset.card_empty] at hc1 hc2
            omega
    have htri1 : X₂ \ X ⊆ (X₂ \ X₁) ∪ (X₁ \ X) := fun e he => by
      rw [Finset.mem_sdiff] at he
      by_cases h1 : e ∈ X₁
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h1, he.2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he.1, h1⟩)
    have htri2 : X \ X₂ ⊆ (X \ X₁) ∪ (X₁ \ X₂) := fun e he => by
      rw [Finset.mem_sdiff] at he
      by_cases h1 : e ∈ X₁
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h1, he.2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he.1, h1⟩)
    have ht1 := (Finset.card_le_card htri1).trans (Finset.card_union_le _ _)
    have ht2 := (Finset.card_le_card htri2).trans (Finset.card_union_le _ _)
    dsimp only [projCompBatchWeight]
    change (X₂ \ X).card + (X \ X₂).card ≤ _
    omega

/-- The length of the output batch of one step, in the form used for the recourse bound (the
analogue of `stepTreeCoreAux_US_lenWith`). The bundles of each bucket only lose edges, and only
edges the input batch deletes (`hBunE`). The extra edges of an inactive component are empty
(`hUnt`). -/
theorem stepBundleTree_US_len {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {G₀ : MGraph}
    (stPrev : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (actB : Finset ℕ → Finset ℤ)
    (hactB : stPrev.activeBuckets = actB)
    (hG₀_eq : stPrev.cs.G₀ = G₀)
    (hI_prev : CompLSFInv C_lsst ℓ₀ stPrev.cs)
    (hAct_prev : stPrev.activeComps ⊆ components G₀)
    (hUnt : ∀ C ∈ components G₀, C ∉ stPrev.activeComps → stPrev.extraEdges C = ∅)
    (hU : stPrev.cs.G.BatchIsValid U)
    (hS_E_prev : stPrev.S_cur.E =
      (stPrev.activeComps.biUnion fun C => (actB C).biUnion fun b => (stPrev.dyn (C, b)).H.E) ∪
        (stPrev.activeComps.biUnion fun C => stPrev.extraEdges C) ∪
        stPrev.cs.crossEdges)
    (hS_E_cur : (stepBundleTree sparsify stPrev U ord ord').state.S_cur.E =
      ((stepBundleTree sparsify stPrev U ord ord').state.activeComps.biUnion fun C =>
        (actB C).biUnion fun b => ((stepBundleTree sparsify stPrev U ord ord').state.dyn (C, b)).H.E) ∪
        ((stepBundleTree sparsify stPrev U ord ord').state.activeComps.biUnion fun C =>
          (stepBundleTree sparsify stPrev U ord ord').state.extraEdges C) ∪
        (stepBundleTree sparsify stPrev U ord ord').state.cs.crossEdges)
    (hUS_card : (stepBundleTree sparsify stPrev U ord ord').U_S.length =
      (stPrev.S_cur.E \ (((stPrev.S_cur.E ∩ (stepBundleTree sparsify stPrev U ord ord').state.S_cur.E) \
        batchDeletes U) \ (stepBundleTree sparsify stPrev U ord ord').D_total)).card +
      ((stepBundleTree sparsify stPrev U ord ord').state.cs.RF.R \ stPrev.cs.RF.R).card +
      ((stepBundleTree sparsify stPrev U ord ord').state.S_cur.E \
        (((stPrev.S_cur.E ∩ (stepBundleTree sparsify stPrev U ord ord').state.S_cur.E) \
          batchDeletes U) \ (stepBundleTree sparsify stPrev U ord ord').D_total)).card)
    (hDyn_UH : ∀ C ∈ (stepBundleTree sparsify stPrev U ord ord').state.activeComps, ∀ b ∈ actB C,
      (stPrev.dyn (C, b)).H.applyBatch ((stepBundleTree sparsify stPrev U ord ord').stepOut (C, b)).UH =
        ((stepBundleTree sparsify stPrev U ord ord').state.dyn (C, b)).H)
    (hBunE : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      ((stepBundleTree sparsify stPrev U ord ord').state.bun (C, b)).edges ⊆
          (stPrev.bun (C, b)).edges ∧
        (stPrev.bun (C, b)).edges \ ((stepBundleTree sparsify stPrev U ord ord').state.bun (C, b)).edges ⊆
          batchDeletes U) :
    let info := stepBundleTree sparsify stPrev U ord ord'
    let stCur := info.state
    info.U_S.length ≤
      (stCur.activeComps.sum fun C => (actB C).sum fun b => (info.stepOut (C, b)).UH.length) +
      (info.newlyActive.sum fun C => (actB C).sum fun b => (stPrev.dyn (C, b)).H.E.card) +
      7 * U.length +
      2 * (stCur.cs.RF.R \ stPrev.cs.RF.R).card +
      2 * info.D_total.card := by
  classical
  subst hactB
  set info := stepBundleTree sparsify stPrev U ord ord'
  set stCur := info.state
  set actB := stPrev.activeBuckets
  set D_reins : Finset ℕ := info.D_total
  set bd := batchDeletes U
  set keepSet := ((stPrev.S_cur.E ∩ stCur.S_cur.E) \ bd) \ D_reins
  have hcs_eq : stCur.cs = compLSFBatch stPrev.cs U := rfl
  have hI_cur : CompLSFInv C_lsst ℓ₀ stCur.cs := hcs_eq ▸ compLSFBatch_inv hI_prev hU
  have hAB : stCur.activeBuckets = actB := rfl
  have hact_cur : stCur.activeComps = stPrev.activeComps ∪ info.newlyActive := rfl
  have hAct_cur : stCur.activeComps ⊆ components G₀ := by
    intro C hC
    rw [hact_cur] at hC
    rcases Finset.mem_union.mp hC with h1 | h2
    · exact hAct_prev h1
    · have ht := Finset.mem_filter.mp (Finset.mem_sdiff.mp h2).1
      exact hG₀_eq ▸ ht.1
  have hprev_act_sub_cur : stPrev.activeComps ⊆ stCur.activeComps := by
    intro C hC; rw [hact_cur]; exact Finset.mem_union_left _ hC
  -- The core edges of a component, before and after.
  let X : Finset ℕ → Finset ℕ := fun C => (stPrev.cs.compSt C).G.E \ (stPrev.cs.compSt C).RF.F.E
  let X' : Finset ℕ → Finset ℕ := fun C => (stCur.cs.compSt C).G.E \ (stCur.cs.compSt C).RF.F.E
  let B : Finset ℕ → Finset ℕ := fun C => (actB C).biUnion fun b => (stPrev.bun (C, b)).edges
  let B' : Finset ℕ → Finset ℕ := fun C => (actB C).biUnion fun b => (stCur.bun (C, b)).edges
  have hex_prev : ∀ C, stPrev.extraEdges C = X C \ B C := fun C => rfl
  have hex_cur : ∀ C, stCur.extraEdges C = X' C \ B' C := fun C => rfl
  have hB'_sub : ∀ C ∈ components G₀, B' C ⊆ B C := by
    intro C hC e he
    simp only [B', Finset.mem_biUnion] at he
    obtain ⟨b, hb, heb⟩ := he
    exact Finset.mem_biUnion.mpr ⟨b, hb, (hBunE C hC b hb).1 heb⟩
  have hB_del : ∀ C ∈ components G₀, B C \ B' C ⊆ bd := by
    intro C hC e he
    rw [Finset.mem_sdiff] at he
    simp only [B, Finset.mem_biUnion] at he
    obtain ⟨⟨b, hb, heb⟩, hnB'⟩ := he
    exact (hBunE C hC b hb).2 (Finset.mem_sdiff.mpr ⟨heb, fun h' =>
      hnB' (Finset.mem_biUnion.mpr ⟨b, hb, h'⟩)⟩)
  have hdel_sub : stPrev.S_cur.E \ keepSet ⊆
      (stPrev.S_cur.E \ stCur.S_cur.E) ∪ bd ∪ D_reins := by
    intro e he
    rw [Finset.mem_sdiff] at he
    by_cases hD : e ∈ D_reins
    · exact Finset.mem_union_right _ hD
    · refine Finset.mem_union_left _ ?_
      by_cases hc : e ∈ stCur.S_cur.E
      · refine Finset.mem_union_right _ ?_
        by_contra hnot
        exact he.2 (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨he.1, hc⟩, hnot⟩, hD⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he.1, hc⟩)
  have hins_sub : stCur.S_cur.E \ keepSet ⊆
      ((stCur.S_cur.E \ stPrev.S_cur.E) \ bd) ∪ bd ∪ D_reins := by
    intro e he
    rw [Finset.mem_sdiff] at he
    by_cases hD : e ∈ D_reins
    · exact Finset.mem_union_right _ hD
    · refine Finset.mem_union_left _ ?_
      by_cases hbd : e ∈ bd
      · exact Finset.mem_union_right _ hbd
      refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨?_, hbd⟩)
      by_cases hp : e ∈ stPrev.S_cur.E
      · exfalso
        exact he.2 (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hp, he.1⟩, hbd⟩, hD⟩)
      · exact Finset.mem_sdiff.mpr ⟨he.1, hp⟩
  have hprev_cur : stPrev.S_cur.E \ stCur.S_cur.E ⊆
      (stCur.activeComps.biUnion fun C => (actB C).biUnion fun b =>
        (stPrev.dyn (C, b)).H.E \ (stCur.dyn (C, b)).H.E) ∪
      ((components G₀).biUnion fun C => X C \ X' C) ∪ bd := by
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
      have hC := hAct_prev hCA
      rw [hex_prev, Finset.mem_sdiff] at heExC
      refine Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_sdiff.mpr ⟨heExC.1, fun hX' => ?_⟩⟩
      refine he.2 (Or.inl (Or.inr (Finset.mem_biUnion.mpr ⟨C, hprev_act_sub_cur hCA, ?_⟩)))
      rw [hex_cur]
      exact Finset.mem_sdiff.mpr ⟨hX', fun hB' => heExC.2 (hB'_sub C hC hB')⟩
    · right
      exact compLSF_crossEdges_sdiff_prev stPrev.cs U (Finset.mem_sdiff.mpr ⟨heX, fun h =>
        he.2 (Or.inr h)⟩)
  have hcur_prev : (stCur.S_cur.E \ stPrev.S_cur.E) \ bd ⊆
      ((stCur.activeComps.biUnion fun C => (actB C).biUnion fun b =>
        (stCur.dyn (C, b)).H.E \ (stPrev.dyn (C, b)).H.E) ∪
       (info.newlyActive.biUnion fun C => (actB C).biUnion fun b =>
        (stPrev.dyn (C, b)).H.E)) ∪
      ((components G₀).biUnion fun C => X' C \ X C) ∪
      (stCur.cs.crossEdges \ stPrev.cs.crossEdges) := by
    intro e he'
    rw [Finset.mem_sdiff] at he'
    have he := he'.1
    have hnbd := he'.2
    rw [hS_E_prev, hS_E_cur] at he
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
          rw [hact_cur] at hCA
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
      have hC := hAct_cur hCA
      rw [hex_cur, Finset.mem_sdiff] at heExC
      have hnEx : e ∉ stPrev.extraEdges C := by
        by_cases hCP : C ∈ stPrev.activeComps
        · exact fun h => he.2 (Or.inl (Or.inr (Finset.mem_biUnion.mpr ⟨C, hCP, h⟩)))
        · rw [hUnt C hC hCP]; exact Finset.notMem_empty e
      refine Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_sdiff.mpr ⟨heExC.1, fun hX => ?_⟩⟩
      by_cases hB : e ∈ B C
      · exact hnbd (hB_del C hC (Finset.mem_sdiff.mpr ⟨hB, heExC.2⟩))
      · exact hnEx (by rw [hex_prev]; exact Finset.mem_sdiff.mpr ⟨hX, hB⟩)
    · right; exact ⟨heX, fun h => he.2 (Or.inr h)⟩
  have hUH_symm : ∀ C ∈ stCur.activeComps, ∀ b ∈ actB C,
      ((stPrev.dyn (C, b)).H.E \ (stCur.dyn (C, b)).H.E).card +
        ((stCur.dyn (C, b)).H.E \ (stPrev.dyn (C, b)).H.E).card ≤
          (info.stepOut (C, b)).UH.length :=
    fun C hC b hb => symmDiff_applyBatch_UH (hDyn_UH C hC b hb)
  have hX_diff : ∀ C ∈ components G₀, (X' C \ X C).card + (X C \ X' C).card ≤
      projCompBatchWeight stPrev.cs.G (stPrev.cs.compSt C).G U +
        ((stCur.cs.compSt C).R \ (stPrev.cs.compSt C).R).card :=
    fun C hC => compLSF_comp_core_diff_le hI_prev hU (hG₀_eq ▸ hC)
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
  have hXsum : ((components G₀).sum fun C => (X' C \ X C).card) +
      ((components G₀).sum fun C => (X C \ X' C).card) ≤
      2 * U.length + (stCur.cs.RF.R \ stPrev.cs.RF.R).card := by
    rw [← Finset.sum_add_distrib, ← hsum_R]
    refine le_trans (Finset.sum_le_sum hX_diff) ?_
    rw [Finset.sum_add_distrib]
    omega
  have hdel_le : bd.card ≤ U.length := batchDeletes_card_le U
  have hcross_le : (stCur.cs.crossEdges \ stPrev.cs.crossEdges).card ≤ U.length := by
    rw [hcs_eq]; exact compLSF_crossEdges_sdiff_cur U stPrev.cs
  have hbi_card_le : ∀ (S : Finset (Finset ℕ)) (f : Finset ℕ → ℤ → Finset ℕ),
      (S.biUnion fun C => (actB C).biUnion fun b => f C b).card ≤
        S.sum fun C => (actB C).sum fun b => (f C b).card := fun S f =>
    le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
  have hc1 : (stPrev.S_cur.E \ keepSet).card ≤
      (stCur.activeComps.sum fun C => (actB C).sum fun b =>
        ((stPrev.dyn (C, b)).H.E \ (stCur.dyn (C, b)).H.E).card) +
      ((components G₀).sum fun C => (X C \ X' C).card) + bd.card + D_reins.card := by
    have hsub : stPrev.S_cur.E \ keepSet ⊆
        (stCur.activeComps.biUnion fun C => (actB C).biUnion fun b =>
          (stPrev.dyn (C, b)).H.E \ (stCur.dyn (C, b)).H.E) ∪
        ((components G₀).biUnion fun C => X C \ X' C) ∪ bd ∪ D_reins := fun e he => by
      rcases Finset.mem_union.mp (hdel_sub he) with h12 | h3
      · rcases Finset.mem_union.mp h12 with h1 | h2
        · exact Finset.mem_union_left _ (hprev_cur h1)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h2)
      · exact Finset.mem_union_right _ h3
    have hpc := le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _)
      (Nat.add_le_add_right (le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
    have h1 := hbi_card_le stCur.activeComps
      (fun C b => (stPrev.dyn (C, b)).H.E \ (stCur.dyn (C, b)).H.E)
    have h2 := (Finset.card_biUnion_le (s := components G₀) (t := fun C => X C \ X' C))
    exact le_trans hpc (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add h1 h2) _) _)
  have hc2 : (stCur.S_cur.E \ keepSet).card ≤
      (stCur.activeComps.sum fun C => (actB C).sum fun b =>
        ((stCur.dyn (C, b)).H.E \ (stPrev.dyn (C, b)).H.E).card) +
      (info.newlyActive.sum fun C => (actB C).sum fun b => (stPrev.dyn (C, b)).H.E.card) +
      ((components G₀).sum fun C => (X' C \ X C).card) +
      (stCur.cs.crossEdges \ stPrev.cs.crossEdges).card + bd.card + D_reins.card := by
    have hins_c := le_trans (Finset.card_le_card hins_sub)
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    have hcp1 := le_trans (Finset.card_le_card hcur_prev) (Finset.card_union_le _ _)
    have h1 := hbi_card_le stCur.activeComps
      (fun C b => (stCur.dyn (C, b)).H.E \ (stPrev.dyn (C, b)).H.E)
    have h1n := hbi_card_le info.newlyActive (fun C b => (stPrev.dyn (C, b)).H.E)
    have h2 := (Finset.card_biUnion_le (s := components G₀) (t := fun C => X' C \ X C))
    refine le_trans hins_c ?_
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right hcp1 _) _) ?_
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _) ?_
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
  dsimp only
  rw [hUS_card]
  change (stPrev.S_cur.E \ keepSet).card + (stCur.cs.RF.R \ stPrev.cs.RF.R).card +
      (stCur.S_cur.E \ keepSet).card ≤
    (stCur.activeComps.sum fun C => (actB C).sum fun b => (info.stepOut (C, b)).UH.length) +
    (info.newlyActive.sum fun C => (actB C).sum fun b => (stPrev.dyn (C, b)).H.E.card) +
    7 * U.length + 2 * (stCur.cs.RF.R \ stPrev.cs.RF.R).card + 2 * D_reins.card
  omega

end MinCostFlow.SparseCore
