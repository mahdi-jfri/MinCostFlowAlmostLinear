module

public import MinCostFlow.Chain.SparseCoreRestart
import MinCostFlow.SparseCore.Lemma517
import MinCostFlow.DynSpanner.StepTransition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bucket batches between restarts

`epochTreeSeq_dyn_spec`: over a stretch of steps with no restart of branch `j`, each bucket
instance receives valid batches of deletions and splits only. Split out of
`SparseCoreRestart.lean` to keep files short.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.LSF

/-- Any bucket batch list over a non-restarted suffix `[s₀, t]` is `Hb.BatchIsValid` and
consists strictly of deletions and splits, matching `DynSpanner.runBatchState` and
`DynSpanner.runBatchStepOut` from `Hb := restartBucketGraph (st 0) C b` without `hThresh`. -/
lemma epochTreeSeq_dyn_spec
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (_hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (s₀ t j : ℕ) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀_rest : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r) :
    let G₀ := D.G 0
    let cs₀ := initCompLSF oracle C_lsst G₀ (D.ℓ 0) k j
    let ts₀ := fun C => initTildeState (cs₀.compSt C)
    let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) * (G₀.maxDeg + 1) +
      Nat.ceil (56 * (M : ℝ) / (k : ℝ))
    let st := epochTreeSeq oracle C_lsst L sparsify k M N D restarts s₀ t j
    let Hb := fun C b => restartBucketGraph (st 0) C b
    let Us_ep : Finset ℕ → ℤ → List (List Update) := fun C b =>
      (List.range (t - s₀)).map fun r => (stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)
    ∀ C ∈ components G₀, ∀ b : ℤ,
      (Hb C b).IsValid ∧ (Hb C b).m ≤ G₀.m ∧ (Hb C b).n ≤ 2 * (Hb C b).m ∧
      (Hb C b).maxDeg ≤ (ts₀ C).C.maxDeg ∧
      (Hb C b).BatchIsValid (Us_ep C b).flatten ∧
      (∀ op ∈ (Us_ep C b).flatten, isDelOrSplit op) ∧
      (st 0).dyn (C, b) = (DynSpanner.init (Hb C b) L (phaseBase ((Hb C b).n + splitB) L)
        (sparsify M)).state ∧
      (∀ δ ≤ t - s₀,
        (st δ).dyn (C, b) = DynSpanner.runBatchState (L := L) (Hb C b)
          (phaseBase ((Hb C b).n + splitB) L) (sparsify M) (Us_ep C b) δ ∧
        ((st δ).dyn (C, b)).G.IsValid ∧
        ((st δ).dyn (C, b)).G.IsSubgraph ((st δ).dyn (C, b)).H ∧
        ((st δ).dyn (C, b)).G.E = ((st δ).ts C).C.E.filter (fun e => (st δ).origBucket e = b) ∧
        ((st δ).ts C).C.IsSubgraph ((st δ).dyn (C, b)).G) ∧
      (∀ δ < t - s₀,
        (stepTreeCoreAux sparsify (st δ) (D.U (s₀ + δ + 1))).stepOut (C, b) =
          DynSpanner.runBatchStepOut (L := L) (Hb C b) (phaseBase ((Hb C b).n + splitB) L)
            (sparsify M) (Us_ep C b) δ ∧
        ((st δ).dyn (C, b)).G.BatchIsValid
          ((stepTreeCoreAux sparsify (st δ) (D.U (s₀ + δ + 1))).U_b (C, b)) ∧
        ((stepTreeCoreAux sparsify (st δ) (D.U (s₀ + δ + 1))).U_b (C, b)).length ≤
          ((stepTreeCoreAux sparsify (st δ) (D.U (s₀ + δ + 1))).U_C C).length) := by
  intro G₀ cs₀ ts₀ splitB st Hb Us_ep C hC b
  let T := sparseCoreRestartTool oracle C_lsst L sparsify
  obtain ⟨hBase, hStep, _⟩ := treeRunSeq_tilde_core_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD j
  obtain ⟨hSt_base, hSt_step⟩ := epochTreeSeq_steps oracle C_lsst L sparsify
    k M N D restarts hV₀ s₀ t j hst hNoRest
  have hne : ∀ s, (T.runAfterRestarts k M N D restarts s).isNonempty = true := fun s =>
    (runAfterRestarts_isNonempty oracle C_lsst L sparsify k M N D restarts s).2.1.trans
      (decide_eq_true hV₀)
  have hSt0_ne : ¬ (s₀ = t ∧ s₀ < t) := fun h => absurd h.1 (ne_of_lt h.2)
  have hst0_eq : st 0 = (T.runAfterRestarts k M N D restarts s₀).trees j := by
    dsimp only [st, epochTreeSeq, T]
    rw [Nat.add_zero]
    simp only [hSt0_ne, ↓reduceIte]
  have hb_s0 := hBase s₀ (le_trans hst htτ)
  have hb_0 := hBase 0 (Nat.zero_le τ)
  have hcov₀ := initLSF_cov0 (j := j) oracle C_lsst hk hG₀ hℓ₀ hC hLSST
  have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hT_0 : TildeInv (cs₀.compSt C) ((st 0).cs.compSt C) ((st 0).ts C) := by
    rw [(hSt_base 0 (Nat.zero_le _)).cs, (hSt_base 0 (Nat.zero_le _)).ts, Nat.add_zero]
    exact (hb_s0.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.1
  have hTs_sub0 : ((st 0).ts C).C.E ⊆ (ts₀ C).C.E := by
    rw [(hSt_base 0 (Nat.zero_le _)).ts, Nat.add_zero]
    exact (hb_s0.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.1
  have hOB_0 : (st 0).origBucket = fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ (D.ℓ 0)) e) := by
    rw [(hSt_base 0 (Nat.zero_le _)).origBucket, Nat.add_zero]
    exact hb_s0.2.2.2.2.1
  have hHb_sp := activeSubgraph_rawBucket_spec hT_0.hC_val (st 0).origBucket b
  have hHb_val : (Hb C b).IsValid := hHb_sp.1
  have hmc : (cs₀.compSt C).G.m ≤ G₀.m := by
    rw [(initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC).2.1]
    exact compGraph_m_le
  have hHb_m : (Hb C b).m ≤ G₀.m := by
    have hE_sub : (Hb C b).E ⊆ (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).E := by
      intro e he
      dsimp only [Hb, restartBucketGraph] at he
      rw [hHb_sp.2.2.1, Finset.mem_filter] at he
      rw [initBucketGraph, rawBucket]
      dsimp only [activeSubgraph]
      rw [Finset.mem_filter]
      refine ⟨hTs_sub0 he.1, ?_⟩
      dsimp only [cs₀]
      rw [← initCompLSF_origBucket_congr oracle hLSST hG₀ hV₀ hℓ₀ hk j hC e (hTs_sub0 he.1),
        ← initCompLSF_safeLen_origBucket_eq oracle C_lsst hk hG₀ hV₀ hℓ₀ hC hLSST (hTs_sub0 he.1)]
      exact (congrFun hOB_0 e).symm ▸ he.2
    have h1 : (Hb C b).m ≤ (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).m :=
      Finset.card_le_card hE_sub
    have h2 : (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).m ≤ (cs₀.compSt C).G.m :=
      (initBucketGraph_spec (hI₀.hCompLSF C hC).1 hcov₀ b).2.2.2.2.2.2.2.1
    exact le_trans (le_trans h1 h2) hmc
  have hHb_mM : (Hb C b).m ≤ M := le_trans hHb_m hM
  have htilde_step : ∀ (tr : TreeCoreState L) (s : ℕ) (hs : s < τ),
      tr.cs = (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.cs →
      tr.ts = (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.ts →
      let info := stepTreeCoreAux sparsify tr (D.U (s + 1))
      ((tr.ts C).C.BatchIsValid (info.U_C C) ∧
       ((tildeStepBatch (tr.cs.compSt C) (tr.ts C)
          (projCompBatchG tr.cs.G (tr.cs.compSt C).G (D.U (s + 1)))).2.1.C =
          (tr.ts C).C.applyBatch (info.U_C C)) ∧
       (∀ op ∈ info.U_C C, isDelOrSplit op)) := by
    intro tr s hs hcs_tr hts_tr info
    have hbs := hBase s (Nat.le_of_lt hs)
    have hStep_s := hStep s hs
    have hG₀_s : tr.cs.G₀ = G₀ := by
      rw [hcs_tr, hbs.2.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
    have hcs_sp := compLSFBatch_compSt (hcs_tr ▸ hbs.2.2.2.2.2.2.2.2.1)
      (hcs_tr ▸ hStep_s.1) (hG₀_s ▸ hC)
    have hT_tr : TildeInv (cs₀.compSt C) (tr.cs.compSt C) (tr.ts C) := by
      rw [hcs_tr, hts_tr]; exact (hbs.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.1
    have htd := tildeStepBatch_spec (hI₀.hCompLSF C hC).1 hcov₀
      ((hcs_tr ▸ hbs.2.2.2.2.2.2.2.2.1).hCompLSF C (hG₀_s ▸ hC)).1
      (by rw [hcs_tr]; exact (hbs.2.2.2.2.2.2.2.2.2.2.2.2 C hC).1)
      hT_tr hcs_sp.2.2.1
    have hUC_def : info.U_C C =
        (tildeStepBatch (tr.cs.compSt C) (tr.ts C)
          (projCompBatchG tr.cs.G (tr.cs.compSt C).G (D.U (s + 1)))).1 := rfl
    have hds_tr : ∀ op ∈ info.U_C C, isDelOrSplit op := by
      have hU_C_eq : info.U_C C =
          (stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
            (D.U (s + 1))).U_C C := by
        dsimp only [info, stepTreeCoreAux, stepTreeCoreAuxWith]; rw [hcs_tr, hts_tr]
      rw [hU_C_eq]
      exact (hStep_s.2.2.2 C hC).2.1
    refine ⟨?_, ?_, hds_tr⟩
    · rw [hUC_def]; exact htd.2.2.2.2.2.1
    · rw [hUC_def]; exact htd.2.2.2.2.2.2.1
  have hts_deg : ((st 0).ts C).C.maxDeg ≤ (ts₀ C).C.maxDeg := by
    have hle_ts : ∀ r ≤ τ, (((treeRunSeq oracle C_lsst L sparsify k M N D j r).1.ts C).C).maxDeg ≤
        (ts₀ C).C.maxDeg := fun r hr => by
      induction r with
      | zero => exact le_rfl
      | succ s ih =>
        have hs_lt : s < τ := hr
        have hbs := hBase s (Nat.le_of_lt hs_lt)
        have htd_s := htilde_step (treeRunSeq oracle C_lsst L sparsify k M N D j s).1 s hs_lt rfl rfl
        have hts_eq : ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.ts C).C =
            ((treeRunSeq oracle C_lsst L sparsify k M N D j s).1.ts C).C.applyBatch
              ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
                (D.U (s + 1))).U_C C) := htd_s.2.1
        have happly_deg : ∀ (G : MGraph) (U : List Update), G.IsValid → G.BatchIsValid U →
            (∀ op ∈ U, isDelOrSplit op) → (G.applyBatch U).maxDeg ≤ G.maxDeg := by
          intro G U hGV hBV hds
          induction U generalizing G with
          | nil => exact le_rfl
          | cons u rest ihu =>
            rw [MGraph.BatchIsValid] at hBV
            have h1 := maxDeg_applyUpdate_le hGV hBV.1 (hds u List.mem_cons_self)
            have h2 := ihu (G.applyUpdate u) (applyUpdate_isValid hGV hBV.1) hBV.2
              (fun op hop => hds op (List.mem_cons_of_mem u hop))
            exact le_trans h2 h1
        rw [hts_eq]
        exact le_trans (happly_deg _ _ (hbs.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.1.hC_val htd_s.1
          htd_s.2.2) (ih (Nat.le_of_lt hr))
    rw [(hSt_base 0 (Nat.zero_le _)).ts, Nat.add_zero]
    exact hle_ts s₀ (le_trans hst htτ)
  have hHb_deg : (Hb C b).maxDeg ≤ (ts₀ C).C.maxDeg := le_trans hHb_sp.2.2.2.2 hts_deg
  have hInit_dyn0 : (st 0).dyn (C, b) = (DynSpanner.init (Hb C b) L
      (phaseBase ((Hb C b).n + splitB) L) (sparsify M)).state := by
    have hspB : (st 0).splitBound = splitB := by
      rw [(hSt_base 0 (Nat.zero_le _)).splitBound, Nat.add_zero]
      exact hb_s0.2.2.2.1
    have hm₀_eq : (st 0).m₀ = M := by
      rw [(hSt_base 0 (Nat.zero_le _)).m₀, Nat.add_zero]
      exact hb_s0.1
    have hHb0_eq : ∀ tr0 : TreeCoreState L,
        tr0.ts C = ts₀ C →
        tr0.origBucket = (fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ (D.ℓ 0)) e)) →
        restartBucketGraph tr0 C b = initBucketGraph (cs₀.compSt C) (D.ℓ 0) b := by
      intro tr0 hts0 hob0
      dsimp only [restartBucketGraph, initBucketGraph]
      rw [hts0, hob0]
      congr 1
      dsimp only [rawBucket]
      congr 1
      refine Finset.filter_congr fun e he => ?_
      rw [initCompLSF_safeLen_origBucket_eq oracle C_lsst hk hG₀ hV₀ hℓ₀ hC hLSST he,
        initCompLSF_origBucket_congr oracle hLSST hG₀ hV₀ hℓ₀ hk j hC e he]
    by_cases hC_act : C ∈ (st 0).activeComps
    · rcases hs₀_rest with rfl | hj_rest
      · by_cases hj0 : j ∈ restarts 0
        · have hst0_fold : st 0 =
              ((restarts 0).foldl (sparseCoreRestartTool oracle C_lsst L sparsify).restart
                ((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate k M N D restarts 0).1).trees j :=
            hst0_eq
          have hf := foldl_restart_dyn_active oracle C_lsst L sparsify (restarts 0)
            ((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate k M N D restarts 0).1 j (C := C) (b := b)
            ((runAfterRestarts_isNonempty oracle C_lsst L sparsify k M N D restarts 0).1.trans
              (decide_eq_true hV₀))
            (by
              have hb_pre := (foldl_restart_props oracle C_lsst L sparsify
                ((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate k M N D restarts 0).1 (restarts 0)).2.2.2.1 j
              rw [hst0_fold] at hC_act
              rwa [← hb_pre.activeComps])
            hj0
          have hpre0_spB : (((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate k M N D restarts 0).1.trees j).splitBound = splitB :=
            (runAfterRestarts_base_proj oracle C_lsst L sparsify k M N D restarts hV₀ j 0).1.splitBound
          have hpre0_m0 : (((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate k M N D restarts 0).1.trees j).m₀ = M :=
            (runAfterRestarts_base_proj oracle C_lsst L sparsify k M N D restarts hV₀ j 0).1.m₀
          have hrb : restartBucketGraph
              (((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate k M N D restarts 0).1.trees j) C b =
              Hb C b :=
            hf.1.symm.trans (by dsimp only [Hb]; rw [hst0_fold])
          have hf2 := hf.2
          rw [← hst0_fold, hrb, hpre0_spB, hpre0_m0] at hf2
          exact hf2
        · have hpre0_eq : (T.runAfterUpdate k M N D restarts 0).1.trees j =
              initTreeCore oracle C_lsst L sparsify k M N G₀ (D.ℓ 0) j := by
            dsimp only [T, SparseCoreRestartTool.runAfterUpdate]
            exact sparseCoreRestartTool_init_trees oracle C_lsst L sparsify k M N G₀ (D.ℓ 0) (D.g 0) j
          have hpost0 : (T.runAfterRestarts k M N D restarts 0).trees j =
              (T.runAfterUpdate k M N D restarts 0).1.trees j :=
            (foldl_restart_props oracle C_lsst L sparsify
              (T.runAfterUpdate k M N D restarts 0).1 (restarts 0)).2.2.2.2 j hj0
          rw [hst0_eq, hpost0, hpre0_eq]
          have hHb_eq : Hb C b = initBucketGraph (cs₀.compSt C) (D.ℓ 0) b := by
            dsimp only [Hb]
            exact hHb0_eq (st 0) (by rw [hst0_eq, hpost0, hpre0_eq]; rfl)
              (by rw [hst0_eq, hpost0, hpre0_eq]; rfl)
          rw [hHb_eq]
          rfl
      · have hst0_fold : st 0 =
            ((restarts s₀).foldl (sparseCoreRestartTool oracle C_lsst L sparsify).restart
              ((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate k M N D restarts s₀).1).trees j :=
          hst0_eq
        have hf := foldl_restart_dyn_active oracle C_lsst L sparsify (restarts s₀)
          ((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate k M N D restarts s₀).1 j (C := C) (b := b)
          ((runAfterRestarts_isNonempty oracle C_lsst L sparsify k M N D restarts s₀).1.trans
            (decide_eq_true hV₀))
          (by
            have hb_pre := (foldl_restart_props oracle C_lsst L sparsify
              ((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate k M N D restarts s₀).1 (restarts s₀)).2.2.2.1 j
            rw [hst0_fold] at hC_act
            rwa [← hb_pre.activeComps])
          hj_rest
        have hpre_spB : (((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate k M N D restarts s₀).1.trees j).splitBound = splitB :=
          (runAfterRestarts_base_proj oracle C_lsst L sparsify k M N D restarts hV₀ j s₀).1.splitBound.trans
            hb_s0.2.2.2.1
        have hpre_m0 : (((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate k M N D restarts s₀).1.trees j).m₀ = M :=
          (runAfterRestarts_base_proj oracle C_lsst L sparsify k M N D restarts hV₀ j s₀).1.m₀.trans
            hb_s0.1
        have hrb : restartBucketGraph
            (((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate k M N D restarts s₀).1.trees j) C b =
            Hb C b :=
          hf.1.symm.trans (by dsimp only [Hb]; rw [hst0_fold])
        have hf2 := hf.2
        rw [← hst0_fold, hrb, hpre_spB, hpre_m0] at hf2
        exact hf2
    · have hinact : ∀ r ≤ s₀,
          ((T.runAfterRestarts k M N D restarts r).trees j).dyn (C, b) =
            ((initTreeCore oracle C_lsst L sparsify k M N G₀ (D.ℓ 0) j).dyn (C, b)) ∧
          ((T.runAfterRestarts k M N D restarts r).trees j).ts C = ts₀ C := by
        have hact_base : ∀ r ≤ s₀,
            C ∉ ((T.runAfterRestarts k M N D restarts r).trees j).activeComps := fun r hr hmem => by
          have hsub_act : ∀ a b0, a ≤ b0 → b0 ≤ τ →
              (treeRunSeq oracle C_lsst L sparsify k M N D j a).1.activeComps ⊆
                (treeRunSeq oracle C_lsst L sparsify k M N D j b0).1.activeComps := fun a b0 hab hb0 => by
            induction b0 with
            | zero => obtain rfl := Nat.le_zero.mp hab; exact Finset.Subset.rfl
            | succ m ihm =>
              rcases Nat.eq_or_lt_of_le hab with rfl | hlt
              · exact Finset.Subset.rfl
              · have hm_lt : m < τ := hb0
                exact Finset.Subset.trans (ihm (Nat.le_of_lt_succ hlt) (Nat.le_of_lt hm_lt))
                  (by rw [(hStep m hm_lt).2.1.2.2.1]; exact Finset.subset_union_left)
          have h1 := (runAfterRestarts_base_proj oracle C_lsst L sparsify k M N D restarts hV₀ j r).2.activeComps
          have h2 := (hSt_base 0 (Nat.zero_le _)).activeComps
          rw [Nat.add_zero] at h2
          rw [h1] at hmem
          rw [h2] at hC_act
          exact hC_act (hsub_act r s₀ hr (le_trans hst htτ) hmem)
        intro r hr
        induction r with
        | zero =>
          have hpre0_eq : (T.runAfterUpdate k M N D restarts 0).1.trees j =
              initTreeCore oracle C_lsst L sparsify k M N G₀ (D.ℓ 0) j := by
            dsimp only [T, SparseCoreRestartTool.runAfterUpdate]
            exact sparseCoreRestartTool_init_trees oracle C_lsst L sparsify k M N G₀ (D.ℓ 0) (D.g 0) j
          have hf0 := (foldl_restart_props oracle C_lsst L sparsify
            (T.runAfterUpdate k M N D restarts 0).1 (restarts 0)).2.2.2.1 j
          have hna0 : C ∉ ((T.runAfterUpdate k M N D restarts 0).1.trees j).activeComps := by
            have := hact_base 0 (Nat.zero_le s₀)
            unfold SparseCoreRestartTool.runAfterRestarts at this
            rwa [hf0.activeComps] at this
          have hdyn0 := foldl_restart_dyn_inactive oracle C_lsst L sparsify (restarts 0)
            (T.runAfterUpdate k M N D restarts 0).1 j (C := C) (b := b) hna0
          refine ⟨?_, ?_⟩
          · change ((restarts 0).foldl T.restart (T.runAfterUpdate k M N D restarts 0).1 |>.trees j).dyn (C, b) = _
            rw [hdyn0, hpre0_eq]
          · change ((restarts 0).foldl T.restart (T.runAfterUpdate k M N D restarts 0).1 |>.trees j).ts C = ts₀ C
            rw [hf0.ts, hpre0_eq]; rfl
        | succ m ih =>
          have hm_le : m ≤ s₀ := Nat.le_of_succ_le hr
          have ihm := ih hm_le
          have hna_m1 : C ∉ ((T.runAfterRestarts k M N D restarts (m + 1)).trees j).activeComps :=
            hact_base (m + 1) hr
          have hf_m1 := (foldl_restart_props oracle C_lsst L sparsify
            (T.runAfterUpdate k M N D restarts (m + 1)).1 (restarts (m + 1))).2.2.2.1 j
          have hna_pre : C ∉ ((T.runAfterUpdate k M N D restarts (m + 1)).1.trees j).activeComps := by
            unfold SparseCoreRestartTool.runAfterRestarts at hna_m1
            rwa [hf_m1.activeComps] at hna_m1
          have hdyn_post := foldl_restart_dyn_inactive oracle C_lsst L sparsify (restarts (m + 1))
            (T.runAfterUpdate k M N D restarts (m + 1)).1 j (C := C) (b := b) hna_pre
          have hpre_eq : (T.runAfterUpdate k M N D restarts (m + 1)).1.trees j =
              (stepTreeCoreAux sparsify ((T.runAfterRestarts k M N D restarts m).trees j)
                (D.U (m + 1))).state := by
            rw [T.runAfterUpdate_succ]
            dsimp only [T]
            rw [sparseCoreRestartTool_update_of_nonempty (hne m)]
          have hcs_m := (runAfterRestarts_base_proj oracle C_lsst L sparsify k M N D restarts hV₀ j m).2.cs
          have hbm := hBase m (le_trans hm_le (le_trans hst htτ))
          have hG₀_m : ((T.runAfterRestarts k M N D restarts m).trees j).cs.G₀ = G₀ := by
            rw [hcs_m, hbm.2.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
          have hnt : C ∉ touchedCompsBatch ((T.runAfterRestarts k M N D restarts m).trees j).cs (D.U (m + 1)) := by
            intro hmem
            rw [hpre_eq] at hna_pre
            exact hna_pre (Finset.mem_union.mpr (Or.inr
              (Finset.mem_sdiff.mpr ⟨hmem, hact_base m hm_le⟩)))
          have hproj_nil : projCompBatchG ((T.runAfterRestarts k M N D restarts m).trees j).cs.G
              (((T.runAfterRestarts k M N D restarts m).trees j).cs.compSt C).G (D.U (m + 1)) = [] := by
            by_contra hne_p
            exact hnt (Finset.mem_filter.mpr ⟨hG₀_m ▸ hC, hne_p⟩)
          have hUb_nil : (stepTreeCoreAux sparsify ((T.runAfterRestarts k M N D restarts m).trees j)
              (D.U (m + 1))).U_b (C, b) = [] := by
            dsimp only [stepTreeCoreAux, stepTreeCoreAuxWith]
            rw [hproj_nil]
            simp [tildeStepBatch, filterBucketBatch]
          have hts_m1 : ((T.runAfterRestarts k M N D restarts (m + 1)).trees j).ts C = ts₀ C := by
            have hp := (runAfterRestarts_base_proj oracle C_lsst L sparsify k M N D restarts hV₀ j (m + 1)).2
            have hbm1 := hBase (m + 1) (le_trans hr (le_trans hst htτ))
            rw [hp.ts]
            exact (hbm1.2.2.2.2.2.2.2.2.2.2.2.1 C hC (by rwa [← hp.activeComps])).2
          have hdyn_pre : ((T.runAfterUpdate k M N D restarts (m + 1)).1.trees j).dyn (C, b) =
              ((T.runAfterRestarts k M N D restarts m).trees j).dyn (C, b) := by
            rw [hpre_eq]
            dsimp only [stepTreeCoreAux, stepTreeCoreAuxWith] at hUb_nil ⊢
            simp [hUb_nil, update_nil]
          refine ⟨?_, hts_m1⟩
          change ((restarts (m + 1)).foldl T.restart (T.runAfterUpdate k M N D restarts (m + 1)).1 |>.trees j).dyn (C, b) = _
          rw [hdyn_post, hdyn_pre, ihm.1]
      have hres := hinact s₀ le_rfl
      rw [hst0_eq] at ⊢
      rw [hres.1]
      have hHb_eq : Hb C b = initBucketGraph (cs₀.compSt C) (D.ℓ 0) b := by
        dsimp only [Hb]
        exact hHb0_eq (st 0) (hst0_eq ▸ hres.2) hOB_0
      rw [hHb_eq]
      rfl
  have hPref : ∀ d ≤ t - s₀,
      let pref := ((Us_ep C b).take d).flatten
      (Hb C b).BatchIsValid pref ∧
      (∀ op ∈ pref, isDelOrSplit op) ∧
      ((st d).dyn (C, b)).G = (Hb C b).applyBatch pref ∧
      (st d).dyn (C, b) = DynSpanner.runBatchState (L := L) (Hb C b)
        (phaseBase ((Hb C b).n + splitB) L) (sparsify M) ((Us_ep C b).take d) d ∧
      ((st d).dyn (C, b)).G.IsValid ∧
      ((st d).dyn (C, b)).G.IsSubgraph ((st d).dyn (C, b)).H ∧
      ((st d).ts C).C.IsSubgraph ((st d).dyn (C, b)).G ∧
      ((st d).dyn (C, b)).G.E = ((st d).ts C).C.E.filter (fun e => (st d).origBucket e = b) := by
    intro d
    induction d with
    | zero =>
      intro _
      have hq1 : 1 ≤ phaseBase ((Hb C b).n + splitB) L := le_trans (by omega) (two_le_phaseBase _ L)
      have hinv0 := (DynSpanner.runInv_all hHb_val hL hq1 hHb_mM hSp (us := [])
        (by trivial) (fun _ h => by simp at h) 0 le_rfl).1
      have h0eq : (st 0).dyn (C, b) = DynSpanner.runBatchState (L := L) (Hb C b)
          (phaseBase ((Hb C b).n + splitB) L) (sparsify M) ((Us_ep C b).take 0) 0 := hInit_dyn0
      have hG0_eq : ((st 0).dyn (C, b)).G = Hb C b := by
        rw [hInit_dyn0]; exact hinv0.G_eq
      refine ⟨trivial, fun _ h => by simp at h, hG0_eq, h0eq, ?_, ?_, ?_, ?_⟩
      · rw [hG0_eq]; exact hHb_val
      · rw [hInit_dyn0]; exact hinv0.H_sub
      · rw [hG0_eq]; exact hHb_sp.2.1
      · rw [hG0_eq]; exact hHb_sp.2.2.1
    | succ δ ih =>
      intro hδ1
      have hδ_lt : δ < t - s₀ := hδ1
      obtain ⟨hBV_p, hds_p, hApp_p, hRun_p, hG_val_p, hH_sub_p, hTs_sub_p, hE_eq_p⟩ :=
        ih (Nat.le_of_lt hδ_lt)
      have hBase_δ := hBase (s₀ + δ) (by omega)
      have hBase_δ1 := hBase (s₀ + δ + 1) (by omega)
      have hst_δ := hSt_base δ (Nat.le_of_lt hδ_lt)
      have hst_δ1 := hSt_base (δ + 1) hδ1
      set info := stepTreeCoreAux sparsify (st δ) (D.U (s₀ + δ + 1))
      have hT_δ : TildeInv (cs₀.compSt C) ((st δ).cs.compSt C) ((st δ).ts C) := by
        rw [hst_δ.cs, hst_δ.ts]; exact (hBase_δ.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.1
      have htd := htilde_step (st δ) (s₀ + δ) (by omega) hst_δ.cs hst_δ.ts
      have hts_eq_step : ((st (δ + 1)).ts C).C = ((st δ).ts C).C.applyBatch (info.U_C C) := by
        rw [hst_δ1.ts, show s₀ + (δ + 1) = s₀ + δ + 1 by omega]
        exact htd.2.1.symm ▸ (by rw [hst_δ.cs, hst_δ.ts]; rfl)
      have hfb := filterBucketBatch_spec hT_δ.hC_val hG_val_p hTs_sub_p hE_eq_p htd.1 htd.2.2
      dsimp only at hfb
      have hUb_def : info.U_b (C, b) =
          (filterBucketBatch ((st δ).dyn (C, b)).G
            ((stepTreeCoreAux sparsify (st δ) (D.U (s₀ + δ + 1))).U_C C)).2 := rfl
      rw [← hUb_def] at hfb
      have hget : (Us_ep C b)[δ]? = some (info.U_b (C, b)) := by
        dsimp only [Us_ep]
        rw [List.getElem?_map, List.getElem?_range hδ_lt]
        rfl
      have htake : ((Us_ep C b).take (δ + 1)).flatten =
          ((Us_ep C b).take δ).flatten ++ info.U_b (C, b) := by
        rw [take_succ_of_getElem? hget, List.flatten_append]
        simp
      have hBV_s1 : (Hb C b).BatchIsValid ((Us_ep C b).take (δ + 1)).flatten := by
        rw [htake, SparseCore.batchIsValid_append]
        refine ⟨hBV_p, ?_⟩
        rw [← hApp_p]
        exact hfb.1
      have hds_s1 : ∀ op ∈ ((Us_ep C b).take (δ + 1)).flatten, isDelOrSplit op := by
        intro op hop
        rw [htake, List.mem_append] at hop
        exact hop.elim (hds_p op) (hfb.2.2.2.2.2.1 op)
      have hq1 : 1 ≤ phaseBase ((Hb C b).n + splitB) L := le_trans (by omega) (two_le_phaseBase _ L)
      have hTrace := DynSpanner.batchTrace_spec hHb_val hL hq1 hHb_mM hSp hBV_s1 hds_s1
      have hUs_take_len : ((Us_ep C b).take (δ + 1)).length = δ + 1 := by
        rw [List.length_take_of_le (by simp [Us_ep]; exact hδ1)]
      have htr1 := hTrace.1 (δ + 1) hUs_take_len.symm.le
      have hget_take : ((Us_ep C b).take (δ + 1))[δ]? = some (info.U_b (C, b)) := by
        rw [List.getElem?_take]; simp [hget]
      have hrun_eq_δ : DynSpanner.runBatchState (L := L) (Hb C b)
          (phaseBase ((Hb C b).n + splitB) L) (sparsify M) ((Us_ep C b).take δ) δ =
          DynSpanner.runBatchState (L := L) (Hb C b)
            (phaseBase ((Hb C b).n + splitB) L) (sparsify M) ((Us_ep C b).take (δ + 1)) δ := by
        rw [runBatchState_take_eq _ _ _ ((Us_ep C b).take (δ + 1)) δ δ le_rfl]
        simp [List.take_take]
      have hm₀_eq : (st δ).m₀ = M := hst_δ.m₀.trans hBase_δ.1
      have hstep_st : (st (δ + 1)).dyn (C, b) =
          (DynSpanner.update ((st δ).dyn (C, b)) (info.U_b (C, b)) (sparsify M)).state := by
        have hstep_eq : (st (δ + 1)).dyn (C, b) =
            ((stepTreeCoreAux sparsify (st δ) (D.U (s₀ + δ + 1))).state).dyn (C, b) :=
          congrFun (congrArg TreeCoreState.dyn (hSt_step δ hδ_lt).1) (C, b)
        rw [hstep_eq]
        change (DynSpanner.update ((st δ).dyn (C, b)) (info.U_b (C, b)) (sparsify (st δ).m₀)).state = _
        rw [hm₀_eq]
      have hrun_s1 : (st (δ + 1)).dyn (C, b) =
          DynSpanner.runBatchState (L := L) (Hb C b) (phaseBase ((Hb C b).n + splitB) L)
            (sparsify M) ((Us_ep C b).take (δ + 1)) (δ + 1) := by
        rw [hstep_st, hRun_p, hrun_eq_δ]
        dsimp only [DynSpanner.runBatchState]
        rw [hget_take]
      have hTake_all_len : ((Us_ep C b).take (δ + 1)).flatten.length =
          batchPrefixLen ((Us_ep C b).take (δ + 1)) (δ + 1) := by
        simp [batchPrefixLen, List.take_of_length_le hUs_take_len.le]
      have hinv1 := (DynSpanner.runInv_all hHb_val hL hq1 hHb_mM hSp hBV_s1 hds_s1
        ((Us_ep C b).take (δ + 1)).flatten.length le_rfl).1
      have hst_runState : (st (δ + 1)).dyn (C, b) =
          DynSpanner.runState (Hb C b) (phaseBase ((Hb C b).n + splitB) L)
            (sparsify M) ((Us_ep C b).take (δ + 1)).flatten
            ((Us_ep C b).take (δ + 1)).flatten.length := by
        rw [hrun_s1, htr1.1, hTake_all_len]
      have hG_app1 : ((st (δ + 1)).dyn (C, b)).G =
          (Hb C b).applyBatch ((Us_ep C b).take (δ + 1)).flatten := by
        rw [hst_runState, hinv1.G_eq, List.take_length]
      have hG_step1 : ((st (δ + 1)).dyn (C, b)).G = ((st δ).dyn (C, b)).G.applyBatch (info.U_b (C, b)) := by
        rw [hG_app1, htake, SparseCore.applyBatch_append, ← hApp_p]
      have hob_eq : (st (δ + 1)).origBucket = (st δ).origBucket := by
        rw [show s₀ + δ + 1 = s₀ + (δ + 1) by omega] at hBase_δ1
        rw [hst_δ.origBucket, hst_δ1.origBucket, hBase_δ.2.2.2.2.1, hBase_δ1.2.2.2.2.1]
      refine ⟨hBV_s1, hds_s1, hG_app1, hrun_s1, ?_, ?_, ?_, ?_⟩
      · rw [hG_step1, ← hfb.2.1]; exact hfb.2.2.1
      · rw [hst_runState, hinv1.G_eq, List.take_length]
        have := hinv1.H_sub
        rwa [List.take_length] at this
      · rw [hG_step1, ← hfb.2.1, hts_eq_step]
        exact hfb.2.2.2.1
      · rw [hG_step1, ← hfb.2.1, hts_eq_step, hob_eq]
        exact hfb.2.2.2.2.1
  have hUs_len : (Us_ep C b).length = t - s₀ := by simp [Us_ep]
  have hTake_all : (Us_ep C b).take (t - s₀) = Us_ep C b := List.take_of_length_le hUs_len.le
  obtain ⟨hBV_fin, hds_fin, _, _, _, _, _, _⟩ := hPref (t - s₀) le_rfl
  rw [hTake_all] at hBV_fin hds_fin
  refine ⟨hHb_val, hHb_m, hHb_sp.2.2.2.1, hHb_deg, hBV_fin, hds_fin, hInit_dyn0, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨_, _, _, hRun_d, hGval_d, hHsub_d, hTsub_d, hEeq_d⟩ := hPref δ hδ
    rw [← runBatchState_take_eq _ _ _ (Us_ep C b) δ δ le_rfl] at hRun_d
    exact ⟨hRun_d, hGval_d, hHsub_d, hEeq_d, hTsub_d⟩
  · intro δ hδ
    obtain ⟨_, _, hApp_d, hRun_d, hGval_d, _, hTsub_d, hEeq_d⟩ := hPref δ (Nat.le_of_lt hδ)
    have hBase_δ := hBase (s₀ + δ) (by omega)
    have hst_δ := hSt_base δ (Nat.le_of_lt hδ)
    set info := stepTreeCoreAux sparsify (st δ) (D.U (s₀ + δ + 1))
    have hT_δ : TildeInv (cs₀.compSt C) ((st δ).cs.compSt C) ((st δ).ts C) := by
      rw [hst_δ.cs, hst_δ.ts]; exact (hBase_δ.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.1
    have htd := htilde_step (st δ) (s₀ + δ) (by omega) hst_δ.cs hst_δ.ts
    have hfb := filterBucketBatch_spec hT_δ.hC_val hGval_d hTsub_d hEeq_d htd.1 htd.2.2
    dsimp only at hfb
    have hUb_def : info.U_b (C, b) =
        (filterBucketBatch ((st δ).dyn (C, b)).G
          ((stepTreeCoreAux sparsify (st δ) (D.U (s₀ + δ + 1))).U_C C)).2 := rfl
    rw [← hUb_def] at hfb
    have hget : (Us_ep C b)[δ]? = some (info.U_b (C, b)) := by
      dsimp only [Us_ep]; rw [List.getElem?_map, List.getElem?_range hδ]; rfl
    have hm₀_eq : (st δ).m₀ = M := hst_δ.m₀.trans hBase_δ.1
    rw [← runBatchState_take_eq _ _ _ (Us_ep C b) δ δ le_rfl] at hRun_d
    refine ⟨?_, hfb.1, hfb.2.2.2.2.2.2.1⟩
    dsimp only [DynSpanner.runBatchStepOut]
    rw [hget, ← hRun_d]
    change DynSpanner.update ((st δ).dyn (C, b)) (info.U_b (C, b)) (sparsify (st δ).m₀) = _
    rw [hm₀_eq]

end MinCostFlow.Chain

end
