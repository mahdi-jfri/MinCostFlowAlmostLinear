module

public import MinCostFlow.Chain.Ordered.ConcreteInstantiationWith
public import MinCostFlow.Chain.Ordered.ConcreteInstantiationNoHidden
import MinCostFlow.Chain.Ordered.Theorem5_1
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Concrete Instantiation of Ordered `Theorem 5.1` (machine-cost bundle tool and `lastLevelTool`)

Re-exports `MinCostFlow.Chain.Ordered.ConcreteInstantiationWith` (`concrete_theorem_5_1_with*`)
and `MinCostFlow.Chain.Ordered.ConcreteInstantiationNoHidden` (`concrete_theorem_5_1_noHidden`,
`concrete_level_instanceHyps_all_levels`), and proves `concrete_theorem_5_1_last` and
`concrete_theorem_5_1` directly from `theorem_5_1_relaxed_own` (with no degree-cap parameter
`C_D` or `D_cap`). The core tool is `sparseCoreBundleRestartToolMachWith lsfInit` with
`bundleCoreParamsMach`. The existential forms take `lsfInit := initLSFOnline oracle C_lsst`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.Expander MinCostFlow.Bundle

section MainInstantiationsOwn

/-- Core instantiation lemma for `algorithm2_dsWithFailureOwn`. -/
private theorem concrete_theorem_5_1_own_core
    (lsfInit : LSFInit) (C_lsst : ℝ)
    (lastTool : LastLevelTool) (C_last : ℝ)
    (hLast : lastTool.IsSpec (lastLevelParams C_last))
    (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (params : ℕ → DynSpanner.SparsifyParams)
    (C_sp K_s K_t : ℝ) (hCsp : 0 < C_sp) (hKs : 0 ≤ K_s) (hKt : 0 ≤ K_t)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧
      (params m).K_t = K_t ∧ (params m).p_t = 1 ∧
      (params m).γ_ℓ ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params m).γ_c ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    (hInit : IsConcreteLSFInit lsfInit C_lsst)
    (hSp : ∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify)
    (C_ψ C_N : ℝ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N) :
    ∃ (C_γ : ℝ) (M_thresh : ℕ),
      3 ≤ C_γ ∧ 2 ≤ M_thresh ∧
      ∀ (M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
        M_thresh ≤ M₀ →
        1 + Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2) →
        alg2PsiGame Ψ M₀ ≤ Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        0 < α →
        let B_cap := concreteBCap C_lsst Ψ M₀ N₀ hM₀1
        let cfg := concreteAlg2CfgWithLast lsfInit C_lsst lastTool C_last sparsify params
          (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1)
          M₀ N₀ B_cap hM₀1 α Ψ ε
        cfg.T.ToolEmbedsSurvivingOrdRestart →
        cfg.T.ToolNoReinsertOrdRestart →
        ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
          MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T →
          HistoryEdgeOnly D T →
          HistoryLengthsInRange D T Ψ →
          (∀ t ≤ T, (D.G t).m ≤ M₀) →
          (∀ t ≤ T, (D.G t).n ≤ N₀) →
          (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
          let A := algorithm2_dsWithFailureOwn cfg
          let κ := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
          let C_κ := 15 + 5 * C_γ
          let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
          let f := alg2TimeFactor C_rt (47 / 48)
          let st := minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate T
          let Ψ_g := alg2PsiGame Ψ M₀
          let Q_upd := alg2UpdateQueries D isUpdate T
          let K_upd := alg2UpdateCount isUpdate T
          let Q_det := alg2DetectSizeOwn cfg D η isUpdate T
          let K_det := alg2DetectCount isUpdate T
          let Q_tot := (M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
          (0 < κ ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ) ∧
          (Filter.Tendsto (fun m : ℕ => Real.log (f m) / Real.log (m : ℝ)) Filter.atTop (nhds 0) ∧
            ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 1 ≤ B ∧ ∀ m : ℕ, 1 ≤ m → f m ≤ B * (m : ℝ) ^ δ) ∧
          (∀ t ≤ T,
            A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) =
              (minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate t).flow ∧
            ∀ e ∈ (D.G t).E,
              A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) e =
                MinCostFlow.IPM.minRatioFlow A.eraseFailure D η isUpdate t e) ∧
          (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
            (D.G (t + 1)).IsCirculation
                (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) ∧
            (D.HiddenStable (t + 1) α Ψ →
              (MinCostFlow.IPM.minRatioFailureDirection A D η isUpdate t).isSome = true ∧
              (D.G (t + 1)).inner (D.g (t + 1))
                  (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) /
                (D.G (t + 1)).lnorm (D.ℓ (t + 1))
                  (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) ≤ -(κ * α)) ∧
            ∀ Δ, MinCostFlow.IPM.minRatioFailureDirection A D η isUpdate t = some Δ →
              let stNext := minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate (t + 1)
              let T_tree := stNext.extTree
              (D.G (t + 1)).IsSubgraph T_tree ∧
              T_tree.IsForest ∧
              (∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V,
                (D.G (t + 1)).Connected u v → T_tree.Connected u v) ∧
              ((∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V, (D.G (t + 1)).Connected u v) →
                T_tree.IsSpanningTreeOn (D.G (t + 1)).V) ∧
              ∃ (offTreeEdges : List (ℕ × Bool)) (treePaths : List (ℕ × ℕ)),
                (offTreeEdges.length : ℝ) ≤ f M₀ ∧
                (∀ x ∈ offTreeEdges, x.1 ∈ (D.G (t + 1)).E \ T_tree.E) ∧
                (treePaths.length : ℝ) ≤ f M₀ ∧
                (∀ p ∈ treePaths, T_tree.Connected p.1 p.2) ∧
                ∀ e : ℕ, Δ e =
                  (offTreeEdges.map (fun x => walkFlow [x] e)).sum +
                  (treePaths.map (fun p => walkFlow (T_tree.forestPath p.1 p.2) e)).sum) ∧
          (∀ t, t + 1 ≤ T → isUpdate (t + 1) = false →
            (A.detect (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t)).1 =
              MinCostFlow.IPM.minRatioDetectSet A.eraseFailure D η isUpdate ε t) ∧
          (D.HiddenStable T α Ψ →
            ¬ minRatioFailFailedBefore (algorithm2_dsOwn cfg) D η isUpdate T) ∧
          (alg2LctAmortizedCharge N₀ st.lctDetectOps ≤ f M₀ * ((Q_det : ℝ) + (K_det : ℝ)) ∧
            st.chain.rebuildCount cfg.P.d = 0 ∧
            st.chain.rebuildCount 0 + st.chain.updCount 0 ≤ Q_upd ∧
            (st.chain.totalRuntime : ℝ) ≤ alg2RuntimeBoundSR cfg st ∧
            (st.chain.totalTreeUpdates : ℝ) ≤ alg2TreeUpdatesBoundSR cfg st ∧
            (∀ i : Fin (cfg.P.d + 1),
              (st.chain.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P Ψ_g st.chain.rebuildCount i.val) ∧
            (st.largeBatchEnc : ℝ) ≤ 40 * (Q_upd : ℝ) *
              Real.log ((M₀ : ℝ) + (Q_upd : ℝ) + 2) ∧
            ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ M₀) →
              st.largeBatchEnc = 0)) ∧
          (((st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
              f M₀ * Q_tot +
                40 * (Q_upd : ℝ) * Real.log ((M₀ : ℝ) + (Q_upd : ℝ) + 2)) ∧
            ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ M₀) →
              (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
                f M₀ * Q_tot)) := by
  obtain ⟨C_γ, M_thresh, hCγ_ge, hMth2, hAll⟩ :=
    concrete_params_asymptotics_with_last C_lsst C_last C_sp K_s K_t hCsp hKs hKt params hp_spec
      C_ψ C_N hCψ hCN false
  refine ⟨14 * C_γ + 2, M_thresh, by linarith, hMth2, ?_⟩
  intro M₀ N₀ α Ψ ε hM₀1 hM₀ hN₀ hΨ hα B_cap cfg
    hEmb hNoReins D η isUpdate T hHist hEdge hLen hmBound hnBound hConn
  have hB := hAll lsfInit lastTool sparsify M₀ N₀ α Ψ ε hM₀1 hM₀ hN₀ hΨ
  rcases hB with ⟨hTP, hLP, hD, hσ_mono, hσ_nn, _, hγℓ, hγr, hσT, hσM, hcT, hcL, hlogF, hγM₀, hγk, hσL_own⟩
  have hT : ChainToolSupply cfg.T cfg.TP cfg.P cfg.N₀ (max 0 cfg.Ψ) :=
    concreteChainToolSupply_withLast_of_cap lsfInit C_lsst hInit lastTool C_last sparsify params
      (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1) hSp
      (fun m n ψ hm => concreteBCap C_lsst ψ m n hm) (fun _ _ _ _ => le_rfl)
      M₀ N₀ α Ψ ε hM₀1 1 le_rfl hγM₀ hγk
  have hMWU : cfg.T.ToolMWUOrdRestartNoHiddenLe cfg.σ_mwu (cfg.P.M₀ ^ 2) :=
    concreteRestartMWULe lsfInit C_lsst hInit lastTool C_last sparsify params
      (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1)
      M₀ N₀ B_cap hM₀1 α Ψ ε
  have hV : cfg.ValidOrd :=
    { hTP := hTP
      hLP := hLP
      hT := hT
      hL := hLast
      hσ_mwu_mono := hσ_mono
      hσ_mwu_nn := hσ_nn
      hMWU := hMWU
      hEmb := hEmb
      hNoReins := hNoReins
      hγM₀ := hγM₀
      hγk := hγk
      hα := hα }
  have hCγ_le : C_γ ≤ 14 * C_γ + 2 := by linarith
  exact theorem_5_1_relaxed_own hV hD (by linarith) hCψ hCN
    (le_trans hγℓ (exp_23_24_mono_LL hCγ_le hM₀1))
    (le_trans hγr (exp_23_24_mono_LL hCγ_le hM₀1))
    (le_trans hσT (exp_47_48_mono_LL hCγ_le hM₀1))
    hσL_own
    (le_trans hσM (exp_23_24_mono_LL hCγ_le hM₀1))
    (le_trans hcT (exp_23_24_mono_LL hCγ_le hM₀1))
    (le_trans hcL (exp_23_24_mono_LL hCγ_le hM₀1))
    hΨ
    (le_trans hlogF (exp_47_48_mono_LL hCγ_le hM₀1))
    hN₀ hHist hEdge hLen hmBound hnBound hConn

/-- Generalization of ordered `concrete_theorem_5_1` to an arbitrary last-level tool
`lastTool : LastLevelTool` satisfying `lastTool.IsSpec (lastLevelParams C_last)`. -/
theorem concrete_theorem_5_1_last
    (hDec : Cited.ExpanderDecomposition)
    (hPaths : Cited.DecrementalExpanderPaths)
    (lastTool : LastLevelTool) (C_last : ℝ)
    (hLast : lastTool.IsSpec (lastLevelParams C_last))
    (C_ψ C_N : ℝ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N) :
    ∃ (lsfInit : LSFInit) (C_lsst : ℝ)
      (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams)
      (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
      (C_γ : ℝ) (M_thresh : ℕ),
      IsConcreteLSFInit lsfInit C_lsst ∧
      (∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify) ∧
      3 ≤ C_γ ∧ 2 ≤ M_thresh ∧
      ∀ (M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
        M_thresh ≤ M₀ →
        1 + Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2) →
        alg2PsiGame Ψ M₀ ≤ Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        0 < α →
        let B_cap := concreteBCap C_lsst Ψ M₀ N₀ hM₀1
        let cfg := concreteAlg2CfgWithLast lsfInit C_lsst lastTool C_last sparsify params hp_s hp_t
          M₀ N₀ B_cap hM₀1 α Ψ ε
        cfg.T.ToolEmbedsSurvivingOrdRestart →
        cfg.T.ToolNoReinsertOrdRestart →
        ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
          MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T →
          HistoryEdgeOnly D T →
          HistoryLengthsInRange D T Ψ →
          (∀ t ≤ T, (D.G t).m ≤ M₀) →
          (∀ t ≤ T, (D.G t).n ≤ N₀) →
          (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
          let A := algorithm2_dsWithFailureOwn cfg
          let κ := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
          let C_κ := 15 + 5 * C_γ
          let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
          let f := alg2TimeFactor C_rt (47 / 48)
          let st := minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate T
          let Ψ_g := alg2PsiGame Ψ M₀
          let Q_upd := alg2UpdateQueries D isUpdate T
          let K_upd := alg2UpdateCount isUpdate T
          let Q_det := alg2DetectSizeOwn cfg D η isUpdate T
          let K_det := alg2DetectCount isUpdate T
          let Q_tot := (M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
          (0 < κ ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ) ∧
          (Filter.Tendsto (fun m : ℕ => Real.log (f m) / Real.log (m : ℝ)) Filter.atTop (nhds 0) ∧
            ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 1 ≤ B ∧ ∀ m : ℕ, 1 ≤ m → f m ≤ B * (m : ℝ) ^ δ) ∧
          (∀ t ≤ T,
            A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) =
              (minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate t).flow ∧
            ∀ e ∈ (D.G t).E,
              A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) e =
                MinCostFlow.IPM.minRatioFlow A.eraseFailure D η isUpdate t e) ∧
          (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
            (D.G (t + 1)).IsCirculation
                (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) ∧
            (D.HiddenStable (t + 1) α Ψ →
              (MinCostFlow.IPM.minRatioFailureDirection A D η isUpdate t).isSome = true ∧
              (D.G (t + 1)).inner (D.g (t + 1))
                  (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) /
                (D.G (t + 1)).lnorm (D.ℓ (t + 1))
                  (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) ≤ -(κ * α)) ∧
            ∀ Δ, MinCostFlow.IPM.minRatioFailureDirection A D η isUpdate t = some Δ →
              let stNext := minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate (t + 1)
              let T_tree := stNext.extTree
              (D.G (t + 1)).IsSubgraph T_tree ∧
              T_tree.IsForest ∧
              (∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V,
                (D.G (t + 1)).Connected u v → T_tree.Connected u v) ∧
              ((∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V, (D.G (t + 1)).Connected u v) →
                T_tree.IsSpanningTreeOn (D.G (t + 1)).V) ∧
              ∃ (offTreeEdges : List (ℕ × Bool)) (treePaths : List (ℕ × ℕ)),
                (offTreeEdges.length : ℝ) ≤ f M₀ ∧
                (∀ x ∈ offTreeEdges, x.1 ∈ (D.G (t + 1)).E \ T_tree.E) ∧
                (treePaths.length : ℝ) ≤ f M₀ ∧
                (∀ p ∈ treePaths, T_tree.Connected p.1 p.2) ∧
                ∀ e : ℕ, Δ e =
                  (offTreeEdges.map (fun x => walkFlow [x] e)).sum +
                  (treePaths.map (fun p => walkFlow (T_tree.forestPath p.1 p.2) e)).sum) ∧
          (∀ t, t + 1 ≤ T → isUpdate (t + 1) = false →
            (A.detect (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t)).1 =
              MinCostFlow.IPM.minRatioDetectSet A.eraseFailure D η isUpdate ε t) ∧
          (D.HiddenStable T α Ψ →
            ¬ minRatioFailFailedBefore (algorithm2_dsOwn cfg) D η isUpdate T) ∧
          (alg2LctAmortizedCharge N₀ st.lctDetectOps ≤ f M₀ * ((Q_det : ℝ) + (K_det : ℝ)) ∧
            st.chain.rebuildCount cfg.P.d = 0 ∧
            st.chain.rebuildCount 0 + st.chain.updCount 0 ≤ Q_upd ∧
            (st.chain.totalRuntime : ℝ) ≤ alg2RuntimeBoundSR cfg st ∧
            (st.chain.totalTreeUpdates : ℝ) ≤ alg2TreeUpdatesBoundSR cfg st ∧
            (∀ i : Fin (cfg.P.d + 1),
              (st.chain.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P Ψ_g st.chain.rebuildCount i.val) ∧
            (st.largeBatchEnc : ℝ) ≤ 40 * (Q_upd : ℝ) *
              Real.log ((M₀ : ℝ) + (Q_upd : ℝ) + 2) ∧
            ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ M₀) →
              st.largeBatchEnc = 0)) ∧
          (((st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
              f M₀ * Q_tot +
                40 * (Q_upd : ℝ) * Real.log ((M₀ : ℝ) + (Q_upd : ℝ) + 2)) ∧
            ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ M₀) →
              (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
                f M₀ * Q_tot)) := by
  obtain ⟨oracle, C_lsst, hLSST_spec⟩ := LSF.theorem_2_2
  obtain ⟨sparsify, params, C_sp, K_s, K_t, hCsp, _, hKs, hKt, h81⟩ :=
    Expander.theorem_8_1_concrete hDec hPaths
  have hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧
      (params m).K_t = K_t ∧ (params m).p_t = 1 ∧
      (params m).γ_ℓ ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params m).γ_c ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
    fun m => ⟨(h81 m).1, (h81 m).2.1, (h81 m).2.2.1,
      (h81 m).2.2.2.1, (h81 m).2.2.2.2.1, (h81 m).2.2.2.2.2.1⟩
  obtain ⟨C_γ, M_thresh, hCγ, hMth, hAll⟩ :=
    concrete_theorem_5_1_own_core (initLSFOnline oracle C_lsst) C_lsst lastTool C_last hLast
      sparsify params C_sp K_s K_t hCsp hKs hKt hp_spec (isConcreteLSFInit_initLSFOnline hLSST_spec)
      (fun mMax => (h81 mMax).2.2.2.2.2.2) C_ψ C_N hCψ hCN
  refine ⟨initLSFOnline oracle C_lsst, C_lsst, sparsify, params, fun m => le_of_eq (h81 m).2.1,
    fun m => le_of_eq (h81 m).2.2.2.1, C_γ, M_thresh, isConcreteLSFInit_initLSFOnline hLSST_spec,
    fun mMax => (h81 mMax).2.2.2.2.2.2, hCγ, hMth, hAll⟩

/-- **Concrete instantiation of ordered `Theorem 5.1`** (`theorem_5_1_relaxed_own`, paper page 15)
with `sparseCoreBundleRestartToolMachWith lsfInit` and `lastLevelTool`, with no degree-cap parameter
`C_D` or `D_cap`. -/
theorem concrete_theorem_5_1
    (hDec : Cited.ExpanderDecomposition)
    (hPaths : Cited.DecrementalExpanderPaths)
    (C_ψ C_N : ℝ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N) :
    ∃ (lsfInit : LSFInit) (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
      (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams)
      (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
      (C_γ : ℝ) (M_thresh : ℕ),
      IsConcreteLSFInit lsfInit C_lsst ∧ HasLSSTSpec oracle C_lsst ∧
      (∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify) ∧
      3 ≤ C_γ ∧ 2 ≤ M_thresh ∧
      ∀ (M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
        M_thresh ≤ M₀ →
        1 + Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2) →
        alg2PsiGame Ψ M₀ ≤ Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        0 < α →
        let B_cap := concreteBCap C_lsst Ψ M₀ N₀ hM₀1
        let cfg := concreteAlg2Cfg lsfInit oracle C_lsst sparsify params hp_s hp_t
          M₀ N₀ B_cap hM₀1 α Ψ ε
        cfg.T.ToolEmbedsSurvivingOrdRestart →
        cfg.T.ToolNoReinsertOrdRestart →
        ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
          MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T →
          HistoryEdgeOnly D T →
          HistoryLengthsInRange D T Ψ →
          (∀ t ≤ T, (D.G t).m ≤ M₀) →
          (∀ t ≤ T, (D.G t).n ≤ N₀) →
          (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
          let A := algorithm2_dsWithFailureOwn cfg
          let κ := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
          let C_κ := 15 + 5 * C_γ
          let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
          let f := alg2TimeFactor C_rt (47 / 48)
          let st := minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate T
          let Ψ_g := alg2PsiGame Ψ M₀
          let Q_upd := alg2UpdateQueries D isUpdate T
          let K_upd := alg2UpdateCount isUpdate T
          let Q_det := alg2DetectSizeOwn cfg D η isUpdate T
          let K_det := alg2DetectCount isUpdate T
          let Q_tot := (M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
          (0 < κ ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ) ∧
          (Filter.Tendsto (fun m : ℕ => Real.log (f m) / Real.log (m : ℝ)) Filter.atTop (nhds 0) ∧
            ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 1 ≤ B ∧ ∀ m : ℕ, 1 ≤ m → f m ≤ B * (m : ℝ) ^ δ) ∧
          (∀ t ≤ T,
            A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) =
              (minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate t).flow ∧
            ∀ e ∈ (D.G t).E,
              A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) e =
                MinCostFlow.IPM.minRatioFlow A.eraseFailure D η isUpdate t e) ∧
          (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
            (D.G (t + 1)).IsCirculation
                (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) ∧
            (D.HiddenStable (t + 1) α Ψ →
              (MinCostFlow.IPM.minRatioFailureDirection A D η isUpdate t).isSome = true ∧
              (D.G (t + 1)).inner (D.g (t + 1))
                  (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) /
                (D.G (t + 1)).lnorm (D.ℓ (t + 1))
                  (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) ≤ -(κ * α)) ∧
            ∀ Δ, MinCostFlow.IPM.minRatioFailureDirection A D η isUpdate t = some Δ →
              let stNext := minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate (t + 1)
              let T_tree := stNext.extTree
              (D.G (t + 1)).IsSubgraph T_tree ∧
              T_tree.IsForest ∧
              (∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V,
                (D.G (t + 1)).Connected u v → T_tree.Connected u v) ∧
              ((∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V, (D.G (t + 1)).Connected u v) →
                T_tree.IsSpanningTreeOn (D.G (t + 1)).V) ∧
              ∃ (offTreeEdges : List (ℕ × Bool)) (treePaths : List (ℕ × ℕ)),
                (offTreeEdges.length : ℝ) ≤ f M₀ ∧
                (∀ x ∈ offTreeEdges, x.1 ∈ (D.G (t + 1)).E \ T_tree.E) ∧
                (treePaths.length : ℝ) ≤ f M₀ ∧
                (∀ p ∈ treePaths, T_tree.Connected p.1 p.2) ∧
                ∀ e : ℕ, Δ e =
                  (offTreeEdges.map (fun x => walkFlow [x] e)).sum +
                  (treePaths.map (fun p => walkFlow (T_tree.forestPath p.1 p.2) e)).sum) ∧
          (∀ t, t + 1 ≤ T → isUpdate (t + 1) = false →
            (A.detect (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t)).1 =
              MinCostFlow.IPM.minRatioDetectSet A.eraseFailure D η isUpdate ε t) ∧
          (D.HiddenStable T α Ψ →
            ¬ minRatioFailFailedBefore (algorithm2_dsOwn cfg) D η isUpdate T) ∧
          (alg2LctAmortizedCharge N₀ st.lctDetectOps ≤ f M₀ * ((Q_det : ℝ) + (K_det : ℝ)) ∧
            st.chain.rebuildCount cfg.P.d = 0 ∧
            st.chain.rebuildCount 0 + st.chain.updCount 0 ≤ Q_upd ∧
            (st.chain.totalRuntime : ℝ) ≤ alg2RuntimeBoundSR cfg st ∧
            (st.chain.totalTreeUpdates : ℝ) ≤ alg2TreeUpdatesBoundSR cfg st ∧
            (∀ i : Fin (cfg.P.d + 1),
              (st.chain.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P Ψ_g st.chain.rebuildCount i.val) ∧
            (st.largeBatchEnc : ℝ) ≤ 40 * (Q_upd : ℝ) *
              Real.log ((M₀ : ℝ) + (Q_upd : ℝ) + 2) ∧
            ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ M₀) →
              st.largeBatchEnc = 0)) ∧
          (((st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
              f M₀ * Q_tot +
                40 * (Q_upd : ℝ) * Real.log ((M₀ : ℝ) + (Q_upd : ℝ) + 2)) ∧
            ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ M₀) →
              (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
                f M₀ * Q_tot)) := by
  obtain ⟨oracle, C_lsst, hLSST_spec⟩ := LSF.theorem_2_2
  obtain ⟨sparsify, params, C_sp, K_s, K_t, hCsp, _, hKs, hKt, h81⟩ :=
    Expander.theorem_8_1_concrete hDec hPaths
  have hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧
      (params m).K_t = K_t ∧ (params m).p_t = 1 ∧
      (params m).γ_ℓ ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params m).γ_c ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
    fun m => ⟨(h81 m).1, (h81 m).2.1, (h81 m).2.2.1,
      (h81 m).2.2.2.1, (h81 m).2.2.2.2.1, (h81 m).2.2.2.2.2.1⟩
  obtain ⟨C_γ, M_thresh, hCγ, hMth, hAll⟩ :=
    concrete_theorem_5_1_own_core (initLSFOnline oracle C_lsst) C_lsst
      (lastLevelTool oracle C_lsst) C_lsst (lastLevelTool_isSpec oracle C_lsst hLSST_spec)
      sparsify params C_sp K_s K_t hCsp hKs hKt hp_spec (isConcreteLSFInit_initLSFOnline hLSST_spec)
      (fun mMax => (h81 mMax).2.2.2.2.2.2) C_ψ C_N hCψ hCN
  refine ⟨initLSFOnline oracle C_lsst, oracle, C_lsst, sparsify, params,
    fun m => le_of_eq (h81 m).2.1, fun m => le_of_eq (h81 m).2.2.2.1, C_γ, M_thresh,
    isConcreteLSFInit_initLSFOnline hLSST_spec, hLSST_spec,
    fun mMax => (h81 mMax).2.2.2.2.2.2, hCγ, hMth, hAll⟩

end MainInstantiationsOwn

end MinCostFlow.Chain.Ordered
