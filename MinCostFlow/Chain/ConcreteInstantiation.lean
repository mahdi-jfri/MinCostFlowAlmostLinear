module

public import MinCostFlow.Chain.ConcreteBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Concrete Instantiation of `Theorem 5.1` (`sparseCoreRestartTool` and `lastLevelTool`)

Imports the asymptotic parameter and `sigmaLast_N0_obstruction` bounds from
`MinCostFlow.Chain.ConcreteBounds` and proves `concrete_theorem_5_1_with`,
`concrete_theorem_5_1`, `concrete_theorem_5_1_noHidden`, and
`concrete_level_instanceHyps_all_levels`.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.Expander

section MainInstantiations

/-- Core instantiation lemma for `concreteAlg2CfgWithLast` given any extracted `(oracle, C_lsst)`
and `(sparsify, params)`, arbitrary `lastTool : LastLevelTool` at `lastLevelParams C_last`
(`C_last` may depend on `C_lsst`), discharging all asymptotic hypotheses of `theorem_5_1_relaxed_own_with`. -/
theorem concrete_theorem_5_1_with_last_core
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
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
    (C_D C_ψ C_N : ℝ) (hCD : 0 ≤ C_D) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (integerBuckets : Bool := false) :
    ∃ (C_γ : ℝ) (M_thresh : ℕ),
      3 ≤ C_γ ∧ 2 ≤ M_thresh ∧
      ∀ (M₀ N₀ D_cap : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
        M_thresh ≤ M₀ →
        1 + Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2) →
        (D_cap : ℝ) ≤ Real.exp (C_D * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        alg2PsiGame Ψ M₀ ≤ Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        0 < α →
        let B_cap := concreteBucketCapacity integerBuckets C_lsst Ψ M₀ N₀ hM₀1
        let cfg := concreteAlg2CfgWithLast oracle C_lsst lastTool C_last sparsify params
          (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1)
          M₀ N₀ B_cap D_cap hM₀1 α Ψ ε
        cfg.T.IsSpecRestart cfg.TP →
        cfg.T.ToolMWURestart cfg.σ_mwu →
        cfg.T.ToolEmbedsSurvivingRestart →
        cfg.T.ToolNoReinsertRestart →
        let κ_own := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
        let C_κ := 15 + 5 * C_γ
        (0 < κ_own ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ_own) ∧
        ∀ (κ : ℝ), 0 < κ → κ ≤ κ_own →
          ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
            MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T →
            (∀ t ≤ T, (D.G t).m ≤ M₀) →
            (∀ t ≤ T, (D.G t).n ≤ N₀) →
            (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
            let A := algorithm2_dsWithFailureWith cfg κ
            let C_rt := 62 + 21 * C_γ + 4 * C_ψ + C_N
            let f := alg2TimeFactor C_rt (47 / 48)
            let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
            let Ψ_g := alg2PsiGame Ψ M₀
            let Q_upd := alg2UpdateQueries D isUpdate T
            let K_upd := alg2UpdateCount isUpdate T
            let Q_det := alg2DetectSizeWith cfg κ D η isUpdate T
            let K_det := alg2DetectCount isUpdate T
            let Q_tot := (M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
            (0 < κ ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ_own) ∧
            (Filter.Tendsto (fun m : ℕ => Real.log (f m) / Real.log (m : ℝ)) Filter.atTop (nhds 0) ∧
              ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 1 ≤ B ∧ ∀ m : ℕ, 1 ≤ m → f m ≤ B * (m : ℝ) ^ δ) ∧
            (∀ t ≤ T,
              A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) =
                (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t).flow ∧
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
                let stNext := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1)
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
              ¬ minRatioFailFailedBefore (algorithm2_dsWith cfg κ) D η isUpdate T) ∧
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
      C_D C_ψ C_N hCD hCψ hCN integerBuckets
  refine ⟨14 * C_γ + 2, M_thresh, by linarith, hMth2, ?_⟩
  intro M₀ N₀ D_cap α Ψ ε hM₀1 hM₀ hN₀ hDcap hΨ hα B_cap cfg
    hT hMWU hEmb hNoReins
  have hB := hAll oracle lastTool sparsify M₀ N₀ D_cap α Ψ ε hM₀1 hM₀ hN₀ hDcap hΨ
  rcases hB with ⟨hTP, hLP, hD, hσ_mono, hσ_nn, _, hγℓ, hγr, hσT, hσM, hcT, hcL, hlogF, hγM₀, hγk, hσL_own⟩
  have hV : cfg.Valid :=
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
  have hγℓ' : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp ((14 * C_γ + 2) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) :=
    le_trans hγℓ (exp_23_24_mono_LL hCγ_le hM₀1)
  have hγr' : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp ((14 * C_γ + 2) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) :=
    le_trans hγr (exp_23_24_mono_LL hCγ_le hM₀1)
  have hσT' : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp ((14 * C_γ + 2) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) :=
    le_trans hσT (exp_47_48_mono_LL hCγ_le hM₀1)
  have hσL' : cfg.LP.σ_last (levelM cfg.TP cfg.P cfg.P.d + 1) ≤
      Real.exp ((14 * C_γ + 2) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := hσL_own
  have hσM' : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp ((14 * C_γ + 2) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) :=
    le_trans hσM (exp_23_24_mono_LL hCγ_le hM₀1)
  have hcT' : cfg.TP.c_T ≤
      Real.exp ((14 * C_γ + 2) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) :=
    le_trans hcT (exp_23_24_mono_LL hCγ_le hM₀1)
  have hcL' : cfg.LP.c_last ≤
      Real.exp ((14 * C_γ + 2) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) :=
    le_trans hcL (exp_23_24_mono_LL hCγ_le hM₀1)
  have hlogF' : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp ((14 * C_γ + 2) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) :=
    le_trans hlogF (exp_47_48_mono_LL hCγ_le hM₀1)
  refine ⟨?_, fun κ hκ_pos hκ_le D η isUpdate T hHist hmBound hnBound hConn => ?_⟩
  · exact theorem_5_1_relaxed_own_kappa_lower hV.toNoHidden hD (by linarith) hCψ hCN
      hγℓ' hγr' hσT' hσL' hσM' hcT' hcL' hΨ hlogF' hN₀
  · exact theorem_5_1_relaxed_own_with κ hV hκ_pos hκ_le hD (by linarith) hCψ hCN
      hγℓ' hγr' hσT' hσL' hσM' hcT' hcL' hΨ hlogF' hN₀ hHist hmBound hnBound hConn

/-- Generalization of `concrete_theorem_5_1_with` to an arbitrary last-level tool
`lastTool : LastLevelTool` satisfying `lastTool.IsSpec (lastLevelParams C_last)`. -/
theorem concrete_theorem_5_1_with_last
    (hDec : Cited.ExpanderDecomposition)
    (hPaths : Cited.DecrementalExpanderPaths)
    (lastTool : LastLevelTool) (C_last : ℝ)
    (hLast : lastTool.IsSpec (lastLevelParams C_last))
    (C_D C_ψ C_N : ℝ) (hCD : 0 ≤ C_D) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (integerBuckets : Bool := false) :
    ∃ (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
      (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams)
      (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
      (C_γ : ℝ) (M_thresh : ℕ),
      HasLSSTSpec oracle C_lsst ∧
      (∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify) ∧
      3 ≤ C_γ ∧ 2 ≤ M_thresh ∧
      ∀ (M₀ N₀ D_cap : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
        M_thresh ≤ M₀ →
        1 + Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2) →
        (D_cap : ℝ) ≤ Real.exp (C_D * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        alg2PsiGame Ψ M₀ ≤ Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        0 < α →
        let B_cap := concreteBucketCapacity integerBuckets C_lsst Ψ M₀ N₀ hM₀1
        let cfg := concreteAlg2CfgWithLast oracle C_lsst lastTool C_last sparsify params hp_s hp_t
          M₀ N₀ B_cap D_cap hM₀1 α Ψ ε
        cfg.T.IsSpecRestart cfg.TP →
        cfg.T.ToolMWURestart cfg.σ_mwu →
        cfg.T.ToolEmbedsSurvivingRestart →
        cfg.T.ToolNoReinsertRestart →
        let κ_own := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
        let C_κ := 15 + 5 * C_γ
        (0 < κ_own ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ_own) ∧
        ∀ (κ : ℝ), 0 < κ → κ ≤ κ_own →
          ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
            MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T →
            (∀ t ≤ T, (D.G t).m ≤ M₀) →
            (∀ t ≤ T, (D.G t).n ≤ N₀) →
            (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
            let A := algorithm2_dsWithFailureWith cfg κ
            let C_rt := 62 + 21 * C_γ + 4 * C_ψ + C_N
            let f := alg2TimeFactor C_rt (47 / 48)
            let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
            let Ψ_g := alg2PsiGame Ψ M₀
            let Q_upd := alg2UpdateQueries D isUpdate T
            let K_upd := alg2UpdateCount isUpdate T
            let Q_det := alg2DetectSizeWith cfg κ D η isUpdate T
            let K_det := alg2DetectCount isUpdate T
            let Q_tot := (M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
            (0 < κ ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ_own) ∧
            (Filter.Tendsto (fun m : ℕ => Real.log (f m) / Real.log (m : ℝ)) Filter.atTop (nhds 0) ∧
              ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 1 ≤ B ∧ ∀ m : ℕ, 1 ≤ m → f m ≤ B * (m : ℝ) ^ δ) ∧
            (∀ t ≤ T,
              A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) =
                (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t).flow ∧
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
                let stNext := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1)
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
              ¬ minRatioFailFailedBefore (algorithm2_dsWith cfg κ) D η isUpdate T) ∧
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
    concrete_theorem_5_1_with_last_core oracle C_lsst lastTool C_last hLast sparsify params
      C_sp K_s K_t hCsp hKs hKt hp_spec C_D C_ψ C_N hCD hCψ hCN integerBuckets
  refine ⟨oracle, C_lsst, sparsify, params, fun m => le_of_eq (h81 m).2.1,
    fun m => le_of_eq (h81 m).2.2.2.1, C_γ, M_thresh, hLSST_spec,
    fun mMax => (h81 mMax).2.2.2.2.2.2, hCγ, hMth, hAll⟩

/-- Small-`κ` generalization of `concrete_theorem_5_1` for `algorithm2_dsWithFailureWith cfg κ`:
restated as the `lastTool := lastLevelTool oracle C_lsst`, `C_last := C_lsst` case of
`concrete_theorem_5_1_with_last_core`. -/
theorem concrete_theorem_5_1_with
    (hDec : Cited.ExpanderDecomposition)
    (hPaths : Cited.DecrementalExpanderPaths)
    (C_D C_ψ C_N : ℝ) (hCD : 0 ≤ C_D) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N) :
    ∃ (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
      (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams)
      (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
      (C_γ : ℝ) (M_thresh : ℕ),
      HasLSSTSpec oracle C_lsst ∧
      (∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify) ∧
      3 ≤ C_γ ∧ 2 ≤ M_thresh ∧
      ∀ (M₀ N₀ D_cap : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
        M_thresh ≤ M₀ →
        1 + Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2) →
        (D_cap : ℝ) ≤ Real.exp (C_D * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        alg2PsiGame Ψ M₀ ≤ Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        0 < α →
        let B_cap := concreteBCap C_lsst Ψ M₀ N₀ hM₀1
        let cfg := concreteAlg2Cfg oracle C_lsst sparsify params hp_s hp_t
          M₀ N₀ B_cap D_cap hM₀1 α Ψ ε
        cfg.T.IsSpecRestart cfg.TP →
        cfg.T.ToolMWURestart cfg.σ_mwu →
        cfg.T.ToolEmbedsSurvivingRestart →
        cfg.T.ToolNoReinsertRestart →
        let κ_own := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
        let C_κ := 15 + 5 * C_γ
        (0 < κ_own ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ_own) ∧
        ∀ (κ : ℝ), 0 < κ → κ ≤ κ_own →
          ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
            MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T →
            (∀ t ≤ T, (D.G t).m ≤ M₀) →
            (∀ t ≤ T, (D.G t).n ≤ N₀) →
            (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
            let A := algorithm2_dsWithFailureWith cfg κ
            let C_rt := 62 + 21 * C_γ + 4 * C_ψ + C_N
            let f := alg2TimeFactor C_rt (47 / 48)
            let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
            let Ψ_g := alg2PsiGame Ψ M₀
            let Q_upd := alg2UpdateQueries D isUpdate T
            let K_upd := alg2UpdateCount isUpdate T
            let Q_det := alg2DetectSizeWith cfg κ D η isUpdate T
            let K_det := alg2DetectCount isUpdate T
            let Q_tot := (M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
            (0 < κ ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ_own) ∧
            (Filter.Tendsto (fun m : ℕ => Real.log (f m) / Real.log (m : ℝ)) Filter.atTop (nhds 0) ∧
              ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 1 ≤ B ∧ ∀ m : ℕ, 1 ≤ m → f m ≤ B * (m : ℝ) ^ δ) ∧
            (∀ t ≤ T,
              A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) =
                (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t).flow ∧
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
                let stNext := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1)
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
              ¬ minRatioFailFailedBefore (algorithm2_dsWith cfg κ) D η isUpdate T) ∧
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
    concrete_theorem_5_1_with_last_core oracle C_lsst (lastLevelTool oracle C_lsst) C_lsst
      (lastLevelTool_isSpec oracle C_lsst hLSST_spec) sparsify params
      C_sp K_s K_t hCsp hKs hKt hp_spec C_D C_ψ C_N hCD hCψ hCN false
  refine ⟨oracle, C_lsst, sparsify, params, fun m => le_of_eq (h81 m).2.1,
    fun m => le_of_eq (h81 m).2.2.2.1, C_γ, M_thresh, hLSST_spec,
    fun mMax => (h81 mMax).2.2.2.2.2.2, hCγ, hMth, hAll⟩

/-- Generalization of `concrete_theorem_5_1` to an arbitrary last-level tool
`lastTool : LastLevelTool` satisfying `lastTool.IsSpec (lastLevelParams C_last)`. -/
theorem concrete_theorem_5_1_last
    (hDec : Cited.ExpanderDecomposition)
    (hPaths : Cited.DecrementalExpanderPaths)
    (lastTool : LastLevelTool) (C_last : ℝ)
    (hLast : lastTool.IsSpec (lastLevelParams C_last))
    (C_D C_ψ C_N : ℝ) (hCD : 0 ≤ C_D) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N) :
    ∃ (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
      (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams)
      (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
      (C_γ : ℝ) (M_thresh : ℕ),
      HasLSSTSpec oracle C_lsst ∧
      (∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify) ∧
      3 ≤ C_γ ∧ 2 ≤ M_thresh ∧
      ∀ (M₀ N₀ D_cap : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
        M_thresh ≤ M₀ →
        1 + Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2) →
        (D_cap : ℝ) ≤ Real.exp (C_D * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        alg2PsiGame Ψ M₀ ≤ Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        0 < α →
        let B_cap := concreteBCap C_lsst Ψ M₀ N₀ hM₀1
        let cfg := concreteAlg2CfgWithLast oracle C_lsst lastTool C_last sparsify params hp_s hp_t
          M₀ N₀ B_cap D_cap hM₀1 α Ψ ε
        cfg.T.IsSpecRestart cfg.TP →
        cfg.T.ToolMWURestart cfg.σ_mwu →
        cfg.T.ToolEmbedsSurvivingRestart →
        cfg.T.ToolNoReinsertRestart →
        ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
          MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T →
          (∀ t ≤ T, (D.G t).m ≤ M₀) →
          (∀ t ≤ T, (D.G t).n ≤ N₀) →
          (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
          let A := algorithm2_dsWithFailureOwn cfg
          let κ := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
          let C_κ := 15 + 5 * C_γ
          let C_rt := 62 + 21 * C_γ + 4 * C_ψ + C_N
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
  obtain ⟨oracle, C_lsst, sparsify, params, hp_s, hp_t, C_γ, M_thresh,
      hLSST_spec, hSp_spec, hCγ, hMth, hAll⟩ :=
    concrete_theorem_5_1_with_last hDec hPaths lastTool C_last hLast
      C_D C_ψ C_N hCD hCψ hCN false
  refine ⟨oracle, C_lsst, sparsify, params, hp_s, hp_t, C_γ, M_thresh,
    hLSST_spec, hSp_spec, hCγ, hMth, ?_⟩
  intro M₀ N₀ D_cap α Ψ ε hM₀1 hM₀ hN₀ hDcap hΨ hα B_cap cfg
    hT hMWU hEmb hNoReins D η isUpdate T hHist hmBound hnBound hConn
  obtain ⟨hKappaOwn, hWith⟩ := hAll M₀ N₀ D_cap α Ψ ε hM₀1 hM₀ hN₀ hDcap hΨ hα
    hT hMWU hEmb hNoReins
  simpa only [algorithm2_dsWithFailureOwn, algorithm2_dsOwn, alg2DetectSizeOwn, cfg, B_cap, concreteBucketCapacity] using
    hWith (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hKappaOwn.1 le_rfl
      hHist hmBound hnBound hConn

/-- **Concrete instantiation of `Theorem 5.1`** (`theorem_5_1_relaxed_own`) with `sparseCoreRestartTool`
and `lastLevelTool` derived from `[AN19]` (`LSF.theorem_2_2`) and Theorem 8.1
(`Expander.theorem_8_1_concrete`). All parameter sanity, monotonicity, asymptotic exponent
(`hγℓ, hγr, hσT, hσL_own, hσM, hcT, hcL, hlogF, hγM₀, hγk`), and `LastLevelTool.IsSpec` obligations are
discharged concretely for all `M₀ ≥ M_thresh` (no global-`N₀` `hσL` assumption); only input
connectedness and the restartable `SparseCoreRestartTool` specification (`IsSpecRestart`,
`ToolMWURestart`, `ToolEmbedsSurvivingRestart`, `ToolNoReinsertRestart`) are hypotheses. -/
theorem concrete_theorem_5_1
    (hDec : Cited.ExpanderDecomposition)
    (hPaths : Cited.DecrementalExpanderPaths)
    (C_D C_ψ C_N : ℝ) (hCD : 0 ≤ C_D) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N) :
    ∃ (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
      (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams)
      (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
      (C_γ : ℝ) (M_thresh : ℕ),
      HasLSSTSpec oracle C_lsst ∧
      (∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify) ∧
      3 ≤ C_γ ∧ 2 ≤ M_thresh ∧
      ∀ (M₀ N₀ D_cap : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
        M_thresh ≤ M₀ →
        1 + Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2) →
        (D_cap : ℝ) ≤ Real.exp (C_D * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        alg2PsiGame Ψ M₀ ≤ Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        0 < α →
        let B_cap := concreteBCap C_lsst Ψ M₀ N₀ hM₀1
        let cfg := concreteAlg2Cfg oracle C_lsst sparsify params hp_s hp_t
          M₀ N₀ B_cap D_cap hM₀1 α Ψ ε
        cfg.T.IsSpecRestart cfg.TP →
        cfg.T.ToolMWURestart cfg.σ_mwu →
        cfg.T.ToolEmbedsSurvivingRestart →
        cfg.T.ToolNoReinsertRestart →
        ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
          MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T →
          (∀ t ≤ T, (D.G t).m ≤ M₀) →
          (∀ t ≤ T, (D.G t).n ≤ N₀) →
          (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
          let A := algorithm2_dsWithFailureOwn cfg
          let κ := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
          let C_κ := 15 + 5 * C_γ
          let C_rt := 62 + 21 * C_γ + 4 * C_ψ + C_N
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
  obtain ⟨oracle, C_lsst, sparsify, params, hp_s, hp_t, C_γ, M_thresh,
      hLSST_spec, hSp_spec, hCγ, hMth, hAll⟩ :=
    concrete_theorem_5_1_with hDec hPaths C_D C_ψ C_N hCD hCψ hCN
  refine ⟨oracle, C_lsst, sparsify, params, hp_s, hp_t, C_γ, M_thresh,
    hLSST_spec, hSp_spec, hCγ, hMth, ?_⟩
  intro M₀ N₀ D_cap α Ψ ε hM₀1 hM₀ hN₀ hDcap hΨ hα B_cap cfg
    hT hMWU hEmb hNoReins D η isUpdate T hHist hmBound hnBound hConn
  obtain ⟨hKappaOwn, hWith⟩ := hAll M₀ N₀ D_cap α Ψ ε hM₀1 hM₀ hN₀ hDcap hΨ hα
    hT hMWU hEmb hNoReins
  simpa only [algorithm2_dsWithFailureOwn, algorithm2_dsOwn, alg2DetectSizeOwn] using
    hWith (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hKappaOwn.1 le_rfl
      hHist hmBound hnBound hConn

/-- Unconditional complexity / query instantiation of `concrete_theorem_5_1` requiring **only**
`IsSpecRestartNoHidden` (`ToolMWURestartNoHidden`, `ToolEmbedsSurvivingRestartNoHidden`,
`ToolNoReinsertRestartNoHidden`), with no global-`N₀` `hσL` assumption and no item-3
(`WeakHiddenClause3Hyps`) hypothesis. -/
theorem concrete_theorem_5_1_noHidden
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst C_sp K_s K_t : ℝ)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (hCsp : 0 < C_sp) (hKs : 0 ≤ K_s) (hKt : 0 ≤ K_t)
    (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧
      (params m).K_t = K_t ∧ (params m).p_t = 1 ∧
      (params m).γ_ℓ ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params m).γ_c ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    (C_D C_ψ C_N : ℝ) (hCD : 0 ≤ C_D) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N) :
    ∃ (C_γ : ℝ) (M_thresh : ℕ), 3 ≤ C_γ ∧ 2 ≤ M_thresh ∧
      ∀ (M₀ N₀ D_cap : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
        M_thresh ≤ M₀ →
        1 + Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2) →
        (D_cap : ℝ) ≤ Real.exp (C_D * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        alg2PsiGame Ψ M₀ ≤ Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        0 < α →
        let B_cap := concreteBCap C_lsst Ψ M₀ N₀ hM₀1
        let cfg := concreteAlg2Cfg oracle C_lsst sparsify params
          (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1)
          M₀ N₀ B_cap D_cap hM₀1 α Ψ ε
        cfg.T.IsSpecRestartNoHidden cfg.TP →
        cfg.T.ToolMWURestartNoHidden cfg.σ_mwu →
        cfg.T.ToolEmbedsSurvivingRestartNoHidden →
        cfg.T.ToolNoReinsertRestartNoHidden →
        ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
          MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T →
          (∀ t ≤ T, (D.G t).m ≤ M₀) →
          (∀ t ≤ T, (D.G t).n ≤ N₀) →
          let A := algorithm2_dsWithFailureOwn cfg
          let κ := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
          let C_κ := 15 + 5 * C_γ
          let C_rt := 62 + 21 * C_γ + 4 * C_ψ + C_N
          let f := alg2TimeFactor C_rt (47 / 48)
          let st := minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate T
          let Q_upd := alg2UpdateQueries D isUpdate T
          let K_upd := alg2UpdateCount isUpdate T
          let Q_det := alg2DetectSizeOwn cfg D η isUpdate T
          let K_det := alg2DetectCount isUpdate T
          let Q_tot := (M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
          (0 < κ ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ) ∧
          (∀ t ≤ T,
            A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) =
              (minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate t).flow) ∧
          ((st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
            f M₀ * Q_tot + 40 * (Q_upd : ℝ) * Real.log ((M₀ : ℝ) + (Q_upd : ℝ) + 2)) := by
  obtain ⟨C_γ, M_thresh, hCγ_ge, hMth2, hAll⟩ :=
    concrete_params_asymptotics C_lsst C_sp K_s K_t hCsp hKs hKt params hp_spec C_D C_ψ C_N hCD hCψ hCN
  refine ⟨14 * C_γ + 2, M_thresh, by linarith, hMth2,
    fun M₀ N₀ D_cap α Ψ ε hM₀1 hM₀ hN₀ hDcap hΨ hα => ?_⟩
  intro B_cap cfg hT hMWU hEmb hNoReins D η isUpdate T hHist hmBound hnBound
  have hB := hAll oracle sparsify M₀ N₀ D_cap α Ψ ε hM₀1 hM₀ hN₀ hDcap hΨ
  rcases hB with ⟨hTP, hLP, hD, hσ_mono, hσ_nn, _, hγℓ, hγr, hσT, hσM, hcT, hcL, hlogF, hγM₀, hγk, hσL_own⟩
  have hVNH : cfg.ValidNoHidden :=
    { hTP := hTP
      hLP := hLP
      hT := hT
      hL := lastLevelTool_isSpec oracle C_lsst hLSST
      hσ_mwu_mono := hσ_mono
      hσ_mwu_nn := hσ_nn
      hMWU := hMWU
      hEmb := hEmb
      hNoReins := hNoReins
      hγM₀ := hγM₀
      hγk := hγk
      hα := hα }
  have hCol := theorem_5_1_collapsed_with (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)
    hVNH (η := η) hHist hmBound hnBound
  have hM₀_eq : cfg.P.M₀ = M₀ := rfl
  have hN₀_eq : cfg.N₀ = N₀ := rfl
  have ha_eq : ((1 : ℝ) + 23 / 24) / 2 = 47 / 48 := by norm_num
  have hCγ_le : C_γ ≤ 14 * C_γ + 2 := by linarith
  have hγℓ' : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp ((14 * C_γ + 2) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) :=
    le_trans hγℓ (exp_23_24_mono_LL hCγ_le hM₀1)
  have hγr' : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp ((14 * C_γ + 2) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) :=
    le_trans hγr (exp_23_24_mono_LL hCγ_le hM₀1)
  have hσT' : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp ((14 * C_γ + 2) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ (((1 : ℝ) + 23 / 24) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := by
    rw [ha_eq]; exact le_trans hσT (exp_47_48_mono_LL hCγ_le hM₀1)
  have hσL' : cfg.LP.σ_last (levelM cfg.TP cfg.P cfg.P.d + 1) ≤
      Real.exp ((14 * C_γ + 2) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ (((1 : ℝ) + 23 / 24) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := by
    rw [ha_eq]; exact hσL_own
  have hσM' : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp ((14 * C_γ + 2) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) :=
    le_trans hσM (exp_23_24_mono_LL hCγ_le hM₀1)
  have hcT' : cfg.TP.c_T ≤
      Real.exp ((14 * C_γ + 2) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) :=
    le_trans hcT (exp_23_24_mono_LL hCγ_le hM₀1)
  have hcL' : cfg.LP.c_last ≤
      Real.exp ((14 * C_γ + 2) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) :=
    le_trans hcL (exp_23_24_mono_LL hCγ_le hM₀1)
  have hlogF' : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp ((14 * C_γ + 2) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ (((1 : ℝ) + 23 / 24) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := by
    rw [ha_eq]; exact le_trans hlogF (exp_47_48_mono_LL hCγ_le hM₀1)
  have hΨ' : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := hΨ
  have hN₀' : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2) := hN₀
  have hAsymp := theorem_5_1_asymptotic_exponents_own (by norm_num : (0 : ℝ) < 23 / 24)
    (by norm_num : (23 : ℝ) / 24 < 1) cfg.P.hM₀ hD hTP hLP (by linarith) hCψ hCN
    hγℓ' hγr' hσT' hσL' hσM' hcT' hcL' hΨ' hlogF' hN₀'
  dsimp only at hAsymp
  have hκ_pos : 0 < alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ :=
    alg2KappaAt_pos hVNH (levelM cfg.TP cfg.P cfg.P.d + 1)
  have hκ_lo : alg2KappaLower (15 + 5 * (14 * C_γ + 2)) (47 / 48) M₀ ≤
      alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ := by
    have hinv : (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)⁻¹ ≤
        Real.exp ((15 + 5 * (14 * C_γ + 2)) * (Real.log ((M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) := by
      simpa only [one_div, ha_eq, hM₀_eq, mul_assoc] using hAsymp.1
    simpa only [alg2KappaLower, Real.exp_neg, mul_assoc] using inv_le_of_inv_le₀ hκ_pos hinv
  have hf_col : alg2CollapsedFactor cfg ≤
      alg2TimeFactor (62 + 21 * (14 * C_γ + 2) + 4 * C_ψ + C_N) (47 / 48) M₀ := by
    simpa only [alg2TimeFactor, ha_eq, hM₀_eq, mul_assoc] using hAsymp.2
  refine ⟨⟨hκ_pos, hκ_lo⟩, fun t _ => by
    change (algorithm2_dsWithFailureWith cfg (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)).query
        (MinCostFlow.IPM.minRatioState
          (algorithm2_dsWithFailureWith cfg (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)).eraseFailure
          D η isUpdate t) = _
    rw [algorithm2_eraseFailure_state_eq_with]; rfl, ?_⟩
  have hQ_nn : (0 : ℝ) ≤ (M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
      (alg2UpdateCount isUpdate T : ℝ) + (alg2DetectSizeOwn cfg D η isUpdate T : ℝ) +
      (alg2DetectCount isUpdate T : ℝ) := by positivity
  have hCol1 : ((minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate T).chain.totalRuntime : ℝ) +
        alg2LctAmortizedCharge N₀
          ((minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate T).lctUpdateOps +
           (minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate T).lctDetectOps) ≤
      alg2CollapsedFactor cfg * ((M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
          (alg2UpdateCount isUpdate T : ℝ) + (alg2DetectSizeOwn cfg D η isUpdate T : ℝ) +
          (alg2DetectCount isUpdate T : ℝ)) +
        40 * (alg2UpdateQueries D isUpdate T : ℝ) *
          Real.log ((M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) + 2) := hCol.1
  calc (minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate T).chain.totalRuntime +
        alg2LctAmortizedCharge N₀
          ((minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate T).lctUpdateOps +
           (minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate T).lctDetectOps)
      ≤ alg2CollapsedFactor cfg * ((M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
          (alg2UpdateCount isUpdate T : ℝ) + (alg2DetectSizeOwn cfg D η isUpdate T : ℝ) +
          (alg2DetectCount isUpdate T : ℝ)) +
        40 * (alg2UpdateQueries D isUpdate T : ℝ) *
          Real.log ((M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) + 2) := hCol1
    _ ≤ alg2TimeFactor (62 + 21 * (14 * C_γ + 2) + 4 * C_ψ + C_N) (47 / 48) M₀ *
          ((M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
          (alg2UpdateCount isUpdate T : ℝ) + (alg2DetectSizeOwn cfg D η isUpdate T : ℝ) +
          (alg2DetectCount isUpdate T : ℝ)) +
        40 * (alg2UpdateQueries D isUpdate T : ℝ) *
          Real.log ((M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) + 2) :=
        add_le_add (mul_le_mul_of_nonneg_right hf_col hQ_nn) le_rfl

private lemma concreteBCap_eq (C_lsst Ψ : ℝ) (M₀ N₀ B_cap D_cap : ℕ) (hM₀ : 1 ≤ M₀)
    (params : ℕ → DynSpanner.SparsifyParams) (hp_s : ∀ m, (params m).p_s ≤ 1)
    (hp_t : ∀ m, (params m).p_t ≤ 1) :
    let P := concreteChainParams M₀ hM₀
    let TP := sparseCoreParams (concreteEnv C_lsst params hp_s hp_t M₀ B_cap D_cap)
    Nat.ceil ((2 * max 0 Ψ + (P.d : ℝ) * Real.log (max (2 : ℝ) (TP.σ P.k N₀))) / Real.log 2) + 2 =
      concreteBCap C_lsst Ψ M₀ N₀ hM₀ := rfl

/-- Complete bridge on `ChainInv` for `concreteAlg2Cfg` across **all levels `0 ≤ i < cfg.P.d`**:
combining `LSF.theorem_2_2` (`hLSST`), `Expander.theorem_8_1_concrete` (`hSp`), and
`LevelInvariants` (`hComp_bound` with `c_n = 1` from connectedness, and `hB_bound` from
level-`0` length bounds), every level `i < cfg.P.d` satisfies `SparseCoreInstanceHyps` up to the
degree hypothesis `hDeg`, while at level `P.d` connectedness gives
`(st.G cfg.P.d).n ≤ levelM cfg.TP cfg.P cfg.P.d + 1`. -/
theorem concrete_level_instanceHyps_all_levels
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (hSp : ∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify)
    (M₀ N₀ D_cap : ℕ) (hM₀ : 1 ≤ M₀) (α Ψ ε : ℝ) :
    let B_cap := concreteBucketCap ⌈C_lsst⌉₊ ⌈Ψ⌉₊ (concreteChainParams M₀ hM₀).k
      (concreteChainParams M₀ hM₀).d N₀
    let E := concreteEnv C_lsst params hp_s hp_t M₀ B_cap D_cap
    let cfg := concreteAlg2Cfg oracle C_lsst sparsify params hp_s hp_t
      M₀ N₀ B_cap D_cap hM₀ α Ψ ε
    cfg.TP.γ_ℓ (M₀ ^ 2) ≤ M₀ →
    cfg.TP.γ_ℓ (M₀ ^ 2) ≤ cfg.P.k →
    cfg.T.IsSpecRestartNoHidden cfg.TP →
    ∀ {st : ChainState cfg.T cfg.P},
      ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P N₀ st →
      (∀ u ∈ (st.G 0).V, ∀ v ∈ (st.G 0).V, (st.G 0).Connected u v) →
      (∀ e ∈ (st.G 0).E, Real.exp (-max 0 Ψ) ≤ st.ℓ e ∧ st.ℓ e ≤ Real.exp (max 0 Ψ)) →
      (∀ i < cfg.P.d, (st.G i).maxDeg ≤ D_cap ∧
        ∀ j < cfg.P.k,
          let cs₀ := initCompLSF oracle C_lsst (st.G i) (st.toTreeChain.chainLen st.ℓ i) cfg.P.k j
          (components (st.G i)).sup (fun C => (initTildeState (cs₀.compSt C)).C.maxDeg) ≤ D_cap) →
      (∀ i < cfg.P.d,
        let D_i : DynamicInstance :=
          { G := fun _ => st.G i
            U := fun _ => []
            ℓ := fun _ => st.toTreeChain.chainLen st.ℓ i
            g := fun _ => st.toTreeChain.chainGrad st.g i }
        SparseCoreInstanceHyps E oracle (fun _ => sparsify) cfg.P.k 0 D_i) ∧
      (st.G cfg.P.d).n ≤ levelM cfg.TP cfg.P cfg.P.d + 1 := by
  intro B_cap E cfg hγM₀ hγk hT st hInv hConn0 hℓ0 hDeg
  have hM₀_eq : cfg.P.M₀ = M₀ := rfl
  have hγM₀' : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.M₀ := by simpa only [hM₀_eq] using hγM₀
  have hγk' : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k := by simpa only [hM₀_eq] using hγk
  have hTP : cfg.TP.Valid := sparseCoreParams_valid E
  have hLvl := level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P N₀ hTP hT hγM₀' hγk' hInv
  have hCompAll := chainInv_comp_bound_all_levels hTP hT hγM₀' hγk' hInv hConn0
  have hσ_eq : ∀ k n, cfg.TP.σ k n = max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log ((n : ℝ) + 2)) ^ 6) :=
    fun _ _ => rfl
  have hBAll := chainInv_bucket_bound_all_levels oracle hLSST hTP hT hσ_eq hγM₀' hγk' hInv
    (le_max_left 0 Ψ) hℓ0
  have hB_le : Nat.ceil ((2 * max 0 Ψ + (cfg.P.d : ℝ) * Real.log (max (2 : ℝ) (cfg.TP.σ cfg.P.k N₀))) / Real.log 2) + 2 ≤ B_cap := by
    have h1 : cfg.P = concreteChainParams M₀ hM₀ := rfl
    have h2 : cfg.TP = sparseCoreParams E := rfl
    rw [h1, h2]
    rw [concreteBCap_eq C_lsst Ψ M₀ N₀ B_cap D_cap hM₀ params hp_s hp_t]
    exact concreteBCap_le_bucketCap_ceil C_lsst Ψ M₀ N₀ hM₀
  refine ⟨fun i hi => ?_, hCompAll.2⟩
  have hk_pos : (0 : ℝ) < cfg.P.k := Nat.cast_pos.mpr cfg.P.hk
  have hm_le_sq : (st.G i).m ≤ M₀ ^ 2 := by
    have h1 : (st.G i).m ≤ levelM cfg.TP cfg.P i := by
      exact_mod_cast (hLvl i (Nat.le_of_lt hi)).2.2.1
    exact le_trans h1 (levelM_le_sq hTP hγM₀' hγk' i)
  exact
    { hLSST := hLSST
      hSp := sparsifySpec_mono_mMax hm_le_sq (hSp (M₀ ^ 2))
      hB_bound := fun j hj C hC => by
        have hb := hBAll i hi j hj C hC
        exact hb.trans (hB_le.trans (le_max_right 1 B_cap))
      hDeg_bound := ⟨(hDeg i hi).1, (hDeg i hi).2⟩
      hComp_bound := by
        change ((st.G i).n : ℝ) ≤ 1 * (((st.G i).m : ℝ) + 1)
        exact hCompAll.1 i (Nat.le_of_lt hi) }

end MainInstantiations

end MinCostFlow.Chain
