module

public import MinCostFlow.Chain.Ordered.ConcreteBounds
public import MinCostFlow.Chain.Ordered.RestartSpecOn
import MinCostFlow.Chain.Ordered.Theorem5_1
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Small-`κ` Concrete Instantiation of Ordered `Theorem 5.1`

Proves `concrete_theorem_5_1_with_last_core`, `concrete_theorem_5_1_with_last`, and
`concrete_theorem_5_1_with` for the degree-free ordered bundle chain with the machine-cost tool
(`sparseCoreBundleRestartToolMachWith lsfInit` and `bundleCoreParamsMach`), for any LSF
initializer that fits `C_lsst` (`IsConcreteLSFInit`). The existential forms take the online
initializer `initLSFOnline oracle C_lsst` of `theorem_2_2`'s oracle
(`isConcreteLSFInit_initLSFOnline`).

The proof is in `concrete_theorem_5_1_with_last_core_uniform`. It picks the constants `C_γ` and
`M_thresh` before the initializer, since `concrete_params_asymptotics_with_last` does not depend on
it. So one pair of constants serves a whole family of initializers at one `C_lsst`, such as one
initializer for each number format.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.Expander MinCostFlow.Bundle

section OconcWithHelpers

private lemma oconc_alg2KappaOwn_pos {cfg : Alg2Config} (hTP : cfg.TP.Valid) :
    0 < alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ := by
  refine kappaBound_pos (hTP.2.2.1 (cfg.P.M₀ ^ 2)) ?_ (le_max_left _ _)
  exact le_trans zero_le_one (le_max_of_le_left (hTP.1 cfg.P.k cfg.N₀ cfg.P.hk))

/-- From `1 ≤ γ ≤ exp(C a c)` with `1 ≤ a` and `1 ≤ c`, the ceiling of `γ` is at least `1` and
at most `exp((C + 1) a c)`: `⌈γ⌉ < γ + 1 ≤ 2 γ`, and `2 ≤ 1 + a c ≤ exp(a c)`. -/
private lemma oconc_ceil_le_exp {γ C a c : ℝ} (h1 : 1 ≤ γ) (hγ : γ ≤ Real.exp (C * a * c))
    (ha : 1 ≤ a) (hc : 1 ≤ c) :
    1 ≤ ⌈γ⌉₊ ∧ (⌈γ⌉₊ : ℝ) ≤ Real.exp ((C + 1) * a * c) := by
  refine ⟨Nat.one_le_ceil_iff.mpr (by linarith), ?_⟩
  have hac : 1 ≤ a * c := one_le_mul_of_one_le_of_one_le ha hc
  have h2 : 2 ≤ Real.exp (a * c) := by linarith [Real.add_one_le_exp (a * c)]
  have hceil : (⌈γ⌉₊ : ℝ) < γ + 1 := Nat.ceil_lt_add_one (by linarith)
  have hsplit : Real.exp ((C + 1) * a * c) = Real.exp (C * a * c) * Real.exp (a * c) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  nlinarith [Real.exp_pos (C * a * c)]

end OconcWithHelpers

section MainInstantiationsWith

/-- Core small-`κ` concrete instantiation of ordered Theorem 5.1 (page 15), with the constants
`C_γ` and `M_thresh` chosen before the LSF initializer: one pair serves every `lsfInit` that fits
`C_lsst` (`IsConcreteLSFInit`). The constants come from `concrete_params_asymptotics_with_last`,
which does not see the initializer. This is what a family of initializers indexed by the number
format needs.

Besides the conclusion of Theorem 5.1, it gives two facts that its proof builds: the validity
`cfg.ValidOrd` of the configuration, and the bound `1 ≤ ⌈γ_r(M₀²)⌉ ≤ exp((C_γ + 1) L^{23/24}
log(L + 2))` with `L = log(M₀ + 2)`, from `γ_r(M₀²) ≤ exp(C_γ L^{23/24} log(L + 2))` and
`oconc_ceil_le_exp`. -/
theorem concrete_theorem_5_1_with_last_core_uniform
    (C_lsst : ℝ)
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
    (hSp : ∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify)
    (C_ψ C_N : ℝ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (integerBuckets : Bool := false) (spanConst : ℕ := 1) (hConst : 1 ≤ spanConst := by omega) :
    ∃ (C_γ : ℝ) (M_thresh : ℕ),
      3 ≤ C_γ ∧ 2 ≤ M_thresh ∧
      ∀ (lsfInit : LSFInit), IsConcreteLSFInit lsfInit C_lsst →
      ∀ (M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
        M_thresh ≤ M₀ →
        1 + Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2) →
        alg2PsiGame Ψ M₀ ≤ Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        0 < α →
        let B_cap := concreteBucketCapacity integerBuckets C_lsst Ψ M₀ N₀ hM₀1
        let cfg := concreteAlg2CfgWithLast lsfInit C_lsst lastTool C_last sparsify params
          (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1)
          M₀ N₀ B_cap hM₀1 α Ψ ε spanConst
        cfg.T.ToolEmbedsSurvivingOrdRestart →
        cfg.T.ToolNoReinsertOrdRestart →
        cfg.ValidOrd ∧
        (1 ≤ ⌈cfg.TP.γ_r (cfg.P.M₀ ^ 2)⌉₊ ∧
          (⌈cfg.TP.γ_r (cfg.P.M₀ ^ 2)⌉₊ : ℝ) ≤
            Real.exp ((C_γ + 1) * Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
              Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2))) ∧
        (let κ_own := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
        let C_κ := 15 + 5 * C_γ
        (0 < κ_own ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ_own) ∧
        ∀ (κ : ℝ), 0 < κ → κ ≤ κ_own →
          ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
            MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T →
            HistoryEdgeOnly D T →
            HistoryLengthsInRange D T Ψ →
            (∀ t ≤ T, (D.G t).m ≤ M₀) →
            (∀ t ≤ T, (D.G t).n ≤ N₀) →
            (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
            let A := algorithm2_dsWithFailureWith cfg κ
            let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
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
                  f M₀ * Q_tot))) := by
  obtain ⟨C_γ, M_thresh, hCγ_ge, hMth2, hAll⟩ :=
    concrete_params_asymptotics_with_last C_lsst C_last C_sp K_s K_t hCsp hKs hKt params hp_spec
      C_ψ C_N hCψ hCN integerBuckets spanConst
  refine ⟨14 * C_γ + 2, M_thresh, by linarith, hMth2, ?_⟩
  intro lsfInit hInit M₀ N₀ α Ψ ε hM₀1 hM₀ hN₀ hΨ hα B_cap cfg
    hEmb hNoReins
  have hB := hAll lsfInit lastTool sparsify M₀ N₀ α Ψ ε hM₀1 hM₀ hN₀ hΨ
  rcases hB with ⟨hTP, hLP, hD, hσ_mono, hσ_nn, _, hγℓ, hγr, hσT, hσM, hcT, hcL, hlogF, hγM₀, hγk, hσL_own⟩
  have hT : ChainToolSupply cfg.T cfg.TP cfg.P cfg.N₀ (max 0 cfg.Ψ) :=
    concreteChainToolSupply_withLast_of_cap lsfInit C_lsst hInit lastTool C_last sparsify params
      (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1) hSp
      (fun m n ψ hm => concreteBucketCapacity integerBuckets C_lsst ψ m n hm)
      (fun m n ψ hm => by
        cases integerBuckets
        · exact le_rfl
        · exact concreteBCap_le_bucketCap_ceil C_lsst ψ m n hm)
      M₀ N₀ α Ψ ε hM₀1 spanConst hConst hγM₀ hγk
  have hMWU : cfg.T.ToolMWUOrdRestartNoHiddenLe cfg.σ_mwu (cfg.P.M₀ ^ 2) :=
    concreteRestartMWULe lsfInit C_lsst hInit lastTool C_last sparsify params
      (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1)
      M₀ N₀ B_cap hM₀1 α Ψ ε spanConst
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
  have hΓ := oconc_ceil_le_exp (hTP.2.2.2.2.2.2.1 (cfg.P.M₀ ^ 2)) hγr'
    (Real.one_le_rpow (one_le_log_add_two_of_one hM₀1) (by norm_num)) (one_le_LL_of_one hM₀1)
  refine ⟨hV, hΓ, ?_, fun κ hκ_pos hκ_le D η isUpdate T hHist hEdge hLen hmBound hnBound hConn => ?_⟩
  · have ha_eq : ((1 : ℝ) + (23 : ℝ) / 24) / 2 = 47 / 48 := by norm_num
    have hAsymp := theorem_5_1_asymptotic_exponents_own (by norm_num : (0 : ℝ) < 23 / 24)
      (by norm_num : (23 : ℝ) / 24 < 1) cfg.P.hM₀ hD hTP hLP (by linarith) hCψ hCN
      hγℓ' hγr' (by rwa [ha_eq]) (by rwa [ha_eq]) hσM' hcT' hcL' hΨ (by rwa [ha_eq]) hN₀
    dsimp only at hAsymp
    have hκ_pos := oconc_alg2KappaOwn_pos hTP
    have hM₀_eq : cfg.P.M₀ = M₀ := rfl
    have hinv : (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)⁻¹ ≤
        Real.exp ((15 + 5 * (14 * C_γ + 2)) * (Real.log ((M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) := by
      simpa only [one_div, ha_eq, hM₀_eq, mul_assoc] using hAsymp.1
    exact ⟨hκ_pos, by simpa only [alg2KappaLower, Real.exp_neg, mul_assoc] using inv_le_of_inv_le₀ hκ_pos hinv⟩
  · exact theorem_5_1_relaxed_own_with κ hV hκ_pos hκ_le hD (by linarith) hCψ hCN
      hγℓ' hγr' hσT' hσL' hσM' hcT' hcL' hΨ hlogF' hN₀ hHist hEdge hLen hmBound hnBound hConn

/-- Core small-`κ` concrete instantiation of ordered `Theorem 5.1` (`concrete_theorem_5_1_with_last`),
parameterized by an arbitrary `lastTool`, LSF initializer `lsfInit`, and `sparsify`, with no
degree-cap parameter. It is `concrete_theorem_5_1_with_last_core_uniform` at one initializer. -/
theorem concrete_theorem_5_1_with_last_core
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
    (C_ψ C_N : ℝ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (integerBuckets : Bool := false) :
    ∃ (C_γ : ℝ) (M_thresh : ℕ),
      3 ≤ C_γ ∧ 2 ≤ M_thresh ∧
      ∀ (M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
        M_thresh ≤ M₀ →
        1 + Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2) →
        alg2PsiGame Ψ M₀ ≤ Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        0 < α →
        let B_cap := concreteBucketCapacity integerBuckets C_lsst Ψ M₀ N₀ hM₀1
        let cfg := concreteAlg2CfgWithLast lsfInit C_lsst lastTool C_last sparsify params
          (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1)
          M₀ N₀ B_cap hM₀1 α Ψ ε
        cfg.T.ToolEmbedsSurvivingOrdRestart →
        cfg.T.ToolNoReinsertOrdRestart →
        let κ_own := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
        let C_κ := 15 + 5 * C_γ
        (0 < κ_own ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ_own) ∧
        ∀ (κ : ℝ), 0 < κ → κ ≤ κ_own →
          ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
            MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T →
            HistoryEdgeOnly D T →
            HistoryLengthsInRange D T Ψ →
            (∀ t ≤ T, (D.G t).m ≤ M₀) →
            (∀ t ≤ T, (D.G t).n ≤ N₀) →
            (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
            let A := algorithm2_dsWithFailureWith cfg κ
            let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
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
  obtain ⟨C_γ, M_thresh, hCγ, hMth, hAll⟩ :=
    concrete_theorem_5_1_with_last_core_uniform C_lsst lastTool C_last hLast sparsify params
      C_sp K_s K_t hCsp hKs hKt hp_spec hSp C_ψ C_N hCψ hCN integerBuckets
  refine ⟨C_γ, M_thresh, hCγ, hMth, ?_⟩
  intro M₀ N₀ α Ψ ε hM₀1 hM₀ hN₀ hΨ hα B_cap cfg hEmb hNoReins
  exact (hAll lsfInit hInit M₀ N₀ α Ψ ε hM₀1 hM₀ hN₀ hΨ hα hEmb hNoReins).2.2

/-- Generalization of `concrete_theorem_5_1_with` to an arbitrary last-level tool
`lastTool : LastLevelTool` satisfying `lastTool.IsSpec (lastLevelParams C_last)`, with no
degree-cap parameter. -/
theorem concrete_theorem_5_1_with_last
    (hDec : Cited.ExpanderDecomposition)
    (hPaths : Cited.DecrementalExpanderPaths)
    (lastTool : LastLevelTool) (C_last : ℝ)
    (hLast : lastTool.IsSpec (lastLevelParams C_last))
    (C_ψ C_N : ℝ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (integerBuckets : Bool := false) :
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
        let B_cap := concreteBucketCapacity integerBuckets C_lsst Ψ M₀ N₀ hM₀1
        let cfg := concreteAlg2CfgWithLast lsfInit C_lsst lastTool C_last sparsify params hp_s hp_t
          M₀ N₀ B_cap hM₀1 α Ψ ε
        cfg.T.ToolEmbedsSurvivingOrdRestart →
        cfg.T.ToolNoReinsertOrdRestart →
        let κ_own := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
        let C_κ := 15 + 5 * C_γ
        (0 < κ_own ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ_own) ∧
        ∀ (κ : ℝ), 0 < κ → κ ≤ κ_own →
          ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
            MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T →
            HistoryEdgeOnly D T →
            HistoryLengthsInRange D T Ψ →
            (∀ t ≤ T, (D.G t).m ≤ M₀) →
            (∀ t ≤ T, (D.G t).n ≤ N₀) →
            (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
            let A := algorithm2_dsWithFailureWith cfg κ
            let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
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
    concrete_theorem_5_1_with_last_core (initLSFOnline oracle C_lsst) C_lsst lastTool C_last hLast
      sparsify params C_sp K_s K_t hCsp hKs hKt hp_spec (isConcreteLSFInit_initLSFOnline hLSST_spec)
      (fun mMax => (h81 mMax).2.2.2.2.2.2) C_ψ C_N hCψ hCN integerBuckets
  refine ⟨initLSFOnline oracle C_lsst, C_lsst, sparsify, params, fun m => le_of_eq (h81 m).2.1,
    fun m => le_of_eq (h81 m).2.2.2.1, C_γ, M_thresh, isConcreteLSFInit_initLSFOnline hLSST_spec,
    fun mMax => (h81 mMax).2.2.2.2.2.2, hCγ, hMth, hAll⟩

/-- Small-`κ` concrete instantiation of ordered `Theorem 5.1` for `algorithm2_dsWithFailureWith`
and `concreteAlg2Cfg` (`lastLevelTool oracle C_lsst`, `C_last = C_lsst`), with no degree-cap
parameter. -/
theorem concrete_theorem_5_1_with
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
        let κ_own := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
        let C_κ := 15 + 5 * C_γ
        (0 < κ_own ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ_own) ∧
        ∀ (κ : ℝ), 0 < κ → κ ≤ κ_own →
          ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
            MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T →
            HistoryEdgeOnly D T →
            HistoryLengthsInRange D T Ψ →
            (∀ t ≤ T, (D.G t).m ≤ M₀) →
            (∀ t ≤ T, (D.G t).n ≤ N₀) →
            (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
            let A := algorithm2_dsWithFailureWith cfg κ
            let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
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
    concrete_theorem_5_1_with_last_core (initLSFOnline oracle C_lsst) C_lsst
      (lastLevelTool oracle C_lsst) C_lsst (lastLevelTool_isSpec oracle C_lsst hLSST_spec) sparsify
      params C_sp K_s K_t hCsp hKs hKt hp_spec (isConcreteLSFInit_initLSFOnline hLSST_spec)
      (fun mMax => (h81 mMax).2.2.2.2.2.2) C_ψ C_N hCψ hCN false
  refine ⟨initLSFOnline oracle C_lsst, oracle, C_lsst, sparsify, params,
    fun m => le_of_eq (h81 m).2.1, fun m => le_of_eq (h81 m).2.2.2.1, C_γ, M_thresh,
    isConcreteLSFInit_initLSFOnline hLSST_spec, hLSST_spec,
    fun mMax => (h81 mMax).2.2.2.2.2.2, hCγ, hMth, hAll⟩

end MainInstantiationsWith

end MinCostFlow.Chain.Ordered
