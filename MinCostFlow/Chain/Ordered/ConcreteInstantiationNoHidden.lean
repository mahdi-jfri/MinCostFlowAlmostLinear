module

public import MinCostFlow.Chain.Ordered.ConcreteBounds
public import MinCostFlow.Chain.Ordered.RestartSpecOn
public import MinCostFlow.Chain.LevelConnected
import MinCostFlow.Chain.Ordered.Theorem5_1Asymptotics
import MinCostFlow.Chain.Ordered.RebuildCollapse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Concrete No-Hidden Instantiation and All-Levels `BundleInstanceHyps` Bridge

Companion to `MinCostFlow.Chain.Ordered.ConcreteInstantiation`, proving:
1. `concrete_theorem_5_1_noHidden`: unconditional complexity / query instantiation of ordered
   `Theorem 5.1`. The restricted tool spec and the MWU bound are proved inside from
   `concreteChainToolSupply_withLast_of_cap` and `concreteRestartMWULe`. The lengths of the
   history must lie in `[e^{-Ψ}, e^Ψ]`.
2. `concrete_level_instanceHyps_all_levels`: complete bridge on the ordered `ChainInv` for
   `concreteAlg2Cfg` across all levels `0 ≤ i < cfg.P.d`, discharging **all** fields of
   `BundleCoreHypsAtWith` (initializer validity, `hSp`, `hB_bound`) and the component bound
   `n ≤ m + 1` with no degree hypothesis at all, plus the level-`d` vertex bound
   `(st.G cfg.P.d).n ≤ levelM cfg.TP cfg.P cfg.P.d + 1`.

The core tool is `sparseCoreBundleRestartToolMachWith lsfInit` for an initializer that fits
`C_lsst` (`IsConcreteLSFInit`); the oracle is used only by the last level.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.Expander MinCostFlow.Bundle

section OconcNoHidden

private lemma oconc_eraseFailure_state_eq_with (cfg : Alg2Config) (κ : ℝ) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t : ℕ) :
    MinCostFlow.IPM.minRatioState (algorithm2_dsWithFailureWith cfg κ).eraseFailure D η isUpdate t =
      minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (if isUpdate (t + 1) then
        ((algorithm2_dsWithFailureWith cfg κ).update
          (MinCostFlow.IPM.minRatioState (algorithm2_dsWithFailureWith cfg κ).eraseFailure D η isUpdate t)
          (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))).1
      else ((algorithm2_dsWithFailureWith cfg κ).detect
        (MinCostFlow.IPM.minRatioState (algorithm2_dsWithFailureWith cfg κ).eraseFailure D η isUpdate t)).2) = _
    rw [ih]
    rfl

private lemma oconc_alg2KappaOwn_pos_nh {cfg : Alg2Config} (hTP : cfg.TP.Valid) :
    0 < alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ := by
  refine kappaBound_pos (hTP.2.2.1 (cfg.P.M₀ ^ 2)) ?_ (le_max_left _ _)
  exact le_trans zero_le_one (le_max_of_le_left (hTP.1 cfg.P.k cfg.N₀ cfg.P.hk))

/-- Unconditional complexity / query instantiation of ordered `concrete_theorem_5_1`. It asks only
for `ToolEmbedsSurvivingOrdRestartNoHidden` and `ToolNoReinsertOrdRestartNoHidden` of the tool,
and for lengths in `[e^{-Ψ}, e^Ψ]` along the history. -/
theorem concrete_theorem_5_1_noHidden
    (lsfInit : LSFInit) (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst C_sp K_s K_t : ℝ)
    (hInit : IsConcreteLSFInit lsfInit C_lsst) (hLSST : HasLSSTSpec oracle C_lsst)
    (hCsp : 0 < C_sp) (hKs : 0 ≤ K_s) (hKt : 0 ≤ K_t)
    (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧
      (params m).K_t = K_t ∧ (params m).p_t = 1 ∧
      (params m).γ_ℓ ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params m).γ_c ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    (hSp : ∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify)
    (C_ψ C_N : ℝ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N) :
    ∃ (C_γ : ℝ) (M_thresh : ℕ), 3 ≤ C_γ ∧ 2 ≤ M_thresh ∧
      ∀ (M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
        M_thresh ≤ M₀ →
        1 + Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2) →
        alg2PsiGame Ψ M₀ ≤ Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        0 < α →
        let B_cap := concreteBCap C_lsst Ψ M₀ N₀ hM₀1
        let cfg := concreteAlg2Cfg lsfInit oracle C_lsst sparsify params
          (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1)
          M₀ N₀ B_cap hM₀1 α Ψ ε
        cfg.T.ToolEmbedsSurvivingOrdRestartNoHidden →
        cfg.T.ToolNoReinsertOrdRestartNoHidden →
        ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
          MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T →
          HistoryEdgeOnly D T →
          HistoryLengthsInRange D T Ψ →
          (∀ t ≤ T, (D.G t).m ≤ M₀) →
          (∀ t ≤ T, (D.G t).n ≤ N₀) →
          let A := algorithm2_dsWithFailureOwn cfg
          let κ := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
          let C_κ := 15 + 5 * C_γ
          let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
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
    concrete_params_asymptotics C_lsst C_sp K_s K_t hCsp hKs hKt params hp_spec C_ψ C_N hCψ hCN
  refine ⟨14 * C_γ + 2, M_thresh, by linarith, hMth2,
    fun M₀ N₀ α Ψ ε hM₀1 hM₀ hN₀ hΨ hα => ?_⟩
  intro B_cap cfg hEmb hNoReins D η isUpdate T hHist hEdge hLen hmBound hnBound
  have hB := hAll lsfInit oracle sparsify M₀ N₀ α Ψ ε hM₀1 hM₀ hN₀ hΨ
  rcases hB with ⟨hTP, hLP, hD, hσ_mono, hσ_nn, _, hγℓ, hγr, hσT, hσM, hcT, hcL, hlogF, hγM₀, hγk, hσL_own⟩
  have hT : ChainToolSupply cfg.T cfg.TP cfg.P cfg.N₀ (max 0 cfg.Ψ) :=
    concreteChainToolSupply_withLast_of_cap lsfInit C_lsst hInit (lastLevelTool oracle C_lsst) C_lsst
      sparsify params (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1)
      hSp (fun m n ψ hm => concreteBCap C_lsst ψ m n hm) (fun _ _ _ _ => le_rfl)
      M₀ N₀ α Ψ ε hM₀1 1 le_rfl hγM₀ hγk
  have hMWU : cfg.T.ToolMWUOrdRestartNoHiddenLe cfg.σ_mwu (cfg.P.M₀ ^ 2) :=
    concreteRestartMWULe lsfInit C_lsst hInit (lastLevelTool oracle C_lsst) C_lsst sparsify params
      (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1)
      M₀ N₀ B_cap hM₀1 α Ψ ε
  have hVNH : cfg.ValidOrdNoHidden :=
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
    hVNH (η := η) hHist hEdge hLen hmBound hnBound
  have hM₀_eq : cfg.P.M₀ = M₀ := rfl
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
  have hAsymp := theorem_5_1_asymptotic_exponents_own (by norm_num : (0 : ℝ) < 23 / 24)
    (by norm_num : (23 : ℝ) / 24 < 1) cfg.P.hM₀ hD hTP hLP (by linarith) hCψ hCN
    hγℓ' hγr' hσT' hσL' hσM' hcT' hcL' hΨ hlogF' hN₀
  dsimp only at hAsymp
  have hκ_pos : 0 < alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ :=
    oconc_alg2KappaOwn_pos_nh hTP
  have hκ_lo : alg2KappaLower (15 + 5 * (14 * C_γ + 2)) (47 / 48) M₀ ≤
      alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ := by
    have hinv : (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)⁻¹ ≤
        Real.exp ((15 + 5 * (14 * C_γ + 2)) * (Real.log ((M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) := by
      simpa only [one_div, ha_eq, hM₀_eq, mul_assoc] using hAsymp.1
    simpa only [alg2KappaLower, Real.exp_neg, mul_assoc] using inv_le_of_inv_le₀ hκ_pos hinv
  have hf_col : alg2CollapsedFactor cfg ≤
      alg2TimeFactor (theorem51RuntimeConstant (14 * C_γ + 2) C_ψ C_N) (47 / 48) M₀ := by
    simpa only [alg2TimeFactor, ha_eq, hM₀_eq, mul_assoc] using hAsymp.2
  refine ⟨⟨hκ_pos, hκ_lo⟩, fun t _ => by
    change (algorithm2_dsWithFailureWith cfg (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)).query
        (MinCostFlow.IPM.minRatioState
          (algorithm2_dsWithFailureWith cfg (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)).eraseFailure
          D η isUpdate t) = _
    rw [oconc_eraseFailure_state_eq_with]; rfl, ?_⟩
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
    _ ≤ alg2TimeFactor (theorem51RuntimeConstant (14 * C_γ + 2) C_ψ C_N) (47 / 48) M₀ *
          ((M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
          (alg2UpdateCount isUpdate T : ℝ) + (alg2DetectSizeOwn cfg D η isUpdate T : ℝ) +
          (alg2DetectCount isUpdate T : ℝ)) +
        40 * (alg2UpdateQueries D isUpdate T : ℝ) *
          Real.log ((M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) + 2) :=
        add_le_add (mul_le_mul_of_nonneg_right hf_col hQ_nn) le_rfl

private lemma oconc_chainInv_comp_bound_all_levels {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    (hConn0 : ∀ u ∈ (st.G 0).V, ∀ v ∈ (st.G 0).V, (st.G 0).Connected u v) :
    (∀ i ≤ P.d, ((st.G i).n : ℝ) ≤ (1 : ℝ) * (((st.G i).m : ℝ) + 1)) ∧
    (st.G P.d).n ≤ levelM TP P P.d + 1 := by
  have hLvl := level_bounds_aux_noHidden T L TP LP P N₀ hTP hγM₀ hγk hInv
  have hConnAll : ∀ i ≤ P.d,
      (∀ u ∈ (st.G i).V, ∀ v ∈ (st.G i).V, (st.G i).Connected u v) ∧
      (st.G i).n ≤ (st.G i).m + 1 := by
    intro i hi
    induction i with
    | zero => exact ⟨hConn0, connected_n_le_m_add_one (hLvl 0 (Nat.zero_le _)).1 hConn0⟩
    | succ i ih =>
      have hi_lt : i < P.d := hi
      obtain ⟨hConni, _⟩ := ih (Nat.le_of_lt hi_lt)
      have hBi := (hLvl i (Nat.le_of_lt hi_lt)).2.2.2.2 hi_lt (st.bran i) (hInv.hBran i hi_lt)
      have hConnsucc : ∀ u ∈ (st.G (i + 1)).V, ∀ v ∈ (st.G (i + 1)).V, (st.G (i + 1)).Connected u v := by
        rw [hInv.hGSucc i hi_lt]
        exact isSparsifiedCoreGraph_connected hBi.1 hBi.2 hConni
      exact ⟨hConnsucc, connected_n_le_m_add_one (hLvl (i + 1) hi).1 hConnsucc⟩
  refine ⟨fun i hi => ?_, ?_⟩
  · have hreal : ((st.G i).n : ℝ) ≤ ((st.G i).m : ℝ) + 1 := by exact_mod_cast (hConnAll i hi).2
    linarith
  · have hm_nat : (st.G P.d).m ≤ levelM TP P P.d := by exact_mod_cast (hLvl P.d le_rfl).2.2.1
    have hPd_nat : (st.G P.d).n ≤ (st.G P.d).m + 1 := (hConnAll P.d le_rfl).2
    omega

/-- Complete degree-free bridge on the ordered `ChainInv` for `concreteAlg2Cfg` across all levels
`0 ≤ i < cfg.P.d`: every level `i < cfg.P.d` satisfies **all** fields of `BundleInstanceHyps`
of `BundleCoreHypsAtWith` (initializer validity, `hSp`, `hB_bound`) at `M = (st.G i).m`, and the
component bound `n ≤ m + 1`, with no degree hypothesis; at level `P.d` connectedness gives
`(st.G cfg.P.d).n ≤ levelM cfg.TP cfg.P cfg.P.d + 1`. -/
theorem concrete_level_instanceHyps_all_levels
    (lsfInit : LSFInit) (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hInit : IsConcreteLSFInit lsfInit C_lsst)
    (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (hSp : ∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify)
    (M₀ N₀ : ℕ) (hM₀ : 1 ≤ M₀) (α Ψ ε : ℝ) :
    let B_cap := concreteBucketCap ⌈C_lsst⌉₊ ⌈Ψ⌉₊ (concreteChainParams M₀ hM₀).k
      (concreteChainParams M₀ hM₀).d N₀
    let E := concreteEnv C_lsst params hp_s hp_t M₀ B_cap
    let cfg := concreteAlg2Cfg lsfInit oracle C_lsst sparsify params hp_s hp_t
      M₀ N₀ B_cap hM₀ α Ψ ε
    cfg.TP.γ_ℓ (M₀ ^ 2) ≤ M₀ →
    cfg.TP.γ_ℓ (M₀ ^ 2) ≤ cfg.P.k →
    cfg.T.IsSpecOrdRestartNoHidden cfg.TP →
    ∀ {st : ChainState cfg.T cfg.P},
      ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P N₀ st →
      (∀ u ∈ (st.G 0).V, ∀ v ∈ (st.G 0).V, (st.G 0).Connected u v) →
      (∀ e ∈ (st.G 0).E, Real.exp (-max 0 Ψ) ≤ st.ℓ e ∧ st.ℓ e ≤ Real.exp (max 0 Ψ)) →
      (∀ i < cfg.P.d,
        let D_i : DynamicInstance :=
          { G := fun _ => st.G i
            U := fun _ => []
            ℓ := fun _ => st.toTreeChain.chainLen st.ℓ i
            g := fun _ => st.toTreeChain.chainGrad st.g i }
        BundleCoreHypsAtWith E lsfInit (fun _ => sparsify) cfg.P.k (st.G i).m D_i ∧
          ((st.G i).n : ℝ) ≤ E.c_n * (((st.G i).m : ℝ) + 1)) ∧
      (st.G cfg.P.d).n ≤ levelM cfg.TP cfg.P cfg.P.d + 1 := by
  intro B_cap E cfg hγM₀ hγk hT st hInv hConn0 hℓ0
  have hM₀_eq : cfg.P.M₀ = M₀ := rfl
  have hγM₀' : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.M₀ := by simpa only [hM₀_eq] using hγM₀
  have hγk' : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k := by simpa only [hM₀_eq] using hγk
  have hTP : cfg.TP.Valid := bundleCoreParamsMach_valid E
  have hLvl := level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P N₀ hTP hγM₀' hγk' hInv
  have hCompAll := oconc_chainInv_comp_bound_all_levels hTP hγM₀' hγk' hInv hConn0
  have hBAll := chainInv_hB_bound_of_concreteBCap_le lsfInit oracle hInit
    sparsify params hp_s hp_t M₀ N₀ B_cap hM₀ α Ψ ε (concreteBCap_le_bucketCap_ceil C_lsst Ψ M₀ N₀ hM₀)
    hγM₀ hγk hInv hℓ0
  refine ⟨fun i hi => ?_, hCompAll.2⟩
  have hm_le_sq : (st.G i).m ≤ M₀ ^ 2 := by
    have h1 : (st.G i).m ≤ levelM cfg.TP cfg.P i := by
      exact_mod_cast (hLvl i (Nat.le_of_lt hi)).2.2.1
    exact le_trans h1 (levelM_le_sq hTP hγM₀' hγk' i)
  refine ⟨
    { hInit := fun _ hj => hInit.validFor hj
      hSp := sparsifySpec_mono_mMax hm_le_sq
        (monoSparsifyParamsEnvelope_sparsifySpec params sparsify hSp (M₀ ^ 2))
      hB_bound := fun j hj C hC => hBAll i hi (st.G i).m 0 (fun _ => []) j hj C hC }, ?_⟩
  change ((st.G i).n : ℝ) ≤ 1 * (((st.G i).m : ℝ) + 1)
  exact hCompAll.1 i (Nat.le_of_lt hi)

end OconcNoHidden

end MinCostFlow.Chain.Ordered
