module

public import MinCostFlow.Final.AssemblyDryRun
public import MinCostFlow.Final.AssemblyDryRunSCFitsBounds
public import MinCostFlow.SparseCore.Program.AssemblyModel
import MinCostFlow.Chain.Ordered.ShiftLoopLevels
import MinCostFlow.Chain.Ordered.InitPreserves
import MinCostFlow.Chain.Ordered.ShiftPreserves
import MinCostFlow.Chain.Ordered.RenameFacts
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Dry-run format and branch-count bounds for P4 (`AssemblyDryRunSCFormat`)

Discharges the format preconditions (`CompInitFormatHyp`) and branch-count cap
(`cfg.P.k ≤ (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ dryCapExp`) required by `AsmCompFamilyAt`
(`AssemblyTopIface.lean`) at every level of the dry run:

* `drySC_k_le_capExp`: `cfg.P.k ≤ (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ dryCapExp`.
* `drySC_compInitFormatHyp`: `CompInitFormatHyp F.limbs F.fmt.precision cfg.P.k G.m` whenever
  `G.m ≤ (solverConnectedAugmented J).m`.
* `ChainInv.levels_m_le`: under `ChainInv`, `(st.G i).m ≤ (st.G 0).m` for every level `i ≤ P.d`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM MinCostFlow MinCostFlow.Chain MinCostFlow.IPM MinCostFlow.IPM.Machine
  MinCostFlow.SparseCore MinCostFlow.SparseCore.Program MinCostFlow.Scaling
  MinCostFlow.LastLevelProgram MinCostFlow.Bundle

/-! ## Branch-count cap bound -/

/-- At every level `i`, the chain's branch count `cfg.P.k` fits within
`(levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ dryCapExp`. -/
theorem drySC_k_le_capExp (J : Circulation) (i : ℕ) :
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    cfg.P.k ≤ (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ dryCapExp := by
  intro cfg
  have hM0_ge1 : (1 : ℝ) ≤ (cfg.P.M₀ : ℝ) := by exact_mod_cast cfg.P.hM₀
  have hd_ge1 : (1 : ℝ) ≤ (cfg.P.d : ℝ) := by exact_mod_cast cfg.P.hd
  have hinv_le1 : (1 : ℝ) / (cfg.P.d : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hd_ge1
  have hrpow : (cfg.P.M₀ : ℝ) ^ ((1 : ℝ) / (cfg.P.d : ℝ)) ≤ (cfg.P.M₀ : ℝ) := by
    calc (cfg.P.M₀ : ℝ) ^ ((1 : ℝ) / (cfg.P.d : ℝ))
        ≤ (cfg.P.M₀ : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM0_ge1 hinv_le1
      _ = (cfg.P.M₀ : ℝ) := Real.rpow_one _
  have hk_real : (cfg.P.k : ℝ) ≤ 2 * (cfg.P.M₀ : ℝ) :=
    cfg.P.hk_upper.trans (by linarith)
  have hk_le_2M0 : cfg.P.k ≤ 2 * cfg.P.M₀ := by exact_mod_cast hk_real
  have hN0_eq : cfg.N₀ = 4 * cfg.P.M₀ := rfl
  have hbase : cfg.P.k ≤ levelM cfg.TP cfg.P i + cfg.N₀ + 2 := by omega
  calc cfg.P.k
      ≤ levelM cfg.TP cfg.P i + cfg.N₀ + 2 := hbase
    _ ≤ (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ dryCapExp :=
        Nat.le_self_pow (by decide : dryCapExp ≠ 0) _

/-! ## Format preconditions (`CompInitFormatHyp`) -/

/-- `cfg.P.k < 2 ^ k_q` at the dry run's quality exponent `k_q`, extracted from
`1 / 2 ^ k_q ≤ alg2KappaOwn` and `cfg.TP.σ cfg.P.k cfg.N₀ ≤ σ_tot`. -/
theorem drySC_k_lt_two_pow_quality (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
    let A := concreteQualityBudgetWithLast dryWitnessUsed
    let k_q := cappedQualityExponent threshold A I.m
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    cfg.P.k < 2 ^ k_q := by
  intro I threshold A k_q cfg
  let V := solverPenalty J.m
  let M₀ := max I.m threshold
  let N₀ := 4 * M₀
  have hM₀1 : 1 ≤ M₀ :=
    (by omega : 1 ≤ 2).trans ((concreteEdgeThresholdWithLast_ge_two dryWitnessUsed).trans (le_max_right _ _))
  let α := Num.IPM.alphaPrime I.m V / 8
  let Ψ := ((ipmQualityRangeExponent I.m V k_q + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
  let ε := (1 / (2 : ℝ) ^ k_q) * Num.IPM.alphaPrime I.m V / 1024
  obtain ⟨hThresh, hN₀, hPsi, hα, -⟩ :=
    concreteCirculation_bounds_of (le_max_left dryWitnessUsed.M_thresh _)
      (le_max_right dryWitnessUsed.M_thresh _)
      (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed) J hJn hJm hCap
  obtain ⟨⟨hκ_pos, hKappa⟩, _⟩ :=
    dryWitnessUsed.specWith (ipmQualityLimbs I.m V k_q) (ipmQualityPrecision I.m V k_q) M₀ N₀ α Ψ ε
      hM₀1 hThresh hN₀ hPsi hα
  have hAge : 15 + 5 * dryWitnessUsed.C_γ ≤ (A : ℝ) := Nat.le_ceil _
  have hk_le_κ : 1 / (2 : ℝ) ^ k_q ≤ alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ :=
    concrete_kappa_le_alg2KappaOwn_of A hAge M₀ hKappa
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  set σ_tot := alg2SigmaTotOwn cfg.TP cfg.LP cfg.P cfg.N₀
  set σ_mwu_max := alg2SigmaGame cfg.σ_mwu cfg.N₀
  have hγ1 : 1 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := hVcfg.hTP.2.2.1 (cfg.P.M₀ ^ 2)
  have hσ_mwu_nn : 0 ≤ σ_mwu_max := le_max_left 0 _
  have hbase_ge1 : 1 ≤ 2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max) := by nlinarith
  have hpow_ge1 : 1 ≤ (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d :=
    one_le_pow₀ hbase_ge1
  have hd_ge1 : 1 ≤ ((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) := by
    have : (0 : ℝ) ≤ cfg.P.d := Nat.cast_nonneg _
    nlinarith
  have hσ_tot_nn : 0 ≤ σ_tot := by
    unfold σ_tot alg2SigmaTotOwn alg2SigmaTotAt
    exact le_trans zero_le_one ((hVcfg.hLP.1 _).trans (le_max_right _ _))
  have hσ_lt_2k : σ_tot + 1 ≤ (2 : ℝ) ^ k_q := by
    have hκ_eq : alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ =
        1 / ((σ_tot + 1) * (((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) *
          (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d)) := rfl
    have hκ_pos' : 0 < alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ := hκ_pos
    have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k_q := by positivity
    have hinv : 1 / alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ ≤ (2 : ℝ) ^ k_q := by
      rw [div_le_iff₀ hκ_pos']
      have h1 := (div_le_iff₀ h2k_pos).mp hk_le_κ
      linarith
    rw [hκ_eq, one_div_one_div] at hinv
    have hprod_ge1 : 1 ≤ ((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) *
        (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d := by nlinarith
    have hdenom_ge : σ_tot + 1 ≤ (σ_tot + 1) *
        (((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) *
          (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d) := by nlinarith
    exact hdenom_ge.trans hinv
  have hσk_le : cfg.TP.σ cfg.P.k cfg.N₀ ≤ σ_tot := le_max_left _ _
  have hlogN_ge1 : 1 ≤ Real.log ((cfg.N₀ : ℝ) + 2) := by
    have hN4 : (4 : ℝ) ≤ (cfg.N₀ : ℝ) := by
      have : 4 ≤ cfg.N₀ := by change 4 ≤ 4 * M₀; omega
      exact_mod_cast this
    have hexp : Real.exp 1 ≤ (cfg.N₀ : ℝ) + 2 := by linarith [Real.exp_one_lt_d9]
    exact (Real.le_log_iff_exp_le (by positivity)).mpr hexp
  have hlog6_ge1 : 1 ≤ (Real.log ((cfg.N₀ : ℝ) + 2)) ^ 6 := one_le_pow₀ hlogN_ge1
  have hmwu_ge1 : 1 ≤ mwuK0 dryWitnessUsed.C_lsst := by
    unfold mwuK0
    have := le_max_left 1 dryWitnessUsed.C_lsst
    linarith
  have hk_le_σ : (cfg.P.k : ℝ) ≤ cfg.TP.σ cfg.P.k cfg.N₀ := by
    have hk_nn : (0 : ℝ) ≤ (cfg.P.k : ℝ) := Nat.cast_nonneg _
    have hmul : (cfg.P.k : ℝ) ≤ mwuK0 dryWitnessUsed.C_lsst * (cfg.P.k : ℝ) *
        (Real.log ((cfg.N₀ : ℝ) + 2)) ^ 6 := by
      have h1 : (cfg.P.k : ℝ) ≤ mwuK0 dryWitnessUsed.C_lsst * (cfg.P.k : ℝ) :=
        le_mul_of_one_le_left hk_nn hmwu_ge1
      exact h1.trans (le_mul_of_one_le_right (by positivity) hlog6_ge1)
    exact hmul.trans (le_max_right 1 _)
  have hreal : ((cfg.P.k : ℕ) : ℝ) < (2 : ℝ) ^ k_q := by linarith
  exact_mod_cast hreal

/-- Discharges all four `CompInitFormatHyp` preconditions at the dry run's IPM quality format for
every graph `G` with `G.m ≤ (solverConnectedAugmented J).m`. -/
theorem drySC_compInitFormatHyp (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {m : ℕ} (hm : m ≤ (solverConnectedAugmented J).m) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
    let A := concreteQualityBudgetWithLast dryWitnessUsed
    let k_q := cappedQualityExponent threshold A I.m
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    CompInitFormatHyp (ipmQualityLimbs I.m V k_q) (ipmQualityPrecision I.m V k_q) cfg.P.k m := by
  intro I V threshold A k_q cfg
  set E := ipmQualityRangeExponent I.m V k_q
  set P_fp := ipmQualityPrecision I.m V k_q
  set L := ipmQualityLimbs I.m V k_q
  have hL_ge : L = P_fp + gradientCoefficientExponent I.m V + 5 * E + 40 := rfl
  have hP_ge : 24 * E + 400 ≤ P_fp := by
    dsimp only [P_fp, ipmQualityPrecision, ipmQualityErrorBits]; omega
  have hkE : 4 * k_q + 100 ≤ E := by
    have hk1 := qualityExponent_le_qualitySlackExponent I.m V k_q
    dsimp only [E, ipmQualityRangeExponent]; omega
  refine ⟨by omega, dvd_mul_right 4 _, by omega, ?_, ?_⟩
  · refine ⟨k_q + 6, by omega, ?_⟩
    have hk_lt := drySC_k_lt_two_pow_quality J hJn hJm hCap
    change cfg.P.k < 2 ^ k_q at hk_lt
    have h64 : 2 ^ (k_q + 6) = 64 * 2 ^ k_q := by rw [pow_add]; ring
    omega
  · have hIm_lt : I.m < 2 ^ I.m.size := Nat.lt_size_self I.m
    have hIm_sz : I.m.size ≤ E := by
      have h1 : I.m.size ≤ (I.m.size + V.size) ^ 2 :=
        le_trans (Nat.le_add_right _ _) (Nat.le_self_pow (by decide : 2 ≠ 0) _)
      have h2 := slackRangeExponent_le_qualitySlackExponent I.m V k_q
      dsimp only [E, ipmQualityRangeExponent]
      unfold slackRangeExponent at h2
      omega
    have hm' : m ≤ I.m := hm
    have hm1 : m + 1 ≤ 2 ^ I.m.size := by omega
    have hexp_lt : 5 + I.m.size + P_fp < 4 * L - 1 := by omega
    have h32 : (32 : ℕ) = 2 ^ 5 := by norm_num
    calc 32 * (m + 1) * 2 ^ P_fp
        ≤ 32 * (2 ^ I.m.size) * 2 ^ P_fp :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 32 hm1)
      _ = 2 ^ (5 + I.m.size + P_fp) := by
          rw [h32, ← pow_add, ← pow_add]
      _ < 2 ^ (4 * L - 1) := Nat.pow_lt_pow_right (by decide) hexp_lt

/-! ## Level edge-count monotonicity under `ChainInv` -/

/-- Under `ChainInv`, every level graph `st.G i` (`i ≤ P.d`) has `(st.G i).E ⊆ (st.G 0).E` and
therefore `(st.G i).m ≤ (st.G 0).m`. -/
theorem chainInv_levels_m_le {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : Chain.Ordered.ChainInv T L TP LP P N₀ st) :
    ∀ i ≤ P.d, (st.G i).m ≤ (st.G 0).m := by
  have hLvl := Chain.Ordered.level_bounds_aux_noHidden T L TP LP P N₀ hTP hγM₀ hγk hInv
  have hSub : ∀ i ≤ P.d, (st.G i).E ⊆ (st.G 0).E := by
    intro i hi
    induction i with
    | zero => exact Finset.Subset.rfl
    | succ i ih =>
      have hi_lt : i < P.d := hi
      have hBi := (hLvl i (Nat.le_of_lt hi_lt)).2.2.2.2 hi_lt (st.bran i) (hInv.hBran i hi_lt)
      have hStep : (st.G (i + 1)).E ⊆ (st.G i).E := by
        rw [hInv.hGSucc i hi_lt]
        exact hBi.2.1.2.1.trans Finset.sdiff_subset
      exact hStep.trans (ih (Nat.le_of_lt hi_lt))
  exact fun i hi => Finset.card_le_card (hSub i hi)

end MinCostFlow.Final.DryRun
