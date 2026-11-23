module

public import MinCostFlow.Final.AssemblyDryRunSCParamMath
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Word-size bounds for dry-run solver parameter setup

Under the dry run's word-size condition `ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB)
(dryAllocDeg B hB)`:
1. `dryParam_outputs_lt_two_pow`: every one of the seven outputs (`d`, `branch`, `⌈cfg.Ψ⌉₊`,
   `quality`, `epsExp`, `N₀`, and `levelM cfg.TP cfg.P i` for every `i < d`) as well as the inputs
   `I.m`, `V`, `threshold`, `M₀ + 2`, `Num.IPM.alphaScale I.m V + 1`, `220000`, and `14 ≤ w` fit
   strictly below `2 ^ w`.
2. `dryParam_general_word_bounds`: above `M_cut = Classical.choose exists_dryLevelM_threshold`,
   proves `4 * M₀ ^ 2 + 2 < 2 ^ w`, `(Nat.log 2 (4 * M₀ ^ 2 + 2) + 2) ^ 3 < 2 ^ w`,
   `drySparsifyDen M₀ < 2 ^ w`, `drySparsifyCap M₀ < 2 ^ w`, `dryWitnessDen < 2 ^ w`,
   `M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i < 2 ^ w` for every `i < d`, and discharges both
   `pathDSBoundsContract` word-width preconditions (`hcw1` and `hcw2`) using `sparsifyPathDSUsed_cw`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Scaling.Machine
  MinRatio DynSpanner.Program

private lemma two_pow_14_mul_paramBound_lt {m U k w : ℕ}
    (hw : ipmQualityParameterWordBits m U k ≤ w) :
    2 ^ 14 * ipmQualityParameterBound m U k < 2 ^ w := by
  have h1 : ipmQualityParameterBound m U k < 2 ^ (ipmQualityParameterBound m U k).size :=
    Nat.lt_size_self _
  have h2 : 2 ^ 14 * ipmQualityParameterBound m U k <
      2 ^ 14 * 2 ^ (ipmQualityParameterBound m U k).size :=
    Nat.mul_lt_mul_of_pos_left h1 (by decide)
  rw [← pow_add] at h2
  exact lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) hw)

private lemma wordSize_ge_27_of_hw {m U k w : ℕ}
    (hw : ipmQualityParameterWordBits m U k ≤ w) :
    27 ≤ w := by
  have hB : 2 ^ 12 ≤ ipmQualityParameterBound m U k := by
    unfold ipmQualityParameterBound ipmQualityPrecision ipmQualityErrorBits
      ipmQualityRangeExponent
    omega
  have hsz : 13 ≤ (ipmQualityParameterBound m U k).size := by
    by_contra hlt
    have h1 := Nat.lt_size_self (ipmQualityParameterBound m U k)
    have h2 : 2 ^ (ipmQualityParameterBound m U k).size ≤ 2 ^ 12 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  unfold ipmQualityParameterWordBits at hw
  omega

private lemma levelM_zero_ge_M0 {TP : SparseCoreParams} {P : ChainParams}
    (hγ : (1 : ℝ) ≤ TP.γ_ℓ (P.M₀ ^ 2)) : P.M₀ ≤ Chain.levelM TP P 0 := by
  unfold Chain.levelM
  simp only [pow_zero, mul_one]
  have hM : (P.M₀ : ℝ) ≤ (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hγ
  exact_mod_cast hM.trans (Nat.le_ceil _)

private lemma branch_pow_le_two_mul_M0_add_two_sq {M₀ d k : ℕ}
    (hM0 : 1 ≤ M₀) (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hd_def : d = Chain.chosenD (23 / 24) M₀)
    (hk_up : (k : ℝ) ≤ 2 * (M₀ : ℝ) ^ (1 / (d : ℝ)))
    {i : ℕ} (hi : i < d) :
    k ^ i ≤ 2 * (M₀ + 2) ^ 2 := by
  have hM1 : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM0
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hk2 : (k : ℝ) ≤ 2 * (M₀ : ℝ) ^ (1 / (d : ℝ)) := hk_up
  have hkpow_d : ((k : ℝ) ^ d) ≤ (2 : ℝ) ^ d * (M₀ : ℝ) := by
    calc (k : ℝ) ^ d
        ≤ (2 * (M₀ : ℝ) ^ (1 / (d : ℝ))) ^ d :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hk2 d
      _ = (2 : ℝ) ^ d * ((M₀ : ℝ) ^ (1 / (d : ℝ))) ^ d := mul_pow _ _ _
      _ = (2 : ℝ) ^ d * (M₀ : ℝ) := by
          rw [← Real.rpow_natCast ((M₀ : ℝ) ^ (1 / (d : ℝ))) d,
            ← Real.rpow_mul (Nat.cast_nonneg _),
            one_div_mul_cancel (by positivity : (d : ℝ) ≠ 0), Real.rpow_one]
  have h2d : (2 : ℝ) ^ d ≤ 2 * ((M₀ : ℝ) + 2) := by
    have hM3 : (3 : ℝ) ≤ (M₀ : ℝ) + 2 := by linarith
    have hlog1 : (1 : ℝ) ≤ Real.log ((M₀ : ℝ) + 2) := by
      have h3 : Real.exp 1 ≤ (M₀ : ℝ) + 2 := le_trans Real.exp_one_lt_three.le hM3
      simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3
    have hrpow_le : Real.log ((M₀ : ℝ) + 2) ^ ((1 : ℝ) / 48) ≤ Real.log ((M₀ : ℝ) + 2) := by
      calc Real.log ((M₀ : ℝ) + 2) ^ ((1 : ℝ) / 48)
          ≤ Real.log ((M₀ : ℝ) + 2) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
        _ = Real.log ((M₀ : ℝ) + 2) := Real.rpow_one _
    have hd_r : (d : ℝ) ≤ Real.log ((M₀ : ℝ) + 2) + 1 := by
      have hceil : (Chain.chosenD (23 / 24) M₀ : ℝ) ≤
          Real.log ((M₀ : ℝ) + 2) ^ ((1 - (23 / 24 : ℝ)) / 2) + 1 := by
        unfold Chain.chosenD
        exact (Nat.ceil_lt_add_one (by positivity)).le
      have hexp : (1 - (23 / 24 : ℝ)) / 2 = 1 / 48 := by norm_num
      rw [hd_def]; rw [hexp] at hceil; linarith
    have hpow_le : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ (Real.log ((M₀ : ℝ) + 2) + 1) := by
      rw [← Real.rpow_natCast (2 : ℝ) d]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hd_r
    have h2log : (2 : ℝ) ^ Real.log ((M₀ : ℝ) + 2) ≤ (M₀ : ℝ) + 2 := by
      have h1 : (2 : ℝ) ^ Real.log ((M₀ : ℝ) + 2) =
          Real.exp (Real.log 2 * Real.log ((M₀ : ℝ) + 2)) := by
        rw [Real.rpow_def_of_pos (by norm_num)]
      rw [h1]
      have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      have hmul : Real.log 2 * Real.log ((M₀ : ℝ) + 2) ≤ Real.log ((M₀ : ℝ) + 2) := by
        nlinarith [hlog1, hlog2]
      calc Real.exp (Real.log 2 * Real.log ((M₀ : ℝ) + 2))
          ≤ Real.exp (Real.log ((M₀ : ℝ) + 2)) := Real.exp_le_exp.mpr hmul
        _ = (M₀ : ℝ) + 2 := Real.exp_log (by linarith)
    calc (2 : ℝ) ^ d
        ≤ (2 : ℝ) ^ (Real.log ((M₀ : ℝ) + 2) + 1) := hpow_le
      _ = (2 : ℝ) ^ Real.log ((M₀ : ℝ) + 2) * (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_add (by norm_num) _ _
      _ = 2 * (2 : ℝ) ^ Real.log ((M₀ : ℝ) + 2) := by rw [Real.rpow_one]; ring
      _ ≤ 2 * ((M₀ : ℝ) + 2) := by linarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hki_le : (k : ℝ) ^ i ≤ (k : ℝ) ^ d := pow_le_pow_right₀ hk1 hi.le
  have hfinal : ((k ^ i : ℕ) : ℝ) ≤ ((2 * (M₀ + 2) ^ 2 : ℕ) : ℝ) := by
    push_cast
    calc (k : ℝ) ^ i ≤ (k : ℝ) ^ d := hki_le
      _ ≤ (2 : ℝ) ^ d * (M₀ : ℝ) := hkpow_d
      _ ≤ (2 * ((M₀ : ℝ) + 2)) * (M₀ : ℝ) := mul_le_mul_of_nonneg_right h2d (Nat.cast_nonneg _)
      _ ≤ 2 * ((M₀ : ℝ) + 2) ^ 2 := by nlinarith
  exact_mod_cast hfinal

/-- **Step 3 (outputs)**: every output of parameter setup (`d`, `branch`, `⌈cfg.Ψ⌉₊`, `quality`,
`epsExp`, `N₀`, and `levelM cfg.TP cfg.P i` for every `i < d`), along with the input bounds
`I.m`, `V`, `threshold`, `M₀ + 2`, `alphaScale + 1`, `220000`, and `14 ≤ w`, fits strictly below
`2 ^ w` under `ForAllDryInputs`. -/
theorem dryParam_outputs_lt_two_pow (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B) :
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J _hw =>
      let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
      let A := concreteQualityBudgetWithLast dryWitnessUsed
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent threshold A I.m
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let w := dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source
      14 ≤ w ∧ 220000 < 2 ^ w ∧
      I.m < 2 ^ w ∧ V < 2 ^ w ∧ threshold < 2 ^ w ∧
      cfg.P.M₀ + 2 < 2 ^ w ∧
      Num.IPM.alphaScale I.m V + 1 < 2 ^ w ∧
      cfg.P.d < 2 ^ w ∧ cfg.P.k < 2 ^ w ∧ ⌈cfg.Ψ⌉₊ < 2 ^ w ∧
      k < 2 ^ w ∧ k + Num.IPM.alphaExponent I.m V + 10 < 2 ^ w ∧
      cfg.N₀ < 2 ^ w ∧ (∀ i < cfg.P.d, Chain.levelM cfg.TP cfg.P i < 2 ^ w) := by
  intro source J hJn hJm _hCost hCap hw
  dsimp only
  set threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  set A := concreteQualityBudgetWithLast dryWitnessUsed
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent threshold A I.m
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  set w := dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source
  have hw27 : 27 ≤ w := wordSize_ge_27_of_hw hw
  have h220000 : 220000 < 2 ^ w := by
    have h1 : 2 ^ 18 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have h14B : 2 ^ 14 * ipmQualityParameterBound I.m V k < 2 ^ w :=
    two_pow_14_mul_paramBound_lt hw
  have hB_def : ipmQualityParameterBound I.m V k =
      2 * ipmQualityPrecision I.m V k + 20 * I.m + Num.IPM.alphaScale I.m V + V +
        ipmQualityLimbs I.m V k + ipmQualityRangeExponent I.m V k + 100 := rfl
  have hk_le_range : k ≤ ipmQualityRangeExponent I.m V k := by
    unfold ipmQualityRangeExponent qualitySlackExponent
    have := le_max_right (slackRangeExponent I.m V) k
    omega
  have hslack_le_range : slackRangeExponent I.m V ≤ ipmQualityRangeExponent I.m V k := by
    unfold ipmQualityRangeExponent qualitySlackExponent
    have := le_max_left (slackRangeExponent I.m V) k
    omega
  have halpha_le : Num.IPM.alphaExponent I.m V ≤ Num.IPM.alphaScale I.m V := by
    unfold Num.IPM.alphaExponent
    exact (Nat.clog_le_iff_le_pow (by decide)).mpr (Nat.le_of_lt Nat.lt_two_pow_self)
  have hPsi_eq : ⌈cfg.Ψ⌉₊ = ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 :=
    (concreteCfg_scalars_eq dryWitnessUsed I.m V).2.2.1
  have hWordPoly := Classical.choose_spec (concrete_solver_word_bounds_poly dryWitnessUsed)
    (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
    ((le_max_right _ _).trans (le_max_left _ _))
    source J hJn hJm (fun e => (hCap e).1) hw
  have h4M0 : 4 * cfg.P.M₀ + 3 < 2 ^ w := hWordPoly.2
  have hthr_le_M0 : threshold ≤ cfg.P.M₀ := le_max_right I.m threshold
  have hd_lt : cfg.P.d < 2 ^ w := by
    have h1 : cfg.P.d ≤ (cfg.P.M₀ + 2).size := chosenD_le_size_add_two cfg.P.hM₀
    have h2 : (cfg.P.M₀ + 2).size ≤ cfg.P.M₀ + 2 := Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  have hk_lt : cfg.P.k < 2 ^ w := by
    have h1 : cfg.P.k ≤ 2 * cfg.P.M₀ := by
      have hM1 : (1 : ℝ) ≤ (cfg.P.M₀ : ℝ) := by exact_mod_cast cfg.P.hM₀
      have hd1 : (1 : ℝ) ≤ (cfg.P.d : ℝ) := by exact_mod_cast cfg.P.hd
      have hinv : 1 / (cfg.P.d : ℝ) ≤ 1 := div_le_one_of_le₀ hd1 (by linarith)
      have h2 : (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) ≤ (cfg.P.M₀ : ℝ) := by
        calc (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ))
            ≤ (cfg.P.M₀ : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 hinv
          _ = (cfg.P.M₀ : ℝ) := Real.rpow_one _
      have h3 : (cfg.P.k : ℝ) ≤ ((2 * cfg.P.M₀ : ℕ) : ℝ) := by
        push_cast; linarith [cfg.P.hk_upper]
      exact_mod_cast h3
    omega
  have hlvl_lt : ∀ i < cfg.P.d, Chain.levelM cfg.TP cfg.P i < 2 ^ w := by
    intro i hi
    have hL := (concrete_sparseCoreCapHyp_uniform dryWitnessUsed J hJn hJm (fun e => (hCap e).1)
      i hi.le 0 0 (by omega)).2
    have hsc := Classical.choose_spec
      (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed)
      (dryAllocCoeffFull B hB) (dryAllocDeg B hB) (le_max_right _ _)
      source J hJn hJm (fun e => (hCap e).1) hw 39 le_rfl i _ hL
    have h1 : Chain.levelM cfg.TP cfg.P i ≤
        (Chain.levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ 39 *
          ((ipmQualityMinRatioFormat I.m V k hw).limbs + 1) := by
      have ha : Chain.levelM cfg.TP cfg.P i ≤ Chain.levelM cfg.TP cfg.P i + cfg.N₀ + 2 := by omega
      have hb : Chain.levelM cfg.TP cfg.P i + cfg.N₀ + 2 ≤
          (Chain.levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ 39 :=
        Nat.le_self_pow (by decide : 39 ≠ 0) _
      have hc : 1 ≤ (ipmQualityMinRatioFormat I.m V k hw).limbs + 1 := by omega
      exact (ha.trans hb).trans (Nat.le_mul_of_pos_right _ hc)
    exact lt_of_le_of_lt h1 hsc
  have hN0_eq : cfg.N₀ = 4 * cfg.P.M₀ := rfl
  refine ⟨by omega, h220000, by omega, by omega, by omega, by omega, by omega,
    hd_lt, hk_lt, by omega, by omega, by omega, by omega, hlvl_lt⟩

/-- **Step 3 (intermediates and `boundsProcs` word width)**: above the threshold `M_cut` of
`exists_dryLevelM_threshold`, every intermediate quantity used by `wireParamModule` fits strictly
below `2 ^ w`, and both `pathDSBoundsContract` word-width preconditions hold (using
`sparsifyPathDSUsed_cw`). -/
theorem dryParam_general_word_bounds (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B) :
    let M_cut := Classical.choose exists_dryLevelM_threshold
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J _hw =>
      M_cut ≤ (solverConnectedAugmented J).m →
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let M₀ := cfg.P.M₀
      let w := dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source
      let pds := sparsifyPathDSUsed.params
      4 * M₀ ^ 2 + 2 < 2 ^ w ∧
      (Nat.log 2 (4 * M₀ ^ 2 + 2) + 2) ^ 3 < 2 ^ w ∧
      drySparsifyDen M₀ < 2 ^ w ∧
      drySparsifyCap M₀ < 2 ^ w ∧
      dryWitnessDen < 2 ^ w ∧
      pds.cw * (Nat.log 2 (drySparsifyDen M₀ + M₀ ^ 2 +
          pds.gExp (drySparsifyDen M₀) (M₀ ^ 2) +
          pds.gDel (drySparsifyDen M₀) (M₀ ^ 2) + 2) + 1) ≤ w ∧
      pds.cw * (Nat.log 2 (dryWitnessDen + drySparsifyCap M₀ +
          pds.gExp dryWitnessDen (drySparsifyCap M₀) +
          pds.gDel dryWitnessDen (drySparsifyCap M₀) + 2) + 1) ≤ w ∧
      (∀ i < cfg.P.d, M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i < 2 ^ w) := by
  intro M_cut source J hJn hJm _hCost hCap hw hMcut
  dsimp only
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  set A := concreteQualityBudgetWithLast dryWitnessUsed
  set k := cappedQualityExponent threshold A I.m
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  set M₀ := cfg.P.M₀
  set w := dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source
  set pds := sparsifyPathDSUsed.params
  have hcw : sparsifyPathDSUsed.params.cw ≤ 25 := by rw [sparsifyPathDSUsed_cw]; decide
  have hMcutSpec := Classical.choose_spec exists_dryLevelM_threshold
  obtain ⟨hM0_eq, hγ_eq, hlvlM_eq, hsum1, hsum2⟩ := hMcutSpec.2 J hJn hJm (fun e => (hCap e).1) hMcut
  have h232_le_Im : 2 ^ 32 ≤ I.m :=
    le_trans (le_max_right _ _) (hMcutSpec.1.trans hMcut)
  have hJm_le_Im : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm (fun e => (hCap e).1)).1
  have hIm_le_7Jm : I.m ≤ 7 * J.m := (solverConnectedAugmented_size J hJn hJm (fun e => (hCap e).1)).2
  have hJm_le_M0 : J.m ≤ M₀ := hJm_le_Im.trans (le_max_left I.m threshold)
  change drySparsifyDen M₀ + M₀ ^ 2 + pds.gExp (drySparsifyDen M₀) (M₀ ^ 2) +
    pds.gDel (drySparsifyDen M₀) (M₀ ^ 2) + 2 ≤ J.m ^ 3 at hsum1
  change dryWitnessDen + drySparsifyCap M₀ + pds.gExp dryWitnessDen (drySparsifyCap M₀) +
    pds.gDel dryWitnessDen (drySparsifyCap M₀) + 2 ≤ J.m ^ 3 at hsum2
  change cfg.TP.γ_ℓ (M₀ ^ 2) = (dryGammaNat M₀ : ℝ) at hγ_eq
  -- Sparse-core power-39 bound at every level `i < d`
  have hsc_level : ∀ i < cfg.P.d, (Chain.levelM cfg.TP cfg.P i + 4 * M₀ + 2) ^ 39 < 2 ^ w := by
    intro i hi
    have hL := (concrete_sparseCoreCapHyp_uniform dryWitnessUsed J hJn hJm (fun e => (hCap e).1)
      i hi.le 0 0 (by omega)).2
    have hsc := Classical.choose_spec
      (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed)
      (dryAllocCoeffFull B hB) (dryAllocDeg B hB) (le_max_right _ _)
      source J hJn hJm (fun e => (hCap e).1) hw 39 le_rfl i _ hL
    have h1 : (Chain.levelM cfg.TP cfg.P i + 4 * M₀ + 2) ^ 39 ≤
        (Chain.levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ 39 *
          ((ipmQualityMinRatioFormat I.m V k hw).limbs + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    exact lt_of_le_of_lt h1 hsc
  have h5M0_39 : (5 * M₀ + 2) ^ 39 < 2 ^ w := by
    have h0 := hsc_level 0 cfg.P.hd
    have hγ1 : (1 : ℝ) ≤ cfg.TP.γ_ℓ (M₀ ^ 2) := by
      rw [hγ_eq]
      have hd1 := Expander.maxPhiDenOf_pos dryDecompK dryDecompThr (M₀ ^ 2)
      have hg1 : 1 ≤ drySparsifyG M₀ := by
        have h2 : 2 ≤ pds.gExp (drySparsifyDen M₀) (M₀ ^ 2) :=
          le_trans (le_trans (le_max_left 2 _) (pds.hphiOutDen_ge _ _ hd1)) (pds.hgExp_ge _ _ hd1)
        exact Nat.one_le_pow 2 _ (le_trans (by omega : 1 ≤ 2) (h2.trans (le_max_left _ _)))
      exact_mod_cast Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos hg1)
    have hle : 5 * M₀ + 2 ≤ Chain.levelM cfg.TP cfg.P 0 + 4 * M₀ + 2 := by
      have := levelM_zero_ge_M0 (TP := cfg.TP) (P := cfg.P) hγ1
      omega
    exact lt_of_le_of_lt (Nat.pow_le_pow_left hle 39) h0
  have hM0_3 : M₀ ^ 3 < 2 ^ w := by
    have h1 : M₀ ^ 3 ≤ (5 * M₀ + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2 : (5 * M₀ + 2) ^ 3 ≤ (5 * M₀ + 2) ^ 39 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    exact lt_of_le_of_lt (h1.trans h2) h5M0_39
  have hJm3_lt : J.m ^ 3 < 2 ^ w :=
    lt_of_le_of_lt (Nat.pow_le_pow_left hJm_le_M0 3) hM0_3
  have h4M2_lt : 4 * M₀ ^ 2 + 2 < 2 ^ w := by
    have h1 : 4 * M₀ ^ 2 + 2 ≤ (5 * M₀ + 2) ^ 2 := by nlinarith only [cfg.P.hM₀]
    have h2 : (5 * M₀ + 2) ^ 2 ≤ (5 * M₀ + 2) ^ 39 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    exact lt_of_le_of_lt (h1.trans h2) h5M0_39
  have hcube_lt : (Nat.log 2 (4 * M₀ ^ 2 + 2) + 2) ^ 3 < 2 ^ w := by
    have hlog : Nat.log 2 (4 * M₀ ^ 2 + 2) ≤ 4 * M₀ ^ 2 + 2 := Nat.log_le_self _ _
    have h1 : Nat.log 2 (4 * M₀ ^ 2 + 2) + 2 ≤ (5 * M₀ + 2) ^ 2 := by
      have : 4 * M₀ ^ 2 + 4 ≤ (5 * M₀ + 2) ^ 2 := by nlinarith only [cfg.P.hM₀]
      omega
    have h2 : (Nat.log 2 (4 * M₀ ^ 2 + 2) + 2) ^ 3 ≤ ((5 * M₀ + 2) ^ 2) ^ 3 :=
      Nat.pow_le_pow_left h1 3
    rw [← pow_mul] at h2
    have h3 : (5 * M₀ + 2) ^ 6 ≤ (5 * M₀ + 2) ^ 39 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    exact lt_of_le_of_lt (h2.trans h3) h5M0_39
  -- Word width lower bound `81 * Nat.log 2 J.m + 15 ≤ w` from `V = solverPenalty J.m`
  have hlogJm_ge : 29 ≤ Nat.log 2 J.m := by
    have h1 : 2 ^ 29 ≤ J.m := by omega
    exact Nat.le_log_of_pow_le (by decide) h1
  have hw_ge_81 : 81 * Nat.log 2 J.m + 15 ≤ w := by
    have hV_ge : J.m ^ 81 ≤ V := by
      change J.m ^ 81 ≤ 4 * J.m * (solverCapacityBound J.m) ^ 2
      have hcap_ge : J.m ^ 40 ≤ solverCapacityBound J.m := le_max_right _ _
      have hsq : (J.m ^ 40) ^ 2 ≤ (solverCapacityBound J.m) ^ 2 := Nat.pow_le_pow_left hcap_ge 2
      calc J.m ^ 81 = 1 * J.m * (J.m ^ 40) ^ 2 := by ring
        _ ≤ 4 * J.m * (solverCapacityBound J.m) ^ 2 :=
            Nat.mul_le_mul (by omega) hsq
    have hV_le_B : V ≤ ipmQualityParameterBound I.m V k := by
      unfold ipmQualityParameterBound; omega
    have hpow_le : 2 ^ (81 * Nat.log 2 J.m) ≤ ipmQualityParameterBound I.m V k := by
      have h2l : 2 ^ Nat.log 2 J.m ≤ J.m := Nat.pow_log_le_self 2 (by omega)
      calc 2 ^ (81 * Nat.log 2 J.m) = (2 ^ Nat.log 2 J.m) ^ 81 := by rw [mul_comm, pow_mul]
        _ ≤ J.m ^ 81 := Nat.pow_le_pow_left h2l 81
        _ ≤ V := hV_ge
        _ ≤ ipmQualityParameterBound I.m V k := hV_le_B
    have hsz : 81 * Nat.log 2 J.m + 1 ≤ (ipmQualityParameterBound I.m V k).size := by
      by_contra hlt
      have h1 := Nat.lt_size_self (ipmQualityParameterBound I.m V k)
      have h2 : 2 ^ (ipmQualityParameterBound I.m V k).size ≤ 2 ^ (81 * Nat.log 2 J.m) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    unfold ipmQualityParameterWordBits at hw
    omega
  have hlog_sum : ∀ s, s ≤ J.m ^ 3 → pds.cw * (Nat.log 2 s + 1) ≤ w := by
    intro s hs
    have hJm_lt : J.m < 2 ^ (Nat.log 2 J.m + 1) := Nat.lt_pow_succ_log_self (by decide) J.m
    have hs_lt : s < 2 ^ (3 * (Nat.log 2 J.m + 1)) := by
      have h3 : J.m ^ 3 < (2 ^ (Nat.log 2 J.m + 1)) ^ 3 := Nat.pow_lt_pow_left hJm_lt (by decide)
      rw [← pow_mul, mul_comm _ 3] at h3
      exact lt_of_le_of_lt hs h3
    have hlog_le : Nat.log 2 s ≤ 3 * (Nat.log 2 J.m + 1) := by
      rcases Nat.eq_zero_or_pos s with rfl | hspos
      · simp
      · exact (Nat.log_lt_of_lt_pow (by omega) hs_lt).le
    have hmul : pds.cw * (Nat.log 2 s + 1) ≤ 25 * (3 * Nat.log 2 J.m + 4) :=
      Nat.mul_le_mul hcw (by omega)
    omega
  have hnumW : ∀ i < cfg.P.d, M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i < 2 ^ w := by
    intro i hi
    have hbr_pow : cfg.P.k ^ i ≤ 2 * (M₀ + 2) ^ 2 :=
      branch_pow_le_two_mul_M0_add_two_sq cfg.P.hM₀ cfg.P.hd cfg.P.hk rfl cfg.P.hk_upper hi
    have hlvl : Chain.levelM cfg.TP cfg.P i =
        (M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i - 1) / cfg.P.k ^ i := hlvlM_eq i
    have hbr_pos : 1 ≤ cfg.P.k ^ i := Nat.one_le_pow _ _ cfg.P.hk
    have hdiv_mul : M₀ * dryGammaNat M₀ ^ (i + 1) ≤ cfg.P.k ^ i * Chain.levelM cfg.TP cfg.P i := by
      rw [hlvl]
      have h1 : M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i - 1 <
          ((M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i - 1) / cfg.P.k ^ i + 1) * cfg.P.k ^ i := by
        have := Nat.div_add_mod (M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i - 1) (cfg.P.k ^ i)
        have hmod := Nat.mod_lt (M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i - 1) hbr_pos
        rw [Nat.add_mul, Nat.one_mul, mul_comm _ (cfg.P.k ^ i)]
        omega
      rw [Nat.add_mul, Nat.one_mul, mul_comm _ (cfg.P.k ^ i)] at h1
      omega
    have hsum_le : M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i ≤
        2 * (M₀ + 2) ^ 2 * (Chain.levelM cfg.TP cfg.P i + 1) := by
      calc M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i
          ≤ cfg.P.k ^ i * Chain.levelM cfg.TP cfg.P i + cfg.P.k ^ i := by omega
        _ = cfg.P.k ^ i * (Chain.levelM cfg.TP cfg.P i + 1) := by ring
        _ ≤ 2 * (M₀ + 2) ^ 2 * (Chain.levelM cfg.TP cfg.P i + 1) :=
            Nat.mul_le_mul_right _ hbr_pow
    have hsq_le : 2 * (M₀ + 2) ^ 2 ≤ (Chain.levelM cfg.TP cfg.P i + 4 * M₀ + 2) ^ 2 :=
      (show 2 * (M₀ + 2) ^ 2 ≤ (4 * M₀ + 2) ^ 2 by nlinarith only [cfg.P.hM₀]).trans
        (Nat.pow_le_pow_left (by omega) 2)
    have hcube : M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i ≤
        (Chain.levelM cfg.TP cfg.P i + 4 * M₀ + 2) ^ 3 := by
      calc M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i
          ≤ 2 * (M₀ + 2) ^ 2 * (Chain.levelM cfg.TP cfg.P i + 1) := hsum_le
        _ ≤ (Chain.levelM cfg.TP cfg.P i + 4 * M₀ + 2) ^ 2 *
              (Chain.levelM cfg.TP cfg.P i + 4 * M₀ + 2) :=
            Nat.mul_le_mul hsq_le (by omega)
        _ = (Chain.levelM cfg.TP cfg.P i + 4 * M₀ + 2) ^ 3 := by ring
    have hpow39 : (Chain.levelM cfg.TP cfg.P i + 4 * M₀ + 2) ^ 3 ≤
        (Chain.levelM cfg.TP cfg.P i + 4 * M₀ + 2) ^ 39 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    exact lt_of_le_of_lt (hcube.trans hpow39) (hsc_level i hi)
  refine ⟨h4M2_lt, hcube_lt,
    lt_of_le_of_lt (by omega : drySparsifyDen M₀ ≤ J.m ^ 3) hJm3_lt,
    lt_of_le_of_lt (by omega : drySparsifyCap M₀ ≤ J.m ^ 3) hJm3_lt,
    lt_of_le_of_lt (by omega : dryWitnessDen ≤ J.m ^ 3) hJm3_lt,
    hlog_sum _ hsum1, hlog_sum _ hsum2, hnumW⟩

end MinCostFlow.Final.DryRun

end
