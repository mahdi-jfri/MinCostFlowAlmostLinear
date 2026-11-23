module

public import MinCostFlow.Final.AssemblyDryRunSCLastMult
public import MinCostFlow.Final.AssemblyDryRunSCSizes
import MinCostFlow.MinRatio.OrdSolverConcreteRate
import MinCostFlow.MinRatio.WireParamMath
import MinCostFlow.SparseCore.BundleCoreParams
import MinCostFlow.SparseCore.BundleMachParams
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Uniform `SubpolyNat` and `PolyNat` bounds for the solver envelope (`AssemblyDryRunSCAsymp`)

Provides `M`-only (`M = (solverConnectedAugmented J).m`) `SubpolyNat` and `PolyNat` upper bounds
for every concrete quantity of `dryInnerSizes` and `DryEnvelopeIneqs`:

* **Subpolynomial (`SubpolyNat`) bounds:**
  - `dryD_le_subpoly` (`cfg.P.d`),
  - `dryGammaRPow_le_subpoly` (`⌈γ_r(M₀²) ^ (a * d + b)⌉₊`),
  - `dryRuntimeFactor_le_subpoly` (`runtimeFactorNat cfg`),
  - `dryTreeUpdateFactor_le_subpoly` (`treeUpdateFactorNat cfg`),
  - `dryFwdWeight_le_subpoly` (`fwdWeight`), `dryCapFwdWeight_le_subpoly` (`capFwdWeight`),
  - `dryInitRebuildCap_le_subpoly` (`chainRebuildCap cfg 1 0 ≤ (I.m + 1) * f I.m`),
  - `dryInitShiftQuota_le_subpoly` (`(d + 1) * ⌊(10 * Ψ_g * k)^{d+1}⌋₊ ≤ (I.m + 1) * f I.m`),
  - `dryLevelM_le_subpoly` (`levelM i ≤ (I.m + 1) * f I.m` for `i ≤ d`),
  - `dryInitFixed_le_subpoly` (`initConcreteFixed ≤ (I.m + 1) * f I.m`).
* **Polynomial (`PolyNat`) bounds:**
  - `dryLoopMax_le_poly` (`(loopDigitCap cfg + 1) ^ (d + 1)`),
  - `dryParamSpace_le_poly` (`dryParamSpace`),
  - `dryLastSpace_le_poly` (`dryLastSpace`),
  - `dryInitSpace_le_poly` (`initConcreteSpace` at `dryCoreInitSpace`),
  - `dryDeepSpace_le_poly` (`dryDeepSpace`, unconditional via `dryDeepRestartSpaceBound_poly`).
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program WideWord

/-! ## 1. Real time-factor helpers and basic parameter bounds -/

/-- `1 ≤ alg2TimeFactor E (47 / 48) M` whenever `0 ≤ E`. -/
theorem one_le_alg2TimeFactor {E : ℝ} (hE : 0 ≤ E) (M : ℕ) :
    1 ≤ alg2TimeFactor E (47 / 48) M := by
  rw [alg2TimeFactor_eq_exp_logShape]
  apply Real.one_le_exp
  unfold logShape
  have hL : 0 ≤ Real.log ((M : ℝ) + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
  have hLL : 0 ≤ Real.log (Real.log ((M : ℝ) + 2) + 2) := Real.log_nonneg (by linarith)
  have hpow : 0 ≤ Real.log ((M : ℝ) + 2) ^ (47 / 48 : ℝ) := Real.rpow_nonneg hL _
  exact mul_nonneg hE (mul_nonneg hpow hLL)

/-- Convert a real `C * alg2TimeFactor E (47 / 48) M` ceiling into a `SubpolyNat` function. -/
theorem subpolyNat_ceil_timeFactor (C E : ℝ) (hE : 0 ≤ E) :
    SubpolyNat (fun M => ⌈max C 0 * alg2TimeFactor E (47 / 48) M⌉₊) := by
  refine ⟨max C 0 + 1, E, hE, fun M => ?_⟩
  have h1 : 1 ≤ alg2TimeFactor E (47 / 48) M := one_le_alg2TimeFactor hE M
  have hnn : 0 ≤ max C 0 * alg2TimeFactor E (47 / 48) M :=
    mul_nonneg (le_max_right C 0) (by linarith)
  have hlt := Nat.ceil_lt_add_one hnn
  nlinarith

/-- `dryM0OfM M ≤ (threshold + 1) * (M + 1)`. -/
theorem dryM0OfM_le_mul (M : ℕ) :
    dryM0OfM M ≤ (concreteEdgeThresholdWithLast dryWitnessUsed + 1) * (M + 1) := by
  unfold dryM0OfM
  set thr := concreteEdgeThresholdWithLast dryWitnessUsed
  rcases le_total M thr with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

/-- `cfg.P.d` is bounded by a `SubpolyNat` function of `I.m`. -/
theorem dryD_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        (concreteCirculationCfgWithLast dryWitnessUsed J).P.d ≤ f (solverConnectedAugmented J).m := by
  refine ⟨fun M => (dryM0OfM M + 2).size, subpolyNat_size_of_poly dryM0OfM_poly, fun J _ _ _ => ?_⟩
  exact chosenD_le_size_add_two (concreteCirculationCfgWithLast dryWitnessUsed J).P.hM₀

/-- `cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.TP.γ_r (cfg.P.M₀ ^ 2)` for every circulation `J`. -/
theorem dryGammaL_le_gammaR (J : Circulation) :
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.TP.γ_r (cfg.P.M₀ ^ 2) := by
  intro cfg
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let M₀ := max I.m (concreteEdgeThresholdWithLast dryWitnessUsed)
  let hM₀1 : 1 ≤ M₀ :=
    (by omega : 1 ≤ 2).trans ((concreteEdgeThresholdWithLast_ge_two dryWitnessUsed).trans (le_max_right _ _))
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let Ψ := ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
  let B_cap := concreteBucketCapacity true dryWitnessUsed.C_lsst Ψ M₀ (4 * M₀) hM₀1
  let E := Chain.Ordered.concreteEnv dryWitnessUsed.C_lsst dryWitnessUsed.params
    dryWitnessUsed.hp_s dryWitnessUsed.hp_t M₀ B_cap
  change bundleGammaLEnv E (M₀ ^ 2) ≤ bundleRecBase E (M₀ ^ 2) * bundleCostMult E (M₀ ^ 2)
  have h1 : bundleGammaLEnv E (M₀ ^ 2) ≤ bundleRecBase E (M₀ ^ 2) :=
    (bundleGammaLEnv_le_bundleRecEnv E (M₀ ^ 2)).trans (le_max_left _ _)
  have h2 : 1 ≤ bundleCostMult E (M₀ ^ 2) := bundleCostMult_ge_one E (M₀ ^ 2)
  have h0 : 0 ≤ bundleRecBase E (M₀ ^ 2) :=
    le_trans (by linarith [bundleRecEnv_ge_four E (M₀ ^ 2)]) (le_max_left _ _)
  nlinarith

/-- For every fixed `a b : ℕ`, `⌈γ_r(M₀²) ^ (a * d + b)⌉₊` is dominated by a `SubpolyNat` function
of `I.m`. -/
theorem dryGammaRPow_le_subpoly (a b : ℕ) :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        ⌈(cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (a * cfg.P.d + b)⌉₊ ≤ f (solverConnectedAugmented J).m := by
  let W := dryWitnessUsed
  let T := concreteEdgeThresholdWithLast W
  let E : ℝ := ((2 * a + b : ℕ) : ℝ) * (W.C_γ + 1)
  have hE : 0 ≤ E := by dsimp only [E]; have := W.hCγ; positivity
  let C : ℝ := alg2TimeFactor E (47 / 48) T
  refine ⟨fun M => ⌈max C 0 * alg2TimeFactor E (47 / 48) M⌉₊,
    subpolyNat_ceil_timeFactor C E hE, fun J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set cfg := concreteCirculationCfgWithLast W J
  obtain ⟨hΓ1, hΓ⟩ := concreteCirculationCfgWithLast_gamma_r W J hJn hJm hCap
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm hCap
  have hΓReal1 : 1 ≤ cfg.TP.γ_r (cfg.P.M₀ ^ 2) :=
    (hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)).trans (dryGammaL_le_gammaR J)
  have hΓRealLe : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp ((W.C_γ + 1) * Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) :=
    (Nat.le_ceil _).trans hΓ
  have hM0Eq : cfg.P.M₀ = max I.m T := rfl
  have hdEq : cfg.P.d = chosenD (23 / 24) cfg.P.M₀ := rfl
  have hL1 := one_le_log_add_two' cfg.P.hM₀
  have hLL1 := one_le_log_log_add_two hL1
  obtain ⟨_, _, hdHi⟩ := chosenD_bounds (β := 23 / 24) (by norm_num) cfg.P.hM₀
  rw [← hdEq, show ((1 : ℝ) - 23 / 24) / 2 = 1 / 48 by norm_num] at hdHi
  set L := Real.log ((cfg.P.M₀ : ℝ) + 2)
  set r := L ^ (1 / 48 : ℝ)
  set L23 := L ^ (23 / 24 : ℝ)
  set LL := Real.log (L + 2)
  have hr1 : 1 ≤ r := Real.one_le_rpow hL1 (by norm_num)
  have hrSplit : r * L23 = L ^ (47 / 48 : ℝ) := by
    rw [← Real.rpow_add (by linarith : 0 < L)]; norm_num
  have hLogΓ : Real.log (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ≤ (W.C_γ + 1) * L23 * LL := by
    have h1 := Real.log_le_log (by linarith) hΓRealLe
    rw [Real.log_exp] at h1
    exact h1
  have hLogNN : 0 ≤ Real.log (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) := Real.log_nonneg hΓReal1
  have hExpLe : ((a * cfg.P.d + b : ℕ) : ℝ) * Real.log (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ≤
      E * logShape cfg.P.M₀ := by
    have had : ((a * cfg.P.d + b : ℕ) : ℝ) ≤ ((2 * a + b : ℕ) : ℝ) * r := by
      push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]
    have h1 : ((a * cfg.P.d + b : ℕ) : ℝ) * Real.log (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ≤
        (((2 * a + b : ℕ) : ℝ) * r) * ((W.C_γ + 1) * L23 * LL) :=
      mul_le_mul had hLogΓ hLogNN (by positivity)
    have h2 : (((2 * a + b : ℕ) : ℝ) * r) * ((W.C_γ + 1) * L23 * LL) = E * logShape cfg.P.M₀ := by
      unfold logShape; dsimp only [E, L, LL]; rw [← hrSplit]; ring
    linarith
  have hPowLe : (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (a * cfg.P.d + b) ≤
      alg2TimeFactor E (47 / 48) cfg.P.M₀ := by
    rw [alg2TimeFactor_eq_exp_logShape, ← Real.exp_log (pow_pos (by linarith) _), Real.log_pow]
    exact Real.exp_le_exp.mpr hExpLe
  have hMax := alg2TimeFactor_max_le hE I.m T
  have hCnn : 0 ≤ C := (alg2TimeFactor_pos E (47 / 48) T).le
  rw [hM0Eq] at hPowLe
  exact Nat.ceil_mono (hPowLe.trans (hMax.trans (by rw [max_eq_left hCnn])))

/-- `⌈(cfg.P.M₀ : ℝ) ^ (2 / cfg.P.d)⌉₊` is bounded by a `SubpolyNat` function of `I.m`. -/
theorem dryM0Root_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        ⌈(cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ))⌉₊ ≤ f (solverConnectedAugmented J).m := by
  let T := concreteEdgeThresholdWithLast dryWitnessUsed
  let C : ℝ := alg2TimeFactor 2 (47 / 48) T
  refine ⟨fun M => ⌈max C 0 * alg2TimeFactor 2 (47 / 48) M⌉₊,
    subpolyNat_ceil_timeFactor C 2 (by norm_num), fun J _ _ _ => ?_⟩
  set I := solverConnectedAugmented J
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hM0Eq : cfg.P.M₀ = max I.m T := rfl
  have hdEq : cfg.P.d = chosenD (23 / 24) cfg.P.M₀ := rfl
  have hM1 : (1 : ℝ) ≤ cfg.P.M₀ := by exact_mod_cast cfg.P.hM₀
  have hL1 := one_le_log_add_two' cfg.P.hM₀
  have hLL1 := one_le_log_log_add_two hL1
  obtain ⟨_, hdLo, _⟩ := chosenD_bounds (β := 23 / 24) (by norm_num) cfg.P.hM₀
  rw [← hdEq, show ((1 : ℝ) - 23 / 24) / 2 = 1 / 48 by norm_num] at hdLo
  set L := Real.log ((cfg.P.M₀ : ℝ) + 2)
  set r := L ^ (1 / 48 : ℝ)
  set L47 := L ^ (47 / 48 : ℝ)
  have hrPos : 0 < r := Real.rpow_pos_of_pos (by linarith) _
  have hSplit : r * L47 = L := by rw [← Real.rpow_add (by linarith : 0 < L)]; norm_num
  have hL47A : L47 ≤ logShape cfg.P.M₀ := by
    unfold logShape
    have hnn : 0 ≤ L47 := Real.rpow_nonneg (by linarith) _
    exact le_mul_of_one_le_right hnn hLL1
  have hPow : (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) ≤ alg2TimeFactor 2 (47 / 48) cfg.P.M₀ := by
    rw [alg2TimeFactor_eq_exp_logShape, Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    have hML : Real.log (cfg.P.M₀ : ℝ) ≤ L := Real.log_le_log (by linarith) (by linarith)
    have h1 : Real.log (cfg.P.M₀ : ℝ) * (2 / (cfg.P.d : ℝ)) ≤ L * (2 / r) :=
      mul_le_mul hML (div_le_div_of_nonneg_left (by norm_num) hrPos hdLo)
        (div_nonneg (by norm_num) (by positivity)) (by linarith)
    have h2 : L * (2 / r) = 2 * L47 := by rw [← hSplit]; field_simp
    linarith
  have hMax := alg2TimeFactor_max_le (by norm_num : (0 : ℝ) ≤ 2) I.m T
  have hCnn : 0 ≤ C := (alg2TimeFactor_pos 2 (47 / 48) T).le
  rw [hM0Eq] at hPow
  exact Nat.ceil_mono (hPow.trans (hMax.trans (by rw [max_eq_left hCnn])))

/-! ## 2. `SubpolyNat` bounds on `runtimeFactorNat`, `treeUpdateFactorNat`, weights, and shift quota -/

/-- `runtimeFactorNat cfg` is bounded by a `SubpolyNat` function of `I.m`. -/
theorem dryRuntimeFactor_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        runtimeFactorNat (concreteCirculationCfgWithLast dryWitnessUsed J) ≤
          f (solverConnectedAugmented J).m := by
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  obtain ⟨fR, hfRSub, hfR⟩ := dryM0Root_le_subpoly
  obtain ⟨fG, hfGSub, hfG⟩ := dryGammaRPow_le_subpoly 3 3
  have hLogPoly : PolyNat (fun M => 5 * dryM0OfM M) := PolyNat.const_mul dryM0OfM_poly 5
  have hLogSub : SubpolyNat (fun M => Nat.log 2 (5 * dryM0OfM M + 2) + 1) :=
    subpolyNat_log_of_poly hLogPoly
  let cTVal : ℝ := ((max 1 dryWitnessUsed.spanConst : ℕ) : ℝ) *
    (65 * (37810 * (7 : ℝ) ^ 1 + 1) + 18000)
  let cTConst : ℕ := ⌈cTVal⌉₊ + 1
  let K : ℕ := 3 * (8 * cTConst + 81 * 8 + 430) * 4 ^ 7
  refine ⟨fun M => K * (fd M + 1) * fR M * fG M * (Nat.log 2 (5 * dryM0OfM M + 2) + 1) ^ 7 + 1,
    SubpolyNat.add_const
      (SubpolyNat.mul
        (SubpolyNat.mul
          (SubpolyNat.mul (SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) K) hfRSub)
          hfGSub)
        (SubpolyNat.pow hLogSub 7)) 1,
    fun J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hcT : cfg.TP.c_T ≤ (cTConst : ℝ) := by
    have hEq : cfg.TP.c_T = cTVal := rfl
    rw [hEq]
    have h1 : cTVal ≤ (⌈cTVal⌉₊ : ℝ) := Nat.le_ceil cTVal
    have h2 : (⌈cTVal⌉₊ : ℝ) ≤ (cTConst : ℝ) := by dsimp only [cTConst]; exact_mod_cast Nat.le_succ _
    linarith
  have hpT : cfg.TP.p_T = 6 := rfl
  have hcLast : cfg.LP.c_last = 8 := rfl
  have hpLast : cfg.LP.p_last = 0 := rfl
  have hγL : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.TP.γ_r (cfg.P.M₀ ^ 2) := dryGammaL_le_gammaR J
  have hγL0 : 0 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := by
    have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
    linarith [hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)]
  have hγProd : cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2) ≤
      (fG I.m : ℝ) := by
    have h1 : cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2) ≤
        (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 3) := by
      have hp : (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2) ≤
          (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2) :=
        pow_le_pow_left₀ hγL0 hγL _
      calc cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2)
          ≤ cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2) :=
            mul_le_mul_of_nonneg_left hp (le_trans hγL0 hγL)
        _ = (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 3) := by rw [← pow_succ']
    exact h1.trans ((Nat.le_ceil _).trans (by exact_mod_cast hfG J hJn hJm hCap))
  have hRoot : (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) ≤ (fR I.m : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hfR J hJn hJm hCap)
  have hLog : 2 * logFactor cfg.P cfg.N₀ ≤ 4 * ((Nat.log 2 (5 * dryM0OfM I.m + 2) + 1 : ℕ) : ℝ) := by
    unfold logFactor
    have hArg : (cfg.P.M₀ : ℝ) + (cfg.N₀ : ℝ) + 2 = ((5 * dryM0OfM I.m + 2 : ℕ) : ℝ) := by
      have h1 : cfg.P.M₀ = dryM0OfM I.m := rfl
      have h2 : cfg.N₀ = 4 * dryM0OfM I.m := rfl
      rw [h1, h2]; push_cast; ring
    rw [hArg]
    have hlt : ((5 * dryM0OfM I.m + 2 : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (Nat.log 2 (5 * dryM0OfM I.m + 2) + 1) := by
      exact_mod_cast (Nat.lt_pow_succ_log_self (by decide) (5 * dryM0OfM I.m + 2)).le
    have hl := Real.log_le_log (by positivity) hlt
    rw [Real.log_pow] at hl
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hnn : (0 : ℝ) ≤ (Nat.log 2 (5 * dryM0OfM I.m + 2) + 1 : ℕ) := Nat.cast_nonneg _
    push_cast at hl ⊢
    nlinarith
  have hdR : (cfg.P.d : ℝ) + 1 ≤ ((fd I.m + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right (hfd J hJn hJm hCap) 1
  have hLogPos : 0 ≤ 2 * logFactor cfg.P cfg.N₀ := by
    unfold logFactor
    have : (1 : ℝ) ≤ (cfg.P.M₀ : ℝ) + (cfg.N₀ : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) cfg.P.M₀, Nat.cast_nonneg (α := ℝ) cfg.N₀]
    have := Real.log_nonneg this
    linarith
  have hLogPow : (2 * logFactor cfg.P cfg.N₀) ^ 7 ≤
      (4 : ℝ) ^ 7 * ((Nat.log 2 (5 * dryM0OfM I.m + 2) + 1 : ℕ) : ℝ) ^ 7 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hLogPos hLog 7
  unfold runtimeFactorNat Chain.Ordered.lemma511TimeFactor
  rw [hpT, hcLast, hpLast, show max 6 0 + 1 = 7 by decide]
  apply Nat.ceil_le.mpr
  have hcT0 : 0 ≤ cfg.TP.c_T := by
    have hEq : cfg.TP.c_T = cTVal := rfl
    rw [hEq]; dsimp only [cTVal]; positivity
  have hCoeff : 3 * ((cfg.P.d : ℝ) + 1) * (8 * cfg.TP.c_T + 81 * 8 + 430) ≤
      3 * ((fd I.m + 1 : ℕ) : ℝ) * (8 * (cTConst : ℝ) + 81 * 8 + 430) := by
    have h8 : 0 ≤ 8 * cfg.TP.c_T + 81 * 8 + 430 := by linarith
    have ha : 3 * ((cfg.P.d : ℝ) + 1) ≤ 3 * ((fd I.m + 1 : ℕ) : ℝ) := by linarith
    have hb : 8 * cfg.TP.c_T + 81 * 8 + 430 ≤ 8 * (cTConst : ℝ) + 81 * 8 + 430 := by linarith
    exact mul_le_mul ha hb h8 (by positivity)
  have hProd :
      3 * ((cfg.P.d : ℝ) + 1) * (8 * cfg.TP.c_T + 81 * 8 + 430) *
        (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) *
        (cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2)) *
        (2 * logFactor cfg.P cfg.N₀) ^ 7 ≤
      (3 * ((fd I.m + 1 : ℕ) : ℝ) * (8 * (cTConst : ℝ) + 81 * 8 + 430)) *
        (fR I.m : ℝ) * (fG I.m : ℝ) *
        ((4 : ℝ) ^ 7 * ((Nat.log 2 (5 * dryM0OfM I.m + 2) + 1 : ℕ) : ℝ) ^ 7) := by
    have h1 : 0 ≤ (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h2 : 0 ≤ cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2) :=
      mul_nonneg (le_trans hγL0 hγL) (pow_nonneg hγL0 _)
    have h3 : 0 ≤ 3 * ((fd I.m + 1 : ℕ) : ℝ) * (8 * (cTConst : ℝ) + 81 * 8 + 430) := by positivity
    have h4 : 0 ≤ (2 * logFactor cfg.P cfg.N₀) ^ 7 := pow_nonneg hLogPos 7
    have s1 := mul_le_mul hCoeff hRoot h1 h3
    have s2 := mul_le_mul s1 hγProd h2 (mul_nonneg h3 (Nat.cast_nonneg _))
    exact mul_le_mul s2 hLogPow h4 (mul_nonneg (mul_nonneg h3 (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
  refine hProd.trans ?_
  dsimp only [K]
  push_cast
  linarith

/-- `treeUpdateFactorNat cfg` is bounded by a `SubpolyNat` function of `I.m`. -/
theorem dryTreeUpdateFactor_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        treeUpdateFactorNat (concreteCirculationCfgWithLast dryWitnessUsed J) ≤
          f (solverConnectedAugmented J).m := by
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  obtain ⟨fG, hfGSub, hfG⟩ := dryGammaRPow_le_subpoly 4 2
  refine ⟨fun M => (14 * fd M + 36) * fG M + 1,
    SubpolyNat.add_const
      (SubpolyNat.mul (SubpolyNat.add_const (SubpolyNat.const_mul hfdSub 14) 36) hfGSub) 1,
    fun J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hγL : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.TP.γ_r (cfg.P.M₀ ^ 2) := dryGammaL_le_gammaR J
  have hγL0 : 0 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := by
    have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
    linarith [hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)]
  have hγR0 : 0 ≤ cfg.TP.γ_r (cfg.P.M₀ ^ 2) := le_trans hγL0 hγL
  have hPow : (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (2 * cfg.P.d + 1) ≤
      (fG I.m : ℝ) := by
    have h1 : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
        (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ 2 := by
      rw [sq (cfg.TP.γ_r (cfg.P.M₀ ^ 2))]; exact mul_le_mul_of_nonneg_right hγL hγR0
    have h2 : (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (2 * cfg.P.d + 1) ≤
        (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (4 * cfg.P.d + 2) := by
      calc _ ≤ ((cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ 2) ^ (2 * cfg.P.d + 1) :=
            pow_le_pow_left₀ (mul_nonneg hγL0 hγR0) h1 _
        _ = (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (4 * cfg.P.d + 2) := by rw [← pow_mul]; congr 1; ring
    exact h2.trans ((Nat.le_ceil _).trans (by exact_mod_cast hfG J hJn hJm hCap))
  have hd : 14 * (cfg.P.d : ℝ) + 36 ≤ ((14 * fd I.m + 36 : ℕ) : ℝ) := by
    push_cast; have : (cfg.P.d : ℝ) ≤ (fd I.m : ℝ) := by exact_mod_cast hfd J hJn hJm hCap
    linarith
  unfold treeUpdateFactorNat alg2TreeUpdatesFactor
  apply Nat.ceil_le.mpr
  have h1 : (14 * (cfg.P.d : ℝ) + 36) *
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (2 * cfg.P.d + 1) ≤
      ((14 * fd I.m + 36 : ℕ) : ℝ) * (fG I.m : ℝ) :=
    mul_le_mul hd hPow (pow_nonneg (mul_nonneg hγL0 hγR0) _) (by positivity)
  push_cast at h1 ⊢
  linarith

/-- `fwdWeight` at level `0` is bounded by a `SubpolyNat` function of `I.m`. -/
theorem dryFwdWeight_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        fwdWeight cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) 0 ≤
          f (solverConnectedAugmented J).m := by
  obtain ⟨C, E, hE, hbd⟩ := MinRatio.concrete_fwdWeight_le_timeFactor dryWitnessUsed
  refine ⟨fun M => ⌈max C 0 * alg2TimeFactor E (47 / 48) M⌉₊,
    subpolyNat_ceil_timeFactor C E hE, fun J hJn hJm hCap => ?_⟩
  have h1 := hbd J hJn hJm hCap
  have h2 : C * alg2TimeFactor E (47 / 48) (solverConnectedAugmented J).m ≤
      max C 0 * alg2TimeFactor E (47 / 48) (solverConnectedAugmented J).m :=
    mul_le_mul_of_nonneg_right (le_max_left C 0) (alg2TimeFactor_pos E (47 / 48) _).le
  have h3 := (h1.trans h2).trans (Nat.le_ceil _)
  exact_mod_cast h3

/-- `capFwdWeight` at level `0` is bounded by a `SubpolyNat` function of `I.m`. -/
theorem dryCapFwdWeight_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        capFwdWeight cfg (fwdGamma cfg) 0 ≤ f (solverConnectedAugmented J).m := by
  obtain ⟨C, E, hE, hbd⟩ := MinRatio.concrete_capFwdWeight_le_timeFactor dryWitnessUsed
  refine ⟨fun M => ⌈max C 0 * alg2TimeFactor E (47 / 48) M⌉₊,
    subpolyNat_ceil_timeFactor C E hE, fun J hJn hJm hCap => ?_⟩
  have h1 := hbd J hJn hJm hCap
  have h2 : C * alg2TimeFactor E (47 / 48) (solverConnectedAugmented J).m ≤
      max C 0 * alg2TimeFactor E (47 / 48) (solverConnectedAugmented J).m :=
    mul_le_mul_of_nonneg_right (le_max_left C 0) (alg2TimeFactor_pos E (47 / 48) _).le
  have h3 := (h1.trans h2).trans (Nat.le_ceil _)
  exact_mod_cast h3

/-- Initial `chainRebuildCap cfg 1 0` is at most `(I.m + 1) * f I.m` with `SubpolyNat f`. -/
theorem dryInitRebuildCap_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        chainRebuildCap cfg 1 (fun _ => 0) ≤
          ((solverConnectedAugmented J).m + 1) * f (solverConnectedAugmented J).m := by
  obtain ⟨C, E, hE, hbd⟩ := MinRatio.concrete_initRebuildCap_le_timeFactor dryWitnessUsed
  refine ⟨fun M => ⌈max C 0 * alg2TimeFactor E (47 / 48) M⌉₊,
    subpolyNat_ceil_timeFactor C E hE, fun J hJn hJm hCap => ?_⟩
  have h1 := hbd J hJn hJm hCap
  have h2 : C * alg2TimeFactor E (47 / 48) (solverConnectedAugmented J).m ≤
      (⌈max C 0 * alg2TimeFactor E (47 / 48) (solverConnectedAugmented J).m⌉₊ : ℝ) :=
    (mul_le_mul_of_nonneg_right (le_max_left C 0) (alg2TimeFactor_pos E (47 / 48) _).le).trans
      (Nat.le_ceil _)
  have h3 : (((solverConnectedAugmented J).m + 1 : ℕ) : ℝ) *
      (C * alg2TimeFactor E (47 / 48) (solverConnectedAugmented J).m) ≤
      (((solverConnectedAugmented J).m + 1 : ℕ) : ℝ) *
        (⌈max C 0 * alg2TimeFactor E (47 / 48) (solverConnectedAugmented J).m⌉₊ : ℝ) :=
    mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  have h4 := h1.trans h3
  exact_mod_cast h4

/-- Initial shift-quota product `(d + 1) * ⌊(10 * Ψ_g * k)^{d+1}⌋₊` is at most `(I.m + 1) * f I.m`
with `SubpolyNat f`. -/
theorem dryInitShiftQuota_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        (cfg.P.d + 1) * ⌊(10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1)⌋₊ ≤
          ((solverConnectedAugmented J).m + 1) * f (solverConnectedAugmented J).m := by
  let T := concreteEdgeThresholdWithLast dryWitnessUsed
  let E : ℝ := 22
  have hE : 0 ≤ E := by norm_num [E]
  let C : ℝ := 9 * (T : ℝ) * alg2TimeFactor E (47 / 48) T
  refine ⟨fun M => ⌈max C 0 * alg2TimeFactor E (47 / 48) M⌉₊,
    subpolyNat_ceil_timeFactor C E hE, fun J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  set psi := alg2PsiGame cfg.Ψ cfg.P.M₀
  obtain ⟨_, _, hPsi, _, _⟩ := concreteCirculation_bounds_of
    (le_max_left dryWitnessUsed.M_thresh _) (le_max_right dryWitnessUsed.M_thresh _)
    (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed) J hJn hJm hCap
  have hpsi : 1 ≤ psi := alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀
  have hM0Eq : cfg.P.M₀ = max I.m T := rfl
  have hdEq : cfg.P.d = chosenD (23 / 24) cfg.P.M₀ := rfl
  have hM1 : (1 : ℝ) ≤ cfg.P.M₀ := by exact_mod_cast cfg.P.hM₀
  have hkd : (cfg.P.k : ℝ) ^ (cfg.P.d + 1) ≤
      (cfg.P.M₀ : ℝ) * (2 : ℝ) ^ (cfg.P.d + 1) * (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) := by
    have hk := cfg.P.hk_upper
    have hkpow : (cfg.P.k : ℝ) ^ cfg.P.d ≤ (2 : ℝ) ^ cfg.P.d * (cfg.P.M₀ : ℝ) := by
      have h1 := pow_le_pow_left₀ (Nat.cast_nonneg _) hk cfg.P.d
      rw [mul_pow, ← Real.rpow_natCast ((cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ))),
        ← Real.rpow_mul (by linarith)] at h1
      have hdne : (cfg.P.d : ℝ) ≠ 0 := by exact_mod_cast cfg.P.hd.ne'
      rw [one_div_mul_cancel hdne, Real.rpow_one] at h1
      exact h1
    have hroot : (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) ≤ (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le hM1 ?_
      have hdpos : (0 : ℝ) < cfg.P.d := by exact_mod_cast cfg.P.hd
      exact div_le_div_of_nonneg_right (by norm_num) hdpos.le
    calc (cfg.P.k : ℝ) ^ (cfg.P.d + 1)
        = (cfg.P.k : ℝ) ^ cfg.P.d * (cfg.P.k : ℝ) := pow_succ _ _
      _ ≤ ((2 : ℝ) ^ cfg.P.d * (cfg.P.M₀ : ℝ)) * (2 * (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ))) :=
          mul_le_mul hkpow hk (Nat.cast_nonneg _) (by positivity)
      _ = (cfg.P.M₀ : ℝ) * (2 : ℝ) ^ (cfg.P.d + 1) * (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) := by
          rw [pow_succ]; ring
      _ ≤ (cfg.P.M₀ : ℝ) * (2 : ℝ) ^ (cfg.P.d + 1) * (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) := by
          gcongr
  have hReal : ((cfg.P.d + 1 : ℕ) : ℝ) * (10 * psi * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1) ≤
      (cfg.P.M₀ : ℝ) * (9 * alg2TimeFactor E (47 / 48) cfg.P.M₀) := by
    have h10 : (10 * psi) ^ (cfg.P.d + 1) ≤ (11 * psi) ^ (cfg.P.d + 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have h2pow : (2 : ℝ) ^ (cfg.P.d + 1) ≤ (2 : ℝ) ^ (cfg.P.d + 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hBase := shiftDepositBound_le_exp cfg.P cfg.P.M₀ hpsi (C_N := 1) zero_le_one hdEq
      (by linarith) hPsi
    have hclog1 : (1 : ℝ) ≤ (Nat.clog 2 (cfg.P.M₀ + 2) : ℝ) ^ 2 := by
      have : 1 ≤ Nat.clog 2 (cfg.P.M₀ + 2) := Nat.succ_le_of_lt (Nat.clog_pos (by omega) (by omega))
      have : (1 : ℝ) ≤ (Nat.clog 2 (cfg.P.M₀ + 2) : ℝ) := by exact_mod_cast this
      nlinarith
    have hBase' : ((cfg.P.d : ℝ) + 1) * (11 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 2) *
        (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) ≤ 9 * alg2TimeFactor E (47 / 48) cfg.P.M₀ := by
      rw [alg2TimeFactor_eq_exp_logShape]
      have hnn : 0 ≤ ((cfg.P.d : ℝ) + 1) * (11 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 2) *
          (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) := by positivity
      have h1 := le_mul_of_one_le_right hnn hclog1
      have h2 : (1 + 2 * (1 : ℝ)) ^ 2 = 9 := by norm_num
      have h3 : (19 + 3 * (1 : ℝ)) = E := by norm_num [E]
      rw [h2, h3] at hBase
      exact h1.trans hBase
    calc ((cfg.P.d + 1 : ℕ) : ℝ) * (10 * psi * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1)
        = ((cfg.P.d : ℝ) + 1) * (10 * psi) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) ^ (cfg.P.d + 1) := by
          push_cast; rw [mul_pow]; ring
      _ ≤ ((cfg.P.d : ℝ) + 1) * (11 * psi) ^ (cfg.P.d + 1) *
            ((cfg.P.M₀ : ℝ) * (2 : ℝ) ^ (cfg.P.d + 1) * (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ))) := by
          have hnn1 : 0 ≤ ((cfg.P.d : ℝ) + 1) * (10 * psi) ^ (cfg.P.d + 1) := by positivity
          have hnn2 : 0 ≤ (cfg.P.k : ℝ) ^ (cfg.P.d + 1) := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left h10 (by positivity)) hkd hnn2 (by positivity)
      _ ≤ (cfg.P.M₀ : ℝ) * (((cfg.P.d : ℝ) + 1) * (11 * psi) ^ (cfg.P.d + 1) *
            (2 : ℝ) ^ (cfg.P.d + 2) * (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ))) := by
          have : 0 ≤ (cfg.P.M₀ : ℝ) * ((cfg.P.d : ℝ) + 1) * (11 * psi) ^ (cfg.P.d + 1) *
              (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) := by positivity
          have hmul := mul_le_mul_of_nonneg_left h2pow this
          linarith
      _ ≤ (cfg.P.M₀ : ℝ) * (9 * alg2TimeFactor E (47 / 48) cfg.P.M₀) :=
          mul_le_mul_of_nonneg_left hBase' (by linarith)
  have hMaxLe : ((max I.m T : ℕ) : ℝ) ≤ ((I.m + 1 : ℕ) : ℝ) * (T : ℝ) := by
    have hT1 : 1 ≤ T := le_trans (by decide) (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed)
    have hnat : max I.m T ≤ (I.m + 1) * T := by
      rcases le_total I.m T with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith
    exact_mod_cast hnat
  have hFin : (((cfg.P.d + 1) * ⌊(10 * psi * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1)⌋₊ : ℕ) : ℝ) ≤
      ((I.m + 1 : ℕ) : ℝ) * (⌈max C 0 * alg2TimeFactor E (47 / 48) I.m⌉₊ : ℝ) := by
    have hfl : (⌊(10 * psi * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1)⌋₊ : ℝ) ≤
        (10 * psi * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1) := Nat.floor_le (by positivity)
    have hstep1 : (((cfg.P.d + 1) * ⌊(10 * psi * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1)⌋₊ : ℕ) : ℝ) ≤
        ((cfg.P.d + 1 : ℕ) : ℝ) * (10 * psi * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1) := by
      push_cast; exact mul_le_mul_of_nonneg_left hfl (by positivity)
    have hstep2 : (cfg.P.M₀ : ℝ) * (9 * alg2TimeFactor E (47 / 48) cfg.P.M₀) ≤
        ((I.m + 1 : ℕ) : ℝ) * (C * alg2TimeFactor E (47 / 48) I.m) := by
      rw [hM0Eq]
      have htf := alg2TimeFactor_max_le hE I.m T
      have hnn : 0 ≤ 9 * alg2TimeFactor E (47 / 48) (max I.m T) :=
        mul_nonneg (by norm_num) (alg2TimeFactor_pos E (47 / 48) _).le
      calc ((max I.m T : ℕ) : ℝ) * (9 * alg2TimeFactor E (47 / 48) (max I.m T))
          ≤ (((I.m + 1 : ℕ) : ℝ) * (T : ℝ)) *
              (9 * (alg2TimeFactor E (47 / 48) T * alg2TimeFactor E (47 / 48) I.m)) :=
            mul_le_mul hMaxLe (mul_le_mul_of_nonneg_left htf (by norm_num)) hnn (by positivity)
        _ = ((I.m + 1 : ℕ) : ℝ) * (C * alg2TimeFactor E (47 / 48) I.m) := by dsimp only [C]; ring
    have hCnn : 0 ≤ C := by dsimp only [C]; have := alg2TimeFactor_pos E (47 / 48) T; positivity
    have hceil : C * alg2TimeFactor E (47 / 48) I.m ≤
        (⌈max C 0 * alg2TimeFactor E (47 / 48) I.m⌉₊ : ℝ) := by
      rw [max_eq_left hCnn]; exact Nat.le_ceil _
    exact hstep1.trans (hReal.trans (hstep2.trans (mul_le_mul_of_nonneg_left hceil (by positivity))))
  exact_mod_cast hFin

/-- `loopMax = (loopDigitCap cfg + 1) ^ (d + 1)` is bounded by a `PolyNat` function of `I.m`. -/
theorem dryLoopMax_le_poly :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        (Chain.Ordered.loopDigitCap cfg + 1) ^ (cfg.P.d + 1) ≤ f (solverConnectedAugmented J).m := by
  obtain ⟨f, hfSub, hf⟩ := dryInitShiftQuota_le_subpoly
  refine ⟨fun M => (M + 1) * f M,
    PolyNat.mul (PolyNat.add_const PolyNat.id 1) (SubpolyNat.toPolyNat hfSub),
    fun J hJn hJm hCap => ?_⟩
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  set psi := alg2PsiGame cfg.Ψ cfg.P.M₀
  have hpsi : 1 ≤ psi := alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀
  have hk1 : (1 : ℝ) ≤ (cfg.P.k : ℝ) := by exact_mod_cast (show 1 ≤ cfg.P.k by have := cfg.P.hk; omega)
  have hbase : ((Chain.Ordered.loopDigitCap cfg + 1 : ℕ) : ℝ) ≤ 10 * psi * (cfg.P.k : ℝ) := by
    unfold Chain.Ordered.loopDigitCap
    have hc : (⌈2 * psi⌉₊ : ℝ) ≤ 2 * psi + 1 := (Nat.ceil_lt_add_one (by linarith)).le
    push_cast
    nlinarith
  have hpow : (((Chain.Ordered.loopDigitCap cfg + 1) ^ (cfg.P.d + 1) : ℕ) : ℝ) ≤
      (10 * psi * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1) := by
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
  have hfl : (Chain.Ordered.loopDigitCap cfg + 1) ^ (cfg.P.d + 1) ≤
      ⌊(10 * psi * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1)⌋₊ := Nat.le_floor hpow
  have hmul : ⌊(10 * psi * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1)⌋₊ ≤
      (cfg.P.d + 1) * ⌊(10 * psi * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1)⌋₊ :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  exact (hfl.trans hmul).trans (hf J hJn hJm hCap)

/-- Every level size `levelM cfg.TP cfg.P i` (for `i ≤ cfg.P.d`) is at most `(I.m + 1) * f I.m`
with `SubpolyNat f`. -/
theorem dryLevelM_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        ∀ i ≤ cfg.P.d, levelM cfg.TP cfg.P i ≤
          ((solverConnectedAugmented J).m + 1) * f (solverConnectedAugmented J).m := by
  obtain ⟨fG, hfGSub, hfG⟩ := dryGammaRPow_le_subpoly 1 1
  let K : ℕ := concreteEdgeThresholdWithLast dryWitnessUsed + 1
  refine ⟨fun M => K * fG M + 1, SubpolyNat.add_const (SubpolyNat.const_mul hfGSub K) 1,
    fun J hJn hJm hCap i hi => ?_⟩
  set I := solverConnectedAugmented J
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hγL : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.TP.γ_r (cfg.P.M₀ ^ 2) := dryGammaL_le_gammaR J
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hγL1 : 1 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)
  have hγR1 : 1 ≤ cfg.TP.γ_r (cfg.P.M₀ ^ 2) := hγL1.trans hγL
  have hk1 : (1 : ℝ) ≤ (cfg.P.k : ℝ) := by exact_mod_cast (show 1 ≤ cfg.P.k by have := cfg.P.hk; omega)
  have hdiv : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / (cfg.P.k : ℝ) ≤ cfg.TP.γ_r (cfg.P.M₀ ^ 2) :=
    (div_le_self (by linarith) hk1).trans hγL
  have harg : (cfg.P.M₀ : ℝ) * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) *
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / (cfg.P.k : ℝ)) ^ i ≤
      (cfg.P.M₀ : ℝ) * (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (1 * cfg.P.d + 1) := by
    have hp : (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / (cfg.P.k : ℝ)) ^ i ≤
        (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ cfg.P.d :=
      (pow_le_pow_left₀ (by positivity) hdiv i).trans (pow_le_pow_right₀ hγR1 hi)
    have h1 : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / (cfg.P.k : ℝ)) ^ i ≤
        (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (1 * cfg.P.d + 1) := by
      rw [one_mul, pow_succ' (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) cfg.P.d]
      exact mul_le_mul hγL hp (by positivity) (by linarith)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
  have hceil : levelM cfg.TP cfg.P i ≤
      cfg.P.M₀ * ⌈(cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (1 * cfg.P.d + 1)⌉₊ := by
    unfold levelM
    apply Nat.ceil_le.mpr
    refine harg.trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg _)
  have hM0 : cfg.P.M₀ ≤ K * (I.m + 1) := dryM0OfM_le_mul I.m
  have hG := hfG J hJn hJm hCap
  have hmul : cfg.P.M₀ * ⌈(cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (1 * cfg.P.d + 1)⌉₊ ≤
      (K * (I.m + 1)) * fG I.m := Nat.mul_le_mul hM0 hG
  calc levelM cfg.TP cfg.P i ≤ (K * (I.m + 1)) * fG I.m := hceil.trans hmul
    _ = (I.m + 1) * (K * fG I.m) := by ring
    _ ≤ (I.m + 1) * (K * fG I.m + 1) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

end MinCostFlow.Final.DryRun

end
