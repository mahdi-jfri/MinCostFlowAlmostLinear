module

public import MinCostFlow.Final.AssemblyDryRunSCInnerSizes
public import MinCostFlow.Final.AssemblyDryRunSCDeepAsymp
import MinCostFlow.Final.AssemblyDryRunSCAsymp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Asymptotic `PolyNat` and `SubpolyNat` bounds for the Branch-B step cap (`AssemblyDryRunSCInnerStepCapAsymp`)

Proves the per-level and chained asymptotic bounds for `dryInnerCoreStepCap`
(`Final/AssemblyDryRunSCInnerSizes.lean`):

* `dryCfgK_le_subpoly`: `cfg.P.k` is bounded by a `SubpolyNat` function of `I.m`.
* `dryUpdateCoreStepRatioPow_le_subpoly`: `(updateCoreStepRatio edMul (levelM 0) cfg.N₀) ^ cfg.P.d`
  is bounded by a `SubpolyNat` function of `I.m`.
* `dryConstPowD_le_subpoly`: `c ^ cfg.P.d` is bounded by a `SubpolyNat` function of `I.m`.
* `dryCfgKPowD_le_poly`: `cfg.P.k ^ cfg.P.d` is bounded by a `PolyNat` function of `I.m`
  (via `cfg.P.hk_upper`, `k ≤ 2 * M₀ ^ (1 / d)`).
* `dryStepCapRPowD_le_poly`: `(122 * cfg.P.k * B₀ ^ 2) ^ cfg.P.d` is `PolyNat` in `I.m`, and
  `dryStepCapR J j ≤ 122 * cfg.P.k * B₀ ^ 2` for all `j`.
* `dryStepCapS_le_poly`: `dryStepCapS J j` is uniformly `PolyNat` in `I.m` for `j ≤ cfg.P.d`.
* `dryBranchBCaps_le_poly`: `branchBCapUL`, `branchBCapBW`, and `branchBCapEW` at
  `dryInnerCoreStepCap J` and `u = 2 * I.m` are uniformly `PolyNat` in `I.m` for `j ≤ cfg.P.d`.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. `SubpolyNat` bounds on `cfg.P.k`, `R ^ d`, and `c ^ d` -/

/-- `cfg.P.k` is bounded by a `SubpolyNat` function of `I.m`. -/
theorem dryCfgK_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        (concreteCirculationCfgWithLast dryWitnessUsed J).P.k ≤ f (solverConnectedAugmented J).m := by
  obtain ⟨fR, hfRSub, hfR⟩ := dryM0Root_le_subpoly
  refine ⟨fun M => 2 * fR M, SubpolyNat.const_mul hfRSub 2, fun J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hM1 : (1 : ℝ) ≤ cfg.P.M₀ := by exact_mod_cast cfg.P.hM₀
  have hdPos : (0 : ℝ) < cfg.P.d := by exact_mod_cast cfg.P.hd
  have hroot : (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) ≤ (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hM1 (div_le_div_of_nonneg_right (by norm_num) hdPos.le)
  have hceil : (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) ≤ (fR I.m : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hfR J hJn hJm hCap)
  have hkReal : (cfg.P.k : ℝ) ≤ ((2 * fR I.m : ℕ) : ℝ) := by
    push_cast
    linarith [cfg.P.hk_upper, hroot, hceil]
  exact_mod_cast hkReal

/-- `(updateCoreStepRatio edMul (levelM 0) cfg.N₀) ^ cfg.P.d` is bounded by a `SubpolyNat`
function of `I.m`. -/
theorem dryUpdateCoreStepRatioPow_le_subpoly (Psc : DrySparseCorePieces) :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let edMul := drySCEdMul Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
        (updateCoreStepRatio edMul (levelM cfg.TP cfg.P 0) cfg.N₀) ^ cfg.P.d ≤
          f (solverConnectedAugmented J).m := by
  obtain ⟨fLM, hfLMSub, hfLM⟩ := dryLevelM_le_subpoly
  let edMul := drySCEdMul Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
  let T := concreteEdgeThresholdWithLast dryWitnessUsed
  have hArgPoly : PolyNat (fun M => (M + 1) * fLM M + 4 * dryM0OfM M + 2) :=
    PolyNat.add_const
      (PolyNat.add (PolyNat.mul (PolyNat.add_const PolyNat.id 1) (SubpolyNat.toPolyNat hfLMSub))
        (PolyNat.const_mul dryM0OfM_poly 4)) 2
  obtain ⟨c₁, p₁, hc₁⟩ := hArgPoly
  let c₂ : ℕ := max 1 c₁
  let p₂ : ℕ := max 1 p₁
  let K₁ : ℕ := 2 * (c₂ + p₂) + 1
  let K₂ : ℕ := (edMul + 6) * K₁ ^ 2 + 2
  let E : ℝ := 2 * ((K₂ : ℝ) + 2)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  let C : ℝ := alg2TimeFactor E (47 / 48) T
  refine ⟨fun M => ⌈max C 0 * alg2TimeFactor E (47 / 48) M⌉₊,
    subpolyNat_ceil_timeFactor C E hE, fun J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hM0Eq : cfg.P.M₀ = max I.m T := rfl
  have hdEq : cfg.P.d = chosenD (23 / 24) cfg.P.M₀ := rfl
  have hL1 := one_le_log_add_two' cfg.P.hM₀
  have hLL1 := one_le_log_log_add_two hL1
  obtain ⟨_, _, hdHi⟩ := chosenD_bounds (β := 23 / 24) (by norm_num) cfg.P.hM₀
  rw [← hdEq, show ((1 : ℝ) - 23 / 24) / 2 = 1 / 48 by norm_num] at hdHi
  set L := Real.log ((cfg.P.M₀ : ℝ) + 2)
  set LL := Real.log (L + 2)
  have hLpos : 0 < L := by linarith
  have hArgLe : levelM cfg.TP cfg.P 0 + cfg.N₀ + 2 ≤ c₂ * (cfg.P.M₀ + 2) ^ p₂ := by
    have hM0 : levelM cfg.TP cfg.P 0 ≤ (I.m + 1) * fLM I.m := hfLM J hJn hJm hCap 0 (Nat.zero_le _)
    have hN0 : cfg.N₀ = 4 * dryM0OfM I.m := rfl
    have h1 : levelM cfg.TP cfg.P 0 + cfg.N₀ + 2 ≤ c₁ * (I.m + 2) ^ p₁ := by
      have hc := hc₁ I.m
      dsimp only at hc
      rw [hN0]
      omega
    have hIM0 : I.m + 2 ≤ cfg.P.M₀ + 2 := by
      have : I.m ≤ cfg.P.M₀ := le_max_left _ _
      omega
    have hpow1 : (I.m + 2) ^ p₁ ≤ (cfg.P.M₀ + 2) ^ p₁ := Nat.pow_le_pow_left hIM0 p₁
    have hpow2 : (cfg.P.M₀ + 2) ^ p₁ ≤ (cfg.P.M₀ + 2) ^ p₂ :=
      Nat.pow_le_pow_right (by omega) (le_max_right 1 p₁)
    exact h1.trans (Nat.mul_le_mul (le_max_right 1 c₁) (hpow1.trans hpow2))
  have hLogNat : ((Nat.log 2 (levelM cfg.TP cfg.P 0 + cfg.N₀ + 2) + 1 : ℕ) : ℝ) ≤ (K₁ : ℝ) * L := by
    set n := levelM cfg.TP cfg.P 0 + cfg.N₀ + 2
    have hnPos : n ≠ 0 := by dsimp only [n]; omega
    have hpow : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 hnPos
    have hlog2Pos : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlogPow : ((Nat.log 2 n : ℕ) : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
      have h1 := Real.log_le_log (by positivity) hpow
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h1
      exact h1
    have hnReal : (n : ℝ) ≤ (c₂ : ℝ) * ((cfg.P.M₀ : ℝ) + 2) ^ p₂ := by
      exact_mod_cast hArgLe
    have hlogN : Real.log (n : ℝ) ≤ ((c₂ + p₂ : ℕ) : ℝ) * L := by
      have hc2Pos : (0 : ℝ) < (c₂ : ℝ) := by
        have : 1 ≤ c₂ := le_max_left 1 c₁
        exact_mod_cast this
      have h1 := Real.log_le_log (by positivity) hnReal
      rw [Real.log_mul hc2Pos.ne' (by positivity), Real.log_pow] at h1
      have hlogc : Real.log (c₂ : ℝ) ≤ (c₂ : ℝ) := by
        linarith [Real.log_le_sub_one_of_pos hc2Pos]
      have hlogcL : Real.log (c₂ : ℝ) ≤ (c₂ : ℝ) * L := by nlinarith
      push_cast
      nlinarith
    have hlogLe : ((Nat.log 2 n : ℕ) : ℝ) ≤ 2 * ((c₂ + p₂ : ℕ) : ℝ) * L := by
      nlinarith [hlogPow, hlog2Pos, hlogN]
    push_cast at hlogLe ⊢
    dsimp only [K₁]
    push_cast
    linarith only [hlogLe, hL1]
  set R := updateCoreStepRatio edMul (levelM cfg.TP cfg.P 0) cfg.N₀
  have hRge2 : (2 : ℝ) ≤ (R : ℝ) := by
    have : 2 ≤ R := by unfold R updateCoreStepRatio; omega
    exact_mod_cast this
  have hRPos : (0 : ℝ) < (R : ℝ) := by linarith
  have hRLe : (R : ℝ) ≤ (K₂ : ℝ) * L ^ 2 := by
    have hB0 : (SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ : ℝ) ≤
        ((K₁ : ℝ) ^ 2) * L ^ 2 := by
      unfold SparseCore.bundleLogFactor
      have hsq : (((Nat.log 2 (levelM cfg.TP cfg.P 0 + cfg.N₀ + 2) + 1 : ℕ) : ℝ)) ^ 2 ≤
          ((K₁ : ℝ) * L) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hLogNat 2
      have hmul : ((K₁ : ℝ) * L) ^ 2 = (K₁ : ℝ) ^ 2 * L ^ 2 := by ring
      rw [Nat.cast_pow]
      linarith
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    have hREq : (R : ℝ) = ((edMul + 6 : ℕ) : ℝ) *
        (SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ : ℝ) + 2 := by
      have hRn : R = (edMul + 6) * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ + 2 :=
        rfl
      rw [hRn]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have hK2Eq : (K₂ : ℝ) = ((edMul + 6 : ℕ) : ℝ) * (K₁ : ℝ) ^ 2 + 2 := by
      have hK2n : K₂ = (edMul + 6) * K₁ ^ 2 + 2 := rfl
      rw [hK2n]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have h1 : ((edMul + 6 : ℕ) : ℝ) *
        (SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ : ℝ) ≤
        ((edMul + 6 : ℕ) : ℝ) * ((K₁ : ℝ) ^ 2 * L ^ 2) :=
      mul_le_mul_of_nonneg_left hB0 (Nat.cast_nonneg _)
    rw [hREq, hK2Eq]
    nlinarith only [h1, hL2]
  have hLogR : Real.log (R : ℝ) ≤ ((K₂ : ℝ) + 2) * LL := by
    have hK2Pos : (0 : ℝ) < (K₂ : ℝ) := by
      have : 0 < K₂ := by dsimp only [K₂]; omega
      exact_mod_cast this
    have h1 := Real.log_le_log hRPos hRLe
    rw [Real.log_mul hK2Pos.ne' (pow_pos hLpos 2).ne', Real.log_pow] at h1
    simp only [Nat.cast_ofNat] at h1
    have hlogK2 : Real.log (K₂ : ℝ) ≤ (K₂ : ℝ) := by linarith [Real.log_le_sub_one_of_pos hK2Pos]
    have hlogL : Real.log L ≤ LL := Real.log_le_log hLpos (by linarith)
    nlinarith only [h1, hlogK2, hlogL, hLL1, hK2Pos]
  have hExpLe : (cfg.P.d : ℝ) * Real.log (R : ℝ) ≤ E * logShape cfg.P.M₀ := by
    have hrPow : L ^ (1 / 48 : ℝ) ≤ L ^ (47 / 48 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hd47 : (cfg.P.d : ℝ) ≤ 2 * L ^ (47 / 48 : ℝ) := by linarith
    have hLogRNN : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by linarith)
    have h1 : (cfg.P.d : ℝ) * Real.log (R : ℝ) ≤ (2 * L ^ (47 / 48 : ℝ)) * (((K₂ : ℝ) + 2) * LL) :=
      mul_le_mul hd47 hLogR hLogRNN (by positivity)
    have h2 : (2 * L ^ (47 / 48 : ℝ)) * (((K₂ : ℝ) + 2) * LL) = E * logShape cfg.P.M₀ := by
      unfold logShape; dsimp only [E, L, LL]; ring
    linarith
  have hPowLe : ((R ^ cfg.P.d : ℕ) : ℝ) ≤ alg2TimeFactor E (47 / 48) cfg.P.M₀ := by
    rw [alg2TimeFactor_eq_exp_logShape, Nat.cast_pow,
      ← Real.exp_log (pow_pos hRPos cfg.P.d), Real.log_pow]
    exact Real.exp_le_exp.mpr hExpLe
  have hMax := alg2TimeFactor_max_le hE I.m T
  have hCnn : 0 ≤ C := (alg2TimeFactor_pos E (47 / 48) T).le
  rw [hM0Eq] at hPowLe
  have hFin : ((R ^ cfg.P.d : ℕ) : ℝ) ≤ (⌈max C 0 * alg2TimeFactor E (47 / 48) I.m⌉₊ : ℝ) :=
    (hPowLe.trans (hMax.trans (by rw [max_eq_left hCnn]))).trans (Nat.le_ceil _)
  exact_mod_cast hFin

/-- For any fixed constant `c : ℕ`, `c ^ cfg.P.d` is bounded by a `SubpolyNat` function of `I.m`. -/
theorem dryConstPowD_le_subpoly (c : ℕ) :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        c ^ (concreteCirculationCfgWithLast dryWitnessUsed J).P.d ≤
          f (solverConnectedAugmented J).m := by
  let c₁ : ℕ := max 1 c
  let T := concreteEdgeThresholdWithLast dryWitnessUsed
  let E : ℝ := 2 * (c₁ : ℝ)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  let C : ℝ := alg2TimeFactor E (47 / 48) T
  refine ⟨fun M => ⌈max C 0 * alg2TimeFactor E (47 / 48) M⌉₊,
    subpolyNat_ceil_timeFactor C E hE, fun J _ _ _ => ?_⟩
  set I := solverConnectedAugmented J
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hcLe : c ^ cfg.P.d ≤ c₁ ^ cfg.P.d := Nat.pow_le_pow_left (le_max_right 1 c) _
  have hc1Pos : (0 : ℝ) < (c₁ : ℝ) := by
    have : 1 ≤ c₁ := le_max_left 1 c
    exact_mod_cast this
  have hM0Eq : cfg.P.M₀ = max I.m T := rfl
  have hdEq : cfg.P.d = chosenD (23 / 24) cfg.P.M₀ := rfl
  have hL1 := one_le_log_add_two' cfg.P.hM₀
  have hLL1 := one_le_log_log_add_two hL1
  obtain ⟨_, _, hdHi⟩ := chosenD_bounds (β := 23 / 24) (by norm_num) cfg.P.hM₀
  rw [← hdEq, show ((1 : ℝ) - 23 / 24) / 2 = 1 / 48 by norm_num] at hdHi
  set L := Real.log ((cfg.P.M₀ : ℝ) + 2)
  set LL := Real.log (L + 2)
  have hrPow : L ^ (1 / 48 : ℝ) ≤ L ^ (47 / 48 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hd47 : (cfg.P.d : ℝ) ≤ 2 * L ^ (47 / 48 : ℝ) := by linarith
  have hLogC : Real.log (c₁ : ℝ) ≤ (c₁ : ℝ) * LL := by
    have h1 : Real.log (c₁ : ℝ) ≤ (c₁ : ℝ) := by linarith [Real.log_le_sub_one_of_pos hc1Pos]
    nlinarith [h1, hLL1, hc1Pos]
  have hLogNN : 0 ≤ Real.log (c₁ : ℝ) := Real.log_nonneg (by
    have : 1 ≤ c₁ := le_max_left 1 c; exact_mod_cast this)
  have hExpLe : (cfg.P.d : ℝ) * Real.log (c₁ : ℝ) ≤ E * logShape cfg.P.M₀ := by
    have h1 : (cfg.P.d : ℝ) * Real.log (c₁ : ℝ) ≤ (2 * L ^ (47 / 48 : ℝ)) * ((c₁ : ℝ) * LL) :=
      mul_le_mul hd47 hLogC hLogNN (by positivity)
    have h2 : (2 * L ^ (47 / 48 : ℝ)) * ((c₁ : ℝ) * LL) = E * logShape cfg.P.M₀ := by
      unfold logShape; dsimp only [E, L, LL]; ring
    linarith
  have hPowLe : ((c₁ ^ cfg.P.d : ℕ) : ℝ) ≤ alg2TimeFactor E (47 / 48) cfg.P.M₀ := by
    rw [alg2TimeFactor_eq_exp_logShape, Nat.cast_pow,
      ← Real.exp_log (pow_pos hc1Pos cfg.P.d), Real.log_pow]
    exact Real.exp_le_exp.mpr hExpLe
  have hMax := alg2TimeFactor_max_le hE I.m T
  have hCnn : 0 ≤ C := (alg2TimeFactor_pos E (47 / 48) T).le
  rw [hM0Eq] at hPowLe
  have hFin : ((c₁ ^ cfg.P.d : ℕ) : ℝ) ≤ (⌈max C 0 * alg2TimeFactor E (47 / 48) I.m⌉₊ : ℝ) :=
    (hPowLe.trans (hMax.trans (by rw [max_eq_left hCnn]))).trans (Nat.le_ceil _)
  exact hcLe.trans (by exact_mod_cast hFin)

/-- `cfg.P.k ^ cfg.P.d` is bounded by a `PolyNat` function of `I.m`. -/
theorem dryCfgKPowD_le_poly :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        (concreteCirculationCfgWithLast dryWitnessUsed J).P.k ^
            (concreteCirculationCfgWithLast dryWitnessUsed J).P.d ≤
          f (solverConnectedAugmented J).m := by
  obtain ⟨f2, hf2Sub, hf2⟩ := dryConstPowD_le_subpoly 2
  refine ⟨fun M => f2 M * dryM0OfM M,
    PolyNat.mul (SubpolyNat.toPolyNat hf2Sub) dryM0OfM_poly, fun J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hM0Pos : (0 : ℝ) < (cfg.P.M₀ : ℝ) := by exact_mod_cast cfg.P.hM₀
  have hdNe : (cfg.P.d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp cfg.P.hd)
  have hPow : ((cfg.P.k ^ cfg.P.d : ℕ) : ℝ) ≤ ((2 ^ cfg.P.d * cfg.P.M₀ : ℕ) : ℝ) := by
    have hkLe : (cfg.P.k : ℝ) ≤ 2 * (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) := cfg.P.hk_upper
    have h1 := pow_le_pow_left₀ (Nat.cast_nonneg _) hkLe cfg.P.d
    rw [mul_pow, ← Real.rpow_natCast ((cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ))) cfg.P.d,
      ← Real.rpow_mul hM0Pos.le, one_div_mul_cancel hdNe, Real.rpow_one] at h1
    push_cast at h1 ⊢
    exact h1
  have hNat : cfg.P.k ^ cfg.P.d ≤ 2 ^ cfg.P.d * cfg.P.M₀ := by exact_mod_cast hPow
  have h2d : 2 ^ cfg.P.d ≤ f2 I.m := hf2 J hJn hJm hCap
  have hM0Eq : cfg.P.M₀ = dryM0OfM I.m := rfl
  rw [hM0Eq] at hNat
  exact hNat.trans (Nat.mul_le_mul_right _ h2d)

/-! ## 2. `PolyNat` bounds on `dryStepCapR ^ d`, `dryStepCapS`, and chained Branch-B caps -/

private lemma dryLevelM_le_zero (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e) (j : ℕ) :
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    levelM cfg.TP cfg.P j ≤ levelM cfg.TP cfg.P 0 := by
  intro cfg
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCapPos
  have hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ (cfg.P.k : ℝ) := hV.hγk
  have hkPos : (0 : ℝ) < (cfg.P.k : ℝ) := by exact_mod_cast cfg.P.hk
  have hγNN : 0 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := by linarith [hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)]
  have hdiv : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / (cfg.P.k : ℝ) ≤ 1 := (div_le_one hkPos).mpr hγk
  have hpow : (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / (cfg.P.k : ℝ)) ^ j ≤ 1 :=
    pow_le_one₀ (div_nonneg hγNN hkPos.le) hdiv
  unfold levelM
  apply Nat.ceil_mono
  rw [pow_zero, mul_one]
  exact mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg _) hγNN) hpow

private lemma branchBCapUL_le_of_affine {stepCap : ℕ → ℕ → ℕ} {R S u n : ℕ}
    (hR1 : 1 ≤ R) (hCap : ∀ j < n, ∀ b, stepCap j b ≤ R * (S + b)) :
    ∀ j ≤ n, branchBCapUL stepCap u j ≤ R ^ j * u + j * R ^ j * S
  | 0, _ => by simp [branchBCapUL]
  | j + 1, hj => by
    have ih := branchBCapUL_le_of_affine (u := u) hR1 hCap j (Nat.le_of_succ_le hj)
    have hstep := hCap j hj (branchBCapUL stepCap u j)
    have hpow : 1 ≤ R ^ j := Nat.one_le_pow _ _ hR1
    calc branchBCapUL stepCap u (j + 1)
        ≤ R * (S + (R ^ j * u + j * R ^ j * S)) :=
          hstep.trans (Nat.mul_le_mul_left R (Nat.add_le_add_left ih S))
      _ = R ^ (j + 1) * u + (R * S + j * R ^ (j + 1) * S) := by rw [pow_succ']; ring
      _ ≤ R ^ (j + 1) * u + (R ^ (j + 1) * S + j * R ^ (j + 1) * S) := by
          have h1 : R ≤ R ^ (j + 1) := by
            rw [pow_succ']; exact Nat.le_mul_of_pos_right R hpow
          have h2 := Nat.mul_le_mul_right S h1
          omega
      _ = R ^ (j + 1) * u + (j + 1) * R ^ (j + 1) * S := by ring

private lemma branchBCapEW_le_of_bounds {edMul : ℕ} {cfg : Alg2Config} {stepCap : ℕ → ℕ → ℕ}
    {Umax Wmax B₀ u n : ℕ}
    (hUL : ∀ j < n, branchBCapUL stepCap u (j + 1) ≤ Umax)
    (hBW : ∀ j < n, branchBCapBW stepCap u j ≤ Wmax)
    (hB : ∀ j < n, SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀ ≤ B₀) :
    ∀ j ≤ n, branchBCapEW edMul cfg stepCap u j ≤
      (edMul * B₀ + 1) ^ j * (10 * u + 1) +
        j * (edMul * B₀ + 1) ^ j * (edMul * (Umax + (Wmax + 1) * B₀))
  | 0, _ => by simp [branchBCapEW]
  | j + 1, hj => by
    set Q := edMul * B₀ + 1
    have hQ1 : 1 ≤ Q := by dsimp only [Q]; omega
    have ih := branchBCapEW_le_of_bounds (edMul := edMul) hUL hBW hB j (Nat.le_of_succ_le hj)
    have h1 : branchBCapEW edMul cfg stepCap u (j + 1) ≤
        edMul * (Umax + (Wmax + branchBCapEW edMul cfg stepCap u j + 1) * B₀) := by
      simp only [branchBCapEW]
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add (hUL j hj)
        (Nat.mul_le_mul (by have := hBW j hj; omega) (hB j hj))
    have h2 : edMul * (Umax + (Wmax + branchBCapEW edMul cfg stepCap u j + 1) * B₀) =
        edMul * B₀ * branchBCapEW edMul cfg stepCap u j +
          edMul * (Umax + (Wmax + 1) * B₀) := by ring
    have h3 : edMul * B₀ * branchBCapEW edMul cfg stepCap u j ≤
        Q * (Q ^ j * (10 * u + 1) + j * Q ^ j * (edMul * (Umax + (Wmax + 1) * B₀))) :=
      Nat.mul_le_mul (by dsimp only [Q]; omega) ih
    have h4 : edMul * (Umax + (Wmax + 1) * B₀) ≤
        Q ^ (j + 1) * (edMul * (Umax + (Wmax + 1) * B₀)) :=
      Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hQ1)
    have h5 : Q * (Q ^ j * (10 * u + 1) + j * Q ^ j * (edMul * (Umax + (Wmax + 1) * B₀))) +
        Q ^ (j + 1) * (edMul * (Umax + (Wmax + 1) * B₀)) =
        Q ^ (j + 1) * (10 * u + 1) + (j + 1) * Q ^ (j + 1) * (edMul * (Umax + (Wmax + 1) * B₀)) := by
      rw [pow_succ']; ring
    linarith only [h1, h2, h3, h4, h5]

/-- `dryStepCapS J j` is uniformly bounded by a `PolyNat` function of `I.m` for all `j ≤ cfg.P.d`. -/
theorem dryStepCapS_le_poly :
    ∃ fS : ℕ → ℕ, PolyNat fS ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        ∀ j ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.d,
          dryStepCapS J j ≤ fS (solverConnectedAugmented J).m := by
  obtain ⟨fk, hfkSub, hfk⟩ := dryCfgK_le_subpoly
  obtain ⟨fLM, hfLMSub, hfLM⟩ := dryLevelM_le_subpoly
  obtain ⟨fG, hfGSub, hfG⟩ := dryGammaRPow_le_subpoly 0 1
  have hfkP : PolyNat fk := SubpolyNat.toPolyNat hfkSub
  have hfGP : PolyNat fG := SubpolyNat.toPolyNat hfGSub
  let fM : ℕ → ℕ := fun M => (M + 1) * fLM M
  have hfMP : PolyNat fM :=
    PolyNat.mul (PolyNat.add_const PolyNat.id 1) (SubpolyNat.toPolyNat hfLMSub)
  let fB : ℕ → ℕ := fun M => (fM M + 4 * dryM0OfM M + 3) ^ 2
  have hfBP : PolyNat fB :=
    PolyNat.pow (PolyNat.add_const (PolyNat.add hfMP (PolyNat.const_mul dryM0OfM_poly 4)) 3) 2
  let fL : ℕ → ℕ := fun M => 4 * dryM0OfM M + 1
  have hfLP : PolyNat fL := PolyNat.add_const (PolyNat.const_mul dryM0OfM_poly 4) 1
  let c_sp := dryWitnessUsed.spanConst
  let fS : ℕ → ℕ := fun M =>
    3 * (fk M + 1) * fM M + (5 + 24 * fB M) * fM M +
      1080 * c_sp * (fG M) ^ 2 * (fk M + 1) ^ 2 * (115 * fM M + 4) * fM M +
      c_sp * (4 * fG M * (115 * fM M + 4) ^ 2 + (fL M + 6) * (115 * fM M + 4)) * fM M
  have hfSP : PolyNat fS := by
    have h115 : PolyNat (fun M => 115 * fM M + 4) :=
      PolyNat.add_const (PolyNat.const_mul hfMP 115) 4
    have h1 := PolyNat.mul (PolyNat.const_mul (PolyNat.add_const hfkP 1) 3) hfMP
    have h2 := PolyNat.mul (PolyNat.add_const (PolyNat.const_mul hfBP 24) 5) hfMP
    have h3 := PolyNat.mul
      (PolyNat.mul
        (PolyNat.mul
          (PolyNat.const_mul (PolyNat.pow hfGP 2) (1080 * c_sp))
          (PolyNat.pow (PolyNat.add_const hfkP 1) 2))
        h115)
      hfMP
    have h4 := PolyNat.mul
      (PolyNat.const_mul
        (PolyNat.add
          (PolyNat.mul (PolyNat.const_mul hfGP 4) (PolyNat.pow h115 2))
          (PolyNat.mul (PolyNat.add_const hfLP 6) h115))
        c_sp)
      hfMP
    exact PolyNat.mono (fun M => by dsimp only [fS]; rw [show (5 + 24 * fB M) * fM M = (24 * fB M + 5) * fM M by ring])
      (PolyNat.add (PolyNat.add (PolyNat.add h1 h2) h3) h4)
  refine ⟨fS, hfSP, fun J hJn hJm hCap j hj => ?_⟩
  set I := solverConnectedAugmented J
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hkLe : cfg.P.k ≤ fk I.m := hfk J hJn hJm hCap
  have hMLe : levelM cfg.TP cfg.P j ≤ fM I.m := hfLM J hJn hJm hCap j hj
  have hGLe : ⌈cfg.TP.γ_r (cfg.P.M₀ ^ 2)⌉₊ ≤ fG I.m := by
    simpa using hfG J hJn hJm hCap
  have hN0Eq : cfg.N₀ = 4 * dryM0OfM I.m := rfl
  have hBLe : SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀ ≤ fB I.m := by
    unfold SparseCore.bundleLogFactor; dsimp only [fB]
    have hlg := Nat.log_le_self 2 (levelM cfg.TP cfg.P j + cfg.N₀ + 2)
    rw [hN0Eq] at hlg ⊢
    exact Nat.pow_le_pow_left (by omega) 2
  have hLLe : Expander.chosenL (cfg.P.M₀ ^ 2) ≤ fL I.m := by
    have hM1 : 1 ≤ cfg.P.M₀ := cfg.P.hM₀
    exact chosenL_sq_le_four_mul_add_one hM1
  have h115Le : 115 * levelM cfg.TP cfg.P j + 4 ≤ 115 * fM I.m + 4 := by omega
  have ht1 : 3 * (cfg.P.k + 1) * levelM cfg.TP cfg.P j ≤ 3 * (fk I.m + 1) * fM I.m :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 3 (by omega)) hMLe
  have ht2 : (5 + 24 * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀) *
      levelM cfg.TP cfg.P j ≤ (5 + 24 * fB I.m) * fM I.m :=
    Nat.mul_le_mul (by omega) hMLe
  have ht3 : 1080 * c_sp * ⌈cfg.TP.γ_r (cfg.P.M₀ ^ 2)⌉₊ ^ 2 * (cfg.P.k + 1) ^ 2 *
      (115 * levelM cfg.TP cfg.P j + 4) * levelM cfg.TP cfg.P j ≤
      1080 * c_sp * (fG I.m) ^ 2 * (fk I.m + 1) ^ 2 * (115 * fM I.m + 4) * fM I.m :=
    Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul_left (1080 * c_sp) (Nat.pow_le_pow_left hGLe 2))
          (Nat.pow_le_pow_left (by omega) 2))
        h115Le)
      hMLe
  have ht4 : c_sp * (4 * ⌈cfg.TP.γ_r (cfg.P.M₀ ^ 2)⌉₊ * (115 * levelM cfg.TP cfg.P j + 4) ^ 2 +
      (Expander.chosenL (cfg.P.M₀ ^ 2) + 6) * (115 * levelM cfg.TP cfg.P j + 4)) *
      levelM cfg.TP cfg.P j ≤
      c_sp * (4 * fG I.m * (115 * fM I.m + 4) ^ 2 + (fL I.m + 6) * (115 * fM I.m + 4)) * fM I.m :=
    Nat.mul_le_mul
      (Nat.mul_le_mul_left c_sp
        (Nat.add_le_add
          (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hGLe) (Nat.pow_le_pow_left h115Le 2))
          (Nat.mul_le_mul (by omega) h115Le)))
      hMLe
  unfold dryStepCapS
  dsimp only [fS, c_sp, I, cfg] at ht1 ht2 ht3 ht4 ⊢
  linarith only [ht1, ht2, ht3, ht4]

/-- Uniform `PolyNat` bounds on the chained Branch-B caps `branchBCapUL`, `branchBCapBW`, and
`branchBCapEW` at `dryInnerCoreStepCap J` and `u = 2 * I.m`, for all `j ≤ cfg.P.d`. -/
theorem dryBranchBCaps_le_poly (Psc : DrySparseCorePieces) :
    let edMul := drySCEdMul Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
    ∃ fUL fBW fEW : ℕ → ℕ, PolyNat fUL ∧ PolyNat fBW ∧ PolyNat fEW ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let I := solverConnectedAugmented J
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        ∀ j ≤ cfg.P.d,
          branchBCapUL (dryInnerCoreStepCap J) (2 * I.m) j ≤ fUL I.m ∧
          branchBCapBW (dryInnerCoreStepCap J) (2 * I.m) j ≤ fBW I.m ∧
          branchBCapEW edMul cfg (dryInnerCoreStepCap J) (2 * I.m) j ≤ fEW I.m := by
  intro edMul
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  obtain ⟨fLM, hfLMSub, hfLM⟩ := dryLevelM_le_subpoly
  obtain ⟨f122, hf122Sub, hf122⟩ := dryConstPowD_le_subpoly 122
  obtain ⟨fKd, hfKdP, hfKd⟩ := dryCfgKPowD_le_poly
  obtain ⟨fRd, hfRdSub, hfRd⟩ := dryUpdateCoreStepRatioPow_le_subpoly Psc
  obtain ⟨fS, hfSP, hfS⟩ := dryStepCapS_le_poly
  have hfdP : PolyNat fd := SubpolyNat.toPolyNat hfdSub
  have hf122P : PolyNat f122 := SubpolyNat.toPolyNat hf122Sub
  have hfRdP : PolyNat fRd := SubpolyNat.toPolyNat hfRdSub
  let fM : ℕ → ℕ := fun M => (M + 1) * fLM M
  have hfMP : PolyNat fM :=
    PolyNat.mul (PolyNat.add_const PolyNat.id 1) (SubpolyNat.toPolyNat hfLMSub)
  let fB : ℕ → ℕ := fun M => (fM M + 4 * dryM0OfM M + 3) ^ 2
  have hfBP : PolyNat fB :=
    PolyNat.pow (PolyNat.add_const (PolyNat.add hfMP (PolyNat.const_mul dryM0OfM_poly 4)) 3) 2
  let fRPow : ℕ → ℕ := fun M => f122 M * fKd M * (fRd M) ^ 2
  have hfRPowP : PolyNat fRPow :=
    PolyNat.mul (PolyNat.mul hf122P hfKdP) (PolyNat.pow hfRdP 2)
  let fUL : ℕ → ℕ := fun M => fRPow M * (2 * M) + fd M * fRPow M * fS M
  have hfULP : PolyNat fUL :=
    PolyNat.add (PolyNat.mul hfRPowP (PolyNat.const_mul PolyNat.id 2))
      (PolyNat.mul (PolyNat.mul hfdP hfRPowP) hfSP)
  let fBW : ℕ → ℕ := fun M => 5 * fUL M + 8 * M + 1
  have hfBWP : PolyNat fBW :=
    PolyNat.add_const (PolyNat.add (PolyNat.const_mul hfULP 5) (PolyNat.const_mul PolyNat.id 8)) 1
  let fEW : ℕ → ℕ := fun M =>
    fRd M * (20 * M + 1) + fd M * fRd M * (edMul * (fUL M + (fBW M + 1) * fB M))
  have hfEWP : PolyNat fEW :=
    PolyNat.add
      (PolyNat.mul hfRdP (PolyNat.add_const (PolyNat.const_mul PolyNat.id 20) 1))
      (PolyNat.mul (PolyNat.mul hfdP hfRdP)
        (PolyNat.const_mul (PolyNat.add hfULP (PolyNat.mul (PolyNat.add_const hfBWP 1) hfBP))
          edMul))
  refine ⟨fUL, fBW, fEW, hfULP, hfBWP, hfEWP, fun J hJn hJm hCap => ?_⟩
  intro I cfg
  set B₀ := SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀
  set Rmax := 122 * cfg.P.k * B₀ ^ 2
  have hB0_pos : 1 ≤ B₀ := by
    unfold B₀ SparseCore.bundleLogFactor
    exact Nat.one_le_pow 2 _ (by omega)
  have hRmax1 : 1 ≤ Rmax := by
    have hk1 : 1 ≤ cfg.P.k := cfg.P.hk
    have hB2 : 1 ≤ B₀ ^ 2 := Nat.one_le_pow 2 _ hB0_pos
    dsimp only [Rmax]; nlinarith
  have hBLe0 : ∀ j, SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀ ≤ B₀ := fun j => by
    unfold B₀ SparseCore.bundleLogFactor
    have hM : levelM cfg.TP cfg.P j ≤ levelM cfg.TP cfg.P 0 := dryLevelM_le_zero J hJn hJm hCap j
    exact Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1) 2
  have hCapLe : ∀ j < cfg.P.d, ∀ b, dryInnerCoreStepCap J j b ≤ Rmax * (fS I.m + b) := fun j hj b => by
    have hBj : SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀ ≤ B₀ := hBLe0 j
    have hR : dryStepCapR J j ≤ Rmax := by
      unfold dryStepCapR; dsimp only [Rmax]
      have h1 : SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀ *
          (10 + 112 * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀) ≤
          122 * B₀ ^ 2 := by nlinarith
      calc cfg.P.k * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀ *
            (10 + 112 * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀)
          = cfg.P.k * (SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀ *
              (10 + 112 * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀)) := by ring
        _ ≤ cfg.P.k * (122 * B₀ ^ 2) := Nat.mul_le_mul_left _ h1
        _ = 122 * cfg.P.k * B₀ ^ 2 := by ring
    exact Nat.mul_le_mul hR (Nat.add_le_add_right (hfS J hJn hJm hCap j hj.le) b)
  have hB0_le_rat : B₀ ≤ updateCoreStepRatio edMul (levelM cfg.TP cfg.P 0) cfg.N₀ := by
    unfold updateCoreStepRatio; dsimp only [B₀]; nlinarith
  have hRmaxPow : Rmax ^ cfg.P.d ≤ fRPow I.m := by
    have hsplit : Rmax ^ cfg.P.d = 122 ^ cfg.P.d * cfg.P.k ^ cfg.P.d * (B₀ ^ cfg.P.d) ^ 2 := by
      dsimp only [Rmax]; ring
    rw [hsplit]
    have h1 := hf122 J hJn hJm hCap
    have h2 := hfKd J hJn hJm hCap
    have h3 : B₀ ^ cfg.P.d ≤ fRd I.m :=
      (Nat.pow_le_pow_left hB0_le_rat cfg.P.d).trans (hfRd J hJn hJm hCap)
    exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (Nat.pow_le_pow_left h3 2)
  have hd : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
  have hUL : ∀ j ≤ cfg.P.d, branchBCapUL (dryInnerCoreStepCap J) (2 * I.m) j ≤ fUL I.m := fun j hj => by
    have h1 := branchBCapUL_le_of_affine (u := 2 * I.m) hRmax1 hCapLe j hj
    have hPowJ : Rmax ^ j ≤ fRPow I.m := (Nat.pow_le_pow_right hRmax1 hj).trans hRmaxPow
    have h2 := Nat.mul_le_mul_right (2 * I.m) hPowJ
    have h3 := Nat.mul_le_mul_right (fS I.m) (Nat.mul_le_mul (hj.trans hd) hPowJ)
    dsimp only [fUL]
    linarith only [h1, h2, h3]
  have hBW : ∀ j ≤ cfg.P.d, branchBCapBW (dryInnerCoreStepCap J) (2 * I.m) j ≤ fBW I.m := fun j hj => by
    cases j with
    | zero => simp only [branchBCapBW, fBW]; omega
    | succ j' =>
      simp only [branchBCapBW, fBW]
      have h := hUL (j' + 1) hj
      omega
  have hB0_le_fB : B₀ ≤ fB I.m := by
    unfold B₀ SparseCore.bundleLogFactor; dsimp only [fB, fM]
    have hM0 : levelM cfg.TP cfg.P 0 ≤ (I.m + 1) * fLM I.m := hfLM J hJn hJm hCap 0 (Nat.zero_le _)
    have hlg := Nat.log_le_self 2 (levelM cfg.TP cfg.P 0 + cfg.N₀ + 2)
    have hN0Eq : cfg.N₀ = 4 * dryM0OfM I.m := rfl
    rw [hN0Eq] at hlg ⊢
    exact Nat.pow_le_pow_left (by omega) 2
  have hQ_le_rat : edMul * B₀ + 1 ≤ updateCoreStepRatio edMul (levelM cfg.TP cfg.P 0) cfg.N₀ := by
    unfold updateCoreStepRatio
    have hmul : edMul * B₀ ≤ (edMul + 6) * B₀ := Nat.mul_le_mul_right B₀ (by omega)
    dsimp only [B₀] at hmul ⊢
    omega
  have hQPow : (edMul * B₀ + 1) ^ cfg.P.d ≤ fRd I.m :=
    (Nat.pow_le_pow_left hQ_le_rat cfg.P.d).trans (hfRd J hJn hJm hCap)
  have hEW : ∀ j ≤ cfg.P.d,
      branchBCapEW edMul cfg (dryInnerCoreStepCap J) (2 * I.m) j ≤ fEW I.m := fun j hj => by
    have h1 := branchBCapEW_le_of_bounds (edMul := edMul) (cfg := cfg)
      (stepCap := dryInnerCoreStepCap J) (Umax := fUL I.m) (Wmax := fBW I.m) (B₀ := B₀)
      (u := 2 * I.m) (n := cfg.P.d)
      (fun r hr => hUL (r + 1) hr) (fun r hr => hBW r hr.le) (fun r _ => hBLe0 r) j hj
    have hQ1 : 1 ≤ edMul * B₀ + 1 := by omega
    have hPowJ : (edMul * B₀ + 1) ^ j ≤ fRd I.m := (Nat.pow_le_pow_right hQ1 hj).trans hQPow
    have h2 : (edMul * B₀ + 1) ^ j * (10 * (2 * I.m) + 1) ≤ fRd I.m * (20 * I.m + 1) := by
      have : 10 * (2 * I.m) + 1 = 20 * I.m + 1 := by omega
      rw [this]; exact Nat.mul_le_mul_right _ hPowJ
    have h3 : j * (edMul * B₀ + 1) ^ j * (edMul * (fUL I.m + (fBW I.m + 1) * B₀)) ≤
        fd I.m * fRd I.m * (edMul * (fUL I.m + (fBW I.m + 1) * fB I.m)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (hj.trans hd) hPowJ)
        (Nat.mul_le_mul_left edMul (Nat.add_le_add_left (Nat.mul_le_mul_left _ hB0_le_fB) _))
    dsimp only [fEW]
    linarith only [h1, h2, h3]
  exact fun j hj => ⟨hUL j hj, hBW j hj, hEW j hj⟩

end MinCostFlow.Final.DryRun

end
