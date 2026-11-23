module

public import MinCostFlow.Final.ForestConcretePrograms
public import MinCostFlow.Final.TimeFactorBounds
import MinCostFlow.Final.RuntimeQualityBounds
import MinCostFlow.IPM.Machine.ConnectedSolverCost
import MinCostFlow.IPM.Machine.TargetTestCost
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Subpolynomial rate bound for the concrete solver with dynamic LCT forest

Absorbs `cappedQualityExponent`, the subpolynomial min-ratio cycle rate, and
`lctForestRate L (n + 1) = 1000000 * (L + 1) * (Nat.log 2 (n + 3) + 1)` into a
single Theorem 5.1 subpolynomial envelope over the original edge count `m`.
-/

@[expose] public noncomputable section
namespace MinCostFlow.Final
open Chain IPM IPM.Machine LinkCut.Prog

def ForestConcreteProgramCore.rateScale (P : ForestConcreteProgramCore) : ℝ :=
  (7 * P.timeConstant + 2 : ℕ)

private theorem ForestConcreteProgramCore.rateScale_ge_two (P : ForestConcreteProgramCore) :
    2 ≤ P.rateScale := by
  unfold ForestConcreteProgramCore.rateScale
  exact_mod_cast (by omega : 2 ≤ 7 * P.timeConstant + 2)

private theorem ForestConcreteProgramCore.rateScale_ge_one (P : ForestConcreteProgramCore) :
    1 ≤ P.rateScale :=
  (by norm_num : (1 : ℝ) ≤ 2).trans P.rateScale_ge_two

def ForestConcreteProgramCore.cycleRescaledExponent (P : ForestConcreteProgramCore) : ℝ :=
  let a := logScale P.rateScale
  P.cycleRateExponent * a ^ (47 / 48 : ℝ) * logScale a

def ForestConcreteProgramCore.qualityRescaledExponent (P : ForestConcreteProgramCore) : ℝ :=
  let s : ℝ := ((P.edgeThreshold + 1 : ℕ) : ℝ) * P.rateScale
  let b := logScale s
  (65536 * ((P.qualityBudget : ℝ) + 1)) * b ^ (47 / 48 : ℝ) * logScale b

def ForestConcreteProgramCore.rateExponent (P : ForestConcreteProgramCore) : ℝ :=
  max P.cycleRescaledExponent
    (max P.qualityRescaledExponent (1 / (Real.log 2) ^ (47 / 48 : ℝ)))

theorem ForestConcreteProgramCore.rateExponent_nonneg (P : ForestConcreteProgramCore) :
    0 ≤ P.rateExponent := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < (Real.log 2) ^ (47 / 48 : ℝ) := Real.rpow_pos_of_pos hlog _
  have h1 : 0 ≤ 1 / (Real.log 2) ^ (47 / 48 : ℝ) := by positivity
  exact h1.trans ((le_max_right _ _).trans (le_max_right _ _))

def ForestConcreteProgramCore.rateCoefficient (P : ForestConcreteProgramCore) : ℝ :=
  1 + 435 * logScale P.rateScale + P.cycleRateConstant

theorem ForestConcreteProgramCore.rateCoefficient_ge_one (P : ForestConcreteProgramCore) :
    1 ≤ P.rateCoefficient := by
  unfold ForestConcreteProgramCore.rateCoefficient
  have hc := P.cycleRateConstant_pos.le
  have hs := logScale_one_le P.rateScale_ge_one
  linarith

private theorem nat_log_succ_le (n : ℕ) (H : ℝ) (hlog : Real.log ((n : ℝ) + 3) ≤ H) (hH : 1 ≤ H) :
    ((Nat.log 2 (n + 3) : ℕ) : ℝ) + 1 ≤ 3 * H := by
  have hp : (2 : ℝ) ^ Nat.log 2 (n + 3) ≤ (n : ℝ) + 3 := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n + 3 ≠ 0)
  have hl := Real.log_le_log (by positivity) hp
  rw [Real.log_pow] at hl
  have hHalf : (1 / 2 : ℝ) ≤ Real.log 2 := Real.log_two_gt_d9.le.trans' (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hHalf (Nat.cast_nonneg (Nat.log 2 (n + 3)))
  linarith only [hl, hmul, hlog, hH]

private theorem forestConcreteRateEnvelope (P : ForestConcreteProgramCore) (m n j : ℕ)
    (hn : n ≤ P.timeConstant * m) (hj : j ≤ P.timeConstant * m) :
    let H := P.rateCoefficient * alg2TimeFactor P.rateExponent (47 / 48) m
    1 ≤ H ∧
    435 * Real.log ((j : ℝ) + 2) ≤ H ∧
    ((Nat.log 2 (n + 3) : ℕ) : ℝ) + 1 ≤ 3 * H ∧
    (∀ M ≤ 7 * j, (P.cycleRate M : ℝ) ≤ H) ∧
    (∀ M ≤ 7 * j, (2 : ℝ) ^ P.runtimeResources.qualityExponent M ≤ H) := by
  dsimp only
  let W := alg2TimeFactor P.rateExponent (47 / 48) m
  let H := P.rateCoefficient * W
  have hCoeff : 1 ≤ P.rateCoefficient := P.rateCoefficient_ge_one
  have hW : 1 ≤ W := scalingTimeFactor_one_le P.rateExponent_nonneg m
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hCoeff hW
  have ha : 1 ≤ logScale P.rateScale := logScale_one_le P.rateScale_ge_one
  have hx2 : (2 : ℝ) ≤ (m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hj_le : (j : ℝ) + 2 ≤ P.rateScale * ((m : ℝ) + 2) := by
    unfold ForestConcreteProgramCore.rateScale
    have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hK_nn : (0 : ℝ) ≤ P.timeConstant := Nat.cast_nonneg _
    have hj' : (j : ℝ) ≤ (P.timeConstant : ℝ) * m := by exact_mod_cast hj
    push_cast
    nlinarith
  have hjlog := log_le_scaled P.rateScale_ge_one hx2 (by positivity) hj_le
  have hmlog_W : Real.log ((m : ℝ) + 2) ≤ W := by
    have hlog_le : Real.log ((m : ℝ) + 2) ≤ (Real.log ((m : ℝ) + 2) + 2) ^ 1 := by
      rw [pow_one]; linarith
    have hp := hlog_le.trans (paddedLog_pow_le_timeFactor 1 m)
    rw [Nat.cast_one] at hp
    have hm : alg2TimeFactor ((1 : ℝ) / (Real.log 2) ^ (47 / 48 : ℝ)) (47 / 48) m ≤ W :=
      scalingTimeFactor_mono ((le_max_right _ _).trans (le_max_right _ _)) m
    exact hp.trans hm
  have hc435 : 435 * logScale P.rateScale ≤ P.rateCoefficient := by
    unfold ForestConcreteProgramCore.rateCoefficient
    linarith [P.cycleRateConstant_pos.le]
  have hW0 : 0 ≤ W := by linarith
  have hB : 435 * Real.log ((j : ℝ) + 2) ≤ H := by
    calc 435 * Real.log ((j : ℝ) + 2)
        ≤ 435 * (logScale P.rateScale * Real.log ((m : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hjlog (by norm_num)
      _ ≤ (435 * logScale P.rateScale) * W := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmlog_W (by linarith)) (by norm_num)
      _ ≤ H := mul_le_mul_of_nonneg_right hc435 hW0
  have hLg : ((Nat.log 2 (n + 3) : ℕ) : ℝ) + 1 ≤ 3 * H := by
    have hn_le : (n : ℝ) + 3 ≤ P.rateScale * ((m : ℝ) + 2) := by
      unfold ForestConcreteProgramCore.rateScale
      have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hK_nn : (0 : ℝ) ≤ P.timeConstant := Nat.cast_nonneg _
      have hn' : (n : ℝ) ≤ (P.timeConstant : ℝ) * m := by exact_mod_cast hn
      push_cast
      nlinarith
    have hnlog := log_le_scaled P.rateScale_ge_one hx2 (by positivity) hn_le
    have h1 : logScale P.rateScale ≤ P.rateCoefficient := by
      have : 0 ≤ logScale P.rateScale := by linarith
      linarith [hc435]
    have hlogH : Real.log ((n : ℝ) + 3) ≤ H :=
      hnlog.trans (mul_le_mul h1 hmlog_W (Real.log_nonneg (by linarith)) (by linarith))
    exact nat_log_succ_le n H hlogH hH
  have hCyc : ∀ M ≤ 7 * j, (P.cycleRate M : ℝ) ≤ H := by
    intro M hMj
    have hM_le : (M : ℝ) + 2 ≤ P.rateScale * ((m : ℝ) + 2) := by
      unfold ForestConcreteProgramCore.rateScale
      have hM' : (M : ℝ) ≤ 7 * ((P.timeConstant : ℝ) * m) := by exact_mod_cast hMj.trans (Nat.mul_le_mul_left 7 hj)
      have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hK_nn : (0 : ℝ) ≤ P.timeConstant := Nat.cast_nonneg _
      push_cast
      nlinarith
    have hresc := scalingTimeFactor_rescale P.rateScale_ge_one P.cycleRateExponent_nonneg m M hM_le
    have hmono : alg2TimeFactor P.cycleRescaledExponent (47 / 48) m ≤ W :=
      scalingTimeFactor_mono (le_max_left _ _) m
    have hcr := (P.cycleRate_subpoly M).trans
      (mul_le_mul_of_nonneg_left (hresc.trans hmono) P.cycleRateConstant_pos.le)
    have hcC : P.cycleRateConstant ≤ P.rateCoefficient := by
      unfold ForestConcreteProgramCore.rateCoefficient
      linarith
    exact hcr.trans (mul_le_mul_of_nonneg_right hcC hW0)
  have hQual : ∀ M ≤ 7 * j, (2 : ℝ) ^ P.runtimeResources.qualityExponent M ≤ H := by
    intro M hMj
    let cap := max M P.edgeThreshold
    have hcap_le : (cap : ℝ) + 2 ≤ ((P.edgeThreshold + 1 : ℕ) : ℝ) * P.rateScale * ((m : ℝ) + 2) := by
      have hM_le : (M : ℝ) + 2 ≤ P.rateScale * ((m : ℝ) + 2) := by
        unfold ForestConcreteProgramCore.rateScale
        have hM' : (M : ℝ) ≤ 7 * ((P.timeConstant : ℝ) * m) := by exact_mod_cast hMj.trans (Nat.mul_le_mul_left 7 hj)
        have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have hK_nn : (0 : ℝ) ≤ P.timeConstant := Nat.cast_nonneg _
        push_cast
        nlinarith
      have hc1 : cap + 2 ≤ (P.edgeThreshold + 1) * (M + 2) := by
        dsimp [cap]
        have : P.edgeThreshold + 2 ≤ (P.edgeThreshold + 1) * (M + 2) := by nlinarith
        have : M + 2 ≤ (P.edgeThreshold + 1) * (M + 2) := by nlinarith
        omega
      have hc1R : (cap : ℝ) + 2 ≤ ((P.edgeThreshold + 1 : ℕ) : ℝ) * ((M : ℝ) + 2) := by exact_mod_cast hc1
      have ht_nn : (0 : ℝ) ≤ ((P.edgeThreshold + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      calc (cap : ℝ) + 2 ≤ ((P.edgeThreshold + 1 : ℕ) : ℝ) * ((M : ℝ) + 2) := hc1R
        _ ≤ ((P.edgeThreshold + 1 : ℕ) : ℝ) * (P.rateScale * ((m : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_left hM_le ht_nn
        _ = _ := by ring
    have hs1 : 1 ≤ ((P.edgeThreshold + 1 : ℕ) : ℝ) * P.rateScale := by
      have ht : (1 : ℝ) ≤ ((P.edgeThreshold + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ P.edgeThreshold + 1)
      exact one_le_mul_of_one_le_of_one_le ht P.rateScale_ge_one
    have hq0 : 0 ≤ 65536 * ((P.qualityBudget : ℝ) + 1) := by positivity
    have hbd := (integerQualityExponent_bounds P.qualityBudget cap).2
    have hresc := scalingTimeFactor_rescale hs1 hq0 m cap hcap_le
    have hmono : alg2TimeFactor P.qualityRescaledExponent (47 / 48) m ≤ W :=
      scalingTimeFactor_mono ((le_max_left _ _).trans (le_max_right _ _)) m
    have hq_le : (2 : ℝ) ^ P.runtimeResources.qualityExponent M ≤ W := by
      change (2 : ℝ) ^ cappedQualityExponent P.edgeThreshold P.qualityBudget M ≤ W
      exact hbd.trans (hresc.trans hmono)
    exact hq_le.trans (le_mul_of_one_le_left hW0 hCoeff)
  exact ⟨hH, hB, hLg, hCyc, hQual⟩

private def forestCostPolynomial (n m M b W epochs forest cycle quality : ℝ) : ℝ :=
  1000 * n + 100000 * m * (W + 3 * b + 3) + forest * (n + 2 + 70 * m) +
    (2 + 2 * b) * (epochs * (M * (100000000 * W ^ 3) + (30 * M + 1) * cycle) + 100 * W + 419) +
    50 + 2 * quality

private theorem forestCostPolynomial_mono
    {n m M b W d f c k n' m' M' b' W' d' f' c' k' : ℝ}
    (hn : 0 ≤ n) (hm : 0 ≤ m) (hM : 0 ≤ M) (hb : 0 ≤ b) (hW : 0 ≤ W)
    (hd : 0 ≤ d) (hf : 0 ≤ f) (hc : 0 ≤ c) (_hk : 0 ≤ k)
    (hn' : n ≤ n') (hm' : m ≤ m') (hM' : M ≤ M') (hb' : b ≤ b') (hW' : W ≤ W')
    (hd' : d ≤ d') (hf' : f ≤ f') (hc' : c ≤ c') (hk' : k ≤ k') :
    forestCostPolynomial n m M b W d f c k ≤ forestCostPolynomial n' m' M' b' W' d' f' c' k' := by
  have hm₀ := hm.trans hm'
  have hf₀ := hf.trans hf'
  have hb₀ := hb.trans hb'
  have hd₀ := hd.trans hd'
  have hM₀ := hM.trans hM'
  unfold forestCostPolynomial
  gcongr

private theorem forestCostPolynomial_bound {x H : ℝ} (hx : 1 ≤ x) (hH : 1 ≤ H) :
    forestCostPolynomial x x x H (30000116 * H ^ 2) (3276800000000001 * H ^ 5)
      (10 ^ 15 * H ^ 3) H (200 * x) ≤ 10 ^ 50 * x * H ^ 12 := by
  have hx0 : 0 ≤ x := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hp (a : ℕ) (ha : a ≤ 12) : x * H ^ a ≤ x * H ^ 12 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH ha) hx0
  have hp0 := hp 0 (by decide)
  have hp1 := hp 1 (by decide)
  have hp2 := hp 2 (by decide)
  have hp3 := hp 3 (by decide)
  have hp6 := hp 6 (by decide)
  have hp7 := hp 7 (by decide)
  have hp11 := hp 11 (by decide)
  have hpure (a : ℕ) (ha : a ≤ 12) : H ^ a ≤ x * H ^ 12 :=
    (pow_le_pow_right₀ hH ha).trans (le_mul_of_one_le_left (pow_nonneg hH0 _) hx)
  have hpure0 := hpure 0 (by decide)
  have hpure1 := hpure 1 (by decide)
  have hpure2 := hpure 2 (by decide)
  have hpure3 := hpure 3 (by decide)
  have hpure6 := hpure 6 (by decide)
  have hpure7 := hpure 7 (by decide)
  unfold forestCostPolynomial
  nlinarith only [hp0, hp1, hp2, hp3, hp6, hp7, hp11,
    hpure0, hpure1, hpure2, hpure3, hpure6, hpure7, mul_nonneg hx0 (pow_nonneg hH0 12)]

private theorem forestSolver_bound_positive (P : ForestConcreteProgramCore) (n m : ℕ)
    (hm : 0 < m) (x H : ℝ) (hx : 1 ≤ x) (hH : 1 ≤ H)
    (hn : (n : ℝ) ≤ x) (he : (m : ℝ) ≤ x) (hAug : ∀ M ∈ Finset.Icc m (7 * m), (M : ℝ) ≤ x)
    (hB : 435 * Real.log ((m : ℝ) + 2) ≤ H)
    (hLg : ((Nat.log 2 (n + 3) : ℕ) : ℝ) + 1 ≤ 3 * H)
    (hR : ∀ M ∈ Finset.Icc m (7 * m), (P.cycleRate M : ℝ) ≤ H)
    (hK : ∀ M ∈ Finset.Icc m (7 * m), (2 : ℝ) ^ P.runtimeResources.qualityExponent M ≤ H)
    (hC : ∀ M ∈ Finset.Icc m (7 * m), (P.runtimeResources.qualityCost M : ℝ) ≤ 200 * x) :
    (forestConnectedSolverRuntimeTime P.runtimeResources n m : ℝ) ≤ 10 ^ 50 * x * H ^ 12 := by
  let r := P.runtimeResources
  obtain ⟨M, hMem, hCost⟩ := forestConnectedSolverRuntimeTime_width_bound r n m hm
  obtain ⟨hSmall, hLarge⟩ := Finset.mem_Icc.mp hMem
  obtain ⟨hSize, hBits⟩ := connectedSolverInputBits_log_bound m M hm hSmall hLarge
  let V := solverPenalty m
  let B := M.size + V.size
  let k := r.qualityExponent M
  let W := 30000000 * B ^ 2 + 116 * k
  let L := ipmQualityLimbs M V k
  let D := targetTestLimit M V k
  have hb : (B : ℝ) ≤ H := hBits.trans hB
  have hk : (k : ℝ) ≤ H := by
    have hk' : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
    exact hk'.trans (hK M hMem)
  have hW : (W : ℝ) ≤ 30000116 * H ^ 2 := by
    have hSq := pow_le_pow_left₀ (Nat.cast_nonneg B) hb 2
    have hH2 : H ≤ H ^ 2 := by nlinarith only [hH, sq_nonneg (H - 1)]
    unfold W; push_cast; linarith only [hSq, hk, hH2]
  have hd : (D : ℝ) ≤ 3276800000000001 * H ^ 5 := by
    have hLimit := targetTest_limit_bit_bound M V k hSize
    change (D : ℝ) ≤ 3276800000000001 * (B : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 2 at hLimit
    refine hLimit.trans ?_
    rw [show (5 : ℕ) = 3 + 2 by decide, pow_add, ← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg B) hb 3) (by norm_num))
      (pow_le_pow_left₀ (by positivity) (hK M hMem) 2) (by positivity) (by positivity)
  have hL_le_W : L ≤ W :=
    (ipmQualityLimbs_le M V k).trans
      (Nat.add_le_add_right (target_format_bit_bound M V (hm.trans_le hSmall)).1 _)
  have hF : (r.template.forestRate (n + 1) L : ℝ) ≤ 10 ^ 15 * H ^ 3 := by
    have hL1 : (L : ℝ) + 1 ≤ 30000117 * H ^ 2 := by
      have hH2 : 1 ≤ H ^ 2 := one_le_pow₀ hH
      have hLW : (L : ℝ) ≤ (W : ℝ) := by exact_mod_cast hL_le_W
      linarith
    have hRateEq : r.template.forestRate (n + 1) L =
        1000000 * (L + 1) * (Nat.log 2 (n + 3) + 1) := by
      change lctForestRate L (n + 1) = _
      unfold lctForestRate
      rfl
    rw [hRateEq]
    push_cast
    have hmul : 1000000 * ((L : ℝ) + 1) * ((Nat.log 2 (n + 3) : ℝ) + 1) ≤
        1000000 * (30000117 * H ^ 2) * (3 * H) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hL1 (by norm_num)) hLg (by positivity) (by positivity)
    have hH3 : (0 : ℝ) ≤ H ^ 3 := by positivity
    calc 1000000 * ((L : ℝ) + 1) * ((Nat.log 2 (n + 3) : ℝ) + 1)
        ≤ 1000000 * (30000117 * H ^ 2) * (3 * H) := hmul
      _ = 90000351000000 * H ^ 3 := by ring
      _ ≤ 10 ^ 15 * H ^ 3 := by
          exact mul_le_mul_of_nonneg_right (by norm_num) hH3
  have hCast : (forestConnectedSolverRuntimeTime r n m : ℝ) ≤ forestCostPolynomial n m M B W D
      (r.template.forestRate (n + 1) L) (r.template.cycleRate M) (r.qualityCost M) := by
    unfold forestCostPolynomial
    exact_mod_cast hCost
  refine hCast.trans ((forestCostPolynomial_mono (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hn he (hAug M hMem)
    hb hW hd hF (hR M hMem) (hC M hMem)).trans (forestCostPolynomial_bound hx hH))

private theorem forestSolver_zero (r : SolverForestRuntimeResources) (n : ℕ) :
    let L0 := ipmQualityLimbs 0 (solverPenalty 0) (r.qualityExponent 0)
    forestConnectedSolverRuntimeTime r n 0 ≤
      (forestConnectedSolverTimeAt (r.forSize 0) 0 0 0 + 2 * r.qualityCost 0 + 1000) *
        (n + 2) * (r.template.forestRate (n + 1) L0 + 1) := by
  dsimp only
  let L0 := ipmQualityLimbs 0 (solverPenalty 0) (r.qualityExponent 0)
  have hIcc : Finset.Icc (0 : ℕ) (7 * 0) = {0} := by ext x; simp
  unfold forestConnectedSolverRuntimeTime
  rw [hIcc, Finset.sup_singleton]
  let E := forestConnectedSolverTimeAt (r.forSize 0) 0 0 0 + 2 * r.qualityCost 0
  let f := r.template.forestRate (n + 1) L0
  have hRate : (r.forSize 0).forestRate (n + 1)
      (ipmQualityLimbs 0 (solverPenalty 0) (r.forSize 0).qualityExponent) = f := rfl
  have hBase : forestConnectedSolverTimeAt (r.forSize 0) n 0 0 + 2 * r.qualityCost 0 ≤
      E + 930 * n + f * (n + 2) := by
    simp only [E, forestConnectedSolverTimeAt, roundMachineCost, Nat.zero_mul, Nat.mul_zero,
      Nat.zero_add, Nat.add_zero]
    rw [hRate, show n + 1 + 1 = n + 2 by rfl]
    omega
  have hE : E + 930 * n ≤ (E + 1000) * (n + 2) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    simp only [Nat.mul_comm 930, Nat.mul_comm 1000]
    have hn := Nat.mul_le_mul_left n (show 930 ≤ 1000 by decide)
    omega
  have hF : f * (n + 2) ≤ (E + 1000) * (n + 2) * f := by
    rw [Nat.mul_comm f]
    have h := Nat.mul_le_mul_right ((n + 2) * f) (show 1 ≤ E + 1000 by omega)
    simpa only [Nat.one_mul, ← Nat.mul_assoc] using h
  have hfixed : 30 ≤ (E + 1000) * (n + 2) :=
    (by omega : 30 ≤ E + 1000).trans (Nat.le_mul_of_pos_right _ (by omega))
  change max 30 _ ≤ (E + 1000) * (n + 2) * (f + 1)
  rw [Nat.mul_add, Nat.mul_one]
  exact max_le (hfixed.trans (Nat.le_add_left _ _)) (hBase.trans (by linarith [hE, hF]))

private theorem zero_rate_add_one_le (L0 : ℕ) {n : ℕ} {H : ℝ}
    (hH : 1 ≤ H) (hLg : ((Nat.log 2 (n + 3) : ℕ) : ℝ) + 1 ≤ 3 * H) :
    (lctForestRate L0 (n + 1) : ℝ) + 1 ≤ 3000001 * ((L0 : ℝ) + 1) * H ^ 12 := by
  unfold lctForestRate
  push_cast
  have hH12 : H ≤ H ^ 12 := by
    simpa only [pow_one] using pow_le_pow_right₀ hH (show 1 ≤ 12 by decide)
  have hL0 : (1 : ℝ) ≤ (L0 : ℝ) + 1 := by linarith only [Nat.cast_nonneg (α := ℝ) L0]
  have hmul : 1000000 * ((L0 : ℝ) + 1) * ((Nat.log 2 (n + 3) : ℝ) + 1) ≤
      3000000 * ((L0 : ℝ) + 1) * H := by
    have h1 := mul_le_mul_of_nonneg_left hLg (by positivity : 0 ≤ 1000000 * ((L0 : ℝ) + 1))
    nlinarith only [h1]
  have hmul' : 3000000 * ((L0 : ℝ) + 1) * H ≤ 3000000 * ((L0 : ℝ) + 1) * H ^ 12 :=
    mul_le_mul_of_nonneg_left hH12 (by positivity)
  have h3 : 1 ≤ ((L0 : ℝ) + 1) * H ^ 12 := one_le_mul_of_one_le_of_one_le hL0 (one_le_pow₀ hH)
  linarith only [hmul, hmul', h3]

def ForestConcreteProgramCore.solverRateCoefficient (P : ForestConcreteProgramCore) : ℝ :=
  let r := P.runtimeResources
  let L0 := ipmQualityLimbs 0 (solverPenalty 0) (r.qualityExponent 0)
  (10 ^ 50 + 3000001 * ((L0 : ℝ) + 1) *
    ((forestConnectedSolverTimeAt (r.forSize 0) 0 0 0 : ℝ) + 2 * r.qualityCost 0 + 1000)) *
    P.rateScale * P.rateCoefficient ^ 12

theorem ForestConcreteProgramCore.solverRateCoefficient_pos (P : ForestConcreteProgramCore) :
    0 < P.solverRateCoefficient := by
  have hScale := P.rateScale_ge_one
  have hCoeff := P.rateCoefficient_ge_one
  unfold ForestConcreteProgramCore.solverRateCoefficient
  positivity

private theorem forestRuntimeTime_le (P : ForestConcreteProgramCore) (m n j : ℕ)
    (hn : n ≤ P.timeConstant * m) (hj : j ≤ P.timeConstant * m) :
    (forestConnectedSolverRuntimeTime P.runtimeResources n j : ℝ) ≤
      P.solverRateCoefficient * ((m : ℝ) + 2) * alg2TimeFactor (12 * P.rateExponent) (47 / 48) m := by
  let r := P.runtimeResources
  let L0 := ipmQualityLimbs 0 (solverPenalty 0) (r.qualityExponent 0)
  let x := (m : ℝ) + 2
  let X := P.rateScale * x
  let W := alg2TimeFactor P.rateExponent (47 / 48) m
  let H := P.rateCoefficient * W
  let E := (forestConnectedSolverTimeAt (r.forSize 0) 0 0 0 : ℝ) + 2 * r.qualityCost 0 + 1000
  have hx : (2 : ℝ) ≤ x := by dsimp [x]; linarith only [Nat.cast_nonneg (α := ℝ) m]
  have hScale := P.rateScale_ge_one
  have hX : 1 ≤ X := le_trans (by linarith only [hx] : (1 : ℝ) ≤ x)
    (le_mul_of_one_le_left (by linarith only [hx]) hScale)
  have hX0 : 0 ≤ X := by positivity
  have hs (a : ℕ) (ha : a ≤ 7 * (P.timeConstant * m)) : (a : ℝ) + 2 ≤ X := by
    have ha' : (a : ℝ) ≤ 7 * ((P.timeConstant : ℝ) * m) := by exact_mod_cast ha
    unfold X x ForestConcreteProgramCore.rateScale
    push_cast
    nlinarith only [ha', Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) P.timeConstant]
  have hn' : (n : ℝ) + 2 ≤ X := hs n (by omega)
  have hj' : (j : ℝ) + 2 ≤ X := hs j (by omega)
  obtain ⟨hH, hB, hLg, hR, hK⟩ := forestConcreteRateEnvelope P m n j hn hj
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hE : 0 ≤ E := by
    dsimp [E]
    exact add_nonneg (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
      (by norm_num)
  have hWork : (forestConnectedSolverRuntimeTime r n j : ℝ) ≤
      (10 ^ 50 + 3000001 * ((L0 : ℝ) + 1) * E) * X * H ^ 12 := by
    by_cases hzero : j = 0
    · subst j
      have hz := forestSolver_zero r n
      have hz' : (forestConnectedSolverRuntimeTime r n 0 : ℝ) ≤
          E * (n + 2) * ((lctForestRate L0 (n + 1) : ℝ) + 1) := by
        unfold E
        exact_mod_cast hz
      have hRate := zero_rate_add_one_le L0 hH hLg
      have hRateNN : 0 ≤ (lctForestRate L0 (n + 1) : ℝ) + 1 :=
        add_nonneg (Nat.cast_nonneg _) zero_le_one
      refine hz'.trans ?_
      calc E * ((n : ℝ) + 2) * ((lctForestRate L0 (n + 1) : ℝ) + 1)
          ≤ E * X * (3000001 * ((L0 : ℝ) + 1) * H ^ 12) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hn' hE) hRate hRateNN (mul_nonneg hE hX0)
        _ = (3000001 * ((L0 : ℝ) + 1) * E) * X * H ^ 12 := by ring
        _ ≤ 10 ^ 50 * X * H ^ 12 + (3000001 * ((L0 : ℝ) + 1) * E) * X * H ^ 12 :=
            le_add_of_nonneg_left (mul_nonneg (mul_nonneg (by norm_num) hX0) (pow_nonneg hH0 12))
        _ = (10 ^ 50 + 3000001 * ((L0 : ℝ) + 1) * E) * X * H ^ 12 := by ring
    · have hp := forestSolver_bound_positive P n j (Nat.pos_of_ne_zero hzero) X H hX hH
        (by linarith only [hn']) (by linarith only [hj'])
        (fun M hM => by
          have hm' := hs M ((Finset.mem_Icc.mp hM).2.trans (Nat.mul_le_mul_left 7 hj))
          linarith only [hm'])
        hB hLg
        (fun M hM => hR M (Finset.mem_Icc.mp hM).2)
        (fun M hM => hK M (Finset.mem_Icc.mp hM).2)
        (fun M hM => by
          have hm' := hs M ((Finset.mem_Icc.mp hM).2.trans (Nat.mul_le_mul_left 7 hj))
          have hq : (r.qualityCost M : ℝ) ≤ 120 * ((M : ℝ) + 1) := by
            change (cappedQualityCost M : ℝ) ≤ _
            exact_mod_cast cappedQualityCost_le M
          linarith only [hm', hq, hX])
      have hNonneg : 0 ≤ 3000001 * ((L0 : ℝ) + 1) * E :=
        mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (Nat.cast_nonneg _) zero_le_one)) hE
      exact hp.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right hNonneg) hX0) (pow_nonneg hH0 _))
  refine hWork.trans_eq ?_
  change (10 ^ 50 + 3000001 * ((L0 : ℝ) + 1) * E) * X * H ^ 12 =
    P.solverRateCoefficient * x * alg2TimeFactor (12 * P.rateExponent) (47 / 48) m
  unfold ForestConcreteProgramCore.solverRateCoefficient
  dsimp only [X, H, x, E]
  rw [mul_pow, scalingTimeFactor_pow]
  simp only [show (↑(12 : ℕ) : ℝ) = 12 from rfl]
  ring

/-- The maximum over outer scaling dimensions obeys the edge-linear bound with
the Theorem 5.1 subpolynomial factor. -/
theorem ForestConcreteProgramCore.linkedSolverTime_le (P : ForestConcreteProgramCore)
    (m N M : ℕ) (hN : N ≤ P.timeConstant * m) (hM : M ≤ P.timeConstant * m) :
    (linkedForestSolverTime P.runtimeResources N M : ℝ) ≤
      P.solverRateCoefficient * ((m : ℝ) + 2) * alg2TimeFactor (12 * P.rateExponent) (47 / 48) m := by
  let rect := Finset.range (N + 1) ×ˢ Finset.range (M + 1)
  have hne : rect.Nonempty := ⟨(N, M), by simp [rect]⟩
  obtain ⟨⟨n, j⟩, hmem, hmax⟩ := Finset.exists_mem_eq_sup rect hne
    (fun nm => forestConnectedSolverRuntimeTime P.runtimeResources nm.1 nm.2)
  have hnm : n ≤ N ∧ j ≤ M := by simpa [rect, Nat.lt_succ_iff] using hmem
  change linkedForestSolverTime P.runtimeResources N M =
    forestConnectedSolverRuntimeTime P.runtimeResources n j at hmax
  rw [hmax]
  exact forestRuntimeTime_le P m n j (hnm.1.trans hN) (hnm.2.trans hM)

def ForestConcreteProgramBase.rateScale (P : ForestConcreteProgramBase) : ℝ := P.toCore.rateScale
def ForestConcreteProgramBase.cycleRescaledExponent (P : ForestConcreteProgramBase) : ℝ := P.toCore.cycleRescaledExponent
def ForestConcreteProgramBase.qualityRescaledExponent (P : ForestConcreteProgramBase) : ℝ := P.toCore.qualityRescaledExponent
def ForestConcreteProgramBase.rateExponent (P : ForestConcreteProgramBase) : ℝ := P.toCore.rateExponent
theorem ForestConcreteProgramBase.rateExponent_nonneg (P : ForestConcreteProgramBase) :
    0 ≤ P.rateExponent := P.toCore.rateExponent_nonneg
def ForestConcreteProgramBase.rateCoefficient (P : ForestConcreteProgramBase) : ℝ := P.toCore.rateCoefficient
theorem ForestConcreteProgramBase.rateCoefficient_ge_one (P : ForestConcreteProgramBase) :
    1 ≤ P.rateCoefficient := P.toCore.rateCoefficient_ge_one
def ForestConcreteProgramBase.solverRateCoefficient (P : ForestConcreteProgramBase) : ℝ := P.toCore.solverRateCoefficient
theorem ForestConcreteProgramBase.solverRateCoefficient_pos (P : ForestConcreteProgramBase) :
    0 < P.solverRateCoefficient := P.toCore.solverRateCoefficient_pos
theorem ForestConcreteProgramBase.linkedSolverTime_le (P : ForestConcreteProgramBase)
    (m N M : ℕ) (hN : N ≤ P.timeConstant * m) (hM : M ≤ P.timeConstant * m) :
    (linkedForestSolverTime P.runtimeResources N M : ℝ) ≤
      P.solverRateCoefficient * ((m : ℝ) + 2) * alg2TimeFactor (12 * P.rateExponent) (47 / 48) m :=
  P.toCore.linkedSolverTime_le m N M hN hM

def ForestConcretePrograms.rateScale (P : ForestConcretePrograms) : ℝ := P.toBase.rateScale
def ForestConcretePrograms.cycleRescaledExponent (P : ForestConcretePrograms) : ℝ := P.toBase.cycleRescaledExponent
def ForestConcretePrograms.qualityRescaledExponent (P : ForestConcretePrograms) : ℝ := P.toBase.qualityRescaledExponent
def ForestConcretePrograms.rateExponent (P : ForestConcretePrograms) : ℝ := P.toBase.rateExponent
theorem ForestConcretePrograms.rateExponent_nonneg (P : ForestConcretePrograms) :
    0 ≤ P.rateExponent := P.toBase.rateExponent_nonneg
def ForestConcretePrograms.rateCoefficient (P : ForestConcretePrograms) : ℝ := P.toBase.rateCoefficient
theorem ForestConcretePrograms.rateCoefficient_ge_one (P : ForestConcretePrograms) :
    1 ≤ P.rateCoefficient := P.toBase.rateCoefficient_ge_one
def ForestConcretePrograms.solverRateCoefficient (P : ForestConcretePrograms) : ℝ := P.toBase.solverRateCoefficient
theorem ForestConcretePrograms.solverRateCoefficient_pos (P : ForestConcretePrograms) :
    0 < P.solverRateCoefficient := P.toBase.solverRateCoefficient_pos
theorem ForestConcretePrograms.linkedSolverTime_le (P : ForestConcretePrograms)
    (m N M : ℕ) (hN : N ≤ P.timeConstant * m) (hM : M ≤ P.timeConstant * m) :
    (linkedForestSolverTime P.runtimeResources N M : ℝ) ≤
      P.solverRateCoefficient * ((m : ℝ) + 2) * alg2TimeFactor (12 * P.rateExponent) (47 / 48) m :=
  P.toBase.linkedSolverTime_le m N M hN hM

def DyadicForestConcretePrograms.rateScale (P : DyadicForestConcretePrograms) : ℝ := P.toBase.rateScale
def DyadicForestConcretePrograms.cycleRescaledExponent (P : DyadicForestConcretePrograms) : ℝ := P.toBase.cycleRescaledExponent
def DyadicForestConcretePrograms.qualityRescaledExponent (P : DyadicForestConcretePrograms) : ℝ := P.toBase.qualityRescaledExponent
def DyadicForestConcretePrograms.rateExponent (P : DyadicForestConcretePrograms) : ℝ := P.toBase.rateExponent
theorem DyadicForestConcretePrograms.rateExponent_nonneg (P : DyadicForestConcretePrograms) :
    0 ≤ P.rateExponent := P.toBase.rateExponent_nonneg
def DyadicForestConcretePrograms.rateCoefficient (P : DyadicForestConcretePrograms) : ℝ := P.toBase.rateCoefficient
theorem DyadicForestConcretePrograms.rateCoefficient_ge_one (P : DyadicForestConcretePrograms) :
    1 ≤ P.rateCoefficient := P.toBase.rateCoefficient_ge_one
def DyadicForestConcretePrograms.solverRateCoefficient (P : DyadicForestConcretePrograms) : ℝ := P.toBase.solverRateCoefficient
theorem DyadicForestConcretePrograms.solverRateCoefficient_pos (P : DyadicForestConcretePrograms) :
    0 < P.solverRateCoefficient := P.toBase.solverRateCoefficient_pos
theorem DyadicForestConcretePrograms.linkedSolverTime_le (P : DyadicForestConcretePrograms)
    (m N M : ℕ) (hN : N ≤ P.timeConstant * m) (hM : M ≤ P.timeConstant * m) :
    (linkedForestSolverTime P.runtimeResources N M : ℝ) ≤
      P.solverRateCoefficient * ((m : ℝ) + 2) * alg2TimeFactor (12 * P.rateExponent) (47 / 48) m :=
  P.toBase.linkedSolverTime_le m N M hN hM

def DyadicWithVConcretePrograms.rateScale (P : DyadicWithVConcretePrograms) : ℝ := P.toCore.rateScale
def DyadicWithVConcretePrograms.cycleRescaledExponent (P : DyadicWithVConcretePrograms) : ℝ := P.toCore.cycleRescaledExponent
def DyadicWithVConcretePrograms.qualityRescaledExponent (P : DyadicWithVConcretePrograms) : ℝ := P.toCore.qualityRescaledExponent
def DyadicWithVConcretePrograms.rateExponent (P : DyadicWithVConcretePrograms) : ℝ := P.toCore.rateExponent
theorem DyadicWithVConcretePrograms.rateExponent_nonneg (P : DyadicWithVConcretePrograms) :
    0 ≤ P.rateExponent := P.toCore.rateExponent_nonneg
def DyadicWithVConcretePrograms.rateCoefficient (P : DyadicWithVConcretePrograms) : ℝ := P.toCore.rateCoefficient
theorem DyadicWithVConcretePrograms.rateCoefficient_ge_one (P : DyadicWithVConcretePrograms) :
    1 ≤ P.rateCoefficient := P.toCore.rateCoefficient_ge_one
def DyadicWithVConcretePrograms.solverRateCoefficient (P : DyadicWithVConcretePrograms) : ℝ := P.toCore.solverRateCoefficient
theorem DyadicWithVConcretePrograms.solverRateCoefficient_pos (P : DyadicWithVConcretePrograms) :
    0 < P.solverRateCoefficient := P.toCore.solverRateCoefficient_pos
theorem DyadicWithVConcretePrograms.linkedSolverTime_le (P : DyadicWithVConcretePrograms)
    (m N M : ℕ) (hN : N ≤ P.timeConstant * m) (hM : M ≤ P.timeConstant * m) :
    (linkedForestSolverTime P.runtimeResources N M : ℝ) ≤
      P.solverRateCoefficient * ((m : ℝ) + 2) * alg2TimeFactor (12 * P.rateExponent) (47 / 48) m :=
  P.toCore.linkedSolverTime_le m N M hN hM

end MinCostFlow.Final
