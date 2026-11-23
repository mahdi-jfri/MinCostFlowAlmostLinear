module

public import MinCostFlow.Final.ConcretePrograms
public import MinCostFlow.Final.TimeFactorBounds
import MinCostFlow.Final.RuntimeQualityBounds
import MinCostFlow.IPM.Machine.ConnectedSolverCost
import MinCostFlow.IPM.Machine.TargetTestCost
import Mathlib.Tactic

/-!
# Subpolynomial rate bound for the concrete linked solver

Absorbs the capped quality exponent (`cappedQualityExponent`), the
subpolynomial min-ratio cycle rate, and the polylogarithmic link-cut forest
rate into a single Theorem 5.1 subpolynomial envelope over the original
edge count `m`.
-/

@[expose] public noncomputable section
namespace MinCostFlow.Final
open Chain IPM IPM.Machine

def ConcreteDataStructurePrograms.rateScale (P : ConcreteDataStructurePrograms) : ℝ :=
  (7 * P.timeConstant + 2 : ℕ)

private theorem ConcreteDataStructurePrograms.rateScale_ge_two (P : ConcreteDataStructurePrograms) :
    2 ≤ P.rateScale := by
  unfold ConcreteDataStructurePrograms.rateScale
  exact_mod_cast (by omega : 2 ≤ 7 * P.timeConstant + 2)

private theorem ConcreteDataStructurePrograms.rateScale_ge_one (P : ConcreteDataStructurePrograms) :
    1 ≤ P.rateScale :=
  (by norm_num : (1 : ℝ) ≤ 2).trans P.rateScale_ge_two

def ConcreteDataStructurePrograms.cycleRescaledExponent (P : ConcreteDataStructurePrograms) : ℝ :=
  let a := logScale P.rateScale
  P.cycleRateExponent * a ^ (47 / 48 : ℝ) * logScale a

def ConcreteDataStructurePrograms.qualityRescaledExponent (P : ConcreteDataStructurePrograms) : ℝ :=
  let s : ℝ := ((P.edgeThreshold + 1 : ℕ) : ℝ) * P.rateScale
  let b := logScale s
  (65536 * ((P.qualityBudget : ℝ) + 1)) * b ^ (47 / 48 : ℝ) * logScale b

def ConcreteDataStructurePrograms.rateExponent (P : ConcreteDataStructurePrograms) : ℝ :=
  max P.cycleRescaledExponent
    (max P.qualityRescaledExponent
      (max ((P.forestLogDegree : ℝ) / (Real.log 2) ^ (47 / 48 : ℝ))
        (1 / (Real.log 2) ^ (47 / 48 : ℝ))))

theorem ConcreteDataStructurePrograms.rateExponent_nonneg (P : ConcreteDataStructurePrograms) :
    0 ≤ P.rateExponent := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < (Real.log 2) ^ (47 / 48 : ℝ) := Real.rpow_pos_of_pos hlog _
  have h1 : 0 ≤ 1 / (Real.log 2) ^ (47 / 48 : ℝ) := by positivity
  exact h1.trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

def ConcreteDataStructurePrograms.rateCoefficient (P : ConcreteDataStructurePrograms) : ℝ :=
  1 + 435 * logScale P.rateScale + P.cycleRateConstant +
    max 0 P.forestConstant * (logScale P.rateScale) ^ P.forestLogDegree

theorem ConcreteDataStructurePrograms.rateCoefficient_ge_one (P : ConcreteDataStructurePrograms) :
    1 ≤ P.rateCoefficient := by
  unfold ConcreteDataStructurePrograms.rateCoefficient
  have hc := P.cycleRateConstant_pos.le
  have hs := logScale_one_le P.rateScale_ge_one
  have hp : 0 ≤ max 0 P.forestConstant * (logScale P.rateScale) ^ P.forestLogDegree :=
    mul_nonneg (le_max_left 0 _) (pow_nonneg (by linarith) _)
  linarith

private theorem concreteRateEnvelope (P : ConcreteDataStructurePrograms) (m n j : ℕ)
    (hn : n ≤ P.timeConstant * m) (hj : j ≤ P.timeConstant * m) :
    let H := P.rateCoefficient * alg2TimeFactor P.rateExponent (47 / 48) m
    1 ≤ H ∧
    435 * Real.log ((j : ℝ) + 2) ≤ H ∧
    (P.resources.forestRate (n + 1) : ℝ) ≤ H ∧
    (∀ M ≤ 7 * j, (P.resources.cycleRate M : ℝ) ≤ H) ∧
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
    unfold ConcreteDataStructurePrograms.rateScale
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
      scalingTimeFactor_mono ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) m
    exact hp.trans hm
  have hB : 435 * Real.log ((j : ℝ) + 2) ≤ H := by
    have hW0 : 0 ≤ W := by linarith
    have hc435 : 435 * logScale P.rateScale ≤ P.rateCoefficient := by
      unfold ConcreteDataStructurePrograms.rateCoefficient
      have hc := P.cycleRateConstant_pos.le
      have hp : 0 ≤ max 0 P.forestConstant * (logScale P.rateScale) ^ P.forestLogDegree :=
        mul_nonneg (le_max_left 0 _) (pow_nonneg (by linarith) _)
      linarith
    calc 435 * Real.log ((j : ℝ) + 2)
        ≤ 435 * (logScale P.rateScale * Real.log ((m : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hjlog (by norm_num)
      _ ≤ (435 * logScale P.rateScale) * W := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmlog_W (by linarith)) (by norm_num)
      _ ≤ H := mul_le_mul_of_nonneg_right hc435 hW0
  have hF : (P.resources.forestRate (n + 1) : ℝ) ≤ H := by
    have hn_le : ((n + 1 : ℕ) : ℝ) + 2 ≤ P.rateScale * ((m : ℝ) + 2) := by
      unfold ConcreteDataStructurePrograms.rateScale
      have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hK_nn : (0 : ℝ) ≤ P.timeConstant := Nat.cast_nonneg _
      have hn' : (n : ℝ) ≤ (P.timeConstant : ℝ) * m := by exact_mod_cast hn
      push_cast
      nlinarith
    have hlog := log_le_scaled P.rateScale_ge_one hx2 (by positivity) hn_le
    have hlog_nn : 0 ≤ Real.log (((n + 1 : ℕ) : ℝ) + 2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (n + 1)])
    have hpow : Real.log (((n + 1 : ℕ) : ℝ) + 2) ^ P.forestLogDegree ≤
        (logScale P.rateScale * Real.log ((m : ℝ) + 2)) ^ P.forestLogDegree :=
      pow_le_pow_left₀ hlog_nn hlog _
    rw [mul_pow] at hpow
    have hmlog_nn : 0 ≤ Real.log ((m : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hpad : Real.log ((m : ℝ) + 2) ^ P.forestLogDegree ≤ W := by
      have h1 := pow_le_pow_left₀ hmlog_nn (show Real.log ((m : ℝ) + 2) ≤ Real.log ((m : ℝ) + 2) + 2 by linarith)
        P.forestLogDegree
      have h2 := paddedLog_pow_le_timeFactor P.forestLogDegree m
      have hm : alg2TimeFactor ((P.forestLogDegree : ℝ) / (Real.log 2) ^ (47 / 48 : ℝ)) (47 / 48) m ≤ W :=
        scalingTimeFactor_mono ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) m
      exact h1.trans (h2.trans hm)
    have hfr := P.forestRate_polylog (n + 1)
    have hf_le : (P.resources.forestRate (n + 1) : ℝ) ≤
        (max 0 P.forestConstant * (logScale P.rateScale) ^ P.forestLogDegree) * W := by
      have hscale_nn : 0 ≤ (logScale P.rateScale) ^ P.forestLogDegree := pow_nonneg (by linarith) _
      calc (P.resources.forestRate (n + 1) : ℝ)
          ≤ P.forestConstant * Real.log (((n + 1 : ℕ) : ℝ) + 2) ^ P.forestLogDegree := hfr
        _ ≤ max 0 P.forestConstant * ((logScale P.rateScale) ^ P.forestLogDegree *
              Real.log ((m : ℝ) + 2) ^ P.forestLogDegree) :=
            mul_le_mul (le_max_right _ _) hpow (pow_nonneg hlog_nn _) (le_max_left _ _)
        _ ≤ max 0 P.forestConstant * ((logScale P.rateScale) ^ P.forestLogDegree * W) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpad hscale_nn) (le_max_left _ _)
        _ = _ := by ring
    have hcF : max 0 P.forestConstant * (logScale P.rateScale) ^ P.forestLogDegree ≤ P.rateCoefficient := by
      unfold ConcreteDataStructurePrograms.rateCoefficient
      have hc := P.cycleRateConstant_pos.le
      linarith
    exact hf_le.trans (mul_le_mul_of_nonneg_right hcF (by linarith))
  have hCyc : ∀ M ≤ 7 * j, (P.resources.cycleRate M : ℝ) ≤ H := by
    intro M hMj
    have hM_le : (M : ℝ) + 2 ≤ P.rateScale * ((m : ℝ) + 2) := by
      unfold ConcreteDataStructurePrograms.rateScale
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
      unfold ConcreteDataStructurePrograms.rateCoefficient
      have hs_nn : 0 ≤ max 0 P.forestConstant * (logScale P.rateScale) ^ P.forestLogDegree :=
        mul_nonneg (le_max_left 0 _) (pow_nonneg (by linarith) _)
      linarith
    exact hcr.trans (mul_le_mul_of_nonneg_right hcC (by linarith))
  have hQual : ∀ M ≤ 7 * j, (2 : ℝ) ^ P.runtimeResources.qualityExponent M ≤ H := by
    intro M hMj
    let cap := max M P.edgeThreshold
    have hcap_le : (cap : ℝ) + 2 ≤ ((P.edgeThreshold + 1 : ℕ) : ℝ) * P.rateScale * ((m : ℝ) + 2) := by
      have hM_le : (M : ℝ) + 2 ≤ P.rateScale * ((m : ℝ) + 2) := by
        unfold ConcreteDataStructurePrograms.rateScale
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
      have hc1R : (cap : ℝ) + 2 ≤ ((P.edgeThreshold + 1 : ℕ) : ℝ) * ((M : ℝ) + 2) := by
        exact_mod_cast hc1
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
    exact hq_le.trans (le_mul_of_one_le_left (by linarith) hCoeff)
  exact ⟨hH, hB, hF, hCyc, hQual⟩

private def concreteCostPolynomial (n m M b W epochs forest cycle quality : ℝ) : ℝ :=
  1000 * n + 100000 * m * (W + 3 * b + 3) + forest * (n + 2 + 70 * m) +
    (2 + 2 * b) * (epochs * (M * (100000000 * W ^ 3) + (30 * M + 1) * cycle) + 100 * W + 419) +
    50 + 2 * quality

private theorem concreteCostPolynomial_mono
    {n m M b W d f c k n' m' M' b' W' d' f' c' k' : ℝ}
    (hn : 0 ≤ n) (hm : 0 ≤ m) (hM : 0 ≤ M) (hb : 0 ≤ b) (hW : 0 ≤ W)
    (hd : 0 ≤ d) (hf : 0 ≤ f) (hc : 0 ≤ c) (_hk : 0 ≤ k)
    (hn' : n ≤ n') (hm' : m ≤ m') (hM' : M ≤ M') (hb' : b ≤ b') (hW' : W ≤ W')
    (hd' : d ≤ d') (hf' : f ≤ f') (hc' : c ≤ c') (hk' : k ≤ k') :
    concreteCostPolynomial n m M b W d f c k ≤
      concreteCostPolynomial n' m' M' b' W' d' f' c' k' := by
  have hm₀ := hm.trans hm'
  have hf₀ := hf.trans hf'
  have hb₀ := hb.trans hb'
  have hd₀ := hd.trans hd'
  have hM₀ := hM.trans hM'
  unfold concreteCostPolynomial
  gcongr

private theorem concreteCostPolynomial_bound {x H : ℝ} (hx : 1 ≤ x) (hH : 1 ≤ H) :
    concreteCostPolynomial x x x H (30000116 * H ^ 2) (3276800000000001 * H ^ 5) H H (200 * x) ≤
      10 ^ 50 * x * H ^ 12 := by
  have hx0 : 0 ≤ x := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hp (a : ℕ) (ha : a ≤ 12) : x * H ^ a ≤ x * H ^ 12 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH ha) hx0
  have hp0 := hp 0 (by decide)
  have hp1 := hp 1 (by decide)
  have hp2 := hp 2 (by decide)
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
  unfold concreteCostPolynomial
  nlinarith only [hp0, hp1, hp2, hp6, hp7, hp11, hpure0, hpure1, hpure2, hpure3, hpure6, hpure7,
    mul_nonneg hx0 (pow_nonneg hH0 12)]

private theorem concreteSolver_bound_positive (r : SolverRuntimeResources) (n m : ℕ)
    (hm : 0 < m) (x H : ℝ) (hx : 1 ≤ x) (hH : 1 ≤ H)
    (hn : (n : ℝ) ≤ x) (he : (m : ℝ) ≤ x) (hAug : ∀ M ∈ Finset.Icc m (7 * m), (M : ℝ) ≤ x)
    (hB : 435 * Real.log ((m : ℝ) + 2) ≤ H)
    (hF : (r.template.forestRate (n + 1) : ℝ) ≤ H)
    (hR : ∀ M ∈ Finset.Icc m (7 * m), (r.template.cycleRate M : ℝ) ≤ H)
    (hK : ∀ M ∈ Finset.Icc m (7 * m), (2 : ℝ) ^ r.qualityExponent M ≤ H)
    (hC : ∀ M ∈ Finset.Icc m (7 * m), (r.qualityCost M : ℝ) ≤ 200 * x) :
    (connectedSolverRuntimeTime r n m : ℝ) ≤ 10 ^ 50 * x * H ^ 12 := by
  obtain ⟨M, hMem, hCost⟩ := connectedSolverRuntimeTime_width_bound r n m hm
  obtain ⟨hSmall, hLarge⟩ := Finset.mem_Icc.mp hMem
  obtain ⟨hSize, hBits⟩ := connectedSolverInputBits_log_bound m M hm hSmall hLarge
  let V := solverPenalty m
  let B := M.size + V.size
  let k := r.qualityExponent M
  let W := 30000000 * B ^ 2 + 116 * k
  let D := targetTestLimit M V k
  have hb : (B : ℝ) ≤ H := hBits.trans hB
  have hk : (k : ℝ) ≤ H := by
    have hk' : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
    exact hk'.trans (hK M hMem)
  have hW : (W : ℝ) ≤ 30000116 * H ^ 2 := by
    have hSq := pow_le_pow_left₀ (Nat.cast_nonneg B) hb 2
    have hH2 : H ≤ H ^ 2 := by nlinarith only [hH, sq_nonneg (H - 1)]
    unfold W
    push_cast
    linarith only [hSq, hk, hH2]
  have hd : (D : ℝ) ≤ 3276800000000001 * H ^ 5 := by
    have hLimit := targetTest_limit_bit_bound M V k hSize
    change (D : ℝ) ≤ 3276800000000001 * (B : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 2 at hLimit
    refine hLimit.trans ?_
    rw [show (5 : ℕ) = 3 + 2 by decide, pow_add, ← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg B) hb 3) (by norm_num))
      (pow_le_pow_left₀ (by positivity) (hK M hMem) 2) (by positivity) (by positivity)
  have hCast : (connectedSolverRuntimeTime r n m : ℝ) ≤ concreteCostPolynomial n m M B W D
      (r.template.forestRate (n + 1)) (r.template.cycleRate M) (r.qualityCost M) := by
    unfold concreteCostPolynomial
    exact_mod_cast hCost
  refine hCast.trans ((concreteCostPolynomial_mono (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hn he (hAug M hMem)
    hb hW hd hF (hR M hMem) (hC M hMem)).trans (concreteCostPolynomial_bound hx hH))

private theorem concreteSolver_zero (r : SolverRuntimeResources) (n : ℕ) :
    connectedSolverRuntimeTime r n 0 ≤
      (connectedSolverTimeAt (r.forSize 0) 0 0 0 + 2 * r.qualityCost 0 + 1000) *
        (n + 2) * (r.template.forestRate (n + 1) + 1) := by
  have hIcc : Finset.Icc (0 : ℕ) (7 * 0) = {0} := by ext x; simp
  unfold connectedSolverRuntimeTime
  rw [hIcc, Finset.sup_singleton]
  let E := connectedSolverTimeAt (r.forSize 0) 0 0 0 + 2 * r.qualityCost 0
  let f := r.template.forestRate (n + 1)
  have hBase : connectedSolverTimeAt (r.forSize 0) n 0 0 + 2 * r.qualityCost 0 ≤
      E + 930 * n + f * (n + 2) := by
    simp only [E, f, connectedSolverTimeAt, roundMachineCost, Nat.zero_mul, Nat.mul_zero,
      Nat.zero_add, Nat.add_zero, SolverRuntimeResources.forSize]
    rw [show n + 1 + 1 = n + 2 by rfl]
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
  exact max_le (hfixed.trans (Nat.le_add_left _ _))
    (hBase.trans (by linarith [hE, hF]))

def ConcreteDataStructurePrograms.solverRateCoefficient (P : ConcreteDataStructurePrograms) : ℝ :=
  let r := P.runtimeResources
  (10 ^ 50 + 2 * ((connectedSolverTimeAt (r.forSize 0) 0 0 0 : ℝ) + 2 * r.qualityCost 0 + 1000)) *
    P.rateScale * P.rateCoefficient ^ 12

theorem ConcreteDataStructurePrograms.solverRateCoefficient_pos (P : ConcreteDataStructurePrograms) :
    0 < P.solverRateCoefficient := by
  have hScale := P.rateScale_ge_one
  have hCoeff := P.rateCoefficient_ge_one
  unfold ConcreteDataStructurePrograms.solverRateCoefficient
  positivity

private theorem concreteRuntimeTime_le (P : ConcreteDataStructurePrograms) (m n j : ℕ)
    (hn : n ≤ P.timeConstant * m) (hj : j ≤ P.timeConstant * m) :
    (connectedSolverRuntimeTime P.runtimeResources n j : ℝ) ≤
      P.solverRateCoefficient * ((m : ℝ) + 2) * alg2TimeFactor (12 * P.rateExponent) (47 / 48) m := by
  let r := P.runtimeResources
  let x := (m : ℝ) + 2
  let X := P.rateScale * x
  let W := alg2TimeFactor P.rateExponent (47 / 48) m
  let H := P.rateCoefficient * W
  let E := (connectedSolverTimeAt (r.forSize 0) 0 0 0 : ℝ) + 2 * r.qualityCost 0 + 1000
  have hx : (2 : ℝ) ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hScale := P.rateScale_ge_one
  have hX : 1 ≤ X := le_trans (by linarith : (1 : ℝ) ≤ x) (le_mul_of_one_le_left (by linarith) hScale)
  have hs (a : ℕ) (ha : a ≤ 7 * (P.timeConstant * m)) : (a : ℝ) + 2 ≤ X := by
    have ha' : (a : ℝ) ≤ 7 * ((P.timeConstant : ℝ) * m) := by exact_mod_cast ha
    unfold X x ConcreteDataStructurePrograms.rateScale
    push_cast
    nlinarith only [ha', Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) P.timeConstant]
  have hn' : (n : ℝ) + 2 ≤ X := hs n (by omega)
  have hj' : (j : ℝ) + 2 ≤ X := hs j (by omega)
  obtain ⟨hH, hB, hF, hR, hK⟩ := concreteRateEnvelope P m n j hn hj
  have hE : 0 ≤ E :=
    add_nonneg (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
      (by norm_num)
  have hWork : (connectedSolverRuntimeTime r n j : ℝ) ≤ (10 ^ 50 + 2 * E) * X * H ^ 12 := by
    by_cases hzero : j = 0
    · subst j
      have hz := concreteSolver_zero r n
      have hz' : (connectedSolverRuntimeTime r n 0 : ℝ) ≤
          E * (n + 2) * ((r.template.forestRate (n + 1) : ℝ) + 1) := by
        unfold E
        exact_mod_cast hz
      have hH12 : H ≤ H ^ 12 := by
        simpa only [pow_one] using pow_le_pow_right₀ hH (show 1 ≤ 12 by decide)
      have hF' : (r.template.forestRate (n + 1) : ℝ) + 1 ≤ 2 * H ^ 12 := by
        change (r.template.forestRate (n + 1) : ℝ) ≤ H at hF
        linarith only [hH, hF, hH12]
      refine hz'.trans ?_
      calc _ ≤ E * X * (2 * H ^ 12) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hn' hE) hF'
            · positivity
            · exact mul_nonneg hE (by linarith)
        _ ≤ _ := by
            have hNum := mul_nonneg (by linarith : 0 ≤ X) (pow_nonneg (show 0 ≤ H by linarith) 12)
            nlinarith only [hNum]
    · have hp := concreteSolver_bound_positive r n j (Nat.pos_of_ne_zero hzero) X H hX hH
        (by linarith only [hn']) (by linarith only [hj'])
        (fun M hM => by
          have hm' := hs M ((Finset.mem_Icc.mp hM).2.trans (Nat.mul_le_mul_left 7 hj))
          linarith only [hm'])
        hB hF
        (fun M hM => hR M (Finset.mem_Icc.mp hM).2)
        (fun M hM => hK M (Finset.mem_Icc.mp hM).2)
        (fun M hM => by
          have hm' := hs M ((Finset.mem_Icc.mp hM).2.trans (Nat.mul_le_mul_left 7 hj))
          have hq : (r.qualityCost M : ℝ) ≤ 120 * ((M : ℝ) + 1) := by
            change (cappedQualityCost M : ℝ) ≤ _
            exact_mod_cast cappedQualityCost_le M
          linarith only [hm', hq, hX])
      exact hp.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (mul_nonneg (by norm_num) hE)) (by linarith)) (pow_nonneg (by linarith) _))
  refine hWork.trans_eq ?_
  change (10 ^ 50 + 2 * E) * X * H ^ 12 =
    (10 ^ 50 + 2 * E) * P.rateScale * P.rateCoefficient ^ 12 * x *
      alg2TimeFactor (12 * P.rateExponent) (47 / 48) m
  dsimp only [X, H, x]
  rw [mul_pow, scalingTimeFactor_pow]
  simp only [show (↑(12 : ℕ) : ℝ) = 12 from rfl]
  ring

/-- The maximum over the dimensions used by outer scaling obeys the edge-linear
bound with a concrete Theorem 5.1 subpolynomial factor. -/
theorem ConcreteDataStructurePrograms.linkedSolverTime_le (P : ConcreteDataStructurePrograms)
    (m N M : ℕ) (hN : N ≤ P.timeConstant * m) (hM : M ≤ P.timeConstant * m) :
    (linkedConnectedSolverTime P.runtimeResources N M : ℝ) ≤
      P.solverRateCoefficient * ((m : ℝ) + 2) * alg2TimeFactor (12 * P.rateExponent) (47 / 48) m := by
  let rect := Finset.range (N + 1) ×ˢ Finset.range (M + 1)
  have hne : rect.Nonempty := ⟨(N, M), by simp [rect]⟩
  obtain ⟨⟨n, j⟩, hmem, hmax⟩ := Finset.exists_mem_eq_sup rect hne
    (fun nm => connectedSolverRuntimeTime P.runtimeResources nm.1 nm.2)
  have hnm : n ≤ N ∧ j ≤ M := by simpa [rect, Nat.lt_succ_iff] using hmem
  change linkedConnectedSolverTime P.runtimeResources N M =
    connectedSolverRuntimeTime P.runtimeResources n j at hmax
  rw [hmax]
  exact concreteRuntimeTime_le P m n j (hnm.1.trans hN) (hnm.2.trans hM)

end MinCostFlow.Final
