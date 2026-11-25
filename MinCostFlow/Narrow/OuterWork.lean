module

public import MinCostFlow.Narrow.OuterDefs
public import MinCostFlow.Final.TimeExponent
public import MinCostFlow.Final.TimeFactorBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Parameterized non-solver work bounds and `timeBound` conversion (Item 4)

This file proves:
1. `outer_work_param_bound` and `outer_work_compressed_bound`: parameterized
   bounds combining per-phase, per-round, and reduction work outside the
   bounded solver across the at most two circulation calls of `narrowOuterModel`.
2. `narrowScalingLogs_le` and `narrow_cost_le_timeBound`: public analogues of
   the private logarithmic-conversion and `timeBound` lemmas in
   `MinCostFlow/Final/Theorem1_1.lean`, adapted to the two-factor logarithmic
   shape `narrowOuterLogFactor` of the narrow-word outer model.
-/

public section

namespace MinCostFlow.Narrow

open MinCostFlow.Scaling MinCostFlow.Final MinCostFlow.Chain

/-- Parameterized total non-solver work bound (Item 4): if each phase costs
at most `a * (m + n + 1)`, each round outside phases costs at most
`a * (m + n + 1) * (logU + logM + 1)`, and the reduction outside its two
circulation calls costs at most `a * (n + m * (logU + logC + 1))`, then total
non-solver work across at most two circulation calls is at most
`225 * a * (m + n + 1) * (logU + logM + 1) * (logC + logM + 1)`. -/
theorem outer_work_param_bound
    (a m n logU logC logM rounds phases phaseWork roundWork redWork : ℕ)
    (hrounds : rounds ≤ 28 * (logC + logM + 1))
    (hphases : phases ≤ 3 * (logU + logM + 1))
    (hphaseW : phaseWork ≤ a * (m + n + 1))
    (hroundW : roundWork ≤ a * (m + n + 1) * (logU + logM + 1))
    (hredW : redWork ≤ a * (n + m * (logU + logC + 1))) :
    redWork + 2 * (rounds * (phases * phaseWork + roundWork)) ≤
      225 * a * (m + n + 1) * (logU + logM + 1) * (logC + logM + 1) := by
  have h1 : phases * phaseWork ≤ 3 * a * (m + n + 1) * (logU + logM + 1) := by
    have hmul := Nat.mul_le_mul hphases hphaseW
    have heq : 3 * (logU + logM + 1) * (a * (m + n + 1)) =
        3 * a * (m + n + 1) * (logU + logM + 1) := by ring
    rwa [heq] at hmul
  have h2 : phases * phaseWork + roundWork ≤ 4 * a * (m + n + 1) * (logU + logM + 1) := by
    have hadd := Nat.add_le_add h1 hroundW
    have heq : 3 * a * (m + n + 1) * (logU + logM + 1) + a * (m + n + 1) * (logU + logM + 1) =
        4 * a * (m + n + 1) * (logU + logM + 1) := by ring
    rwa [heq] at hadd
  have h3 : 2 * (rounds * (phases * phaseWork + roundWork)) ≤
      224 * a * (m + n + 1) * (logU + logM + 1) * (logC + logM + 1) := by
    have hmul := Nat.mul_le_mul_left 2 (Nat.mul_le_mul hrounds h2)
    have heq : 2 * (28 * (logC + logM + 1) * (4 * a * (m + n + 1) * (logU + logM + 1))) =
        224 * a * (m + n + 1) * (logU + logM + 1) * (logC + logM + 1) := by ring
    rwa [heq] at hmul
  have hprod_ge : logU + logC + 1 ≤ (logU + logM + 1) * (logC + logM + 1) := by
    have heq : (logU + logM + 1) * (logC + logM + 1) =
        (logU + logC + 1) + (logU * logC + logU * logM + logM * logC + logM * logM + 2 * logM) := by
      ring
    omega
  have hprod_pos : 1 ≤ (logU + logM + 1) * (logC + logM + 1) := by omega
  have hred : redWork ≤ a * (m + n + 1) * (logU + logM + 1) * (logC + logM + 1) := by
    have hn_le : n ≤ n * ((logU + logM + 1) * (logC + logM + 1)) := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hprod_pos
    have hm_le : m * (logU + logC + 1) ≤ m * ((logU + logM + 1) * (logC + logM + 1)) :=
      Nat.mul_le_mul_left m hprod_ge
    have hsum : n + m * (logU + logC + 1) ≤
        (m + n + 1) * ((logU + logM + 1) * (logC + logM + 1)) := by
      have h1' : n + m * (logU + logC + 1) ≤
          (m + n) * ((logU + logM + 1) * (logC + logM + 1)) := by
        have heq : (m + n) * ((logU + logM + 1) * (logC + logM + 1)) =
            m * ((logU + logM + 1) * (logC + logM + 1)) +
              n * ((logU + logM + 1) * (logC + logM + 1)) := by ring
        omega
      exact le_trans h1' (Nat.mul_le_mul_right _ (Nat.le_succ _))
    have hmul := Nat.mul_le_mul_left a hsum
    have heq : a * ((m + n + 1) * ((logU + logM + 1) * (logC + logM + 1))) =
        a * (m + n + 1) * (logU + logM + 1) * (logC + logM + 1) := by ring
    exact le_trans hredW (heq ▸ hmul)
  have htot := Nat.add_le_add hred h3
  have heq : a * (m + n + 1) * (logU + logM + 1) * (logC + logM + 1) +
      224 * a * (m + n + 1) * (logU + logM + 1) * (logC + logM + 1) =
      225 * a * (m + n + 1) * (logU + logM + 1) * (logC + logM + 1) := by ring
  rwa [heq] at htot

/-- Compressed-circulation form of the parameterized non-solver work bound:
inside the two circulation calls `m_c ≤ 3 * m` and `n_c ≤ 2 * m_c`, so the
original vertex count `n` appears only linearly (`a * n`), matching `timeBound`. -/
theorem outer_work_compressed_bound
    (a m n m_c n_c logU logC logM rounds phases phaseWork roundWork redWork : ℕ)
    (hmc : m_c ≤ 3 * m) (hnc : n_c ≤ 2 * m_c)
    (hrounds : rounds ≤ 28 * (logC + logM + 1))
    (hphases : phases ≤ 3 * (logU + logM + 1))
    (hphaseW : phaseWork ≤ a * (m_c + n_c + 1))
    (hroundW : roundWork ≤ a * (m_c + n_c + 1) * (logU + logM + 1))
    (hredW : redWork ≤ a * (n + m * (logU + logC + 1))) :
    redWork + 2 * (rounds * (phases * phaseWork + roundWork)) ≤
      a * n + 2017 * a * (m + 1) * (logU + logM + 1) * (logC + logM + 1) := by
  have hmn : m_c + n_c + 1 ≤ 9 * (m + 1) := by omega
  have h1 : phases * phaseWork ≤ 27 * a * (m + 1) * (logU + logM + 1) := by
    have hp : phaseWork ≤ 9 * a * (m + 1) := by
      have := le_trans hphaseW (Nat.mul_le_mul_left a hmn)
      have heq : a * (9 * (m + 1)) = 9 * a * (m + 1) := by ring
      rwa [heq] at this
    have hmul := Nat.mul_le_mul hphases hp
    have heq : 3 * (logU + logM + 1) * (9 * a * (m + 1)) =
        27 * a * (m + 1) * (logU + logM + 1) := by ring
    rwa [heq] at hmul
  have h2 : roundWork ≤ 9 * a * (m + 1) * (logU + logM + 1) := by
    have := le_trans hroundW (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left a hmn))
    have heq : a * (9 * (m + 1)) * (logU + logM + 1) =
        9 * a * (m + 1) * (logU + logM + 1) := by ring
    rwa [heq] at this
  have h3 : phases * phaseWork + roundWork ≤ 36 * a * (m + 1) * (logU + logM + 1) := by
    have hadd := Nat.add_le_add h1 h2
    have heq : 27 * a * (m + 1) * (logU + logM + 1) + 9 * a * (m + 1) * (logU + logM + 1) =
        36 * a * (m + 1) * (logU + logM + 1) := by ring
    rwa [heq] at hadd
  have h4 : 2 * (rounds * (phases * phaseWork + roundWork)) ≤
      2016 * a * (m + 1) * (logU + logM + 1) * (logC + logM + 1) := by
    have hmul := Nat.mul_le_mul_left 2 (Nat.mul_le_mul hrounds h3)
    have heq : 2 * (28 * (logC + logM + 1) * (36 * a * (m + 1) * (logU + logM + 1))) =
        2016 * a * (m + 1) * (logU + logM + 1) * (logC + logM + 1) := by ring
    rwa [heq] at hmul
  have hprod_ge : logU + logC + 1 ≤ (logU + logM + 1) * (logC + logM + 1) := by
    have heq : (logU + logM + 1) * (logC + logM + 1) =
        (logU + logC + 1) + (logU * logC + logU * logM + logM * logC + logM * logM + 2 * logM) := by
      ring
    omega
  have hred : redWork ≤ a * n + a * (m + 1) * (logU + logM + 1) * (logC + logM + 1) := by
    have hm_le : m * (logU + logC + 1) ≤ (m + 1) * ((logU + logM + 1) * (logC + logM + 1)) :=
      Nat.mul_le_mul (Nat.le_succ m) hprod_ge
    have hmul := Nat.mul_le_mul_left a (Nat.add_le_add_left hm_le n)
    have heq : a * (n + (m + 1) * ((logU + logM + 1) * (logC + logM + 1))) =
        a * n + a * (m + 1) * (logU + logM + 1) * (logC + logM + 1) := by ring
    exact le_trans hredW (heq ▸ hmul)
  have htot := Nat.add_le_add hred h4
  have heq : a * n + a * (m + 1) * (logU + logM + 1) * (logC + logM + 1) +
      2016 * a * (m + 1) * (logU + logM + 1) * (logC + logM + 1) =
      a * n + 2017 * a * (m + 1) * (logU + logM + 1) * (logC + logM + 1) := by ring
  rwa [heq] at htot

private noncomputable def narrowBinaryLogCoef : ℝ := 3 / Real.log 2

private lemma narrowBinaryLogCoef_pos : 0 < narrowBinaryLogCoef :=
  div_pos (by norm_num) (Real.log_pos (by norm_num))

private lemma narrow_padded_clog_le (m : ℕ) :
    (Nat.clog 2 (m + 2) : ℝ) + 1 ≤ narrowBinaryLogCoef * Real.log ((m : ℝ) + 2) := by
  let k := Nat.clog 2 (m + 2)
  let x := (m : ℝ) + 2
  have hx : 2 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hlog : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk : 0 < k := Nat.clog_pos (by decide) (by omega)
  have he : k.pred + 1 = k := Nat.succ_pred_eq_of_pos hk
  have h := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega : 1 < m + 2)
  have hcast : (2 : ℝ) ^ k.pred < x := by
    dsimp only [k, x]
    exact_mod_cast h
  have hp := (Real.log_lt_log (by positivity) hcast).le
  rw [Real.log_pow] at hp
  have hcast' : (k.pred : ℝ) + 1 = k := by exact_mod_cast he
  change (k : ℝ) + 1 ≤ (3 / Real.log 2) * Real.log x
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hl).mpr
  rw [← hcast']
  linarith only [hp, hlog]

private lemma narrow_padded_clog_succ_le (m : ℕ) :
    (Nat.clog 2 (m + 1) : ℝ) + 1 ≤ narrowBinaryLogCoef * Real.log ((m : ℝ) + 2) := by
  have h : Nat.clog 2 (m + 1) ≤ Nat.clog 2 (m + 2) := Nat.clog_mono_right 2 (by omega)
  exact (add_le_add_left (by exact_mod_cast h) 1).trans (narrow_padded_clog_le m)

/-- Constant coefficient absorbing the two-factor binary-log product
`narrowOuterLogFactor m C U` into `log(m+2)^2 * log(U+2) * log(C+2)`. -/
noncomputable def narrowScalingLogCoefficient : ℝ :=
  36 / (Real.log 2) ^ 4

/-- `narrowScalingLogCoefficient` is strictly positive. -/
theorem narrowScalingLogCoefficient_pos : 0 < narrowScalingLogCoefficient :=
  div_pos (by norm_num) (pow_pos (Real.log_pos (by norm_num)) 4)

/-- Real-logarithm upper bound for `narrowOuterLogFactor m C U`, replacing the
private three-factor `scalingLogs_le` of `MinCostFlow/Final/Theorem1_1.lean`. -/
theorem narrowScalingLogs_le (m U C : ℕ) :
    (narrowOuterLogFactor m C U : ℝ) ≤
      narrowScalingLogCoefficient * (Real.log ((m : ℝ) + 2)) ^ 2 *
        Real.log ((U : ℝ) + 2) * Real.log ((C : ℝ) + 2) := by
  let l := Real.log 2
  let x := Real.log ((m : ℝ) + 2)
  let y := Real.log ((U : ℝ) + 2)
  let z := Real.log ((C : ℝ) + 2)
  let B := narrowBinaryLogCoef
  have hl : 0 < l := Real.log_pos (by norm_num)
  have hx : l ≤ x := Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hy : l ≤ y := Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) U])
  have hz : l ≤ z := Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) C])
  have hB : 0 < B := narrowBinaryLogCoef_pos
  have hm : (Nat.clog 2 (m + 1) : ℝ) + 1 ≤ B * x := narrow_padded_clog_succ_le m
  have hu : (Nat.clog 2 (U + 1) : ℝ) ≤ B * y := by
    have h := narrow_padded_clog_succ_le U
    change (Nat.clog 2 (U + 1) : ℝ) + 1 ≤ B * y at h
    linarith only [h]
  have hc : (Nat.clog 2 (C + 2) : ℝ) ≤ B * z := by
    have h := narrow_padded_clog_le C
    change (Nat.clog 2 (C + 2) : ℝ) + 1 ≤ B * z at h
    linarith only [h]
  have hxy : x + y ≤ (2 / l) * x * y := by
    have h1 := mul_le_mul_of_nonneg_left hy (show 0 ≤ x by linarith)
    have h2 := mul_le_mul_of_nonneg_right hx (show 0 ≤ y by linarith)
    have he : (2 / l) * x * y = (2 * x * y) / l := by ring
    rw [he]
    apply (le_div_iff₀ hl).mpr
    nlinarith only [h1, h2]
  have hxz : x + z ≤ (2 / l) * x * z := by
    have h1 := mul_le_mul_of_nonneg_left hz (show 0 ≤ x by linarith)
    have h2 := mul_le_mul_of_nonneg_right hx (show 0 ≤ z by linarith)
    have he : (2 / l) * x * z = (2 * x * z) / l := by ring
    rw [he]
    apply (le_div_iff₀ hl).mpr
    nlinarith only [h1, h2]
  have hf1 : (Nat.clog 2 (U + 1) : ℝ) + (Nat.clog 2 (m + 1) : ℝ) + 1 ≤ B * ((2 / l) * x * y) := by
    calc
      _ ≤ B * x + B * y := by linarith only [hm, hu]
      _ = B * (x + y) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hxy hB.le
  have hf2 : (Nat.clog 2 (C + 2) : ℝ) + (Nat.clog 2 (m + 1) : ℝ) + 1 ≤ B * ((2 / l) * x * z) := by
    calc
      _ ≤ B * x + B * z := by linarith only [hm, hc]
      _ = B * (x + z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hxz hB.le
  have hf1_nonneg : (0 : ℝ) ≤ (Nat.clog 2 (U + 1) : ℝ) + (Nat.clog 2 (m + 1) : ℝ) + 1 := by
    positivity
  have hf2_nonneg : (0 : ℝ) ≤ (Nat.clog 2 (C + 2) : ℝ) + (Nat.clog 2 (m + 1) : ℝ) + 1 := by
    positivity
  unfold narrowOuterLogFactor
  push_cast
  calc
    _ ≤ (B * ((2 / l) * x * y)) * (B * ((2 / l) * x * z)) :=
      mul_le_mul hf1 hf2 hf2_nonneg (le_trans hf1_nonneg hf1)
    _ = narrowScalingLogCoefficient * x ^ 2 * y * z := by
      unfold narrowScalingLogCoefficient
      dsimp only [B, narrowBinaryLogCoef, l]
      ring

/-- Plug-and-play `timeBound` conversion for the narrow-word outer model,
analogous to `scaling_cost_le_timeBound` in `MinCostFlow/Final/Theorem1_1.lean`. -/
theorem narrow_cost_le_timeBound
    (K : ℕ) (S_val cost : ℕ) (rateCoef rateExp finalCoef : ℝ) (I : Instance)
    (hRateExp : 0 ≤ rateExp) (hRateCoef : 0 < rateCoef)
    (hFinalCoef : finalCoef = max 1 (K : ℝ) * narrowScalingLogCoefficient * (rateCoef + 1))
    (hFinalPos : 0 < finalCoef)
    (hs : (S_val : ℝ) ≤ rateCoef * ((I.m : ℝ) + 2) *
      alg2TimeFactor (12 * rateExp) (47 / 48) I.m)
    (hcost : cost ≤ K * narrowOuterLogFactor I.m I.maxCost I.maxCapacity *
      (S_val + I.m + 1) + K * I.n) :
    (cost : ℝ) ≤ timeBound K
      (scalingTimeExponent finalCoef
        (12 * rateExp + 2 / (Real.log 2) ^ (47 / 48 : ℝ))) I := by
  let S : ℝ := (S_val : ℝ)
  let m := I.m
  let U := I.maxCapacity
  let C := I.maxCost
  let KR := (K : ℝ)
  let x := (m : ℝ) + 2
  let l := Real.log x
  let u := Real.log ((U : ℝ) + 2)
  let c := Real.log ((C : ℝ) + 2)
  let W := alg2TimeFactor (12 * rateExp) (47 / 48) m
  let V := alg2TimeFactor (2 / (Real.log 2) ^ (47 / 48 : ℝ)) (47 / 48) m
  have hW : 1 ≤ W := scalingTimeFactor_one_le (mul_nonneg (by norm_num) hRateExp) m
  have hx : 2 ≤ x := by dsimp only [x]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hl : 0 ≤ l := Real.log_nonneg (by linarith)
  have hu : 0 ≤ u := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) U])
  have hc : 0 ≤ c := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) C])
  have hpower : l ^ 2 ≤ V := by
    apply le_trans (pow_le_pow_left₀ hl (show l ≤ l + 2 by linarith) 2)
    simpa only [Nat.cast_ofNat] using paddedLog_pow_le_timeFactor 2 m
  have hlogs : (narrowOuterLogFactor m C U : ℝ) ≤ narrowScalingLogCoefficient * l ^ 2 * u * c :=
    narrowScalingLogs_le m U C
  have hs' : S + m + 1 ≤ (rateCoef + 1) * x * W := by
    have hm1 : (m : ℝ) + 1 ≤ x * W := by
      have h := mul_le_mul_of_nonneg_left hW (show 0 ≤ x by linarith)
      dsimp only [x] at h ⊢
      linarith
    change S ≤ rateCoef * x * W at hs
    linarith only [hs, hm1,
      show (rateCoef + 1) * x * W = rateCoef * x * W + x * W by ring]
  let L : ℝ := (narrowOuterLogFactor m C U : ℝ)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hK : 0 ≤ KR := Nat.cast_nonneg _
  have hterm : KR * L * (S + m + 1) ≤
      max 1 KR * (narrowScalingLogCoefficient * l ^ 2 * u * c) * ((rateCoef + 1) * x * W) := by
    have hbound : 0 ≤ (rateCoef + 1) * x * W := by positivity
    apply le_trans (mul_le_mul_of_nonneg_left hs' (mul_nonneg hK hL))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (le_max_right _ _) hlogs hL (le_trans zero_le_one (le_max_left _ _))) hbound
  have hprod : W * V = alg2TimeFactor (12 * rateExp + 2 / (Real.log 2) ^ (47 / 48 : ℝ)) (47 / 48) m := by
    dsimp only [W, V]
    rw [scalingTimeFactor_eq, scalingTimeFactor_eq, scalingTimeFactor_eq, ← Real.exp_add, add_mul]
  apply cost_le_timeBound_of_timeFactor _ _ _ _ hFinalPos
  have hcast : (cost : ℝ) ≤ KR * L * (S + m + 1) + KR * I.n := by
    dsimp only [KR, L, m, U, C, S]
    have hc' : (cost : ℝ) ≤ ((_ : ℕ) : ℝ) := (Nat.cast_le (α := ℝ)).mpr hcost
    push_cast at hc' ⊢
    simpa only [mul_assoc, add_assoc] using hc'
  calc
    _ ≤ KR * L * (S + m + 1) + KR * I.n := hcast
    _ ≤ max 1 KR * (narrowScalingLogCoefficient * l ^ 2 * u * c) *
        ((rateCoef + 1) * x * W) + KR * I.n := add_le_add_left hterm _
    _ = KR * I.n + (x * finalCoef * (W * l ^ 2)) * u * c := by
      rw [hFinalCoef]
      ring
    _ ≤ KR * I.n + (x * finalCoef * (W * V)) * u * c := by
      have hx0 : 0 ≤ x := by linarith
      have hW0 : 0 ≤ W := by linarith
      gcongr
    _ = _ := by
      rw [hprod]

end MinCostFlow.Narrow
