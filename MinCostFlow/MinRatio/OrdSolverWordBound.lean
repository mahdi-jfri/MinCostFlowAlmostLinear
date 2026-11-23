module

public import MinCostFlow.MinRatio.OrdSolverLevelCapBounds
public import MinCostFlow.MinRatio.ShiftQuotaBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Word-size discharge for the sparse-core initialization condition (`(M + N + 2) ^ wordExp * (L + 1) < 2 ^ w`)

Under the split sparse-core contract (`SparseCore/Program/AssemblyContract.lean`), the word-size
condition at sparse-core initialization is
`(M + N + 2) ^ wordExp * (L + 1) < 2 ^ w`,
where `wordExp` depends only on `capExp` (`wordExp = 24` at `capExp = 3`), while `L` is bounded by
`limbMul * SparseCore.bundleLogFactor M N` (quadratic in `log₂ (M + N + 2)`).

Proves:
- `levelM_le_M0_mul_k`: under `cfg.ValidOrdNoHidden`, `levelM cfg.TP cfg.P i ≤ cfg.P.M₀ * cfg.P.k`.
- `chainParams_k_le_alg2TimeFactor`: for `P.d = chosenD (23 / 24) P.M₀`,
  `(P.k : ℝ) ≤ alg2TimeFactor 2 (47 / 48) P.M₀`.
- `bundleLogFactor_le_rpow`: `((Nat.log 2 A + 1) ^ 2 : ℝ) ≤ 289 * (A : ℝ) ^ (1 / 4 : ℝ)` for `2 ≤ A`.
- `concrete_sparseCoreWordBound_poly`: for any concrete chain witness `W`, `wordExp : ℕ`, and
  `limbMul : ℕ`, there is a constant `C_poly` (depending only on `W`, `wordExp`, `limbMul`) such
  that for every valid circulation `J`, every level `i`, and every
  `L ≤ limbMul * bundleLogFactor (levelM i) cfg.N₀`,
  `(levelM i + cfg.N₀ + 2) ^ wordExp * (L + 1) ≤ C_poly * (J.m + 2) ^ (wordExp + 1)`.
  At `wordExp = 24` this has degree `25 ≤ 40`.
- `forestProgramsScratchDegree_covers_poly`: generalizes
  `forestProgramsScratchDegree_covers_shiftQuota` from degree `7` to every degree `D ≤ 40`.
- `concrete_sparseCoreWordBound_lt_two_pow_wordSize`: discharges
  `(levelM i + cfg.N₀ + 2) ^ wordExp * (L + 1) < 2 ^ w` for every `wordExp ≤ 39` (in particular
  `wordExp = 24`, degree `25 ≤ 40`) via `lt_two_pow_wordSize_of_poly_and_hw`, whenever
  `C_sw ≤ allocationCoefficient`.
- `concrete_sparseCoreWordBound_lt_two_pow_wordSize_deg25` and
  `concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize`: explicit corollaries at `wordExp = 24`
  (degree `25`) and for uniform `F.limbs = ipmQualityLimbs I.m V k` with
  `limbMul = concreteReadout2LimbMul W`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Final

/-- Under `cfg.ValidOrdNoHidden`, `levelM cfg.TP cfg.P i ≤ cfg.P.M₀ * cfg.P.k` for every level `i`. -/
theorem levelM_le_M0_mul_k {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden) (i : ℕ) :
    levelM cfg.TP cfg.P i ≤ cfg.P.M₀ * cfg.P.k := by
  have hk : (0 : ℝ) < cfg.P.k := Nat.cast_pos.mpr cfg.P.hk
  have hγ1 : 1 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)
  have hγnn : 0 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / (cfg.P.k : ℝ) :=
    div_nonneg (le_trans zero_le_one hγ1) hk.le
  have hγle : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / (cfg.P.k : ℝ) ≤ 1 := (div_le_one hk).mpr hV.hγk
  have hpow : (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / (cfg.P.k : ℝ)) ^ i ≤ 1 := pow_le_one₀ hγnn hγle
  have hle : (cfg.P.M₀ : ℝ) * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) *
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / (cfg.P.k : ℝ)) ^ i ≤ ((cfg.P.M₀ * cfg.P.k : ℕ) : ℝ) := by
    push_cast
    calc
      (cfg.P.M₀ : ℝ) * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) *
          (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / (cfg.P.k : ℝ)) ^ i
          ≤ (cfg.P.M₀ : ℝ) * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one hγ1))
      _ = (cfg.P.M₀ : ℝ) * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := mul_one _
      _ ≤ (cfg.P.M₀ : ℝ) * (cfg.P.k : ℝ) :=
        mul_le_mul_of_nonneg_left hV.hγk (Nat.cast_nonneg _)
  exact Nat.ceil_le.mpr hle

/-- The branching factor `P.k` at depth `chosenD (23 / 24) P.M₀` is bounded by the subpolynomial
envelope `alg2TimeFactor 2 (47 / 48) P.M₀`. -/
theorem chainParams_k_le_alg2TimeFactor (P : ChainParams)
    (hd : P.d = chosenD (23 / 24) P.M₀) :
    (P.k : ℝ) ≤ alg2TimeFactor 2 (47 / 48) P.M₀ := by
  have hM₀ : 1 ≤ P.M₀ := P.hM₀
  have hM1 : (1 : ℝ) ≤ (P.M₀ : ℝ) := by exact_mod_cast hM₀
  have hM_pos : (0 : ℝ) < (P.M₀ : ℝ) := by linarith
  set L : ℝ := Real.log ((P.M₀ : ℝ) + 2)
  set LL : ℝ := Real.log (L + 2)
  set E : ℝ := L ^ (47 / 48 : ℝ) * LL
  have hL1 : 1 ≤ L := by
    have hexp : Real.exp 1 ≤ (P.M₀ : ℝ) + 2 := by linarith [Real.exp_one_lt_d9]
    exact (Real.le_log_iff_exp_le (by linarith)).mpr hexp
  have hL_pos : 0 < L := by linarith
  have hLL1 : 1 ≤ LL := by
    have hexp : Real.exp 1 ≤ L + 2 := by linarith [Real.exp_one_lt_d9]
    exact (Real.le_log_iff_exp_le (by linarith)).mpr hexp
  have hLa1 : 1 ≤ L ^ (47 / 48 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hE1 : 1 ≤ E := one_le_mul_of_one_le_of_one_le hLa1 hLL1
  obtain ⟨_, hd_lo, _⟩ := chosenD_bounds (β := 23 / 24) (by norm_num) hM₀
  rw [← hd, show ((1 : ℝ) - 23 / 24) / 2 = 1 / 48 by norm_num] at hd_lo
  have hd_pos : (0 : ℝ) < (P.d : ℝ) := Nat.cast_pos.mpr P.hd
  have hM1d0 : 0 ≤ (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) := by positivity
  have hM1d : (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) ≤ Real.exp E := by
    have hlogM : Real.log (P.M₀ : ℝ) ≤ L := Real.log_le_log hM_pos (by linarith)
    have hdiv_le : Real.log (P.M₀ : ℝ) / (P.d : ℝ) ≤ L / L ^ (1 / 48 : ℝ) :=
      le_trans (div_le_div_of_nonneg_right hlogM hd_pos.le)
        (div_le_div_of_nonneg_left (by linarith) (by positivity) hd_lo)
    have hL_pow_div : L / L ^ (1 / 48 : ℝ) = L ^ (47 / 48 : ℝ) := by
      nth_rw 1 [← Real.rpow_one L]
      rw [← Real.rpow_sub hL_pos]
      congr 1; norm_num
    have hexp_le : Real.log (P.M₀ : ℝ) / (P.d : ℝ) ≤ E := by
      rw [hL_pow_div] at hdiv_le
      have hLE : L ^ (47 / 48 : ℝ) ≤ E := le_mul_of_one_le_right (by linarith) hLL1
      linarith
    rw [Real.rpow_def_of_pos hM_pos, mul_one_div]
    exact Real.exp_le_exp.mpr hexp_le
  have h2E : (2 : ℝ) ≤ Real.exp E :=
    le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_le_exp.mpr hE1)
  calc (P.k : ℝ)
      ≤ 2 * (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) := P.hk_upper
    _ ≤ Real.exp E * Real.exp E := mul_le_mul h2E hM1d hM1d0 (by positivity)
    _ = Real.exp (2 * E) := by rw [← Real.exp_add]; ring_nf
    _ = alg2TimeFactor 2 (47 / 48) P.M₀ := by
        unfold alg2TimeFactor
        congr 1; ring

/-- The squared binary log factor `(Nat.log 2 A + 1) ^ 2` is bounded by `289 * A ^ (1 / 4)` for
every `A ≥ 2`. -/
theorem bundleLogFactor_le_rpow {A : ℕ} (hA : 2 ≤ A) :
    (((Nat.log 2 A + 1) ^ 2 : ℕ) : ℝ) ≤ 289 * (A : ℝ) ^ (1 / 4 : ℝ) := by
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast (by omega : 1 ≤ A)
  have hApos : (0 : ℝ) < (A : ℝ) := by linarith
  have hpowLe : ((2 ^ Nat.log 2 A : ℕ) : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog2 : (Nat.log 2 A : ℝ) * Real.log 2 ≤ Real.log (A : ℝ) := by
    have h1 := Real.log_le_log (by positivity) hpowLe
    simpa [Real.log_pow] using h1
  have hlog2_lo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogLe : (Nat.log 2 A : ℝ) ≤ 2 * Real.log (A : ℝ) := by
    have hnn : (0 : ℝ) ≤ (Nat.log 2 A : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hlogRpow : Real.log (A : ℝ) ≤ 8 * (A : ℝ) ^ (1 / 8 : ℝ) := by
    have h := Real.log_le_rpow_div hApos.le (by norm_num : (0 : ℝ) < 1 / 8)
    linarith
  have h1le : (1 : ℝ) ≤ (A : ℝ) ^ (1 / 8 : ℝ) := Real.one_le_rpow hA1 (by norm_num)
  have hlin : ((Nat.log 2 A + 1 : ℕ) : ℝ) ≤ 17 * (A : ℝ) ^ (1 / 8 : ℝ) := by
    push_cast
    linarith
  have hsq : (((Nat.log 2 A + 1) ^ 2 : ℕ) : ℝ) ≤ (17 * (A : ℝ) ^ (1 / 8 : ℝ)) ^ 2 := by
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hlin 2
  have hrpowSq : ((A : ℝ) ^ (1 / 8 : ℝ)) ^ 2 = (A : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast ((A : ℝ) ^ (1 / 8 : ℝ)) 2, ← Real.rpow_mul hApos.le]
    congr 1; norm_num
  calc (((Nat.log 2 A + 1) ^ 2 : ℕ) : ℝ)
      ≤ (17 * (A : ℝ) ^ (1 / 8 : ℝ)) ^ 2 := hsq
    _ = 289 * ((A : ℝ) ^ (1 / 8 : ℝ)) ^ 2 := by ring
    _ = 289 * (A : ℝ) ^ (1 / 4 : ℝ) := by rw [hrpowSq]

/-- For every chain witness `W` and exponent `δ > 0`, `levelM cfg.TP cfg.P i + cfg.N₀ + 2` is
bounded by `C₁ * (J.m + 2) ^ (1 + δ)` with `1 ≤ C₁` depending only on `W` and `δ`. -/
private theorem levelM_add_N0_add_two_le_rpow
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ (J : Circulation),
      J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
      let cfg := concreteCirculationCfgWithLast W J
      ∀ i : ℕ,
        ((levelM cfg.TP cfg.P i + cfg.N₀ + 2 : ℕ) : ℝ) ≤
          C₁ * ((J.m : ℝ) + 2) ^ (1 + δ) := by
  let threshold := concreteEdgeThresholdWithLast W
  obtain ⟨B, hB1, hB⟩ := alg2TimeFactor_le_rpow (C := 2) (a := 47 / 48) (δ := δ)
    (by norm_num) (by norm_num) hδ
  have hth1 : (1 : ℝ) ≤ ((threshold + 7 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ threshold + 7)
  have hthPow1 : (1 : ℝ) ≤ ((threshold + 7 : ℕ) : ℝ) ^ (1 + δ) :=
    Real.one_le_rpow hth1 (by linarith)
  set C₁ : ℝ := (B + 6) * ((threshold + 7 : ℕ) : ℝ) ^ (1 + δ)
  have hC₁1 : 1 ≤ C₁ := by
    have : (1 : ℝ) ≤ B + 6 := by linarith
    exact one_le_mul_of_one_le_of_one_le this hthPow1
  refine ⟨C₁, hC₁1, fun J hJn hJm hCap => ?_⟩
  dsimp only
  intro i
  set cfg := concreteCirculationCfgWithLast W J
  set I := solverConnectedAugmented J
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm hCap
  have hM0_1 : 1 ≤ cfg.P.M₀ := cfg.P.hM₀
  have hM0_r1 : (1 : ℝ) ≤ (cfg.P.M₀ : ℝ) := by exact_mod_cast hM0_1
  have hM0_pos : (0 : ℝ) < (cfg.P.M₀ : ℝ) := by linarith
  have hk_le : (cfg.P.k : ℝ) ≤ B * (cfg.P.M₀ : ℝ) ^ δ :=
    (chainParams_k_le_alg2TimeFactor cfg.P rfl).trans (hB cfg.P.M₀ hM0_1)
  have hlvl_le : (levelM cfg.TP cfg.P i : ℝ) ≤ B * (cfg.P.M₀ : ℝ) ^ (1 + δ) := by
    have h1 : (levelM cfg.TP cfg.P i : ℝ) ≤ (cfg.P.M₀ : ℝ) * (cfg.P.k : ℝ) := by
      exact_mod_cast levelM_le_M0_mul_k hVcfg i
    have h2 : (cfg.P.M₀ : ℝ) * (cfg.P.k : ℝ) ≤ (cfg.P.M₀ : ℝ) * (B * (cfg.P.M₀ : ℝ) ^ δ) :=
      mul_le_mul_of_nonneg_left hk_le hM0_pos.le
    have h3 : (cfg.P.M₀ : ℝ) * (B * (cfg.P.M₀ : ℝ) ^ δ) = B * (cfg.P.M₀ : ℝ) ^ (1 + δ) := by
      rw [Real.rpow_add hM0_pos, Real.rpow_one]; ring
    linarith
  have hM0_le_rpow : (cfg.P.M₀ : ℝ) ≤ (cfg.P.M₀ : ℝ) ^ (1 + δ) := by
    calc (cfg.P.M₀ : ℝ) = (cfg.P.M₀ : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (cfg.P.M₀ : ℝ) ^ (1 + δ) := Real.rpow_le_rpow_of_exponent_le hM0_r1 (by linarith)
  have hN0_le : (cfg.N₀ : ℝ) + 2 ≤ 6 * (cfg.P.M₀ : ℝ) ^ (1 + δ) := by
    have hN0Eq : (cfg.N₀ : ℝ) = 4 * (cfg.P.M₀ : ℝ) := by
      change ((4 * cfg.P.M₀ : ℕ) : ℝ) = _; push_cast; ring
    linarith
  have hsumM0 : ((levelM cfg.TP cfg.P i + cfg.N₀ + 2 : ℕ) : ℝ) ≤
      (B + 6) * (cfg.P.M₀ : ℝ) ^ (1 + δ) := by
    push_cast
    linarith
  have hImLe : I.m ≤ 7 * J.m := (solverConnectedAugmented_size J hJn hJm hCap).2
  have hM0LeJm : cfg.P.M₀ ≤ (threshold + 7) * (J.m + 2) := by
    have h1 : cfg.P.M₀ ≤ 7 * J.m + threshold := by
      change max I.m threshold ≤ 7 * J.m + threshold
      exact max_le (by omega) (by omega)
    have h2 : 7 * J.m + threshold ≤ (threshold + 7) * (J.m + 2) := by nlinarith
    exact h1.trans h2
  have hM0LeJm_r : (cfg.P.M₀ : ℝ) ≤ ((threshold + 7 : ℕ) : ℝ) * ((J.m : ℝ) + 2) := by
    exact_mod_cast hM0LeJm
  have hpowM0 : (cfg.P.M₀ : ℝ) ^ (1 + δ) ≤
      ((threshold + 7 : ℕ) : ℝ) ^ (1 + δ) * ((J.m : ℝ) + 2) ^ (1 + δ) := by
    calc (cfg.P.M₀ : ℝ) ^ (1 + δ)
        ≤ (((threshold + 7 : ℕ) : ℝ) * ((J.m : ℝ) + 2)) ^ (1 + δ) :=
          Real.rpow_le_rpow hM0_pos.le hM0LeJm_r (by linarith)
      _ = ((threshold + 7 : ℕ) : ℝ) ^ (1 + δ) * ((J.m : ℝ) + 2) ^ (1 + δ) :=
          Real.mul_rpow (by positivity) (by positivity)
  calc ((levelM cfg.TP cfg.P i + cfg.N₀ + 2 : ℕ) : ℝ)
      ≤ (B + 6) * (cfg.P.M₀ : ℝ) ^ (1 + δ) := hsumM0
    _ ≤ (B + 6) * (((threshold + 7 : ℕ) : ℝ) ^ (1 + δ) * ((J.m : ℝ) + 2) ^ (1 + δ)) :=
        mul_le_mul_of_nonneg_left hpowM0 (by linarith)
    _ = C₁ * ((J.m : ℝ) + 2) ^ (1 + δ) := by ring

/-- **Polynomial bound on `(levelM i + N₀ + 2) ^ wordExp * (L + 1)` of degree `wordExp + 1`.**
For every witness `W`, `wordExp : ℕ`, and `limbMul : ℕ`, there is a constant `C_poly` (depending
only on `W`, `wordExp`, `limbMul`) such that for every valid circulation `J`, every level `i`, and
every `L ≤ limbMul * bundleLogFactor (levelM i) cfg.N₀`,
`(levelM i + cfg.N₀ + 2) ^ wordExp * (L + 1) ≤ C_poly * (J.m + 2) ^ (wordExp + 1)`.
At `wordExp = 24` (`capExp = 3`), the degree is `25 ≤ 40`. -/
theorem concrete_sparseCoreWordBound_poly
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    (wordExp limbMul : ℕ) :
    ∃ C_poly : ℕ, ∀ (J : Circulation),
      J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
      let cfg := concreteCirculationCfgWithLast W J
      ∀ (i L : ℕ),
        L ≤ limbMul * bundleLogFactor (levelM cfg.TP cfg.P i) cfg.N₀ →
        (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ wordExp * (L + 1) ≤
          C_poly * (J.m + 2) ^ (wordExp + 1) := by
  set δ : ℝ := 1 / (2 * ((wordExp : ℝ) + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨C₁, hC₁1, hC₁⟩ := levelM_add_N0_add_two_le_rpow W hδ
  set K : ℝ := C₁ ^ wordExp * (((limbMul : ℝ) + 1) * 289 * C₁ ^ (1 / 4 : ℝ))
  refine ⟨⌈K⌉₊, fun J hJn hJm hCap => ?_⟩
  dsimp only
  intro i L hL
  set cfg := concreteCirculationCfgWithLast W J
  set A := levelM cfg.TP cfg.P i + cfg.N₀ + 2
  have hA2 : 2 ≤ A := by omega
  have hA_le : (A : ℝ) ≤ C₁ * ((J.m : ℝ) + 2) ^ (1 + δ) := hC₁ J hJn hJm hCap i
  have hJm2_1 : (1 : ℝ) ≤ (J.m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) J.m]
  have hJm2_pos : (0 : ℝ) < (J.m : ℝ) + 2 := by linarith
  have hApow : ((A ^ wordExp : ℕ) : ℝ) ≤
      C₁ ^ wordExp * ((J.m : ℝ) + 2) ^ ((wordExp : ℝ) * (1 + δ)) := by
    push_cast
    calc (A : ℝ) ^ wordExp
        ≤ (C₁ * ((J.m : ℝ) + 2) ^ (1 + δ)) ^ wordExp :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hA_le wordExp
      _ = C₁ ^ wordExp * (((J.m : ℝ) + 2) ^ (1 + δ)) ^ wordExp := mul_pow _ _ _
      _ = C₁ ^ wordExp * ((J.m : ℝ) + 2) ^ ((wordExp : ℝ) * (1 + δ)) := by
          rw [← Real.rpow_natCast (((J.m : ℝ) + 2) ^ (1 + δ)) wordExp,
            ← Real.rpow_mul hJm2_pos.le, mul_comm (1 + δ)]
  have hL1_le : ((L + 1 : ℕ) : ℝ) ≤
      ((limbMul : ℝ) + 1) * 289 * C₁ ^ (1 / 4 : ℝ) * ((J.m : ℝ) + 2) ^ ((1 + δ) / 4) := by
    have hbf1 : 1 ≤ bundleLogFactor (levelM cfg.TP cfg.P i) cfg.N₀ := by
      unfold bundleLogFactor; exact Nat.one_le_pow _ _ (by omega)
    have hL1_nat : L + 1 ≤ (limbMul + 1) * bundleLogFactor (levelM cfg.TP cfg.P i) cfg.N₀ := by
      have : L + 1 ≤ limbMul * bundleLogFactor (levelM cfg.TP cfg.P i) cfg.N₀ +
          1 * bundleLogFactor (levelM cfg.TP cfg.P i) cfg.N₀ := by omega
      rwa [← Nat.add_mul] at this
    have hL1_r : ((L + 1 : ℕ) : ℝ) ≤
        ((limbMul : ℝ) + 1) * (((Nat.log 2 A + 1) ^ 2 : ℕ) : ℝ) := by
      have : ((L + 1 : ℕ) : ℝ) ≤
          (((limbMul + 1) * bundleLogFactor (levelM cfg.TP cfg.P i) cfg.N₀ : ℕ) : ℝ) := by
        exact_mod_cast hL1_nat
      simpa [bundleLogFactor, A, Nat.cast_mul, Nat.cast_add] using this
    have hbf_r : (((Nat.log 2 A + 1) ^ 2 : ℕ) : ℝ) ≤ 289 * (A : ℝ) ^ (1 / 4 : ℝ) :=
      bundleLogFactor_le_rpow hA2
    have hAr4 : (A : ℝ) ^ (1 / 4 : ℝ) ≤ C₁ ^ (1 / 4 : ℝ) * ((J.m : ℝ) + 2) ^ ((1 + δ) / 4) := by
      calc (A : ℝ) ^ (1 / 4 : ℝ)
          ≤ (C₁ * ((J.m : ℝ) + 2) ^ (1 + δ)) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hA_le (by norm_num)
        _ = C₁ ^ (1 / 4 : ℝ) * (((J.m : ℝ) + 2) ^ (1 + δ)) ^ (1 / 4 : ℝ) :=
            Real.mul_rpow (by linarith) (by positivity)
        _ = C₁ ^ (1 / 4 : ℝ) * ((J.m : ℝ) + 2) ^ ((1 + δ) / 4) := by
            rw [← Real.rpow_mul hJm2_pos.le]; congr 2; ring
    calc ((L + 1 : ℕ) : ℝ)
        ≤ ((limbMul : ℝ) + 1) * (289 * (A : ℝ) ^ (1 / 4 : ℝ)) :=
          hL1_r.trans (mul_le_mul_of_nonneg_left hbf_r (by positivity))
      _ ≤ ((limbMul : ℝ) + 1) * (289 * (C₁ ^ (1 / 4 : ℝ) * ((J.m : ℝ) + 2) ^ ((1 + δ) / 4))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAr4 (by norm_num)) (by positivity)
      _ = ((limbMul : ℝ) + 1) * 289 * C₁ ^ (1 / 4 : ℝ) * ((J.m : ℝ) + 2) ^ ((1 + δ) / 4) := by
          ring
  have hexpLe : (wordExp : ℝ) * (1 + δ) + (1 + δ) / 4 ≤ ((wordExp + 1 : ℕ) : ℝ) := by
    have h1 : (wordExp : ℝ) * δ ≤ 1 / 2 := by
      dsimp only [δ]
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) wordExp]
    have h2 : δ ≤ 1 / 2 := by
      dsimp only [δ]
      rw [div_le_iff₀ (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) wordExp]
    push_cast
    linarith
  have hpowExp : ((J.m : ℝ) + 2) ^ ((wordExp : ℝ) * (1 + δ) + (1 + δ) / 4) ≤
      ((J.m : ℝ) + 2) ^ (wordExp + 1) := by
    calc ((J.m : ℝ) + 2) ^ ((wordExp : ℝ) * (1 + δ) + (1 + δ) / 4)
        ≤ ((J.m : ℝ) + 2) ^ ((wordExp + 1 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hJm2_1 hexpLe
      _ = ((J.m : ℝ) + 2) ^ (wordExp + 1) := Real.rpow_natCast _ _
  have hprod : ((A ^ wordExp * (L + 1) : ℕ) : ℝ) ≤ K * ((J.m : ℝ) + 2) ^ (wordExp + 1) := by
    rw [Nat.cast_mul]
    calc ((A ^ wordExp : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ)
        ≤ (C₁ ^ wordExp * ((J.m : ℝ) + 2) ^ ((wordExp : ℝ) * (1 + δ))) *
            (((limbMul : ℝ) + 1) * 289 * C₁ ^ (1 / 4 : ℝ) * ((J.m : ℝ) + 2) ^ ((1 + δ) / 4)) :=
          mul_le_mul hApow hL1_le (Nat.cast_nonneg _) (by positivity)
      _ = K * (((J.m : ℝ) + 2) ^ ((wordExp : ℝ) * (1 + δ)) * ((J.m : ℝ) + 2) ^ ((1 + δ) / 4)) := by
          dsimp only [K]; ring
      _ = K * ((J.m : ℝ) + 2) ^ ((wordExp : ℝ) * (1 + δ) + (1 + δ) / 4) := by
          rw [← Real.rpow_add hJm2_pos]
      _ ≤ K * ((J.m : ℝ) + 2) ^ (wordExp + 1) :=
          mul_le_mul_of_nonneg_left hpowExp (by positivity)
  have hKceil : K * ((J.m : ℝ) + 2) ^ (wordExp + 1) ≤
      ((⌈K⌉₊ * (J.m + 2) ^ (wordExp + 1) : ℕ) : ℝ) := by
    push_cast
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil K) (by positivity)
  exact_mod_cast hprod.trans hKceil

/-- When `D ≤ 40` and `C ≤ allocationCoefficient`, `forestProgramsScratchDegree allocationCoefficient
allocationDegree Ck` automatically satisfies `(3 ^ D * C) ^ 2 < 2 ^ (3 * (deg + 1))`.
Generalizes `forestProgramsScratchDegree_covers_shiftQuota` (`D = 7`) to every degree up to `40`. -/
theorem forestProgramsScratchDegree_covers_poly
    (allocationCoefficient allocationDegree Ck C D : ℕ)
    (hD : D ≤ 40) (hC : C ≤ allocationCoefficient) :
    (3 ^ D * C) ^ 2 <
      2 ^ (3 * (forestProgramsScratchDegree allocationCoefficient allocationDegree Ck + 1)) := by
  set deg := forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
  have hclog : Nat.clog 2 C ≤
      Nat.clog 2 (forestSpaceCoeff allocationCoefficient * 8 ^ forestSpaceDeg allocationDegree) := by
    apply Nat.clog_mono_right
    have h1 : C ≤ forestSpaceCoeff allocationCoefficient := hC.trans (le_max_left _ _)
    have h2 : 1 ≤ 8 ^ forestSpaceDeg allocationDegree := Nat.one_le_pow _ _ (by decide)
    exact h1.trans (Nat.le_mul_of_pos_right _ h2)
  have hdegLo : 10 * Nat.clog 2 C + 2400 ≤ deg := by
    dsimp only [deg, forestProgramsScratchDegree, forestScratchDegree]
    omega
  have hexp : 160 + 2 * Nat.clog 2 C < 3 * (deg + 1) := by omega
  have hCpow : C ≤ 2 ^ Nat.clog 2 C := Nat.le_pow_clog (by decide) C
  have h3D : 3 ^ D ≤ 2 ^ 80 := by
    calc 3 ^ D ≤ 3 ^ 40 := Nat.pow_le_pow_right (by decide) hD
      _ ≤ 4 ^ 40 := Nat.pow_le_pow_left (by decide) 40
      _ = 2 ^ 80 := by norm_num
  calc (3 ^ D * C) ^ 2
      ≤ (2 ^ 80 * 2 ^ Nat.clog 2 C) ^ 2 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul h3D hCpow) 2
    _ = 2 ^ (160 + 2 * Nat.clog 2 C) := by
        rw [Nat.mul_pow, ← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
    _ < 2 ^ (3 * (deg + 1)) := Nat.pow_lt_pow_right (by decide) hexp

/-- **Word-size discharge for the sparse-core initialization condition.**
For every witness `W`, `wordExp ≤ 39` (in particular `wordExp = 24`, degree `25 ≤ 40`), and
`limbMul : ℕ`, there is a constant `C_sw` depending only on `W`, `wordExp`, and `limbMul` such
that whenever `C_sw ≤ allocationCoefficient`, at the final solver word size `w` with `hw`:
`(levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ wordExp * (L + 1) < 2 ^ w`
for every level `i` and every limb count `L ≤ limbMul * bundleLogFactor (levelM i) cfg.N₀`. -/
theorem concrete_sparseCoreWordBound_lt_two_pow_wordSize
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    (wordExp : ℕ) (hwordExp : wordExp ≤ 39) (limbMul : ℕ) :
    ∃ C_sw : ℕ, ∀ (allocationCoefficient allocationDegree : ℕ),
      C_sw ≤ allocationCoefficient →
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let threshold := concreteEdgeThresholdWithLast W
        let A := concreteQualityBudgetWithLast W
        let Ck := concreteQualityLinearCoeff threshold A
        let deg := forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent threshold A I.m
        let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
        let cfg := concreteCirculationCfgWithLast W J
        ipmQualityParameterWordBits I.m V k ≤ w →
        ∀ (i L : ℕ),
          L ≤ limbMul * bundleLogFactor (levelM cfg.TP cfg.P i) cfg.N₀ →
          (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ wordExp * (L + 1) < 2 ^ w := by
  obtain ⟨C_poly, hpoly⟩ := concrete_sparseCoreWordBound_poly W wordExp limbMul
  refine ⟨C_poly, fun allocCoeff allocDeg hle source J hJn hJm hCap hw i L hL => ?_⟩
  set threshold := concreteEdgeThresholdWithLast W
  set A := concreteQualityBudgetWithLast W
  set Ck := concreteQualityLinearCoeff threshold A
  have hdeg := forestProgramsScratchDegree_covers_poly allocCoeff allocDeg Ck C_poly (wordExp + 1)
    (by omega) hle
  exact lt_two_pow_wordSize_of_poly_and_hw source J hJm (by omega : wordExp + 1 ≤ 40) hw
    (hpoly J hJn hJm hCap i L hL) hdeg

/-- Specialization of `concrete_sparseCoreWordBound_lt_two_pow_wordSize` at `wordExp = 24`
(the value of `asmTopWordExp` at `capExp = 3`, using degree `25 ≤ 40`). -/
theorem concrete_sparseCoreWordBound_lt_two_pow_wordSize_deg25
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) :
    ∃ C_sw : ℕ, ∀ (allocationCoefficient allocationDegree : ℕ),
      C_sw ≤ allocationCoefficient →
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let threshold := concreteEdgeThresholdWithLast W
        let A := concreteQualityBudgetWithLast W
        let Ck := concreteQualityLinearCoeff threshold A
        let deg := forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent threshold A I.m
        let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
        let cfg := concreteCirculationCfgWithLast W J
        ipmQualityParameterWordBits I.m V k ≤ w →
        ∀ (i L : ℕ),
          L ≤ concreteReadout2LimbMul W * bundleLogFactor (levelM cfg.TP cfg.P i) cfg.N₀ →
          (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ 24 * (L + 1) < 2 ^ w :=
  concrete_sparseCoreWordBound_lt_two_pow_wordSize W 24 (by decide) (concreteReadout2LimbMul W)

/-- **Uniform word-size discharge for every `wordExp ≤ 39` with one witness-only constant.**
Uses `wordExp = 39` (degree `40 ≤ 40`) with `limbMul = concreteReadout2LimbMul W`, so a single
`allocationCoefficient` floor `C_sw` depending only on `W` discharges
`(levelM i + cfg.N₀ + 2) ^ wordExp * (L + 1) < 2 ^ w` for every `wordExp ≤ 39` and every
`L ≤ concreteReadout2LimbMul W * bundleLogFactor (levelM i) cfg.N₀` (covering both uniform
`ipmQualityLimbs I.m V k` and per-level readout-`2` schedules with constant `128`). -/
theorem concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) :
    ∃ C_sw : ℕ, ∀ (allocationCoefficient allocationDegree : ℕ),
      C_sw ≤ allocationCoefficient →
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let threshold := concreteEdgeThresholdWithLast W
        let A := concreteQualityBudgetWithLast W
        let Ck := concreteQualityLinearCoeff threshold A
        let deg := forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent threshold A I.m
        let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
        let cfg := concreteCirculationCfgWithLast W J
        ipmQualityParameterWordBits I.m V k ≤ w →
        ∀ (wordExp : ℕ), wordExp ≤ 39 →
        ∀ (i L : ℕ),
          L ≤ concreteReadout2LimbMul W * bundleLogFactor (levelM cfg.TP cfg.P i) cfg.N₀ →
          (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ wordExp * (L + 1) < 2 ^ w := by
  obtain ⟨C_sw, hCsw⟩ :=
    concrete_sparseCoreWordBound_lt_two_pow_wordSize W 39 (by decide) (concreteReadout2LimbMul W)
  refine ⟨C_sw, fun allocCoeff allocDeg hle source J hJn hJm hCap hw wordExp hwe i L hL => ?_⟩
  have h39 := hCsw allocCoeff allocDeg hle source J hJn hJm hCap hw i L hL
  have hbase : 1 ≤ levelM (concreteCirculationCfgWithLast W J).TP
      (concreteCirculationCfgWithLast W J).P i + (concreteCirculationCfgWithLast W J).N₀ + 2 := by
    omega
  have hpow : (levelM (concreteCirculationCfgWithLast W J).TP
      (concreteCirculationCfgWithLast W J).P i + (concreteCirculationCfgWithLast W J).N₀ + 2) ^ wordExp ≤
      (levelM (concreteCirculationCfgWithLast W J).TP
      (concreteCirculationCfgWithLast W J).P i + (concreteCirculationCfgWithLast W J).N₀ + 2) ^ 39 :=
    Nat.pow_le_pow_right hbase hwe
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hpow) h39

end MinCostFlow.MinRatio
