module

public import MinCostFlow.MinRatio.OrdSolverCapBounds
public import MinCostFlow.Chain.Theorem5_1Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Quadratic per-level cap and limb bounds (`SparseCoreCapHyp`, `WireCapFactsSplit`)

`MinRatio/OrdSolverCapBounds.lean` proved that the old linear limb bound
`L ≤ capExp * (Nat.log 2 (M + N + 2) + 1)` is false on concrete circulations
(`not_sparseCoreCapHyp_limbs`), while the true bound on the level-`0` solver limb count is
quadratic in the log (`concrete_ipmQualityLimbs_le_bundleLogFactor`, matching
`SparseCore.bundleLogFactor M N = (Nat.log 2 (M + N + 2) + 1) ^ 2`).

Under the split sparse-core cap hypothesis
`SparseCoreCapHyp capExp limbMul L M N vCap eCap`
(`vCap + eCap + 2 ≤ (M + N + 2) ^ capExp ∧ L ≤ limbMul * bundleLogFactor M N`),
the capacity exponent stays fixed at `capExp = 3` (even `2` suffices for `N₀ = 4 M₀`), while
`limbMul` absorbs the quadratic limb count and per-level readout-`2` limb growth
`L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)`
with `sparseCoreReadout2LimbConst = 128`.

Proves:
- `sparseCoreCapHyp_mono`, `WireCapFactsSplit`, and the compatibility predicates
  `SparseCoreCapHypQuad`, `WireCapFactsPerLevel`, `WireCapFactsQuad`.
- `chosenD_le_three_log`: `chosenD (23 / 24) M₀ ≤ 3 * (Nat.log 2 (M₀ + 2) + 1)`.
- `levelM_log_le_three_mul`: under `cfg.ValidOrdNoHidden` and `cfg.N₀ = 4 * cfg.P.M₀`,
  `Nat.log 2 (levelM cfg.TP cfg.P j + cfg.N₀ + 2) + 1 ≤ 3 * (Nat.log 2 (levelM cfg.TP cfg.P i + cfg.N₀ + 2) + 1)`
  for all levels `j, i`.
- `concrete_sparseCoreCapHyp_perLevel`: for every witness `W` and step-growth constant `stepExp`,
  there is a limb multiplier `limbMul ≥ 3` (depending only on `W` and `stepExp`) satisfying
  `SparseCoreCapHyp 3 limbMul (L_lvl i) (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap` at every level
  `i ≤ d` and every `vCap + eCap + 2 ≤ 12 * cfg.P.M₀ + 4`.
- `concreteReadout2LimbMul`: canonical limb multiplier for `capExp = 3` and readout-`2` step
  constant `3 + sparseCoreReadout2LimbConst` (`= 131`), together with
  `concrete_sparseCoreCapHyp_readout2` (per-level readout-`2` schedules),
  `concrete_sparseCoreCapHyp_uniform` (uniform `ipmQualityLimbs`),
  `concrete_sparseCoreCapHyp_uniform_bridge`, and `concrete_reached_wireCapFactsSplit`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Final

/-- Updated sparse-core capacity and quadratic limb condition:
`vCap + eCap + 2 ≤ (M + N + 2) ^ capExp` and `L ≤ capExp * bundleLogFactor M N`. -/
@[expose] def SparseCoreCapHypQuad (capExp L M N vCap eCap : ℕ) : Prop :=
  vCap + eCap + 2 ≤ (M + N + 2) ^ capExp ∧ L ≤ capExp * bundleLogFactor M N

/-- Per-level quadratic cap and limb facts for every sparse-core level `i < d` of `model.chain`
with level-`i` limb count `L_lvl i` and capacity limit `capLimit`. -/
@[expose] def WireCapFactsPerLevel {cfg : Alg2Config} (capExp : ℕ) (L_lvl : ℕ → ℕ)
    (capLimit : ℕ) (model : Alg2State cfg) : Prop :=
  ∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ capLimit →
    SparseCoreCapHypQuad capExp (L_lvl i) (model.chain.lvlM i) model.chain.N₀ vCap eCap

/-- Uniform-limb specialization of `WireCapFactsPerLevel`. -/
@[expose] def WireCapFactsQuad {cfg : Alg2Config} (capExp L capLimit : ℕ)
    (model : Alg2State cfg) : Prop :=
  WireCapFactsPerLevel capExp (fun _ => L) capLimit model

/-- `WireCapFactsPerLevel` depends on `model` only through `lvlM` and `N₀`. -/
theorem WireCapFactsPerLevel.congr {cfg : Alg2Config} {capExp capLimit : ℕ} {L_lvl : ℕ → ℕ}
    {model model' : Alg2State cfg} (h : WireCapFactsPerLevel capExp L_lvl capLimit model)
    (hM : ∀ i < cfg.P.d, model'.chain.lvlM i = model.chain.lvlM i)
    (hN : model'.chain.N₀ = model.chain.N₀) :
    WireCapFactsPerLevel capExp L_lvl capLimit model' := by
  intro i hi vCap eCap hcap
  rw [hM i hi, hN]
  exact h i hi vCap eCap hcap

/-- The chain depth `chosenD (23 / 24) M₀` is at most `3 * (Nat.log 2 (M₀ + 2) + 1)`. -/
theorem chosenD_le_three_log {M₀ : ℕ} (hM : 1 ≤ M₀) :
    chosenD (23 / 24) M₀ ≤ 3 * (Nat.log 2 (M₀ + 2) + 1) := by
  have hL1 : 1 ≤ Real.log ((M₀ : ℝ) + 2) := by
    have hexp : Real.exp 1 ≤ (M₀ : ℝ) + 2 := by
      have : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM
      linarith [Real.exp_one_lt_d9]
    exact (Real.le_log_iff_exp_le (by positivity)).mpr hexp
  obtain ⟨_, _, hdHi⟩ := chosenD_bounds (β := 23 / 24) (by norm_num) hM
  rw [show ((1 : ℝ) - 23 / 24) / 2 = 1 / 48 by norm_num] at hdHi
  have hrpow : Real.log ((M₀ : ℝ) + 2) ^ (1 / 48 : ℝ) ≤ Real.log ((M₀ : ℝ) + 2) := by
    calc Real.log ((M₀ : ℝ) + 2) ^ (1 / 48 : ℝ)
        ≤ Real.log ((M₀ : ℝ) + 2) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = Real.log ((M₀ : ℝ) + 2) := Real.rpow_one _
  have hltPow : ((M₀ + 2 : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 (M₀ + 2) + 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide) (M₀ + 2)).le
  push_cast at hltPow
  have hlogLe : Real.log ((M₀ : ℝ) + 2) ≤ ((Nat.log 2 (M₀ + 2) + 1 : ℕ) : ℝ) := by
    have h1 := Real.log_le_log (by positivity) hltPow
    rw [Real.log_pow] at h1
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hnn : (0 : ℝ) ≤ ((Nat.log 2 (M₀ + 2) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast at h1 ⊢
    nlinarith
  have hreal : (chosenD (23 / 24) M₀ : ℝ) ≤ ((3 * (Nat.log 2 (M₀ + 2) + 1) : ℕ) : ℝ) := by
    push_cast at hlogLe ⊢
    linarith
  exact_mod_cast hreal

/-- Under `cfg.ValidOrdNoHidden` and `cfg.N₀ = 4 * cfg.P.M₀`, every level's log factor
`Nat.log 2 (levelM cfg.TP cfg.P j + cfg.N₀ + 2) + 1` is within a factor `3` of any other level's. -/
theorem levelM_log_le_three_mul {cfg : Alg2Config}
    (hV : cfg.ValidOrdNoHidden) (hN₀ : cfg.N₀ = 4 * cfg.P.M₀) (j i : ℕ) :
    Nat.log 2 (levelM cfg.TP cfg.P j + cfg.N₀ + 2) + 1 ≤
      3 * (Nat.log 2 (levelM cfg.TP cfg.P i + cfg.N₀ + 2) + 1) := by
  have hjSq : levelM cfg.TP cfg.P j ≤ cfg.P.M₀ ^ 2 :=
    levelM_le_sq hV.hTP hV.hγM₀ hV.hγk j
  have hsum : levelM cfg.TP cfg.P j + cfg.N₀ + 2 ≤ (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ 2 := by
    have h1 : cfg.P.M₀ ^ 2 + 4 * cfg.P.M₀ + 2 ≤ (4 * cfg.P.M₀ + 2) ^ 2 := by nlinarith
    have h2 : (4 * cfg.P.M₀ + 2) ^ 2 ≤ (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    omega
  set A := levelM cfg.TP cfg.P i + cfg.N₀ + 2
  have hApos : 0 < A := by omega
  have hAltp : A < 2 ^ (Nat.log 2 A + 1) := Nat.lt_pow_succ_log_self (by decide) A
  have hlt : levelM cfg.TP cfg.P j + cfg.N₀ + 2 < 2 ^ (2 * (Nat.log 2 A + 1)) := by
    calc levelM cfg.TP cfg.P j + cfg.N₀ + 2
        ≤ A ^ 2 := hsum
      _ < (2 ^ (Nat.log 2 A + 1)) ^ 2 := Nat.pow_lt_pow_left hAltp (by decide)
      _ = 2 ^ (2 * (Nat.log 2 A + 1)) := by rw [← pow_mul, mul_comm]
  have hlogLt : Nat.log 2 (levelM cfg.TP cfg.P j + cfg.N₀ + 2) < 2 * (Nat.log 2 A + 1) :=
    (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr hlt
  omega

/-- Inductive bound for a per-level limb schedule `L_lvl` growing by at most
`stepExp * (Nat.log 2 (lvlM j + N₀ + 2) + 1)` at each level `j → j + 1`. -/
theorem perLevel_limbs_le_of_step {d L₀ stepExp N₀ : ℕ} {lvlM L_lvl : ℕ → ℕ}
    (h0 : L_lvl 0 ≤ L₀)
    (hstep : ∀ j < d, L_lvl (j + 1) ≤ L_lvl j + stepExp * (Nat.log 2 (lvlM j + N₀ + 2) + 1))
    {i B : ℕ} (hi : i ≤ d)
    (hlog : ∀ j < d, Nat.log 2 (lvlM j + N₀ + 2) + 1 ≤ 3 * B)
    (hd : d ≤ 3 * B) :
    L_lvl i ≤ L₀ + 9 * stepExp * B ^ 2 := by
  have hrec : ∀ n ≤ d, L_lvl n ≤ L₀ + n * (3 * stepExp * B) := by
    intro n
    induction n with
    | zero => intro _; simpa using h0
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := hstep n (by omega)
      have h3 := hlog n (by omega)
      have h4 : stepExp * (Nat.log 2 (lvlM n + N₀ + 2) + 1) ≤ 3 * stepExp * B := by
        calc stepExp * (Nat.log 2 (lvlM n + N₀ + 2) + 1)
            ≤ stepExp * (3 * B) := Nat.mul_le_mul_left stepExp h3
          _ = 3 * stepExp * B := by ring
      calc L_lvl (n + 1)
          ≤ L_lvl n + stepExp * (Nat.log 2 (lvlM n + N₀ + 2) + 1) := h2
        _ ≤ (L₀ + n * (3 * stepExp * B)) + (3 * stepExp * B) := Nat.add_le_add h1 h4
        _ = L₀ + (n + 1) * (3 * stepExp * B) := by ring
  calc L_lvl i
      ≤ L₀ + i * (3 * stepExp * B) := hrec i hi
    _ ≤ L₀ + (3 * B) * (3 * stepExp * B) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (hi.trans hd)) L₀
    _ = L₀ + 9 * stepExp * B ^ 2 := by ring

/-- **Per-level quadratic cap and limb facts for every level `i < d`.**
For every chain witness `W` and per-level limb growth constant `stepExp`, there is a constant
`capExp` (depending only on `W` and `stepExp`) such that on every valid circulation `J`, for
every per-level limb schedule `L_lvl` starting at `≤ ipmQualityLimbs I.m V k` and growing by
at most `stepExp * (Nat.log 2 (levelM j + N₀ + 2) + 1)` per level, `SparseCoreCapHypQuad capExp
(L_lvl i) (levelM i) N₀ vCap eCap` holds at every level `i < d` and every
`vCap + eCap + 2 ≤ 12 * M₀ + 4`. -/
theorem concrete_sparseCoreCapHypQuad_perLevel
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    (stepExp : ℕ) :
    ∃ capExp : ℕ, 2 ≤ capExp ∧
      ∀ (J : Circulation),
        J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let threshold := concreteEdgeThresholdWithLast W
        let A := concreteQualityBudgetWithLast W
        let k := cappedQualityExponent threshold A I.m
        let cfg := concreteCirculationCfgWithLast W J
        ∀ (L_lvl : ℕ → ℕ),
          L_lvl 0 ≤ ipmQualityLimbs I.m V k →
          (∀ j < cfg.P.d,
            L_lvl (j + 1) ≤ L_lvl j + stepExp * (Nat.log 2 (levelM cfg.TP cfg.P j + cfg.N₀ + 2) + 1)) →
          ∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ 12 * cfg.P.M₀ + 4 →
            SparseCoreCapHypQuad capExp (L_lvl i) (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap := by
  obtain ⟨C_L, hCL⟩ := concrete_ipmQualityLimbs_le_bundleLogFactor W
  refine ⟨max 2 (C_L + 9 * stepExp), le_max_left _ _, fun J hJn hJm hCap => ?_⟩
  dsimp only
  intro L_lvl hL0 hLstep i hi vCap eCap hcap
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let k := cappedQualityExponent threshold A I.m
  let cfg := concreteCirculationCfgWithLast W J
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm hCap
  have hN₀ : cfg.N₀ = 4 * cfg.P.M₀ := rfl
  have hdEq : cfg.P.d = chosenD (23 / 24) cfg.P.M₀ := rfl
  refine ⟨?_, ?_⟩
  · have hsq : vCap + eCap + 2 ≤ (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ 2 := by
      have h1 : 12 * cfg.P.M₀ + 4 ≤ (4 * cfg.P.M₀ + 2) ^ 2 := by nlinarith
      have h2 : (4 * cfg.P.M₀ + 2) ^ 2 ≤ (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      exact hcap.trans (h1.trans h2)
    have hbasePos : 1 ≤ levelM cfg.TP cfg.P i + cfg.N₀ + 2 := by omega
    exact hsq.trans (Nat.pow_le_pow_right hbasePos (le_max_left 2 _))
  · set B := Nat.log 2 (levelM cfg.TP cfg.P i + cfg.N₀ + 2) + 1
    have hdLe : cfg.P.d ≤ 3 * B := by
      rw [hdEq]
      refine (chosenD_le_three_log cfg.P.hM₀).trans ?_
      exact Nat.mul_le_mul_left 3 (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1)
    have hlogAll : ∀ j < cfg.P.d, Nat.log 2 (levelM cfg.TP cfg.P j + cfg.N₀ + 2) + 1 ≤ 3 * B :=
      fun j _ => levelM_log_le_three_mul hVcfg hN₀ j i
    have hLstep' := perLevel_limbs_le_of_step hL0 hLstep hi.le hlogAll hdLe
    have hL0B : ipmQualityLimbs I.m V k ≤ C_L * B ^ 2 := hCL J hJn hJm hCap i
    have hsum : L_lvl i ≤ (C_L + 9 * stepExp) * B ^ 2 := by
      calc L_lvl i ≤ ipmQualityLimbs I.m V k + 9 * stepExp * B ^ 2 := hLstep'
        _ ≤ C_L * B ^ 2 + 9 * stepExp * B ^ 2 := Nat.add_le_add_right hL0B _
        _ = (C_L + 9 * stepExp) * B ^ 2 := by ring
    exact hsum.trans (Nat.mul_le_mul_right _ (le_max_right 2 _))

/-- Uniform-limb specialization of `concrete_sparseCoreCapHypQuad_perLevel` (all levels at
`ipmQualityLimbs I.m V k`). -/
theorem concrete_sparseCoreCapHypQuad_uniform
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) :
    ∃ capExp : ℕ, 2 ≤ capExp ∧
      ∀ (J : Circulation),
        J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let threshold := concreteEdgeThresholdWithLast W
        let A := concreteQualityBudgetWithLast W
        let k := cappedQualityExponent threshold A I.m
        let cfg := concreteCirculationCfgWithLast W J
        ∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ 12 * cfg.P.M₀ + 4 →
          SparseCoreCapHypQuad capExp (ipmQualityLimbs I.m V k)
            (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap := by
  obtain ⟨capExp, h2, h⟩ := concrete_sparseCoreCapHypQuad_perLevel W 0
  exact ⟨capExp, h2, fun J hJn hJm hCap i hi vCap eCap hcap =>
    h J hJn hJm hCap (fun _ => _) le_rfl (fun _ _ => by omega) i hi vCap eCap hcap⟩

/-- Reached-state corollary: for every state `model` satisfying `OrdSolverReached`, `model.chain`
keeps `lvlM = levelM cfg.TP cfg.P` and `N₀ = cfg.N₀`, so `WireCapFactsPerLevel` holds on `model`
for every per-level limb schedule with growth constant `stepExp`. -/
theorem concrete_reached_wireCapFactsPerLevel
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    (stepExp : ℕ) :
    ∃ capExp : ℕ, 2 ≤ capExp ∧
      ∀ (J : Circulation),
        J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let threshold := concreteEdgeThresholdWithLast W
        let A := concreteQualityBudgetWithLast W
        let k := cappedQualityExponent threshold A I.m
        let cfg := concreteCirculationCfgWithLast W J
        ∀ (model : Alg2State cfg) (L_lvl : ℕ → ℕ),
          OrdSolverReached cfg (1 / (2 : ℝ) ^ k) (namedInstance I) model →
          L_lvl 0 ≤ ipmQualityLimbs I.m V k →
          (∀ j < cfg.P.d,
            L_lvl (j + 1) ≤ L_lvl j + stepExp * (Nat.log 2 (levelM cfg.TP cfg.P j + cfg.N₀ + 2) + 1)) →
          WireCapFactsPerLevel capExp L_lvl (12 * cfg.P.M₀ + 4) model := by
  obtain ⟨capExp, h2, hcap⟩ := concrete_sparseCoreCapHypQuad_perLevel W stepExp
  refine ⟨capExp, h2, fun J hJn hJm hCap => ?_⟩
  dsimp only
  intro model L_lvl hreach hL0 hLstep
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let k := cappedQualityExponent threshold A I.m
  let cfg := concreteCirculationCfgWithLast W J
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm hCap
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of (le_max_left W.M_thresh _)
    (le_max_right W.M_thresh _) (concreteEdgeThresholdWithLast_ge_two W) J hJn hJm hCap
  have hmG : (namedInstance I).m ≤ cfg.P.M₀ := by rw [namedInstance_m]; exact le_max_left _ _
  have hnG : (namedInstance I).n ≤ cfg.N₀ := by
    have : (namedInstance I).n = I.n := by simp [namedInstance, MGraph.n]
    rw [this]; exact hIn
  obtain ⟨D, η, op, T, hHist, hE, hL, hG, hm⟩ := hreach
  have hInv := ((Ordered.algorithm2_uncond_preserves_with (η := η) (1 / (2 : ℝ) ^ k) hVcfg hHist
    hE hL (fun t ht => by rw [hG t ht]; exact hmG)
    (fun t ht => by rw [hG t ht]; exact hnG)).1 T le_rfl).1
  rw [← hm] at hInv
  intro i hi vCap eCap hlim
  rw [hInv.hLvlM, hInv.hN0]
  exact hcap J hJn hJm hCap L_lvl hL0 hLstep i hi vCap eCap hlim

/-! ## Split `(capExp = 3, limbMul)` bounds for `SparseCore.Program.SparseCoreCapHyp` -/

/-- Monotonicity of `SparseCoreCapHyp` in both `capExp` and `limbMul`. -/
theorem sparseCoreCapHyp_mono {c₁ c₂ m₁ m₂ L M N vCap eCap : ℕ}
    (hc : c₁ ≤ c₂) (hm : m₁ ≤ m₂)
    (h : SparseCoreCapHyp c₁ m₁ L M N vCap eCap) :
    SparseCoreCapHyp c₂ m₂ L M N vCap eCap :=
  ⟨h.1.trans (Nat.pow_le_pow_right (by omega) hc), h.2.trans (Nat.mul_le_mul_right _ hm)⟩

/-- Split per-level cap and limb facts for `SparseCoreCapHyp capExp limbMul` at every level
`i < cfg.P.d` of `model.chain`. -/
@[expose] def WireCapFactsSplit {cfg : Alg2Config} (capExp limbMul : ℕ) (L_lvl : ℕ → ℕ)
    (capLimit : ℕ) (model : Alg2State cfg) : Prop :=
  ∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ capLimit →
    SparseCoreCapHyp capExp limbMul (L_lvl i) (model.chain.lvlM i) model.chain.N₀ vCap eCap

/-- `WireCapFactsSplit` depends on `model` only through `lvlM` and `N₀`. -/
theorem WireCapFactsSplit.congr {cfg : Alg2Config} {capExp limbMul capLimit : ℕ}
    {L_lvl : ℕ → ℕ} {model model' : Alg2State cfg}
    (h : WireCapFactsSplit capExp limbMul L_lvl capLimit model)
    (hM : ∀ i < cfg.P.d, model'.chain.lvlM i = model.chain.lvlM i)
    (hN : model'.chain.N₀ = model.chain.N₀) :
    WireCapFactsSplit capExp limbMul L_lvl capLimit model' := by
  intro i hi vCap eCap hcap
  rw [hM i hi, hN]
  exact h i hi vCap eCap hcap

/-- **Split per-level cap and limb facts with `capExp = 3`.**
For every chain witness `W` and per-level limb growth constant `stepExp`, there is a limb
multiplier `limbMul ≥ 3` (depending only on `W` and `stepExp`, built from
`concrete_ipmQualityLimbs_le_bundleLogFactor`) such that on every valid circulation `J`, for
every per-level limb schedule `L_lvl` starting at `≤ ipmQualityLimbs I.m V k` and growing by
at most `stepExp * (Nat.log 2 (levelM j + N₀ + 2) + 1)` per level,
`SparseCoreCapHyp 3 limbMul (L_lvl i) (levelM i) N₀ vCap eCap` holds at every level `i ≤ d`
and every `vCap + eCap + 2 ≤ 12 * M₀ + 4`. -/
theorem concrete_sparseCoreCapHyp_perLevel
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    (stepExp : ℕ) :
    ∃ limbMul : ℕ, 3 ≤ limbMul ∧
      ∀ (J : Circulation),
        J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let threshold := concreteEdgeThresholdWithLast W
        let A := concreteQualityBudgetWithLast W
        let k := cappedQualityExponent threshold A I.m
        let cfg := concreteCirculationCfgWithLast W J
        ∀ (L_lvl : ℕ → ℕ),
          L_lvl 0 ≤ ipmQualityLimbs I.m V k →
          (∀ j < cfg.P.d,
            L_lvl (j + 1) ≤ L_lvl j + stepExp * (Nat.log 2 (levelM cfg.TP cfg.P j + cfg.N₀ + 2) + 1)) →
          ∀ i ≤ cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ 12 * cfg.P.M₀ + 4 →
            SparseCoreCapHyp 3 limbMul (L_lvl i) (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap := by
  obtain ⟨C_L, hCL⟩ := concrete_ipmQualityLimbs_le_bundleLogFactor W
  refine ⟨max 3 (C_L + 9 * stepExp), le_max_left _ _, fun J hJn hJm hCap => ?_⟩
  dsimp only
  intro L_lvl hL0 hLstep i hi vCap eCap hcap
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let k := cappedQualityExponent threshold A I.m
  let cfg := concreteCirculationCfgWithLast W J
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm hCap
  have hN₀ : cfg.N₀ = 4 * cfg.P.M₀ := rfl
  have hdEq : cfg.P.d = chosenD (23 / 24) cfg.P.M₀ := rfl
  refine ⟨?_, ?_⟩
  · have hsq : vCap + eCap + 2 ≤ (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ 2 := by
      have h1 : 12 * cfg.P.M₀ + 4 ≤ (4 * cfg.P.M₀ + 2) ^ 2 := by nlinarith
      have h2 : (4 * cfg.P.M₀ + 2) ^ 2 ≤ (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      exact hcap.trans (h1.trans h2)
    have hbasePos : 1 ≤ levelM cfg.TP cfg.P i + cfg.N₀ + 2 := by omega
    exact hsq.trans (Nat.pow_le_pow_right hbasePos (by decide : 2 ≤ 3))
  · set B := Nat.log 2 (levelM cfg.TP cfg.P i + cfg.N₀ + 2) + 1
    have hdLe : cfg.P.d ≤ 3 * B := by
      rw [hdEq]
      refine (chosenD_le_three_log cfg.P.hM₀).trans ?_
      exact Nat.mul_le_mul_left 3 (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1)
    have hlogAll : ∀ j < cfg.P.d, Nat.log 2 (levelM cfg.TP cfg.P j + cfg.N₀ + 2) + 1 ≤ 3 * B :=
      fun j _ => levelM_log_le_three_mul hVcfg hN₀ j i
    have hLstep' := perLevel_limbs_le_of_step hL0 hLstep hi hlogAll hdLe
    have hL0B : ipmQualityLimbs I.m V k ≤ C_L * B ^ 2 := hCL J hJn hJm hCap i
    have hsum : L_lvl i ≤ (C_L + 9 * stepExp) * B ^ 2 := by
      calc L_lvl i ≤ ipmQualityLimbs I.m V k + 9 * stepExp * B ^ 2 := hLstep'
        _ ≤ C_L * B ^ 2 + 9 * stepExp * B ^ 2 := Nat.add_le_add_right hL0B _
        _ = (C_L + 9 * stepExp) * B ^ 2 := by ring
    exact hsum.trans (Nat.mul_le_mul_right _ (le_max_right 3 _))

/-- Canonical limb multiplier for `capExp = 3` covering both the level-`0` solver limb count
`ipmQualityLimbs I.m V k` (`concrete_ipmQualityLimbs_le_bundleLogFactor`) and every per-level
readout-`2` schedule growing by `(3 + sparseCoreReadout2LimbConst) * (log₂ (M_j + N₀ + 2) + 1)`
at each level `j < d` (with `sparseCoreReadout2LimbConst = 128`). -/
noncomputable def concreteReadout2LimbMul
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) : ℕ :=
  Classical.choose (concrete_sparseCoreCapHyp_perLevel W (3 + sparseCoreReadout2LimbConst))

/-- `3 ≤ concreteReadout2LimbMul W`. -/
theorem three_le_concreteReadout2LimbMul
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) :
    3 ≤ concreteReadout2LimbMul W :=
  (Classical.choose_spec (concrete_sparseCoreCapHyp_perLevel W (3 + sparseCoreReadout2LimbConst))).1

/-- **Per-level readout-`2` cap and limb facts at `capExp = 3` with constant `128`.**
Every per-level limb schedule starting at `≤ ipmQualityLimbs I.m V k` and advancing via readout `2`
(`L_lvl (j + 1) ≤ max (L_lvl j) (L_w j)` with `L_w j ≤ L_lvl j + (3 + 128) * (log₂ (M_j + N₀ + 2) + 1)`)
satisfies `SparseCoreCapHyp 3 (concreteReadout2LimbMul W)` at every level `i ≤ d`. -/
theorem concrete_sparseCoreCapHyp_readout2
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCap : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let threshold := concreteEdgeThresholdWithLast W
    let A := concreteQualityBudgetWithLast W
    let k := cappedQualityExponent threshold A I.m
    let cfg := concreteCirculationCfgWithLast W J
    ∀ (L_lvl : ℕ → ℕ),
      L_lvl 0 ≤ ipmQualityLimbs I.m V k →
      (∀ j < cfg.P.d,
        L_lvl (j + 1) ≤
          L_lvl j + (3 + sparseCoreReadout2LimbConst) *
            (Nat.log 2 (levelM cfg.TP cfg.P j + cfg.N₀ + 2) + 1)) →
      ∀ i ≤ cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ 12 * cfg.P.M₀ + 4 →
        SparseCoreCapHyp 3 (concreteReadout2LimbMul W) (L_lvl i)
          (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap :=
  (Classical.choose_spec (concrete_sparseCoreCapHyp_perLevel W (3 + sparseCoreReadout2LimbConst))).2
    J hJn hJm hCap

/-- **Uniform-limb cap and limb facts at `capExp = 3` and `limbMul = concreteReadout2LimbMul W`.**
Discharges `SparseCoreCapHyp 3 (concreteReadout2LimbMul W) (ipmQualityLimbs I.m V k)` at every
level `i ≤ d` and every `vCap + eCap + 2 ≤ 12 * M₀ + 4`. -/
theorem concrete_sparseCoreCapHyp_uniform
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCap : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let threshold := concreteEdgeThresholdWithLast W
    let A := concreteQualityBudgetWithLast W
    let k := cappedQualityExponent threshold A I.m
    let cfg := concreteCirculationCfgWithLast W J
    ∀ i ≤ cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ 12 * cfg.P.M₀ + 4 →
      SparseCoreCapHyp 3 (concreteReadout2LimbMul W) (ipmQualityLimbs I.m V k)
        (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap := by
  dsimp only
  intro i hi vCap eCap hcap
  exact concrete_sparseCoreCapHyp_readout2 W J hJn hJm hCap (fun _ => _) le_rfl
    (fun _ _ => Nat.le_add_right _ _) i hi vCap eCap hcap

/-- Reached-state corollary for `WireCapFactsSplit 3 (concreteReadout2LimbMul W)`: every state
satisfying `OrdSolverReached` satisfies `SparseCoreCapHyp 3 (concreteReadout2LimbMul W)` at every
sparse-core level `i < d` for any readout-`2` per-level limb schedule. -/
theorem concrete_reached_wireCapFactsSplit
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCap : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let threshold := concreteEdgeThresholdWithLast W
    let A := concreteQualityBudgetWithLast W
    let k := cappedQualityExponent threshold A I.m
    let cfg := concreteCirculationCfgWithLast W J
    ∀ (model : Alg2State cfg) (L_lvl : ℕ → ℕ),
      OrdSolverReached cfg (1 / (2 : ℝ) ^ k) (namedInstance I) model →
      L_lvl 0 ≤ ipmQualityLimbs I.m V k →
      (∀ j < cfg.P.d,
        L_lvl (j + 1) ≤
          L_lvl j + (3 + sparseCoreReadout2LimbConst) *
            (Nat.log 2 (levelM cfg.TP cfg.P j + cfg.N₀ + 2) + 1)) →
      WireCapFactsSplit 3 (concreteReadout2LimbMul W) L_lvl (12 * cfg.P.M₀ + 4) model := by
  dsimp only
  intro model L_lvl hreach hL0 hLstep
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let k := cappedQualityExponent threshold A I.m
  let cfg := concreteCirculationCfgWithLast W J
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm hCap
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of (le_max_left W.M_thresh _)
    (le_max_right W.M_thresh _) (concreteEdgeThresholdWithLast_ge_two W) J hJn hJm hCap
  have hmG : (namedInstance I).m ≤ cfg.P.M₀ := by rw [namedInstance_m]; exact le_max_left _ _
  have hnG : (namedInstance I).n ≤ cfg.N₀ := by
    have : (namedInstance I).n = I.n := by simp [namedInstance, MGraph.n]
    rw [this]; exact hIn
  obtain ⟨D, η, op, T, hHist, hE, hL, hG, hm⟩ := hreach
  have hInv := ((Ordered.algorithm2_uncond_preserves_with (η := η) (1 / (2 : ℝ) ^ k) hVcfg hHist
    hE hL (fun t ht => by rw [hG t ht]; exact hmG)
    (fun t ht => by rw [hG t ht]; exact hnG)).1 T le_rfl).1
  rw [← hm] at hInv
  intro i hi vCap eCap hlim
  rw [hInv.hLvlM, hInv.hN0]
  exact concrete_sparseCoreCapHyp_readout2 W J hJn hJm hCap L_lvl hL0 hLstep i hi.le vCap eCap hlim

end MinCostFlow.MinRatio
