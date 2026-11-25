module

public import MinCostFlow.Statement.Main
public import MinCostFlow.NarrowProg.Stage0Defs
public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Narrow.OuterWork
public import MinCostFlow.Scaling.SolverContract
public import MinCostFlow.Final.ForestConcretePrograms
public import MinCostFlow.Final.ForestConcreteSolverRate
public import MinCostFlow.Final.TimeExponent
import MinCostFlow.Narrow.OuterCirculation
import MinCostFlow.Scaling.VertexCompression
import Mathlib.Tactic.Ring

/-!
# Time bound for the narrow-word top theorem

Connects the explicit cost shape of `stage1Mod_meets` (`stage1CostShape`) and the outer cost of
`narrowMain` (`narrowTotalCostBound`) with any monotone host-width solver time `T_sol` bounded by
`A * linkedForestSolverTime P.runtimeResources (2 * m) m + B * (m + 1)`.

Using the bundle's solver rate bound (`DyadicWithVConcretePrograms.linkedSolverTime_le`), the
logarithmic round/phase bounds, `narrow_cost_le_timeBound` (`MinCostFlow/Narrow/OuterWork.lean`),
and `scalingTimeExponent_tendsto` (`MinCostFlow/Final/TimeExponent.lean`), proves:
- `narrowTimeExponent_tendsto`: `Tendsto (narrowTimeExponent P A B a0 a1) atTop (𝓝 0)`, and
- `narrowCost_le_timeBound`: `(cost : ℝ) ≤ timeBound (narrowTimeConstant A B a0 a1) (narrowTimeExponent P A B a0 a1) I`.
-/

@[expose] public section

open Filter Topology WordRAM MinCostFlow.Scaling MinCostFlow.Scaling.Machine MinCostFlow.Narrow
  MinCostFlow.NarrowProg MinCostFlow.Final MinCostFlow.Chain

namespace MinCostFlow.NarrowTop

/-! ### Stage 1 cost shape, monotone envelope, and outer total cost bound -/

/-- Exact cost shape proved by `stage1Mod_meets` (`MinCostFlow/NarrowProg/Stage1Mod.lean:190`). -/
def stage1CostShape (T_sol : ℕ → ℕ → ℕ) (K : Circulation) (k : ℕ) : ℕ :=
  let C := K.compress
  let R := narrowCostRounds C
  let T_U := bitScalingPhases K
  let L := costScaleBits K
  R * (T_U * T_sol (C.n + 1) (4 * K.m) + T_sol (C.n + 2) (8 * K.m + 2 * C.n) +
        T_U * K.m + K.m * (T_U / k + 1) + T_U + C.n + 1) +
    K.m * (T_U / k + L / k + 1) + T_U + L + 1

/-- Monotone upper envelope on `stage1CostShape T_sol K k` depending only on
`(K.m, circMaxCapacity K, circMaxCost K)`. -/
def narrowStage1CostEnvelope (T_sol : ℕ → ℕ → ℕ) (m U_cap C_cost : ℕ) : ℕ :=
  let R := Nat.size C_cost + Nat.clog 2 ((2 * m) ^ 8) + 1 + Nat.size (2 * m + 1)
  let T_U := Nat.size U_cap
  let L := Nat.size C_cost
  R * ((T_U + 1) * T_sol (2 * m + 2) (12 * m) + (2 * m + 1) * (T_U + 1) + 2 * m + 1) +
    m * (T_U + L + 1) + T_U + L + 1

/-- Total outer cost bound of `narrowMain`, parameterized by:
- `T_sol`: the host-width bounded solver's time function,
- `a0`: the constant factor of `narrowMain`'s overhead outside `stage1Circ`,
- `a1`: the constant factor of `stage1Circ` from `stage1Mod_meets`. -/
def narrowTotalCostBound (T_sol : ℕ → ℕ → ℕ) (a0 a1 : ℕ) (I : Instance) : ℕ :=
  a0 * (I.n + I.m * (narrowMaxCapLimbs I + narrowMaxCostLimbs I + 1) + 1) +
    a1 * (narrowStage1CostEnvelope T_sol (3 * I.m)
            (FlowReduction.scalingCapacityBudget I I.maxCapacity) 1 +
          narrowStage1CostEnvelope T_sol (2 * I.m)
            (2 * I.maxCapacity) I.maxCost)

/-- Leading constant `K` in `timeBound K ε I`. -/
def narrowTimeConstant (A B a0 a1 : ℕ) : ℕ :=
  a0 + 2 + 2 * a1 * (84 * A + 3024 * B + 1020)

/-- Vanishing exponent `ε : ℕ → ℝ` in `timeBound K ε I`. -/
noncomputable def narrowTimeExponent (P : DyadicWithVConcretePrograms) (A B a0 a1 : ℕ) : ℕ → ℝ :=
  scalingTimeExponent
    (max 1 (narrowTimeConstant A B a0 a1 : ℝ) * narrowScalingLogCoefficient *
      (P.solverRateCoefficient + 1))
    (12 * P.rateExponent + 2 / (Real.log 2) ^ (47 / 48 : ℝ))

/-! ### Monotonicity and Stage 1 envelope comparison -/

/-- `narrowStage1CostEnvelope T_sol` is monotone in edge count, max capacity, and max cost
whenever `T_sol` is monotone. -/
theorem narrowStage1CostEnvelope_mono {T_sol : ℕ → ℕ → ℕ} (hmono : SolverTimeMonotone T_sol)
    {m m' U U' C C' : ℕ} (hm : m ≤ m') (hU : U ≤ U') (hC : C ≤ C') :
    narrowStage1CostEnvelope T_sol m U C ≤ narrowStage1CostEnvelope T_sol m' U' C' := by
  unfold narrowStage1CostEnvelope
  dsimp only
  have hL : Nat.size C ≤ Nat.size C' := Nat.size_le_size hC
  have hT : Nat.size U ≤ Nat.size U' := Nat.size_le_size hU
  have hp : Nat.clog 2 ((2 * m) ^ 8) ≤ Nat.clog 2 ((2 * m') ^ 8) :=
    Nat.clog_mono_right 2 (Nat.pow_le_pow_left (by omega) 8)
  have hn : Nat.size (2 * m + 1) ≤ Nat.size (2 * m' + 1) := Nat.size_le_size (by omega)
  have hR : Nat.size C + Nat.clog 2 ((2 * m) ^ 8) + 1 + Nat.size (2 * m + 1) ≤
      Nat.size C' + Nat.clog 2 ((2 * m') ^ 8) + 1 + Nat.size (2 * m' + 1) := by omega
  have hsol : T_sol (2 * m + 2) (12 * m) ≤ T_sol (2 * m' + 2) (12 * m') :=
    hmono _ _ _ _ (by omega) (by omega)
  have ht1 : (Nat.size U + 1) * T_sol (2 * m + 2) (12 * m) ≤
      (Nat.size U' + 1) * T_sol (2 * m' + 2) (12 * m') :=
    Nat.mul_le_mul (by omega) hsol
  have ht2 : (2 * m + 1) * (Nat.size U + 1) ≤ (2 * m' + 1) * (Nat.size U' + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hbody : (Nat.size U + 1) * T_sol (2 * m + 2) (12 * m) +
        (2 * m + 1) * (Nat.size U + 1) + 2 * m + 1 ≤
      (Nat.size U' + 1) * T_sol (2 * m' + 2) (12 * m') +
        (2 * m' + 1) * (Nat.size U' + 1) + 2 * m' + 1 := by omega
  have hprod := Nat.mul_le_mul hR hbody
  have hinit : m * (Nat.size U + Nat.size C + 1) ≤ m' * (Nat.size U' + Nat.size C' + 1) :=
    Nat.mul_le_mul hm (by omega)
  omega

/-- The `stage1Mod_meets` cost shape is bounded by `narrowStage1CostEnvelope`. -/
theorem stage1CostShape_le_envelope {T_sol : ℕ → ℕ → ℕ} (hmono : SolverTimeMonotone T_sol)
    (K : Circulation) (k : ℕ) :
    stage1CostShape T_sol K k ≤
      narrowStage1CostEnvelope T_sol K.m (circMaxCapacity K) (circMaxCost K) := by
  unfold stage1CostShape narrowStage1CostEnvelope
  dsimp only
  have hCn : K.compress.n ≤ 2 * K.m := K.endpointLabels_count_le
  have hR : narrowCostRounds K.compress ≤
      Nat.size (circMaxCost K) + Nat.clog 2 ((2 * K.m) ^ 8) + 1 + Nat.size (2 * K.m + 1) := by
    unfold narrowCostRounds costScaleBits costPrecisionExp
    have hcost_eq : circMaxCost K.compress = circMaxCost K := rfl
    have hm_eq : K.compress.m = K.m := rfl
    have hns : Nat.size (K.compress.n + 1) ≤ Nat.size (2 * K.m + 1) := Nat.size_le_size (by omega)
    rw [hcost_eq, hm_eq]
    omega
  have hT_eq : bitScalingPhases K = Nat.size (circMaxCapacity K) := rfl
  have hL_eq : costScaleBits K = Nat.size (circMaxCost K) := rfl
  have hsol1 : T_sol (K.compress.n + 1) (4 * K.m) ≤ T_sol (2 * K.m + 2) (12 * K.m) :=
    hmono _ _ _ _ (by omega) (by omega)
  have hsol2 : T_sol (K.compress.n + 2) (8 * K.m + 2 * K.compress.n) ≤
      T_sol (2 * K.m + 2) (12 * K.m) :=
    hmono _ _ _ _ (by omega) (by omega)
  have hsol_sum : bitScalingPhases K * T_sol (K.compress.n + 1) (4 * K.m) +
        T_sol (K.compress.n + 2) (8 * K.m + 2 * K.compress.n) ≤
      (bitScalingPhases K + 1) * T_sol (2 * K.m + 2) (12 * K.m) := by
    have h1 := Nat.mul_le_mul_left (bitScalingPhases K) hsol1
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hdivT : bitScalingPhases K / k ≤ bitScalingPhases K := Nat.div_le_self _ _
  have hdivL : costScaleBits K / k ≤ costScaleBits K := Nat.div_le_self _ _
  have hnon_sol : bitScalingPhases K * K.m + K.m * (bitScalingPhases K / k + 1) +
        bitScalingPhases K + K.compress.n + 1 ≤
      (2 * K.m + 1) * (bitScalingPhases K + 1) + 2 * K.m + 1 := by
    have h1 : K.m * (bitScalingPhases K / k + 1) ≤ K.m * (bitScalingPhases K + 1) :=
      Nat.mul_le_mul_left K.m (by omega)
    have heq : (2 * K.m + 1) * (bitScalingPhases K + 1) =
        bitScalingPhases K * K.m + K.m * (bitScalingPhases K + 1) + K.m + bitScalingPhases K + 1 := by
      ring
    omega
  have hbody : bitScalingPhases K * T_sol (K.compress.n + 1) (4 * K.m) +
        T_sol (K.compress.n + 2) (8 * K.m + 2 * K.compress.n) +
        bitScalingPhases K * K.m + K.m * (bitScalingPhases K / k + 1) +
        bitScalingPhases K + K.compress.n + 1 ≤
      (Nat.size (circMaxCapacity K) + 1) * T_sol (2 * K.m + 2) (12 * K.m) +
        (2 * K.m + 1) * (Nat.size (circMaxCapacity K) + 1) + 2 * K.m + 1 := by
    rw [← hT_eq]; omega
  have hprod := Nat.mul_le_mul hR hbody
  have hinit : K.m * (bitScalingPhases K / k + costScaleBits K / k + 1) ≤
      K.m * (Nat.size (circMaxCapacity K) + Nat.size (circMaxCost K) + 1) := by
    rw [← hT_eq, ← hL_eq]
    exact Nat.mul_le_mul_left K.m (by omega)
  have hCn_eq : K.compress.n = K.endpointLabels.count := rfl
  rw [hCn_eq] at hprod
  rw [← hT_eq, ← hL_eq] at hprod hinit ⊢
  omega

/-! ### Logarithmic and solver-rate helpers -/

private lemma round_env_le (m C : ℕ) :
    Nat.size (max C 1) + Nat.clog 2 ((2 * (3 * m)) ^ 8) + 1 + Nat.size (2 * (3 * m) + 1) ≤
      28 * (Nat.clog 2 (C + 2) + Nat.clog 2 (m + 1) + 1) := by
  have hL : Nat.size (max C 1) ≤ Nat.clog 2 (C + 2) :=
    le_trans (size_le_clog_succ (max C 1)) (Nat.clog_mono_right 2 (by omega))
  have hpow := Nat.le_pow_clog (by decide : 1 < 2) (m + 1)
  have hp : Nat.clog 2 ((2 * (3 * m)) ^ 8) ≤ 24 + 8 * Nat.clog 2 (m + 1) := by
    apply Nat.clog_le_of_le_pow
    calc (2 * (3 * m)) ^ 8
        ≤ (8 * (m + 1)) ^ 8 := Nat.pow_le_pow_left (by omega) 8
      _ ≤ (8 * 2 ^ Nat.clog 2 (m + 1)) ^ 8 :=
          Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 hpow) 8
      _ = 2 ^ (24 + 8 * Nat.clog 2 (m + 1)) := by
          rw [Nat.mul_pow, Nat.pow_add, ← Nat.pow_mul, Nat.mul_comm 8]
  have hn : Nat.size (2 * (3 * m) + 1) ≤ 3 + Nat.clog 2 (m + 1) := by
    apply Nat.size_le.mpr
    calc 2 * (3 * m) + 1
        < 8 * (m + 1) := by omega
      _ ≤ 8 * 2 ^ Nat.clog 2 (m + 1) := Nat.mul_le_mul_left 8 hpow
      _ = 2 ^ (3 + Nat.clog 2 (m + 1)) := by rw [Nat.pow_add]
  omega

private lemma phase_env_le (I : Instance) :
    Nat.size (FlowReduction.scalingCapacityBudget I I.maxCapacity) + 1 ≤
      3 * (Nat.clog 2 (I.maxCapacity + 1) + Nat.clog 2 (I.m + 1) + 1) := by
  have hm := Nat.le_pow_clog (by decide : 1 < 2) (I.m + 1)
  have hu := Nat.le_pow_clog (by decide : 1 < 2) (I.maxCapacity + 1)
  have h1 := size_le_clog_succ (FlowReduction.scalingCapacityBudget I I.maxCapacity)
  have h2 : Nat.clog 2 (FlowReduction.scalingCapacityBudget I I.maxCapacity + 1) ≤
      2 + Nat.clog 2 (I.m + 1) + Nat.clog 2 (I.maxCapacity + 1) := by
    apply Nat.clog_le_of_le_pow
    have hsmall : FlowReduction.scalingCapacityBudget I I.maxCapacity + 1 ≤
        4 * ((I.m + 1) * (I.maxCapacity + 1)) := by
      unfold FlowReduction.scalingCapacityBudget
      have he : 4 * ((I.m + 1) * (I.maxCapacity + 1)) =
          4 * ((I.m + 1) * I.maxCapacity) + 4 * (I.m + 1) := by ring
      have hmul : 2 * (I.m + 1) * I.maxCapacity = 2 * ((I.m + 1) * I.maxCapacity) := by ring
      omega
    calc FlowReduction.scalingCapacityBudget I I.maxCapacity + 1
        ≤ 4 * ((I.m + 1) * (I.maxCapacity + 1)) := hsmall
      _ ≤ 4 * (2 ^ Nat.clog 2 (I.m + 1) * 2 ^ Nat.clog 2 (I.maxCapacity + 1)) :=
          Nat.mul_le_mul_left 4 (Nat.mul_le_mul hm hu)
      _ = 2 ^ (2 + Nat.clog 2 (I.m + 1) + Nat.clog 2 (I.maxCapacity + 1)) := by
          rw [Nat.pow_add, Nat.pow_add]; ring
  omega

private lemma timeConstant_ge_72 (P : DyadicWithVConcretePrograms) : 72 ≤ P.timeConstant :=
  P.toCore.timeConstant_ge_72

private lemma envelope_bound (P : DyadicWithVConcretePrograms)
    {T_sol : ℕ → ℕ → ℕ} {A B : ℕ}
    (hle : ∀ n m, T_sol n m ≤ A * linkedForestSolverTime P.runtimeResources (2 * m) m + B * (m + 1))
    (I : Instance) :
    narrowStage1CostEnvelope T_sol (3 * I.m)
        (FlowReduction.scalingCapacityBudget I I.maxCapacity) (max I.maxCost 1) ≤
      (84 * A + 3024 * B + 1020) * narrowOuterLogFactor I.m I.maxCost I.maxCapacity *
        (linkedForestSolverTime P.runtimeResources (72 * I.m) (36 * I.m) + I.m + 1) := by
  set m := I.m
  set U := I.maxCapacity
  set C := I.maxCost
  set U1 := FlowReduction.scalingCapacityBudget I U
  set Lfac := narrowOuterLogFactor m C U
  set Sval := linkedForestSolverTime P.runtimeResources (72 * m) (36 * m)
  set Renv := Nat.size (max C 1) + Nat.clog 2 ((2 * (3 * m)) ^ 8) + 1 + Nat.size (2 * (3 * m) + 1)
  set Tenv := Nat.size U1
  set Lenv := Nat.size (max C 1)
  have hR : Renv ≤ 28 * (Nat.clog 2 (C + 2) + Nat.clog 2 (m + 1) + 1) := round_env_le m C
  have hT : Tenv + 1 ≤ 3 * (Nat.clog 2 (U + 1) + Nat.clog 2 (m + 1) + 1) := phase_env_le I
  have hL : Lenv ≤ Nat.clog 2 (C + 2) :=
    le_trans (size_le_clog_succ (max C 1)) (Nat.clog_mono_right 2 (by omega))
  have hRT : Renv * (Tenv + 1) ≤ 84 * Lfac := by
    have hmul := Nat.mul_le_mul hR hT
    have heq : 28 * (Nat.clog 2 (C + 2) + Nat.clog 2 (m + 1) + 1) *
        (3 * (Nat.clog 2 (U + 1) + Nat.clog 2 (m + 1) + 1)) = 84 * Lfac := by
      dsimp only [Lfac, narrowOuterLogFactor]; ring
    omega
  have hsol : T_sol (2 * (3 * m) + 2) (12 * (3 * m)) ≤ A * Sval + 36 * B * (m + 1) := by
    have h0 := hle (2 * (3 * m) + 2) (12 * (3 * m))
    have hS_eq : linkedForestSolverTime P.runtimeResources (2 * (12 * (3 * m))) (12 * (3 * m)) =
        Sval := by
      dsimp only [Sval]; congr 1 <;> omega
    rw [hS_eq] at h0
    have hB : B * (12 * (3 * m) + 1) ≤ 36 * B * (m + 1) := by
      have : 36 * B * (m + 1) = B * (36 * m + 36) := by ring
      rw [this]; exact Nat.mul_le_mul_left B (by omega)
    omega
  have hterm1 : Renv * ((Tenv + 1) * T_sol (2 * (3 * m) + 2) (12 * (3 * m))) ≤
      84 * A * Lfac * Sval + 3024 * B * Lfac * (m + 1) := by
    rw [← Nat.mul_assoc]
    have h1 := Nat.mul_le_mul hRT hsol
    have heq : 84 * Lfac * (A * Sval + 36 * B * (m + 1)) =
        84 * A * Lfac * Sval + 3024 * B * Lfac * (m + 1) := by ring
    omega
  have hterm2 : Renv * ((2 * (3 * m) + 1) * (Tenv + 1) + 2 * (3 * m) + 1) ≤
      1008 * Lfac * (m + 1) := by
    have hlin : (2 * (3 * m) + 1) * (Tenv + 1) + 2 * (3 * m) + 1 ≤
        (Tenv + 1) * (12 * (m + 1)) := by
      have h1 : (2 * (3 * m) + 1) * (Tenv + 1) + 2 * (3 * m) + 1 =
          (6 * m + 1) * (Tenv + 2) := by ring
      have h2 : (6 * m + 1) * (Tenv + 2) ≤ (6 * (m + 1)) * (2 * (Tenv + 1)) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h3 : (6 * (m + 1)) * (2 * (Tenv + 1)) = (Tenv + 1) * (12 * (m + 1)) := by ring
      omega
    calc Renv * ((2 * (3 * m) + 1) * (Tenv + 1) + 2 * (3 * m) + 1)
        ≤ Renv * ((Tenv + 1) * (12 * (m + 1))) := Nat.mul_le_mul_left Renv hlin
      _ = (Renv * (Tenv + 1)) * (12 * (m + 1)) := (Nat.mul_assoc _ _ _).symm
      _ ≤ (84 * Lfac) * (12 * (m + 1)) := Nat.mul_le_mul_right _ hRT
      _ = 1008 * Lfac * (m + 1) := by ring
  have hterm3 : (3 * m) * (Tenv + Lenv + 1) + Tenv + Lenv + 1 ≤ 12 * Lfac * (m + 1) := by
    have hT_Lfac : Tenv + 1 ≤ 3 * Lfac := by
      have hge1 : 1 ≤ Nat.clog 2 (C + 2) + Nat.clog 2 (m + 1) + 1 := by omega
      have hmul := Nat.mul_le_mul_left (Nat.clog 2 (U + 1) + Nat.clog 2 (m + 1) + 1) hge1
      rw [Nat.mul_one] at hmul
      have hLfac_def : Lfac = (Nat.clog 2 (U + 1) + Nat.clog 2 (m + 1) + 1) *
          (Nat.clog 2 (C + 2) + Nat.clog 2 (m + 1) + 1) := rfl
      omega
    have hL_Lfac : Lenv ≤ Lfac := by
      have hge1 : 1 ≤ Nat.clog 2 (U + 1) + Nat.clog 2 (m + 1) + 1 := by omega
      have hmul := Nat.mul_le_mul_right (Nat.clog 2 (C + 2) + Nat.clog 2 (m + 1) + 1) hge1
      rw [Nat.one_mul] at hmul
      have hLfac_def : Lfac = (Nat.clog 2 (U + 1) + Nat.clog 2 (m + 1) + 1) *
          (Nat.clog 2 (C + 2) + Nat.clog 2 (m + 1) + 1) := rfl
      omega
    have heq : (3 * m) * (Tenv + Lenv + 1) + Tenv + Lenv + 1 =
        (3 * m + 1) * (Tenv + 1 + Lenv) := by ring
    have hmul := Nat.mul_le_mul (show 3 * m + 1 ≤ 3 * (m + 1) by omega)
      (show Tenv + 1 + Lenv ≤ 4 * Lfac by omega)
    have heq2 : 3 * (m + 1) * (4 * Lfac) = 12 * Lfac * (m + 1) := by ring
    omega
  have hcombine : (84 * A * Lfac * Sval + 3024 * B * Lfac * (m + 1)) +
        1008 * Lfac * (m + 1) + 12 * Lfac * (m + 1) ≤
      (84 * A + 3024 * B + 1020) * Lfac * (Sval + m + 1) := by
    have heq : (84 * A + 3024 * B + 1020) * Lfac * (Sval + m + 1) =
        84 * A * Lfac * Sval + (3024 * B + 1020) * Lfac * (m + 1) +
        84 * A * Lfac * (m + 1) + (3024 * B + 1020) * Lfac * Sval := by ring
    have heq2 : (84 * A * Lfac * Sval + 3024 * B * Lfac * (m + 1)) +
        1008 * Lfac * (m + 1) + 12 * Lfac * (m + 1) =
        84 * A * Lfac * Sval + (3024 * B + 1020) * Lfac * (m + 1) := by ring
    omega
  unfold narrowStage1CostEnvelope
  dsimp only
  change Renv * ((Tenv + 1) * T_sol (2 * (3 * m) + 2) (12 * (3 * m)) +
      (2 * (3 * m) + 1) * (Tenv + 1) + 2 * (3 * m) + 1) +
      (3 * m) * (Tenv + Lenv + 1) + Tenv + Lenv + 1 ≤ _
  have hsplit : Renv * ((Tenv + 1) * T_sol (2 * (3 * m) + 2) (12 * (3 * m)) +
      (2 * (3 * m) + 1) * (Tenv + 1) + 2 * (3 * m) + 1) =
      Renv * ((Tenv + 1) * T_sol (2 * (3 * m) + 2) (12 * (3 * m))) +
      Renv * ((2 * (3 * m) + 1) * (Tenv + 1) + 2 * (3 * m) + 1) := by ring
  omega

/-! ### Main time-bound theorems -/

/-- The vanishing exponent `narrowTimeExponent P A B a0 a1` tends to `0` as `m → ∞`. -/
theorem narrowTimeExponent_tendsto (P : DyadicWithVConcretePrograms) (A B a0 a1 : ℕ) :
    Tendsto (narrowTimeExponent P A B a0 a1) atTop (𝓝 0) := by
  apply scalingTimeExponent_tendsto
  have h1 : (0 : ℝ) ≤ 12 * P.rateExponent := mul_nonneg (by norm_num) P.rateExponent_nonneg
  have h2 : (0 : ℝ) ≤ 2 / (Real.log 2) ^ (47 / 48 : ℝ) :=
    div_nonneg (by norm_num) (Real.rpow_nonneg (Real.log_pos (by norm_num)).le _)
  linarith

/-- Any run cost bounded by `narrowTotalCostBound T_sol a0 a1 I + 2` satisfies the Theorem 1.1
time bound `timeBound (narrowTimeConstant A B a0 a1) (narrowTimeExponent P A B a0 a1) I`. -/
theorem narrowCost_le_timeBound (P : DyadicWithVConcretePrograms)
    {T_sol : ℕ → ℕ → ℕ} {A B : ℕ}
    (hmono : SolverTimeMonotone T_sol)
    (hle : ∀ n m, T_sol n m ≤ A * linkedForestSolverTime P.runtimeResources (2 * m) m + B * (m + 1))
    (a0 a1 : ℕ) (I : Instance) (cost : ℕ)
    (hcost : cost ≤ narrowTotalCostBound T_sol a0 a1 I + 2) :
    (cost : ℝ) ≤ timeBound (narrowTimeConstant A B a0 a1) (narrowTimeExponent P A B a0 a1) I := by
  set K := narrowTimeConstant A B a0 a1
  set Sval := linkedForestSolverTime P.runtimeResources (72 * I.m) (36 * I.m)
  set Lfac := narrowOuterLogFactor I.m I.maxCost I.maxCapacity
  have hcall1 : narrowStage1CostEnvelope T_sol (3 * I.m)
      (FlowReduction.scalingCapacityBudget I I.maxCapacity) 1 ≤
      narrowStage1CostEnvelope T_sol (3 * I.m)
        (FlowReduction.scalingCapacityBudget I I.maxCapacity) (max I.maxCost 1) :=
    narrowStage1CostEnvelope_mono hmono le_rfl le_rfl (le_max_right _ _)
  have hcall2 : narrowStage1CostEnvelope T_sol (2 * I.m) (2 * I.maxCapacity) I.maxCost ≤
      narrowStage1CostEnvelope T_sol (3 * I.m)
        (FlowReduction.scalingCapacityBudget I I.maxCapacity) (max I.maxCost 1) := by
    refine narrowStage1CostEnvelope_mono hmono (by omega) ?_ (le_max_left _ _)
    unfold FlowReduction.scalingCapacityBudget
    have hmul : 2 * I.maxCapacity ≤ 2 * (I.m + 1) * I.maxCapacity := by
      have := Nat.mul_le_mul_right I.maxCapacity (show 2 ≤ 2 * (I.m + 1) by omega)
      exact this
    omega
  have henv : narrowStage1CostEnvelope T_sol (3 * I.m)
        (FlowReduction.scalingCapacityBudget I I.maxCapacity) (max I.maxCost 1) ≤
      (84 * A + 3024 * B + 1020) * Lfac * (Sval + I.m + 1) := envelope_bound P hle I
  have hcalls : a1 * (narrowStage1CostEnvelope T_sol (3 * I.m)
        (FlowReduction.scalingCapacityBudget I I.maxCapacity) 1 +
      narrowStage1CostEnvelope T_sol (2 * I.m) (2 * I.maxCapacity) I.maxCost) ≤
      2 * a1 * (84 * A + 3024 * B + 1020) * Lfac * (Sval + I.m + 1) := by
    have hsum : narrowStage1CostEnvelope T_sol (3 * I.m)
          (FlowReduction.scalingCapacityBudget I I.maxCapacity) 1 +
        narrowStage1CostEnvelope T_sol (2 * I.m) (2 * I.maxCapacity) I.maxCost ≤
        2 * ((84 * A + 3024 * B + 1020) * Lfac * (Sval + I.m + 1)) := by omega
    have hmul := Nat.mul_le_mul_left a1 hsum
    have heq : a1 * (2 * ((84 * A + 3024 * B + 1020) * Lfac * (Sval + I.m + 1))) =
        2 * a1 * (84 * A + 3024 * B + 1020) * Lfac * (Sval + I.m + 1) := by ring
    omega
  have hoverhead : a0 * (I.n + I.m * (narrowMaxCapLimbs I + narrowMaxCostLimbs I + 1) + 1) + 2 ≤
      (a0 + 2) * Lfac * (Sval + I.m + 1) + (a0 + 2) * I.n := by
    have hk1 := one_le_narrowLimbWidth I
    have hLU : narrowMaxCapLimbs I ≤ Nat.clog 2 (I.maxCapacity + 1) := digits_length_le_clog hk1
    have hLC : narrowMaxCostLimbs I ≤ Nat.clog 2 (I.maxCost + 2) :=
      le_trans (digits_length_le_clog hk1) (Nat.clog_mono_right 2 (by omega))
    have hLfac_ge : Nat.clog 2 (I.maxCapacity + 1) + Nat.clog 2 (I.maxCost + 2) + 1 ≤ Lfac := by
      dsimp only [Lfac, narrowOuterLogFactor]
      have heq : (Nat.clog 2 (I.maxCapacity + 1) + Nat.clog 2 (I.m + 1) + 1) *
          (Nat.clog 2 (I.maxCost + 2) + Nat.clog 2 (I.m + 1) + 1) =
          (Nat.clog 2 (I.maxCapacity + 1) + Nat.clog 2 (I.maxCost + 2) + 1) +
          (Nat.clog 2 (I.maxCapacity + 1) * Nat.clog 2 (I.maxCost + 2) +
           Nat.clog 2 (I.maxCapacity + 1) * Nat.clog 2 (I.m + 1) +
           Nat.clog 2 (I.m + 1) * Nat.clog 2 (I.maxCost + 2) +
           Nat.clog 2 (I.m + 1) * Nat.clog 2 (I.m + 1) + 2 * Nat.clog 2 (I.m + 1)) := by ring
      omega
    have h1_Lfac : 1 ≤ Lfac := by omega
    have hpart : I.m * (narrowMaxCapLimbs I + narrowMaxCostLimbs I + 1) + 1 ≤
        Lfac * (Sval + I.m + 1) := by
      have h1 : I.m * (narrowMaxCapLimbs I + narrowMaxCostLimbs I + 1) ≤ I.m * Lfac :=
        Nat.mul_le_mul_left I.m (by omega)
      have h2 : I.m * Lfac + 1 ≤ Lfac * (I.m + 1) := by
        have : Lfac * (I.m + 1) = I.m * Lfac + Lfac := by ring
        omega
      have h3 : Lfac * (I.m + 1) ≤ Lfac * (Sval + I.m + 1) :=
        Nat.mul_le_mul_left Lfac (by omega)
      omega
    have h2_le : 2 ≤ 2 * (Lfac * (Sval + I.m + 1)) := by
      have : 1 ≤ Lfac * (Sval + I.m + 1) := Nat.mul_pos h1_Lfac (by omega)
      omega
    have hmul0 := Nat.mul_le_mul_left a0 hpart
    have heq1 : a0 * (I.n + I.m * (narrowMaxCapLimbs I + narrowMaxCostLimbs I + 1) + 1) =
        a0 * I.n + a0 * (I.m * (narrowMaxCapLimbs I + narrowMaxCostLimbs I + 1) + 1) := by ring
    have heq2 : (a0 + 2) * Lfac * (Sval + I.m + 1) + (a0 + 2) * I.n =
        a0 * I.n + 2 * I.n + a0 * (Lfac * (Sval + I.m + 1)) +
        2 * (Lfac * (Sval + I.m + 1)) := by ring
    omega
  have hcost_tot : cost ≤ K * Lfac * (Sval + I.m + 1) + K * I.n := by
    unfold narrowTotalCostBound at hcost
    have hK_eq : K * Lfac * (Sval + I.m + 1) + K * I.n =
        ((a0 + 2) * Lfac * (Sval + I.m + 1) + (a0 + 2) * I.n) +
        2 * a1 * (84 * A + 3024 * B + 1020) * Lfac * (Sval + I.m + 1) +
        2 * a1 * (84 * A + 3024 * B + 1020) * I.n := by
      dsimp only [K, narrowTimeConstant]; ring
    omega
  have htc : 72 ≤ P.timeConstant := timeConstant_ge_72 P
  have hSval : (Sval : ℝ) ≤ P.solverRateCoefficient * ((I.m : ℝ) + 2) *
      alg2TimeFactor (12 * P.rateExponent) (47 / 48) I.m :=
    P.linkedSolverTime_le I.m (72 * I.m) (36 * I.m)
      (Nat.mul_le_mul_right I.m htc) (Nat.mul_le_mul_right I.m (by omega))
  have hfinal_pos : 0 < max 1 (K : ℝ) * narrowScalingLogCoefficient * (P.solverRateCoefficient + 1) :=
    mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) narrowScalingLogCoefficient_pos)
      (by linarith [P.solverRateCoefficient_pos])
  exact narrow_cost_le_timeBound K Sval cost P.solverRateCoefficient P.rateExponent
    (max 1 (K : ℝ) * narrowScalingLogCoefficient * (P.solverRateCoefficient + 1)) I
    P.rateExponent_nonneg P.solverRateCoefficient_pos rfl hfinal_pos hSval hcost_tot

end MinCostFlow.NarrowTop
