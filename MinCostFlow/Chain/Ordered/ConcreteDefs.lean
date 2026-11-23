module

public import MinCostFlow.Chain.Ordered.Algorithm2
public import MinCostFlow.Chain.ConcreteDefs
public import MinCostFlow.Chain.BundleRestartMach
public import MinCostFlow.SparseCore.BundleMachParams
public import MinCostFlow.SparseCore.LastLevel
public import MinCostFlow.Expander.Section8Params

/-!
# Concrete Definitions for the Ordered Bundle Chain

Defines the degree-free `concreteEnv`, `concreteAlg2CfgWithLast`, and `concreteAlg2Cfg` in
`MinCostFlow.Chain.Ordered`. The core tool is the bundle tool with the machine cost,
`sparseCoreBundleRestartToolMachWith lsfInit` (`Chain/BundleRestartMach.lean`), for any LSF
initializer `lsfInit`, and its parameters are `bundleCoreParamsMach`
(`SparseCore/BundleMachParams.lean`). There is no `D_cap` parameter as in
`Chain/ConcreteDefs.lean`.

The MWU bound `σ_mwu` is `concreteSigmaMWUMach`, with constant `30 · mwuK0 C_lsst`. This is the
constant `3 K_ρ K₀` of `sparseCoreBundleRestartToolMachWith_toolMWUOrdRestart` for the online
initializer (`K_ρ = 10`, `K₀ = mwuK0 C_lsst`), and any initializer whose constants fit
`C_lsst` meets it (`Chain/Ordered/ConcreteLSFInit.lean`).

Pure numeric definitions and real-analysis helpers that do not depend on `D_cap` or on ordered
objects (`concreteChainParams`, `concreteSigmaMWU`, `concreteBCap`, `concreteBucketCapacity`,
`sparsifySpec_mono_mMax`, etc.) are reused directly from `MinCostFlow.Chain`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.Expander MinCostFlow.Bundle

section ConcreteDefs

/-- Explicit `σ_mwu` for the concrete chain on any fitting LSF initializer, with
`μ = ⌈log(M₀^2 + 2) / log 3⌉ + 1` so that `m + 2 ≤ (n + 2)^μ` holds for every valid graph with
`m ≤ M₀^2` (`concrete_m_poly_of_le_sq`). -/
noncomputable def concreteSigmaMWUMach (C_lsst : ℝ) (M₀ n : ℕ) : ℝ :=
  let μ := Nat.ceil (Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) / Real.log 3) + 1
  (μ : ℝ) * (30 * mwuK0 C_lsst) * (Real.log ((n : ℝ) + 2)) ^ 7

lemma concreteSigmaMWUMach_nonneg (C_lsst : ℝ) (M₀ n : ℕ) :
    0 ≤ concreteSigmaMWUMach C_lsst M₀ n := by
  unfold concreteSigmaMWUMach
  have hK := mwuK0_pos C_lsst
  have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := by linarith [half_lt_log_add_two n]
  positivity

lemma concreteSigmaMWUMach_mono (C_lsst : ℝ) (M₀ : ℕ) :
    ∀ n₁ n₂, n₁ ≤ n₂ → concreteSigmaMWUMach C_lsst M₀ n₁ ≤ concreteSigmaMWUMach C_lsst M₀ n₂ := by
  intro n₁ n₂ hn
  dsimp only [concreteSigmaMWUMach]
  have hK := mwuK0_pos C_lsst
  have hlog1 : 0 ≤ Real.log ((n₁ : ℝ) + 2) := by linarith [half_lt_log_add_two n₁]
  have hlog_le : Real.log ((n₁ : ℝ) + 2) ≤ Real.log ((n₂ : ℝ) + 2) := by
    refine Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) n₁]) ?_
    have : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hn
    linarith
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog1 hlog_le 7) (by positivity)

/-- Degree-free concrete `SparseCoreEnv` at edge bound `M₀`, bucket cap `max 1 B_cap`, depth
`L = chosenL (M₀ ^ 2)`, constant `P_fn := fun _ => params (M₀ ^ 2)`, and `c_n = 1`. The
`d_fn` field is set to `0` and never read by `bundleCoreParams`. -/
noncomputable def concreteEnv (C_lsst : ℝ) (params : ℕ → DynSpanner.SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (M₀ B_cap : ℕ) : SparseCoreEnv where
  C_lsst := C_lsst
  L := chosenL (M₀ ^ 2)
  hL := one_le_chosenL (M₀ ^ 2)
  P_fn := fun _ => monoSparsifyParamsEnvelope params (M₀ ^ 2)
  hMono := monoSparsifyParams_const (monoSparsifyParamsEnvelope params (M₀ ^ 2))
  p_s_hi := 1
  p_t_hi := 1
  hp_s := fun _ => monoSparsifyParamsEnvelope_p_s_le params hp_s (M₀ ^ 2)
  hp_t := fun _ => monoSparsifyParamsEnvelope_p_t_le params hp_t (M₀ ^ 2)
  B_fn := fun _ => max 1 B_cap
  hB_pos := fun _ => le_max_left 1 B_cap
  hB_mono := fun _ _ _ => le_rfl
  d_fn := fun _ => 0
  hd_mono := fun _ _ _ => le_rfl
  c_n := 1
  hc_n := le_rfl

/-- Concrete `Alg2Config` assembling `sparseCoreBundleRestartToolMachWith lsfInit`, an arbitrary
`lastTool : LastLevelTool` at `LP := lastLevelParams C_last`, `bundleCoreParamsMachWith`, and
`concreteChainParams`, with no degree cap `D_cap`. -/
noncomputable def concreteAlg2CfgWithLast
    (lsfInit : LSFInit) (C_lsst : ℝ)
    (lastTool : LastLevelTool) (C_last : ℝ)
    (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (M₀ N₀ B_cap : ℕ) (hM₀ : 1 ≤ M₀) (α Ψ ε : ℝ) (spanConst : ℕ := 1) : Alg2Config where
  T := sparseCoreBundleRestartToolMachWith lsfInit C_lsst (chosenL (M₀ ^ 2)) (fun _ => sparsify)
    params spanConst
  L := lastTool
  TP := bundleCoreParamsMachWith (concreteEnv C_lsst params hp_s hp_t M₀ B_cap) spanConst
  LP := lastLevelParams C_last
  P := concreteChainParams M₀ hM₀
  σ_mwu := concreteSigmaMWUMach C_lsst M₀
  N₀ := N₀
  α := α
  Ψ := Ψ
  ε := ε

/-- Concrete `Alg2Config` assembling `sparseCoreBundleRestartToolMachWith lsfInit`,
`lastLevelTool oracle C_lsst`, `bundleCoreParamsMachWith`, and `lastLevelParams C_lsst`, with no
degree cap `D_cap`. The oracle is used only by the last level. -/
noncomputable def concreteAlg2Cfg (lsfInit : LSFInit)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (M₀ N₀ B_cap : ℕ) (hM₀ : 1 ≤ M₀) (α Ψ ε : ℝ) (spanConst : ℕ := 1) : Alg2Config :=
  concreteAlg2CfgWithLast lsfInit C_lsst (lastLevelTool oracle C_lsst) C_lsst
    sparsify params hp_s hp_t M₀ N₀ B_cap hM₀ α Ψ ε spanConst

end ConcreteDefs

end MinCostFlow.Chain.Ordered
