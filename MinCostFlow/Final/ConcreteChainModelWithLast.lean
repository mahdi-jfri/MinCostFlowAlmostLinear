module

public import MinCostFlow.Final.OrderedConcreteChainModel

/-!
# Generalized degree-free ordered concrete chain model for arbitrary `LastLevelTool`

Companion to `MinCostFlow.Final.OrderedConcreteChainModel` unpacking
`Chain.Ordered.concrete_theorem_5_1_with_last_core` for any `lastTool : LastLevelTool`
satisfying `lastTool.IsSpec (lastLevelParams C_last)`, with no degree cap (`C_D` / `D_cap`),
with `ToolEmbedsSurvivingOrdRestart` and `ToolNoReinsertOrdRestart` discharged unconditionally,
and with `MinRatioSpecWithFailureEdgeOnlyConnectedUpTo`. Also defines
`concreteCirculationCfgOfDims` to make explicit that every parameter of
`concreteCirculationCfgWithLast` depends solely on `(I.m, V)` and fixed witness constants.

The core tool is `sparseCoreBundleRestartToolMachWith (lsfInit L_in P_fp)`. The witness holds a
family `lsfInit : ℕ → ℕ → LSFInit` of LSF initializers, one for each number format: `L_in` is the
number of limbs and `P_fp` the precision of the lengths. Every member fits the same constant
`C_lsst` (`IsConcreteLSFInit`). A program can only compute the initializer in the format of its
input, and the solver's format depends on the instance. So the configuration of an instance,
`concreteCirculationCfgOfDims W I_m V`, uses the member at the solver's own format: the limbs and
the precision of `ipmQualityMinRatioFormat I_m V k` (`concreteCirculationCfgWithLast_T`).

The constants `C_γ` and `M_thresh` of the witness are chosen once for the whole family, from
`Chain.Ordered.concrete_theorem_5_1_with_last_core_uniform`. That theorem also gives the fields
`validWith` (the configuration is `ValidOrd`) and `gammaWith` (the rounded rebuild factor
`⌈γ_r(M₀²)⌉` is at most `exp((C_γ + 1) L^{23/24} log(L + 2))`). For the configuration of an
instance they read `concreteCirculationCfgWithLast_validOrd`, `…_validOrdNoHidden` and
`…_gamma_r`. The witness is built by
`concreteChainWitnessWithLastOf` from a given family. `concreteChainWitnessWithLast_nonempty`
passes the constant family of the online initializer `initLSFOnline oracle C_lsst` of
`theorem_2_2`'s oracle.
-/

@[expose] public noncomputable section
namespace MinCostFlow.Final
open Chain IPM IPM.Machine WordRAM Scaling LSF SparseCore

/-- Degree-free witness bundle unpacked from
`Chain.Ordered.concrete_theorem_5_1_with_last_core_uniform` at `C_ψ = 1`, `C_N = 4` for an
arbitrary `lastTool : LastLevelTool` at `lastLevelParams C_last`, with
`ToolEmbedsSurvivingOrdRestart` and `ToolNoReinsertOrdRestart` already discharged. The LSF
initializer is a family indexed by the number format `(L_in, P_fp)` (limbs, precision); the
constants `C_lsst`, `C_γ`, `M_thresh` serve every member. -/
structure ConcreteChainWitnessWithLast
    (lastTool : LastLevelTool) (C_last : ℝ)
    (hLast : lastTool.IsSpec (lastLevelParams C_last)) where
  lsfInit : ℕ → ℕ → LSFInit
  C_lsst : ℝ
  sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut
  params : ℕ → DynSpanner.SparsifyParams
  hp_s : ∀ m, (params m).p_s ≤ 1
  hp_t : ∀ m, (params m).p_t ≤ 1
  spanConst : ℕ
  hspanConst : 1 ≤ spanConst
  C_γ : ℝ
  M_thresh : ℕ
  hInit : ∀ L_in P_fp, Chain.Ordered.IsConcreteLSFInit (lsfInit L_in P_fp) C_lsst
  hsparsify : ∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify
  hCγ : 3 ≤ C_γ
  hM_thresh : 2 ≤ M_thresh
  /-- The configuration of every member and every admissible size is valid (`ValidOrd`, so also
  `ValidOrdNoHidden` by `ValidOrd.toNoHidden`). -/
  validWith : ∀ (L_in P_fp : ℕ) (M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
    M_thresh ≤ M₀ →
    1 + Real.log ((N₀ : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) →
    alg2PsiGame Ψ M₀ ≤ Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
    0 < α →
    let B_cap := concreteBucketCapacity true C_lsst Ψ M₀ N₀ hM₀1
    let cfg := Chain.Ordered.concreteAlg2CfgWithLast (lsfInit L_in P_fp) C_lsst lastTool C_last
      sparsify params hp_s hp_t M₀ N₀ B_cap hM₀1 α Ψ ε spanConst
    cfg.ValidOrd
  /-- The rounded rebuild factor `Γ = ⌈γ_r(M₀²)⌉` of the configuration is at least `1` and at most
  `exp((C_γ + 1) L^{23/24} log(L + 2))` with `L = log(M₀ + 2)`. -/
  gammaWith : ∀ (L_in P_fp : ℕ) (M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
    M_thresh ≤ M₀ →
    1 + Real.log ((N₀ : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) →
    alg2PsiGame Ψ M₀ ≤ Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
    0 < α →
    let B_cap := concreteBucketCapacity true C_lsst Ψ M₀ N₀ hM₀1
    let cfg := Chain.Ordered.concreteAlg2CfgWithLast (lsfInit L_in P_fp) C_lsst lastTool C_last
      sparsify params hp_s hp_t M₀ N₀ B_cap hM₀1 α Ψ ε spanConst
    1 ≤ ⌈cfg.TP.γ_r (cfg.P.M₀ ^ 2)⌉₊ ∧
      (⌈cfg.TP.γ_r (cfg.P.M₀ ^ 2)⌉₊ : ℝ) ≤
        Real.exp ((C_γ + 1) * Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2))
  /-- Theorem 5.1 for the configuration of every member and every admissible size. -/
  specWith : ∀ (L_in P_fp : ℕ) (M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
    M_thresh ≤ M₀ →
    1 + Real.log ((N₀ : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) →
    alg2PsiGame Ψ M₀ ≤ Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
    0 < α →
    let B_cap := concreteBucketCapacity true C_lsst Ψ M₀ N₀ hM₀1
    let cfg := Chain.Ordered.concreteAlg2CfgWithLast (lsfInit L_in P_fp) C_lsst lastTool C_last
      sparsify params hp_s hp_t M₀ N₀ B_cap hM₀1 α Ψ ε spanConst
    let κ_own := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
    let C_κ := 15 + 5 * C_γ
    (0 < κ_own ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ_own) ∧
    ∀ (κ : ℝ), 0 < κ → κ ≤ κ_own →
      ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
        MinRatioHistoryValid D isUpdate T →
        Chain.Ordered.HistoryEdgeOnly D T →
        Chain.Ordered.HistoryLengthsInRange D T Ψ →
        (∀ t ≤ T, (D.G t).m ≤ M₀) →
        (∀ t ≤ T, (D.G t).n ≤ N₀) →
        (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
        let A := Chain.Ordered.algorithm2_dsWithFailureWith cfg κ
        (∀ t ≤ T, ∀ e ∈ (D.G t).E,
          A.query (minRatioState A.eraseFailure D η isUpdate t) e =
            minRatioFlow A.eraseFailure D η isUpdate t e) ∧
        (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
          (D.G (t + 1)).IsCirculation
            (minRatioDirection A.eraseFailure D η isUpdate t) ∧
          (D.HiddenStable (t + 1) α Ψ →
            (minRatioFailureDirection A D η isUpdate t).isSome = true ∧
            (D.G (t + 1)).inner (D.g (t + 1))
                (minRatioDirection A.eraseFailure D η isUpdate t) /
              (D.G (t + 1)).lnorm (D.ℓ (t + 1))
                (minRatioDirection A.eraseFailure D η isUpdate t) ≤ -(κ * α))) ∧
        (∀ t, t + 1 ≤ T → isUpdate (t + 1) = false →
          (A.detect (minRatioState A.eraseFailure D η isUpdate t)).1 =
            minRatioDetectSet A.eraseFailure D η isUpdate ε t)

/-- The witness with given data: the family of LSF initializers `lsfInit` (each member fitting
`C_lsst`), the sparsifier `sparsify` and its parameters `params` are the arguments, by definition
(the `…_lsfInit`/`…_sparsify` lemmas below are `rfl`). Only the constants `C_γ` and `M_thresh`
are chosen, from `Chain.Ordered.concrete_theorem_5_1_with_last_core_uniform`, once for all
members. `ToolEmbedsSurvivingOrdRestart` and `ToolNoReinsertOrdRestart` are discharged via
`Chain.Ordered.RestartSpecOn` for each member. -/
def concreteChainWitnessWithLastOf
    (lastTool : LastLevelTool) (C_last : ℝ)
    (hLast : lastTool.IsSpec (lastLevelParams C_last))
    (lsfInit : ℕ → ℕ → LSFInit) (C_lsst : ℝ)
    (hInit : ∀ L_in P_fp, Chain.Ordered.IsConcreteLSFInit (lsfInit L_in P_fp) C_lsst)
    (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (params : ℕ → DynSpanner.SparsifyParams)
    (C_sp K_s K_t : ℝ) (hCsp : 0 < C_sp) (hKs : 0 ≤ K_s) (hKt : 0 ≤ K_t)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧
      (params m).K_t = K_t ∧ (params m).p_t = 1 ∧
      (params m).γ_ℓ ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params m).γ_c ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    (hsparsify : ∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify)
    (spanConst : ℕ := 1) (hspanConst : 1 ≤ spanConst := by omega) :
    ConcreteChainWitnessWithLast lastTool C_last hLast :=
  have hp_s : ∀ m, (params m).p_s ≤ 1 := fun m => le_of_eq (hp_spec m).2.1
  have hp_t : ∀ m, (params m).p_t ≤ 1 := fun m => le_of_eq (hp_spec m).2.2.2.1
  have hcore := Chain.Ordered.concrete_theorem_5_1_with_last_core_uniform C_lsst lastTool C_last
    hLast sparsify params C_sp K_s K_t hCsp hKs hKt hp_spec hsparsify 1 4 zero_le_one
    (by norm_num) true spanConst hspanConst
  have hcore' := Classical.choose_spec hcore
  have hspec := Classical.choose_spec hcore'
  have hAll := fun (L_in P_fp M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀) hM hN hΨ hα =>
    hspec.2.2 (lsfInit L_in P_fp) (hInit L_in P_fp) M₀ N₀ α Ψ ε hM₀1 hM hN hΨ hα
      (Chain.Ordered.concreteRestartEmbeds (lsfInit L_in P_fp) C_lsst lastTool C_last
        sparsify params hp_s hp_t M₀ N₀ (concreteBucketCapacity true C_lsst Ψ M₀ N₀ hM₀1) hM₀1
        α Ψ ε spanConst)
      (Chain.Ordered.concreteRestartNoReinsert (lsfInit L_in P_fp) C_lsst
        (hInit L_in P_fp) lastTool C_last sparsify params hp_s hp_t hsparsify M₀ N₀
        (concreteBucketCapacity true C_lsst Ψ M₀ N₀ hM₀1) hM₀1 α Ψ ε spanConst)
  { lsfInit := lsfInit
    C_lsst := C_lsst
    sparsify := sparsify
    params := params
    hp_s := hp_s
    hp_t := hp_t
    spanConst := spanConst
    hspanConst := hspanConst
    C_γ := Classical.choose hcore
    M_thresh := Classical.choose hcore'
    hInit := hInit
    hsparsify := hsparsify
    hCγ := hspec.1
    hM_thresh := hspec.2.1
    validWith := fun L_in P_fp M₀ N₀ α Ψ ε hM₀1 hM hN hΨ hα =>
      (hAll L_in P_fp M₀ N₀ α Ψ ε hM₀1 hM hN hΨ hα).1
    gammaWith := fun L_in P_fp M₀ N₀ α Ψ ε hM₀1 hM hN hΨ hα =>
      (hAll L_in P_fp M₀ N₀ α Ψ ε hM₀1 hM hN hΨ hα).2.1
    specWith := fun L_in P_fp M₀ N₀ α Ψ ε hM₀1 hM hN hΨ hα =>
      let hAll := (hAll L_in P_fp M₀ N₀ α Ψ ε hM₀1 hM hN hΨ hα).2.2
      ⟨hAll.1, fun κ hκ0 hκ_le {D η isUpdate T} hHist hEdge hLen hmBound hnBound hConn => by
        obtain ⟨_, _, hQuery, hUpdate, hDetect, _⟩ :=
          hAll.2 κ hκ0 hκ_le hHist hEdge hLen hmBound hnBound hConn
        refine ⟨fun t ht e he => (hQuery t ht).2 e he, ?_, hDetect⟩
        intro t ht hop
        exact ⟨(hUpdate t ht hop).1, (hUpdate t ht hop).2.1⟩⟩ }

section
variable {lastTool : LastLevelTool} {C_last : ℝ} {hLast : lastTool.IsSpec (lastLevelParams C_last)}
  {lsfInit : ℕ → ℕ → LSFInit} {C_lsst : ℝ}
  {hInit : ∀ L_in P_fp, Chain.Ordered.IsConcreteLSFInit (lsfInit L_in P_fp) C_lsst}
  {sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut}
  {params : ℕ → DynSpanner.SparsifyParams} {C_sp K_s K_t : ℝ} {hCsp : 0 < C_sp} {hKs : 0 ≤ K_s}
  {hKt : 0 ≤ K_t} {hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧
      (params m).K_t = K_t ∧ (params m).p_t = 1 ∧
      (params m).γ_ℓ ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params m).γ_c ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ))}
  {hsparsify : ∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify}
  {spanConst : ℕ} {hspanConst : 1 ≤ spanConst}

@[simp] theorem concreteChainWitnessWithLastOf_lsfInit :
    (concreteChainWitnessWithLastOf lastTool C_last hLast lsfInit C_lsst hInit sparsify params
      C_sp K_s K_t hCsp hKs hKt hp_spec hsparsify spanConst hspanConst).lsfInit = lsfInit := rfl

@[simp] theorem concreteChainWitnessWithLastOf_C_lsst :
    (concreteChainWitnessWithLastOf lastTool C_last hLast lsfInit C_lsst hInit sparsify params
      C_sp K_s K_t hCsp hKs hKt hp_spec hsparsify spanConst hspanConst).C_lsst = C_lsst := rfl

@[simp] theorem concreteChainWitnessWithLastOf_sparsify :
    (concreteChainWitnessWithLastOf lastTool C_last hLast lsfInit C_lsst hInit sparsify params
      C_sp K_s K_t hCsp hKs hKt hp_spec hsparsify spanConst hspanConst).sparsify = sparsify := rfl

@[simp] theorem concreteChainWitnessWithLastOf_params :
    (concreteChainWitnessWithLastOf lastTool C_last hLast lsfInit C_lsst hInit sparsify params
      C_sp K_s K_t hCsp hKs hKt hp_spec hsparsify spanConst hspanConst).params = params := rfl

@[simp] theorem concreteChainWitnessWithLastOf_spanConst :
    (concreteChainWitnessWithLastOf lastTool C_last hLast lsfInit C_lsst hInit sparsify params
      C_sp K_s K_t hCsp hKs hKt hp_spec hsparsify spanConst hspanConst).spanConst =
      spanConst := rfl

end

/-- The witness exists for any family of LSF initializers that fit one constant, with the
sparsifier of `HierPaths.theorem_8_1_concrete_unconditional` (`concreteChainWitnessWithLastOf`).
A single initializer is the constant family `fun _ _ => lsfInit`. -/
theorem concreteChainWitnessWithLast_nonempty_of
    (lastTool : LastLevelTool) (C_last : ℝ)
    (hLast : lastTool.IsSpec (lastLevelParams C_last))
    (lsfInit : ℕ → ℕ → LSFInit) (C_lsst : ℝ)
    (hInit : ∀ L_in P_fp, Chain.Ordered.IsConcreteLSFInit (lsfInit L_in P_fp) C_lsst) :
    Nonempty (ConcreteChainWitnessWithLast lastTool C_last hLast) := by
  obtain ⟨sparsify, params, C_sp, K_s, K_t, hCsp, _, hKs, hKt, h81⟩ :=
    HierPaths.theorem_8_1_concrete_unconditional
  exact ⟨concreteChainWitnessWithLastOf lastTool C_last hLast lsfInit C_lsst hInit sparsify params
    C_sp K_s K_t hCsp hKs hKt
    (fun m => ⟨(h81 m).1, (h81 m).2.1, (h81 m).2.2.1,
      (h81 m).2.2.2.1, (h81 m).2.2.2.2.1, (h81 m).2.2.2.2.2.1⟩)
    (fun mMax => (h81 mMax).2.2.2.2.2.2)⟩

/-- The witness exists, with the oracle and constant of `theorem_2_2` and the constant family of
the online initializer `initLSFOnline oracle C_lsst` (`isConcreteLSFInit_initLSFOnline`). -/
theorem concreteChainWitnessWithLast_nonempty
    (lastTool : LastLevelTool) (C_last : ℝ)
    (hLast : lastTool.IsSpec (lastLevelParams C_last)) :
    Nonempty (ConcreteChainWitnessWithLast lastTool C_last hLast) := by
  obtain ⟨oracle, C_lsst, hlsst⟩ := LSF.theorem_2_2
  exact concreteChainWitnessWithLast_nonempty_of lastTool C_last hLast
    (fun _ _ => initLSFOnline oracle C_lsst) C_lsst
    (fun _ _ => Chain.Ordered.isConcreteLSFInit_initLSFOnline hlsst)

/-- Extract `ConcreteChainWitnessWithLast` from ordered `concrete_theorem_5_1_with_last_core`. -/
def concreteChainWitnessWithLast
    (lastTool : LastLevelTool) (C_last : ℝ)
    (hLast : lastTool.IsSpec (lastLevelParams C_last)) :
    ConcreteChainWitnessWithLast lastTool C_last hLast :=
  Classical.choice (concreteChainWitnessWithLast_nonempty lastTool C_last hLast)

def concreteQualityBudgetWithLast
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) : ℕ :=
  Nat.ceil (15 + 5 * W.C_γ)

private theorem concreteQualityBudgetWithLast_ge
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) :
    15 + 5 * W.C_γ ≤ (concreteQualityBudgetWithLast W : ℝ) :=
  Nat.le_ceil _

def concreteEdgeThresholdWithLast
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) : ℕ :=
  max W.M_thresh (concretePsiThreshold (concreteQualityBudgetWithLast W))

theorem concreteEdgeThresholdWithLast_ge_two
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) :
    2 ≤ concreteEdgeThresholdWithLast W :=
  W.hM_thresh.trans (le_max_left _ _)

/-- Explicit dimension-only construction of `concreteCirculationCfgWithLast`: depends solely on
`(I_m, V)` and the fixed constants of `W` (`M_thresh`, `C_γ`, `lsfInit`, `C_lsst`, `sparsify`,
`params`, `lastTool`, `C_last`), with no degree cap. The LSF initializer is the member of the
family `W.lsfInit` at the solver's format for `(I_m, V)`: the limbs `ipmQualityLimbs I_m V k` and
the precision `ipmQualityPrecision I_m V k` of `ipmQualityMinRatioFormat I_m V k`
(`concreteCirculationCfgWithLast_T`). -/
def concreteCirculationCfgOfDims
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    (I_m V : ℕ) : Alg2Config :=
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let M₀ := max I_m threshold
  let N₀ := 4 * M₀
  let hM₀1 : 1 ≤ M₀ :=
    (by omega : 1 ≤ 2).trans ((concreteEdgeThresholdWithLast_ge_two W).trans (le_max_right _ _))
  let k := cappedQualityExponent threshold A I_m
  let α := Num.IPM.alphaPrime I_m V / 8
  let Ψ := ((ipmQualityRangeExponent I_m V k + slackRangeExponent I_m V + 6 : ℕ) : ℝ)
  let ε := (1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I_m V / 1024
  let B_cap := concreteBucketCapacity true W.C_lsst Ψ M₀ N₀ hM₀1
  Chain.Ordered.concreteAlg2CfgWithLast (W.lsfInit (ipmQualityLimbs I_m V k)
    (ipmQualityPrecision I_m V k)) W.C_lsst lastTool C_last W.sparsify W.params
    W.hp_s W.hp_t M₀ N₀ B_cap hM₀1 α Ψ ε W.spanConst

/-- Connected degree-free ordered `concreteAlg2CfgWithLast` built for a circulation `J`. -/
def concreteCirculationCfgWithLast
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    (J : Circulation) : Alg2Config :=
  concreteCirculationCfgOfDims W (solverConnectedAugmented J).m (solverPenalty J.m)

/-- The core tool of the configuration of an instance `J` is the bundle tool with the member of
the LSF family at the solver's own format `F := ipmQualityMinRatioFormat I.m V k hw`, the format
of `minRatioMachineContractWithV` in `DyadicWithVConcretePrograms.supported`: its limbs `F.limbs`
and its precision `F.fmt.precision`. This holds for every word size `w` with `hw`, since the limbs
and the precision of `F` do not depend on `w`. -/
theorem concreteCirculationCfgWithLast_T
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    (J : Circulation) {w : ℕ}
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        (solverConnectedAugmented J).m) ≤ w) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let threshold := concreteEdgeThresholdWithLast W
    let k := cappedQualityExponent threshold (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    (concreteCirculationCfgWithLast W J).T =
      sparseCoreBundleRestartToolMachWith (W.lsfInit F.limbs F.fmt.precision) W.C_lsst
        (Expander.chosenL (max I.m threshold ^ 2)) (fun _ => W.sparsify)
        W.params W.spanConst := rfl

/-- The configuration of an instance `J` meets the validity conditions of Algorithm 2 with orders,
`ValidOrd`: the field `validWith` at the sizes of `J`, which meet its conditions by
`concreteCirculation_bounds_of`. -/
theorem concreteCirculationCfgWithLast_validOrd
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hm : 0 < J.m) (hp : ∀ e, 1 ≤ J.capacity e) :
    (concreteCirculationCfgWithLast W J).ValidOrd := by
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThresholdWithLast W
  let M₀ := max I.m threshold
  let hM₀1 : 1 ≤ M₀ :=
    (by omega : 1 ≤ 2).trans ((concreteEdgeThresholdWithLast_ge_two W).trans (le_max_right _ _))
  let k := cappedQualityExponent threshold (concreteQualityBudgetWithLast W) I.m
  let Ψ := ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
  obtain ⟨hThresh, hN₀, hPsi, hα, -⟩ :=
    concreteCirculation_bounds_of (le_max_left W.M_thresh _) (le_max_right W.M_thresh _)
      (concreteEdgeThresholdWithLast_ge_two W) J hJn hm hp
  exact W.validWith (ipmQualityLimbs I.m V k) (ipmQualityPrecision I.m V k) M₀ (4 * M₀)
    (Num.IPM.alphaPrime I.m V / 8) Ψ ((1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024) hM₀1
    hThresh hN₀ hPsi hα

/-- The configuration of an instance `J` meets `ValidOrdNoHidden`
(`concreteCirculationCfgWithLast_validOrd` and `ValidOrd.toNoHidden`). -/
theorem concreteCirculationCfgWithLast_validOrdNoHidden
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hm : 0 < J.m) (hp : ∀ e, 1 ≤ J.capacity e) :
    (concreteCirculationCfgWithLast W J).ValidOrdNoHidden :=
  (concreteCirculationCfgWithLast_validOrd W J hJn hm hp).toNoHidden

/-- The rounded rebuild factor `Γ = ⌈γ_r(M₀²)⌉` of the configuration of an instance `J` is at least
`1` and at most `exp((C_γ + 1) L^{23/24} log(L + 2))` with `L = log(M₀ + 2)` and the constant
`C_γ` of the witness: the field `gammaWith` at the sizes of `J`. -/
theorem concreteCirculationCfgWithLast_gamma_r
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hm : 0 < J.m) (hp : ∀ e, 1 ≤ J.capacity e) :
    let cfg := concreteCirculationCfgWithLast W J
    1 ≤ ⌈cfg.TP.γ_r (cfg.P.M₀ ^ 2)⌉₊ ∧
      (⌈cfg.TP.γ_r (cfg.P.M₀ ^ 2)⌉₊ : ℝ) ≤
        Real.exp ((W.C_γ + 1) * Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := by
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThresholdWithLast W
  let M₀ := max I.m threshold
  let hM₀1 : 1 ≤ M₀ :=
    (by omega : 1 ≤ 2).trans ((concreteEdgeThresholdWithLast_ge_two W).trans (le_max_right _ _))
  let k := cappedQualityExponent threshold (concreteQualityBudgetWithLast W) I.m
  let Ψ := ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
  obtain ⟨hThresh, hN₀, hPsi, hα, -⟩ :=
    concreteCirculation_bounds_of (le_max_left W.M_thresh _) (le_max_right W.M_thresh _)
      (concreteEdgeThresholdWithLast_ge_two W) J hJn hm hp
  exact W.gammaWith (ipmQualityLimbs I.m V k) (ipmQualityPrecision I.m V k) M₀ (4 * M₀)
    (Num.IPM.alphaPrime I.m V / 8) Ψ ((1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024) hM₀1
    hThresh hN₀ hPsi hα

/-- The dyadic ordered Algorithm 2 structure `Chain.Ordered.algorithm2_dsWithFailureWith (concreteCirculationCfgWithLast W J) (1 / 2 ^ k)`
satisfies `MinRatioSpecWithFailureEdgeOnlyConnectedUpTo` at the capped dyadic quality `1 / 2 ^ k`. -/
theorem concrete_minRatioSpecWithFailureEdgeOnlyConnectedUpTo_withLast
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hm : 0 < J.m) (hp : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let threshold := concreteEdgeThresholdWithLast W
    let A := concreteQualityBudgetWithLast W
    let k := cappedQualityExponent threshold A I.m
    MinRatioSpecWithFailureEdgeOnlyConnectedUpTo
      (Chain.Ordered.algorithm2_dsWithFailureWith (concreteCirculationCfgWithLast W J) (1 / (2 : ℝ) ^ k))
      (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
      ((1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024) I.m I.n := by
  dsimp only
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let M₀ := max I.m threshold
  let N₀ := 4 * M₀
  let hM₀1 : 1 ≤ M₀ :=
    (by omega : 1 ≤ 2).trans ((concreteEdgeThresholdWithLast_ge_two W).trans (le_max_right _ _))
  let k := cappedQualityExponent threshold A I.m
  let α := Num.IPM.alphaPrime I.m V / 8
  let Ψ := ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
  let ε := (1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024
  obtain ⟨hThresh, hN₀, hPsi, hα, hIn_le⟩ :=
    concreteCirculation_bounds_of (le_max_left W.M_thresh _) (le_max_right W.M_thresh _)
      (concreteEdgeThresholdWithLast_ge_two W) J hJn hm hp
  obtain ⟨⟨_, hKappa⟩, hWith⟩ :=
    W.specWith (ipmQualityLimbs I.m V k) (ipmQualityPrecision I.m V k) M₀ N₀ α Ψ ε hM₀1 hThresh
      hN₀ hPsi hα
  have hk_pos : (0 : ℝ) < 1 / (2 : ℝ) ^ k := by positivity
  have hk_le_κ : 1 / (2 : ℝ) ^ k ≤
      alg2KappaOwn (concreteCirculationCfgWithLast W J).TP
        (concreteCirculationCfgWithLast W J).LP
        (concreteCirculationCfgWithLast W J).P
        (concreteCirculationCfgWithLast W J).σ_mwu
        (concreteCirculationCfgWithLast W J).N₀ :=
    concrete_kappa_le_alg2KappaOwn_of A (concreteQualityBudgetWithLast_ge W) M₀ hKappa
  exact minRatioSpecWithFailureEdgeOnlyConnectedUpTo_of_ordered (le_max_left _ _) hIn_le
    (fun hValid hEdge hLen hmM₀ hnN₀ hConn =>
      hWith (1 / (2 : ℝ) ^ k) hk_pos hk_le_κ hValid hEdge hLen hmM₀ hnN₀ hConn)

end MinCostFlow.Final
