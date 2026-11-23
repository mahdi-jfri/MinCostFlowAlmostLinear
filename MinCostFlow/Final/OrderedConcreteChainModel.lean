module

public import MinCostFlow.Chain.Ordered.ConcreteInstantiation
public import MinCostFlow.Chain.Ordered.RestartSpecOn
public import MinCostFlow.HierPaths.BuildFinal
public import MinCostFlow.Final.ConcreteChainModel
public import MinCostFlow.Final.EdgeOnlySpec
import MinCostFlow.IPM.Machine.ConnectedSolverFinish
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Degree-free ordered concrete chain model from Theorem 5.1

Unpacks `Chain.Ordered.concrete_theorem_5_1_with_last_core` at `C_ψ = 1`, `C_N = 4`
for the machine-cost bundle tool `sparseCoreBundleRestartToolMachWith lsfInit` with no degree-cap
parameter (`C_D` / `D_cap`),
discharges `ToolEmbedsSurvivingOrdRestart` and `ToolNoReinsertOrdRestart` unconditionally via
`Chain.Ordered.concreteRestartEmbeds` and `Chain.Ordered.concreteRestartNoReinsert`, and derives
`MinRatioSpecWithFailureEdgeOnlyConnectedUpTo` on `solverConnectedAugmented J` at the capped
dyadic quality exponent.

The witness holds an LSF initializer `lsfInit` that fits `C_lsst` (`IsConcreteLSFInit`). It is
built by `orderedConcreteChainWitness_nonempty_of` from any such initializer, and
`orderedConcreteChainWitness_nonempty` passes the online initializer
`initLSFOnline oracle C_lsst` of `theorem_2_2`'s oracle. The oracle itself is used only by the
last level (`lastLevelTool oracle C_lsst`).
-/

@[expose] public noncomputable section
namespace MinCostFlow.Final
open Chain IPM IPM.Machine WordRAM Scaling LSF

/-- Degree-free witness bundle unpacked from ordered `Chain.Ordered.concrete_theorem_5_1_with_last_core`
at fixed asymptotic constants `C_ψ = 1` and `C_N = 4`, with `ToolEmbedsSurvivingOrdRestart` and
`ToolNoReinsertOrdRestart` already discharged for `sparseCoreBundleRestartToolMachWith lsfInit`. -/
structure OrderedConcreteChainWitness where
  oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph
  lsfInit : SparseCore.LSFInit
  C_lsst : ℝ
  sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut
  params : ℕ → DynSpanner.SparsifyParams
  hp_s : ∀ m, (params m).p_s ≤ 1
  hp_t : ∀ m, (params m).p_t ≤ 1
  C_γ : ℝ
  M_thresh : ℕ
  hlsst : HasLSSTSpec oracle C_lsst
  hInit : Chain.Ordered.IsConcreteLSFInit lsfInit C_lsst
  hsparsify : ∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify
  hCγ : 3 ≤ C_γ
  hM_thresh : 2 ≤ M_thresh
  spec : ∀ (M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
    M_thresh ≤ M₀ →
    1 + Real.log ((N₀ : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) →
    alg2PsiGame Ψ M₀ ≤ Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
    0 < α →
    let B_cap := concreteBCap C_lsst Ψ M₀ N₀ hM₀1
    let cfg := Chain.Ordered.concreteAlg2Cfg lsfInit oracle C_lsst sparsify params hp_s hp_t
      M₀ N₀ B_cap hM₀1 α Ψ ε
    ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
      MinRatioHistoryValid D isUpdate T →
      Chain.Ordered.HistoryEdgeOnly D T →
      Chain.Ordered.HistoryLengthsInRange D T Ψ →
      (∀ t ≤ T, (D.G t).m ≤ M₀) →
      (∀ t ≤ T, (D.G t).n ≤ N₀) →
      (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
      let A := Chain.Ordered.algorithm2_dsWithFailureOwn cfg
      let κ := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
      let C_κ := 15 + 5 * C_γ
      (0 < κ ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ) ∧
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
  specWith : ∀ (M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
    M_thresh ≤ M₀ →
    1 + Real.log ((N₀ : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) →
    alg2PsiGame Ψ M₀ ≤ Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
    0 < α →
    let B_cap := concreteBCap C_lsst Ψ M₀ N₀ hM₀1
    let cfg := Chain.Ordered.concreteAlg2Cfg lsfInit oracle C_lsst sparsify params hp_s hp_t
      M₀ N₀ B_cap hM₀1 α Ψ ε
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

/-- The degree-free ordered concrete chain witness with given data: the oracle `oracle` of the
last level, the LSF initializer `lsfInit` (fitting `C_lsst`), the sparsifier `sparsify` and its
parameters `params` are the arguments, by definition (the `…_lsfInit`/`…_sparsify` lemmas below
are `rfl`). Only the constants `C_γ` and `M_thresh` are chosen, from
`Chain.Ordered.concrete_theorem_5_1_with_last_core`. `ToolEmbedsSurvivingOrdRestart` and
`ToolNoReinsertOrdRestart` are discharged via `Chain.Ordered.concreteRestartEmbeds` and
`Chain.Ordered.concreteRestartNoReinsert`. -/
def orderedConcreteChainWitnessOf
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (hlsst : HasLSSTSpec oracle C_lsst)
    (lsfInit : SparseCore.LSFInit) (hInit : Chain.Ordered.IsConcreteLSFInit lsfInit C_lsst)
    (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (params : ℕ → DynSpanner.SparsifyParams)
    (C_sp K_s K_t : ℝ) (hCsp : 0 < C_sp) (hKs : 0 ≤ K_s) (hKt : 0 ≤ K_t)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧
      (params m).K_t = K_t ∧ (params m).p_t = 1 ∧
      (params m).γ_ℓ ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params m).γ_c ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    (hsparsify : ∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify) :
    OrderedConcreteChainWitness :=
  have hp_s : ∀ m, (params m).p_s ≤ 1 := fun m => le_of_eq (hp_spec m).2.1
  have hp_t : ∀ m, (params m).p_t ≤ 1 := fun m => le_of_eq (hp_spec m).2.2.2.1
  have hcore := Chain.Ordered.concrete_theorem_5_1_with_last_core lsfInit C_lsst
      (SparseCore.lastLevelTool oracle C_lsst) C_lsst
      (SparseCore.lastLevelTool_isSpec oracle C_lsst hlsst) sparsify params
      C_sp K_s K_t hCsp hKs hKt hp_spec hInit hsparsify 1 4 zero_le_one (by norm_num) false
  have hcore' := Classical.choose_spec hcore
  have hspec := Classical.choose_spec hcore'
  { oracle := oracle
    lsfInit := lsfInit
    C_lsst := C_lsst
    sparsify := sparsify
    params := params
    hp_s := hp_s
    hp_t := hp_t
    C_γ := Classical.choose hcore
    M_thresh := Classical.choose hcore'
    hlsst := hlsst
    hInit := hInit
    hsparsify := hsparsify
    hCγ := hspec.1
    hM_thresh := hspec.2.1
    spec := fun M₀ N₀ α Ψ ε hM₀1 hM hN hΨ hα
        {D η isUpdate T} hHist hEdge hLen hmBound hnBound hConn => by
      have hr3 := Chain.Ordered.concreteRestartEmbeds lsfInit C_lsst
        (SparseCore.lastLevelTool oracle C_lsst) C_lsst sparsify params hp_s hp_t
        M₀ N₀ (concreteBCap C_lsst Ψ M₀ N₀ hM₀1) hM₀1 α Ψ ε
      have hr4 := Chain.Ordered.concreteRestartNoReinsert lsfInit C_lsst hInit
        (SparseCore.lastLevelTool oracle C_lsst) C_lsst sparsify params hp_s hp_t hsparsify
        M₀ N₀ (concreteBCap C_lsst Ψ M₀ N₀ hM₀1) hM₀1 α Ψ ε
      have hAll := hspec.2.2 M₀ N₀ α Ψ ε hM₀1 hM hN hΨ hα hr3 hr4
      have hKappa := hAll.1
      obtain ⟨_, _, hQuery, hUpdate, hDetect, _⟩ :=
        hAll.2 _ hKappa.1 le_rfl hHist hEdge hLen hmBound hnBound hConn
      simpa only [Chain.Ordered.algorithm2_dsWithFailureOwn] using
        ⟨hKappa, fun t ht e he => (hQuery t ht).2 e he,
          fun t ht hop => ⟨(hUpdate t ht hop).1, (hUpdate t ht hop).2.1⟩, hDetect⟩
    specWith := fun M₀ N₀ α Ψ ε hM₀1 hM hN hΨ hα =>
      let hr3 := Chain.Ordered.concreteRestartEmbeds lsfInit C_lsst
        (SparseCore.lastLevelTool oracle C_lsst) C_lsst sparsify params hp_s hp_t
        M₀ N₀ (concreteBCap C_lsst Ψ M₀ N₀ hM₀1) hM₀1 α Ψ ε
      let hr4 := Chain.Ordered.concreteRestartNoReinsert lsfInit C_lsst hInit
        (SparseCore.lastLevelTool oracle C_lsst) C_lsst sparsify params hp_s hp_t hsparsify
        M₀ N₀ (concreteBCap C_lsst Ψ M₀ N₀ hM₀1) hM₀1 α Ψ ε
      let hAll := hspec.2.2 M₀ N₀ α Ψ ε hM₀1 hM hN hΨ hα hr3 hr4
      ⟨hAll.1, fun κ hκ0 hκ_le {D η isUpdate T} hHist hEdge hLen hmBound hnBound hConn => by
        obtain ⟨_, _, hQuery, hUpdate, hDetect, _⟩ :=
          hAll.2 κ hκ0 hκ_le hHist hEdge hLen hmBound hnBound hConn
        refine ⟨fun t ht e he => (hQuery t ht).2 e he, ?_, hDetect⟩
        intro t ht hop
        exact ⟨(hUpdate t ht hop).1, (hUpdate t ht hop).2.1⟩⟩ }

section
variable {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ}
  {hlsst : HasLSSTSpec oracle C_lsst}
  {lsfInit : SparseCore.LSFInit} {hInit : Chain.Ordered.IsConcreteLSFInit lsfInit C_lsst}
  {sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut}
  {params : ℕ → DynSpanner.SparsifyParams} {C_sp K_s K_t : ℝ} {hCsp : 0 < C_sp} {hKs : 0 ≤ K_s}
  {hKt : 0 ≤ K_t} {hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧
      (params m).K_t = K_t ∧ (params m).p_t = 1 ∧
      (params m).γ_ℓ ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params m).γ_c ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ))}
  {hsparsify : ∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify}

@[simp] theorem orderedConcreteChainWitnessOf_oracle :
    (orderedConcreteChainWitnessOf oracle C_lsst hlsst lsfInit hInit sparsify params
      C_sp K_s K_t hCsp hKs hKt hp_spec hsparsify).oracle = oracle := rfl

@[simp] theorem orderedConcreteChainWitnessOf_lsfInit :
    (orderedConcreteChainWitnessOf oracle C_lsst hlsst lsfInit hInit sparsify params
      C_sp K_s K_t hCsp hKs hKt hp_spec hsparsify).lsfInit = lsfInit := rfl

@[simp] theorem orderedConcreteChainWitnessOf_sparsify :
    (orderedConcreteChainWitnessOf oracle C_lsst hlsst lsfInit hInit sparsify params
      C_sp K_s K_t hCsp hKs hKt hp_spec hsparsify).sparsify = sparsify := rfl

@[simp] theorem orderedConcreteChainWitnessOf_params :
    (orderedConcreteChainWitnessOf oracle C_lsst hlsst lsfInit hInit sparsify params
      C_sp K_s K_t hCsp hKs hKt hp_spec hsparsify).params = params := rfl

end

/-- The degree-free ordered concrete chain witness exists, with the unconditional sparsifier
`HierPaths.theorem_8_1_concrete_unconditional` (`orderedConcreteChainWitnessOf`), for an oracle
with `HasLSSTSpec` and any LSF initializer that fits its constant. -/
theorem orderedConcreteChainWitness_nonempty_of
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (hlsst : HasLSSTSpec oracle C_lsst)
    (lsfInit : SparseCore.LSFInit) (hInit : Chain.Ordered.IsConcreteLSFInit lsfInit C_lsst) :
    Nonempty OrderedConcreteChainWitness := by
  obtain ⟨sparsify, params, C_sp, K_s, K_t, hCsp, _, hKs, hKt, h81⟩ :=
    HierPaths.theorem_8_1_concrete_unconditional
  exact ⟨orderedConcreteChainWitnessOf oracle C_lsst hlsst lsfInit hInit sparsify params
    C_sp K_s K_t hCsp hKs hKt
    (fun m => ⟨(h81 m).1, (h81 m).2.1, (h81 m).2.2.1,
      (h81 m).2.2.2.1, (h81 m).2.2.2.2.1, (h81 m).2.2.2.2.2.1⟩)
    (fun mMax => (h81 mMax).2.2.2.2.2.2)⟩

/-- The degree-free ordered concrete chain witness exists, with the oracle and constant of
`theorem_2_2` and the online initializer `initLSFOnline oracle C_lsst`
(`isConcreteLSFInit_initLSFOnline`). -/
theorem orderedConcreteChainWitness_nonempty : Nonempty OrderedConcreteChainWitness := by
  obtain ⟨oracle, C_lsst, hlsst⟩ := LSF.theorem_2_2
  exact orderedConcreteChainWitness_nonempty_of oracle C_lsst hlsst
    (SparseCore.initLSFOnline oracle C_lsst) (Chain.Ordered.isConcreteLSFInit_initLSFOnline hlsst)

/-- Canonical degree-free ordered concrete chain witness. -/
def orderedConcreteChainWitness : OrderedConcreteChainWitness :=
  Classical.choice orderedConcreteChainWitness_nonempty

/-- Quality budget `A ≥ 15 + 5 * C_γ` matched to ordered `concrete_theorem_5_1`. -/
def orderedConcreteQualityBudget (W : OrderedConcreteChainWitness) : ℕ :=
  Nat.ceil (15 + 5 * W.C_γ)

theorem orderedConcreteQualityBudget_ge (W : OrderedConcreteChainWitness) :
    15 + 5 * W.C_γ ≤ (orderedConcreteQualityBudget W : ℝ) :=
  Nat.le_ceil _

/-- Edge threshold combining `W.M_thresh` with `concretePsiThreshold`. -/
def orderedConcreteEdgeThreshold (W : OrderedConcreteChainWitness) : ℕ :=
  max W.M_thresh (concretePsiThreshold (orderedConcreteQualityBudget W))

theorem orderedConcreteEdgeThreshold_ge_two (W : OrderedConcreteChainWitness) :
    2 ≤ orderedConcreteEdgeThreshold W :=
  W.hM_thresh.trans (le_max_left _ _)

/-- Degree-free ordered `concreteAlg2Cfg` built for a circulation `J`. -/
def orderedConcreteCirculationCfg (W : OrderedConcreteChainWitness) (J : Circulation) :
    Alg2Config :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := orderedConcreteEdgeThreshold W
  let A := orderedConcreteQualityBudget W
  let M₀ := max I.m threshold
  let N₀ := 4 * M₀
  let hM₀1 : 1 ≤ M₀ :=
    (by omega : 1 ≤ 2).trans ((orderedConcreteEdgeThreshold_ge_two W).trans (le_max_right _ _))
  let k := cappedQualityExponent threshold A I.m
  let α := Num.IPM.alphaPrime I.m V / 8
  let Ψ := ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
  let ε := (1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024
  let B_cap := concreteBCap W.C_lsst Ψ M₀ N₀ hM₀1
  Chain.Ordered.concreteAlg2Cfg W.lsfInit W.oracle W.C_lsst W.sparsify W.params W.hp_s W.hp_t
    M₀ N₀ B_cap hM₀1 α Ψ ε

/-- The dyadic ordered Algorithm 2 structure satisfies
`MinRatioSpecWithFailureEdgeOnlyConnectedUpTo` at `1 / 2 ^ k`. -/
theorem orderedConcrete_minRatioSpecWithFailureEdgeOnlyConnectedUpTo_with
    (W : OrderedConcreteChainWitness)
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hm : 0 < J.m) (hp : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let threshold := orderedConcreteEdgeThreshold W
    let A := orderedConcreteQualityBudget W
    let k := cappedQualityExponent threshold A I.m
    MinRatioSpecWithFailureEdgeOnlyConnectedUpTo
      (Chain.Ordered.algorithm2_dsWithFailureWith (orderedConcreteCirculationCfg W J) (1 / (2 : ℝ) ^ k))
      (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
      ((1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024) I.m I.n := by
  dsimp only
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := orderedConcreteEdgeThreshold W
  let A := orderedConcreteQualityBudget W
  let M₀ := max I.m threshold
  let N₀ := 4 * M₀
  let hM₀1 : 1 ≤ M₀ :=
    (by omega : 1 ≤ 2).trans ((orderedConcreteEdgeThreshold_ge_two W).trans (le_max_right _ _))
  let k := cappedQualityExponent threshold A I.m
  let α := Num.IPM.alphaPrime I.m V / 8
  let Ψ := ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
  let ε := (1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024
  obtain ⟨hThresh, hN₀, hPsi, hα, hIn_le⟩ :=
    concreteCirculation_bounds_of (le_max_left W.M_thresh _) (le_max_right W.M_thresh _)
      (orderedConcreteEdgeThreshold_ge_two W) J hJn hm hp
  obtain ⟨⟨_, hKappa⟩, hWith⟩ :=
    W.specWith M₀ N₀ α Ψ ε hM₀1 hThresh hN₀ hPsi hα
  have hk_pos : (0 : ℝ) < 1 / (2 : ℝ) ^ k := by positivity
  have hk_le_κ : 1 / (2 : ℝ) ^ k ≤
      alg2KappaOwn (orderedConcreteCirculationCfg W J).TP (orderedConcreteCirculationCfg W J).LP
        (orderedConcreteCirculationCfg W J).P (orderedConcreteCirculationCfg W J).σ_mwu
        (orderedConcreteCirculationCfg W J).N₀ :=
    concrete_kappa_le_alg2KappaOwn_of A (orderedConcreteQualityBudget_ge W) M₀ hKappa
  exact minRatioSpecWithFailureEdgeOnlyConnectedUpTo_of_ordered (le_max_left _ _) hIn_le
    (fun hValid hEdge hLen hmM₀ hnN₀ hConn =>
      hWith (1 / (2 : ℝ) ^ k) hk_pos hk_le_κ hValid hEdge hLen hmM₀ hnN₀ hConn)

/-- The ordered Algorithm 2 structure `algorithm2_dsWithFailureOwn` satisfies
`MinRatioSpecWithFailureEdgeOnlyConnectedUpTo` at `1 / 2 ^ k`. -/
theorem orderedConcrete_minRatioSpecWithFailureEdgeOnlyConnectedUpTo
    (W : OrderedConcreteChainWitness)
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hm : 0 < J.m) (hp : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let threshold := orderedConcreteEdgeThreshold W
    let A := orderedConcreteQualityBudget W
    let k := cappedQualityExponent threshold A I.m
    MinRatioSpecWithFailureEdgeOnlyConnectedUpTo
      (Chain.Ordered.algorithm2_dsWithFailureOwn (orderedConcreteCirculationCfg W J))
      (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
      ((1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024) I.m I.n := by
  dsimp only
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := orderedConcreteEdgeThreshold W
  let A := orderedConcreteQualityBudget W
  let M₀ := max I.m threshold
  let N₀ := 4 * M₀
  let hM₀1 : 1 ≤ M₀ :=
    (by omega : 1 ≤ 2).trans ((orderedConcreteEdgeThreshold_ge_two W).trans (le_max_right _ _))
  let k := cappedQualityExponent threshold A I.m
  let α := Num.IPM.alphaPrime I.m V / 8
  let Ψ := ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
  let ε := (1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024
  obtain ⟨hThresh, hN₀, hPsi, hα, hIn_le⟩ :=
    concreteCirculation_bounds_of (le_max_left W.M_thresh _) (le_max_right W.M_thresh _)
      (orderedConcreteEdgeThreshold_ge_two W) J hJn hm hp
  obtain ⟨⟨_, hKappa⟩, _⟩ := W.specWith M₀ N₀ α Ψ ε hM₀1 hThresh hN₀ hPsi hα
  have hk_le_κ : 1 / (2 : ℝ) ^ k ≤
      alg2KappaOwn (orderedConcreteCirculationCfg W J).TP (orderedConcreteCirculationCfg W J).LP
        (orderedConcreteCirculationCfg W J).P (orderedConcreteCirculationCfg W J).σ_mwu
        (orderedConcreteCirculationCfg W J).N₀ :=
    concrete_kappa_le_alg2KappaOwn_of A (orderedConcreteQualityBudget_ge W) M₀ hKappa
  exact minRatioSpecWithFailureEdgeOnlyConnectedUpTo_of_ordered_le hα.le hk_le_κ
    (le_max_left _ _) hIn_le
    (fun hValid hEdge hLen hmM₀ hnN₀ hConn =>
      (W.spec M₀ N₀ α Ψ ε hM₀1 hThresh hN₀ hPsi hα hValid hEdge hLen hmM₀ hnN₀ hConn).2)

end MinCostFlow.Final
