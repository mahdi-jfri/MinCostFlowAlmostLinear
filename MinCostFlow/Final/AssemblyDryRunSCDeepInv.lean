module

public import MinCostFlow.Final.AssemblyDryRunSCDeepUpdate
public import MinCostFlow.MinRatio.OrdSolverRepFullKFBL
import Mathlib.Tactic

/-!
# `DeepShiftChainInvHyps` for `DryChainLenGridInv` (`AssemblyDryRunSCDeepInv`)

Packages `dryChainLenGridInv_init`, `dryChainLenGridInv_preLoop_of_reached`,
`dryChainLenGridInv_shift`, and `dryShiftDeepModelInv_of_wordBound` into
`MinRatio.DeepShiftChainInvHyps` for the dry run (`dryWitnessUsed`), strictly below
`Final/AssemblyDryRunSC.lean`.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Scaling.Machine
  MinRatio LastLevelProgram DynSpanner.Program

/-- Discharges `DeepShiftChainInvHyps` at `DryChainLenGridInv J` for any dry-run input
`(source, J)` whose word size covers `(levelM j + N₀ + 2) ^ wordExp * (F.limbs + 1)` and whose
`stretchP` is at most `100 * F.rangeExponent`. -/
theorem dryChainLenGridInv_deepShiftChainInvHyps
    (allocationCoefficient allocationDegree wordExp stretchP : ℕ)
    (hSCWordCoeff :
      Classical.choose (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed) ≤
        allocationCoefficient)
    (source J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCap : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    (hWordBound :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
      ∀ j < cfg.P.d, (levelM cfg.TP cfg.P j + cfg.N₀ + 2) ^ wordExp * (F.limbs + 1) < 2 ^ w)
    (hStretchLe :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      stretchP ≤ 100 * ipmQualityRangeExponent I.m V k) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
    DeepShiftChainInvHyps w F cfg (namedInstance I) k wordExp stretchP (DryChainLenGridInv J) := by
  intro I V k F cfg w
  have hWordLvl : ∀ j < cfg.P.d,
      levelM cfg.TP cfg.P j < 2 ^ w ∧
      (levelM cfg.TP cfg.P j + cfg.N₀ + 2) ^ wordExp * (F.limbs + 1) < 2 ^ w := by
    intro j hj
    refine ⟨?_, hWordBound j hj⟩
    have hL := (concrete_sparseCoreCapHyp_uniform dryWitnessUsed J hJn hJm hCap j hj.le 0 0
      (by omega)).2
    have h1 := Classical.choose_spec
      (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed)
      allocationCoefficient allocationDegree hSCWordCoeff source J hJn hJm hCap hw
      1 (by decide) j _ hL
    have hle : levelM cfg.TP cfg.P j ≤
        (levelM cfg.TP cfg.P j + cfg.N₀ + 2) ^ 1 * (F.limbs + 1) := by
      rw [pow_one]
      exact le_trans (by omega) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
    exact lt_of_le_of_lt hle h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ ℓ₀ hLen hGrid
    exact dryChainLenGridInv_init J hJn hJm hCap ℓ₀ g₀ hLen hGrid
  · intro model U gVec lVec hReach _ hU hLen hGrid hAgree hD
    exact (dryChainLenGridInv_preLoop_of_reached J hJn hJm hCap hReach hD hU hLen hGrid hAgree).1
  · intro ch hLoop hD i hi
    exact dryChainLenGridInv_shift J hJn hJm hCap hLoop hD hi
  · intro stM i hiLt hLoop hD
    exact (dryShiftDeepModelInv_of_wordBound allocationCoefficient allocationDegree wordExp
      source J hJn hJm hCap hw hWordLvl stM i stretchP hiLt hLoop hD hStretchLe).1

/-- `stretchP = (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (I.m + 1).size` (definitionally
`dryLastStretchP J`) lies below `100 * ipmQualityRangeExponent I.m V k`. -/
theorem dryLastStretchP_im_le_100_E (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (I.m + 1).size ≤
      100 * ipmQualityRangeExponent I.m V k := by
  intro I V k
  have hle := dryLastStretchP_le_rangeExponent J hJn hJm hCap
  have hsz : (I.m + 1).size ≤
      (max I.m (levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
        (concreteCirculationCfgWithLast dryWitnessUsed J).P
        (concreteCirculationCfgWithLast dryWitnessUsed J).P.d) + 1).size :=
    Nat.size_le_size (Nat.add_le_add_right (le_max_left _ _) 1)
  dsimp only [I, V, k] at hsz ⊢
  omega

/-- `initTargetCap cfg (namedInstance I)` is bounded by
`2 * (Ordered.alg2NameBase cfg (namedInstance I) + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * I.m)`
(definitionally `dryDeepIntCapMax J`). -/
theorem dryInitTargetCap_le_intCapMax (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    initTargetCap cfg G ≤
      2 * (Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * I.m) := by
  intro I cfg G
  have hImPos : 0 < I.m :=
    lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap).1
  unfold initTargetCap
  rw [namedInstance_m]
  omega

/-- `2 * (namedInstance I).n ≤ 2 * (cfg.P.d + 1) * I.n` (definitionally `dryDeepForestEdgeCap J`). -/
theorem dryTwoMulN_le_forestEdgeCap (J : Circulation) :
    let I := solverConnectedAugmented J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    2 * (namedInstance I).n ≤ 2 * (cfg.P.d + 1) * I.n := by
  intro I cfg
  have hn : (namedInstance I).n = I.n := by simp [namedInstance, MGraph.n]
  rw [hn]
  have h1 : 2 ≤ 2 * (cfg.P.d + 1) := by omega
  exact Nat.mul_le_mul_right I.n h1

end MinCostFlow.Final.DryRun
