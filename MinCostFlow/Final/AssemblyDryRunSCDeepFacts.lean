module

public import MinCostFlow.Final.AssemblyDryRunSCCoreKFBL
public import MinCostFlow.Final.AssemblyDryRunSCDeepGrid
import Mathlib.Tactic

/-!
# Dry-run tool and numeric facts for the deep shift (`AssemblyDryRunSCDeepFacts`)

Instantiates `Final/AssemblyDryRunSCDeepGrid.lean` at `Psc : DrySparseCorePieces`, discharging
`drySC_deepWordLvl` and `drySC_shiftDeepModelInv_of_loopInv` via `drySCWordBound_proved`.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Scaling.Machine
  MinRatio LastLevelProgram DynSpanner.Program

/-- Hypothesis 3 of `shiftDeepModelInv_of_loopInv`: both per-level word-size bounds
`levelM j < 2 ^ w` and `(levelM j + N₀ + 2) ^ wordExp * (F.limbs + 1) < 2 ^ w` hold for every
dry-run input. -/
theorem drySC_deepWordLvl (Psc : DrySparseCorePieces)
    (allocationCoefficient allocationDegree : ℕ)
    (hSCWordCoeff :
      Classical.choose (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed) ≤
        allocationCoefficient) :
    ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
      ∀ j < cfg.P.d,
        levelM cfg.TP cfg.P j < 2 ^ w ∧
        (levelM cfg.TP cfg.P j + cfg.N₀ + 2) ^
            (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).wordExp *
            (F.limbs + 1) <
          2 ^ w := by
  intro source J hJn hJm hCost hCap hw
  dsimp only
  intro j hj
  refine ⟨?_, drySCWordBound_proved Psc allocationCoefficient allocationDegree hSCWordCoeff
    source J hJn hJm hCost hCap hw j hj⟩
  have hL := (concrete_sparseCoreCapHyp_uniform dryWitnessUsed J hJn hJm (fun e => (hCap e).1)
    j hj.le 0 0 (by omega)).2
  have h1 := Classical.choose_spec (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed)
    allocationCoefficient allocationDegree hSCWordCoeff source J hJn hJm (fun e => (hCap e).1) hw
    1 (by decide) j _ hL
  have hle : levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
      (concreteCirculationCfgWithLast dryWitnessUsed J).P j ≤
      (levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
        (concreteCirculationCfgWithLast dryWitnessUsed J).P j +
        (concreteCirculationCfgWithLast dryWitnessUsed J).N₀ + 2) ^ 1 *
        ((ipmQualityMinRatioFormat (solverConnectedAugmented J).m (solverPenalty J.m)
          (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
            (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) hw).limbs + 1) := by
    rw [pow_one]
    exact le_trans (by omega) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  exact lt_of_le_of_lt hle h1

/-- **Combined deep-shift model facts at the dry run:** for every dry-run input `(source, J)`,
every state `model` satisfying `ShiftLoopChainInv` and `DryChainLenGridInv`, every non-terminal
level `i < cfg.P.d`, and every `stretchP ≤ 100 * F.rangeExponent`, both
`ShiftDeepModelInv` and `ShiftDeepModelInvKFBL` hold. -/
theorem drySC_shiftDeepModelInv_of_loopInv (Psc : DrySparseCorePieces)
    (allocationCoefficient allocationDegree : ℕ)
    (hSCWordCoeff :
      Classical.choose (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed) ≤
        allocationCoefficient) :
    ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
      let wordExp := (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).wordExp
      ∀ (model : Alg2State cfg) (i : Fin (cfg.P.d + 1)) (stretchP : ℕ),
        i.val < cfg.P.d →
        Ordered.ShiftLoopChainInv cfg model.chain →
        DryChainLenGridInv J model.chain →
        stretchP ≤ 100 * F.rangeExponent →
        ShiftDeepModelInv w F.limbs F.fmt.precision wordExp stretchP model i ∧
        ShiftDeepModelInvKFBL model i := by
  intro source J hJn hJm hCost hCap hw
  exact dryShiftDeepModelInv_of_wordBound allocationCoefficient allocationDegree
    (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).wordExp
    source J hJn hJm (fun e => (hCap e).1) hw
    (drySC_deepWordLvl Psc allocationCoefficient allocationDegree hSCWordCoeff
      source J hJn hJm hCost hCap hw)

end MinCostFlow.Final.DryRun
