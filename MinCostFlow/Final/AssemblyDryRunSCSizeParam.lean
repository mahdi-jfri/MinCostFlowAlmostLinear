module

public import MinCostFlow.Final.AssemblyDryRun
import Mathlib.Tactic

/-!
# Per-circulation logical size parameter for the dry-run sparse core (`AssemblyDryRunSCSizeParam`)

Defines `drySCSizeParam J` — the logical size parameter `sizeParam` passed to the top-layer
sparse-core allocation `asmTopAlloc` on circulation `J` — and proves `drySCSizeParam_ge`: for every
valid circulation `J`, every level `i`, and every cap pair `vCap + eCap + 2 ≤ dryCapLimit`,
`levelM cfg.TP cfg.P i + cfg.N₀ + cfg.P.k + vCap + eCap + ipmQualityLimbs I.m V k + depth ≤
drySCSizeParam J`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open Chain IPM IPM.Machine Scaling

/-- Per-circulation logical size parameter `sizeParam` for the top-layer sparse-core allocation
`asmTopAlloc`: dominates `levelM cfg.TP cfg.P i + cfg.N₀ + cfg.P.k + vCap + eCap + L + depth`
for every level `i` and every cap pair with `vCap + eCap + 2 ≤ dryCapLimit dryWitnessUsed J`. -/
def drySCSizeParam (J : Circulation) : ℕ :=
  let W := dryWitnessUsed
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
    (concreteQualityBudgetWithLast W) I.m
  let cfg := concreteCirculationCfgWithLast W J
  levelM cfg.TP cfg.P 0 + cfg.N₀ + cfg.P.k + dryCapLimit W J +
    ipmQualityLimbs I.m V k + Expander.chosenL (max I.m (concreteEdgeThresholdWithLast W) ^ 2)

/-- Level sizes are bounded by `levelM TP P 0` whenever `γ_ℓ(M₀²) ≤ k`. -/
private lemma levelM_le_levelM_zero_aux {TP : SparseCoreParams} {P : ChainParams}
    (hTP : TP.Valid) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k) (i : ℕ) :
    levelM TP P i ≤ levelM TP P 0 := by
  unfold levelM
  have hk : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγnn : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hTP.2.2.1 (P.M₀ ^ 2))
  have hdiv_nn : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ) := div_nonneg hγnn hk.le
  have hdiv_le : TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ) ≤ 1 := (div_le_one hk).mpr hγk
  have hpow : (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i ≤ 1 := pow_le_one₀ hdiv_nn hdiv_le
  refine Nat.ceil_mono ?_
  have hbase_nn : 0 ≤ (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) :=
    mul_nonneg (Nat.cast_nonneg _) hγnn
  simpa [pow_zero, mul_one] using mul_le_mul_of_nonneg_left hpow hbase_nn

/-- `drySCSizeParam J` dominates `levelM cfg.TP cfg.P i + cfg.N₀ + cfg.P.k + vCap + eCap +
ipmQualityLimbs I.m V k + depth` for every level `i` and every cap pair below `dryCapLimit`. -/
theorem drySCSizeParam_ge (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (i vCap eCap : ℕ) (hlim : vCap + eCap + 2 ≤ dryCapLimit dryWitnessUsed J) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let cfg := concreteCirculationCfgWithLast W J
    levelM cfg.TP cfg.P i + cfg.N₀ + cfg.P.k + vCap + eCap +
      ipmQualityLimbs I.m V k + Expander.chosenL (max I.m (concreteEdgeThresholdWithLast W) ^ 2) ≤
      drySCSizeParam J := by
  intro W I V k cfg
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm hCapPos
  have hM : levelM cfg.TP cfg.P i ≤ levelM cfg.TP cfg.P 0 :=
    levelM_le_levelM_zero_aux hV.hTP hV.hγk i
  unfold drySCSizeParam
  dsimp only [W, I, V, k, cfg] at hM ⊢
  omega

end MinCostFlow.Final.DryRun

end
