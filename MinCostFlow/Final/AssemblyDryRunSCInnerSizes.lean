module

public import MinCostFlow.Final.AssemblyDryRunSCSizes
public import MinCostFlow.Final.AssemblyDryRunSCCoreKFBL
public import MinCostFlow.MinRatio.WireChainCoreCostKFBL
import Mathlib.Tactic

/-!
# Concrete inner chain-core sizes `dryInnerCoreSizes` and operational bounds (`AssemblyDryRunSCInnerSizes`)

Defines the concrete `DryCoreOpenSizes` instance `dryInnerCoreSizes Psc` matching the space and
cost budgets of Branch A and Branch B (`UpdateCoreOpsHypKFBL`, `WireChainCoreSpecKFBL.lean`,
`WireChainCoreCostBaseKFBL.lean`, `WireChainCoreCostKFBL.lean`):

* `dryInnerCoreUpdStepSpace`, `dryInnerCoreTermUpdSpace`, `dryInnerCoreSpaceA`,
  `dryInnerCoreSpaceB`, `dryInnerCoreSpace`: heap-independent space upper bounds for Branch A and
  Branch B, monotone in the batch length `u` (`dryInnerCoreSpace_mono`).
* `dryInnerCoreFixed`, `dryInnerCoreToolMul`, `dryInnerCoreTreeMul`: exact specializations of
  `updateCoreFixedBound`, `updateCoreToolMulBound`, and `updateCoreTreeMulBound` at the dry
  parameters.
* `dryInnerCoreSizes`: concrete `DryCoreOpenSizes` bundle.
* Operational domination lemmas discharging eight of the nine fields of `UpdateCoreOpsHypKFBL`
  unconditionally at the dry values (`dryInnerCore_lastSpaceDom`, `dryInnerCore_updStepSpaceDom`,
  `dryInnerCore_termUpdSpaceDom`, `dryInnerCore_levelCostDom`, `dryInnerCore_spaceTotalBranchA`,
  `dryInnerCore_spaceTotalBranchB`, `dryInnerCore_costTotalBranchA`,
  `dryInnerCore_costTotalBranchB`), together with the guarded level-space bound
  `dryInnerCore_levelSpaceDom_guarded` (assuming `(next.G (j + 1)).m ≤ levelM cfg.TP cfg.P (j + 1)`).
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Concrete inner chain-core step cap, space, and cost size definitions -/

/-- Multiplicative per-level step-cap factor `R j = k * B_j * (10 + 112 * B_j)` at the dry values,
where `B_j = bundleLogFactor (levelM j) N₀`. Its `d`-fold product is `PolyNat` in `I.m`
(`k^d ≤ 2^d * M₀` and `B₀^d` is `SubpolyNat`). -/
def dryStepCapR (J : Circulation) (j : ℕ) : ℕ :=
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let B := SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀
  cfg.P.k * B * (10 + 112 * B)

/-- Additive per-level step-cap term `S j` at the dry values, covering the batch-length-free parts
of `stepBundleTree_machCost` (bundle batch encodings, spanner batch charges, output-batch
deletions/insertions/split potential, and lazy initialization). -/
def dryStepCapS (J : Circulation) (j : ℕ) : ℕ :=
  let W := dryWitnessUsed
  let cfg := concreteCirculationCfgWithLast W J
  let M := levelM cfg.TP cfg.P j
  let B := SparseCore.bundleLogFactor M cfg.N₀
  let k := cfg.P.k
  let L := Expander.chosenL (cfg.P.M₀ ^ 2)
  let Γ := ⌈cfg.TP.γ_r (cfg.P.M₀ ^ 2)⌉₊
  let c_sp := W.spanConst
  3 * (k + 1) * M + (5 + 24 * B) * M +
    1080 * c_sp * Γ ^ 2 * (k + 1) ^ 2 * (115 * M + 4) * M +
    c_sp * (4 * Γ * (115 * M + 4) ^ 2 + (L + 6) * (115 * M + 4)) * M

/-- Per-level tool-cost step cap `stepCap j b = dryStepCapR J j * (dryStepCapS J j + b)` for
`UpdateCoreOpsHypKFBL` and `BranchBToolStepKFBL` at the dry values. -/
def dryInnerCoreStepCap (J : Circulation) (j b : ℕ) : ℕ :=
  dryStepCapR J j * (dryStepCapS J j + b)

/-- Heap-independent per-level non-rebuild update step space bound `updStepSpace j u` for
`UpdateCoreOpsHypKFBL.updStepSpaceDom` at level `j` and batch length `u`, using the chained
Branch-B caps `branchBCapUL`, `branchBCapBW`, and `branchBCapEW` at `dryInnerCoreStepCap J`. -/
def dryInnerCoreUpdStepSpace (Psc : DrySparseCorePieces) (J : Circulation) (j u : ℕ) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let edMul := drySCEdMul Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
  let lvlM := levelM cfg.TP cfg.P j
  let LwMax := ordLevelLwMax L dryCapExp lvlM cfg.N₀
  let sc := dryInnerCoreStepCap J
  let bWMax := branchBCapBW sc u j
  let eWMax := branchBCapEW edMul cfg sc u j
  let uLMax := branchBCapUL sc u j
  let nUMax := branchBCapUL sc u (j + 1)
  3 * drySCOp0Bound Psc I.m bWMax eWMax + 7 +
    nUMax * wireCoreLenEdgeSpace LwMax + uLMax + nUMax

/-- Non-empty terminal level-`d` update space bound `termUpdSpace` for
`UpdateCoreOpsHypKFBL.termUpdSpaceDom`. -/
def dryInnerCoreTermUpdSpace (J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let capLimit := dryCapLimit dryWitnessUsed J
  let lvlMd := levelM cfg.TP cfg.P cfg.P.d
  let LwMax := ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀
  1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
    lvlMd * wireCoreLenEdgeSpace LwMax + (2 + 2 * cfg.N₀ + 2 * lvlMd) + dryLastSpace J + 7

/-- Total space budget for Branch A (level-0 rebuild) matching
`UpdateCoreOpsHypKFBL.spaceTotalBranchA`. -/
def dryInnerCoreSpaceA (Psc : DrySparseCorePieces) (J : Circulation) (u : ℕ) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let intCapMax := dryDeepIntCapMax J
  let forestEdgeCap := dryDeepForestEdgeCap J
  (1 + 12 * cfg.P.d) + 3 * (cfg.P.d + 1) + 4 + cfg.P.d * 5 +
    (3 * intCapMax + forestEdgeCap * (2 + wireTreeSyncEditSpace L)) +
    (3 * L + u * wireRefreshOneSpace L) +
    (2 * intCapMax) + wireCompactLevel0Space cfg.N₀ intCapMax L intCapMax +
    (1 + 4 * cfg.N₀ + 2 * intCapMax) +
    (Finset.range cfg.P.d).sum (dryDeepLevelSpace Psc J) + dryLastSpace J + 5 * cfg.P.d +
    (3 * intCapMax + forestEdgeCap * (2 + wireTreeSyncEditSpace L)) + 1

/-- Total space budget for Branch B (update loop with optional suffix/terminal rebuild) matching
`UpdateCoreOpsHypKFBL.spaceTotalBranchB`. -/
def dryInnerCoreSpaceB (Psc : DrySparseCorePieces) (J : Circulation) (u : ℕ) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let intCapMax := dryDeepIntCapMax J
  let forestEdgeCap := dryDeepForestEdgeCap J
  (1 + 12 * cfg.P.d) + 3 * (cfg.P.d + 1) + 4 +
    (3 * u + u * wireTreeSyncEditSpace L) +
    (3 * L + u * wireRefreshOneSpace L) + (4 * u + 1) +
    (Finset.range cfg.P.d).sum (fun j => dryInnerCoreUpdStepSpace Psc J j u) +
    (10 * cfg.P.d + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P 0 + 10 +
      (Finset.range cfg.P.d).sum (dryDeepLevelSpace Psc J) + dryLastSpace J) +
    dryInnerCoreTermUpdSpace J +
    (2 * forestEdgeCap + forestEdgeCap * wireTreeSyncEditSpace L + 1) +
    (3 * intCapMax + 4 * forestEdgeCap + forestEdgeCap * wireTreeSyncEditSpace L + 1) +
    (5 + dryDeepFCap J + 5 * cfg.P.d)

/-- Combined inner chain-core space budget covering both Branch A and Branch B. -/
def dryInnerCoreSpace (Psc : DrySparseCorePieces) (J : Circulation) (u : ℕ) : ℕ :=
  max (dryInnerCoreSpaceA Psc J u) (dryInnerCoreSpaceB Psc J u)

/-- Inner chain-core fixed cost budget (`updateCoreFixedBound` at the dry values). -/
def dryInnerCoreFixed (Psc : DrySparseCorePieces) (J : Circulation) (u : ℕ) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let limbMul := concreteReadout2LimbMul dryWitnessUsed
  let PscP := drySCParams Psc dryCapExp limbMul
  let edMul := drySCEdMul Psc dryCapExp limbMul
  updateCoreFixedBound L dryCapExp (detectOffTreeDrainUnit L) edMul (dryLastMult J)
    (concreteEdgeThresholdWithLast dryWitnessUsed) PscP cfg.P.k cfg.P.d
    (levelM cfg.TP cfg.P 0) (levelM cfg.TP cfg.P cfg.P.d) cfg.N₀ u

/-- Inner chain-core tool multiplier (`updateCoreToolMulBound` at the dry values). -/
def dryInnerCoreToolMul (Psc : DrySparseCorePieces) (J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let limbMul := concreteReadout2LimbMul dryWitnessUsed
  let PscP := drySCParams Psc dryCapExp limbMul
  let edMul := drySCEdMul Psc dryCapExp limbMul
  updateCoreToolMulBound L dryCapExp (detectOffTreeDrainUnit L) edMul (dryLastMult J)
    PscP cfg.P.k cfg.P.d (levelM cfg.TP cfg.P 0) cfg.N₀

/-- Inner chain-core tree-update multiplier (`updateCoreTreeMulBound` at the dry values). -/
def dryInnerCoreTreeMul (J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  updateCoreTreeMulBound L (detectOffTreeDrainUnit L)

/-- Concrete `DryCoreOpenSizes` instance for the inner chain-update core. -/
def dryInnerCoreSizes (Psc : DrySparseCorePieces) : DryCoreOpenSizes where
  coreSpace := fun _ J u => dryInnerCoreSpace Psc J u
  coreFixed := fun _ J u => dryInnerCoreFixed Psc J u
  coreToolMul := fun _ J => dryInnerCoreToolMul Psc J
  coreTreeMul := fun _ J => dryInnerCoreTreeMul J

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 2. Monotonicity in the batch length `u` -/

theorem dryInnerCoreStepCap_mono (J : Circulation) (j : ℕ) :
    Monotone (dryInnerCoreStepCap J j) := by
  intro b₁ b₂ hb
  unfold dryInnerCoreStepCap
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hb _)

/-- The cap `branchBCapUL f u j` is monotone in `u` when every step `f j` is. The step `f` is a
variable here, so the kernel never unfolds a concrete step function when it checks the recursion. -/
private theorem branchBCapUL_mono_of {f : ℕ → ℕ → ℕ} (hf : ∀ j, Monotone (f j)) (j : ℕ) :
    Monotone (fun u => branchBCapUL f u j) := by
  induction j with
  | zero => intro u₁ u₂ hu; exact hu
  | succ j ih =>
    intro u₁ u₂ hu
    exact hf j (ih hu)

theorem branchBCapUL_dry_mono (J : Circulation) (j : ℕ) :
    Monotone (fun u => branchBCapUL (dryInnerCoreStepCap J) u j) :=
  branchBCapUL_mono_of (dryInnerCoreStepCap_mono J) j

theorem branchBCapBW_dry_mono (J : Circulation) (j : ℕ) :
    Monotone (fun u => branchBCapBW (dryInnerCoreStepCap J) u j) := by
  cases j with
  | zero => intro u₁ u₂ hu; simp only [branchBCapBW]; omega
  | succ j =>
    intro u₁ u₂ hu
    simp only [branchBCapBW]
    have h : branchBCapUL (dryInnerCoreStepCap J) u₁ (j + 1) ≤
        branchBCapUL (dryInnerCoreStepCap J) u₂ (j + 1) := branchBCapUL_dry_mono J (j + 1) hu
    omega

theorem branchBCapEW_dry_mono (Psc : DrySparseCorePieces) (J : Circulation) (j : ℕ) :
    Monotone (fun u =>
      branchBCapEW (drySCEdMul Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed))
        (concreteCirculationCfgWithLast dryWitnessUsed J) (dryInnerCoreStepCap J) u j) := by
  induction j with
  | zero => intro u₁ u₂ hu; simp only [branchBCapEW]; omega
  | succ j ih =>
    intro u₁ u₂ hu
    simp only [branchBCapEW]
    apply Nat.mul_le_mul_left
    have h1 : branchBCapUL (dryInnerCoreStepCap J) u₁ (j + 1) ≤
        branchBCapUL (dryInnerCoreStepCap J) u₂ (j + 1) := branchBCapUL_dry_mono J (j + 1) hu
    have h2 : branchBCapBW (dryInnerCoreStepCap J) u₁ j ≤
        branchBCapBW (dryInnerCoreStepCap J) u₂ j := branchBCapBW_dry_mono J j hu
    have h3 : branchBCapEW (drySCEdMul Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed))
        (concreteCirculationCfgWithLast dryWitnessUsed J) (dryInnerCoreStepCap J) u₁ j ≤
        branchBCapEW (drySCEdMul Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed))
        (concreteCirculationCfgWithLast dryWitnessUsed J) (dryInnerCoreStepCap J) u₂ j := ih hu
    exact Nat.add_le_add h1 (Nat.mul_le_mul_right _ (by omega))

theorem dryInnerCoreUpdStepSpace_mono (Psc : DrySparseCorePieces) (J : Circulation) (j : ℕ) :
    Monotone (dryInnerCoreUpdStepSpace Psc J j) := by
  intro u₁ u₂ hu
  unfold dryInnerCoreUpdStepSpace
  dsimp only
  have hb : branchBCapBW (dryInnerCoreStepCap J) u₁ j ≤
      branchBCapBW (dryInnerCoreStepCap J) u₂ j := branchBCapBW_dry_mono J j hu
  have he : branchBCapEW (drySCEdMul Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed))
      (concreteCirculationCfgWithLast dryWitnessUsed J) (dryInnerCoreStepCap J) u₁ j ≤
      branchBCapEW (drySCEdMul Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed))
      (concreteCirculationCfgWithLast dryWitnessUsed J) (dryInnerCoreStepCap J) u₂ j :=
    branchBCapEW_dry_mono Psc J j hu
  have huL : branchBCapUL (dryInnerCoreStepCap J) u₁ j ≤
      branchBCapUL (dryInnerCoreStepCap J) u₂ j := branchBCapUL_dry_mono J j hu
  have hnU : branchBCapUL (dryInnerCoreStepCap J) u₁ (j + 1) ≤
      branchBCapUL (dryInnerCoreStepCap J) u₂ (j + 1) := branchBCapUL_dry_mono J (j + 1) hu
  have hop := drySCOp0Bound_mono Psc (M := (solverConnectedAugmented J).m) hb he
  have hmul := Nat.mul_le_mul_right
    (wireCoreLenEdgeSpace (ordLevelLwMax
      (ipmQualityLimbs (solverConnectedAugmented J).m (solverPenalty J.m)
        (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m))
      dryCapExp
      (levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
        (concreteCirculationCfgWithLast dryWitnessUsed J).P j)
      (concreteCirculationCfgWithLast dryWitnessUsed J).N₀)) hnU
  linarith only [hop, hmul, huL, hnU]

theorem dryInnerCoreSpaceA_mono (Psc : DrySparseCorePieces) (J : Circulation) :
    Monotone (dryInnerCoreSpaceA Psc J) := by
  intro u₁ u₂ hu
  unfold dryInnerCoreSpaceA
  dsimp only
  set L := ipmQualityLimbs (solverConnectedAugmented J).m (solverPenalty J.m)
    (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m)
  have h1 := Nat.mul_le_mul_right (wireRefreshOneSpace L) hu
  omega

theorem dryInnerCoreSpaceB_mono (Psc : DrySparseCorePieces) (J : Circulation) :
    Monotone (dryInnerCoreSpaceB Psc J) := by
  intro u₁ u₂ hu
  unfold dryInnerCoreSpaceB
  dsimp only
  set L := ipmQualityLimbs (solverConnectedAugmented J).m (solverPenalty J.m)
    (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m)
  have h1 := Nat.mul_le_mul_right (wireTreeSyncEditSpace L) hu
  have h2 := Nat.mul_le_mul_right (wireRefreshOneSpace L) hu
  have h3 : (Finset.range (concreteCirculationCfgWithLast dryWitnessUsed J).P.d).sum
      (fun j => dryInnerCoreUpdStepSpace Psc J j u₁) ≤
      (Finset.range (concreteCirculationCfgWithLast dryWitnessUsed J).P.d).sum
      (fun j => dryInnerCoreUpdStepSpace Psc J j u₂) :=
    Finset.sum_le_sum fun j _ => dryInnerCoreUpdStepSpace_mono Psc J j hu
  omega

theorem dryInnerCoreSpace_mono (Psc : DrySparseCorePieces) (J : Circulation) :
    Monotone (dryInnerCoreSpace Psc J) := by
  intro u₁ u₂ hu
  exact max_le_max (dryInnerCoreSpaceA_mono Psc J hu) (dryInnerCoreSpaceB_mono Psc J hu)

/-! ## 3. Operational domination lemmas for `UpdateCoreOpsHypKFBL` -/

/-- Guarded `levelSpaceDom` at the dry values (assuming `(next.G (j + 1)).m ≤ levelM (j + 1)`). -/
theorem dryInnerCore_levelSpaceDom_guarded (Psc : DrySparseCorePieces) (J : Circulation)
    {w : ℕ} (fmt : Num.Format w)
    (next : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P)
    (j gB lB grB oB h : ℕ)
    (_hj : j < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    (hFacts : ShiftLoopLevelFacts (concreteCirculationCfgWithLast dryWitnessUsed J) next)
    (hNextM : (next.G (j + 1)).m ≤
      levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
        (concreteCirculationCfgWithLast dryWitnessUsed J).P (j + 1)) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let limbMul := concreteReadout2LimbMul dryWitnessUsed
    ordLevelSpace L dryCapExp (dryCapLimit dryWitnessUsed J)
      (drySCAlloc Psc dryCapExp limbMul J 6 [gB, lB, grB, oB, cfg.P.k, next.lvlM j, next.N₀, L,
        fmt.precision, Expander.chosenL (cfg.P.M₀ ^ 2), h])
      (next.lvlM j) next.N₀ (next.G (j + 1)).m ≤ dryDeepLevelSpace Psc J j := by
  intro I V k L cfg limbMul
  obtain ⟨_, hLvlM, hN0, _⟩ := hFacts
  rw [hLvlM, hN0]
  have hInitEq := drySCAlloc_init_eq_dryCoreInitSpace Psc J j gB lB grB oB fmt.precision
    (Expander.chosenL (cfg.P.M₀ ^ 2)) h
  change ordLevelSpace L dryCapExp (dryCapLimit dryWitnessUsed J)
    (drySCAlloc Psc dryCapExp limbMul J 6 [gB, lB, grB, oB, cfg.P.k, levelM cfg.TP cfg.P j,
      cfg.N₀, L, fmt.precision, Expander.chosenL (cfg.P.M₀ ^ 2), h])
    (levelM cfg.TP cfg.P j) cfg.N₀ (next.G (j + 1)).m ≤ _
  rw [hInitEq]
  have hmul := Nat.mul_le_mul_right
    (wireCoreLenEdgeSpace (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P j) cfg.N₀)) hNextM
  unfold dryDeepLevelSpace ordLevelSpace
  dsimp only [I, V, k, L, cfg, limbMul] at hmul ⊢
  omega

/-- Discharges `UpdateCoreOpsHypKFBL.lastSpaceDom` at `lastAlloc := fun _ _ => dryLastSpace J`. -/
theorem dryInnerCore_lastSpaceDom (J : Circulation) (gB lB L P h : ℕ) :
    (fun (_ : ℕ) (_ : List ℕ) => dryLastSpace J) 1 [gB, lB, L, P, h] ≤ dryLastSpace J :=
  le_rfl

/-- Discharges `UpdateCoreOpsHypKFBL.updStepSpaceDom` at `dryInnerCoreUpdStepSpace` and
`dryInnerCoreStepCap`. -/
theorem dryInnerCore_updStepSpaceDom (Psc : DrySparseCorePieces) (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (idx uLen coreH gB bPtr bW ePtr eW lB h nU uL : ℕ) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let limbMul := concreteReadout2LimbMul dryWitnessUsed
    let edMul := drySCEdMul Psc dryCapExp limbMul
    let lvlM := levelM cfg.TP cfg.P idx
    let LwMax := ordLevelLwMax L dryCapExp lvlM cfg.N₀
    bW ≤ branchBCapBW (dryInnerCoreStepCap J) uLen idx →
    eW ≤ branchBCapEW edMul cfg (dryInnerCoreStepCap J) uLen idx →
    nU ≤ branchBCapUL (dryInnerCoreStepCap J) uLen (idx + 1) →
    uL ≤ branchBCapUL (dryInnerCoreStepCap J) uLen idx →
    3 * drySCAlloc Psc dryCapExp limbMul J 0 [coreH, gB, bPtr, bW, ePtr, eW, lB, lB, h] + 7 +
      nU * wireCoreLenEdgeSpace LwMax + uL + nU ≤
      dryInnerCoreUpdStepSpace Psc J idx uLen := by
  intro I V k L cfg limbMul edMul lvlM LwMax hbW heW hnU huL
  have hop0 : drySCAlloc Psc dryCapExp limbMul J 0 [coreH, gB, bPtr, bW, ePtr, eW, lB, lB, h] ≤
      drySCOp0Bound Psc I.m (branchBCapBW (dryInnerCoreStepCap J) uLen idx)
        (branchBCapEW edMul cfg (dryInnerCoreStepCap J) uLen idx) :=
    (drySCAlloc_op0_le_bound Psc J hJn hJm hCapPos coreH gB bPtr bW ePtr eW lB lB h).trans
      (drySCOp0Bound_mono Psc hbW heW)
  have hmul := Nat.mul_le_mul_right (wireCoreLenEdgeSpace LwMax) hnU
  unfold dryInnerCoreUpdStepSpace
  dsimp only [I, V, k, L, cfg, limbMul, edMul, lvlM, LwMax] at hnU huL hop0 hmul ⊢
  omega

/-- Discharges `UpdateCoreOpsHypKFBL.termUpdSpaceDom` at `dryInnerCoreTermUpdSpace`. -/
theorem dryInnerCore_termUpdSpaceDom (J : Circulation) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let capLimit := dryCapLimit dryWitnessUsed J
    let lvlMd := levelM cfg.TP cfg.P cfg.P.d
    let LwMax := ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀
    1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
      lvlMd * wireCoreLenEdgeSpace LwMax + (2 + 2 * cfg.N₀ + 2 * lvlMd) + dryLastSpace J + 7 ≤
      dryInnerCoreTermUpdSpace J :=
  le_rfl

/-- Discharges `UpdateCoreOpsHypKFBL.levelCostDom` at `updateCoreRebuildLevelCost`. -/
theorem dryInnerCore_levelCostDom (Psc : DrySparseCorePieces) (J : Circulation)
    (next : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P) (j : ℕ) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
    updateCoreRebuildLevelCost L dryCapExp cfg PscP next j ≤
      updateCoreRebuildLevelCost L dryCapExp cfg PscP next j :=
  le_rfl

/-- Discharges `UpdateCoreOpsHypKFBL.spaceTotalBranchA` at `dryInnerCoreSpace`. -/
theorem dryInnerCore_spaceTotalBranchA (Psc : DrySparseCorePieces) (J : Circulation)
    (n rootECap uLen mNew : ℕ) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let intCapMax := dryDeepIntCapMax J
    let forestEdgeCap := dryDeepForestEdgeCap J
    n ≤ cfg.N₀ → rootECap ≤ intCapMax → mNew ≤ intCapMax →
    (1 + 12 * cfg.P.d) + 3 * (cfg.P.d + 1) + 4 + cfg.P.d * 5 +
      (3 * intCapMax + forestEdgeCap * (2 + wireTreeSyncEditSpace L)) +
      (3 * L + uLen * wireRefreshOneSpace L) +
      (2 * intCapMax) + wireCompactLevel0Space n rootECap L mNew +
      (1 + 4 * n + 2 * rootECap) +
      (Finset.range cfg.P.d).sum (dryDeepLevelSpace Psc J) + dryLastSpace J + 5 * cfg.P.d +
      (3 * intCapMax + forestEdgeCap * (2 + wireTreeSyncEditSpace L)) + 1 ≤
      dryInnerCoreSpace Psc J uLen := by
  intro I V k L cfg intCapMax forestEdgeCap hn hroot hmNew
  have hComp : wireCompactLevel0Space n rootECap L mNew ≤
      wireCompactLevel0Space cfg.N₀ intCapMax L intCapMax := by
    unfold wireCompactLevel0Space dynGraphSize
    have hmul := Nat.mul_le_mul_right L hroot
    omega
  refine le_trans ?_ (le_max_left _ _)
  unfold dryInnerCoreSpaceA
  dsimp only [I, V, k, L, cfg, intCapMax, forestEdgeCap] at hn hroot hmNew hComp ⊢
  omega

/-- Discharges `UpdateCoreOpsHypKFBL.spaceTotalBranchB` at `dryInnerCoreSpace`. -/
theorem dryInnerCore_spaceTotalBranchB (Psc : DrySparseCorePieces) (J : Circulation) (uLen : ℕ) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let intCapMax := dryDeepIntCapMax J
    let forestEdgeCap := dryDeepForestEdgeCap J
    (1 + 12 * cfg.P.d) + 3 * (cfg.P.d + 1) + 4 +
      (3 * uLen + uLen * wireTreeSyncEditSpace L) +
      (3 * L + uLen * wireRefreshOneSpace L) + (4 * uLen + 1) +
      (Finset.range cfg.P.d).sum (fun j => dryInnerCoreUpdStepSpace Psc J j uLen) +
      (10 * cfg.P.d + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P 0 + 10 +
        (Finset.range cfg.P.d).sum (dryDeepLevelSpace Psc J) + dryLastSpace J) +
      dryInnerCoreTermUpdSpace J +
      (2 * forestEdgeCap + forestEdgeCap * wireTreeSyncEditSpace L + 1) +
      (3 * intCapMax + 4 * forestEdgeCap + forestEdgeCap * wireTreeSyncEditSpace L + 1) +
      (5 + dryDeepFCap J + 5 * cfg.P.d) ≤
      dryInnerCoreSpace Psc J uLen :=
  le_max_right _ _

/-- Discharges `UpdateCoreOpsHypKFBL.costTotalBranchA` at `dryInnerCoreFixed` and
`dryInnerCoreToolMul`. -/
theorem dryInnerCore_costTotalBranchA (Psc : DrySparseCorePieces) (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    {w : ℕ}
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤ w) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast W J
    let G := namedInstance I
    let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul W)
    let drainUnit := detectOffTreeDrainUnit L
    let mThresh := concreteEdgeThresholdWithLast W
    ∀ (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ)
      (intCap rootECap : ℕ),
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let U_int := tr.2.2.2.2
      let modelPre := alg2PreResetState cfg model U gVec lVec
      let n := model.extG.n
      let mNew := (modelPre.chain.G 0).m
      let sumOld := graphListEdgeSum (chainSuffixForests model.chain 0)
      let sumNew := graphListEdgeSum (chainSuffixForests modelPre.chain 0)
      0 < cfg.P.d →
      intRebuildThreshold cfg.P model.chain.N₀ 0 < model.chain.updCount 0 + U_int.length →
      FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh →
      RefreshBatch model.extG U →
      UpdateCoreModelInvKFBL model U gVec lVec →
      model.extG.m = I.m →
      rootECap ≤ intCap →
      intCap ≤ initTargetCap cfg G →
      G.E.sup id ≤ G.m →
      G.m = I.m →
      cfg.P.M₀ ≤ I.m + mThresh →
      cfg.P.d * (PscP.readout + 48) +
        (230 * (cfg.P.d + 1) + 85 * sumOld + 300) +
        sumOld * (wireTreeSyncEditCost L drainUnit + 2) +
        (U.length * (wireRefreshOneCost L + 120) + 71 * L + 220) +
        (670 * (4 * U.length + 1) + 30) +
        (U.length * (17 * L + 70) + 80) +
        (85 * intCap + 40 * I.m + 110) +
        wireCompactLevel0Cost n rootECap intCap L mNew +
        (150 * rootECap + 60 * n + 120) + 150 +
        (Finset.range cfg.P.d).sum
          (fun j => updateCoreRebuildLevelCost L dryCapExp cfg PscP modelPre.chain j + 9) +
        dryLastMult J * (cfg.L.cost (modelPre.chain.G cfg.P.d) + 1) +
        cfg.P.d * (PscP.readout + 48) + 40 * cfg.P.d +
        (230 * (cfg.P.d + 1) + 85 * sumNew + 260) +
        sumNew * (wireTreeSyncEditCost L drainUnit + 2) +
        (80 * mNew + mNew * drainUnit + 120) + 1500 ≤
        dryInnerCoreFixed Psc J U.length +
          dryInnerCoreToolMul Psc J * (modelPre.chain.totalRuntime - model.chain.totalRuntime) := by
  intro W I V k L cfg G PscP drainUnit mThresh
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm hCapPos
  have hT := concreteCirculationCfgWithLast_T_eq_progTool W sparsifyImplUsed rfl rfl rfl J hw
  intro model U gVec lVec intCap rootECap tr U_int modelPre n mNew sumOld sumNew
    hdPos hOver0 hFresh hRef hModelK hExtM hRLeI hIntLe hGSup hGM hM0Le
  exact updateCore_costTotalBranchA_mach
    (dryLSFInitUsed L (ipmQualityMinRatioFormat I.m V k hw).fmt.precision) dryCLsstUsed
    (Expander.chosenL (max I.m mThresh ^ 2))
    (fun _ => canonicalSparsify sparsifyImplUsed) (canonicalSparsifyParams sparsifyImplUsed)
    (dsAmortConst sparsifyImplUsed)
    L dryCapExp drainUnit (drySCEdMul Psc dryCapExp (concreteReadout2LimbMul W))
    (dryLastMult J) mThresh I.m cfg G PscP hT hV.hTP hV.hγk
    model U gVec lVec intCap rootECap hdPos hOver0 hFresh hRef hModelK hExtM hRLeI hIntLe
    hGSup hGM hM0Le

/-- Discharges `UpdateCoreOpsHypKFBL.costTotalBranchB` at `dryInnerCoreFixed` and
`dryInnerCoreToolMul`. -/
theorem dryInnerCore_costTotalBranchB (Psc : DrySparseCorePieces) (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    {w : ℕ}
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤ w) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast W J
    let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul W)
    let drainUnit := detectOffTreeDrainUnit L
    let edMul := drySCEdMul Psc dryCapExp (concreteReadout2LimbMul W)
    ∀ (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ)
      (bW eW nextULen Δc : ℕ → ℕ) (i₀ : ℕ),
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let U_int := tr.2.2.2.2
      let modelPre := alg2PreResetState cfg model U gVec lVec
      let d := cfg.P.d
      let B₀ := SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀
      let LwMax₀ := ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀
      0 < d → i₀ ≤ d →
      ¬ (intRebuildThreshold cfg.P model.chain.N₀ 0 < model.chain.updCount 0 + U_int.length) →
      UpdateCoreModelInvKFBL model U gVec lVec →
      bW 0 ≤ 4 * U.length + 1 →
      eW 0 ≤ 10 * U.length + 1 →
      (∀ j < i₀, nextULen j ≤ Δc j ∧ bW (j + 1) ≤ 6 * Δc j + 1 ∧
        eW (j + 1) ≤ edMul * (Δc j + (bW j + eW j + 1) * B₀)) →
      let prefixCost :=
        (134 * U.length + 65) + U.length * (wireTreeSyncEditCost L drainUnit + 2) +
        (U.length * (wireRefreshOneCost L + 120) + 71 * L + 220) +
        (670 * (4 * U.length + 1) + 30) +
        (U.length * (17 * L + 70) + 80) +
        (Finset.range i₀).sum (fun j =>
          updateCoreNoRebuildStepCost L dryCapExp PscP cfg.P.k (levelM cfg.TP cfg.P j) cfg.N₀
            (bW j) (eW j) (nextULen j) (Δc j) + 30) +
        (130 * U.length + U.length * drainUnit + 100) + 100 * d + 1000
      let rhs := dryInnerCoreFixed Psc J U.length +
        dryInnerCoreToolMul Psc J * (modelPre.chain.totalRuntime - model.chain.totalRuntime)
      ((0 < i₀ → i₀ < d →
        (∀ j, i₀ ≤ j → j < d → ∃ ℓj gj ordj,
          modelPre.chain.scState j =
            cfg.T.initOrd cfg.P.k (modelPre.chain.lvlM j) modelPre.chain.N₀ (modelPre.chain.G j)
              ℓj gj ordj) →
        (Finset.range i₀).sum Δc +
          (Finset.Ico i₀ d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) +
          cfg.L.cost (modelPre.chain.G d) ≤
          modelPre.chain.totalRuntime - model.chain.totalRuntime →
        (model.chain.G i₀).m ≤ (modelPre.chain.G i₀).m + bW i₀ →
        let sumOldSuf := graphListEdgeSum (chainSuffixForests model.chain i₀)
        let sumNewSuf := graphListEdgeSum (chainSuffixForests modelPre.chain i₀)
        prefixCost +
          670 * bW i₀ +
          PscP.mul * (2 * (modelPre.chain.G i₀).n + 2 * (modelPre.chain.G i₀).m + 2) * B₀ +
          2 * PscP.readout + 200 +
          (Finset.Ico i₀ d).sum
            (fun j => updateCoreRebuildLevelCost L dryCapExp cfg PscP modelPre.chain j + 9) +
          dryLastMult J * (cfg.L.cost (modelPre.chain.G d) + 1) +
          2 * d * (PscP.readout + 68) +
          (230 * (d + 1) + 85 * (sumOldSuf + sumNewSuf) + 260) +
          70 * (sumOldSuf + sumNewSuf) + 300 ≤ rhs) ∧
       (i₀ = d →
        (Finset.range d).sum Δc + cfg.L.cost (modelPre.chain.G d) ≤
          modelPre.chain.totalRuntime - model.chain.totalRuntime →
        let Gd := modelPre.chain.G d
        let oldLastF := (model.chain.lastLSFs model.chain.lastBran).F.F
        let newLastF := (modelPre.chain.lastLSFs modelPre.chain.lastBran).F.F
        prefixCost +
          3 * PscP.readout + copyGraphLiveCost Gd.n Gd.m +
          Gd.m * (wireCoreLenEdgeCost LwMax₀ + 30) +
          PscP.mul * (2 * Gd.n + 2 * Gd.m + 2) * B₀ +
          dryLastMult J * (cfg.L.cost Gd + 1) +
          (230 * 2 + 85 * (oldLastF.m + newLastF.m) + 260) +
          70 * (oldLastF.m + newLastF.m) + 400 ≤ rhs) ∧
       (i₀ = d →
        (Finset.range d).sum Δc ≤ modelPre.chain.totalRuntime - model.chain.totalRuntime →
        prefixCost + 600 ≤ rhs)) := by
  intro W I V k L cfg PscP drainUnit edMul
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm hCapPos
  have hT := concreteCirculationCfgWithLast_T_eq_progTool W sparsifyImplUsed rfl rfl rfl J hw
  intro model U gVec lVec bW eW nextULen Δc i₀ tr U_int modelPre d B₀ LwMax₀
    hdPos hiLe _ hModelK hb0 he0 hStep
  exact updateCore_costTotalBranchB_mach
    (dryLSFInitUsed L (ipmQualityMinRatioFormat I.m V k hw).fmt.precision) dryCLsstUsed
    (Expander.chosenL (max I.m (concreteEdgeThresholdWithLast W) ^ 2))
    (fun _ => canonicalSparsify sparsifyImplUsed) (canonicalSparsifyParams sparsifyImplUsed)
    (dsAmortConst sparsifyImplUsed)
    L dryCapExp drainUnit edMul (dryLastMult J) (concreteEdgeThresholdWithLast W) cfg PscP
    hT hV.hTP hV.hγk model U gVec lVec bW eW nextULen Δc i₀ hdPos hiLe hModelK hb0 he0 hStep

end MinCostFlow.Final.DryRun

end
