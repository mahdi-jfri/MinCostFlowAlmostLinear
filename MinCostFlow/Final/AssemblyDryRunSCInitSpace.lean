module

public import MinCostFlow.Final.AssemblyDryRunSCCoreKFBL
import Mathlib.Tactic

/-!
# Unconditional init space bound for the sparse core (`AssemblyDryRunSCInitSpace`)

Proves `DrySCInitSpaceLe` (`Final/AssemblyDryRunSC.lean`) unconditionally for `drySparseCoreCode`
from the top-layer allocation bound `SparseCoreInitAllocBound` carried through the sparse-core
bridge (`AssemblyTopProcs.lean`, `AssemblyBridge.lean`, `AssemblyCodeCarry.lean`).

On op `6` (init), the top-layer allocation `asmTopAlloc` reads only `(k, M, N, L)` — independent
of all pointer arguments, `P_fp`, and `depth` — and is bounded by a fixed input-independent
`PolyBound` evaluated at `k + M + N + L`.

* `drySCAlloc_initBound`: exports `SparseCoreInitAllocBound (drySCAlloc Psc capExp limbMul)`.
* `drySCInitPoly`: the input-independent `PolyBound` dominating op `6` of `drySCAlloc`.
* `dryCoreInitSpace`: the concrete per-level init space bound for `drySparseCoreCode` at circulation
  `J` and level `i` (namely `drySCAlloc` at `[0, 0, 0, 0, cfg.P.k, levelM i, cfg.N₀, F.limbs, 0, 0, 0]`).
* `drySC_hInitSpaceLe_proved`: proves `DrySCInitSpaceLe` for `dryCoreInitSpace Psc J` with zero
  extra hypotheses.
* `dryCoreInitSpace_le_poly` and `drySC_hInitSpaceLe_poly`: proves that `dryCoreInitSpace Psc J i`
  (and hence `drySCAlloc ... 6`) is bounded by `(drySCInitPoly ...).eval (k + levelM i + N₀ + L)`,
  allowing the solver's `B.initSpace` and `sz.initSpace'` to bound `initConcreteSpace` polynomially.
* `DrySCInitSizeHyps`, `DrySCInitSizeHyps.toOpenHyps`, and `theorem_1_1_dry_run_sc_initSpace`:
  discharges `coreInitSpace` and `hInitSpaceLe` from `DrySCInitOpenHyps`, leaving only the three
  size bounds into `sz` (`hSpaceLe`, `hFixedLe`, `hMulLe`) evaluated at `dryCoreInitSpace`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## Init allocation bound extracted from the sparse-core bridge -/

/-- `drySCAllocAt Psc capExp limbMul` satisfies `SparseCoreUpdateRestartAllocBound`: op `6` is
independent of `sizeParam`, op `1` is bounded by `P1.eval sizeParam`, and op `0` is bounded by
`P0.eval (sizeParam + words + editWords)`. -/
theorem drySCAllocAt_updateRestartBound (Psc : DrySparseCorePieces) (capExp limbMul : ℕ) :
    SparseCoreUpdateRestartAllocBound (drySCAllocAt Psc capExp limbMul) :=
  (Classical.choose_spec (Classical.choose_spec
    ((Classical.choose_spec (drySC_bridged_exists Psc)).2 capExp limbMul))).2.2.1

/-- `drySCAllocAt Psc capExp limbMul sizeParam` satisfies `SparseCoreInitAllocBound`: on op `6`,
it depends only on `(k, M, N, L)` and is bounded by a `PolyBound` in `k + M + N + L`. -/
theorem drySCAllocAt_initBound (Psc : DrySparseCorePieces) (capExp limbMul sizeParam : ℕ) :
    SparseCoreInitAllocBound (drySCAllocAt Psc capExp limbMul sizeParam) :=
  (Classical.choose_spec (Classical.choose_spec
    ((Classical.choose_spec (drySC_bridged_exists Psc)).2 capExp limbMul))).2.1 sizeParam

/-- `drySCAlloc Psc capExp limbMul J` satisfies `SparseCoreInitAllocBound`. -/
theorem drySCAlloc_initBound (Psc : DrySparseCorePieces) (capExp limbMul : ℕ) (J : Circulation) :
    SparseCoreInitAllocBound (drySCAlloc Psc capExp limbMul J) :=
  drySCAllocAt_initBound Psc capExp limbMul (drySCSizeParam J)

/-- Input-independent `PolyBound` dominating `drySCAlloc Psc capExp limbMul J 6` on any
11-argument init list `[g, l, gr, o, k, M, N, L, P_fp, depth, h]`, evaluated at `k + M + N + L`. -/
def drySCInitPoly (Psc : DrySparseCorePieces) (capExp limbMul : ℕ) : PolyBound :=
  Classical.choose (drySCAllocAt_initBound Psc capExp limbMul 0).2

theorem drySCAlloc_init_le_poly (Psc : DrySparseCorePieces) (capExp limbMul : ℕ) (J : Circulation)
    (g l gr o k M N L P_fp depth h : ℕ) :
    drySCAlloc Psc capExp limbMul J 6 [g, l, gr, o, k, M, N, L, P_fp, depth, h] ≤
      (drySCInitPoly Psc capExp limbMul).eval (k + M + N + L) := by
  change drySCAllocAt Psc capExp limbMul (drySCSizeParam J) 6 _ ≤ _
  rw [(drySCAllocAt_updateRestartBound Psc capExp limbMul).1 (drySCSizeParam J) 0]
  exact Classical.choose_spec (drySCAllocAt_initBound Psc capExp limbMul 0).2
    g l gr o k M N L P_fp depth h

/-! ## Concrete `coreInitSpace` and unconditional proof of `DrySCInitSpaceLe` -/

/-- Concrete per-level sparse-core init space bound for `drySparseCoreCode` on circulation `J`
at level `i`: evaluates `drySCAlloc` at op `6` with the level's `(k, levelM i, N₀, F.limbs)` and
zeroed pointer/precision/depth slots. -/
def dryCoreInitSpace (Psc : DrySparseCorePieces) (J : Circulation) (i : ℕ) : ℕ :=
  let W := dryWitnessUsed
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
    (concreteQualityBudgetWithLast W) I.m
  let cfg := concreteCirculationCfgWithLast W J
  let limbMul := concreteReadout2LimbMul W
  drySCAlloc Psc dryCapExp limbMul J 6
    [0, 0, 0, 0, cfg.P.k, levelM cfg.TP cfg.P i, cfg.N₀, ipmQualityLimbs I.m V k, 0, 0, 0]

/-- Exact equality between op `6` of `drySCAlloc` on any pointer/precision/depth init arguments
and `dryCoreInitSpace Psc J i`. -/
theorem drySCAlloc_init_eq_dryCoreInitSpace (Psc : DrySparseCorePieces) (J : Circulation)
    (i g l gr o P_fp depth h : ℕ) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let cfg := concreteCirculationCfgWithLast W J
    let limbMul := concreteReadout2LimbMul W
    drySCAlloc Psc dryCapExp limbMul J 6
        [g, l, gr, o, cfg.P.k, levelM cfg.TP cfg.P i, cfg.N₀, ipmQualityLimbs I.m V k, P_fp, depth, h] =
      dryCoreInitSpace Psc J i :=
  (drySCAlloc_initBound Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed) J).1
    g l gr o _ _ _ _ P_fp depth h

/-- Polynomial upper bound on `dryCoreInitSpace Psc J i` in terms of `k + levelM i + N₀ + L`,
with an input-independent `PolyBound` (`drySCInitPoly`). -/
theorem dryCoreInitSpace_le_poly (Psc : DrySparseCorePieces) (J : Circulation) (i : ℕ) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let cfg := concreteCirculationCfgWithLast W J
    dryCoreInitSpace Psc J i ≤
      (drySCInitPoly Psc dryCapExp (concreteReadout2LimbMul W)).eval
        (cfg.P.k + levelM cfg.TP cfg.P i + cfg.N₀ + ipmQualityLimbs I.m V k) :=
  drySCAlloc_init_le_poly Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed) J
    0 0 0 0 _ _ _ _ 0 0 0

/-- **Unconditional proof of `DrySCInitSpaceLe` for `drySparseCoreCode`**: at every dry-run input
and every level `i < cfg.P.d`, op `6` of `drySCAlloc` on any init arguments is at most
`dryCoreInitSpace Psc J i` (in fact equal to it). -/
theorem drySC_hInitSpaceLe_proved (Psc : DrySparseCorePieces)
    (allocationCoefficient allocationDegree : ℕ) :
    ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun _source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let depth := Expander.chosenL (max I.m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2)
      let limbMul := concreteReadout2LimbMul dryWitnessUsed
      DrySCInitSpaceLe (drySCAlloc Psc dryCapExp limbMul J) (dryCoreInitSpace Psc J) cfg.P.d
        cfg.P.k cfg.N₀ F.limbs F.fmt.precision depth (levelM cfg.TP cfg.P) := by
  intro _source J _hJn _hJm _hCost _hCap _hw
  dsimp only
  intro i _hi g l gr o h
  exact le_of_eq (drySCAlloc_init_eq_dryCoreInitSpace Psc J i g l gr o _ _ h)

/-- Polynomial variant of `drySC_hInitSpaceLe_proved`: `DrySCInitSpaceLe` also holds with
`coreInitSpace i := (drySCInitPoly ...).eval (cfg.P.k + levelM i + cfg.N₀ + F.limbs)`. -/
theorem drySC_hInitSpaceLe_poly (Psc : DrySparseCorePieces)
    (allocationCoefficient allocationDegree : ℕ) :
    ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun _source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let depth := Expander.chosenL (max I.m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2)
      let limbMul := concreteReadout2LimbMul dryWitnessUsed
      DrySCInitSpaceLe (drySCAlloc Psc dryCapExp limbMul J)
        (fun i => (drySCInitPoly Psc dryCapExp limbMul).eval
          (cfg.P.k + levelM cfg.TP cfg.P i + cfg.N₀ + F.limbs))
        cfg.P.d cfg.P.k cfg.N₀ F.limbs F.fmt.precision depth (levelM cfg.TP cfg.P) := by
  intro _source J _hJn _hJm _hCost _hCap _hw
  dsimp only
  intro i _hi g l gr o h
  exact drySCAlloc_init_le_poly Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed) J
    g l gr o _ _ _ _ _ _ h

/-! ## Discharging `hInitSpaceLe` from `DrySCInitOpenHyps` -/

/-- The three other Init size bounds into `sz` (`hSpaceLe`, `hFixedLe`, `hMulLe`) once
`coreInitSpace` is fixed to `dryCoreInitSpace Psc J` and `hInitSpaceLe` is discharged by
`drySC_hInitSpaceLe_proved`. -/
structure DrySCInitSizeHyps (Psc : DrySparseCorePieces)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (sz : Circulation → Circulation → WiredInnerSizes) : Prop where
  hSpaceLe : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    initConcreteSpace I.m (namedInstance I).n F.limbs cfg.P.d (dryParamSpace source J) dryCapExp
      (dryCapLimit dryWitnessUsed J) (dryLastSpace J)
      (LinkCut.PathProg.arenaEnd 0 (namedInstance I).n F.limbs)
      (20 * LinkCut.PathProg.treeLimbs F.limbs + 100)
      (dryCoreInitSpace Psc J) (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀ ≤
    (sz source J).initSpace'
  hFixedLe : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let limbMul := concreteReadout2LimbMul dryWitnessUsed
    initConcreteFixed I.m (namedInstance I).n F.limbs cfg.P.d (dryParamCost source J) dryCapExp
      (dryCapLimit dryWitnessUsed J) (dryLastMult J) LinkCut.PathProg.pathC
      (drySCParams Psc dryCapExp limbMul)
      (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀ ≤
    (sz source J).initFixed
  hMulLe : ∀ source J,
    max (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).mul (dryLastMult J) ≤
      (sz source J).toolMul

/-- Builds `DrySCInitOpenHyps` from `DrySCInitSizeHyps`, instantiating `coreInitSpace` to
`dryCoreInitSpace Psc J` and discharging `hInitSpaceLe` via `drySC_hInitSpaceLe_proved`. -/
def DrySCInitSizeHyps.toOpenHyps {Psc : DrySparseCorePieces} {rem : SolverInnerOpenNoParam}
    {B : OrdSolverInnerBounds} {hB : InnerBoundsHyp B}
    {sz : Circulation → Circulation → WiredInnerSizes}
    (H : DrySCInitSizeHyps Psc B hB sz) :
    DrySCInitOpenHyps Psc rem B hB sz where
  coreInitSpace := fun _ J => dryCoreInitSpace Psc J
  hInitSpaceLe := drySC_hInitSpaceLe_proved Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
  hSpaceLe := H.hSpaceLe
  hFixedLe := H.hFixedLe
  hMulLe := H.hMulLe

/-- **Theorem 1.1 (page 2), second dry run with `hInitSpaceLe` discharged.**
Calls `theorem_1_1_dry_run_sc_open` with `coreInitSpace := fun _ J => dryCoreInitSpace Psc J` and
`drySC_hInitSpaceLe_proved`, leaving only the three Init size bounds `DrySCInitSizeHyps` alongside
`Psc`, `rem`, `B`, `sz`, and `DrySCSolverHyps`. -/
theorem theorem_1_1_dry_run_sc_initSpace (Psc : DrySparseCorePieces)
    (rem : SolverInnerOpenNoParam) (hrem : rem.IsDeterministic)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (sz : Circulation → Circulation → WiredInnerSizes)
    (hInitSize : DrySCInitSizeHyps Psc B hB sz)
    (hS : DrySCSolverHyps Psc rem.toSolverInnerOpen B hB sz) :
    MinCostFlowStatement :=
  theorem_1_1_dry_run_sc_open Psc rem hrem B hB sz hInitSize.toOpenHyps hS

end MinCostFlow.Final.DryRun

end
