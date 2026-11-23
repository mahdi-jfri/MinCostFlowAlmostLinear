module

public import MinCostFlow.Final.AssemblyDryRunSCRem
public import MinCostFlow.Final.AssemblyDryRunSCEnvelope
public import MinCostFlow.Final.AssemblyDryRunSCSpace
import Mathlib.Tactic

/-!
# Concrete per-input inner sizes `sz` (`AssemblyDryRunSCSizes`)

Defines the concrete per-input size bundle `dryInnerSizesWithSelect Psc openSz selSz : Circulation →
Circulation → WiredInnerSizes` (and its zero-select-rebuild specialization `dryInnerSizes`) from
the proved body bounds of the solver's inner procedures, taking only the fields of
`selectRoute` and `ordChainCore` as parameters (`DryOpenSizes`):

* **Init (`initSpace'`, `initFixed`, `toolMul`):** exact `initConcreteSpace` (at
  `dryCoreInitSpace Psc J`, `dryParamSpace`, `dryLastSpace`, `dryCapLimit`), exact
  `initConcreteFixed` (at `dryParamCost`, `dryLastMult`, `drySCParams`), and `dryToolMul`
  (covering `Psc.mul`, `dryLastMult`, `deepShiftToolMulBound`, and select-update multiplier terms).
  Discharges `DrySCInitSizeHyps` (`hSpaceLe`, `hFixedLe`, `hMulLe`) unconditionally
  (`dryInnerSizesWithSelect_initSizeHyps`, `dryInnerSizes_initSizeHyps`).
* **Eval (`evalSpace`, `evalBudget`):** exact `evalCycleSpace` and `evalCycleBudget` at
  `F.limbs`, `openSz.maxEdges`, `openSz.maxPaths`. Discharges `hEvalSpace` and `hEvalBudget` of
  `drySC_hEval_proved` unconditionally (`dryInnerSizes_hEvalSpace`, `dryInnerSizes_hEvalBudget`).
* **Terminal shift (`termSpace`, `termFixed`, `treeMul`):** exact bounds of
  `shiftTermChainBody_meets_spec` / `drySC_hTermExt_proved` at `lastTreeCap = 2 * levelM d` plus
  level-`d` select rebuild (`selSz.termSelectFixed`). Discharges `hTermSpace`, `hTermFixed`, and
  `hTreeMul` unconditionally.
* **Deep shift (`deepSpace`, `deepFixed`, `DeepShiftOpsHypKFBL`):** exact space total `dryDeepSpace`
  using the concrete heap-independent op-1 restart bound `dryDeepRestartSpace Psc J`
  (`Final/AssemblyDryRunSCSpace.lean`), op-2 forest cap `dryDeepFCap`, `dryDeepIntCapMax`, and
  `dryDeepForestEdgeCap = 2 * I.n`; exact fixed cost `dryDeepShiftFixed` from
  `deepShiftFixedBound` plus `selSz.deepSelectFixed`. Discharges `DeepShiftOpsHypKFBL`
  unconditionally at `dryInnerSizesWithSelect` (`dryInnerSizesWithSelect_deepShiftOpsHypKFBL`).
* **Fixed-point bounds (`B_tree`, `B_bound`, `R_bound`):** powers of 2
  `B_tree = 2 ^ (P + 2 * E + 1)` and `B_bound = R_bound = 2 ^ (P + 80 * E)`, discharging five of
  the six clauses of `DryCapSimpleBounds` unconditionally and leaving only
  `openSz.maxEdges + openSz.maxPaths < 2 ^ (3 * E + 20)` (`dryInnerSizes_capSimpleBounds`).

Also states `DryOpenSizesIneqs` (the exact inequalities that the select and chain-core bodies
must satisfy on `openSz`).
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## Size parameters for select and chain core -/

/-- Fields of `WiredInnerSizes` for the bodies `selectRoute` and `ordChainCore`, given as
parameters. -/
structure DryOpenSizes where
  selectSpace : Circulation → Circulation → ℕ
  selectBudget : Circulation → Circulation → ℕ
  maxEdges : Circulation → Circulation → ℕ
  maxPaths : Circulation → Circulation → ℕ
  coreSpace : Circulation → Circulation → ℕ → ℕ
  coreFixed : Circulation → Circulation → ℕ → ℕ
  /-- Extra tool multiplier of `Update` (the chain-update core and its select part), added to
  `dryToolMul`. The core's bound `updateCoreToolMulBound` has powers of the forwarding ratio. -/
  coreToolMul : Circulation → Circulation → ℕ
  /-- Extra tree multiplier of `Update`, added to the tree multiplier of the shifts. The core pays
  `wireEmitLSFChangeEditsBody` and the select part pays `dgDeleteEdgeList` per deleted forest edge. -/
  coreTreeMul : Circulation → Circulation → ℕ

/-- The chain-core fields of `DryOpenSizes` (`coreSpace`, `coreFixed`,
`coreToolMul` and `coreTreeMul`),
once the select-route fields (`selectSpace`, `selectBudget`, `maxEdges`, `maxPaths`) are fixed
to their concrete values in `Final/WireSelectSizes.lean`. -/
structure DryCoreOpenSizes where
  coreSpace : Circulation → Circulation → ℕ → ℕ
  coreFixed : Circulation → Circulation → ℕ → ℕ
  coreToolMul : Circulation → Circulation → ℕ
  coreTreeMul : Circulation → Circulation → ℕ

/-! ## Concrete deep-shift sizes from `ordLevelSpace`, `ordLevelFixedCost`, `DeepShiftOpsHypKFBL` -/

/-- Upper bound `fcap` on `dynGraphSize forestVCap forestECap` emitted by op `2` at any cap pair
with `vCap + eCap + 2 ≤ dryCapLimit dryWitnessUsed J` (`drySC_forestCap_level`). -/
def dryDeepFCap (J : Circulation) : ℕ :=
  let capLimit := dryCapLimit dryWitnessUsed J
  dynGraphSize capLimit (2 * capLimit ^ 2)

/-- Per-level rebuild space `ordLevelSpace` at level `j` using `dryCoreInitSpace Psc J j`. -/
def dryDeepLevelSpace (Psc : DrySparseCorePieces) (J : Circulation) (j : ℕ) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  ordLevelSpace L dryCapExp (dryCapLimit dryWitnessUsed J) (dryCoreInitSpace Psc J j)
    (levelM cfg.TP cfg.P j) cfg.N₀ (levelM cfg.TP cfg.P (j + 1))

/-- Upper bound `intCapMax` on `tok.intCap` (`2 * (nfMax + 2 * I.m)`). -/
def dryDeepIntCapMax (J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let nfMax := Ordered.alg2NameBase cfg (namedInstance I) + intRebuildThreshold cfg.P cfg.N₀ 0
  2 * (nfMax + 2 * I.m)

/-- Upper bound `forestEdgeCap` on `graphListEdgeSum old + graphListEdgeSum new` across the
suffix forests of a deep shift (`2 * (cfg.P.d + 1) * I.n`, matching `shiftDeep_forestEdgeSum_le`).
Enters only `deepSpace` (polynomial in `I.m`), never per-update cost. -/
def dryDeepForestEdgeCap (J : Circulation) : ℕ :=
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  2 * (cfg.P.d + 1) * (solverConnectedAugmented J).n

/-- Concrete `deepSpace` matching `DeepShiftOpsHypKFBL.spaceTotal`, using the concrete
heap-independent op-1 restart space `dryDeepRestartSpace Psc J`. -/
def dryDeepSpace (Psc : DrySparseCorePieces) (J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  2 * (cfg.P.d + 1) + (5 + dryDeepFCap J + 5 * cfg.P.d) + dryDeepRestartSpace Psc J +
    (Finset.range cfg.P.d).sum (dryDeepLevelSpace Psc J) + dryLastSpace J + 5 * cfg.P.d +
    3 * dryDeepIntCapMax J + dryDeepForestEdgeCap J * (2 + wireTreeSyncEditSpace L)

/-- Concrete `deepFixed` matching the non-`Δ totalRuntime` terms of `DeepShiftOpsHypKFBL.costTotal`
(`ordLevelFixedCost`, op-2 forest copy `17 * fcap`, graph copy `17 * dynGraphSize capLimit capLimit`,
`bundleLogFactor` readout overhead, `wireCoreLenEdgeCost`, and `85 * forestEdgeCap`). -/
def dryDeepFixed (Psc : DrySparseCorePieces) (J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let capLimit := dryCapLimit dryWitnessUsed J
  let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
  let M0 := levelM cfg.TP cfg.P 0
  let LwMax0 := ordLevelLwMax L dryCapExp M0 cfg.N₀
  17 * dryDeepFCap J + PscP.mul +
    PscP.mul * (2 * cfg.N₀ + 2 * M0 + 2) * SparseCore.bundleLogFactor M0 cfg.N₀ +
    2 * PscP.readout + 17 * dynGraphSize capLimit capLimit +
    M0 * (wireCoreLenEdgeCost LwMax0 + 30) +
    (Finset.range cfg.P.d).sum (fun j =>
      ordLevelFixedCost L dryCapExp capLimit PscP (levelM cfg.TP cfg.P j) cfg.N₀
        (levelM cfg.TP cfg.P (j + 1)) + 35) +
    dryLastMult J +
    2 * cfg.P.d * (PscP.readout + 48) + 210 * (cfg.P.d + 1) +
    85 * dryDeepForestEdgeCap J + 1100

/-- Select-region, select-rebuild, and re-embedding space and cost terms added to `initSpace'`,
`initFixed`, `termSpace`, `termFixed`, `deepSpace`, `deepFixed`, and `toolMul` to cover the select
region, select heap, and level-block updates (`SelectRegionSkeleton`, `SelectInitFinalize`,
`WireReembPotChain`, `SelectPhiFill`, `DynGraphRefill`, `WireSelectUpdate`). Each space field is
`PolyNat` in `I.m`, `initSelectFixed` is `(I.m + 1) * m^{o(1)}`, and each remaining cost field is
`m^{o(1)}`. -/
structure DrySelectRebuildSizes where
  /-- Extra heap space at Init for `SelectRegion`, `SelectHeap`, `SelectLevelMeta`, and
  `selectInitFinalizeSpace` (`PolyNat`). -/
  initSelectSpace : Circulation → Circulation → ℕ
  /-- Extra fixed cost at Init for building `SelectHeap` and `SelectLevelMeta`
  (`(I.m + 1) * m^{o(1)}`). -/
  initSelectFixed : Circulation → Circulation → ℕ
  /-- Extra heap space per terminal shift for level-`d` select rebuild (`PolyNat`). -/
  termSelectSpace : Circulation → Circulation → ℕ
  /-- Extra heap space per deep shift for suffix select rebuild (`PolyNat`). -/
  deepSelectSpace : Circulation → Circulation → ℕ
  /-- Extra fixed cost per deep shift for suffix select rebuild (`O(d * ...)`). -/
  deepSelectFixed : Circulation → Circulation → ℕ
  /-- Extra fixed cost per terminal shift for level-`d` select rebuild
  (`O((levelM d + 1) * ((d + 1) * Lk + LwMax₀^2 + log(cap) * Lk^2))`). -/
  termSelectFixed : Circulation → Circulation → ℕ
  /-- Cost `K_key` of one select-heap key evaluation/update (`WireReembPotChain`). -/
  keyCost : Circulation → Circulation → ℕ
  /-- Re-embedding cost ratio `cReemb` (`WireReembPot`, `reembCostBound_of_progTool`). -/
  cReemb : Circulation → Circulation → ℕ
  /-- Additional per-tool-cost multiplier terms from select updates
  (`O(slot + (d + 1) * Lk + LwMax₀^2)`). -/
  selectToolMulExtra : Circulation → Circulation → ℕ

/-- The Init select fields of `DrySelectRebuildSizes` (`initSelectSpace`,
`initSelectFixed`). -/
structure DryInitSelectSizes where
  initSelectSpace : Circulation → Circulation → ℕ
  initSelectFixed : Circulation → Circulation → ℕ

/-- The shift select fields of `DrySelectRebuildSizes` (`termSelectSpace`,
`deepSelectSpace`, `termSelectFixed`, `deepSelectFixed`). -/
structure DryShiftSelectSizes where
  termSelectSpace : Circulation → Circulation → ℕ
  deepSelectSpace : Circulation → Circulation → ℕ
  termSelectFixed : Circulation → Circulation → ℕ
  deepSelectFixed : Circulation → Circulation → ℕ

/-- Concrete `deepFixed` from `deepShiftFixedBound` (`WireShiftDeepCostKFBL`) plus suffix select
rebuild overhead (`selSz.deepSelectFixed`). -/
def dryDeepShiftFixed (Psc : DrySparseCorePieces) (selSz : DrySelectRebuildSizes)
    (source J : Circulation) : ℕ :=
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
  deepShiftFixedBound PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d (dryLastMult J) +
    selSz.deepSelectFixed source J

/-- Concrete `toolMul` covering `Psc.mul`, `dryLastMult`, `deepShiftToolMulBound`
(`WireShiftDeepCostKFBL`), `K_key * (cReemb + 2)`, and select-update multiplier terms. -/
def dryToolMul (Psc : DrySparseCorePieces) (selSz : DrySelectRebuildSizes)
    (source J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
  max (deepShiftToolMulBound L dryCapExp PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d (dryLastMult J))
    PscP.mul +
    selSz.keyCost source J * (selSz.cReemb source J + 2) +
    selSz.selectToolMulExtra source J

/-- Concrete `termFixed` covering path-tree sync at `2 * levelM cfg.TP cfg.P cfg.P.d` plus
level-`d` select rebuild (`selSz.termSelectFixed`). -/
def dryTermFixed (selSz : DrySelectRebuildSizes) (source J : Circulation) : ℕ :=
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  41 * (2 * levelM cfg.TP cfg.P cfg.P.d) + 320 + selSz.termSelectFixed source J

/-! ## Concrete `sz : Circulation → Circulation → WiredInnerSizes` -/

/-- Concrete per-input `WiredInnerSizes` built from each proved body bound (init, eval, terminal
shift at `lastTreeCap = 2 * levelM cfg.TP cfg.P cfg.P.d` plus level-`d` select rebuild, deep shift
via `deepShiftFixedBound` and `deepShiftToolMulBound` plus suffix select rebuild and
`K_key * (cReemb + 2)`, and power-of-2 fixed-point bounds), taking the select and chain-core sizes
from `openSz` and select-rebuild overhead from `selSz`. -/
def dryInnerSizesWithSelect (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (selSz : DrySelectRebuildSizes) (source J : Circulation) : WiredInnerSizes :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let P := ipmQualityPrecision I.m V k
  let E := ipmQualityRangeExponent I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let limbMul := concreteReadout2LimbMul dryWitnessUsed
  let me := openSz.maxEdges source J
  let mp := openSz.maxPaths source J
  { initSpace' :=
      initConcreteSpace I.m (namedInstance I).n L cfg.P.d (dryParamSpace source J) dryCapExp
        (dryCapLimit dryWitnessUsed J) (dryLastSpace J)
        (LinkCut.PathProg.arenaEnd 0 (namedInstance I).n L)
        (20 * LinkCut.PathProg.treeLimbs L + 100)
        (dryCoreInitSpace Psc J) (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1))
        cfg.N₀ + selSz.initSelectSpace source J
    initFixed :=
      initConcreteFixed I.m (namedInstance I).n L cfg.P.d (dryParamCost source J) dryCapExp
        (dryCapLimit dryWitnessUsed J) (dryLastMult J) LinkCut.PathProg.pathC
        (drySCParams Psc dryCapExp limbMul)
        (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀ +
        selSz.initSelectFixed source J
    selectSpace := openSz.selectSpace source J
    selectBudget := openSz.selectBudget source J
    evalSpace := evalCycleSpace L me mp
    evalBudget := evalCycleBudget L me mp
    termSpace := (2 * levelM cfg.TP cfg.P cfg.P.d) * (2 + wireTreeSyncEditSpace L) +
      selSz.termSelectSpace source J
    termFixed := dryTermFixed selSz source J
    deepSpace := dryDeepSpace Psc J + selSz.deepSelectSpace source J
    deepFixed := dryDeepShiftFixed Psc selSz source J
    maxEdges := me
    maxPaths := mp
    toolMul := dryToolMul Psc selSz source J + openSz.coreToolMul source J
    treeMul := wireTreeSyncEditCost L (detectOffTreeDrainUnit L) + 2 + openSz.coreTreeMul source J
    coreSpace := openSz.coreSpace source J
    coreFixed := openSz.coreFixed source J
    B_tree := (2 : ℤ) ^ (P + 2 * E + 1)
    B_bound := (2 : ℤ) ^ (P + 80 * E)
    R_bound := (2 : ℤ) ^ (P + 80 * E) }

/-- Zero select-rebuild overhead specialization (retaining `deepShiftFixedBound` and
`deepShiftToolMulBound`). -/
def dryZeroSelectRebuildSizes : DrySelectRebuildSizes where
  initSelectSpace := fun _ _ => 0
  initSelectFixed := fun _ _ => 0
  termSelectSpace := fun _ _ => 0
  deepSelectSpace := fun _ _ => 0
  deepSelectFixed := fun _ _ => 0
  termSelectFixed := fun _ _ => 0
  keyCost := fun _ _ => 0
  cReemb := fun _ _ => 0
  selectToolMulExtra := fun _ _ => 0

/-- Concrete per-input `WiredInnerSizes` at zero select-rebuild overhead (`dryInnerSizesWithSelect`
at `dryZeroSelectRebuildSizes`, using `deepShiftFixedBound` and `deepShiftToolMulBound`). -/
def dryInnerSizes (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (source J : Circulation) : WiredInnerSizes :=
  dryInnerSizesWithSelect Psc openSz dryZeroSelectRebuildSizes source J

/-! ## Exact inequalities required of the select and chain-core bodies -/

/-- Exact arithmetic, polynomial, and subpolynomial inequalities that the bodies of `selectRoute`
and `ordChainCore` must satisfy on `openSz` for fixed-point capacity bounds (`DryCapSimpleBounds`),
polynomial update space (`PolyNat B.updateSpace`), and subpolynomial update rate
(`SubpolyNat B.updateRate`). -/
structure DryOpenSizesIneqs (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (openSz : DryOpenSizes) : Prop where
  /-- Fixed-point capacity condition on the route length (`DryCapSimpleBounds` clause 6). -/
  hMaxEP : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
    fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      openSz.maxEdges source J + openSz.maxPaths source J < 2 ^ (3 * F.rangeExponent + 20)
  /-- Monotonicity of `coreSpace` in the batch length (`DryEnvelopeIneqs` clause 5). -/
  hCoreSpaceMono : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
    fun source J _ => Monotone (openSz.coreSpace source J)
  /-- Polynomial space bounds (as functions of `I.m`) for `selectSpace`, `coreSpace (2 * I.m)`,
  `maxEdges`, and `maxPaths` (`PolyNat B.updateSpace`). -/
  hSpacePoly :
    ∃ (fSelSp fCoreSp fME fMP : ℕ → ℕ),
      PolyNat fSelSp ∧ PolyNat fCoreSp ∧ PolyNat fME ∧ PolyNat fMP ∧
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
        fun source J _ =>
          let m := (solverConnectedAugmented J).m
          openSz.selectSpace source J ≤ fSelSp m ∧
          openSz.coreSpace source J (2 * m) ≤ fCoreSp m ∧
          openSz.maxEdges source J ≤ fME m ∧
          openSz.maxPaths source J ≤ fMP m
  /-- Subpolynomial budget/route bounds (as functions of `I.m`) for `selectBudget`, `maxEdges`,
  `maxPaths`, and linear `coreFixed u ≤ ρ₀ + ρ₁ * u` (`SubpolyNat B.updateRate`). -/
  hRateSubpoly :
    ∃ (fSelBud fME fMP fRho0 fRho1 : ℕ → ℕ),
      SubpolyNat fSelBud ∧ SubpolyNat fME ∧ SubpolyNat fMP ∧
      SubpolyNat fRho0 ∧ SubpolyNat fRho1 ∧
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
        fun source J _ =>
          let m := (solverConnectedAugmented J).m
          openSz.selectBudget source J ≤ fSelBud m ∧
          openSz.maxEdges source J ≤ fME m ∧
          openSz.maxPaths source J ≤ fMP m ∧
          ∀ u ≤ 2 * m, openSz.coreFixed source J u ≤ fRho0 m + fRho1 m * u

/-! ## Proved Init, Eval, Term, Deep-space, and Cap-bounds discharges for `dryInnerSizes` -/

/-- **Init inequalities:** `dryInnerSizes Psc openSz` unconditionally satisfies all three
Init size/multiplier inequalities of `DrySCInitSizeHyps` at `dryCoreInitSpace Psc J`. -/
theorem dryInnerSizesWithSelect_initSizeHyps (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (selSz : DrySelectRebuildSizes) (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B) :
    DrySCInitSizeHyps Psc B hB (dryInnerSizesWithSelect Psc openSz selSz) where
  hSpaceLe := fun _ _ _ _ _ _ _ => Nat.le_add_right _ _
  hFixedLe := fun _ _ _ _ _ _ _ => Nat.le_add_right _ _
  hMulLe := fun source J => by
    show max _ (dryLastMult J) ≤ dryToolMul Psc selSz source J + openSz.coreToolMul source J
    dsimp only [dryToolMul, deepShiftToolMulBound]
    omega

/-- **Init inequalities:** `dryInnerSizes Psc openSz` unconditionally satisfies all three
Init size/multiplier inequalities of `DrySCInitSizeHyps` at `dryCoreInitSpace Psc J`. -/
theorem dryInnerSizes_initSizeHyps (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B) :
    DrySCInitSizeHyps Psc B hB (dryInnerSizes Psc openSz) :=
  dryInnerSizesWithSelect_initSizeHyps Psc openSz dryZeroSelectRebuildSizes B hB

/-- `dryInnerSizesWithSelect` satisfies `deepShiftFixedBound ≤ deepFixed`,
`deepShiftToolMulBound ≤ toolMul`, and `keyCost * (cReemb + 2) + selectToolMulExtra ≤ toolMul`. -/
theorem dryInnerSizesWithSelect_deep_select_bounds (Psc : DrySparseCorePieces)
    (openSz : DryOpenSizes) (selSz : DrySelectRebuildSizes) (source J : Circulation) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
    let s := dryInnerSizesWithSelect Psc openSz selSz source J
    deepShiftFixedBound PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d (dryLastMult J) ≤ s.deepFixed ∧
    deepShiftToolMulBound L dryCapExp PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d (dryLastMult J) ≤
      s.toolMul ∧
    selSz.keyCost source J * (selSz.cReemb source J + 2) + selSz.selectToolMulExtra source J ≤
      s.toolMul ∧
    41 * (2 * levelM cfg.TP cfg.P cfg.P.d) + 320 ≤ s.termFixed := by
  dsimp only [dryInnerSizesWithSelect, dryDeepShiftFixed, dryToolMul, dryTermFixed]
  refine ⟨Nat.le_add_right _ _, ?_, by omega, Nat.le_add_right _ _⟩
  exact (le_max_left _ _).trans ((Nat.le_add_right _ _).trans
    ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))

/-- `dryInnerSizes` unconditionally satisfies `hEvalSpace` of `drySC_hEval_proved`. -/
theorem dryInnerSizes_hEvalSpace (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B) :
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      evalCycleSpace F.limbs (dryInnerSizes Psc openSz source J).maxEdges
        (dryInnerSizes Psc openSz source J).maxPaths ≤
        (dryInnerSizes Psc openSz source J).evalSpace :=
  fun _ _ _ _ _ _ _ => le_rfl

/-- `dryInnerSizes` unconditionally satisfies `hEvalBudget` of `drySC_hEval_proved`. -/
theorem dryInnerSizes_hEvalBudget (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B) :
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      evalCycleBudget F.limbs (dryInnerSizes Psc openSz source J).maxEdges
        (dryInnerSizes Psc openSz source J).maxPaths ≤
        (dryInnerSizes Psc openSz source J).evalBudget :=
  fun _ _ _ _ _ _ _ => le_rfl

/-- `dryInnerSizes` unconditionally satisfies `hTermSpace` of `drySC_hTermExt_proved` at
`lastTreeCap = 2 * levelM cfg.TP cfg.P cfg.P.d`. -/
theorem dryInnerSizes_hTermSpace (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B) :
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      (2 * levelM cfg.TP cfg.P cfg.P.d) * (2 + wireTreeSyncEditSpace F.limbs) ≤
        (dryInnerSizes Psc openSz source J).termSpace :=
  fun _ _ _ _ _ _ _ => Nat.le_add_right _ _

/-- `dryInnerSizes` unconditionally satisfies `hTermFixed` of `drySC_hTermExt_proved` at
`lastTreeCap = 2 * levelM cfg.TP cfg.P cfg.P.d`. -/
theorem dryInnerSizes_hTermFixed (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B) :
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J _ =>
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      41 * (2 * levelM cfg.TP cfg.P cfg.P.d) + 320 ≤
        (dryInnerSizes Psc openSz source J).termFixed :=
  fun _ _ _ _ _ _ _ => Nat.le_add_right _ _

/-- `dryInnerSizes` unconditionally satisfies `hTreeMul` of `drySC_hTermExt_proved`. -/
theorem dryInnerSizes_hTreeMul (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B) :
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      wireTreeSyncEditCost F.limbs (detectOffTreeDrainUnit F.limbs) + 2 ≤
        (dryInnerSizes Psc openSz source J).treeMul :=
  fun _ _ _ _ _ _ _ => Nat.le_add_right _ _

/-- `dryInnerSizesWithSelect` unconditionally satisfies `DeepShiftOpsHypKFBL.spaceTotal` at
`dryDeepSpace` and `dryDeepRestartSpace`. -/
theorem dryInnerSizesWithSelect_deepSpaceTotal (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (selSz : DrySelectRebuildSizes) (source J : Circulation) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    2 * (cfg.P.d + 1) + (5 + dryDeepFCap J + 5 * cfg.P.d) + dryDeepRestartSpace Psc J +
      (Finset.range cfg.P.d).sum (dryDeepLevelSpace Psc J) + dryLastSpace J + 5 * cfg.P.d +
      3 * dryDeepIntCapMax J + dryDeepForestEdgeCap J * (2 + wireTreeSyncEditSpace L) ≤
      (dryInnerSizesWithSelect Psc openSz selSz source J).deepSpace :=
  Nat.le_add_right _ _

/-- `dryInnerSizes` unconditionally satisfies `DeepShiftOpsHypKFBL.spaceTotal` at
`dryDeepSpace` and `dryDeepRestartSpace`. -/
theorem dryInnerSizes_deepSpaceTotal (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (source J : Circulation) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    2 * (cfg.P.d + 1) + (5 + dryDeepFCap J + 5 * cfg.P.d) + dryDeepRestartSpace Psc J +
      (Finset.range cfg.P.d).sum (dryDeepLevelSpace Psc J) + dryLastSpace J + 5 * cfg.P.d +
      3 * dryDeepIntCapMax J + dryDeepForestEdgeCap J * (2 + wireTreeSyncEditSpace L) ≤
      (dryInnerSizes Psc openSz source J).deepSpace :=
  Nat.le_add_right _ _

/-- Monotonicity of `DeepShiftOpsHypKFBL` in `deepSpace`, `deepFixed`, and `toolMul`. -/
theorem deepShiftOpsHypKFBL_mono
    {w L capExp capLimit fcap lastMul intCapMax forestEdgeCap sp₁ sp₂ fix₁ fix₂ tm₁ tm₂ : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {allocation lastAlloc : ℕ → List ℕ → ℕ}
    {restartSpace : ℕ} {levelSpace : ℕ → ℕ}
    {levelCost : Alg2State cfg → Fin (cfg.P.d + 1) → ℕ → ℕ} {lastSpace : ℕ}
    (h : DeepShiftOpsHypKFBL (w := w) (L := L) (capExp := capExp) (capLimit := capLimit)
      (fcap := fcap) (lastMul := lastMul) (intCapMax := intCapMax)
      (forestEdgeCap := forestEdgeCap) (deepSpace := sp₁) (deepFixed := fix₁) (toolMul := tm₁)
      (fmt := fmt) (cfg := cfg) (Psc := Psc) (allocation := allocation) (lastAlloc := lastAlloc)
      restartSpace levelSpace levelCost lastSpace)
    (hsp : sp₁ ≤ sp₂) (hfix : fix₁ ≤ fix₂) (htm : tm₁ ≤ tm₂) :
    DeepShiftOpsHypKFBL (w := w) (L := L) (capExp := capExp) (capLimit := capLimit)
      (fcap := fcap) (lastMul := lastMul) (intCapMax := intCapMax)
      (forestEdgeCap := forestEdgeCap) (deepSpace := sp₂) (deepFixed := fix₂) (toolMul := tm₂)
      (fmt := fmt) (cfg := cfg) (Psc := Psc) (allocation := allocation) (lastAlloc := lastAlloc)
      restartSpace levelSpace levelCost lastSpace where
  restartSpaceDom := h.restartSpaceDom
  levelSpaceDom := h.levelSpaceDom
  lastSpaceDom := h.lastSpaceDom
  spaceTotal := h.spaceTotal.trans hsp
  levelCostDom := h.levelCostDom
  costTotal := fun model i hi hbran hOrd hK =>
    (h.costTotal model i hi hbran hOrd hK).trans
      (Nat.add_le_add hfix (Nat.mul_le_mul_right _ htm))

/-- Unconditional discharge of `DeepShiftOpsHypKFBL` at the exact `deepSpace`, `deepFixed`, and
`toolMul` of `dryInnerSizesWithSelect Psc openSz selSz`, via `drySC_deepShiftOpsHypKFBL` and
`dryInnerSizesWithSelect_deep_select_bounds`. -/
theorem dryInnerSizesWithSelect_deepShiftOpsHypKFBL (Psc : DrySparseCorePieces)
    (openSz : DryOpenSizes) (selSz : DrySelectRebuildSizes)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let limbMul := concreteReadout2LimbMul W
    let PscP := drySCParams Psc dryCapExp limbMul
    let s := dryInnerSizesWithSelect Psc openSz selSz source J
    DeepShiftOpsHypKFBL
      (w := dryWordSize W allocationCoefficient allocationDegree source)
      (L := F.limbs) (capExp := dryCapExp) (capLimit := dryCapLimit W J)
      (fcap := dryDeepFCap J) (lastMul := dryLastMult J)
      (intCapMax := dryDeepIntCapMax J) (forestEdgeCap := dryDeepForestEdgeCap J)
      (deepSpace := s.deepSpace) (deepFixed := s.deepFixed) (toolMul := s.toolMul)
      (fmt := F.fmt) (cfg := cfg) (Psc := PscP)
      (allocation := drySCAlloc Psc dryCapExp limbMul J)
      (lastAlloc := fun _ _ => dryLastSpace J)
      (dryDeepRestartSpace Psc J)
      (dryDeepLevelSpace Psc J)
      (deepShiftLevelCost F.limbs dryCapExp cfg PscP) (dryLastSpace J) := by
  have hBase := drySC_deepShiftOpsHypKFBL Psc allocationCoefficient allocationDegree source J
    hJn hJm hCapPos hw
    (fcap := dryDeepFCap J) (lastMul := dryLastMult J)
    (intCapMax := dryDeepIntCapMax J) (forestEdgeCap := dryDeepForestEdgeCap J)
    (deepSpace := dryDeepSpace Psc J) (lastSpace := dryLastSpace J)
    (lastAlloc := fun _ _ => dryLastSpace J)
    (fun _ _ _ => le_rfl) le_rfl
  have hBds := dryInnerSizesWithSelect_deep_select_bounds Psc openSz selSz source J
  exact deepShiftOpsHypKFBL_mono hBase (Nat.le_add_right _ _) hBds.1 hBds.2.1

private theorem pow2_cap_le {P E : ℕ} (hE : 100 ≤ E) :
    (2 : ℤ) ^ (P + 2 * E + 1) ≤ (2 : ℤ) ^ (P + 80 * E) :=
  pow_le_pow_right₀ (by norm_num) (by omega)

/-- `dryInnerSizes` satisfies `DryCapSimpleBounds` (and hence all seven clauses of
`DryFixedPointCapBounds` via `dryFixedPointCapBounds_of_bounds`) from the single route-length
inequality `openSz.maxEdges + openSz.maxPaths < 2 ^ (3 * F.rangeExponent + 20)`. -/
theorem dryInnerSizes_capSimpleBounds (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (hMaxEP : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
      fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        openSz.maxEdges source J + openSz.maxPaths source J < 2 ^ (3 * F.rangeExponent + 20)) :
    DryCapSimpleBounds B hB (dryInnerSizes Psc openSz) := by
  refine ⟨fun source J hJn hJm hCost hCap hw => ?_⟩
  have hE100 : 100 ≤ ipmQualityRangeExponent (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) := by
    unfold ipmQualityRangeExponent; omega
  have hpow := pow2_cap_le
    (P := ipmQualityPrecision (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m))
    hE100
  exact ⟨le_refl _, hpow, hpow, le_refl _, le_refl _, hMaxEP source J hJn hJm hCost hCap hw⟩

end MinCostFlow.Final.DryRun

end
