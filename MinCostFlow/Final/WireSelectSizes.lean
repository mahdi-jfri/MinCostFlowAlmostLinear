module

public import MinCostFlow.Final.AssemblyDryRunSCDeepAsymp
public import MinCostFlow.Final.WireSelectEmbLen
public import MinCostFlow.MinRatio.WireSelectSpec
public import MinCostFlow.MinRatio.WireSelectEvalKeyDefs
public import MinCostFlow.MinRatio.SelectCoreLenFill
public import MinCostFlow.MinRatio.SolverSelectState
import Mathlib.Tactic

/-!
# Concrete select-route and select-update sizes for the dry run (`WireSelectSizes`)

Fixes the select-route fields of `DryOpenSizes` and the per-key / re-embedding / select-update
multiplier fields of `DrySelectRebuildSizes` at the dry run's exact parameters, and proves all
corresponding `PolyNat`, `SubpolyNat`, and fixed-point capacity (`hMaxEP`) bounds:

1. **Select-route fields of `DryOpenSizes`:**
   * `drySelectMaxEdges _ J := dryMaxEdges I.m` (`dryMaxEmbLen I.m + 1`),
   * `drySelectMaxPaths _ J := dryMaxPaths I.m` (`2 * dryMaxEdges I.m`),
   * `drySelectSpace _ J := selectRouteTotalSpace (dryMaxPaths I.m) L (pathApplySpace L)`,
   * `drySelectBudget _ J := selectRouteTotalCost L (dryMaxPaths I.m) L (25 * (pathC * (L + 1)^2) * (4 * L + 1))`.
   These match `ordCycleRouteSelectSpecHeap_proved` (`MinRatio/WireSelectQueryProofs.lean`)
   definitionally, including the `O(maxPaths ^ 2)` in-place opposite-pair edge cancellation pass
   (`cancelRouteEdgesCost`). Proves `drySelectSpace_le_poly`, `drySelectBudget_le_subpoly`,
   `drySelect_hMaxEP`, and `DryCoreOpenSizeBounds.toDryOpenSizeBounds`.
2. **Per-key, re-embedding, and select-update multiplier fields of `DrySelectRebuildSizes`:**
   * `dryCReemb _ _ := 1` (matching `reembCostBound_of_progTool` and `selectUpdateLevel_paid_step_progTool`),
   * `dryKeyCost _ J := selectProcessEdgeCost (selectHeapCap cfg G I.m) L (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) L) + (18 * drySlot I.m + 80) + 160`
     (covering `selectProcessEdgeCost + 40`, `selectRebuildLevelCost_le_linear`'s `+ 60`, and
     `selEmbCopyContract`'s `18 * slot + 80` per re-embedded edge),
   * `drySelectToolMulExtra _ J` covering the select-update and suffix-rebuild per-tool-cost terms:
     `(d + 3) * dryKeyCost` (old suffix clearing across `d + 1` levels, new suffix + level-`d`
     inserts, and `chainReembPot_rebuild_le`), `2 * (18 * drySlot + 80)` (`selEmbCopy`),
     `1800 * (d + 1) * (L + 1)` (`selectPhiFill` + `splitPot`), `2 * (selCoreLenEdgeCost L LwMax₀ + 40)`
     (`selCoreLenFill`), `1000 * (d + 1)` (`dgRefillFromLists`), and `36 * L + 200`
     (`selCopyValues` + `selCoreList`).
   Proves `dryCReemb_le_subpoly`, `dryKeyCost_le_subpoly`, `drySelectToolMulExtra_le_subpoly`, and
   `mkDrySelectRebuildSizeBounds`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Concrete select-route fields of `DryOpenSizes` -/

/-- Concrete `maxEdges` for `DryOpenSizes` (`dryMaxEdges I.m = dryMaxEmbLen I.m + 1`). -/
def drySelectMaxEdges (_source J : Circulation) : ℕ :=
  dryMaxEdges (solverConnectedAugmented J).m

/-- Concrete `maxPaths` for `DryOpenSizes` (`dryMaxPaths I.m = 2 * dryMaxEdges I.m`). -/
def drySelectMaxPaths (_source J : Circulation) : ℕ :=
  dryMaxPaths (solverConnectedAugmented J).m

/-- Concrete `selectSpace` for `DryOpenSizes`, matching `ordCycleRouteSelectSpecHeap_proved`
definitionally (`selectRouteTotalSpace maxPaths L (pathApplySpace L)`). -/
def drySelectSpace (_source J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  selectRouteTotalSpace (dryMaxPaths I.m) L (pathApplySpace L)

/-- Concrete `selectBudget` for `DryOpenSizes`, matching `ordCycleRouteSelectSpecHeap_proved`
definitionally (`selectRouteTotalCost L maxPaths L (25 * (pathC * (L + 1)^2) * (4 * L + 1))`,
including `cancelRouteEdgesCost`). -/
def drySelectBudget (_source J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  selectRouteTotalCost L (dryMaxPaths I.m) L
    (25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1))

/-- Uniform `PolyNat` (in fact `SubpolyNat`) bound on `drySelectSpace`. -/
theorem drySelectSpace_le_poly :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        drySelectSpace source J ≤ f (solverConnectedAugmented J).m := by
  have hMPSub : SubpolyNat dryMaxPaths := progTool_embLen_le_subpoly.2.2.1
  have hMPP : PolyNat dryMaxPaths := SubpolyNat.toPolyNat hMPSub
  have hLP : PolyNat dryLimbsOfM := SubpolyNat.toPolyNat dryLimbsOfM_subpoly
  let f : ℕ → ℕ := fun M =>
    8 * dryMaxPaths M +
      (4 * (dryMaxPaths M) ^ 4 + 1) *
        ((dryMaxPaths M) ^ 2 * (322 * dryLimbsOfM M + 1040) + 1)
  have hfP : PolyNat f := by
    have h1 := PolyNat.const_mul hMPP 8
    have h2 := PolyNat.add_const (PolyNat.const_mul (PolyNat.pow hMPP 4) 4) 1
    have h3 := PolyNat.add_const
      (PolyNat.mul (PolyNat.pow hMPP 2)
        (PolyNat.add_const (PolyNat.const_mul hLP 322) 1040)) 1
    exact PolyNat.add h1 (PolyNat.mul h2 h3)
  refine ⟨f, hfP, fun _source J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
  unfold drySelectSpace selectRouteTotalSpace selectRawRouteSpace cancelRoutePathsSpace
    pathApplySpace LinkCut.PathProg.treeLimbs
  dsimp only [f]
  have hsq : dryMaxPaths I.m * dryMaxPaths I.m = (dryMaxPaths I.m) ^ 2 := by ring
  rw [hsq]
  have hIn : 4 * (20 * (4 * L + 8) + 100) + 2 * L ≤ 322 * dryLimbsOfM I.m + 1040 := by omega
  have hMul1 := Nat.mul_le_mul_left ((dryMaxPaths I.m) ^ 2) hIn
  have hMul2 := Nat.mul_le_mul_left (4 * (dryMaxPaths I.m) ^ 4 + 1) (Nat.add_le_add_right hMul1 1)
  exact Nat.add_le_add_left hMul2 (8 * dryMaxPaths I.m)

/-- Uniform `SubpolyNat` bound on `drySelectBudget` via `selectRouteTotal_cost_paper_form`. -/
theorem drySelectBudget_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        drySelectBudget source J ≤ f (solverConnectedAugmented J).m := by
  have hMPSub : SubpolyNat dryMaxPaths := progTool_embLen_le_subpoly.2.2.1
  have hLSub : SubpolyNat dryLimbsOfM := dryLimbsOfM_subpoly
  let fTB : ℕ → ℕ := fun M =>
    25 * (LinkCut.PathProg.pathC * (dryLimbsOfM M + 1) ^ 2) * (4 * dryLimbsOfM M + 1)
  have hfTBSub : SubpolyNat fTB :=
    SubpolyNat.mul
      (SubpolyNat.const_mul (SubpolyNat.const_mul (SubpolyNat.pow (SubpolyNat.add_const hLSub 1) 2)
        LinkCut.PathProg.pathC) 25)
      (SubpolyNat.add_const (SubpolyNat.const_mul hLSub 4) 1)
  let f : ℕ → ℕ := fun M =>
    520 * (dryLimbsOfM M + dryMaxPaths M + 1) +
      440 * (4 * (dryMaxPaths M) ^ 4 + 1) *
        (((dryMaxPaths M) ^ 2 + 1) * (4 * fTB M + dryLimbsOfM M + 1))
  have hfSub : SubpolyNat f := by
    have h1 := SubpolyNat.const_mul (SubpolyNat.add_const (SubpolyNat.add hLSub hMPSub) 1) 520
    have h2 := SubpolyNat.const_mul (SubpolyNat.add_const (SubpolyNat.const_mul (SubpolyNat.pow hMPSub 4) 4) 1) 440
    have h3 := SubpolyNat.mul (SubpolyNat.add_const (SubpolyNat.pow hMPSub 2) 1)
      (SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.const_mul hfTBSub 4) hLSub) 1)
    exact SubpolyNat.add h1 (SubpolyNat.mul h2 h3)
  refine ⟨f, hfSub, fun _source J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hPaper := selectRouteTotal_cost_paper_form L (dryMaxPaths I.m) L
    (25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1))
  have hTB : 25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) ≤ fTB I.m := by
    dsimp only [fTB]
    exact Nat.mul_le_mul
      (Nat.mul_le_mul_left 25 (Nat.mul_le_mul_left LinkCut.PathProg.pathC (Nat.pow_le_pow_left (by omega) 2)))
      (by omega)
  refine hPaper.trans ?_
  dsimp only [f]
  have hA : 520 * (L + dryMaxPaths I.m + 1) ≤ 520 * (dryLimbsOfM I.m + dryMaxPaths I.m + 1) :=
    Nat.mul_le_mul_left 520 (by omega)
  have hB : 440 * (4 * (dryMaxPaths I.m) ^ 4 + 1) *
        (((dryMaxPaths I.m) ^ 2 + 1) *
          (4 * (25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1)) + L + 1)) ≤
      440 * (4 * (dryMaxPaths I.m) ^ 4 + 1) *
        (((dryMaxPaths I.m) ^ 2 + 1) * (4 * fTB I.m + dryLimbsOfM I.m + 1)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  exact Nat.add_le_add hA hB

/-- `hMaxEP` (clause 6 of `DryCapSimpleBounds`) holds unconditionally for `drySelectMaxEdges` and
`drySelectMaxPaths` (from `dryMaxEdges_add_maxPaths_lt`). -/
theorem drySelect_hMaxEP (allocCoeff allocDeg : ℕ) :
    ForAllDryInputs dryWitnessUsed allocCoeff allocDeg fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      drySelectMaxEdges source J + drySelectMaxPaths source J < 2 ^ (3 * F.rangeExponent + 20) :=
  fun _source J _ _ _ _ _ => dryMaxEdges_add_maxPaths_lt J

/-- Build a full `DryOpenSizes` from the chain-core sizes `coreSz` and the concrete
select-route sizes (`drySelectSpace`, `drySelectBudget`, `drySelectMaxEdges`, `drySelectMaxPaths`). -/
def DryCoreOpenSizes.toDryOpenSizes (coreSz : DryCoreOpenSizes) : DryOpenSizes where
  selectSpace := drySelectSpace
  selectBudget := drySelectBudget
  maxEdges := drySelectMaxEdges
  maxPaths := drySelectMaxPaths
  coreSpace := coreSz.coreSpace
  coreFixed := coreSz.coreFixed
  coreToolMul := coreSz.coreToolMul
  coreTreeMul := coreSz.coreTreeMul

/-- Lift `DryCoreOpenSizeBounds` to `DryOpenSizeBounds` using the proved concrete select-route
bounds (`drySelectSpace_le_poly`, `drySelectBudget_le_subpoly`, `progTool_embLen_le_subpoly`). -/
theorem DryCoreOpenSizeBounds.toDryOpenSizeBounds {coreSz : DryCoreOpenSizes}
    (hCore : DryCoreOpenSizeBounds coreSz) :
    DryOpenSizeBounds coreSz.toDryOpenSizes where
  hCoreSpaceMono := hCore.hCoreSpaceMono
  hCoreMulSubpoly := hCore.hCoreMulSubpoly
  hSpacePoly := by
    obtain ⟨fSelSp, hfSelSpP, hSelSp⟩ := drySelectSpace_le_poly
    obtain ⟨fCoreSp, hfCoreSpP, hCoreSp⟩ := hCore.hCoreSpacePoly
    exact ⟨fSelSp, fCoreSp, hfSelSpP, hfCoreSpP, fun source J hJn hJm hCap =>
      ⟨hSelSp source J hJn hJm hCap, hCoreSp source J hJn hJm hCap⟩⟩
  hRateSubpoly := by
    obtain ⟨fSelBud, hfSelBudSub, hSelBud⟩ := drySelectBudget_le_subpoly
    obtain ⟨fRho0, fRho1, hfRho0Sub, hfRho1Sub, hCoreF⟩ := hCore.hCoreFixedSubpoly
    exact ⟨fSelBud, dryMaxEdges, dryMaxPaths, fRho0, fRho1,
      hfSelBudSub, progTool_embLen_le_subpoly.2.1, progTool_embLen_le_subpoly.2.2.1,
      hfRho0Sub, hfRho1Sub, fun source J hJn hJm hCap =>
        ⟨hSelBud source J hJn hJm hCap, le_rfl, le_rfl, hCoreF source J hJn hJm hCap⟩⟩

/-! ## 2. Concrete `cReemb`, `keyCost`, and `selectToolMulExtra` for `DrySelectRebuildSizes` -/

/-- Concrete re-embedding ratio `cReemb = 1` (`reembCostBound_of_progTool`). -/
def dryCReemb (_source _J : Circulation) : ℕ := 1

/-- Concrete single-key cost `K_key` for `DrySelectRebuildSizes` and `solverStateRepSel`:
covers `selectProcessEdgeCost` at `cap = selectHeapCap cfg (namedInstance I) I.m`, `Lk = L`,
`evalCost = evalKeyCost cfg.P.d (dryMaxEmbLen I.m) L`, plus `selectUpdateLevelCost` (`+ 40`),
the core's re-embedding charge (`+ 40`), and `selEmbUpdateFromListCost` (`18 * drySlot I.m + 160`)
per re-embedded edge. -/
def dryKeyCost (_source J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let cap := selectHeapCap cfg (namedInstance I) I.m
  selectProcessEdgeCost cap L (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) L) +
    (18 * drySlot I.m + 80) + 160

/-- Concrete `selectToolMulExtra` covering every per-tool-cost select-update and suffix-rebuild
term from the solver cost trace:
* `(d + 3) * dryKeyCost` (old suffix clearing across `d + 1` levels, new suffix + level-`d`
  inserts, and `chainReembPot_rebuild_le`);
* `2 * (18 * drySlot I.m + 80)` (`selEmbCopyContract`);
* `1800 * (d + 1) * (L + 1)` (`selectPhiFillCost_paper_form` and `splitPot`);
* `2 * (selCoreLenEdgeCost L LwMax₀ + 40)` (`selCoreLenFillContract`);
* `1000 * (d + 1)` (`dgRefillFromListsCost` across `d + 1` suffix levels);
* `36 * L + 200` (`selCopyValues` + `selCoreList`). -/
def drySelectToolMulExtra (source J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let d := cfg.P.d
  let LwMax₀ := ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀
  (d + 3) * dryKeyCost source J +
    2 * (18 * drySlot I.m + 80) +
    1800 * (d + 1) * (L + 1) +
    2 * (selCoreLenEdgeCost L LwMax₀ + 40) +
    1000 * (d + 1) +
    36 * L + 200

/-- `dryKeyCost` covers `selectProcessEdgeCost + 40` (`selectUpdateLevel_paid_step_progTool`),
`selectProcessEdgeCost + 60` (`selectRebuildLevelCost_le_linear`), and
`selectProcessEdgeCost + 40 + (18 * drySlot + 80)` (joint `selEmbCopy` + `selectUpdateLevel` on
`reemb_j`). -/
theorem dryKeyCost_covers (source J : Circulation) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let cap := selectHeapCap cfg (namedInstance I) I.m
    let pEdge := selectProcessEdgeCost cap L (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) L)
    pEdge + 40 ≤ dryKeyCost source J ∧
    pEdge + 60 ≤ dryKeyCost source J ∧
    pEdge + 40 + (18 * drySlot I.m + 80) ≤ dryKeyCost source J ∧
    pEdge + (18 * drySlot I.m + 160) + 80 ≤ dryKeyCost source J := by
  dsimp only [dryKeyCost]
  omega

/-- `dryCReemb` is `SubpolyNat`. -/
theorem dryCReemb_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        dryCReemb source J ≤ f (solverConnectedAugmented J).m :=
  ⟨fun _ => 1, SubpolyNat.const 1, fun _ _ _ _ _ => le_rfl⟩

/-- `selectHeapCap cfg (namedInstance I) I.m ≤ 8 * dryM0OfM I.m`. -/
private theorem drySelectHeapCap_le (J : Circulation) :
    let I := solverConnectedAugmented J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    selectHeapCap cfg (namedInstance I) I.m ≤ 8 * dryM0OfM I.m := by
  dsimp only
  unfold selectHeapCap
  have hNf := dryNfMax_le_two_mul_M0 J
  have hMle : (solverConnectedAugmented J).m ≤ dryM0OfM (solverConnectedAugmented J).m := le_max_left _ _
  dsimp only at hNf
  omega

/-- Uniform `SubpolyNat` bound on `dryKeyCost`. -/
theorem dryKeyCost_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        dryKeyCost source J ≤ f (solverConnectedAugmented J).m := by
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  have hEmbSub : SubpolyNat dryMaxEmbLen := progTool_embLen_le_subpoly.1
  have hSlotSub : SubpolyNat drySlot := progTool_embLen_le_subpoly.2.2.2
  have hLSub : SubpolyNat dryLimbsOfM := dryLimbsOfM_subpoly
  let fPotG : ℕ → ℕ := fun M => (fd M + 1) * (130 * dryLimbsOfM M + 240) + 18 * dryLimbsOfM M + 80
  have hfPotGSub : SubpolyNat fPotG :=
    SubpolyNat.add_const (SubpolyNat.add
      (SubpolyNat.mul (SubpolyNat.add_const hfdSub 1)
        (SubpolyNat.add_const (SubpolyNat.const_mul hLSub 130) 240))
      (SubpolyNat.const_mul hLSub 18)) 80
  let fEval : ℕ → ℕ := fun M =>
    fPotG M + (dryMaxEmbLen M * (fPotG M + 148 * dryLimbsOfM M + 280) + 20) +
      120 * dryLimbsOfM M + 380
  have hfEvalSub : SubpolyNat fEval :=
    SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.add hfPotGSub
      (SubpolyNat.add_const (SubpolyNat.mul hEmbSub
        (SubpolyNat.add_const (SubpolyNat.add hfPotGSub (SubpolyNat.const_mul hLSub 148)) 280)) 20))
      (SubpolyNat.const_mul hLSub 120)) 380
  let fLogCap : ℕ → ℕ := fun M => (Nat.log 2 (8 * dryM0OfM M + 2) + 1) + 1
  have hfLogCapSub : SubpolyNat fLogCap :=
    SubpolyNat.add_const (subpolyNat_log_of_poly (PolyNat.const_mul dryM0OfM_poly 8)) 1
  let fKC : ℕ → ℕ := fun M => 304 * (dryLimbsOfM M) ^ 2 + 720 * dryLimbsOfM M + 400
  have hfKCSub : SubpolyNat fKC :=
    SubpolyNat.add_const (SubpolyNat.add
      (SubpolyNat.const_mul (SubpolyNat.pow hLSub 2) 304)
      (SubpolyNat.const_mul hLSub 720)) 400
  let f : ℕ → ℕ := fun M =>
    (fEval M + fLogCap M * (2 * fKC M + 720)) + (18 * drySlot M + 80) + 160
  have hfSub : SubpolyNat f :=
    SubpolyNat.add_const (SubpolyNat.add
      (SubpolyNat.add hfEvalSub
        (SubpolyNat.mul hfLogCapSub (SubpolyNat.add_const (SubpolyNat.const_mul hfKCSub 2) 720)))
      (SubpolyNat.add_const (SubpolyNat.const_mul hSlotSub 18) 80)) 160
  refine ⟨f, hfSub, fun _source J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  set cap := selectHeapCap cfg (namedInstance I) I.m
  have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hd : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
  have hPotG : evalEdgePotGradCostExact cfg.P.d L ≤ fPotG I.m := by
    unfold evalEdgePotGradCostExact
    dsimp only [fPotG]
    have hm := Nat.mul_le_mul (Nat.add_le_add_right hd 1) (show 130 * L + 240 ≤ 130 * dryLimbsOfM I.m + 240 by omega)
    omega
  have hEvalLe : evalKeyCost cfg.P.d (dryMaxEmbLen I.m) L ≤ fEval I.m := by
    unfold evalKeyCost evalKeyWalkLoopCost evalKeyStepCost
    dsimp only [fEval]
    have hm := Nat.mul_le_mul_left (dryMaxEmbLen I.m)
      (show evalEdgePotGradCostExact cfg.P.d L + 148 * L + 240 + 40 ≤
        fPotG I.m + 148 * dryLimbsOfM I.m + 280 by omega)
    omega
  have hCapLe : cap ≤ 8 * dryM0OfM I.m := drySelectHeapCap_le J
  have hLogLe : Nat.log 2 (cap + 1) + 2 ≤ fLogCap I.m := by
    dsimp only [fLogCap]
    have hlg : Nat.log 2 (cap + 1) ≤ Nat.log 2 (8 * dryM0OfM I.m + 2) :=
      Nat.log_mono_right (b := 2) (by omega)
    omega
  have hKCLe : keyCompareCost L ≤ fKC I.m := by
    unfold keyCompareCost
    dsimp only [fKC]
    have hsq : L ^ 2 ≤ (dryLimbsOfM I.m) ^ 2 := Nat.pow_le_pow_left hL 2
    omega
  have hProcLe : selectProcessEdgeCost cap L (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) L) ≤
      fEval I.m + fLogCap I.m * (2 * fKC I.m + 720) := by
    refine (selectKeyUpdate_cost_paper_form cap L _).trans ?_
    exact Nat.add_le_add hEvalLe (Nat.mul_le_mul hLogLe (by omega))
  unfold dryKeyCost
  dsimp only [f]
  linarith only [hProcLe]

/-- Uniform `SubpolyNat` bound on `drySelectToolMulExtra`. -/
theorem drySelectToolMulExtra_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        drySelectToolMulExtra source J ≤ f (solverConnectedAugmented J).m := by
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  obtain ⟨fLM, hfLMSub, hfLM⟩ := dryLevelM_le_subpoly
  obtain ⟨fKey, hfKeySub, hKey⟩ := dryKeyCost_le_subpoly
  have hSlotSub : SubpolyNat drySlot := progTool_embLen_le_subpoly.2.2.2
  have hLSub : SubpolyNat dryLimbsOfM := dryLimbsOfM_subpoly
  let cLw := dryCapExp + sparseCoreReadout2LimbConst
  let fArgPoly : PolyNat (fun M => (M + 1) * fLM M + 4 * dryM0OfM M) :=
    PolyNat.add (PolyNat.mul (PolyNat.add_const PolyNat.id 1) (SubpolyNat.toPolyNat hfLMSub))
      (PolyNat.const_mul dryM0OfM_poly 4)
  let fLw : ℕ → ℕ := fun M => dryLimbsOfM M + cLw * (Nat.log 2 (((M + 1) * fLM M + 4 * dryM0OfM M) + 2) + 1)
  have hfLwSub : SubpolyNat fLw :=
    SubpolyNat.add hLSub (SubpolyNat.const_mul (subpolyNat_log_of_poly fArgPoly) cLw)
  let fCL : ℕ → ℕ := fun M => 35 * dryLimbsOfM M + (1400 * (fLw M) ^ 2 + 2100 * fLw M + 850) + 160
  have hfCLSub : SubpolyNat fCL :=
    SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.const_mul hLSub 35)
      (SubpolyNat.add_const (SubpolyNat.add
        (SubpolyNat.const_mul (SubpolyNat.pow hfLwSub 2) 1400)
        (SubpolyNat.const_mul hfLwSub 2100)) 850)) 160
  let f : ℕ → ℕ := fun M =>
    (fd M + 3) * fKey M +
      2 * (18 * drySlot M + 80) +
      1800 * (fd M + 1) * (dryLimbsOfM M + 1) +
      2 * fCL M +
      1000 * (fd M + 1) +
      36 * dryLimbsOfM M + 200
  have hfSub : SubpolyNat f := by
    have h1 := SubpolyNat.mul (SubpolyNat.add_const hfdSub 3) hfKeySub
    have h2 := SubpolyNat.const_mul (SubpolyNat.add_const (SubpolyNat.const_mul hSlotSub 18) 80) 2
    have h3 := SubpolyNat.mul (SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) 1800)
      (SubpolyNat.add_const hLSub 1)
    have h4 := SubpolyNat.const_mul hfCLSub 2
    have h5 := SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) 1000
    have h6 := SubpolyNat.add_const (SubpolyNat.const_mul hLSub 36) 200
    exact SubpolyNat.mono (fun M => by dsimp only [f]; omega)
      (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add h1 h2) h3) h4) h5) h6)
  refine ⟨f, hfSub, fun source J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hd : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
  have hK : dryKeyCost source J ≤ fKey I.m := hKey source J hJn hJm hCap
  have hM0 : levelM cfg.TP cfg.P 0 ≤ (I.m + 1) * fLM I.m := hfLM J hJn hJm hCap 0 (Nat.zero_le _)
  have hN0 : cfg.N₀ = 4 * dryM0OfM I.m := rfl
  have hLw : ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀ ≤ fLw I.m := by
    unfold ordLevelLwMax
    dsimp only [fLw, cLw]
    exact Nat.add_le_add hL (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.log_mono_right (b := 2) (by omega)) 1))
  have hLleLw : L ≤ ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀ := by
    unfold ordLevelLwMax; omega
  have hCL : selCoreLenEdgeCost L (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀) + 40 ≤
      fCL I.m := by
    unfold selCoreLenEdgeCost wireCoreLenEdgeCost
    rw [max_eq_right hLleLw]
    dsimp only [fCL]
    have hsq := Nat.pow_le_pow_left hLw 2
    nlinarith only [hL, hLw, hsq]
  have hm1 : (cfg.P.d + 3) * dryKeyCost source J ≤ (fd I.m + 3) * fKey I.m :=
    Nat.mul_le_mul (by omega) hK
  have hm3 : 1800 * (cfg.P.d + 1) * (L + 1) ≤ 1800 * (fd I.m + 1) * (dryLimbsOfM I.m + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 1800 (by omega)) (by omega)
  unfold drySelectToolMulExtra
  dsimp only [f]
  linarith only [hm1, hm3, hCL, hd, hL]

/-- Build a full `DrySelectRebuildSizes` from the Init select sizes (`initSel`) and
shift select sizes (`shiftSel`), plugging in the concrete `dryKeyCost`, `dryCReemb`, and
`drySelectToolMulExtra`. -/
def mkDrySelectRebuildSizes (initSel : DryInitSelectSizes) (shiftSel : DryShiftSelectSizes) :
    DrySelectRebuildSizes where
  initSelectSpace := initSel.initSelectSpace
  initSelectFixed := initSel.initSelectFixed
  termSelectSpace := shiftSel.termSelectSpace
  deepSelectSpace := shiftSel.deepSelectSpace
  deepSelectFixed := shiftSel.deepSelectFixed
  termSelectFixed := shiftSel.termSelectFixed
  keyCost := dryKeyCost
  cReemb := dryCReemb
  selectToolMulExtra := drySelectToolMulExtra

/-- Lift `DryInitSelectSizeBounds` and `DryShiftSelectSizeBounds` to `DrySelectRebuildSizeBounds`
using the proved concrete bounds (`dryKeyCost_le_subpoly`, `dryCReemb_le_subpoly`,
`drySelectToolMulExtra_le_subpoly`). -/
theorem mkDrySelectRebuildSizeBounds {initSel : DryInitSelectSizes} {shiftSel : DryShiftSelectSizes}
    (hInit : DryInitSelectSizeBounds initSel) (hShift : DryShiftSelectSizeBounds shiftSel) :
    DrySelectRebuildSizeBounds (mkDrySelectRebuildSizes initSel shiftSel) where
  hInitSelectSpacePoly := hInit.hInitSelectSpacePoly
  hInitSelectFixedSub := hInit.hInitSelectFixedSub
  hTermSelectSpacePoly := hShift.hTermSelectSpacePoly
  hDeepSelectSpacePoly := hShift.hDeepSelectSpacePoly
  hDeepSelectFixedSub := hShift.hDeepSelectFixedSub
  hTermSelectFixedSub := hShift.hTermSelectFixedSub
  hKeyCostSub := dryKeyCost_le_subpoly
  hCReembSub := dryCReemb_le_subpoly
  hSelectToolMulExtraSub := drySelectToolMulExtra_le_subpoly

end MinCostFlow.Final.DryRun

end
