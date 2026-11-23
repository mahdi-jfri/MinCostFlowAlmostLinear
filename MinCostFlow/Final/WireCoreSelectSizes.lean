module

public import MinCostFlow.Final.WireDeepSelectSizes
public import MinCostFlow.MinRatio.SelectUpdatePostCoreCost
import Mathlib.Tactic

/-!
# Concrete select-aware chain-update sizes (`WireCoreSelectSizes`)

Lifts any inner chain-update core size bundle `innerSz : DryCoreOpenSizes` (for a core block
satisfying `OrdChainUpdateCoreSpecWExtKFBL`) to the select-aware `Update` size bundle
`dryCoreSelectSizes Psc innerSz : DryCoreOpenSizes` by adding the post-core select-maintenance
space, fixed-cost, tool-multiplier, and tree-multiplier bounds from `SelectUpdatePostCoreCost.lean`
(at `uWordsMul = 5`, `uWordsFix = cfg.P.d`, `K = dryKeyCost`, `c = dryCReemb = 1`, matching
`SmallBatchAt` in `UpdateCoreSelectOutAt`):

1. `dryCoreSelectSpace`: `innerSp + selectUpdatePostCoreSpaceBound ... innerSp`.
2. `dryCoreSelectFixed`: `innerFixed u + selectUpdatePostCoreFixedBound ... u cfg.P.d + 40`.
3. `dryCoreSelectToolMul`: `innerToolMul + selectUpdatePostCoreToolMulBound ... 5`.
4. `dryCoreSelectTreeMul`: `innerTreeMul + selectUpdatePostCoreTreeMulBound (drySlot I.m) (dryKeyCost source J)`.
5. `dryCoreSelectSizeBounds`: lifts `DryCoreOpenSizeBounds innerSz` to
   `DryCoreOpenSizeBounds (dryCoreSelectSizes Psc innerSz)` (monotonicity in `u`, `PolyNat` space,
   linear `SubpolyNat` fixed cost, and `SubpolyNat` tool/tree multipliers).
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-- Concrete `coreSpace` for select-aware `Update`: inner core scratch plus
`selectUpdatePostCoreSpaceBound`. -/
def dryCoreSelectSpace (innerSz : DryCoreOpenSizes) (source J : Circulation) (u : ℕ) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let G := namedInstance I
  let innerSp := innerSz.coreSpace source J u
  innerSp +
    selectUpdatePostCoreSpaceBound cfg.P.d G.n (initTargetCap cfg G) (selectHeapCap cfg G I.m)
      L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀ (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L)
      innerSp

/-- Concrete `coreFixed` for select-aware `Update`: inner core fixed cost plus
`selectUpdatePostCoreFixedBound` (at `uWordsFix = cfg.P.d`, `mD = levelM cfg.TP cfg.P cfg.P.d`)
plus wrapper glue (`40`). -/
def dryCoreSelectFixed (Psc : DrySparseCorePieces) (innerSz : DryCoreOpenSizes)
    (source J : Circulation) (u : ℕ) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
  innerSz.coreFixed source J u +
    selectUpdatePostCoreFixedBound PscP.readout cfg.P.d L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀
      (drySlot I.m) (dryKeyCost source J) (dryCReemb source J) cfg.P.d
      (levelM cfg.TP cfg.P cfg.P.d) + 40

/-- Concrete `coreToolMul` for select-aware `Update`: inner core tool multiplier plus
`selectUpdatePostCoreToolMulBound` (at `uWordsMul = 10`). -/
def dryCoreSelectToolMul (innerSz : DryCoreOpenSizes) (source J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  innerSz.coreToolMul source J +
    selectUpdatePostCoreToolMulBound cfg.P.d L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀
      (drySlot I.m) (dryKeyCost source J) (dryCReemb source J) 10

/-- Concrete `coreTreeMul` for select-aware `Update`: inner core tree multiplier plus
`selectUpdatePostCoreTreeMulBound`. -/
def dryCoreSelectTreeMul (innerSz : DryCoreOpenSizes) (source J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  innerSz.coreTreeMul source J +
    selectUpdatePostCoreTreeMulBound (drySlot I.m) (dryKeyCost source J)

/-- Select-aware `DryCoreOpenSizes` wrapping any inner core size bundle `innerSz`. -/
def dryCoreSelectSizes (Psc : DrySparseCorePieces) (innerSz : DryCoreOpenSizes) :
    DryCoreOpenSizes where
  coreSpace := dryCoreSelectSpace innerSz
  coreFixed := dryCoreSelectFixed Psc innerSz
  coreToolMul := dryCoreSelectToolMul innerSz
  coreTreeMul := dryCoreSelectTreeMul innerSz

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

private lemma selectUpdatePostCoreSpaceBound_mono_coreSp
    {d vCap eCap cap L capExp M₀ N₀ evalSpace s₁ s₂ : ℕ} (h : s₁ ≤ s₂) :
    selectUpdatePostCoreSpaceBound d vCap eCap cap L capExp M₀ N₀ evalSpace s₁ ≤
      selectUpdatePostCoreSpaceBound d vCap eCap cap L capExp M₀ N₀ evalSpace s₂ := by
  unfold selectUpdatePostCoreSpaceBound
  dsimp only
  have h1 := Nat.mul_le_mul_right (selCoreLenEdgeSpace L (ordLevelLwMax L capExp M₀ N₀)) h
  have h2 := Nat.mul_le_mul_left d (Nat.add_le_add h h1)
  have h3 := Nat.mul_le_mul_left d (Nat.add_le_add_left (Nat.mul_le_mul_left 8 h) 2)
  have h4 := Nat.mul_le_mul_left d (Nat.mul_le_mul_right (selectProcessEdgeSpace cap L evalSpace)
    (Nat.mul_le_mul_left 4 h))
  omega

private lemma selCoreLenEdgeSpace_le_quad_cs {L a b : ℕ} (hLa : L ≤ a) (hab : a ≤ b) :
    selCoreLenEdgeSpace L a ≤ 20 * (b * b) + 40 * b + 10 := by
  unfold selCoreLenEdgeSpace wireCoreLenEdgeSpace Num.integerDivideSpace Num.unsignedDivideSpace
  rw [max_eq_right hLa]
  have hsq : a * a ≤ b * b := Nat.mul_le_mul hab hab
  nlinarith

private lemma evalKeySpace_le_poly_cs {d₁ d₂ e L₁ L₂ : ℕ} (hd : d₁ ≤ d₂) (hL : L₁ ≤ L₂) :
    evalKeySpace d₁ e L₁ ≤
      (d₂ + 1) * (3 * L₂) + e * ((d₂ + 1) * (3 * L₂) + 3 * L₂) + 4 * L₂ + 4 := by
  simp only [evalKeySpace, evalEdgePotGradSpace, evalKeyWalkLoopSpace, evalKeyStepSpace]
  have h1 := Nat.mul_le_mul (Nat.add_le_add_right hd 1) (Nat.mul_le_mul_left 3 hL)
  have h2 := Nat.mul_le_mul_left e (Nat.add_le_add h1 (Nat.mul_le_mul_left 3 hL))
  omega

private lemma drySelectHeapCap_le_cs (J : Circulation) :
    let I := solverConnectedAugmented J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    selectHeapCap cfg (namedInstance I) I.m ≤ 8 * dryM0OfM I.m := by
  dsimp only
  unfold selectHeapCap
  have hNf := dryNfMax_le_two_mul_M0 J
  have hMle : (solverConnectedAugmented J).m ≤ dryM0OfM (solverConnectedAugmented J).m :=
    le_max_left _ _
  dsimp only at hNf
  omega

/-- Uniform `DryCoreOpenSizeBounds` lift for `dryCoreSelectSizes Psc innerSz`. -/
theorem dryCoreSelectSizeBounds (Psc : DrySparseCorePieces) {innerSz : DryCoreOpenSizes}
    (hInner : DryCoreOpenSizeBounds innerSz) :
    DryCoreOpenSizeBounds (dryCoreSelectSizes Psc innerSz) where
  hCoreSpaceMono := fun source J hJn hJm hCap u₁ u₂ hu => by
    have hm := hInner.hCoreSpaceMono source J hJn hJm hCap hu
    unfold dryCoreSelectSizes dryCoreSelectSpace
    exact Nat.add_le_add hm (selectUpdatePostCoreSpaceBound_mono_coreSp hm)
  hCoreSpacePoly := by
    obtain ⟨fCoreSp, hfCoreSpP, hCoreSp⟩ := hInner.hCoreSpacePoly
    obtain ⟨fDeepSp, hfDeepSpP, hDeepSp⟩ := dryDeepSelectSpace_le_poly
    obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
    obtain ⟨fLM, hfLMSub, hfLM⟩ := dryLevelM_le_subpoly
    have hfdP : PolyNat fd := SubpolyNat.toPolyNat hfdSub
    have hfLMP : PolyNat fLM := SubpolyNat.toPolyNat hfLMSub
    have hLP : PolyNat dryLimbsOfM := SubpolyNat.toPolyNat dryLimbsOfM_subpoly
    have hEmbP : PolyNat dryMaxEmbLen := SubpolyNat.toPolyNat progTool_embLen_le_subpoly.1
    have hM0P : PolyNat dryM0OfM := dryM0OfM_poly
    let cLw : ℕ := dryCapExp + sparseCoreReadout2LimbConst
    let fLw : ℕ → ℕ := fun M =>
      dryLimbsOfM M + cLw * (Nat.log 2 ((M + 1) * fLM M + 4 * dryM0OfM M + 2) + 1)
    have hfLwP : PolyNat fLw := by
      have hlogP : PolyNat (fun M => Nat.log 2 ((M + 1) * fLM M + 4 * dryM0OfM M + 2) + 1) :=
        PolyNat.mono (fun M => Nat.add_le_add_right (Nat.log_le_self 2 _) 1)
          (PolyNat.add_const (PolyNat.add_const (PolyNat.add
            (PolyNat.mul (PolyNat.add_const PolyNat.id 1) hfLMP) (PolyNat.const_mul hM0P 4)) 2) 1)
      exact PolyNat.add hLP (PolyNat.const_mul hlogP cLw)
    let fEdgeSp : ℕ → ℕ := fun M => 20 * (fLw M * fLw M) + 40 * fLw M + 10
    have hfEdgeSpP : PolyNat fEdgeSp :=
      PolyNat.add_const (PolyNat.add (PolyNat.const_mul (PolyNat.mul hfLwP hfLwP) 20)
        (PolyNat.const_mul hfLwP 40)) 10
    let fEvalSp : ℕ → ℕ := fun M =>
      (fd M + 1) * (3 * dryLimbsOfM M) +
        dryMaxEmbLen M * ((fd M + 1) * (3 * dryLimbsOfM M) + 3 * dryLimbsOfM M) +
        4 * dryLimbsOfM M + 4
    have hfEvalSpP : PolyNat fEvalSp :=
      PolyNat.add_const (PolyNat.add (PolyNat.add
        (PolyNat.mul (PolyNat.add_const hfdP 1) (PolyNat.const_mul hLP 3))
        (PolyNat.mul hEmbP (PolyNat.add
          (PolyNat.mul (PolyNat.add_const hfdP 1) (PolyNat.const_mul hLP 3))
          (PolyNat.const_mul hLP 3))))
        (PolyNat.const_mul hLP 4)) 4
    let fLogCap : ℕ → ℕ := fun M => 2 * Nat.log 2 (8 * dryM0OfM M + 2) + 1
    have hfLogCapP : PolyNat fLogCap :=
      PolyNat.mono (fun M => Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.log_le_self 2 _)) 1)
        (PolyNat.add_const (PolyNat.const_mul (PolyNat.add_const (PolyNat.const_mul hM0P 8) 2) 2) 1)
    let fProcSp : ℕ → ℕ := fun M =>
      2 * dryLimbsOfM M + fEvalSp M + fLogCap M * (16 * dryLimbsOfM M)
    have hfProcSpP : PolyNat fProcSp :=
      PolyNat.add (PolyNat.add (PolyNat.const_mul hLP 2) hfEvalSpP)
        (PolyNat.mul hfLogCapP (PolyNat.const_mul hLP 16))
    let f : ℕ → ℕ := fun M =>
      fCoreSp M +
        (fCoreSp M +
          fd M * (fCoreSp M + fCoreSp M * fEdgeSp M) +
          fd M * (2 + 8 * fCoreSp M) +
          fDeepSp M +
          fd M * (4 * fCoreSp M * fProcSp M))
    have hfP : PolyNat f := by
      have h1 := PolyNat.mul hfdP (PolyNat.add hfCoreSpP (PolyNat.mul hfCoreSpP hfEdgeSpP))
      have h2 := PolyNat.mul hfdP (PolyNat.add (PolyNat.const 2) (PolyNat.const_mul hfCoreSpP 8))
      have h3 := PolyNat.mul hfdP (PolyNat.mul (PolyNat.const_mul hfCoreSpP 4) hfProcSpP)
      exact PolyNat.add hfCoreSpP
        (PolyNat.add (PolyNat.add (PolyNat.add (PolyNat.add hfCoreSpP h1) h2) hfDeepSpP) h3)
    refine ⟨f, hfP, fun source J hJn hJm hCap => ?_⟩
    set I := solverConnectedAugmented J
    set V := solverPenalty J.m
    set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    set L := ipmQualityLimbs I.m V k
    set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    set G := namedInstance I
    have hCS : innerSz.coreSpace source J (2 * I.m) ≤ fCoreSp I.m := hCoreSp source J hJn hJm hCap
    have hDS : dryDeepSelectSpace source J ≤ fDeepSp I.m := hDeepSp source J hJn hJm hCap
    have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
    have hd : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
    have hCapLe : selectHeapCap cfg G I.m ≤ 8 * dryM0OfM I.m := drySelectHeapCap_le_cs J
    have hM0 : levelM cfg.TP cfg.P 0 ≤ (I.m + 1) * fLM I.m := hfLM J hJn hJm hCap 0 (Nat.zero_le _)
    have hLw : ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀ ≤ fLw I.m := by
      unfold ordLevelLwMax; dsimp only [fLw, cLw]
      have hN0 : cfg.N₀ = 4 * dryM0OfM I.m := rfl
      exact Nat.add_le_add hL (Nat.mul_le_mul_left _
        (Nat.add_le_add_right (Nat.log_mono_right (b := 2)
          (Nat.add_le_add_right (Nat.add_le_add hM0 (le_of_eq hN0)) 2)) 1))
    have hEdgeSp : selCoreLenEdgeSpace L (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀) ≤
        fEdgeSp I.m := selCoreLenEdgeSpace_le_quad_cs (Nat.le_add_right _ _) hLw
    have hEval : evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L ≤ fEvalSp I.m :=
      evalKeySpace_le_poly_cs hd hL
    have hlg : 2 * Nat.log 2 (selectHeapCap cfg G I.m + 1) + 1 ≤ fLogCap I.m := by
      dsimp only [fLogCap]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 2
        (Nat.log_mono_right (b := 2) (by omega))) 1
    have hProcSp : selectProcessEdgeSpace (selectHeapCap cfg G I.m) L
        (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L) ≤ fProcSp I.m := by
      unfold selectProcessEdgeSpace heapRebalanceSpace keyCompareSpace
      dsimp only [fProcSp]
      exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 hL) hEval)
        (Nat.mul_le_mul hlg (Nat.mul_le_mul_left 16 hL))
    have hT1 : cfg.P.d * (innerSz.coreSpace source J (2 * I.m) +
        innerSz.coreSpace source J (2 * I.m) *
          selCoreLenEdgeSpace L (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀)) ≤
        fd I.m * (fCoreSp I.m + fCoreSp I.m * fEdgeSp I.m) :=
      Nat.mul_le_mul hd (Nat.add_le_add hCS (Nat.mul_le_mul hCS hEdgeSp))
    have hT2 : cfg.P.d * (2 + 8 * innerSz.coreSpace source J (2 * I.m)) ≤
        fd I.m * (2 + 8 * fCoreSp I.m) :=
      Nat.mul_le_mul hd (Nat.add_le_add_left (Nat.mul_le_mul_left 8 hCS) 2)
    have hT3 : cfg.P.d * (4 * innerSz.coreSpace source J (2 * I.m) *
        selectProcessEdgeSpace (selectHeapCap cfg G I.m) L
          (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L)) ≤
        fd I.m * (4 * fCoreSp I.m * fProcSp I.m) :=
      Nat.mul_le_mul hd (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hCS) hProcSp)
    change innerSz.coreSpace source J (2 * I.m) +
      selectUpdatePostCoreSpaceBound cfg.P.d G.n (initTargetCap cfg G) (selectHeapCap cfg G I.m)
        L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀ (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L)
        (innerSz.coreSpace source J (2 * I.m)) ≤ f I.m
    unfold selectUpdatePostCoreSpaceBound
    dsimp only [f]
    have hDeepEq : shiftDeepSelectSpaceBound cfg.P.d G.n (initTargetCap cfg G)
        (selectHeapCap cfg G I.m) L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀
        (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L) = dryDeepSelectSpace source J := rfl
    rw [hDeepEq]
    omega
  hCoreFixedSubpoly := by
    obtain ⟨fRho0In, fRho1In, hf0In, hf1In, hCoreF⟩ := hInner.hCoreFixedSubpoly
    obtain ⟨fDeepFix, hfDeepFixSub, hDeepFix⟩ := dryDeepSelectFixed_le_subpoly Psc
    obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
    obtain ⟨fLM, hfLMSub, hfLM⟩ := dryLevelM_le_subpoly
    obtain ⟨fKey, hfKeySub, hKey⟩ := dryKeyCost_le_subpoly
    have hSlotSub : SubpolyNat drySlot := progTool_embLen_le_subpoly.2.2.2
    have hLSub : SubpolyNat dryLimbsOfM := dryLimbsOfM_subpoly
    have hMdSub : SubpolyNat (fun M => 2 ^ dryKOfM M) := subpolyNat_two_pow_dryKOfM
    let cLw := dryCapExp + sparseCoreReadout2LimbConst
    let fArgPoly : PolyNat (fun M => (M + 1) * fLM M + 4 * dryM0OfM M) :=
      PolyNat.add (PolyNat.mul (PolyNat.add_const PolyNat.id 1) (SubpolyNat.toPolyNat hfLMSub))
        (PolyNat.const_mul dryM0OfM_poly 4)
    let fLw : ℕ → ℕ := fun M =>
      dryLimbsOfM M + cLw * (Nat.log 2 (((M + 1) * fLM M + 4 * dryM0OfM M) + 2) + 1)
    have hfLwSub : SubpolyNat fLw :=
      SubpolyNat.add hLSub (SubpolyNat.const_mul (subpolyNat_log_of_poly fArgPoly) cLw)
    let fCL : ℕ → ℕ := fun M => 35 * dryLimbsOfM M + (1400 * (fLw M) ^ 2 + 2100 * fLw M + 850) + 160
    have hfCLSub : SubpolyNat fCL :=
      SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.const_mul hLSub 35)
        (SubpolyNat.add_const (SubpolyNat.add
          (SubpolyNat.const_mul (SubpolyNat.pow hfLwSub 2) 1400)
          (SubpolyNat.const_mul hfLwSub 2100)) 850)) 160
    let fSufC : ℕ → ℕ := fun M =>
      4 * fKey M + (18 * drySlot M + 80) + 1800 * (fd M + 1) * (dryLimbsOfM M + 1) +
        2 * fCL M + 140 * fd M + 2450
    have hfSufCSub : SubpolyNat fSufC := by
      have h1 := SubpolyNat.const_mul hfKeySub 4
      have h2 := SubpolyNat.add_const (SubpolyNat.const_mul hSlotSub 18) 80
      have h3 := SubpolyNat.mul (SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) 1800)
        (SubpolyNat.add_const hLSub 1)
      have h4 := SubpolyNat.const_mul hfCLSub 2
      have h5 := SubpolyNat.add_const (SubpolyNat.const_mul hfdSub 140) 2450
      exact SubpolyNat.mono (fun M => by dsimp only [fSufC]; omega)
        (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add h1 h2) h3) h4) h5)
    let rc : ℕ := (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).readout
    let fRho0 : ℕ → ℕ := fun M =>
      fRho0In M + fDeepFix M + 80 + fd M * (rc + fKey M + 1600) + 670 * fd M + 740 +
        (2 ^ dryKOfM M) * fSufC M
    have hfRho0Sub : SubpolyNat fRho0 := by
      have h1 := SubpolyNat.add hf0In hfDeepFixSub
      have h2 := SubpolyNat.mul hfdSub
        (SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.const rc) hfKeySub) 1600)
      have h3 := SubpolyNat.const_mul hfdSub 670
      have h4 := SubpolyNat.mul hMdSub hfSufCSub
      exact SubpolyNat.add
        (SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add_const h1 80) h2) h3) 740)
        h4
    refine ⟨fRho0, fRho1In, hfRho0Sub, hf1In, fun source J hJn hJm hCap u hu => ?_⟩
    set I := solverConnectedAugmented J
    set V := solverPenalty J.m
    set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    set L := ipmQualityLimbs I.m V k
    set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    have hInF : innerSz.coreFixed source J u ≤ fRho0In I.m + fRho1In I.m * u :=
      hCoreF source J hJn hJm hCap u hu
    have hDF : dryDeepSelectFixed Psc source J ≤ fDeepFix I.m := hDeepFix source J hJn hJm hCap
    have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
    have hd : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
    have hK : dryKeyCost source J ≤ fKey I.m := hKey source J hJn hJm hCap
    have hmD : levelM cfg.TP cfg.P cfg.P.d ≤ 2 ^ dryKOfM I.m :=
      dryLevelMd_le_two_pow_dryKOfM J hJn hJm hCap
    have hM0 : levelM cfg.TP cfg.P 0 ≤ (I.m + 1) * fLM I.m := hfLM J hJn hJm hCap 0 (Nat.zero_le _)
    have hN0 : cfg.N₀ = 4 * dryM0OfM I.m := rfl
    have hLw : ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀ ≤ fLw I.m := by
      unfold ordLevelLwMax; dsimp only [fLw, cLw]
      exact Nat.add_le_add hL (Nat.mul_le_mul_left _
        (Nat.add_le_add_right (Nat.log_mono_right (b := 2) (by omega)) 1))
    have hLleLw : L ≤ ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀ :=
      Nat.le_add_right _ _
    have hCL : selCoreLenEdgeCost L (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀) + 40 ≤
        fCL I.m := by
      unfold selCoreLenEdgeCost wireCoreLenEdgeCost
      rw [max_eq_right hLleLw]
      dsimp only [fCL]
      have hsq := Nat.pow_le_pow_left hLw 2
      nlinarith only [hL, hLw, hsq]
    have hMulD : cfg.P.d * (rc + dryKeyCost source J * 1 + 1600) ≤
        fd I.m * (rc + fKey I.m + 1600) :=
      Nat.mul_le_mul hd (by omega)
    have hSufCLe :
        4 * dryKeyCost source J + (18 * drySlot I.m + 80) + 1800 * (cfg.P.d + 1) * (L + 1) +
          2 * (selCoreLenEdgeCost L (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀) + 40) +
          140 * cfg.P.d + 2450 ≤ fSufC I.m := by
      dsimp only [fSufC]
      have hm3 : 1800 * (cfg.P.d + 1) * (L + 1) ≤ 1800 * (fd I.m + 1) * (dryLimbsOfM I.m + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 1800 (by omega)) (by omega)
      have hm4 : 2 * (selCoreLenEdgeCost L (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀) + 40) ≤
          2 * fCL I.m := Nat.mul_le_mul_left 2 hCL
      exact Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hK) (18 * drySlot I.m + 80))
          hm3) hm4) (Nat.mul_le_mul_left 140 hd)) 2450
    have hMdMul : levelM cfg.TP cfg.P cfg.P.d *
        (4 * dryKeyCost source J + (18 * drySlot I.m + 80) + 1800 * (cfg.P.d + 1) * (L + 1) +
          2 * (selCoreLenEdgeCost L (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀) + 40) +
          140 * cfg.P.d + 2450) ≤ (2 ^ dryKOfM I.m) * fSufC I.m :=
      Nat.mul_le_mul hmD hSufCLe
    unfold dryCoreSelectSizes dryCoreSelectFixed selectUpdatePostCoreFixedBound dryCReemb
    dsimp only [fRho0]
    have hDeepEq : shiftDeepSelectFixedBound rc cfg.P.d L = dryDeepSelectFixed Psc source J := rfl
    change innerSz.coreFixed source J u +
      (shiftDeepSelectFixedBound rc cfg.P.d L + 80 +
        cfg.P.d * (rc + dryKeyCost source J * 1 + 1600) + 670 * cfg.P.d + 700 +
        levelM cfg.TP cfg.P cfg.P.d *
          (4 * dryKeyCost source J + (18 * drySlot I.m + 80) + 1800 * (cfg.P.d + 1) * (L + 1) +
            2 * (selCoreLenEdgeCost L (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀) + 40) +
            140 * cfg.P.d + 2450)) + 40 ≤
      fRho0In I.m + fDeepFix I.m + 80 + fd I.m * (rc + fKey I.m + 1600) + 670 * fd I.m + 740 +
        (2 ^ dryKOfM I.m) * fSufC I.m + fRho1In I.m * u
    rw [hDeepEq]
    have h1 : innerSz.coreFixed source J u +
        (dryDeepSelectFixed Psc source J + 80 +
          cfg.P.d * (rc + dryKeyCost source J * 1 + 1600) + 670 * cfg.P.d + 700 +
          levelM cfg.TP cfg.P cfg.P.d *
            (4 * dryKeyCost source J + (18 * drySlot I.m + 80) + 1800 * (cfg.P.d + 1) * (L + 1) +
              2 * (selCoreLenEdgeCost L (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀) + 40) +
              140 * cfg.P.d + 2450)) + 40 ≤
        (fRho0In I.m + fRho1In I.m * u) +
          (fDeepFix I.m + 80 + fd I.m * (rc + fKey I.m + 1600) + 670 * fd I.m + 700 +
            (2 ^ dryKOfM I.m) * fSufC I.m) + 40 :=
      Nat.add_le_add_right (Nat.add_le_add hInF
        (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add_right hDF 80) hMulD)
          (Nat.mul_le_mul_left 670 hd)) 700) hMdMul)) 40
    exact h1.trans (le_of_eq (by ring))
  hCoreMulSubpoly := by
    obtain ⟨fToolIn, fTreeIn, hfToolIn, hfTreeIn, hMulIn⟩ := hInner.hCoreMulSubpoly
    obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
    obtain ⟨fLM, hfLMSub, hfLM⟩ := dryLevelM_le_subpoly
    obtain ⟨fKey, hfKeySub, hKey⟩ := dryKeyCost_le_subpoly
    have hSlotSub : SubpolyNat drySlot := progTool_embLen_le_subpoly.2.2.2
    have hLSub : SubpolyNat dryLimbsOfM := dryLimbsOfM_subpoly
    let cLw := dryCapExp + sparseCoreReadout2LimbConst
    let fArgPoly : PolyNat (fun M => (M + 1) * fLM M + 4 * dryM0OfM M) :=
      PolyNat.add (PolyNat.mul (PolyNat.add_const PolyNat.id 1) (SubpolyNat.toPolyNat hfLMSub))
        (PolyNat.const_mul dryM0OfM_poly 4)
    let fLw : ℕ → ℕ := fun M =>
      dryLimbsOfM M + cLw * (Nat.log 2 (((M + 1) * fLM M + 4 * dryM0OfM M) + 2) + 1)
    have hfLwSub : SubpolyNat fLw :=
      SubpolyNat.add hLSub (SubpolyNat.const_mul (subpolyNat_log_of_poly fArgPoly) cLw)
    let fCL : ℕ → ℕ := fun M => 35 * dryLimbsOfM M + (1400 * (fLw M) ^ 2 + 2100 * fLw M + 850) + 160
    have hfCLSub : SubpolyNat fCL :=
      SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.const_mul hLSub 35)
        (SubpolyNat.add_const (SubpolyNat.add
          (SubpolyNat.const_mul (SubpolyNat.pow hfLwSub 2) 1400)
          (SubpolyNat.const_mul hfLwSub 2100)) 850)) 160
    let fTool : ℕ → ℕ := fun M =>
      fToolIn M +
        (10 * fKey M + 6700 + (90 * drySlot M + 720) +
          1800 * (fd M + 1) * (dryLimbsOfM M + 1) +
          4 * fCL M + 140 * fd M + 126 * dryLimbsOfM M + 3210)
    let fTree : ℕ → ℕ := fun M => fTreeIn M + (fKey M + 18 * drySlot M + 650)
    have hfToolSub : SubpolyNat fTool := by
      have h1 := SubpolyNat.add_const (SubpolyNat.const_mul hfKeySub 10) 6700
      have h2 := SubpolyNat.add_const (SubpolyNat.const_mul hSlotSub 90) 720
      have h3 := SubpolyNat.mul (SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) 1800)
        (SubpolyNat.add_const hLSub 1)
      have h4 := SubpolyNat.const_mul hfCLSub 4
      have h5 := SubpolyNat.const_mul hfdSub 140
      have h6 := SubpolyNat.add_const (SubpolyNat.const_mul hLSub 126) 3210
      exact SubpolyNat.add hfToolIn
        (SubpolyNat.mono (fun M => by omega)
          (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add h1 h2) h3) h4) h5) h6))
    have hfTreeSub : SubpolyNat fTree :=
      SubpolyNat.add hfTreeIn
        (SubpolyNat.add_const (SubpolyNat.add hfKeySub (SubpolyNat.const_mul hSlotSub 18)) 650)
    refine ⟨fTool, fTree, hfToolSub, hfTreeSub, fun source J hJn hJm hCap => ?_⟩
    dsimp only [dryCoreSelectSizes, dryCoreSelectToolMul, dryCoreSelectTreeMul,
      selectUpdatePostCoreToolMulBound, selectUpdatePostCoreTreeMulBound, dryCReemb, fTool, fTree]
    set I := solverConnectedAugmented J
    set V := solverPenalty J.m
    set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    set L := ipmQualityLimbs I.m V k
    set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    obtain ⟨hToolInLe, hTreeInLe⟩ := hMulIn source J hJn hJm hCap
    have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
    have hd : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
    have hK : dryKeyCost source J ≤ fKey I.m := hKey source J hJn hJm hCap
    have hM0 : levelM cfg.TP cfg.P 0 ≤ (I.m + 1) * fLM I.m := hfLM J hJn hJm hCap 0 (Nat.zero_le _)
    have hN0 : cfg.N₀ = 4 * dryM0OfM I.m := rfl
    have hLw : ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀ ≤ fLw I.m := by
      unfold ordLevelLwMax; dsimp only [fLw, cLw]
      exact Nat.add_le_add hL (Nat.mul_le_mul_left _
        (Nat.add_le_add_right (Nat.log_mono_right (b := 2) (by omega)) 1))
    have hLleLw : L ≤ ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀ :=
      Nat.le_add_right _ _
    have hCL : selCoreLenEdgeCost L (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀) + 40 ≤
        fCL I.m := by
      unfold selCoreLenEdgeCost wireCoreLenEdgeCost
      rw [max_eq_right hLleLw]
      dsimp only [fCL]
      have hsq := Nat.pow_le_pow_left hLw 2
      nlinarith only [hL, hLw, hsq]
    have hm3 : 1800 * (cfg.P.d + 1) * (L + 1) ≤ 1800 * (fd I.m + 1) * (dryLimbsOfM I.m + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 1800 (by omega)) (by omega)
    constructor
    · have h1 : (9 + 1) * dryKeyCost source J ≤ 10 * fKey I.m := Nat.mul_le_mul_left 10 hK
      have h2 : 4 * (selCoreLenEdgeCost L (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀) + 40) ≤
          4 * fCL I.m := Nat.mul_le_mul_left 4 hCL
      have h3 : 140 * cfg.P.d ≤ 140 * fd I.m := Nat.mul_le_mul_left 140 hd
      have h4 : 126 * L ≤ 126 * dryLimbsOfM I.m := Nat.mul_le_mul_left 126 hL
      exact Nat.add_le_add hToolInLe
        (Nat.add_le_add_right
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add
                  (Nat.add_le_add_right (Nat.add_le_add_right h1 6700) (90 * drySlot I.m + 720))
                  hm3) h2) h3) h4) 3210)
    · exact Nat.add_le_add hTreeInLe
        (Nat.add_le_add_right (Nat.add_le_add_right hK (18 * drySlot I.m)) 650)

end MinCostFlow.Final.DryRun

end
