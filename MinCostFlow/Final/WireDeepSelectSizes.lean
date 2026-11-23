module

public import MinCostFlow.Final.WireSelectSizes
public import MinCostFlow.Final.WireTermSelectSizes
public import MinCostFlow.MinRatio.WireShiftDeepSelectCost
import Mathlib.Tactic

/-!
# Concrete deep-shift select-refresh space, fixed cost, and multiplier bounds (`WireDeepSelectSizes`)

Defines the concrete `deepSelectSpace` and `deepSelectFixed` fields of `DryShiftSelectSizes`
matching `shiftDeepSelectSpaceBound` and `shiftDeepSelectFixedBound`
(`MinRatio/WireShiftDeepSelectCost.lean`) at the dry-run parameters, and proves:

1. `dryDeepSelectSpace_le_poly`: `dryDeepSelectSpace` is bounded by a `PolyNat` function of
   `(solverConnectedAugmented J).m` (discharging `DryShiftSelectSizeBounds.hDeepSelectSpacePoly`).
2. `dryDeepSelectFixed_le_subpoly`: `dryDeepSelectFixed Psc` is bounded by a `SubpolyNat` function
   of `(solverConnectedAugmented J).m` (discharging `DryShiftSelectSizeBounds.hDeepSelectFixedSub`).
3. `dryDeepSelectToolMul_le`: `deepShiftToolMulBound ... + shiftDeepSelectToolMulBound ... ≤
   dryToolMul Psc selSz source J` whenever `selSz.keyCost = dryKeyCost`, `selSz.cReemb = dryCReemb`,
   and `selSz.selectToolMulExtra = drySelectToolMulExtra` (so the amortized select-refresh cost of
   `shiftDeepSelectBody` fits into `dryToolMul` as defined in `WireSelectSizes.lean`).
4. `DryTermSelectSizes` / `DryTermSelectSizeBounds` and `mkDryShiftSelectSizes` /
   `mkDryShiftSelectSizeBounds`: plugs in `dryDeepSelectSpace` and `dryDeepSelectFixed Psc` while
   leaving the term-shift fields (`termSelectSpace`, `termSelectFixed`) as parameters.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-- Concrete `deepSelectSpace` matching `shiftDeepSelectSpaceBound`
(`WireShiftDeepSelectCost.lean`) at the dry-run parameters `vCap = (namedInstance I).n`,
`eCap = initTargetCap cfg (namedInstance I)`, `cap = selectHeapCap cfg (namedInstance I) I.m`,
`M₀ = levelM cfg.TP cfg.P 0`, and `evalSpace = evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L`. -/
def dryDeepSelectSpace (_source J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let G := namedInstance I
  shiftDeepSelectSpaceBound cfg.P.d G.n (initTargetCap cfg G) (selectHeapCap cfg G I.m)
    L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀ (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L)

/-- Concrete `deepSelectFixed` matching `shiftDeepSelectFixedBound`
(`WireShiftDeepSelectCost.lean`) at `readoutCost = (drySCParams Psc dryCapExp limbMul).readout`. -/
def dryDeepSelectFixed (Psc : DrySparseCorePieces) (_source J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
  shiftDeepSelectFixedBound PscP.readout cfg.P.d L

/-- Term-shift select size fields, given as parameters (splitting `DryShiftSelectSizes` so
`deepSelectSpace` and `deepSelectFixed` are fixed concretely by `mkDryShiftSelectSizes`). -/
structure DryTermSelectSizes where
  termSelectSpace : Circulation → Circulation → ℕ
  termSelectFixed : Circulation → Circulation → ℕ

/-- `PolyNat` / `SubpolyNat` bounds for the term-shift select size fields. -/
structure DryTermSelectSizeBounds (termSel : DryTermSelectSizes) : Prop where
  hTermSelectSpacePoly :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        termSel.termSelectSpace source J ≤ f (solverConnectedAugmented J).m
  hTermSelectFixedSub :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        termSel.termSelectFixed source J ≤ f (solverConnectedAugmented J).m

/-- Build `DryShiftSelectSizes` from `termSel : DryTermSelectSizes` and the concrete deep-shift
select sizes (`dryDeepSelectSpace`, `dryDeepSelectFixed Psc`). -/
def mkDryShiftSelectSizes (Psc : DrySparseCorePieces) (termSel : DryTermSelectSizes) :
    DryShiftSelectSizes where
  termSelectSpace := termSel.termSelectSpace
  deepSelectSpace := dryDeepSelectSpace
  deepSelectFixed := dryDeepSelectFixed Psc
  termSelectFixed := termSel.termSelectFixed

/-- Concrete `DryTermSelectSizes` from `WireTermSelectSizes.lean`. -/
def dryTermSelectSizes : DryTermSelectSizes where
  termSelectSpace := dryTermSelectSpace
  termSelectFixed := dryTermSelectFixed

/-- Complete concrete `DryShiftSelectSizes` combining `WireTermSelectSizes.lean` (term shift) and
`WireDeepSelectSizes.lean` (deep shift). -/
def dryShiftSelectSizes (Psc : DrySparseCorePieces) : DryShiftSelectSizes :=
  mkDryShiftSelectSizes Psc dryTermSelectSizes

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

private lemma selCoreLenEdgeSpace_le_quad {L a b : ℕ} (hLa : L ≤ a) (hab : a ≤ b) :
    selCoreLenEdgeSpace L a ≤ 20 * (b * b) + 40 * b + 10 := by
  unfold selCoreLenEdgeSpace wireCoreLenEdgeSpace Num.integerDivideSpace Num.unsignedDivideSpace
  rw [max_eq_right hLa]
  have hsq : a * a ≤ b * b := Nat.mul_le_mul hab hab
  nlinarith

private lemma evalKeySpace_le_poly_aux {d₁ d₂ e L₁ L₂ : ℕ} (hd : d₁ ≤ d₂) (hL : L₁ ≤ L₂) :
    evalKeySpace d₁ e L₁ ≤
      (d₂ + 1) * (3 * L₂) + e * ((d₂ + 1) * (3 * L₂) + 3 * L₂) + 4 * L₂ + 4 := by
  simp only [evalKeySpace, evalEdgePotGradSpace, evalKeyWalkLoopSpace, evalKeyStepSpace]
  have h1 := Nat.mul_le_mul (Nat.add_le_add_right hd 1) (Nat.mul_le_mul_left 3 hL)
  have h2 := Nat.mul_le_mul_left e (Nat.add_le_add h1 (Nat.mul_le_mul_left 3 hL))
  omega

private lemma drySelectHeapCap_le_deep (J : Circulation) :
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

private lemma dryNamedInstance_n_le_deep (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e) :
    (namedInstance (solverConnectedAugmented J)).n ≤ 2 * (solverConnectedAugmented J).m + 2 := by
  have hAug := solverConnectedAugmented_size J hJn hJm hCap
  have hN : (namedInstance (solverConnectedAugmented J)).n = (solverConnectedAugmented J).n :=
    Finset.card_range _
  have hAugN : (solverConnectedAugmented J).n ≤ 2 * (solverConnectedAugmented J).m + 2 := by
    change J.n + 1 ≤ 2 * (solverConnectedAugmented J).m + 2
    omega
  omega

private lemma dryInitTargetCap_le_deep (J : Circulation) :
    let I := solverConnectedAugmented J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    initTargetCap cfg (namedInstance I) ≤ 4 * dryM0OfM I.m := by
  dsimp only
  unfold initTargetCap
  have hNf := dryNfMax_le_two_mul_M0 J
  have hGm : (namedInstance (solverConnectedAugmented J)).m = (solverConnectedAugmented J).m :=
    namedInstance_m _
  have hMle : (solverConnectedAugmented J).m ≤ dryM0OfM (solverConnectedAugmented J).m :=
    le_max_left _ _
  dsimp only at hNf
  omega

/-- Uniform `PolyNat` bound on `dryDeepSelectSpace` (discharging
`DryShiftSelectSizeBounds.hDeepSelectSpacePoly`). -/
theorem dryDeepSelectSpace_le_poly :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        dryDeepSelectSpace source J ≤ f (solverConnectedAugmented J).m := by
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  obtain ⟨fLM, hfLMSub, hfLM⟩ := dryLevelM_le_subpoly
  have hfdP : PolyNat fd := SubpolyNat.toPolyNat hfdSub
  have hfLMP : PolyNat fLM := SubpolyNat.toPolyNat hfLMSub
  have hLP : PolyNat dryLimbsOfM := SubpolyNat.toPolyNat dryLimbsOfM_subpoly
  have hEmbP : PolyNat dryMaxEmbLen := SubpolyNat.toPolyNat progTool_embLen_le_subpoly.1
  have hM0P : PolyNat dryM0OfM := dryM0OfM_poly
  let fV : ℕ → ℕ := fun M => 2 * M + 2
  have hfVP : PolyNat fV := PolyNat.add_const (PolyNat.const_mul PolyNat.id 2) 2
  let fE : ℕ → ℕ := fun M => 4 * dryM0OfM M
  have hfEP : PolyNat fE := PolyNat.const_mul hM0P 4
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
  let f : ℕ → ℕ := fun M =>
    fd M * (7 + fE M * (fEdgeSp M + 4)) + 1 +
      fE M * (6 + fEdgeSp M) +
      (fd M + 1) * (1 + 2 * fV M + fV M * (4 * dryLimbsOfM M +
        (1 + 2 * dryLimbsOfM M + fd M * (4 * dryLimbsOfM M + 2)) + 2 * dryLimbsOfM M + 1)) +
      fE M * (fLogCap M * (16 * dryLimbsOfM M)) +
      (fd M + 1) * fE M * (2 * dryLimbsOfM M + fEvalSp M + fLogCap M * (16 * dryLimbsOfM M))
  have hfP : PolyNat f := by
    have h1 := PolyNat.add_const
      (PolyNat.mul hfdP (PolyNat.add (PolyNat.const 7) (PolyNat.mul hfEP (PolyNat.add_const hfEdgeSpP 4)))) 1
    have h2 := PolyNat.mul hfEP (PolyNat.add (PolyNat.const 6) hfEdgeSpP)
    have hPhiStep : PolyNat (fun M => 4 * dryLimbsOfM M +
        (1 + 2 * dryLimbsOfM M + fd M * (4 * dryLimbsOfM M + 2)) + 2 * dryLimbsOfM M + 1) :=
      PolyNat.add_const (PolyNat.add (PolyNat.add (PolyNat.const_mul hLP 4)
        (PolyNat.add (PolyNat.add (PolyNat.const 1) (PolyNat.const_mul hLP 2))
          (PolyNat.mul hfdP (PolyNat.add_const (PolyNat.const_mul hLP 4) 2))))
        (PolyNat.const_mul hLP 2)) 1
    have h3 := PolyNat.mul (PolyNat.add_const hfdP 1)
      (PolyNat.add (PolyNat.add (PolyNat.const 1) (PolyNat.const_mul hfVP 2))
        (PolyNat.mul hfVP hPhiStep))
    have h4 := PolyNat.mul hfEP (PolyNat.mul hfLogCapP (PolyNat.const_mul hLP 16))
    have h5 := PolyNat.mul (PolyNat.mul (PolyNat.add_const hfdP 1) hfEP)
      (PolyNat.add (PolyNat.add (PolyNat.const_mul hLP 2) hfEvalSpP)
        (PolyNat.mul hfLogCapP (PolyNat.const_mul hLP 16)))
    exact PolyNat.add (PolyNat.add (PolyNat.add (PolyNat.add h1 h2) h3) h4) h5
  refine ⟨f, hfP, fun _source J hJn hJm hCap => ?_⟩
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let G := namedInstance I
  have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hd : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
  have hVle : G.n ≤ fV I.m := dryNamedInstance_n_le_deep J hJn hJm hCap
  have hEle : initTargetCap cfg G ≤ fE I.m := dryInitTargetCap_le_deep J
  have hCapLe : selectHeapCap cfg G I.m ≤ 8 * dryM0OfM I.m := drySelectHeapCap_le_deep J
  have hM0 : levelM cfg.TP cfg.P 0 ≤ (I.m + 1) * fLM I.m := hfLM J hJn hJm hCap 0 (Nat.zero_le _)
  have hLw : ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀ ≤ fLw I.m := by
    unfold ordLevelLwMax; dsimp only [fLw, cLw]
    have hN0 : cfg.N₀ = 4 * dryM0OfM I.m := rfl
    exact Nat.add_le_add hL (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.log_mono_right (b := 2)
        (Nat.add_le_add_right (Nat.add_le_add hM0 (le_of_eq hN0)) 2)) 1))
  have hLleLw : L ≤ ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀ :=
    Nat.le_add_right _ _
  have hEdgeSp : selCoreLenEdgeSpace L (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀) ≤
      fEdgeSp I.m := selCoreLenEdgeSpace_le_quad hLleLw hLw
  have hEval : evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L ≤ fEvalSp I.m :=
    evalKeySpace_le_poly_aux hd hL
  have hlg : 2 * Nat.log 2 (selectHeapCap cfg G I.m + 1) + 1 ≤ fLogCap I.m := by
    dsimp only [fLogCap]
    have h1 : selectHeapCap cfg G I.m + 1 ≤ 8 * dryM0OfM I.m + 2 :=
      Nat.add_le_add hCapLe (Nat.le_succ 1)
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.log_mono_right (b := 2) h1)) 1
  have hReb : heapRebalanceSpace (selectHeapCap cfg G I.m) L ≤ fLogCap I.m * (16 * dryLimbsOfM I.m) := by
    unfold heapRebalanceSpace keyCompareSpace
    exact Nat.mul_le_mul hlg (Nat.mul_le_mul_left 16 hL)
  have hT1 : cfg.P.d * (7 + initTargetCap cfg G *
      (selCoreLenEdgeSpace L (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀) + 4)) ≤
      fd I.m * (7 + fE I.m * (fEdgeSp I.m + 4)) :=
    Nat.mul_le_mul hd (Nat.add_le_add_left (Nat.mul_le_mul hEle (Nat.add_le_add_right hEdgeSp 4)) 7)
  have hT2 : initTargetCap cfg G *
      (6 + selCoreLenEdgeSpace L (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀)) ≤
      fE I.m * (6 + fEdgeSp I.m) :=
    Nat.mul_le_mul hEle (Nat.add_le_add_left hEdgeSp 6)
  have hT3 : (cfg.P.d + 1) * selectPhiFillSpace cfg.P.d G.n L ≤
      (fd I.m + 1) * (1 + 2 * fV I.m + fV I.m * (4 * dryLimbsOfM I.m +
        (1 + 2 * dryLimbsOfM I.m + fd I.m * (4 * dryLimbsOfM I.m + 2)) + 2 * dryLimbsOfM I.m + 1)) := by
    unfold selectPhiFillSpace phiFillEdgeStepSpace
    have hmul1 : (3 * cfg.P.d + 3) * L ≤ 4 * dryLimbsOfM I.m +
        (1 + 2 * dryLimbsOfM I.m + fd I.m * (4 * dryLimbsOfM I.m + 2)) + 2 * dryLimbsOfM I.m + 1 := by
      have h1 := Nat.mul_le_mul hd hL
      have h2 := Nat.mul_le_mul_left 3 h1
      have h3 := Nat.mul_le_mul_left 3 hL
      nlinarith only [h2, h3]
    have hmul2 := Nat.mul_le_mul hVle hmul1
    exact Nat.mul_le_mul (Nat.add_le_add_right hd 1)
      (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hVle) 1) hmul2)
  have hT4 : initTargetCap cfg G * heapRebalanceSpace (selectHeapCap cfg G I.m) L ≤
      fE I.m * (fLogCap I.m * (16 * dryLimbsOfM I.m)) :=
    Nat.mul_le_mul hEle hReb
  have hT5 : (cfg.P.d + 1) * initTargetCap cfg G *
      selectProcessEdgeSpace (selectHeapCap cfg G I.m) L (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L) ≤
      (fd I.m + 1) * fE I.m * (2 * dryLimbsOfM I.m + fEvalSp I.m + fLogCap I.m * (16 * dryLimbsOfM I.m)) := by
    unfold selectProcessEdgeSpace
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.add_le_add_right hd 1) hEle)
      (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 hL) hEval) hReb)
  unfold dryDeepSelectSpace shiftDeepSelectSpaceBound
  dsimp only [f]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add_right hT1 1) hT2) hT3) hT4) hT5

/-- Uniform `SubpolyNat` bound on `dryDeepSelectFixed Psc` (discharging
`DryShiftSelectSizeBounds.hDeepSelectFixedSub`). -/
theorem dryDeepSelectFixed_le_subpoly (Psc : DrySparseCorePieces) :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        dryDeepSelectFixed Psc source J ≤ f (solverConnectedAugmented J).m := by
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  have hLSub : SubpolyNat dryLimbsOfM := dryLimbsOfM_subpoly
  let rc : ℕ := (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).readout
  let f : ℕ → ℕ := fun M =>
    (2 * fd M + 1) * rc + (fd M + 1) * (1800 * (fd M + 1) * (dryLimbsOfM M + 1) + 1700) + 2800
  have hfSub : SubpolyNat f :=
    SubpolyNat.add_const (SubpolyNat.add
      (SubpolyNat.mul (SubpolyNat.add_const (SubpolyNat.const_mul hfdSub 2) 1) (SubpolyNat.const rc))
      (SubpolyNat.mul (SubpolyNat.add_const hfdSub 1)
        (SubpolyNat.add_const (SubpolyNat.mul
          (SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) 1800)
          (SubpolyNat.add_const hLSub 1)) 1700))) 2800
  refine ⟨f, hfSub, fun _source J hJn hJm hCap => ?_⟩
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hd : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
  have h1 : (2 * cfg.P.d + 1) * rc ≤ (2 * fd I.m + 1) * rc :=
    Nat.mul_le_mul_right rc (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hd) 1)
  have h2 : 1800 * (cfg.P.d + 1) * (L + 1) ≤ 1800 * (fd I.m + 1) * (dryLimbsOfM I.m + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 1800 (Nat.add_le_add_right hd 1)) (Nat.add_le_add_right hL 1)
  have h3 : (cfg.P.d + 1) * (1800 * (cfg.P.d + 1) * (L + 1) + 1700) ≤
      (fd I.m + 1) * (1800 * (fd I.m + 1) * (dryLimbsOfM I.m + 1) + 1700) :=
    Nat.mul_le_mul (Nat.add_le_add_right hd 1) (Nat.add_le_add_right h2 1700)
  exact Nat.add_le_add_right (Nat.add_le_add h1 h3) 2800

/-- The combined deep-shift + select-refresh per-tool-cost multiplier fits inside `dryToolMul`
with zero changes to `dryToolMul`, `dryKeyCost`, or `drySelectToolMulExtra`. -/
theorem dryDeepSelectToolMul_le (Psc : DrySparseCorePieces)
    (initSel : DryInitSelectSizes) (shiftSel : DryShiftSelectSizes) (source J : Circulation) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
    let selSz := mkDrySelectRebuildSizes initSel shiftSel
    deepShiftToolMulBound L dryCapExp PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d (dryLastMult J) +
      shiftDeepSelectToolMulBound cfg.P.d L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀
        (drySlot I.m) (dryKeyCost source J) ≤
      dryToolMul Psc selSz source J := by
  intro I V k L cfg PscP selSz
  dsimp only [selSz]
  unfold dryToolMul mkDrySelectRebuildSizes dryCReemb drySelectToolMulExtra
    shiftDeepSelectToolMulBound
  dsimp only
  have hKge : 740 ≤ dryKeyCost source J := by
    unfold dryKeyCost selectProcessEdgeCost heapUpsertCost
    dsimp only
    omega
  have hMulK : dryKeyCost source J * (1 + 2) + (cfg.P.d + 3) * dryKeyCost source J =
      4 * dryKeyCost source J + (cfg.P.d + 2) * dryKeyCost source J := by ring
  have hKslack : 2 * 740 ≤ (cfg.P.d + 2) * dryKeyCost source J := by
    have h1 : 2 ≤ cfg.P.d + 2 := by omega
    exact Nat.mul_le_mul h1 hKge
  have hMax : deepShiftToolMulBound L dryCapExp PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d
      (dryLastMult J) ≤
      max (deepShiftToolMulBound L dryCapExp PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d
        (dryLastMult J)) PscP.mul := le_max_left _ _
  linarith

/-- Lift `DryTermSelectSizeBounds` to `DryShiftSelectSizeBounds` using `dryDeepSelectSpace_le_poly`
and `dryDeepSelectFixed_le_subpoly`. -/
theorem mkDryShiftSelectSizeBounds (Psc : DrySparseCorePieces) {termSel : DryTermSelectSizes}
    (hTerm : DryTermSelectSizeBounds termSel) :
    DryShiftSelectSizeBounds (mkDryShiftSelectSizes Psc termSel) where
  hTermSelectSpacePoly := hTerm.hTermSelectSpacePoly
  hDeepSelectSpacePoly := dryDeepSelectSpace_le_poly
  hDeepSelectFixedSub := dryDeepSelectFixed_le_subpoly Psc
  hTermSelectFixedSub := hTerm.hTermSelectFixedSub

/-- `DryTermSelectSizeBounds` for `dryTermSelectSizes`. -/
theorem dryTermSelectSizeBounds : DryTermSelectSizeBounds dryTermSelectSizes where
  hTermSelectSpacePoly := dryTermSelectSpace_le_poly
  hTermSelectFixedSub := dryTermSelectFixed_le_subpoly

/-- Complete concrete `DryShiftSelectSizeBounds` for `dryShiftSelectSizes Psc`, discharging all
four `PolyNat` / `SubpolyNat` clauses of `DryShiftSelectSizeBounds`. -/
theorem dryShiftSelectSizeBounds (Psc : DrySparseCorePieces) :
    DryShiftSelectSizeBounds (dryShiftSelectSizes Psc) :=
  mkDryShiftSelectSizeBounds Psc dryTermSelectSizeBounds

end MinCostFlow.Final.DryRun

end
