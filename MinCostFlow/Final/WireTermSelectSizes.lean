module

public import MinCostFlow.Final.WireSelectSizes
public import MinCostFlow.MinRatio.WireShiftTermSelect
import Mathlib.Tactic

/-!
# Concrete terminal-shift select space and fixed cost bounds (`WireTermSelectSizes`)

Defines `dryTermSelectSpace` and `dryTermSelectFixed` matching `termSelectSpace` and
`termSelectFixed` (`MinRatio/WireShiftTermSelect.lean`) at the dry-run parameters
`(nD = levelM cfg.TP cfg.P cfg.P.d + 1, mD = levelM cfg.TP cfg.P cfg.P.d,
cap = selectHeapCap cfg (namedInstance I) I.m)`, and proves:

1. `termSelectSpace_le_dryTermSelectSpace` and `termSelectFixed_le_dryTermSelectFixed`: dominance
   over `termSelectSpace` and `termSelectFixed` for any `nD ≤ levelM d + 1` and `mD ≤ levelM d`.
2. `dryTermSelectSpace_le_subpoly` and `dryTermSelectSpace_le_poly`: uniform `SubpolyNat` (and
   hence `PolyNat`) bound on `dryTermSelectSpace` matching `DryShiftSelectSizeBounds.hTermSelectSpacePoly`.
3. `dryTermSelectFixed_le_subpoly`: uniform `SubpolyNat` bound on `dryTermSelectFixed` matching
   `DryShiftSelectSizeBounds.hTermSelectFixedSub`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Concrete `termSelectSpace` and `termSelectFixed` -/

/-- Concrete `termSelectSpace` matching `shiftTermSelectBody_runs` (`WireShiftTermSelect.lean`) at
`nD = levelM cfg.TP cfg.P cfg.P.d + 1`, `mD = levelM cfg.TP cfg.P cfg.P.d`,
`cap = selectHeapCap cfg (namedInstance I) I.m`, and
`evalSpace = evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L`. -/
def dryTermSelectSpace (_source J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let G := namedInstance I
  let d := cfg.P.d
  let mD := levelM cfg.TP cfg.P d
  let cap := selectHeapCap cfg G I.m
  termSelectSpace d (mD + 1) mD cap L (evalKeySpace d (dryMaxEmbLen I.m) L)

/-- Concrete `termSelectFixed` matching `shiftTermSelectBody_runs` (`WireShiftTermSelect.lean`) at
`nD = levelM cfg.TP cfg.P cfg.P.d + 1`, `mD = levelM cfg.TP cfg.P cfg.P.d`,
`cap = selectHeapCap cfg (namedInstance I) I.m`, and
`evalCost = evalKeyCost cfg.P.d (dryMaxEmbLen I.m) L`. -/
def dryTermSelectFixed (_source J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let G := namedInstance I
  let d := cfg.P.d
  let mD := levelM cfg.TP cfg.P d
  let cap := selectHeapCap cfg G I.m
  termSelectFixed d (mD + 1) mD cap L (evalKeyCost d (dryMaxEmbLen I.m) L)

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 2. Dominance over `termSelectSpace` and `termSelectFixed` -/

/-- `dryTermSelectSpace` dominates `termSelectSpace` for any `nD ≤ levelM d + 1` and
`mD ≤ levelM d`. -/
theorem termSelectSpace_le_dryTermSelectSpace (source J : Circulation) {nD mD : ℕ}
    (hn : nD ≤ levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
      (concreteCirculationCfgWithLast dryWitnessUsed J).P
      (concreteCirculationCfgWithLast dryWitnessUsed J).P.d + 1)
    (hm : mD ≤ levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
      (concreteCirculationCfgWithLast dryWitnessUsed J).P
      (concreteCirculationCfgWithLast dryWitnessUsed J).P.d) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let cap := selectHeapCap cfg (namedInstance I) I.m
    termSelectSpace cfg.P.d nD mD cap L (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L) ≤
      dryTermSelectSpace source J := by
  dsimp only [dryTermSelectSpace, termSelectSpace]
  exact Nat.add_le_add (levelDBlocksSpace_mono hn hm hm) (selectRebuildLevelSpace_mono hm hm)

/-- `dryTermSelectFixed` dominates `termSelectFixed` for any `nD ≤ levelM d + 1` and
`mD ≤ levelM d`. -/
theorem termSelectFixed_le_dryTermSelectFixed (source J : Circulation) {nD mD : ℕ}
    (hn : nD ≤ levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
      (concreteCirculationCfgWithLast dryWitnessUsed J).P
      (concreteCirculationCfgWithLast dryWitnessUsed J).P.d + 1)
    (hm : mD ≤ levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
      (concreteCirculationCfgWithLast dryWitnessUsed J).P
      (concreteCirculationCfgWithLast dryWitnessUsed J).P.d) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let cap := selectHeapCap cfg (namedInstance I) I.m
    termSelectFixed cfg.P.d nD mD cap L (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) L) ≤
      dryTermSelectFixed source J := by
  dsimp only [dryTermSelectFixed, termSelectFixed]
  exact Nat.add_le_add_right
    (Nat.add_le_add (levelDBlocksCost_mono hn hm hn hm hm) (selectRebuildLevelCost_mono hm hm)) 120

/-! ## 3. Asymptotic `SubpolyNat` / `PolyNat` bounds -/

private theorem drySelectHeapCap_le_term (J : Circulation) :
    let I := solverConnectedAugmented J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    selectHeapCap cfg (namedInstance I) I.m ≤ 8 * dryM0OfM I.m := by
  dsimp only
  unfold selectHeapCap
  have hNf := dryNfMax_le_two_mul_M0 J
  have hMle : (solverConnectedAugmented J).m ≤ dryM0OfM (solverConnectedAugmented J).m := le_max_left _ _
  dsimp only at hNf
  omega

/-- Uniform `SubpolyNat` bound on `dryTermSelectSpace`. -/
theorem dryTermSelectSpace_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        dryTermSelectSpace source J ≤ f (solverConnectedAugmented J).m := by
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  have hMdSub : SubpolyNat (fun M => 2 ^ dryKOfM M) := subpolyNat_two_pow_dryKOfM
  have hLSub : SubpolyNat dryLimbsOfM := dryLimbsOfM_subpoly
  have hEmbSub : SubpolyNat dryMaxEmbLen := progTool_embLen_le_subpoly.1
  let fMd : ℕ → ℕ := fun M => 2 ^ dryKOfM M
  let fLogCap : ℕ → ℕ := fun M => 2 * (Nat.log 2 (8 * dryM0OfM M + 2) + 1) + 1
  have hfLogCapSub : SubpolyNat fLogCap :=
    SubpolyNat.add_const (SubpolyNat.const_mul
      (subpolyNat_log_of_poly (PolyNat.const_mul dryM0OfM_poly 8)) 2) 1
  let fEdgeSp : ℕ → ℕ := fun M => 25 * (dryLimbsOfM M) ^ 2 + 25 * dryLimbsOfM M + 10
  have hfEdgeSpSub : SubpolyNat fEdgeSp :=
    SubpolyNat.add_const (SubpolyNat.add
      (SubpolyNat.const_mul (SubpolyNat.pow hLSub 2) 25)
      (SubpolyNat.const_mul hLSub 25)) 10
  let fEvalSp : ℕ → ℕ := fun M =>
    4 * dryLimbsOfM M + (fd M + 1) * (3 * dryLimbsOfM M) +
      dryMaxEmbLen M * ((fd M + 1) * (3 * dryLimbsOfM M) + 3 * dryLimbsOfM M)
  have hfEvalSpSub : SubpolyNat fEvalSp := by
    have hpg := SubpolyNat.mul (SubpolyNat.add_const hfdSub 1) (SubpolyNat.const_mul hLSub 3)
    exact SubpolyNat.add (SubpolyNat.add (SubpolyNat.const_mul hLSub 4) hpg)
      (SubpolyNat.mul hEmbSub (SubpolyNat.add hpg (SubpolyNat.const_mul hLSub 3)))
  let f : ℕ → ℕ := fun M =>
    (3 * fMd M + (1 + 2 * (fMd M + 1) + (fMd M + 1) * ((3 * fd M + 3) * dryLimbsOfM M)) +
      fMd M * fEdgeSp M) +
    (fMd M * (fLogCap M * (16 * dryLimbsOfM M)) +
      fMd M * (2 * dryLimbsOfM M + fEvalSp M + fLogCap M * (16 * dryLimbsOfM M)))
  have hfSub : SubpolyNat f := by
    have h1 := SubpolyNat.add (SubpolyNat.add (SubpolyNat.const_mul hMdSub 3)
      (SubpolyNat.add (SubpolyNat.add (SubpolyNat.const 1)
        (SubpolyNat.const_mul (SubpolyNat.add_const hMdSub 1) 2))
        (SubpolyNat.mul (SubpolyNat.add_const hMdSub 1)
          (SubpolyNat.mul (SubpolyNat.add_const (SubpolyNat.const_mul hfdSub 3) 3) hLSub))))
      (SubpolyNat.mul hMdSub hfEdgeSpSub)
    have h2 := SubpolyNat.add
      (SubpolyNat.mul hMdSub (SubpolyNat.mul hfLogCapSub (SubpolyNat.const_mul hLSub 16)))
      (SubpolyNat.mul hMdSub (SubpolyNat.add (SubpolyNat.add (SubpolyNat.const_mul hLSub 2) hfEvalSpSub)
        (SubpolyNat.mul hfLogCapSub (SubpolyNat.const_mul hLSub 16))))
    exact SubpolyNat.add h1 h2
  refine ⟨f, hfSub, fun _source J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  set G := namedInstance I
  set d := cfg.P.d
  set mD := levelM cfg.TP cfg.P d
  set cap := selectHeapCap cfg G I.m
  have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hd : d ≤ fd I.m := hfd J hJn hJm hCap
  have hmD : mD ≤ fMd I.m := dryLevelMd_le_two_pow_dryKOfM J hJn hJm hCap
  have hCapLe : cap ≤ 8 * dryM0OfM I.m := drySelectHeapCap_le_term J
  have hLogLe : 2 * Nat.log 2 (cap + 1) + 1 ≤ fLogCap I.m := by
    dsimp only [fLogCap]
    have hlg := Nat.log_mono_right (b := 2) (show cap + 1 ≤ 8 * dryM0OfM I.m + 2 by omega)
    omega
  have hEdgeLe : selCoreLenEdgeSpace L L ≤ fEdgeSp I.m := by
    unfold selCoreLenEdgeSpace wireCoreLenEdgeSpace Num.integerDivideSpace Num.unsignedDivideSpace
    have hmx : max L L = L := max_self L
    rw [hmx]
    have hsq : L ^ 2 ≤ (dryLimbsOfM I.m) ^ 2 := Nat.pow_le_pow_left hL 2
    dsimp only [fEdgeSp]
    nlinarith only [hL, hsq]
  have hEvalLe : evalKeySpace d (dryMaxEmbLen I.m) L ≤ fEvalSp I.m := by
    simp only [evalKeySpace, evalEdgePotGradSpace, evalKeyWalkLoopSpace, evalKeyStepSpace]
    dsimp only [fEvalSp]
    have h1 := Nat.mul_le_mul (show d + 1 ≤ fd I.m + 1 by omega)
      (show 3 * L ≤ 3 * dryLimbsOfM I.m by omega)
    have h2 := Nat.mul_le_mul_left (dryMaxEmbLen I.m)
      (show (d + 1) * (3 * L) + 3 * L ≤ (fd I.m + 1) * (3 * dryLimbsOfM I.m) + 3 * dryLimbsOfM I.m by omega)
    omega
  have hBlocks : levelDBlocksSpace d (mD + 1) mD mD L ≤
      3 * fMd I.m + (1 + 2 * (fMd I.m + 1) + (fMd I.m + 1) * ((3 * fd I.m + 3) * dryLimbsOfM I.m)) +
        fMd I.m * fEdgeSp I.m := by
    unfold levelDBlocksSpace selectPhiFillSpace phiFillEdgeStepSpace
    have h1 := Nat.mul_le_mul (show mD + 1 ≤ fMd I.m + 1 by omega)
      (Nat.mul_le_mul (show 3 * d + 3 ≤ 3 * fd I.m + 3 by omega) hL)
    have h2 := Nat.mul_le_mul hmD hEdgeLe
    omega
  have hRebal : heapRebalanceSpace cap L ≤ fLogCap I.m * (16 * dryLimbsOfM I.m) := by
    unfold heapRebalanceSpace keyCompareSpace
    exact Nat.mul_le_mul hLogLe (by omega)
  have hReb : selectRebuildLevelSpace mD mD cap L (evalKeySpace d (dryMaxEmbLen I.m) L) ≤
      fMd I.m * (fLogCap I.m * (16 * dryLimbsOfM I.m)) +
        fMd I.m * (2 * dryLimbsOfM I.m + fEvalSp I.m + fLogCap I.m * (16 * dryLimbsOfM I.m)) := by
    unfold selectRebuildLevelSpace heapClearLevelSpace selectProcessListSpace selectProcessEdgeSpace
    have h1 := Nat.mul_le_mul hmD hRebal
    have h2 := Nat.mul_le_mul hmD (show 2 * L + evalKeySpace d (dryMaxEmbLen I.m) L +
      heapRebalanceSpace cap L ≤ 2 * dryLimbsOfM I.m + fEvalSp I.m +
        fLogCap I.m * (16 * dryLimbsOfM I.m) by omega)
    omega
  change termSelectSpace d (mD + 1) mD cap L (evalKeySpace d (dryMaxEmbLen I.m) L) ≤ f I.m
  unfold termSelectSpace
  dsimp only [f]
  omega

/-- Uniform `PolyNat` bound on `dryTermSelectSpace` (matches `DryShiftSelectSizeBounds.hTermSelectSpacePoly`). -/
theorem dryTermSelectSpace_le_poly :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        dryTermSelectSpace source J ≤ f (solverConnectedAugmented J).m := by
  obtain ⟨f, hfSub, hf⟩ := dryTermSelectSpace_le_subpoly
  exact ⟨f, SubpolyNat.toPolyNat hfSub, hf⟩

/-- Uniform `SubpolyNat` bound on `dryTermSelectFixed` (matches `DryShiftSelectSizeBounds.hTermSelectFixedSub`). -/
theorem dryTermSelectFixed_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        dryTermSelectFixed source J ≤ f (solverConnectedAugmented J).m := by
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  obtain ⟨fKey, hfKeySub, hKey⟩ := dryKeyCost_le_subpoly
  have hMdSub : SubpolyNat (fun M => 2 ^ dryKOfM M) := subpolyNat_two_pow_dryKOfM
  have hLSub : SubpolyNat dryLimbsOfM := dryLimbsOfM_subpoly
  let fMd : ℕ → ℕ := fun M => 2 ^ dryKOfM M
  let fLogCap : ℕ → ℕ := fun M => (Nat.log 2 (8 * dryM0OfM M + 2) + 1) + 1
  have hfLogCapSub : SubpolyNat fLogCap :=
    SubpolyNat.add_const (subpolyNat_log_of_poly (PolyNat.const_mul dryM0OfM_poly 8)) 1
  let fKC : ℕ → ℕ := fun M => 304 * (dryLimbsOfM M) ^ 2 + 720 * dryLimbsOfM M + 400
  have hfKCSub : SubpolyNat fKC :=
    SubpolyNat.add_const (SubpolyNat.add
      (SubpolyNat.const_mul (SubpolyNat.pow hLSub 2) 304)
      (SubpolyNat.const_mul hLSub 720)) 400
  let fDel : ℕ → ℕ := fun M => fLogCap M * (2 * fKC M + 240) + fKC M + 460
  have hfDelSub : SubpolyNat fDel :=
    SubpolyNat.add_const (SubpolyNat.add
      (SubpolyNat.mul hfLogCapSub (SubpolyNat.add_const (SubpolyNat.const_mul hfKCSub 2) 240))
      hfKCSub) 460
  let fCL : ℕ → ℕ := fun M => 35 * dryLimbsOfM M + (1400 * (dryLimbsOfM M) ^ 2 + 2100 * dryLimbsOfM M + 850) + 160
  have hfCLSub : SubpolyNat fCL :=
    SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.const_mul hLSub 35)
      (SubpolyNat.add_const (SubpolyNat.add
        (SubpolyNat.const_mul (SubpolyNat.pow hLSub 2) 1400)
        (SubpolyNat.const_mul hLSub 2100)) 850)) 160
  let f : ℕ → ℕ := fun M =>
    (1200 * (fMd M + 1) + 1200 * fMd M + 1200) +
    ((fMd M + 1) * (fd M * (130 * dryLimbsOfM M + 240) + 125 * dryLimbsOfM M + 900) + 200) +
    fMd M * fCL M + 320 +
    (fMd M * fDel M + fMd M * fKey M + 180) + 120
  have hfSub : SubpolyNat f := by
    have h1 := SubpolyNat.add_const (SubpolyNat.add
      (SubpolyNat.const_mul (SubpolyNat.add_const hMdSub 1) 1200)
      (SubpolyNat.const_mul hMdSub 1200)) 1200
    have h2 := SubpolyNat.add_const (SubpolyNat.mul (SubpolyNat.add_const hMdSub 1)
      (SubpolyNat.add_const (SubpolyNat.add
        (SubpolyNat.mul hfdSub (SubpolyNat.add_const (SubpolyNat.const_mul hLSub 130) 240))
        (SubpolyNat.const_mul hLSub 125)) 900)) 200
    have h3 := SubpolyNat.add_const (SubpolyNat.mul hMdSub hfCLSub) 320
    have h4 := SubpolyNat.add_const (SubpolyNat.add_const (SubpolyNat.add
      (SubpolyNat.mul hMdSub hfDelSub) (SubpolyNat.mul hMdSub hfKeySub)) 180) 120
    exact SubpolyNat.mono (fun M => by dsimp only [f, fMd]; omega)
      (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add h1 h2) h3) h4)
  refine ⟨f, hfSub, fun source J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  set G := namedInstance I
  set d := cfg.P.d
  set mD := levelM cfg.TP cfg.P d
  set cap := selectHeapCap cfg G I.m
  have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hd : d ≤ fd I.m := hfd J hJn hJm hCap
  have hmD : mD ≤ fMd I.m := dryLevelMd_le_two_pow_dryKOfM J hJn hJm hCap
  have hCapLe : cap ≤ 8 * dryM0OfM I.m := drySelectHeapCap_le_term J
  have hLogLe : Nat.log 2 (cap + 1) + 1 ≤ fLogCap I.m := by
    dsimp only [fLogCap]
    have hlg := Nat.log_mono_right (b := 2) (show cap + 1 ≤ 8 * dryM0OfM I.m + 2 by omega)
    omega
  have hKCLe : keyCompareCost L ≤ fKC I.m := by
    unfold keyCompareCost
    dsimp only [fKC]
    have hsq : L ^ 2 ≤ (dryLimbsOfM I.m) ^ 2 := Nat.pow_le_pow_left hL 2
    omega
  have hDelLe : heapDeleteCost cap L + 60 ≤ fDel I.m := by
    unfold heapDeleteCost heapRebalanceCost
    dsimp only [fDel]
    have h1 := Nat.mul_le_mul hLogLe (show 2 * keyCompareCost L + 240 ≤ 2 * fKC I.m + 240 by omega)
    omega
  have hKeyLe : selectProcessEdgeCost cap L (evalKeyCost d (dryMaxEmbLen I.m) L) + 40 ≤ fKey I.m :=
    (dryKeyCost_covers source J).1.trans (hKey source J hJn hJm hCap)
  have hCLLe : selCoreLenEdgeCost L L + 40 ≤ fCL I.m := by
    unfold selCoreLenEdgeCost wireCoreLenEdgeCost
    have hmx : max L L = L := max_self L
    rw [hmx]
    have hsq : L ^ 2 ≤ (dryLimbsOfM I.m) ^ 2 := Nat.pow_le_pow_left hL 2
    dsimp only [fCL]
    nlinarith only [hL, hsq]
  have hDG : dgRefillFromDynGraphCost (mD + 1) mD (mD + 1) mD ≤
      1200 * (fMd I.m + 1) + 1200 * fMd I.m + 1200 := by
    unfold dgRefillFromDynGraphCost dgRefillFromListsCost dgPackEdgeTriplesCost
    omega
  have hPhi : selectPhiFillCost d (mD + 1) L ≤
      (fMd I.m + 1) * (fd I.m * (130 * dryLimbsOfM I.m + 240) + 125 * dryLimbsOfM I.m + 900) + 200 := by
    unfold selectPhiFillCost
    have h1 := Nat.mul_le_mul hd (show 130 * L + 240 ≤ 130 * dryLimbsOfM I.m + 240 by linarith only [hL])
    have h2 := Nat.mul_le_mul (Nat.add_le_add_right hmD 1)
      (show d * (130 * L + 240) + 125 * L + 900 ≤
        fd I.m * (130 * dryLimbsOfM I.m + 240) + 125 * dryLimbsOfM I.m + 900 by linarith only [h1, hL])
    exact Nat.add_le_add_right h2 200
  have hCoreLen : mD * (selCoreLenEdgeCost L L + 40) ≤ fMd I.m * fCL I.m :=
    Nat.mul_le_mul hmD hCLLe
  have hReb : selectRebuildLevelCost mD mD cap L (evalKeyCost d (dryMaxEmbLen I.m) L) ≤
      fMd I.m * fDel I.m + fMd I.m * fKey I.m + 180 := by
    unfold selectRebuildLevelCost heapClearLevelCost selectProcessListCost
    have h1 := Nat.mul_le_mul hmD hDelLe
    have h2 := Nat.mul_le_mul hmD hKeyLe
    omega
  change levelDBlocksCost d (mD + 1) mD (mD + 1) mD mD L +
    selectRebuildLevelCost mD mD cap L (evalKeyCost d (dryMaxEmbLen I.m) L) + 120 ≤ f I.m
  unfold levelDBlocksCost
  dsimp only [f]
  linarith only [hDG, hPhi, hCoreLen, hReb]

end MinCostFlow.Final.DryRun

end
