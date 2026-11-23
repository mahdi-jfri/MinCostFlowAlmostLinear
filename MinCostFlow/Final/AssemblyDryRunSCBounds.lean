module

public import MinCostFlow.Final.AssemblyDryRunSCDeepAsymp
import Mathlib.Tactic

/-!
# Concrete `B : OrdSolverInnerBounds`, `InnerBoundsHyp B`, `DryEnvelopeIneqs`, and `hNames`

Constructs the concrete solver inner-bound bundle `dryInnerBounds : OrdSolverInnerBounds` from
`dryInnerSizesWithSelect Psc openSz selSz` (using `deepShiftFixedBound`, `deepShiftToolMulBound`,
`2 * levelM cfg.TP cfg.P cfg.P.d`, `initWiredExtraSpace`, and `initWiredExtraCost`), and proves:

* `dryInnerBounds_hyp`: all eight clauses of `InnerBoundsHyp dryInnerBounds`.
* `dryInnerBounds_envelopeIneqs`: all seven clauses of `DryEnvelopeIneqs`
  (`Final/AssemblyDryRunSCEnvelope.lean`), directly matching `initWiredExtraSpace`,
  `initWiredExtraCost`, and no-growth `Update` rate.
* `dryInnerBounds_hNames`: `Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 +
  2 * I.m ≤ B.names I.m`.
* `dryInnerBounds_hEnv_proved`: discharges `OrdSolverContractEnvelopeFullCredit` unconditionally
  via `drySC_hEnv_of_ineqs`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Uniform `SubpolyNat` and `PolyNat` bounds for the four envelope clauses -/

/-- `SubpolyNat` bound on the cycle-loop iteration budget `B_iter`. -/
theorem dryBIter_le_subpoly (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (hOpen : DryOpenSizeBounds openSz) (selSz : DrySelectRebuildSizes)
    (hSel : DrySelectRebuildSizeBounds selSz) :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let L := ipmQualityLimbs I.m V k
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let s := dryInnerSizesWithSelect Psc openSz selSz source J
        cycleLoopIterBudget L cfg.P.d (s.selectBudget + s.evalBudget + 90)
          (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220) ≤ f I.m := by
  obtain ⟨fSelBud, fME, fMP, _, _, hfSelSub, hfMESub, hfMPSub, _, _, hRate⟩ := hOpen.hRateSubpoly
  obtain ⟨fDeepFix, hfDeepFixSub, hDeepFix⟩ := deepShiftFixedBound_le_subpoly Psc
  obtain ⟨fDSel, hfDSelSub, hDSel⟩ := hSel.hDeepSelectFixedSub
  obtain ⟨fTSel, hfTSelSub, hTSel⟩ := hSel.hTermSelectFixedSub
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  let fL := dryLimbsOfM
  have hfL := dryLimbsOfM_subpoly
  let fEval : ℕ → ℕ := fun M =>
    fMP M * (25 * (LinkCut.PathProg.pathC * (fL M + 1) ^ 2) * (4 * fL M + 1) + 76 * fL M + 170) +
      fME M * (112 * fL M + 180) + 44 * fL M + 120
  have hfEvalSub : SubpolyNat fEval := by
    have hL1sq : SubpolyNat (fun M => (fL M + 1) ^ 2) :=
      SubpolyNat.pow (SubpolyNat.add_const hfL 1) 2
    have hP1 : SubpolyNat (fun M =>
        25 * (LinkCut.PathProg.pathC * (fL M + 1) ^ 2) * (4 * fL M + 1) + 76 * fL M + 170) :=
      SubpolyNat.add_const (SubpolyNat.add
        (SubpolyNat.mul (SubpolyNat.const_mul (SubpolyNat.const_mul hL1sq LinkCut.PathProg.pathC) 25)
          (SubpolyNat.add_const (SubpolyNat.const_mul hfL 4) 1))
        (SubpolyNat.const_mul hfL 76)) 170
    have hP2 : SubpolyNat (fun M => 112 * fL M + 180) :=
      SubpolyNat.add_const (SubpolyNat.const_mul hfL 112) 180
    exact SubpolyNat.add_const (SubpolyNat.add
      (SubpolyNat.add (SubpolyNat.mul hfMPSub hP1) (SubpolyNat.mul hfMESub hP2))
      (SubpolyNat.const_mul hfL 44)) 120
  let fShiftF : ℕ → ℕ := fun M => (82 * 2 ^ dryKOfM M + 320 + fTSel M) + (fDeepFix M + fDSel M)
  have hfShiftFSub : SubpolyNat fShiftF :=
    SubpolyNat.add
      (SubpolyNat.add (SubpolyNat.add_const (SubpolyNat.const_mul subpolyNat_two_pow_dryKOfM 82) 320) hfTSelSub)
      (SubpolyNat.add hfDeepFixSub hfDSelSub)
  let fTot : ℕ → ℕ := fun M =>
    (fSelBud M + fEval M + 90) + 181 * fL M + 20 * (fd M + 1) +
      (fShiftF M + 28 * (fd M + 1) + 220) + 420
  have hfTotSub : SubpolyNat fTot := by
    have h1 := SubpolyNat.add_const (SubpolyNat.add hfSelSub hfEvalSub) 90
    have h2 := SubpolyNat.const_mul hfL 181
    have h3 := SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) 20
    have h4 := SubpolyNat.add_const (SubpolyNat.add hfShiftFSub
      (SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) 28)) 220
    exact SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add h1 h2) h3) h4) 420
  refine ⟨fTot, hfTotSub, fun source J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hL : L ≤ fL I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hd : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
  obtain ⟨hSel', hME, hMP, _⟩ := hRate source J hJn hJm hCap
  have hMd := dryLevelMd_le_two_pow_dryKOfM J hJn hJm hCap
  have hTF := hTSel source J hJn hJm hCap
  have hDF := hDeepFix J hJn hJm hCap
  have hDS := hDSel source J hJn hJm hCap
  have hEvalLe : evalCycleBudget L (openSz.maxEdges source J) (openSz.maxPaths source J) ≤
      fEval I.m := by
    unfold evalCycleBudget
    dsimp only [fEval]
    have hsq : (L + 1) ^ 2 ≤ (fL I.m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hmulA : 25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) ≤
        25 * (LinkCut.PathProg.pathC * (fL I.m + 1) ^ 2) * (4 * fL I.m + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 25 (Nat.mul_le_mul_left LinkCut.PathProg.pathC hsq)) (by omega)
    have h1 := Nat.mul_le_mul hMP (show 25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) +
        76 * L + 170 ≤ 25 * (LinkCut.PathProg.pathC * (fL I.m + 1) ^ 2) * (4 * fL I.m + 1) +
        76 * fL I.m + 170 by omega)
    have h2 := Nat.mul_le_mul hME (show 112 * L + 180 ≤ 112 * fL I.m + 180 by omega)
    linarith only [hL, h1, h2]
  have hMaxLe : max (dryTermFixed selSz source J) (dryDeepShiftFixed Psc selSz source J) ≤
      fShiftF I.m := by
    unfold dryTermFixed dryDeepShiftFixed
    dsimp only [fShiftF] at hMd hDF ⊢
    refine max_le ?_ ((Nat.add_le_add hDF hDS).trans (Nat.le_add_left _ _))
    exact (Nat.add_le_add (Nat.add_le_add_right (show 41 * (2 * levelM _ _ _) ≤ 82 * 2 ^ dryKOfM I.m by
      calc 41 * (2 * levelM _ _ _) = 82 * levelM _ _ _ := by ring
        _ ≤ 82 * 2 ^ dryKOfM I.m := Nat.mul_le_mul_left 82 hMd) 320) hTF).trans (Nat.le_add_right _ _)
  unfold cycleLoopIterBudget dryInnerSizesWithSelect
  dsimp only [fTot]
  linarith only [hSel', hEvalLe, hL, hd, hMaxLe]

/-- `PolyNat` bound on `s.initSpace' + initWiredExtraSpace cfg G` (`DryEnvelopeIneqs` clause 3),
including `selSz.initSelectSpace` (for `SelectRegion`, `SelectHeap`, `SelectLevelMeta`, and
`selectInitFinalizeSpace`). -/
theorem dryInitSpaceWithExtra_le_poly (Psc : DrySparseCorePieces)
    (selSz : DrySelectRebuildSizes) (hSel : DrySelectRebuildSizeBounds selSz) :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let L := ipmQualityLimbs I.m V k
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        (initConcreteSpace I.m (namedInstance I).n L cfg.P.d (dryParamSpace source J) dryCapExp
          (dryCapLimit dryWitnessUsed J) (dryLastSpace J)
          (LinkCut.PathProg.arenaEnd 0 (namedInstance I).n L)
          (20 * LinkCut.PathProg.treeLimbs L + 100)
          (dryCoreInitSpace Psc J) (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1))
          cfg.N₀ + selSz.initSelectSpace source J) +
          initWiredExtraSpace cfg (namedInstance I) ≤ f I.m := by
  obtain ⟨fInitSp, hfInitSpP, hInitSp⟩ := dryInitSpace_le_poly Psc
  obtain ⟨fInitSelSp, hfInitSelSpP, hInitSelSp⟩ := hSel.hInitSelectSpacePoly
  refine ⟨fun M => (fInitSp M + fInitSelSp M) + 24 * dryM0OfM M,
    PolyNat.add (PolyNat.add hfInitSpP hfInitSelSpP) (PolyNat.const_mul dryM0OfM_poly 24),
    fun source J hJn hJm hCap => ?_⟩
  have h1 := hInitSp source J hJn hJm hCap
  have hSel1 := hInitSelSp source J hJn hJm hCap
  have hNf := dryNfMax_le_two_mul_M0 J
  have hMle : (solverConnectedAugmented J).m ≤ dryM0OfM (solverConnectedAugmented J).m := le_max_left _ _
  have hGm : (namedInstance (solverConnectedAugmented J)).m = (solverConnectedAugmented J).m :=
    namedInstance_m _
  have hEx : initWiredExtraSpace (concreteCirculationCfgWithLast dryWitnessUsed J)
      (namedInstance (solverConnectedAugmented J)) ≤ 24 * dryM0OfM (solverConnectedAugmented J).m := by
    unfold initWiredExtraSpace initTargetCap
    rw [hGm]; dsimp only at hNf; omega
  exact Nat.add_le_add (Nat.add_le_add h1 hSel1) hEx

/-- `SubpolyNat` bound on `initBudFull / (I.m + 1)` with `initWiredExtraCost`
(`DryEnvelopeIneqs` clause 4). -/
theorem dryInitBudgetWithExtra_le_subpoly (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (hOpen : DryOpenSizeBounds openSz) (selSz : DrySelectRebuildSizes)
    (hSel : DrySelectRebuildSizeBounds selSz) :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let L := ipmQualityLimbs I.m V k
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        let s := dryInnerSizesWithSelect Psc openSz selSz source J
        let B_iter := cycleLoopIterBudget L cfg.P.d (s.selectBudget + s.evalBudget + 90)
          (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220)
        (s.initFixed + initWiredExtraCost cfg G) +
          B_iter * ((cfg.P.d + 1) *
            ⌊(10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1)⌋₊) +
          s.toolMul * chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0) +
          s.treeMul * chainRebuildCap cfg (treeUpdateFactorNat cfg) (fun _ => 0) ≤
          (I.m + 1) * f I.m := by
  obtain ⟨fInitFix, hfInitFixSub, hInitFix⟩ := dryInitFixed_le_subpoly Psc
  obtain ⟨fInitSelFix, hfInitSelFixSub, hInitSelFix⟩ := hSel.hInitSelectFixedSub
  obtain ⟨fBIter, hfBIterSub, hBIter⟩ := dryBIter_le_subpoly Psc openSz hOpen selSz hSel
  obtain ⟨fShiftQ, hfShiftQSub, hShiftQ⟩ := dryInitShiftQuota_le_subpoly
  obtain ⟨fToolMul0, hfToolMulSub0, hToolMul⟩ := dryToolMul_le_subpoly Psc selSz hSel
  obtain ⟨fCoreTool, fCoreTree, hfCoreToolSub, hfCoreTreeSub, hCoreMul⟩ := hOpen.hCoreMulSubpoly
  let fToolMul : ℕ → ℕ := fun M => fToolMul0 M + fCoreTool M
  have hfToolMulSub : SubpolyNat fToolMul := SubpolyNat.add hfToolMulSub0 hfCoreToolSub
  obtain ⟨fRunF, hfRunFSub, hRunF⟩ := dryRuntimeFactor_le_subpoly
  obtain ⟨fTreeF, hfTreeFSub, hTreeF⟩ := dryTreeUpdateFactor_le_subpoly
  obtain ⟨fRebCap, hfRebCapSub, hRebCap⟩ := dryInitRebuildCap_le_subpoly
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  let fL := dryLimbsOfM
  have hfL := dryLimbsOfM_subpoly
  let K_thr : ℕ := concreteEdgeThresholdWithLast dryWitnessUsed + 1
  let fLogM0 : ℕ → ℕ := fun M => Nat.log 2 (4 * dryM0OfM M + 2) + 1
  have hfLogM0Sub : SubpolyNat fLogM0 := subpolyNat_log_of_poly (PolyNat.const_mul dryM0OfM_poly 4)
  let fTreeMul : ℕ → ℕ := fun M =>
    50 * (LinkCut.PathProg.pathC * (fL M + 1) ^ 2) * (4 * fL M + 1) + 247 * fL M + 722 +
      fCoreTree M
  have hfTreeMulSub : SubpolyNat fTreeMul :=
    SubpolyNat.add (SubpolyNat.add_const (SubpolyNat.add
      (SubpolyNat.mul (SubpolyNat.const_mul (SubpolyNat.const_mul (SubpolyNat.pow (SubpolyNat.add_const hfL 1) 2)
        LinkCut.PathProg.pathC) 50) (SubpolyNat.add_const (SubpolyNat.const_mul hfL 4) 1))
      (SubpolyNat.const_mul hfL 247)) 722) hfCoreTreeSub
  let fExtraC : ℕ → ℕ := fun M => 40 * fLogM0 M + 22 * (fd M + 1) + (102 + 68 * K_thr + 450)
  have hfExtraCSub : SubpolyNat fExtraC :=
    SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.const_mul hfLogM0Sub 40)
      (SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) 22)) (102 + 68 * K_thr + 450)
  let fTot : ℕ → ℕ := fun M =>
    (fInitFix M + fInitSelFix M) + fExtraC M + fBIter M * fShiftQ M +
      fToolMul M * (fRunF M * fRebCap M) + fTreeMul M * (fTreeF M * fRebCap M)
  have hfTotSub : SubpolyNat fTot :=
    SubpolyNat.add (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add
      (SubpolyNat.add hfInitFixSub hfInitSelFixSub) hfExtraCSub)
      (SubpolyNat.mul hfBIterSub hfShiftQSub))
      (SubpolyNat.mul hfToolMulSub (SubpolyNat.mul hfRunFSub hfRebCapSub)))
      (SubpolyNat.mul hfTreeMulSub (SubpolyNat.mul hfTreeFSub hfRebCapSub))
  refine ⟨fTot, hfTotSub, fun source J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  set G := namedInstance I
  set s := dryInnerSizesWithSelect Psc openSz selSz source J
  have hL : L ≤ fL I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hd : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
  have h1 : s.initFixed ≤ (I.m + 1) * (fInitFix I.m + fInitSelFix I.m) := by
    have h1a := hInitFix source J hJn hJm hCap
    have h1b := hInitSelFix source J hJn hJm hCap
    change _ + selSz.initSelectFixed source J ≤ _
    rw [Nat.mul_add]
    exact Nat.add_le_add h1a h1b
  have h2 : initWiredExtraCost cfg G ≤ (I.m + 1) * fExtraC I.m := by
    unfold initWiredExtraCost initTargetCap
    have hGm : G.m = I.m := namedInstance_m I
    have hNf := dryNfMax_le_two_mul_M0 J
    have hMle : I.m ≤ dryM0OfM I.m := le_max_left _ _
    have hM0K : dryM0OfM I.m ≤ K_thr * (I.m + 1) := dryM0OfM_le_mul I.m
    have hclog : Nat.clog 2 (4 * cfg.P.M₀ + 2) ≤ fLogM0 I.m := dry_clog2_le_log2_add_one _
    have hA : 40 * Nat.clog 2 (4 * cfg.P.M₀ + 2) + 22 * (cfg.P.d + 1) + 450 ≤
        (I.m + 1) * (40 * fLogM0 I.m + 22 * (fd I.m + 1) + 450) :=
      (by omega : 40 * Nat.clog 2 (4 * cfg.P.M₀ + 2) + 22 * (cfg.P.d + 1) + 450 ≤
          40 * fLogM0 I.m + 22 * (fd I.m + 1) + 450).trans
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    have hB : 102 * G.m ≤ (I.m + 1) * 102 := by rw [hGm]; nlinarith
    have hC : 17 * (Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * G.m) ≤
        (I.m + 1) * (68 * K_thr) := by
      rw [hGm]; dsimp only at hNf
      have hT : Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * I.m ≤
          4 * dryM0OfM I.m := by linarith only [hNf, hMle]
      calc _ ≤ 17 * (4 * dryM0OfM I.m) := Nat.mul_le_mul_left 17 hT
        _ ≤ 17 * (4 * (K_thr * (I.m + 1))) := Nat.mul_le_mul_left 17 (Nat.mul_le_mul_left 4 hM0K)
        _ = (I.m + 1) * (68 * K_thr) := by ring
    have hExp2 : (I.m + 1) * fExtraC I.m =
        (I.m + 1) * (40 * fLogM0 I.m + 22 * (fd I.m + 1) + 450) + (I.m + 1) * 102 +
        (I.m + 1) * (68 * K_thr) := by dsimp only [fExtraC]; ring
    rw [hExp2]; linarith only [hA, hB, hC]
  have h3 : cycleLoopIterBudget L cfg.P.d (s.selectBudget + s.evalBudget + 90)
        (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220) *
      ((cfg.P.d + 1) * ⌊(10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1)⌋₊) ≤
      (I.m + 1) * (fBIter I.m * fShiftQ I.m) := by
    have hmul := Nat.mul_le_mul (hBIter source J hJn hJm hCap) (hShiftQ J hJn hJm hCap)
    calc _ ≤ fBIter I.m * ((I.m + 1) * fShiftQ I.m) := hmul
      _ = (I.m + 1) * (fBIter I.m * fShiftQ I.m) := by ring
  have hTool : s.toolMul ≤ fToolMul I.m :=
    Nat.add_le_add (hToolMul source J hJn hJm hCap) (hCoreMul source J hJn hJm hCap).1
  have hTree : s.treeMul ≤ fTreeMul I.m := by
    show wireTreeSyncEditCost L (detectOffTreeDrainUnit L) + 2 + openSz.coreTreeMul source J ≤
      fTreeMul I.m
    have hct : openSz.coreTreeMul source J ≤ fCoreTree I.m := (hCoreMul source J hJn hJm hCap).2
    unfold wireTreeSyncEditCost detectOffTreeDrainUnit
    dsimp only [fTreeMul]
    have hsq : (L + 1) ^ 2 ≤ (fL I.m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 50 (Nat.mul_le_mul_left LinkCut.PathProg.pathC hsq))
      (by omega : 4 * L + 1 ≤ 4 * fL I.m + 1)
    omega
  have h4 : s.toolMul * chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0) ≤
      (I.m + 1) * (fToolMul I.m * (fRunF I.m * fRebCap I.m)) := by
    rw [dry_chainRebuildCap_eq_mul]
    have hmul := Nat.mul_le_mul hTool
      (Nat.mul_le_mul (hRunF J hJn hJm hCap) (hRebCap J hJn hJm hCap))
    calc _ ≤ fToolMul I.m * (fRunF I.m * ((I.m + 1) * fRebCap I.m)) := hmul
      _ = (I.m + 1) * (fToolMul I.m * (fRunF I.m * fRebCap I.m)) := by ring
  have h5 : s.treeMul * chainRebuildCap cfg (treeUpdateFactorNat cfg) (fun _ => 0) ≤
      (I.m + 1) * (fTreeMul I.m * (fTreeF I.m * fRebCap I.m)) := by
    rw [dry_chainRebuildCap_eq_mul]
    have hmul := Nat.mul_le_mul hTree
      (Nat.mul_le_mul (hTreeF J hJn hJm hCap) (hRebCap J hJn hJm hCap))
    calc _ ≤ fTreeMul I.m * (fTreeF I.m * ((I.m + 1) * fRebCap I.m)) := hmul
      _ = (I.m + 1) * (fTreeMul I.m * (fTreeF I.m * fRebCap I.m)) := by ring
  have hExp : (I.m + 1) * fTot I.m =
      (I.m + 1) * (fInitFix I.m + fInitSelFix I.m) + (I.m + 1) * fExtraC I.m +
      (I.m + 1) * (fBIter I.m * fShiftQ I.m) +
      (I.m + 1) * (fToolMul I.m * (fRunF I.m * fRebCap I.m)) +
      (I.m + 1) * (fTreeMul I.m * (fTreeF I.m * fRebCap I.m)) := by
    dsimp only [fTot]; simp only [Nat.mul_add]
  dsimp only
  rw [hExp]
  linarith only [h1, h2, h3, h4, h5]

/-- `PolyNat` bound on the Update heap space (`DryEnvelopeIneqs` clause 6), including
`selSz.termSelectSpace` and `selSz.deepSelectSpace`. -/
theorem dryUpdateSpace_le_poly (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (hOpen : DryOpenSizeBounds openSz) (selSz : DrySelectRebuildSizes)
    (hSel : DrySelectRebuildSizeBounds selSz) :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let L := ipmQualityLimbs I.m V k
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        let s := dryInnerSizesWithSelect Psc openSz selSz source J
        let nfMax := Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0
        let loopMax := (Chain.Ordered.loopDigitCap cfg + 1) ^ (cfg.P.d + 1)
        updateSpaceBound L I.m cfg.P.d nfMax (2 * I.m) loopMax
          (6 + s.selectSpace + s.evalSpace) (max s.termSpace s.deepSpace)
          s.maxEdges s.maxPaths (cfg.P.d + (8 * (2 * I.m) + 1) + s.coreSpace (2 * I.m)) + 2 ≤
          f I.m := by
  obtain ⟨fSelSp, fCoreSp, hfSelSpP, hfCoreSpP, hSp⟩ := hOpen.hSpacePoly
  obtain ⟨_, fME, fMP, _, _, _, hfMESub, hfMPSub, _, _, hRate⟩ := hOpen.hRateSubpoly
  obtain ⟨fDeepSp, hfDeepSpP, hDeepSp⟩ := dryDeepSpace_le_poly Psc
  obtain ⟨fTSelSp, hfTSelSpP, hTSelSp⟩ := hSel.hTermSelectSpacePoly
  obtain ⟨fDSelSp, hfDSelSpP, hDSelSp⟩ := hSel.hDeepSelectSpacePoly
  obtain ⟨fLoop, hfLoopP, hLoop⟩ := dryLoopMax_le_poly
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  let fL := dryLimbsOfM
  have hfLP := SubpolyNat.toPolyNat dryLimbsOfM_subpoly
  have hfMEP := SubpolyNat.toPolyNat hfMESub
  have hfMPP := SubpolyNat.toPolyNat hfMPSub
  have hfCapP := PolyNat.const_mul (SubpolyNat.toPolyNat subpolyNat_two_pow_dryKOfM) 2
  have hfdP := SubpolyNat.toPolyNat hfdSub
  let fEvalSp : ℕ → ℕ := fun M =>
    2 * fL M + fMP M * (84 * fL M + 260) + fME M * (3 * fL M) + 1
  have hfEvalSpP : PolyNat fEvalSp :=
    PolyNat.add_const (PolyNat.add (PolyNat.add (PolyNat.const_mul hfLP 2)
      (PolyNat.mul hfMPP (PolyNat.add_const (PolyNat.const_mul hfLP 84) 260)))
      (PolyNat.mul hfMEP (PolyNat.const_mul hfLP 3))) 1
  let fShiftSp : ℕ → ℕ := fun M =>
    ((2 * 2 ^ dryKOfM M) * (170 * fL M + 532) + fTSelSp M) + (fDeepSp M + fDSelSp M)
  have hfShiftSpP : PolyNat fShiftSp :=
    PolyNat.add
      (PolyNat.add (PolyNat.mul hfCapP (PolyNat.add_const (PolyNat.const_mul hfLP 170) 532)) hfTSelSpP)
      (PolyNat.add hfDeepSpP hfDSelSpP)
  let fGoodSp : ℕ → ℕ := fun M =>
    60 * (fL M) ^ 2 + 58 * fL M + 10 + fMP M * (80 * fL M + 260) + fME M * (17 * fL M + 4)
  have hfGoodSpP : PolyNat fGoodSp :=
    PolyNat.add (PolyNat.add
      (PolyNat.add_const (PolyNat.add (PolyNat.const_mul (PolyNat.pow hfLP 2) 60)
        (PolyNat.const_mul hfLP 58)) 10)
      (PolyNat.mul hfMPP (PolyNat.add_const (PolyNat.const_mul hfLP 80) 260)))
      (PolyNat.mul hfMEP (PolyNat.add_const (PolyNat.const_mul hfLP 17) 4))
  let fTot : ℕ → ℕ := fun M =>
    (6 * fL M + 2 * fd M + 48 * dryM0OfM M + 48 * M + 12) +
      2 * (M * fL M) + fCoreSp M +
      (fLoop M + 1) * (6 + fSelSp M + fEvalSp M + (5 * fL M + 1) + fShiftSp M) +
      fGoodSp M
  have hfTotP : PolyNat fTot := by
    have h1 := PolyNat.add_const (PolyNat.add (PolyNat.add (PolyNat.add
      (PolyNat.const_mul hfLP 6) (PolyNat.const_mul hfdP 2))
      (PolyNat.const_mul dryM0OfM_poly 48)) (PolyNat.const_mul PolyNat.id 48)) 12
    have h2 := PolyNat.const_mul (PolyNat.mul PolyNat.id hfLP) 2
    have h3 := PolyNat.mul (PolyNat.add_const hfLoopP 1)
      (PolyNat.add (PolyNat.add (PolyNat.add
        (PolyNat.add (PolyNat.add_const hfSelSpP 6) hfEvalSpP)
        (PolyNat.add_const (PolyNat.const_mul hfLP 5) 1)) hfShiftSpP) (PolyNat.const 0))
    exact PolyNat.mono (fun M => by
        dsimp only [fTot, fL]
        have h3eq : 6 + fSelSp M + fEvalSp M + (5 * dryLimbsOfM M + 1) + fShiftSp M =
            fSelSp M + 6 + fEvalSp M + (5 * dryLimbsOfM M + 1) + fShiftSp M + 0 := by omega
        rw [h3eq])
      (PolyNat.add (PolyNat.add (PolyNat.add (PolyNat.add h1 h2) hfCoreSpP) h3) hfGoodSpP)
  refine ⟨fTot, hfTotP, fun source J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  set G := namedInstance I
  have hL : L ≤ fL I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hd : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
  have hNf : Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 ≤ 2 * dryM0OfM I.m :=
    dryNfMax_le_two_mul_M0 J
  have hMle : I.m ≤ dryM0OfM I.m := le_max_left _ _
  have hLoop' := hLoop J hJn hJm hCap
  obtain ⟨hSelSp, hCoreSp⟩ := hSp source J hJn hJm hCap
  obtain ⟨_, hME, hMP, _⟩ := hRate source J hJn hJm hCap
  have hMd := dryLevelMd_le_two_pow_dryKOfM J hJn hJm hCap
  have hDeep' := hDeepSp J hJn hJm hCap
  have hEvalSpLe : evalCycleSpace L (openSz.maxEdges source J) (openSz.maxPaths source J) ≤
      fEvalSp I.m := by
    unfold evalCycleSpace pathApplySpace LinkCut.PathProg.treeLimbs
    dsimp only [fEvalSp]
    have h1 := Nat.mul_le_mul hMP (show 20 * (4 * L + 8) + 100 + 4 * L ≤ 84 * fL I.m + 260 by omega)
    have h2 := Nat.mul_le_mul hME (show 3 * L ≤ 3 * fL I.m by omega)
    linarith only [hL, h1, h2]
  have hShiftSpLe : max ((2 * levelM cfg.TP cfg.P cfg.P.d) * (2 + wireTreeSyncEditSpace L) +
      selSz.termSelectSpace source J) (dryDeepSpace Psc J + selSz.deepSelectSpace source J) ≤
      fShiftSp I.m := by
    have hT : (2 * levelM cfg.TP cfg.P cfg.P.d) * (2 + wireTreeSyncEditSpace L) ≤
        (2 * 2 ^ dryKOfM I.m) * (170 * fL I.m + 532) := by
      unfold wireTreeSyncEditSpace LinkCut.PathProg.treeLimbs
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hMd) (by omega)
    have hTS := hTSelSp source J hJn hJm hCap
    have hDS := hDSelSp source J hJn hJm hCap
    exact max_le
      ((Nat.add_le_add hT hTS).trans (Nat.le_add_right _ _))
      ((Nat.add_le_add hDeep' hDS).trans (Nat.le_add_left _ _))
  have hLoopTerm : ((Chain.Ordered.loopDigitCap cfg + 1) ^ (cfg.P.d + 1) + 1) *
      cycleLoopIterSpace L (6 + openSz.selectSpace source J +
        evalCycleSpace L (openSz.maxEdges source J) (openSz.maxPaths source J))
        (max ((2 * levelM cfg.TP cfg.P cfg.P.d) * (2 + wireTreeSyncEditSpace L) +
          selSz.termSelectSpace source J)
          (dryDeepSpace Psc J + selSz.deepSelectSpace source J)) ≤
      (fLoop I.m + 1) * (6 + fSelSp I.m + fEvalSp I.m + (5 * fL I.m + 1) + fShiftSp I.m) := by
    unfold cycleLoopIterSpace
    exact Nat.mul_le_mul (Nat.add_le_add_right hLoop' 1)
      (by linarith only [hSelSp, hEvalSpLe, hL, hShiftSpLe])
  have hGoodLe : goodApplySpace L (openSz.maxPaths source J) (openSz.maxEdges source J) ≤
      fGoodSp I.m := by
    unfold goodApplySpace Num.fixedDivideSpace Num.integerDivideSpace Num.unsignedDivideSpace
      pathApplySpace explicitRouteSpace LinkCut.PathProg.treeLimbs
    dsimp only [fGoodSp]
    have hsq : L ^ 2 ≤ (fL I.m) ^ 2 := Nat.pow_le_pow_left hL 2
    have hDiv : 10 * L + (3 * (3 * L) + 2 + 5 * (3 * L) * (3 * L + 1) + 3 * (3 * L)) + 8 * L ≤
        60 * (fL I.m) ^ 2 + 58 * fL I.m + 10 := by nlinarith only [hL, hsq]
    have hP := Nat.mul_le_mul hMP (show 20 * (4 * L + 8) + 100 ≤ 80 * fL I.m + 260 by omega)
    have hE : openSz.maxEdges source J + openSz.maxEdges source J * (17 * L + 3) ≤
        fME I.m * (17 * fL I.m + 4) := by
      have heq : openSz.maxEdges source J + openSz.maxEdges source J * (17 * L + 3) =
          openSz.maxEdges source J * (17 * L + 4) := by ring
      rw [heq]; exact Nat.mul_le_mul hME (by omega)
    linarith only [hDiv, hP, hE]
  have hML : I.m * L ≤ I.m * fL I.m := Nat.mul_le_mul_left _ hL
  unfold updateSpaceBound dryInnerSizesWithSelect
  dsimp only [fTot]
  linarith only [hL, hd, hNf, hMle, hCoreSp, hML, hLoopTerm, hGoodLe]

/-- `SubpolyNat` bound on the amortized Update rate (`DryEnvelopeIneqs` clause 7). -/
theorem dryUpdateRate_le_subpoly (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (hOpen : DryOpenSizeBounds openSz) (selSz : DrySelectRebuildSizes)
    (hSel : DrySelectRebuildSizeBounds selSz) :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let L := ipmQualityLimbs I.m V k
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        let s := dryInnerSizesWithSelect Psc openSz selSz source J
        let B_iter := cycleLoopIterBudget L cfg.P.d (s.selectBudget + s.evalBudget + 90)
          (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220)
        let creditPerEdge :=
          s.toolMul * (runtimeFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 +
            (40 * Nat.clog 2 (3 * cfg.P.M₀ + 2) + 40)) +
          s.treeMul * (treeUpdateFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0)
        ∃ ρ₀ ρ₁ : ℕ,
          (∀ u ≤ 2 * I.m, s.coreFixed u ≤ ρ₀ + ρ₁ * u) ∧
          (600 + 20 * L +
              (ρ₀ + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 62 * (cfg.P.d + 1) + 240) +
              updateGoodBranchBudget L G.n s.maxEdges s.maxPaths (detectOffTreeDrainUnit L)) +
            (520 + 34 * L + ρ₁ + creditPerEdge) +
            B_iter + B_iter * fwdWeight cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) 0 ≤
            f I.m := by
  obtain ⟨_, fME, fMP, fRho0, fRho1, _, hfMESub, hfMPSub, hfRho0Sub, hfRho1Sub, hRate⟩ :=
    hOpen.hRateSubpoly
  obtain ⟨fBIter, hfBIterSub, hBIter⟩ := dryBIter_le_subpoly Psc openSz hOpen selSz hSel
  obtain ⟨fFwd, hfFwdSub, hFwd⟩ := dryFwdWeight_le_subpoly
  obtain ⟨fCapFwd, hfCapFwdSub, hCapFwd⟩ := dryCapFwdWeight_le_subpoly
  obtain ⟨fRunF, hfRunFSub, hRunF⟩ := dryRuntimeFactor_le_subpoly
  obtain ⟨fTreeF, hfTreeFSub, hTreeF⟩ := dryTreeUpdateFactor_le_subpoly
  obtain ⟨fToolMul0, hfToolMulSub0, hToolMul⟩ := dryToolMul_le_subpoly Psc selSz hSel
  obtain ⟨fCoreTool, fCoreTree, hfCoreToolSub, hfCoreTreeSub, hCoreMul⟩ := hOpen.hCoreMulSubpoly
  let fToolMul : ℕ → ℕ := fun M => fToolMul0 M + fCoreTool M
  have hfToolMulSub : SubpolyNat fToolMul := SubpolyNat.add hfToolMulSub0 hfCoreToolSub
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  let fL := dryLimbsOfM
  have hfL := dryLimbsOfM_subpoly
  let fLogM0 : ℕ → ℕ := fun M => Nat.log 2 (3 * dryM0OfM M + 2) + 1
  have hfLogM0Sub : SubpolyNat fLogM0 := subpolyNat_log_of_poly (PolyNat.const_mul dryM0OfM_poly 3)
  let fLogV : ℕ → ℕ := fun M => Nat.log 2 (4 * M + 5) + 1
  have hfLogVSub : SubpolyNat fLogV :=
    SubpolyNat.mono (fun M => by
        dsimp only [fLogV]; exact Nat.add_le_add_right (Nat.log_mono_right (b := 2) (by omega)) 1)
      (subpolyNat_log_of_poly (PolyNat.add_const (PolyNat.const_mul PolyNat.id 4) 3))
  let fTreeMul : ℕ → ℕ := fun M =>
    50 * (LinkCut.PathProg.pathC * (fL M + 1) ^ 2) * (4 * fL M + 1) + 247 * fL M + 722 +
      fCoreTree M
  have hfTreeMulSub : SubpolyNat fTreeMul :=
    SubpolyNat.add (SubpolyNat.add_const (SubpolyNat.add
      (SubpolyNat.mul (SubpolyNat.const_mul (SubpolyNat.const_mul (SubpolyNat.pow (SubpolyNat.add_const hfL 1) 2)
        LinkCut.PathProg.pathC) 50) (SubpolyNat.add_const (SubpolyNat.const_mul hfL 4) 1))
      (SubpolyNat.const_mul hfL 247)) 722) hfCoreTreeSub
  let fGood : ℕ → ℕ := fun M =>
    2852 * (fL M) ^ 2 + 3183 * fL M +
      fMP M * (25 * (LinkCut.PathProg.pathC * (fL M + 1) ^ 2) * fLogV M + 45) +
      fME M * (136 * fME M + 152 * (fL M) ^ 2 + 648 * fL M + 1180) + 1400
  have hfGoodSub : SubpolyNat fGood := by
    have hL2 := SubpolyNat.pow hfL 2
    have hL12 := SubpolyNat.pow (SubpolyNat.add_const hfL 1) 2
    have hP := SubpolyNat.mul hfMPSub (SubpolyNat.add_const
      (SubpolyNat.mul (SubpolyNat.const_mul (SubpolyNat.const_mul hL12 LinkCut.PathProg.pathC) 25) hfLogVSub) 45)
    have hE := SubpolyNat.mul hfMESub (SubpolyNat.add_const
      (SubpolyNat.add (SubpolyNat.add (SubpolyNat.const_mul hfMESub 136) (SubpolyNat.const_mul hL2 152))
        (SubpolyNat.const_mul hfL 648)) 1180)
    exact SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.add
      (SubpolyNat.add (SubpolyNat.const_mul hL2 2852) (SubpolyNat.const_mul hfL 3183)) hP) hE) 1400
  let fCred : ℕ → ℕ := fun M =>
    fToolMul M * (fRunF M * fCapFwd M + (40 * fLogM0 M + 40)) + fTreeMul M * (fTreeF M * fCapFwd M)
  have hfCredSub : SubpolyNat fCred :=
    SubpolyNat.add
      (SubpolyNat.mul hfToolMulSub (SubpolyNat.add (SubpolyNat.mul hfRunFSub hfCapFwdSub)
        (SubpolyNat.add_const (SubpolyNat.const_mul hfLogM0Sub 40) 40)))
      (SubpolyNat.mul hfTreeMulSub (SubpolyNat.mul hfTreeFSub hfCapFwdSub))
  let fTot : ℕ → ℕ := fun M =>
    (600 + 20 * fL M +
      (fRho0 M + (30 * (fd M + 1) + 25 * fLogM0 M + 140) + 62 * (fd M + 1) + 240) + fGood M) +
    (520 + 34 * fL M + fRho1 M + fCred M) +
    fBIter M + fBIter M * fFwd M
  have hfTotSub : SubpolyNat fTot := by
    have h1 := SubpolyNat.add_const (SubpolyNat.const_mul hfL 20) 600
    have h2 := SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.add hfRho0Sub
      (SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) 30)
        (SubpolyNat.const_mul hfLogM0Sub 25)) 140))
      (SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) 62)) 240
    have h3 := SubpolyNat.add (SubpolyNat.add (SubpolyNat.add_const (SubpolyNat.const_mul hfL 34) 520) hfRho1Sub) hfCredSub
    have h4 := SubpolyNat.add hfBIterSub (SubpolyNat.mul hfBIterSub hfFwdSub)
    exact SubpolyNat.mono (fun M => by dsimp only [fTot, fL]; omega)
      (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add h1 h2) hfGoodSub) h3) h4)
  refine ⟨fTot, hfTotSub, fun source J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  set G := namedInstance I
  set s := dryInnerSizesWithSelect Psc openSz selSz source J
  have hL : L ≤ fL I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hd : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
  have hGn : G.n ≤ 2 * I.m + 2 := dryGn_le_two_mul_m_add_two J hJn hJm hCap
  obtain ⟨_, hME, hMP, hCoreF⟩ := hRate source J hJn hJm hCap
  refine ⟨fRho0 I.m, fRho1 I.m, hCoreF, ?_⟩
  have hSQ : shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ ≤ 30 * (fd I.m + 1) + 25 * fLogM0 I.m + 140 := by
    unfold shiftQuotaWriterBudget
    have hc : Nat.clog 2 (cfg.P.M₀ + 1) ≤ fLogM0 I.m :=
      (dry_clog2_le_log2_add_one _).trans (Nat.add_le_add_right (Nat.log_mono_right (b := 2) (by
        change cfg.P.M₀ + 1 ≤ 3 * cfg.P.M₀ + 2; omega)) 1)
    omega
  have hGoodLe : updateGoodBranchBudget L G.n s.maxEdges s.maxPaths (detectOffTreeDrainUnit L) ≤
      fGood I.m := by
    unfold updateGoodBranchBudget pathTreeBudget detectOffTreeDrainUnit
    dsimp only [fGood, fLogV]
    have hL2 : L ^ 2 ≤ (fL I.m) ^ 2 := Nat.pow_le_pow_left hL 2
    have hL12 : (L + 1) ^ 2 ≤ (fL I.m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hlgV : Nat.log 2 (2 * G.n + 1) ≤ Nat.log 2 (4 * I.m + 5) :=
      Nat.log_mono_right (b := 2) (by omega)
    have hPT : 25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (Nat.log 2 (2 * G.n + 1) + 1) ≤
        25 * (LinkCut.PathProg.pathC * (fL I.m + 1) ^ 2) * (Nat.log 2 (4 * I.m + 5) + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 25 (Nat.mul_le_mul_left LinkCut.PathProg.pathC hL12)) (by omega)
    have hMP' := Nat.mul_le_mul hMP (by omega : 25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) *
      (Nat.log 2 (2 * G.n + 1) + 1) + 45 ≤
      25 * (LinkCut.PathProg.pathC * (fL I.m + 1) ^ 2) * (Nat.log 2 (4 * I.m + 5) + 1) + 45)
    have hME' := Nat.mul_le_mul hME (show 136 * openSz.maxEdges source J + 152 * L ^ 2 + 561 * L +
        (87 * L + 220) + 960 ≤ 136 * fME I.m + 152 * (fL I.m) ^ 2 + 648 * fL I.m + 1180 by
      linarith only [hME, hL2, hL])
    have hMEs : s.maxEdges = openSz.maxEdges source J := rfl
    have hMPs : s.maxPaths = openSz.maxPaths source J := rfl
    rw [hMEs, hMPs]
    linarith only [hL2, hL, hMP', hME']
  have hTool : s.toolMul ≤ fToolMul I.m :=
    Nat.add_le_add (hToolMul source J hJn hJm hCap) (hCoreMul source J hJn hJm hCap).1
  have hTree : s.treeMul ≤ fTreeMul I.m := by
    show wireTreeSyncEditCost L (detectOffTreeDrainUnit L) + 2 + openSz.coreTreeMul source J ≤
      fTreeMul I.m
    have hct : openSz.coreTreeMul source J ≤ fCoreTree I.m := (hCoreMul source J hJn hJm hCap).2
    unfold wireTreeSyncEditCost detectOffTreeDrainUnit
    dsimp only [fTreeMul]
    have hsq : (L + 1) ^ 2 ≤ (fL I.m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 50 (Nat.mul_le_mul_left LinkCut.PathProg.pathC hsq))
      (by omega : 4 * L + 1 ≤ 4 * fL I.m + 1)
    omega
  have hCredLe : s.toolMul * (runtimeFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 +
      (40 * Nat.clog 2 (3 * cfg.P.M₀ + 2) + 40)) +
      s.treeMul * (treeUpdateFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0) ≤ fCred I.m := by
    dsimp only [fCred]
    have hc : Nat.clog 2 (3 * cfg.P.M₀ + 2) ≤ fLogM0 I.m := dry_clog2_le_log2_add_one _
    have hc40 : 40 * Nat.clog 2 (3 * cfg.P.M₀ + 2) + 40 ≤ 40 * fLogM0 I.m + 40 := by omega
    have h1 := Nat.mul_le_mul hTool
      (Nat.add_le_add (Nat.mul_le_mul (hRunF J hJn hJm hCap) (hCapFwd J hJn hJm hCap)) hc40)
    have h2 := Nat.mul_le_mul hTree
      (Nat.mul_le_mul (hTreeF J hJn hJm hCap) (hCapFwd J hJn hJm hCap))
    exact Nat.add_le_add h1 h2
  have hBI := hBIter source J hJn hJm hCap
  have hBIF := Nat.mul_le_mul hBI (hFwd J hJn hJm hCap)
  dsimp only [fTot]
  linarith only [hL, hd, hSQ, hGoodLe, hCredLe, hBI, hBIF]

/-! ## 4. Concrete `dryInnerBounds : OrdSolverInnerBounds`, `InnerBoundsHyp`, `DryEnvelopeIneqs`, and `hNames` -/

/-- Concrete `OrdSolverInnerBounds` built from `dryInnerSizesWithSelect` and the uniform asymptotic
bounds of `AssemblyDryRunSCLastMult`, `AssemblyDryRunSCAsymp`, `AssemblyDryRunSCLastSpace`, and
`AssemblyDryRunSCInitAsymp`. -/
def dryInnerBounds (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (hOpen : DryOpenSizeBounds openSz) (selSz : DrySelectRebuildSizes)
    (hSel : DrySelectRebuildSizeBounds selSz) : OrdSolverInnerBounds where
  limbs := dryLimbsOfM
  verts := fun M => 2 * M + 2
  names := fun M => 8 * dryM0OfM M
  initSpace := Classical.choose (dryInitSpaceWithExtra_le_poly Psc selSz hSel)
  initBudget := fun M =>
    (M + 1) * Classical.choose (dryInitBudgetWithExtra_le_subpoly Psc openSz hOpen selSz hSel) M
  updateSpace := Classical.choose (dryUpdateSpace_le_poly Psc openSz hOpen selSz hSel)
  updateRate := Classical.choose (dryUpdateRate_le_subpoly Psc openSz hOpen selSz hSel)

/-- `dryInnerBounds` satisfies all eight clauses of `InnerBoundsHyp`. -/
theorem dryInnerBounds_hyp (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (hOpen : DryOpenSizeBounds openSz) (selSz : DrySelectRebuildSizes)
    (hSel : DrySelectRebuildSizeBounds selSz) :
    InnerBoundsHyp (dryInnerBounds Psc openSz hOpen selSz hSel) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact dryLimbsOfM_subpoly
  · exact SubpolyNat.mono (fun M => by
        show Nat.log 2 (2 * (2 * M + 2) + 1) ≤ Nat.log 2 (4 * M + 5 + 2) + 1
        exact (Nat.log_mono_right (b := 2) (by omega)).trans (Nat.le_succ _))
      (subpolyNat_log_of_poly (PolyNat.add_const (PolyNat.const_mul PolyNat.id 4) 5))
  · exact SubpolyNat.mono (fun M => by
        show (M + 1) * Classical.choose (dryInitBudgetWithExtra_le_subpoly Psc openSz hOpen selSz hSel) M / (M + 1) ≤ _
        rw [Nat.mul_div_right _ (Nat.succ_pos M)])
      (Classical.choose_spec (dryInitBudgetWithExtra_le_subpoly Psc openSz hOpen selSz hSel)).1
  · exact (Classical.choose_spec (dryUpdateRate_le_subpoly Psc openSz hOpen selSz hSel)).1
  · exact SubpolyNat.toPolyNat dryLimbsOfM_subpoly
  · exact PolyNat.const_mul dryM0OfM_poly 8
  · exact (Classical.choose_spec (dryInitSpaceWithExtra_le_poly Psc selSz hSel)).1
  · exact (Classical.choose_spec (dryUpdateSpace_le_poly Psc openSz hOpen selSz hSel)).1

/-- `dryInnerBounds` satisfies all seven clauses of `DryEnvelopeIneqs` (`AssemblyDryRunSCEnvelope`)
for `dryInnerSizesWithSelect Psc openSz selSz`. -/
theorem dryInnerBounds_envelopeIneqs (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (hOpen : DryOpenSizeBounds openSz) (selSz : DrySelectRebuildSizes)
    (hSel : DrySelectRebuildSizeBounds selSz) :
    DryEnvelopeIneqs (dryInnerBounds Psc openSz hOpen selSz hSel)
      (dryInnerBounds_hyp Psc openSz hOpen selSz hSel)
      (dryInnerSizesWithSelect Psc openSz selSz) := by
  refine ⟨fun source J hJn hJm _ hCap _ => ?_⟩
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  exact ⟨dryLimbs_le_ofM J hJn hJm hCap1,
    dryGn_le_two_mul_m_add_two J hJn hJm hCap1,
    (Classical.choose_spec (dryInitSpaceWithExtra_le_poly Psc selSz hSel)).2 source J hJn hJm hCap1,
    (Classical.choose_spec (dryInitBudgetWithExtra_le_subpoly Psc openSz hOpen selSz hSel)).2 source J hJn hJm hCap1,
    hOpen.hCoreSpaceMono source J hJn hJm hCap1,
    (Classical.choose_spec (dryUpdateSpace_le_poly Psc openSz hOpen selSz hSel)).2 source J hJn hJm hCap1,
    (Classical.choose_spec (dryUpdateRate_le_subpoly Psc openSz hOpen selSz hSel)).2 source J hJn hJm hCap1⟩

/-- `dryInnerBounds` satisfies `hNames` (`nfMax + 2 * I.m ≤ B.names I.m`) unconditionally. -/
theorem dryInnerBounds_hNames (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (hOpen : DryOpenSizeBounds openSz) (selSz : DrySelectRebuildSizes)
    (hSel : DrySelectRebuildSizeBounds selSz) :
    ForAllDryInputs dryWitnessUsed
      (dryAllocCoeffFull (dryInnerBounds Psc openSz hOpen selSz hSel)
        (dryInnerBounds_hyp Psc openSz hOpen selSz hSel))
      (dryAllocDeg (dryInnerBounds Psc openSz hOpen selSz hSel)
        (dryInnerBounds_hyp Psc openSz hOpen selSz hSel))
      fun _source J _hw =>
        let I := solverConnectedAugmented J
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * I.m ≤
          (dryInnerBounds Psc openSz hOpen selSz hSel).names I.m := by
  intro _source J _ _ _ _ _
  have hNf := dryNfMax_le_two_mul_M0 J
  have hMle : (solverConnectedAugmented J).m ≤ dryM0OfM (solverConnectedAugmented J).m := le_max_left _ _
  change _ ≤ 8 * dryM0OfM (solverConnectedAugmented J).m
  dsimp only at hNf
  omega

/-- Unconditional discharge of `OrdSolverContractEnvelopeFullCredit` at `dryInnerBounds` and
`dryInnerSizesWithSelect` via `drySC_hEnv_of_ineqs`. -/
theorem dryInnerBounds_hEnv_proved (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (hOpen : DryOpenSizeBounds openSz) (selSz : DrySelectRebuildSizes)
    (hSel : DrySelectRebuildSizeBounds selSz) :
    ForAllDryInputs dryWitnessUsed
      (dryAllocCoeffFull (dryInnerBounds Psc openSz hOpen selSz hSel)
        (dryInnerBounds_hyp Psc openSz hOpen selSz hSel))
      (dryAllocDeg (dryInnerBounds Psc openSz hOpen selSz hSel)
        (dryInnerBounds_hyp Psc openSz hOpen selSz hSel))
      fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let Rcore := drySCRep Psc
          (dryAllocCoeffFull (dryInnerBounds Psc openSz hOpen selSz hSel)
            (dryInnerBounds_hyp Psc openSz hOpen selSz hSel))
          (dryAllocDeg (dryInnerBounds Psc openSz hOpen selSz hSel)
            (dryInnerBounds_hyp Psc openSz hOpen selSz hSel))
          source J hw
        let s := dryInnerSizesWithSelect Psc openSz selSz source J
        OrdSolverContractEnvelopeFullCredit F cfg (namedInstance I) I.m V ⌈cfg.Ψ⌉₊ k
          (k + Num.IPM.alphaExponent I.m V + 10)
          (s.initSpace' + initWiredExtraSpace cfg (namedInstance I))
          (s.initFixed + initWiredExtraCost cfg (namedInstance I))
          (6 + s.selectSpace + s.evalSpace) (s.selectBudget + s.evalBudget + 90)
          (max s.termSpace s.deepSpace) (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220)
          s.maxEdges s.maxPaths s.toolMul s.treeMul
          (fun uLen => cfg.P.d + (8 * uLen + 1) + s.coreSpace uLen)
          (fun uLen => s.coreFixed uLen + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 120 * uLen +
            62 * (cfg.P.d + 1) + 240)
          Rcore (dryInnerBounds Psc openSz hOpen selSz hSel).cycleRate
          ((dryInnerBounds Psc openSz hOpen selSz hSel).cycleAllocation I.n I.m) :=
  drySC_hEnv_of_ineqs Psc (dryInnerBounds Psc openSz hOpen selSz hSel)
    (dryInnerBounds_hyp Psc openSz hOpen selSz hSel)
    (dryInnerSizesWithSelect Psc openSz selSz)
    (dryInnerBounds_envelopeIneqs Psc openSz hOpen selSz hSel)
    (dryInnerBounds_hNames Psc openSz hOpen selSz hSel)

end MinCostFlow.Final.DryRun

end
