module

public import MinCostFlow.Final.AssemblyDryRunSCInnerSizes
public import MinCostFlow.Final.AssemblyDryRunSCInnerStepCapAsymp
public import MinCostFlow.Final.AssemblyDryRunSCDeepAsymp
import MinCostFlow.Final.AssemblyDryRunSCAsymp
import Mathlib.Tactic

/-!
# Asymptotic `PolyNat` and `SubpolyNat` bounds for `dryInnerCoreSizes` (`AssemblyDryRunSCInnerAsymp`)

Proves `DryCoreOpenSizeBounds (dryInnerCoreSizes Psc)` unconditionally, building on
`AssemblyDryRunSCInnerStepCapAsymp` (`dryCfgK_le_subpoly`, `dryUpdateCoreStepRatioPow_le_subpoly`,
`dryBranchBCaps_le_poly`):

* `dryInnerCoreSpace_le_poly`: `dryInnerCoreSpace Psc J (2 * I.m)` is `PolyNat` in `I.m`.
* `dryInnerCoreFixed_le_subpoly`: `dryInnerCoreFixed Psc J u ≤ fRho0 I.m + fRho1 I.m * u` with
  `SubpolyNat fRho0, fRho1`.
* `dryInnerCoreMul_le_subpoly`: `dryInnerCoreToolMul Psc J` and `dryInnerCoreTreeMul J` are
  `SubpolyNat` in `I.m`.
* `dryInnerCoreSizeBounds`: bundles all four fields into `DryCoreOpenSizeBounds (dryInnerCoreSizes Psc)`.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. `PolyNat` bound on `dryInnerCoreSpace` -/

private theorem dryDeepIntCapMax_le_eight_M0 (J : Circulation) :
    dryDeepIntCapMax J ≤ 8 * dryM0OfM (solverConnectedAugmented J).m := by
  set I := solverConnectedAugmented J
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  unfold dryDeepIntCapMax Ordered.alg2NameBase intRebuildThreshold
  dsimp only
  have hM0ge : I.m ≤ cfg.P.M₀ := le_max_left _ _
  have hThr : cfg.P.M₀ / (cfg.P.k ^ (0 + 1) * Nat.clog 2 (cfg.N₀ + 2) ^ 2) ≤ cfg.P.M₀ :=
    Nat.div_le_self _ _
  have hM0_2 : 2 ≤ cfg.P.M₀ :=
    (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed).trans (le_max_right _ _)
  have hBase' : max ((namedInstance I).E.sup id + 1) cfg.P.M₀ ≤ cfg.P.M₀ := by
    apply max_le _ le_rfl
    have hSup' : (namedInstance I).E.sup id + 1 ≤ max 1 I.m := by
      rcases Nat.eq_zero_or_pos I.m with h0 | hpos
      · have : (namedInstance I).E = ∅ := by simp [namedInstance, h0]
        rw [this]; simp
      · have : (namedInstance I).E.sup id ≤ I.m - 1 :=
          Finset.sup_le fun e he => by
            change e ≤ I.m - 1
            simp [namedInstance] at he; omega
        omega
    omega
  change 2 * (max ((namedInstance I).E.sup id + 1) cfg.P.M₀ +
    cfg.P.M₀ / (cfg.P.k ^ (0 + 1) * Nat.clog 2 (cfg.N₀ + 2) ^ 2) + 2 * I.m) ≤ 8 * cfg.P.M₀
  omega

/-- `dryInnerCoreSpace Psc J (2 * I.m)` is uniformly bounded by a `PolyNat` function of `I.m`. -/
theorem dryInnerCoreSpace_le_poly (Psc : DrySparseCorePieces) :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        dryInnerCoreSpace Psc J (2 * (solverConnectedAugmented J).m) ≤
          f (solverConnectedAugmented J).m := by
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  obtain ⟨fLM, hfLMSub, hfLM⟩ := dryLevelM_le_subpoly
  obtain ⟨fLvl, hfLvlP, hLvl⟩ := dryDeepLevelSpace_le_poly Psc
  obtain ⟨fLast, hfLastP, hLast⟩ := dryLastSpace_le_poly
  obtain ⟨fUL, fBW, fEW, hfULP, hfBWP, hfEWP, hCaps⟩ := dryBranchBCaps_le_poly Psc
  let cLw : ℕ := dryCapExp + sparseCoreReadout2LimbConst
  let fL : ℕ → ℕ := dryLimbsOfM
  have hfLP : PolyNat fL := SubpolyNat.toPolyNat dryLimbsOfM_subpoly
  have hfdP : PolyNat fd := SubpolyNat.toPolyNat hfdSub
  let fM : ℕ → ℕ := fun M => (M + 1) * fLM M
  have hfMP : PolyNat fM := PolyNat.mul (PolyNat.add_const PolyNat.id 1) (SubpolyNat.toPolyNat hfLMSub)
  let fCap : ℕ → ℕ := fun M => 12 * dryM0OfM M + 4
  have hfCapP : PolyNat fCap := PolyNat.add_const (PolyNat.const_mul dryM0OfM_poly 12) 4
  let fInt : ℕ → ℕ := fun M => 8 * dryM0OfM M
  have hfIntP : PolyNat fInt := PolyNat.const_mul dryM0OfM_poly 8
  let fFor : ℕ → ℕ := fun M => (fd M + 1) * (4 * M + 4)
  have hfForP : PolyNat fFor :=
    PolyNat.mul (PolyNat.add_const hfdP 1) (PolyNat.add_const (PolyNat.const_mul PolyNat.id 4) 4)
  let fFCap : ℕ → ℕ := fun M => 11 * fCap M + 5 + 18 * (fCap M) ^ 2
  have hfFCapP : PolyNat fFCap :=
    PolyNat.add (PolyNat.add_const (PolyNat.const_mul hfCapP 11) 5)
      (PolyNat.const_mul (PolyNat.pow hfCapP 2) 18)
  let fSyncSp : ℕ → ℕ := fun M => 170 * fL M + 530
  have hfSyncSpP : PolyNat fSyncSp := PolyNat.add_const (PolyNat.const_mul hfLP 170) 530
  let fRefSp : ℕ → ℕ := fun M => 100 * (fL M) ^ 2 + 100 * fL M + 10
  have hfRefSpP : PolyNat fRefSp :=
    PolyNat.add_const (PolyNat.add (PolyNat.const_mul (PolyNat.pow hfLP 2) 100)
      (PolyNat.const_mul hfLP 100)) 10
  let fLw : ℕ → ℕ := fun M => fL M + cLw * (fM M + 4 * dryM0OfM M + 3)
  have hfLwP : PolyNat fLw :=
    PolyNat.add hfLP (PolyNat.const_mul (PolyNat.add_const (PolyNat.add hfMP (PolyNat.const_mul dryM0OfM_poly 4)) 3) cLw)
  let fEdgeSp : ℕ → ℕ := fun M => 30 * (fLw M) ^ 2 + 30 * fLw M + 2
  have hfEdgeSpP : PolyNat fEdgeSp :=
    PolyNat.add_const (PolyNat.add (PolyNat.const_mul (PolyNat.pow hfLwP 2) 30)
      (PolyNat.const_mul hfLwP 30)) 2
  have hOp0P : PolyNat (fun M => drySCOp0Bound Psc M (fBW M) (fEW M)) :=
    drySCOp0Bound_poly Psc hfBWP hfEWP
  let fStep : ℕ → ℕ := fun M =>
    3 * drySCOp0Bound Psc M (fBW M) (fEW M) + 7 + fUL M * fEdgeSp M + 2 * fUL M
  have hfStepP : PolyNat fStep :=
    PolyNat.add
      (PolyNat.add (PolyNat.add_const (PolyNat.const_mul hOp0P 3) 7) (PolyNat.mul hfULP hfEdgeSpP))
      (PolyNat.const_mul hfULP 2)
  let fTerm : ℕ → ℕ := fun M =>
    16 * fCap M + 10 + fCap M * fL M + fM M * fEdgeSp M +
      (8 * dryM0OfM M + 2 + 2 * fM M) + fLast M + 7
  have hfTermP : PolyNat fTerm :=
    PolyNat.add_const
      (PolyNat.add
        (PolyNat.add
          (PolyNat.add
            (PolyNat.add (PolyNat.add_const (PolyNat.const_mul hfCapP 16) 10)
              (PolyNat.mul hfCapP hfLP))
            (PolyNat.mul hfMP hfEdgeSpP))
          (PolyNat.add (PolyNat.add_const (PolyNat.const_mul dryM0OfM_poly 8) 2)
            (PolyNat.const_mul hfMP 2)))
        hfLastP) 7
  let fComp : ℕ → ℕ := fun M =>
    fInt M * fL M + 3 * fInt M + 2 * (28 * dryM0OfM M + 4 + 9 * fInt M)
  have hfCompP : PolyNat fComp :=
    PolyNat.add (PolyNat.add (PolyNat.mul hfIntP hfLP) (PolyNat.const_mul hfIntP 3))
      (PolyNat.const_mul
        (PolyNat.add (PolyNat.add_const (PolyNat.const_mul dryM0OfM_poly 28) 4)
          (PolyNat.const_mul hfIntP 9)) 2)
  let fA : ℕ → ℕ := fun M =>
    25 * fd M + 10 * fInt M + 2 * (fFor M * (fSyncSp M + 2)) +
      3 * fL M + 2 * M * fRefSp M + fComp M + 16 * dryM0OfM M +
      fd M * fLvl M + fLast M + 20
  let fB : ℕ → ℕ := fun M =>
    30 * fd M + 14 * M + 2 * M * (fSyncSp M + fRefSp M) +
      3 * fL M + fd M * fStep M + 8 * dryM0OfM M + 2 * fM M +
      fd M * fLvl M + fLast M + fTerm M +
      3 * fInt M + 6 * fFor M + 2 * (fFor M * fSyncSp M) + fFCap M + 30
  have hfAP : PolyNat fA := by
    have h1 := PolyNat.add (PolyNat.add (PolyNat.const_mul hfdP 25) (PolyNat.const_mul hfIntP 10))
      (PolyNat.const_mul (PolyNat.mul hfForP (PolyNat.add_const hfSyncSpP 2)) 2)
    have h2 := PolyNat.add (PolyNat.const_mul hfLP 3)
      (PolyNat.mul (PolyNat.const_mul PolyNat.id 2) hfRefSpP)
    have h3 := PolyNat.add (PolyNat.add hfCompP (PolyNat.const_mul dryM0OfM_poly 16))
      (PolyNat.add (PolyNat.mul hfdP hfLvlP) hfLastP)
    exact PolyNat.mono (fun M => by dsimp only [fA]; omega)
      (PolyNat.add_const (PolyNat.add (PolyNat.add h1 h2) h3) 20)
  have hfBP : PolyNat fB := by
    have h1 := PolyNat.add (PolyNat.add (PolyNat.const_mul hfdP 30) (PolyNat.const_mul PolyNat.id 14))
      (PolyNat.mul (PolyNat.const_mul PolyNat.id 2) (PolyNat.add hfSyncSpP hfRefSpP))
    have h2 := PolyNat.add (PolyNat.add (PolyNat.const_mul hfLP 3) (PolyNat.mul hfdP hfStepP))
      (PolyNat.add (PolyNat.const_mul dryM0OfM_poly 8) (PolyNat.const_mul hfMP 2))
    have h3 := PolyNat.add (PolyNat.add (PolyNat.mul hfdP hfLvlP) hfLastP)
      (PolyNat.add hfTermP (PolyNat.add (PolyNat.const_mul hfIntP 3) hfFCapP))
    have h4 := PolyNat.add (PolyNat.const_mul hfForP 6)
      (PolyNat.const_mul (PolyNat.mul hfForP hfSyncSpP) 2)
    exact PolyNat.mono (fun M => by dsimp only [fB]; omega)
      (PolyNat.add_const (PolyNat.add (PolyNat.add (PolyNat.add h1 h2) h3) h4) 30)
  refine ⟨fun M => fA M + fB M, PolyNat.add hfAP hfBP, fun J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hL : L ≤ fL I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hd : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
  have hCapEq : dryCapLimit dryWitnessUsed J = fCap I.m := rfl
  have hN0Eq : cfg.N₀ = 4 * dryM0OfM I.m := rfl
  have hInt : dryDeepIntCapMax J ≤ fInt I.m := dryDeepIntCapMax_le_eight_M0 J
  have hInLe : I.n ≤ 2 * I.m + 2 := by
    have hIn : I.n = J.n + 1 := by
      simp [I, solverConnectedAugmented, connectedInitialInstance, instanceOfArrays,
        Circulation.toInstance]
    have hJmLe : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCap).1
    omega
  have hFor : dryDeepForestEdgeCap J ≤ fFor I.m := by
    unfold dryDeepForestEdgeCap; dsimp only [fFor]
    calc 2 * (cfg.P.d + 1) * I.n = (cfg.P.d + 1) * (2 * I.n) := by ring
      _ ≤ (fd I.m + 1) * (4 * I.m + 4) := Nat.mul_le_mul (by omega) (by omega)
  have hFCap : dryDeepFCap J ≤ fFCap I.m := by
    unfold dryDeepFCap dynGraphSize; dsimp only [fFCap, fCap]
    have : dryCapLimit dryWitnessUsed J = 12 * dryM0OfM I.m + 4 := rfl
    rw [this]; omega
  have hSync : wireTreeSyncEditSpace L ≤ fSyncSp I.m := by
    unfold wireTreeSyncEditSpace LinkCut.PathProg.treeLimbs; dsimp only [fSyncSp]; omega
  have hRef : wireRefreshOneSpace L ≤ fRefSp I.m := by
    unfold wireRefreshOneSpace Num.fixedDivideSpace Num.integerDivideSpace Num.unsignedDivideSpace
    dsimp only [fRefSp]
    have hsq := Nat.pow_le_pow_left hL 2
    nlinarith only [hL, hsq]
  have hLvlSum : (Finset.range cfg.P.d).sum (dryDeepLevelSpace Psc J) ≤ fd I.m * fLvl I.m := by
    calc _ ≤ ∑ _ ∈ Finset.range cfg.P.d, fLvl I.m :=
          Finset.sum_le_sum fun j hj => hLvl J hJn hJm hCap j (Finset.mem_range.mp hj)
      _ = cfg.P.d * fLvl I.m := by simp
      _ ≤ fd I.m * fLvl I.m := Nat.mul_le_mul_right _ hd
  have hLast' : dryLastSpace J ≤ fLast I.m := hLast J hJn hJm hCap
  have hLwLe : ∀ j ≤ cfg.P.d,
      ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P j) cfg.N₀ ≤ fLw I.m := by
    intro j hj
    have hMj : levelM cfg.TP cfg.P j ≤ fM I.m := hfLM J hJn hJm hCap j hj
    have hlg := Nat.log_le_self 2 (levelM cfg.TP cfg.P j + cfg.N₀ + 2)
    unfold ordLevelLwMax; dsimp only [fLw, cLw]
    rw [hN0Eq] at hlg ⊢
    exact Nat.add_le_add hL (Nat.mul_le_mul_left cLw (by omega))
  have hEdgeLe : ∀ j ≤ cfg.P.d,
      wireCoreLenEdgeSpace (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P j) cfg.N₀) ≤
        fEdgeSp I.m := by
    intro j hj
    have hlw := hLwLe j hj
    have hsq := Nat.pow_le_pow_left hlw 2
    unfold wireCoreLenEdgeSpace Num.integerDivideSpace Num.unsignedDivideSpace
    dsimp only [fEdgeSp]
    nlinarith only [hlw, hsq]
  have hStepSum : (Finset.range cfg.P.d).sum
      (fun j => dryInnerCoreUpdStepSpace Psc J j (2 * I.m)) ≤ fd I.m * fStep I.m := by
    calc _ ≤ ∑ _ ∈ Finset.range cfg.P.d, fStep I.m := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := Finset.mem_range.mp hj
          obtain ⟨hULj, hBWj, hEWj⟩ := hCaps J hJn hJm hCap j hj'.le
          obtain ⟨hULj1, _, _⟩ := hCaps J hJn hJm hCap (j + 1) hj'
          have hES := hEdgeLe j hj'.le
          have hop0 := drySCOp0Bound_mono Psc (M := I.m) hBWj hEWj
          have hmul := Nat.mul_le_mul hULj1 hES
          unfold dryInnerCoreUpdStepSpace
          dsimp only [I, V, k, L, cfg, fStep] at hop0 hmul hULj hULj1 ⊢
          linarith only [hop0, hmul, hULj, hULj1]
      _ = cfg.P.d * fStep I.m := by simp
      _ ≤ fd I.m * fStep I.m := Nat.mul_le_mul_right _ hd
  have hTermLe : dryInnerCoreTermUpdSpace J ≤ fTerm I.m := by
    have hMd : levelM cfg.TP cfg.P cfg.P.d ≤ fM I.m := hfLM J hJn hJm hCap cfg.P.d le_rfl
    have hES := hEdgeLe (cfg.P.d - 1) (Nat.sub_le _ _)
    have h1 := Nat.mul_le_mul_left (fCap I.m) hL
    have h2 := Nat.mul_le_mul hMd hES
    change 1 + (4 + 7 * fCap I.m + 9 * fCap I.m) + 5 + fCap I.m * L +
      levelM cfg.TP cfg.P cfg.P.d *
        wireCoreLenEdgeSpace (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀) +
      (2 + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P cfg.P.d) + dryLastSpace J + 7 ≤ fTerm I.m
    rw [hN0Eq] at h2 ⊢
    dsimp only [fTerm]
    linarith only [h1, h2, hMd, hLast']
  have hSpaceA : dryInnerCoreSpaceA Psc J (2 * I.m) ≤ fA I.m := by
    have hComp : wireCompactLevel0Space cfg.N₀ (dryDeepIntCapMax J) L (dryDeepIntCapMax J) ≤
        fComp I.m := by
      unfold wireCompactLevel0Space dynGraphSize; dsimp only [fComp]; rw [hN0Eq]
      have h1 := Nat.mul_le_mul hInt hL; linarith only [h1, hInt]
    have hForSync : dryDeepForestEdgeCap J * (2 + wireTreeSyncEditSpace L) ≤
        fFor I.m * (fSyncSp I.m + 2) := Nat.mul_le_mul hFor (by linarith only [hSync])
    have hRefU := Nat.mul_le_mul_left (2 * I.m) hRef
    unfold dryInnerCoreSpaceA
    dsimp only [I, V, k, L, cfg, fA] at hd hInt hForSync hL hRefU hComp hLvlSum hLast' hN0Eq ⊢
    rw [hN0Eq] at hComp ⊢
    linarith only [hd, hInt, hForSync, hL, hRefU, hComp, hLvlSum, hLast']
  have hSpaceB : dryInnerCoreSpaceB Psc J (2 * I.m) ≤ fB I.m := by
    have hM0 : levelM cfg.TP cfg.P 0 ≤ fM I.m := hfLM J hJn hJm hCap 0 (Nat.zero_le _)
    have hSyncU := Nat.mul_le_mul_left (2 * I.m) hSync
    have hRefU := Nat.mul_le_mul_left (2 * I.m) hRef
    have hForSync := Nat.mul_le_mul hFor hSync
    have hdistr : 2 * I.m * (fSyncSp I.m + fRefSp I.m) =
        2 * I.m * fSyncSp I.m + 2 * I.m * fRefSp I.m := by ring
    unfold dryInnerCoreSpaceB
    dsimp only [I, V, k, L, cfg, fB] at *
    rw [hN0Eq]
    linarith only [hd, hM0, hSyncU, hL, hRefU, hStepSum, hFCap, hLvlSum, hLast', hTermLe, hInt,
      hFor, hForSync, hdistr]
  unfold dryInnerCoreSpace
  exact max_le (hSpaceA.trans (Nat.le_add_right _ _)) (hSpaceB.trans (Nat.le_add_left _ _))

/-! ## 3. `SubpolyNat` bounds on `dryInnerCoreFixed`, `dryInnerCoreToolMul`, `dryInnerCoreTreeMul` -/

private theorem dryInnerCoreCostPieces_le_subpoly (Psc : DrySparseCorePieces) :
    let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
    ∃ (fd fL fB0 fDrain fSyncC fEdgeC fRdTerm fLast : ℕ → ℕ),
      SubpolyNat fd ∧ SubpolyNat fL ∧ SubpolyNat fB0 ∧ SubpolyNat fDrain ∧
      SubpolyNat fSyncC ∧ SubpolyNat fEdgeC ∧ SubpolyNat fRdTerm ∧ SubpolyNat fLast ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let L := ipmQualityLimbs I.m V k
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let B0 := SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀
        let Lw0 := ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀
        let Rpow := (updateCoreStepRatio (drySCEdMul Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed))
          (levelM cfg.TP cfg.P 0) cfg.N₀) ^ cfg.P.d
        cfg.P.d ≤ fd I.m ∧ L ≤ fL I.m ∧ B0 ≤ fB0 I.m ∧
        detectOffTreeDrainUnit L ≤ fDrain I.m ∧
        wireTreeSyncEditCost L (detectOffTreeDrainUnit L) ≤ fSyncC I.m ∧
        wireCoreLenEdgeCost Lw0 ≤ fEdgeC I.m ∧
        cfg.P.d * Rpow * (PscP.mul * (cfg.P.k + 1) * B0 + 730) +
          (670 + 155 * (cfg.P.d + 1)) * Rpow ≤ fRdTerm I.m ∧
        dryLastMult J ≤ fLast I.m := by
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  obtain ⟨fk, hfkSub, hfk⟩ := dryCfgK_le_subpoly
  obtain ⟨fLM, hfLMSub, hfLM⟩ := dryLevelM_le_subpoly
  obtain ⟨fLast, hfLastSub, hfLast⟩ := dryLastMult_le_subpoly
  obtain ⟨fRd, hfRdSub, hfRd⟩ := dryUpdateCoreStepRatioPow_le_subpoly Psc
  let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
  let cLw := dryCapExp + sparseCoreReadout2LimbConst
  let fL : ℕ → ℕ := dryLimbsOfM
  have hfLSub : SubpolyNat fL := dryLimbsOfM_subpoly
  let fArgPoly : PolyNat (fun M => (M + 1) * fLM M + 4 * dryM0OfM M) :=
    PolyNat.add (PolyNat.mul (PolyNat.add_const PolyNat.id 1) (SubpolyNat.toPolyNat hfLMSub))
      (PolyNat.const_mul dryM0OfM_poly 4)
  let fB0 : ℕ → ℕ := fun M => (Nat.log 2 (((M + 1) * fLM M + 4 * dryM0OfM M) + 2) + 1) ^ 2
  have hfB0Sub : SubpolyNat fB0 := SubpolyNat.pow (subpolyNat_log_of_poly fArgPoly) 2
  let fLw : ℕ → ℕ := fun M => fL M + cLw * (Nat.log 2 (((M + 1) * fLM M + 4 * dryM0OfM M) + 2) + 1)
  have hfLwSub : SubpolyNat fLw :=
    SubpolyNat.add hfLSub (SubpolyNat.const_mul (subpolyNat_log_of_poly fArgPoly) cLw)
  let fDrain : ℕ → ℕ := fun M => 87 * fL M + 220
  have hfDrainSub : SubpolyNat fDrain := SubpolyNat.add_const (SubpolyNat.const_mul hfLSub 87) 220
  let fSyncC : ℕ → ℕ := fun M =>
    50 * (LinkCut.PathProg.pathC * (fL M + 1) ^ 2) * (4 * fL M + 1) + 160 * fL M + fDrain M + 500
  have hfSyncCSub : SubpolyNat fSyncC :=
    SubpolyNat.add_const
      (SubpolyNat.add
        (SubpolyNat.add
          (SubpolyNat.mul
            (SubpolyNat.const_mul (SubpolyNat.const_mul (SubpolyNat.pow (SubpolyNat.add_const hfLSub 1) 2)
              LinkCut.PathProg.pathC) 50)
            (SubpolyNat.add_const (SubpolyNat.const_mul hfLSub 4) 1))
          (SubpolyNat.const_mul hfLSub 160))
        hfDrainSub) 500
  let fEdgeC : ℕ → ℕ := fun M => 1400 * (fLw M) ^ 2 + 2100 * fLw M + 850
  have hfEdgeCSub : SubpolyNat fEdgeC :=
    SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.const_mul (SubpolyNat.pow hfLwSub 2) 1400)
      (SubpolyNat.const_mul hfLwSub 2100)) 850
  let fStepMul : ℕ → ℕ := fun M => PscP.mul * (fk M + 1) * fB0 M + 730
  have hfStepMulSub : SubpolyNat fStepMul :=
    SubpolyNat.add_const
      (SubpolyNat.mul (SubpolyNat.const_mul (SubpolyNat.add_const hfkSub 1) PscP.mul) hfB0Sub) 730
  let fRdTerm : ℕ → ℕ := fun M => fd M * fRd M * fStepMul M + (670 + 155 * (fd M + 1)) * fRd M
  have hfRdTermSub : SubpolyNat fRdTerm :=
    SubpolyNat.add
      (SubpolyNat.mul (SubpolyNat.mul hfdSub hfRdSub) hfStepMulSub)
      (SubpolyNat.mul (SubpolyNat.mono (fun M => by omega)
        (SubpolyNat.add_const (SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) 155) 670)) hfRdSub)
  refine ⟨fd, fL, fB0, fDrain, fSyncC, fEdgeC, fRdTerm, fLast,
    hfdSub, hfLSub, hfB0Sub, hfDrainSub, hfSyncCSub, hfEdgeCSub, hfRdTermSub, hfLastSub,
    fun J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  set B0 := SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀
  set Lw0 := ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀
  set Rpow := (updateCoreStepRatio (drySCEdMul Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed))
    (levelM cfg.TP cfg.P 0) cfg.N₀) ^ cfg.P.d
  have hL : L ≤ fL I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hd : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
  have hk : cfg.P.k ≤ fk I.m := hfk J hJn hJm hCap
  have hM0 : levelM cfg.TP cfg.P 0 ≤ (I.m + 1) * fLM I.m := hfLM J hJn hJm hCap 0 (Nat.zero_le _)
  have hN0 : cfg.N₀ = 4 * dryM0OfM I.m := rfl
  have hRd : Rpow ≤ fRd I.m := hfRd J hJn hJm hCap
  have hB0 : B0 ≤ fB0 I.m := by
    dsimp only [B0, fB0]; unfold SparseCore.bundleLogFactor
    exact Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right (b := 2) (by omega)) 1) 2
  have hLw : Lw0 ≤ fLw I.m := by
    dsimp only [Lw0, fLw, cLw]; unfold ordLevelLwMax
    exact Nat.add_le_add hL (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.log_mono_right (b := 2) (by omega)) 1))
  have hDrain : detectOffTreeDrainUnit L ≤ fDrain I.m := by
    unfold detectOffTreeDrainUnit; dsimp only [fDrain]; omega
  have hSyncC : wireTreeSyncEditCost L (detectOffTreeDrainUnit L) ≤ fSyncC I.m := by
    unfold wireTreeSyncEditCost; dsimp only [fSyncC]
    have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hL 1) 2
    have h1 := Nat.mul_le_mul (Nat.mul_le_mul_left 50 (Nat.mul_le_mul_left LinkCut.PathProg.pathC hsq))
      (show 4 * L + 1 ≤ 4 * fL I.m + 1 by omega)
    linarith only [h1, hL, hDrain]
  have hEdgeC : wireCoreLenEdgeCost Lw0 ≤ fEdgeC I.m := by
    unfold wireCoreLenEdgeCost; dsimp only [fEdgeC]
    have hsq := Nat.pow_le_pow_left hLw 2; nlinarith only [hLw, hsq]
  have hStepMul : PscP.mul * (cfg.P.k + 1) * B0 + 730 ≤ fStepMul I.m := by
    dsimp only [fStepMul]
    have h1 := Nat.mul_le_mul (Nat.mul_le_mul_left PscP.mul (Nat.add_le_add_right hk 1)) hB0
    linarith only [h1]
  have hRdTerm : cfg.P.d * Rpow * (PscP.mul * (cfg.P.k + 1) * B0 + 730) +
      (670 + 155 * (cfg.P.d + 1)) * Rpow ≤ fRdTerm I.m := by
    dsimp only [fRdTerm]
    have h1 := Nat.mul_le_mul (Nat.mul_le_mul hd hRd) hStepMul
    have h2 := Nat.mul_le_mul (show 670 + 155 * (cfg.P.d + 1) ≤ 670 + 155 * (fd I.m + 1) by omega) hRd
    linarith only [h1, h2]
  exact ⟨hd, hL, hB0, hDrain, hSyncC, hEdgeC, hRdTerm, hfLast J hJn hJm hCap⟩

/-- `dryInnerCoreFixed Psc J u ≤ fRho0 I.m + fRho1 I.m * u` with `SubpolyNat fRho0, fRho1`. -/
theorem dryInnerCoreFixed_le_subpoly (Psc : DrySparseCorePieces) :
    ∃ (fRho0 fRho1 : ℕ → ℕ), SubpolyNat fRho0 ∧ SubpolyNat fRho1 ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        ∀ u, dryInnerCoreFixed Psc J u ≤
          fRho0 (solverConnectedAugmented J).m + fRho1 (solverConnectedAugmented J).m * u := by
  obtain ⟨fd, fL, fB0, fDrain, fSyncC, fEdgeC, fRdTerm, fLast,
    hfdSub, hfLSub, hfB0Sub, hfDrainSub, hfSyncCSub, hfEdgeCSub, hfRdTermSub, hfLastSub, hP⟩ :=
    dryInnerCoreCostPieces_le_subpoly Psc
  let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
  let mThresh := concreteEdgeThresholdWithLast dryWitnessUsed
  let fMd : ℕ → ℕ := fun M => 2 ^ dryKOfM M
  have hfMdSub : SubpolyNat fMd := subpolyNat_two_pow_dryKOfM
  let fRefC : ℕ → ℕ := fun M => 2700 * (fL M) ^ 2 + 3350 * fL M + 1300
  have hfRefCSub : SubpolyNat fRefC :=
    SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.const_mul (SubpolyNat.pow hfLSub 2) 2700)
      (SubpolyNat.const_mul hfLSub 3350)) 1300
  let fRho1 : ℕ → ℕ := fun M =>
    fRefC M + fSyncC M + 17 * fL M + fDrain M + 3200 + 14 * fRdTerm M
  have hfRho1Sub : SubpolyNat fRho1 :=
    SubpolyNat.add
      (SubpolyNat.add_const
        (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add hfRefCSub hfSyncCSub)
          (SubpolyNat.const_mul hfLSub 17)) hfDrainSub) 3200)
      (SubpolyNat.const_mul hfRdTermSub 14)
  let fTermFix : ℕ → ℕ := fun M =>
    2 * PscP.readout + (290 * fMd M + 240) + fMd M * (fEdgeC M + 30) +
      PscP.mul * (4 * fMd M + 4) * fB0 M + fLast M + 310 * fMd M + 1200
  have hfTermFixSub : SubpolyNat fTermFix := by
    have h1 := SubpolyNat.add_const (SubpolyNat.const_mul hfMdSub 290) (2 * PscP.readout + 240)
    have h2 := SubpolyNat.mul hfMdSub (SubpolyNat.add_const hfEdgeCSub 30)
    have h3 := SubpolyNat.mul
      (SubpolyNat.const_mul (SubpolyNat.add_const (SubpolyNat.const_mul hfMdSub 4) 4) PscP.mul) hfB0Sub
    have h4 := SubpolyNat.add_const (SubpolyNat.add hfLastSub (SubpolyNat.const_mul hfMdSub 310)) 1200
    exact SubpolyNat.mono (fun M => by dsimp only [fTermFix]; omega)
      (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add h1 h2) h3) h4)
  let fRho0 : ℕ → ℕ := fun M =>
    3 * fRdTerm M +
      fd M * (5 * PscP.mul + 4 * PscP.mul * fB0 M + 5 * PscP.readout + 2000) +
      4 * PscP.mul * fB0 M + 2 * PscP.readout + 71 * fL M + 600 * (fd M + 1) +
      fTermFix M + 510 * mThresh + 8500
  have hfRho0Sub : SubpolyNat fRho0 := by
    have h1 := SubpolyNat.const_mul hfRdTermSub 3
    have h2In : SubpolyNat (fun M => 5 * PscP.mul + 4 * PscP.mul * fB0 M + 5 * PscP.readout + 2000) :=
      SubpolyNat.mono (fun M => by omega)
        (SubpolyNat.add_const (SubpolyNat.const_mul hfB0Sub (4 * PscP.mul))
          (5 * PscP.mul + 5 * PscP.readout + 2000))
    have h2 := SubpolyNat.mul hfdSub h2In
    have h3 := SubpolyNat.add
      (SubpolyNat.add (SubpolyNat.const_mul hfB0Sub (4 * PscP.mul)) (SubpolyNat.const_mul hfLSub 71))
      (SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) 600)
    exact SubpolyNat.mono (fun M => by dsimp only [fRho0]; omega)
      (SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add h1 h2) h3) hfTermFixSub)
        (2 * PscP.readout + 510 * mThresh + 8500))
  refine ⟨fRho0, fRho1, hfRho0Sub, hfRho1Sub, fun J hJn hJm hCap u => ?_⟩
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let B0 := SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀
  let Lw0 := ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀
  let Rpow := (updateCoreStepRatio (drySCEdMul Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed))
    (levelM cfg.TP cfg.P 0) cfg.N₀) ^ cfg.P.d
  obtain ⟨hd, hL, hB0, hDrain, hSyncC, hEdgeC, hRdTerm, hLast'⟩ := hP J hJn hJm hCap
  have hMd : levelM cfg.TP cfg.P cfg.P.d ≤ fMd I.m := dryLevelMd_le_two_pow_dryKOfM J hJn hJm hCap
  have hRefC : wireRefreshOneCost L ≤ fRefC I.m := by
    unfold wireRefreshOneCost; dsimp only [fRefC, I, V, k, L] at hL ⊢
    have hsq := Nat.pow_le_pow_left hL 2; nlinarith only [hL, hsq]
  have hTermFix :
      2 * PscP.readout + (290 * levelM cfg.TP cfg.P cfg.P.d + 240) +
        levelM cfg.TP cfg.P cfg.P.d * (wireCoreLenEdgeCost Lw0 + 30) +
        PscP.mul * (4 * levelM cfg.TP cfg.P cfg.P.d + 4) * B0 +
        dryLastMult J + 310 * levelM cfg.TP cfg.P cfg.P.d + 1200 ≤ fTermFix I.m := by
    dsimp only [fTermFix, I, V, k, L, cfg, B0, Lw0] at hMd hEdgeC hB0 hLast' ⊢
    have h1 := Nat.mul_le_mul hMd (Nat.add_le_add_right hEdgeC 30)
    have h2 := Nat.mul_le_mul (Nat.mul_le_mul_left PscP.mul
      (show 4 * levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
        (concreteCirculationCfgWithLast dryWitnessUsed J).P
        (concreteCirculationCfgWithLast dryWitnessUsed J).P.d + 4 ≤
        4 * fMd (solverConnectedAugmented J).m + 4 by omega)) hB0
    linarith only [hMd, h1, h2, hLast']
  have hB04 : 4 * PscP.mul * B0 ≤ 4 * PscP.mul * fB0 I.m := Nat.mul_le_mul_left _ hB0
  have hDterm : cfg.P.d * (5 * PscP.mul + 4 * PscP.mul * B0 + 5 * PscP.readout + 2000) ≤
      fd I.m * (5 * PscP.mul + 4 * PscP.mul * fB0 I.m + 5 * PscP.readout + 2000) :=
    Nat.mul_le_mul hd (by dsimp only [I, cfg, B0] at hB04 ⊢; linarith only [hB04])
  have hLin :
      u * (wireRefreshOneCost L + wireTreeSyncEditCost L (detectOffTreeDrainUnit L) + 17 * L +
        detectOffTreeDrainUnit L + 3200 +
        14 * (cfg.P.d * Rpow * (PscP.mul * (cfg.P.k + 1) * B0 + 730) +
          (670 + 155 * (cfg.P.d + 1)) * Rpow)) ≤ fRho1 I.m * u := by
    rw [Nat.mul_comm (fRho1 I.m) u]
    apply Nat.mul_le_mul_left u
    dsimp only [fRho1, I, V, k, L, cfg, B0, Rpow] at hRefC hSyncC hL hDrain hRdTerm ⊢
    linarith only [hRefC, hSyncC, hL, hDrain, hRdTerm]
  change u * (wireRefreshOneCost L + wireTreeSyncEditCost L (detectOffTreeDrainUnit L) + 17 * L +
        detectOffTreeDrainUnit L + 3200 +
        14 * (cfg.P.d * Rpow * (PscP.mul * (cfg.P.k + 1) * B0 + 730) +
          (670 + 155 * (cfg.P.d + 1)) * Rpow)) +
      3 * (cfg.P.d * Rpow * (PscP.mul * (cfg.P.k + 1) * B0 + 730) +
        (670 + 155 * (cfg.P.d + 1)) * Rpow) +
      cfg.P.d * (5 * PscP.mul + 4 * PscP.mul * B0 + 5 * PscP.readout + 2000) +
      4 * PscP.mul * B0 + 2 * PscP.readout + 71 * L + 600 * (cfg.P.d + 1) +
      (2 * PscP.readout + (290 * levelM cfg.TP cfg.P cfg.P.d + 240) +
        levelM cfg.TP cfg.P cfg.P.d * (wireCoreLenEdgeCost Lw0 + 30) +
        PscP.mul * (4 * levelM cfg.TP cfg.P cfg.P.d + 4) * B0 +
        dryLastMult J + 310 * levelM cfg.TP cfg.P cfg.P.d + 1200) +
      510 * mThresh + 8500 ≤ fRho0 I.m + fRho1 I.m * u
  dsimp only [fRho0, I, V, k, L, cfg, B0, Lw0, Rpow] at hLin hRdTerm hDterm hB04 hL hd hTermFix ⊢
  linarith only [hLin, hRdTerm, hDterm, hB04, hL, hd, hTermFix]

/-- `dryInnerCoreToolMul Psc J` and `dryInnerCoreTreeMul J` are `SubpolyNat` in `I.m`. -/
theorem dryInnerCoreMul_le_subpoly (Psc : DrySparseCorePieces) :
    ∃ (fTool fTree : ℕ → ℕ), SubpolyNat fTool ∧ SubpolyNat fTree ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        dryInnerCoreToolMul Psc J ≤ fTool (solverConnectedAugmented J).m ∧
        dryInnerCoreTreeMul J ≤ fTree (solverConnectedAugmented J).m := by
  obtain ⟨fd, fL, fB0, fDrain, fSyncC, fEdgeC, fRdTerm, fLast,
    hfdSub, hfLSub, hfB0Sub, hfDrainSub, hfSyncCSub, hfEdgeCSub, hfRdTermSub, hfLastSub, hP⟩ :=
    dryInnerCoreCostPieces_le_subpoly Psc
  let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
  let fBranchA : ℕ → ℕ := fun M =>
    2 * (fd M + 1) * (fSyncC M + 172) + 17 * fL M + fDrain M + 3100 +
      (5 * PscP.mul + fEdgeC M + 320)
  have hfBranchASub : SubpolyNat fBranchA :=
    SubpolyNat.add
      (SubpolyNat.add_const
        (SubpolyNat.add
          (SubpolyNat.add
            (SubpolyNat.mul (SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) 2)
              (SubpolyNat.add_const hfSyncCSub 172))
            (SubpolyNat.const_mul hfLSub 17))
          hfDrainSub) 3100)
      (SubpolyNat.mono (fun M => by omega) (SubpolyNat.add_const hfEdgeCSub (5 * PscP.mul + 320)))
  let fBranchB : ℕ → ℕ := fun M =>
    PscP.mul + fEdgeC M + 120 + fRdTerm M + (5 * PscP.mul + fEdgeC M + 320) +
      4 * PscP.mul * fB0 M + 310 * (fd M + 1)
  have hfBranchBSub : SubpolyNat fBranchB := by
    have h1 := SubpolyNat.add (SubpolyNat.const_mul hfEdgeCSub 2) hfRdTermSub
    have h2 := SubpolyNat.add (SubpolyNat.const_mul hfB0Sub (4 * PscP.mul))
      (SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) 310)
    exact SubpolyNat.mono (fun M => by dsimp only [fBranchB]; omega)
      (SubpolyNat.add_const (SubpolyNat.add h1 h2) (6 * PscP.mul + 440))
  let fTool : ℕ → ℕ := fun M => fLast M + fBranchA M + fBranchB M
  have hfToolSub : SubpolyNat fTool :=
    SubpolyNat.add (SubpolyNat.add hfLastSub hfBranchASub) hfBranchBSub
  let fTree : ℕ → ℕ := fun M => fSyncC M + 120
  have hfTreeSub : SubpolyNat fTree := SubpolyNat.add_const hfSyncCSub 120
  refine ⟨fTool, fTree, hfToolSub, hfTreeSub, fun J hJn hJm hCap => ?_⟩
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let B0 := SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀
  let Lw0 := ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀
  let Rpow := (updateCoreStepRatio (drySCEdMul Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed))
    (levelM cfg.TP cfg.P 0) cfg.N₀) ^ cfg.P.d
  obtain ⟨hd, hL, hB0, hDrain, hSyncC, hEdgeC, hRdTerm, hLast'⟩ := hP J hJn hJm hCap
  have hBrA :
      2 * (cfg.P.d + 1) * (wireTreeSyncEditCost L (detectOffTreeDrainUnit L) + 172) +
        17 * L + detectOffTreeDrainUnit L + 3100 +
        (5 * PscP.mul + wireCoreLenEdgeCost Lw0 + 320) ≤ fBranchA I.m := by
    dsimp only [fBranchA, I, V, k, L, cfg, Lw0] at hd hL hDrain hSyncC hEdgeC ⊢
    have h1 := Nat.mul_le_mul (show 2 * ((concreteCirculationCfgWithLast dryWitnessUsed J).P.d + 1) ≤
      2 * (fd (solverConnectedAugmented J).m + 1) by omega)
      (Nat.add_le_add_right hSyncC 172)
    linarith only [h1, hL, hDrain, hEdgeC]
  have hBrB :
      PscP.mul + wireCoreLenEdgeCost Lw0 + 120 +
        (cfg.P.d * Rpow * (PscP.mul * (cfg.P.k + 1) * B0 + 730) +
          (670 + 155 * (cfg.P.d + 1)) * Rpow) +
        (5 * PscP.mul + wireCoreLenEdgeCost Lw0 + 320) +
        4 * PscP.mul * B0 + 310 * (cfg.P.d + 1) ≤ fBranchB I.m := by
    have hB04 := Nat.mul_le_mul_left (4 * PscP.mul) hB0
    dsimp only [fBranchB, I, V, k, L, cfg, B0, Lw0, Rpow] at hEdgeC hRdTerm hB04 hd ⊢
    linarith only [hEdgeC, hRdTerm, hB04, hd]
  constructor
  · change max (dryLastMult J)
      (max (2 * (cfg.P.d + 1) * (wireTreeSyncEditCost L (detectOffTreeDrainUnit L) + 172) +
            17 * L + detectOffTreeDrainUnit L + 3100 +
            (5 * PscP.mul + wireCoreLenEdgeCost Lw0 + 320))
        (PscP.mul + wireCoreLenEdgeCost Lw0 + 120 +
          (cfg.P.d * Rpow * (PscP.mul * (cfg.P.k + 1) * B0 + 730) +
            (670 + 155 * (cfg.P.d + 1)) * Rpow) +
          (5 * PscP.mul + wireCoreLenEdgeCost Lw0 + 320) +
          4 * PscP.mul * B0 + 310 * (cfg.P.d + 1))) ≤ fTool I.m
    dsimp only [fTool]
    exact max_le (by linarith only [hLast']) (max_le (by linarith only [hBrA]) (by linarith only [hBrB]))
  · change wireTreeSyncEditCost L (detectOffTreeDrainUnit L) + 120 ≤ fTree I.m
    dsimp only [fTree, I, V, k, L] at hSyncC ⊢
    linarith only [hSyncC]

/-! ## 4. Full `DryCoreOpenSizeBounds (dryInnerCoreSizes Psc)` -/

/-- Unconditional `DryCoreOpenSizeBounds` for `dryInnerCoreSizes Psc`. -/
theorem dryInnerCoreSizeBounds (Psc : DrySparseCorePieces) :
    DryCoreOpenSizeBounds (dryInnerCoreSizes Psc) where
  hCoreSpaceMono := fun _ J _ _ _ => dryInnerCoreSpace_mono Psc J
  hCoreSpacePoly := by
    obtain ⟨f, hfP, hbd⟩ := dryInnerCoreSpace_le_poly Psc
    exact ⟨f, hfP, fun _ J hJn hJm hCap => hbd J hJn hJm hCap⟩
  hCoreFixedSubpoly := by
    obtain ⟨f0, f1, hf0, hf1, hbd⟩ := dryInnerCoreFixed_le_subpoly Psc
    exact ⟨f0, f1, hf0, hf1, fun _ J hJn hJm hCap u _ => hbd J hJn hJm hCap u⟩
  hCoreMulSubpoly := by
    obtain ⟨fTool, fTree, hfTool, hfTree, hbd⟩ := dryInnerCoreMul_le_subpoly Psc
    exact ⟨fTool, fTree, hfTool, hfTree, fun _ J hJn hJm hCap => hbd J hJn hJm hCap⟩

end MinCostFlow.Final.DryRun

end
