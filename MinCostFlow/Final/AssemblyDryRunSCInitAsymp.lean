module

public import MinCostFlow.Final.AssemblyDryRunSCAsymp
public import MinCostFlow.Final.AssemblyDryRunSCLastSpace
import MinCostFlow.Final.AssemblyDryRunSCParam
import Mathlib.Tactic

/-!
# Uniform Init and Deep-Shift asymptotic bounds (`AssemblyDryRunSCInitAsymp`)

Proves:
* `dryInitFixed_le_subpoly`: `initConcreteFixed ≤ (I.m + 1) * f I.m` with `SubpolyNat f`
  (modulo `PackedNonLoopMultExposed`);
* `drySparsifyDen_poly` and `dryParamSpace_le_poly`;
* `dryDeepLevelSpace_le_poly`, `dryInitSpace_le_poly`, and `dryDeepSpace_le_poly`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program WideWord

/-! ## 3. `SubpolyNat` bound for `initConcreteFixed` (`(I.m + 1) * SubpolyNat`) -/

/-- `initConcreteFixed` at `dryParamCost`, `dryLastMult`, `drySCParams` is at most
`(I.m + 1) * f I.m` with `SubpolyNat f`. -/
theorem dryInitFixed_le_subpoly (Psc : DrySparseCorePieces) :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let L := ipmQualityLimbs I.m V k
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let limbMul := concreteReadout2LimbMul dryWitnessUsed
        initConcreteFixed I.m (namedInstance I).n L cfg.P.d (dryParamCost source J) dryCapExp
          (dryCapLimit dryWitnessUsed J) (dryLastMult J) LinkCut.PathProg.pathC
          (drySCParams Psc dryCapExp limbMul)
          (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀ ≤
        (I.m + 1) * f I.m := by
  obtain ⟨C_par, hPar⟩ := dryParamCost_polylog
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  obtain ⟨fLM, hfLMSub, hfLM⟩ := dryLevelM_le_subpoly
  obtain ⟨fLast, hfLastSub, hfLast⟩ := dryLastMult_le_subpoly
  let P := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
  let K_thr : ℕ := concreteEdgeThresholdWithLast dryWitnessUsed + 1
  let fLog : ℕ → ℕ := fun M => Nat.log 2 (M + 2) + 1
  have hfLogSub : SubpolyNat fLog := subpolyNat_log_add_two
  let fM1 : ℕ → ℕ := fun M => fLM M + 4 * K_thr + 2
  have hfM1Sub : SubpolyNat fM1 := SubpolyNat.add_const (SubpolyNat.add_const hfLMSub (4 * K_thr)) 2
  let fM1Poly : PolyNat (fun M => (M + 1) * fM1 M) :=
    PolyNat.mul (PolyNat.add_const PolyNat.id 1) (SubpolyNat.toPolyNat hfM1Sub)
  let fBLog : ℕ → ℕ := fun M => (Nat.log 2 ((M + 1) * fM1 M + 2) + 1) ^ 2
  have hfBLogSub : SubpolyNat fBLog := SubpolyNat.pow (subpolyNat_log_of_poly fM1Poly) 2
  let cLw : ℕ := dryCapExp + sparseCoreReadout2LimbConst
  let fLw : ℕ → ℕ := fun M => dryLimbsOfM M + cLw * (Nat.log 2 ((M + 1) * fM1 M + 2) + 1)
  have hfLwSub : SubpolyNat fLw :=
    SubpolyNat.add dryLimbsOfM_subpoly (SubpolyNat.const_mul (subpolyNat_log_of_poly fM1Poly) cLw)
  let fLvl : ℕ → ℕ := fun M =>
    P.mul * (12 * K_thr + 3 * fLM M + 2) +
    P.mul * (8 * K_thr + 2 * fLM M + 2) * fBLog M +
    2 * P.readout + 17 * (20 * (12 * K_thr + 4) + 5) +
    fLM M * (1400 * (fLw M) ^ 2 + 2100 * fLw M + 880) + 250
  have hfLvlSub : SubpolyNat fLvl := by
    have h1 := SubpolyNat.const_mul (SubpolyNat.add_const (SubpolyNat.const_mul hfLMSub 3) (12 * K_thr + 2)) P.mul
    have h2 := SubpolyNat.mul
      (SubpolyNat.const_mul (SubpolyNat.add_const (SubpolyNat.const_mul hfLMSub 2) (8 * K_thr + 2)) P.mul)
      hfBLogSub
    have h3 := SubpolyNat.mul hfLMSub
      (SubpolyNat.add (SubpolyNat.const_mul (SubpolyNat.pow hfLwSub 2) 1400)
        (SubpolyNat.add_const (SubpolyNat.const_mul hfLwSub 2100) 880))
    have h4 := SubpolyNat.add_const
      (SubpolyNat.add
        (SubpolyNat.add_const
          (SubpolyNat.add_const (SubpolyNat.add h1 h2) (2 * P.readout))
          (17 * (20 * (12 * K_thr + 4) + 5))) h3) 250
    exact SubpolyNat.mono (fun M => by
      dsimp only [fLvl]
      have ha : 12 * K_thr + 3 * fLM M + 2 = 3 * fLM M + (12 * K_thr + 2) := by omega
      have hb : 8 * K_thr + 2 * fLM M + 2 = 2 * fLM M + (8 * K_thr + 2) := by omega
      have hc : 1400 * (fLw M) ^ 2 + 2100 * fLw M + 880 =
          1400 * (fLw M) ^ 2 + (2100 * fLw M + 880) := by omega
      rw [ha, hb, hc]) h4
  let fLogV : ℕ → ℕ := fun M => Nat.log 2 (2 * (2 * M + 2) + 1) + 1
  have hfLogVSub : SubpolyNat fLogV :=
    SubpolyNat.mono (fun M => Nat.add_le_add_right (Nat.log_mono_right (by omega : 2 * (2 * M + 2) + 1 ≤ 4 * M + 5 + 2)) 1)
      (subpolyNat_log_of_poly (PolyNat.add_const (PolyNat.const_mul PolyNat.id 4) 5))
  let fTot : ℕ → ℕ := fun M =>
    2000 + 150 * (12 * K_thr + 4) + C_par * (fLog M) ^ 24 + fd M * fLvl M + fLast M + 30 +
    LinkCut.PathProg.pathC * (dryLimbsOfM M + 1) ^ 2 * 3 +
    (2700 * (dryLimbsOfM M) ^ 2 + 2920 * dryLimbsOfM M + 869) + 101 * dryLimbsOfM M +
    fd M * (2 * P.readout + 136) + 22 * fBLog M +
    (25 * (LinkCut.PathProg.pathC * (dryLimbsOfM M + 1) ^ 2) * fLogV M + 96) + 2000
  have hfTotSub : SubpolyNat fTot := by
    have hL1 := SubpolyNat.add_const dryLimbsOfM_subpoly 1
    have hL1sq := SubpolyNat.pow hL1 2
    have hLsq := SubpolyNat.pow dryLimbsOfM_subpoly 2
    have ha := SubpolyNat.const_mul (SubpolyNat.pow hfLogSub 24) C_par
    have hb := SubpolyNat.mul hfdSub hfLvlSub
    have hc := SubpolyNat.const_mul (SubpolyNat.const_mul hL1sq LinkCut.PathProg.pathC) 3
    have hd' := SubpolyNat.add_const
      (SubpolyNat.add (SubpolyNat.const_mul hLsq 2700) (SubpolyNat.const_mul dryLimbsOfM_subpoly 2920)) 869
    have he := SubpolyNat.const_mul dryLimbsOfM_subpoly 101
    have hf' := SubpolyNat.const_mul hfdSub (2 * P.readout + 136)
    have hfB := SubpolyNat.const_mul hfBLogSub 22
    have hg := SubpolyNat.add_const
      (SubpolyNat.mul (SubpolyNat.const_mul (SubpolyNat.const_mul hL1sq LinkCut.PathProg.pathC) 25) hfLogVSub) 96
    have hall := SubpolyNat.add_const
      (SubpolyNat.add
        (SubpolyNat.add
          (SubpolyNat.add
            (SubpolyNat.add
              (SubpolyNat.add
                (SubpolyNat.add
                  (SubpolyNat.add_const
                    (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add_const ha (2000 + 150 * (12 * K_thr + 4))) hb) hfLastSub) 30)
                  hc) hd') he) hf') hfB) hg) 2000
    exact SubpolyNat.mono (fun M => by
      dsimp only [fTot]
      have hcomm1 : LinkCut.PathProg.pathC * (dryLimbsOfM M + 1) ^ 2 * 3 =
          3 * (LinkCut.PathProg.pathC * (dryLimbsOfM M + 1) ^ 2) := by ring
      have hcomm2 : fd M * (2 * P.readout + 136) = (2 * P.readout + 136) * fd M := by ring
      omega) hall
  refine ⟨fTot, hfTotSub, fun source J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hJmLe : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCap).1
  have hGnEq : (namedInstance I).n = I.n := by simp [namedInstance, MGraph.n]
  have hInLe : I.n ≤ 2 * I.m + 2 := by
    have hIn : I.n = J.n + 1 := by
      simp [I, solverConnectedAugmented, connectedInitialInstance, instanceOfArrays,
        Circulation.toInstance]
    omega
  have hM0Le : cfg.P.M₀ ≤ K_thr * (I.m + 1) := dryM0OfM_le_mul I.m
  have hN0Le : cfg.N₀ ≤ 4 * K_thr * (I.m + 1) := by
    have : cfg.N₀ = 4 * cfg.P.M₀ := rfl; nlinarith only [this, hM0Le]
  have hCapLe : dryCapLimit dryWitnessUsed J ≤ (12 * K_thr + 4) * (I.m + 1) := by
    have : dryCapLimit dryWitnessUsed J = 12 * cfg.P.M₀ + 4 := rfl
    nlinarith only [this, hM0Le]
  have hDgLe : dynGraphSize (dryCapLimit dryWitnessUsed J) (dryCapLimit dryWitnessUsed J) ≤
      (20 * (12 * K_thr + 4) + 5) * (I.m + 1) := by
    unfold dynGraphSize; nlinarith only [hCapLe]
  have hParLe : dryParamCost source J ≤ (I.m + 1) * (C_par * (fLog I.m) ^ 24) := by
    have h1 := hPar source J hJn hJm hCap
    have h2 : Nat.log 2 (J.m + 2) + 1 ≤ fLog I.m :=
      Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
    have h3 : C_par * (Nat.log 2 (J.m + 2) + 1) ^ 24 ≤ C_par * (fLog I.m) ^ 24 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 24)
    exact (h1.trans h3).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hLvlSum : (∑ i ∈ Finset.range cfg.P.d,
      (ordLevelFixedCost L dryCapExp (dryCapLimit dryWitnessUsed J) P
        (levelM cfg.TP cfg.P i) cfg.N₀ (levelM cfg.TP cfg.P (i + 1)) + 9)) ≤
      (I.m + 1) * (fd I.m * fLvl I.m) := by
    have hterm : ∀ i ∈ Finset.range cfg.P.d,
        ordLevelFixedCost L dryCapExp (dryCapLimit dryWitnessUsed J) P
          (levelM cfg.TP cfg.P i) cfg.N₀ (levelM cfg.TP cfg.P (i + 1)) + 9 ≤
        (I.m + 1) * fLvl I.m := by
      intro i hi
      have hiLt : i < cfg.P.d := Finset.mem_range.mp hi
      have hMi := hfLM J hJn hJm hCap i hiLt.le
      have hMi1 := hfLM J hJn hJm hCap (i + 1) hiLt
      have hMN : levelM cfg.TP cfg.P i + cfg.N₀ + 2 ≤ (I.m + 1) * fM1 I.m + 2 := by
        dsimp only [fM1]; nlinarith only [hMi, hN0Le]
      have hBL : SparseCore.bundleLogFactor (levelM cfg.TP cfg.P i) cfg.N₀ ≤ fBLog I.m := by
        unfold SparseCore.bundleLogFactor
        exact Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right hMN) 1) 2
      have hLw : ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P i) cfg.N₀ ≤ fLw I.m := by
        unfold ordLevelLwMax
        have hlg := Nat.add_le_add_right (Nat.log_mono_right (b := 2) hMN) 1
        exact Nat.add_le_add hL (Nat.mul_le_mul_left cLw hlg)
      have hCL : wireCoreLenEdgeCost (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P i) cfg.N₀) + 30 ≤
          1400 * (fLw I.m) ^ 2 + 2100 * fLw I.m + 880 := by
        unfold wireCoreLenEdgeCost
        have hsq := Nat.pow_le_pow_left hLw 2
        omega
      unfold ordLevelFixedCost
      dsimp only [fLvl]
      have h1 : P.mul * (cfg.N₀ + levelM cfg.TP cfg.P i + (2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P i + 1) + 1) ≤
          (I.m + 1) * (P.mul * (12 * K_thr + 3 * fLM I.m + 2)) := by
        have ha : cfg.N₀ + levelM cfg.TP cfg.P i + (2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P i + 1) + 1 ≤
            (I.m + 1) * (12 * K_thr + 3 * fLM I.m + 2) := by nlinarith only [hMi, hN0Le]
        calc P.mul * _ ≤ P.mul * ((I.m + 1) * (12 * K_thr + 3 * fLM I.m + 2)) :=
              Nat.mul_le_mul_left _ ha
          _ = _ := by ring
      have h2 : P.mul * (2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P (i + 1) + 2) *
          SparseCore.bundleLogFactor (levelM cfg.TP cfg.P i) cfg.N₀ ≤
          (I.m + 1) * (P.mul * (8 * K_thr + 2 * fLM I.m + 2) * fBLog I.m) := by
        have ha : 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P (i + 1) + 2 ≤
            (I.m + 1) * (8 * K_thr + 2 * fLM I.m + 2) := by nlinarith only [hMi1, hN0Le]
        calc P.mul * _ * _ ≤ P.mul * ((I.m + 1) * (8 * K_thr + 2 * fLM I.m + 2)) * fBLog I.m :=
              Nat.mul_le_mul (Nat.mul_le_mul_left _ ha) hBL
          _ = _ := by ring
      have h3 : levelM cfg.TP cfg.P (i + 1) *
          (wireCoreLenEdgeCost (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P i) cfg.N₀) + 30) ≤
          (I.m + 1) * (fLM I.m * (1400 * (fLw I.m) ^ 2 + 2100 * fLw I.m + 880)) := by
        calc _ ≤ ((I.m + 1) * fLM I.m) * (1400 * (fLw I.m) ^ 2 + 2100 * fLw I.m + 880) :=
              Nat.mul_le_mul hMi1 hCL
          _ = _ := by ring
      have h4 : 17 * dynGraphSize (dryCapLimit dryWitnessUsed J) (dryCapLimit dryWitnessUsed J) ≤
          (I.m + 1) * (17 * (20 * (12 * K_thr + 4) + 5)) := by
        have := Nat.mul_le_mul_left 17 hDgLe; linarith
      have h5 : 2 * P.readout ≤ (I.m + 1) * (2 * P.readout) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      have h6 : 244 ≤ (I.m + 1) * 250 := by nlinarith
      have hExp : (I.m + 1) * (P.mul * (12 * K_thr + 3 * fLM I.m + 2) +
          P.mul * (8 * K_thr + 2 * fLM I.m + 2) * fBLog I.m +
          2 * P.readout + 17 * (20 * (12 * K_thr + 4) + 5) +
          fLM I.m * (1400 * (fLw I.m) ^ 2 + 2100 * fLw I.m + 880) + 250) =
          (I.m + 1) * (P.mul * (12 * K_thr + 3 * fLM I.m + 2)) +
          (I.m + 1) * (P.mul * (8 * K_thr + 2 * fLM I.m + 2) * fBLog I.m) +
          (I.m + 1) * (2 * P.readout) +
          (I.m + 1) * (17 * (20 * (12 * K_thr + 4) + 5)) +
          (I.m + 1) * (fLM I.m * (1400 * (fLw I.m) ^ 2 + 2100 * fLw I.m + 880)) +
          (I.m + 1) * 250 := by simp only [Nat.mul_add]
      rw [hExp]; omega
    calc _ ≤ ∑ _ ∈ Finset.range cfg.P.d, (I.m + 1) * fLvl I.m := Finset.sum_le_sum hterm
      _ = cfg.P.d * ((I.m + 1) * fLvl I.m) := by simp
      _ ≤ fd I.m * ((I.m + 1) * fLvl I.m) := Nat.mul_le_mul_right _ (hfd J hJn hJm hCap)
      _ = (I.m + 1) * (fd I.m * fLvl I.m) := by ring
  unfold initConcreteFixed ordInitLevelsFixed initPostTailCost initLinkChainCost pathTreeBudget
  dsimp only
  rw [hGnEq]
  have hLastLe : dryLastMult J ≤ (I.m + 1) * fLast I.m :=
    (hfLast J hJn hJm hCap).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hLsq : L ^ 2 ≤ (dryLimbsOfM I.m) ^ 2 := Nat.pow_le_pow_left hL 2
  have hL1sq : (L + 1) ^ 2 ≤ (dryLimbsOfM I.m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hPT : 25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (Nat.log 2 (2 * I.n + 1) + 1) ≤
      25 * (LinkCut.PathProg.pathC * (dryLimbsOfM I.m + 1) ^ 2) * fLogV I.m :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 25 (Nat.mul_le_mul_left _ hL1sq))
      (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1)
  have hTree1 : LinkCut.PathProg.pathC * (L + 1) ^ 2 * (I.n + 1) ≤
      (I.m + 1) * (LinkCut.PathProg.pathC * (dryLimbsOfM I.m + 1) ^ 2 * 3) := by
    have hn3 : I.n + 1 ≤ (I.m + 1) * 3 := by omega
    calc LinkCut.PathProg.pathC * (L + 1) ^ 2 * (I.n + 1)
        ≤ LinkCut.PathProg.pathC * (dryLimbsOfM I.m + 1) ^ 2 * ((I.m + 1) * 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hL1sq) hn3
      _ = (I.m + 1) * (LinkCut.PathProg.pathC * (dryLimbsOfM I.m + 1) ^ 2 * 3) := by ring
  have hPost1 : I.m * (2700 * L ^ 2 + 2920 * L + 869) ≤
      (I.m + 1) * (2700 * (dryLimbsOfM I.m) ^ 2 + 2920 * dryLimbsOfM I.m + 869) :=
    Nat.mul_le_mul (Nat.le_succ _) (by omega)
  have hPost2 : I.m * (25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (Nat.log 2 (2 * I.n + 1) + 1) + 96) ≤
      (I.m + 1) * (25 * (LinkCut.PathProg.pathC * (dryLimbsOfM I.m + 1) ^ 2) * fLogV I.m + 96) :=
    Nat.mul_le_mul (Nat.le_succ _) (by omega)
  have hPost3 : cfg.P.d * (2 * P.readout + 80) + 56 * cfg.P.d ≤
      (I.m + 1) * (fd I.m * (2 * P.readout + 136)) := by
    have h1 : cfg.P.d * (2 * P.readout + 80) + 56 * cfg.P.d = cfg.P.d * (2 * P.readout + 136) := by ring
    rw [h1]
    exact (Nat.mul_le_mul_right _ (hfd J hJn hJm hCap)).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have h101L : 71 * L + 30 * (I.m * L) ≤ (I.m + 1) * (101 * dryLimbsOfM I.m) := by
    have h1 : 71 * L ≤ (I.m + 1) * (71 * dryLimbsOfM I.m) :=
      (Nat.mul_le_mul_left 71 hL).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    have h2 : 30 * (I.m * L) ≤ (I.m + 1) * (30 * dryLimbsOfM I.m) := by
      calc 30 * (I.m * L) = I.m * (30 * L) := by ring
        _ ≤ (I.m + 1) * (30 * dryLimbsOfM I.m) := Nat.mul_le_mul (Nat.le_succ _) (Nat.mul_le_mul_left 30 hL)
    linarith only [h1, h2]
  have hCap150 : 150 * dryCapLimit dryWitnessUsed J ≤ (I.m + 1) * (150 * (12 * K_thr + 4)) := by
    calc 150 * dryCapLimit dryWitnessUsed J ≤ 150 * ((12 * K_thr + 4) * (I.m + 1)) :=
          Nat.mul_le_mul_left 150 hCapLe
      _ = (I.m + 1) * (150 * (12 * K_thr + 4)) := by
          rw [Nat.mul_comm ((12 * K_thr + 4)) (I.m + 1), Nat.mul_left_comm]
  have hClogN0 : 22 * Nat.clog 2 (cfg.N₀ + 2) ≤ (I.m + 1) * (22 * fBLog I.m) := by
    have hN0_le : cfg.N₀ + 2 ≤ (I.m + 1) * fM1 I.m + 2 := by
      dsimp only [fM1]
      have h1 : 4 * K_thr * (I.m + 1) ≤ (I.m + 1) * (fLM I.m + 4 * K_thr + 2) := by
        rw [Nat.mul_comm (4 * K_thr) (I.m + 1)]
        exact Nat.mul_le_mul_left (I.m + 1) (by omega)
      omega
    have hclog_le : Nat.clog 2 (cfg.N₀ + 2) ≤ Nat.log 2 ((I.m + 1) * fM1 I.m + 2) + 1 :=
      (Nat.clog_le_iff_le_pow (by decide)).mpr
        (hN0_le.trans (Nat.lt_pow_succ_log_self (by decide) _).le)
    have hsq_ge : Nat.log 2 ((I.m + 1) * fM1 I.m + 2) + 1 ≤ fBLog I.m :=
      Nat.le_self_pow (by decide : 2 ≠ 0) _
    exact (Nat.mul_le_mul_left 22 (hclog_le.trans hsq_ge)).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hLin : 130 * I.n + 490 * I.m + 145 + (60 * I.n + 120) + 20 * I.m + 92 +
      140 + 520 + 650 ≤ (I.m + 1) * 2000 := by omega
  have h1000 : 1000 ≤ (I.m + 1) * 2000 := by omega
  have h30 : 30 ≤ (I.m + 1) * 30 := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hExpTot : (I.m + 1) * fTot I.m =
      (I.m + 1) * 2000 + (I.m + 1) * (150 * (12 * K_thr + 4)) + (I.m + 1) * (C_par * (fLog I.m) ^ 24) +
      (I.m + 1) * (fd I.m * fLvl I.m) + (I.m + 1) * fLast I.m + (I.m + 1) * 30 +
      (I.m + 1) * (LinkCut.PathProg.pathC * (dryLimbsOfM I.m + 1) ^ 2 * 3) +
      (I.m + 1) * (2700 * (dryLimbsOfM I.m) ^ 2 + 2920 * dryLimbsOfM I.m + 869) +
      (I.m + 1) * (101 * dryLimbsOfM I.m) +
      (I.m + 1) * (fd I.m * (2 * P.readout + 136)) + (I.m + 1) * (22 * fBLog I.m) +
      (I.m + 1) * (25 * (LinkCut.PathProg.pathC * (dryLimbsOfM I.m + 1) ^ 2) * fLogV I.m + 96) +
      (I.m + 1) * 2000 := by dsimp only [fTot]; simp only [Nat.mul_add]
  rw [hExpTot]
  linarith only [hParLe, hLvlSum, hLastLe, hTree1, hPost1, hPost2, hPost3, h101L, hCap150, hClogN0,
    hLin, h1000, h30]

/-! ## 4. `PolyNat` bounds on `dryParamSpace`, `dryLastSpace`, `initConcreteSpace`, `dryDeepSpace` -/

/-- `Expander.maxPhiDenOf dryDecompK dryDecompThr (M₀ ^ 2)` is bounded by a `PolyNat` function of `M`. -/
theorem drySparsifyDen_poly : PolyNat (fun M => Expander.maxPhiDenOf dryDecompK dryDecompThr (dryM0OfM M ^ 2)) := by
  obtain ⟨C₀_p, C₁_p, hC₀p, hC₁p, hden_sb⟩ :=
    Expander.decomposeImpl_phi_lb_subpoly ExpanderDecomp.expanderDecompositionUsed_holds
  obtain ⟨B_den, hBden, hBden_le⟩ :=
    Chain.exp_subpoly_mul_loglog_le_rpow (a := 2 / 3) (C := C₀_p) (δ := 1)
      (by norm_num) (by norm_num) (by norm_num)
  let K : ℕ := max 1 ⌈C₁_p * B_den⌉₊
  have h1 : ∀ M, Expander.maxPhiDenOf dryDecompK dryDecompThr (dryM0OfM M ^ 2) ≤
      K * (dryM0OfM M ^ 2 + 2) := by
    intro M
    have hM01 : 1 ≤ dryM0OfM M :=
      (by omega : 1 ≤ 2).trans ((concreteEdgeThresholdWithLast_ge_two dryWitnessUsed).trans (le_max_right _ _))
    have hinv := hden_sb (dryM0OfM M ^ 2)
    have hphi : (Expander.decomposeImplUsed ExpanderDecomp.expanderDecompositionUsed_holds).φ_lb
        (dryM0OfM M ^ 2) = 1 / (Expander.maxPhiDenOf dryDecompK dryDecompThr (dryM0OfM M ^ 2) : ℝ) := rfl
    rw [hphi, one_div_one_div] at hinv
    unfold Expander.subpolyB1 at hinv
    have harg : (3 : ℝ) ≤ ((dryM0OfM M ^ 2 : ℕ) : ℝ) + 2 := by
      exact_mod_cast (show 3 ≤ dryM0OfM M ^ 2 + 2 by nlinarith)
    have hexp := hBden_le (((dryM0OfM M ^ 2 : ℕ) : ℝ) + 2) harg
    rw [Real.rpow_one] at hexp
    have h2 : (Expander.maxPhiDenOf dryDecompK dryDecompThr (dryM0OfM M ^ 2) : ℝ) ≤
        (C₁_p * B_den) * (((dryM0OfM M ^ 2 : ℕ) : ℝ) + 2) := by
      have hm := mul_le_mul_of_nonneg_left hexp (by linarith : (0 : ℝ) ≤ C₁_p)
      have hcast : ((dryM0OfM M ^ 2 : ℕ) : ℝ) = (dryM0OfM M : ℝ) ^ 2 := by push_cast; rfl
      rw [hcast] at hinv hm ⊢
      linarith
    have hK : C₁_p * B_den ≤ (K : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)
    have h3 : (Expander.maxPhiDenOf dryDecompK dryDecompThr (dryM0OfM M ^ 2) : ℝ) ≤
        (K : ℝ) * (((dryM0OfM M ^ 2 : ℕ) : ℝ) + 2) :=
      h2.trans (mul_le_mul_of_nonneg_right hK (by positivity))
    exact_mod_cast h3
  exact PolyNat.mono h1 (PolyNat.const_mul (PolyNat.add_const (PolyNat.pow dryM0OfM_poly 2) 2) K)

private theorem wireParamDepthSpace_le (B E q P L : ℕ) (hB : 1 ≤ B)
    (hq : q = 38 * (B * E) ^ 8 + E) (hP : P = 4 * (q + E + 10)) (hL : L = P + E + 4) :
    L + L + Num.logarithmSpace L P E ≤ 5000 * ((400 * B ^ 8) * (E + 2) ^ 8) ^ 4 := by
  have hLogSp' : ∀ L P E : ℕ, Num.logarithmSpace L P E ≤ 600 * (L + P + E + 2) ^ 4 := by
    intro L P E
    simp only [Num.logarithmSpace, Num.rangeLogarithmSpace, Num.normalizedLogarithmSpace,
      Num.fixedDivideSpace, Num.logHornerSpace, Num.logHornerStepSpace,
      Num.integerDivideSpace, Num.unsignedDivideSpace]
    set Z := L + P + E + 2
    have hZ1 : 1 ≤ Z := by omega
    have h12 : 1 ≤ Z ^ 2 := Nat.one_le_pow 2 Z hZ1
    have h14 : 1 ≤ Z ^ 4 := Nat.one_le_pow 4 Z hZ1
    have hZ12 : Z ≤ Z ^ 2 := by nlinarith only [hZ1]
    have hZ13 : Z ≤ Z ^ 3 := by nlinarith only [hZ1, hZ12]
    have hZ14 : Z ≤ Z ^ 4 := by nlinarith only [hZ1, hZ12, hZ13]
    have hZ23 : Z ^ 2 ≤ Z ^ 3 := by nlinarith only [hZ1, hZ12]
    have hZ24 : Z ^ 2 ≤ Z ^ 4 := by nlinarith only [hZ1, hZ12, hZ23]
    have hZ34 : Z ^ 3 ≤ Z ^ 4 := by nlinarith only [hZ1, hZ12, hZ23]
    have hL' : L ≤ Z := by omega
    have hP' : P ≤ Z := by omega
    have hE' : E ≤ Z := by omega
    have hH : (P + 4) * (13 * L + (3 * L + 2 + 5 * L * (L + 1) + 3 * L) + 1) ≤ 120 * Z ^ 3 := by
      have ha : 13 * L + (3 * L + 2 + 5 * L * (L + 1) + 3 * L) + 1 ≤ 35 * Z ^ 2 := by
        nlinarith only [hL', hZ1, h12, hZ12]
      have hb : P + 4 ≤ 3 * Z := by omega
      calc _ ≤ (3 * Z) * (35 * Z ^ 2) := Nat.mul_le_mul hb ha
        _ = 105 * Z ^ 3 := by ring
        _ ≤ 120 * Z ^ 3 := by omega
    have hD : 5 * (3 * L) * (3 * L + 1) ≤ 60 * Z ^ 2 := by nlinarith only [hL', hZ1, h12, hZ12]
    have hEL : E * (3 * L + 1) ≤ 4 * Z ^ 2 := by nlinarith only [hE', hL', hZ1, h12, hZ12]
    linarith only [hH, hD, hEL, hL', hP', hE', h14, hZ14, hZ24, hZ34]
  have hE1 : 1 ≤ E + 2 := by omega
  have hBE : (B * E) ^ 8 ≤ B ^ 8 * (E + 2) ^ 8 := by
    rw [mul_pow]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 8)
  have hB1 : 1 ≤ B ^ 8 := Nat.one_le_pow 8 B hB
  have hE8 : E + 2 ≤ (E + 2) ^ 8 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hE1 (by decide : 1 ≤ 8)
  have hSum : L + P + E + 2 ≤ (400 * B ^ 8) * (E + 2) ^ 8 := by
    have hE8B : E + 2 ≤ B ^ 8 * (E + 2) ^ 8 := hE8.trans (Nat.le_mul_of_pos_left _ hB1)
    have h1B : 1 ≤ B ^ 8 * (E + 2) ^ 8 := le_trans (by omega) hE8B
    have hAssoc : (400 * B ^ 8) * (E + 2) ^ 8 = 400 * (B ^ 8 * (E + 2) ^ 8) := Nat.mul_assoc _ _ _
    rw [hAssoc]
    omega
  have hLle : L ≤ L + P + E + 2 := by omega
  have hLog := hLogSp' L P E
  have hP1 : 1 ≤ L + P + E + 2 := by omega
  have hP14 : L + P + E + 2 ≤ (L + P + E + 2) ^ 4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hP1 (by decide : 1 ≤ 4)
  have hPow4 := Nat.pow_le_pow_left hSum 4
  linarith only [hLog, hLle, hP14, hPow4]

private theorem wireParamChainDepthSpace_le (M₀ : ℕ) :
    wireParamChainDepthSpace M₀ ≤ 5000 * ((400 * (2 ^ 48) ^ 8) * (M₀ + 4) ^ 8) ^ 4 := by
  unfold wireParamChainDepthSpace
  extract_lets E q P L
  have hs : E ≤ M₀ + 2 := Nat.size_le.mpr Nat.lt_two_pow_self
  refine (wireParamDepthSpace_le (2 ^ 48) E q P L (Nat.one_le_pow 48 2 (by decide)) rfl rfl rfl).trans ?_
  exact Nat.mul_le_mul_left 5000 (Nat.pow_le_pow_left
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : E + 2 ≤ M₀ + 4) 8)) 4)

private theorem wireParamSparseDepthSpace_le (M₀ : ℕ) :
    wireParamSparseDepthSpace M₀ ≤ 5000 * ((400 * (2 ^ 24) ^ 8) * (M₀ ^ 2 + 4) ^ 8) ^ 4 := by
  unfold wireParamSparseDepthSpace
  extract_lets E q P L
  have hs : E ≤ M₀ ^ 2 + 2 := Nat.size_le.mpr Nat.lt_two_pow_self
  refine (wireParamDepthSpace_le (2 ^ 24) E q P L (Nat.one_le_pow 24 2 (by decide)) rfl rfl rfl).trans ?_
  exact Nat.mul_le_mul_left 5000 (Nat.pow_le_pow_left
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : E + 2 ≤ M₀ ^ 2 + 4) 8)) 4)

private theorem dryParamSpace_eq_at_dryM0 (source J : Circulation) :
    dryParamSpace source J =
      wireParamSpace dryDecompK dryDecompThr dryWitnessDen sparsifyPathDSUsed.params
        (dryM0OfM (solverConnectedAugmented J).m) := rfl

/-- `dryParamSpace` is bounded by a `PolyNat` function of `I.m`. -/
theorem dryParamSpace_le_poly :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        dryParamSpace source J ≤ f (solverConnectedAugmented J).m := by
  let pds := sparsifyPathDSUsed.params
  let fDen : ℕ → ℕ := fun M => Expander.maxPhiDenOf dryDecompK dryDecompThr (dryM0OfM M ^ 2)
  let fCap : ℕ → ℕ := fun M => 36 * dryM0OfM M ^ 2 * fDen M + 1
  have hfCapPoly : PolyNat fCap :=
    PolyNat.add_const
      (PolyNat.mul (PolyNat.const_mul (PolyNat.pow dryM0OfM_poly 2) 36) drySparsifyDen_poly) 1
  let K48 : ℕ := 400 * (2 ^ 48) ^ 8
  let K24 : ℕ := 400 * (2 ^ 24) ^ 8
  let fTot : ℕ → ℕ := fun M =>
    (((7 + (dryM0OfM M + 2)) +
      5000 * (K48 * (dryM0OfM M + 4) ^ 8) ^ 4) +
      5000 * (K24 * (dryM0OfM M ^ 2 + 4) ^ 8) ^ 4) +
    (pds.C_space * (fDen M + dryM0OfM M ^ 2 + 2) ^ pds.c_space +
      pds.C_space * (dryWitnessDen + fCap M + 2) ^ pds.c_space)
  have hfTotPoly : PolyNat fTot := by
    have h1 := PolyNat.add_const dryM0OfM_poly 2
    have h2 := PolyNat.const_mul (PolyNat.pow (PolyNat.const_mul (PolyNat.pow (PolyNat.add_const dryM0OfM_poly 4) 8) K48) 4) 5000
    have h3 := PolyNat.const_mul (PolyNat.pow (PolyNat.const_mul (PolyNat.pow (PolyNat.add_const (PolyNat.pow dryM0OfM_poly 2) 4) 8) K24) 4) 5000
    have h4 := PolyNat.const_mul (PolyNat.pow (PolyNat.add_const (PolyNat.add drySparsifyDen_poly (PolyNat.pow dryM0OfM_poly 2)) 2) pds.c_space) pds.C_space
    have h5 := PolyNat.const_mul (PolyNat.pow (PolyNat.add_const (PolyNat.add_const hfCapPoly dryWitnessDen) 2) pds.c_space) pds.C_space
    exact PolyNat.mono (fun M => by
      dsimp only [fTot, fDen]
      rw [Nat.add_comm 7 (dryM0OfM M + 2), Nat.add_comm dryWitnessDen (fCap M)])
      (PolyNat.add (PolyNat.add (PolyNat.add (PolyNat.add_const h1 7) h2) h3) (PolyNat.add h4 h5))
  refine ⟨fTot, hfTotPoly, fun source J _ _ _ => ?_⟩
  rw [dryParamSpace_eq_at_dryM0]
  unfold wireParamSpace
  dsimp only
  set M₀ := dryM0OfM (solverConnectedAugmented J).m
  have hs1 : (M₀ + 2).size ≤ M₀ + 2 := Nat.size_le.mpr Nat.lt_two_pow_self
  have hd1 := wireParamChainDepthSpace_le M₀
  have hd2 := wireParamSparseDepthSpace_le M₀
  have hb1 := pds.hboundsSpace_le (fDen (solverConnectedAugmented J).m) (M₀ ^ 2)
  have hb2 := pds.hboundsSpace_le dryWitnessDen (fCap (solverConnectedAugmented J).m)
  dsimp only [fTot]
  rw [Nat.add_assoc]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left hs1 7) hd1) hd2)
    (Nat.add_le_add hb1 hb2)

/-- `dryDeepLevelSpace Psc J j` (for `j < d`) is uniformly bounded by a `PolyNat` function of `I.m`. -/
theorem dryDeepLevelSpace_le_poly (Psc : DrySparseCorePieces) :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        ∀ j < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d,
          dryDeepLevelSpace Psc J j ≤ f (solverConnectedAugmented J).m := by
  obtain ⟨fLM, hfLMSub, hfLM⟩ := dryLevelM_le_subpoly
  let pb := drySCInitPoly Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
  let fM : ℕ → ℕ := fun M => (M + 1) * fLM M
  have hfMPoly : PolyNat fM := PolyNat.mul (PolyNat.add_const PolyNat.id 1) (SubpolyNat.toPolyNat hfLMSub)
  let fCoreArg : ℕ → ℕ := fun M => (2 * dryM0OfM M + 1) + fM M + 4 * dryM0OfM M + dryLimbsOfM M
  have hfCoreArgPoly : PolyNat fCoreArg :=
    PolyNat.add
      (PolyNat.add
        (PolyNat.add (PolyNat.add_const (PolyNat.const_mul dryM0OfM_poly 2) 1) hfMPoly)
        (PolyNat.const_mul dryM0OfM_poly 4))
      (SubpolyNat.toPolyNat dryLimbsOfM_subpoly)
  let cLw : ℕ := dryCapExp + sparseCoreReadout2LimbConst
  let fLw : ℕ → ℕ := fun M => dryLimbsOfM M + cLw * (fM M + 4 * dryM0OfM M + 3)
  have hfLwPoly : PolyNat fLw :=
    PolyNat.add (SubpolyNat.toPolyNat dryLimbsOfM_subpoly)
      (PolyNat.const_mul (PolyNat.add_const (PolyNat.add hfMPoly (PolyNat.const_mul dryM0OfM_poly 4)) 3) cLw)
  let fCap : ℕ → ℕ := fun M => 12 * dryM0OfM M + 4
  have hfCapPoly : PolyNat fCap := PolyNat.add_const (PolyNat.const_mul dryM0OfM_poly 12) 4
  let fTot : ℕ → ℕ := fun M =>
    pb.coeff * (fCoreArg M + 2) ^ pb.deg + 1 + (5 + 20 * fCap M) + 5 +
    fCap M * dryLimbsOfM M + fM M * (30 * (fLw M) ^ 2 + 30 * fLw M + 2) +
    (2 + 8 * dryM0OfM M + 2 * fM M)
  have hfTotPoly : PolyNat fTot := by
    have h1 := PolyNat.const_mul (PolyNat.pow (PolyNat.add_const hfCoreArgPoly 2) pb.deg) pb.coeff
    have h2 := PolyNat.add_const (PolyNat.const_mul hfCapPoly 20) 5
    have h3 := PolyNat.mul hfCapPoly (SubpolyNat.toPolyNat dryLimbsOfM_subpoly)
    have h4 := PolyNat.mul hfMPoly
      (PolyNat.add (PolyNat.const_mul (PolyNat.pow hfLwPoly 2) 30)
        (PolyNat.add_const (PolyNat.const_mul hfLwPoly 30) 2))
    have h5 := PolyNat.add (PolyNat.add_const (PolyNat.const_mul dryM0OfM_poly 8) 2)
      (PolyNat.const_mul hfMPoly 2)
    exact PolyNat.mono (fun M => by
      dsimp only [fTot]
      rw [Nat.add_assoc (30 * (fLw M) ^ 2)]
      omega)
      (PolyNat.add (PolyNat.add (PolyNat.add (PolyNat.add_const (PolyNat.add (PolyNat.add_const h1 1) h2) 5) h3) h4) h5)
  refine ⟨fTot, hfTotPoly, fun J hJn hJm hCap j hj => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hMj : levelM cfg.TP cfg.P j ≤ (I.m + 1) * fLM I.m := hfLM J hJn hJm hCap j hj.le
  have hMj1 : levelM cfg.TP cfg.P (j + 1) ≤ (I.m + 1) * fLM I.m := hfLM J hJn hJm hCap (j + 1) hj
  have hk_le : cfg.P.k ≤ 2 * dryM0OfM I.m + 1 := by
    have h1 := cfg.P.hk_upper
    have hM1 : (1 : ℝ) ≤ cfg.P.M₀ := by exact_mod_cast cfg.P.hM₀
    have hd1 : (1 : ℝ) ≤ cfg.P.d := by exact_mod_cast cfg.P.hd
    have hroot : (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) ≤ (cfg.P.M₀ : ℝ) := by
      calc (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) ≤ (cfg.P.M₀ : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hM1 (div_le_one_of_le₀ hd1 (by positivity))
        _ = (cfg.P.M₀ : ℝ) := Real.rpow_one _
    have h2 : (cfg.P.k : ℝ) ≤ 2 * (dryM0OfM I.m : ℝ) + 1 := by
      have : cfg.P.M₀ = dryM0OfM I.m := rfl
      rw [← this]; linarith
    exact_mod_cast h2
  have hCore : dryCoreInitSpace Psc J j ≤ pb.coeff * (fCoreArg I.m + 2) ^ pb.deg := by
    have h1 : dryCoreInitSpace Psc J j ≤ pb.eval (cfg.P.k + levelM cfg.TP cfg.P j + cfg.N₀ + L) :=
      dryCoreInitSpace_le_poly Psc J j
    have h2 : cfg.P.k + levelM cfg.TP cfg.P j + cfg.N₀ + L ≤ fCoreArg I.m := by
      have : cfg.N₀ = 4 * dryM0OfM I.m := rfl
      dsimp only [fCoreArg, fM]; omega
    exact h1.trans (pb.eval_mono h2)
  have hLw : ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P j) cfg.N₀ ≤ fLw I.m := by
    unfold ordLevelLwMax
    have hlg := Nat.log_le_self 2 (levelM cfg.TP cfg.P j + cfg.N₀ + 2)
    have hN0 : cfg.N₀ = 4 * dryM0OfM I.m := rfl
    dsimp only [fLw, fM]
    exact Nat.add_le_add hL (Nat.mul_le_mul_left cLw (by omega))
  have hES : wireCoreLenEdgeSpace (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P j) cfg.N₀) ≤
      30 * (fLw I.m) ^ 2 + 30 * fLw I.m + 2 := by
    unfold wireCoreLenEdgeSpace Num.integerDivideSpace Num.unsignedDivideSpace
    have hsq := Nat.pow_le_pow_left hLw 2
    nlinarith only [hLw, hsq]
  unfold dryDeepLevelSpace ordLevelSpace dynGraphSize
  dsimp only
  have hCapEq : dryCapLimit dryWitnessUsed J = fCap I.m := rfl
  have hN0Eq : cfg.N₀ = 4 * dryM0OfM I.m := rfl
  dsimp only [fTot, fM]
  change dryCoreInitSpace Psc J j + 1 + (4 + 7 * dryCapLimit dryWitnessUsed J + 9 * dryCapLimit dryWitnessUsed J) +
      5 + dryCapLimit dryWitnessUsed J * L +
      levelM cfg.TP cfg.P (j + 1) * wireCoreLenEdgeSpace (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P j) cfg.N₀) +
      (2 + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P (j + 1)) ≤ _
  rw [hCapEq, hN0Eq]
  have hmul1 : fCap I.m * L ≤ fCap I.m * dryLimbsOfM I.m := Nat.mul_le_mul_left _ hL
  have hmul2 : levelM cfg.TP cfg.P (j + 1) *
      wireCoreLenEdgeSpace (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P j) cfg.N₀) ≤
      ((I.m + 1) * fLM I.m) * (30 * (fLw I.m) ^ 2 + 30 * fLw I.m + 2) := Nat.mul_le_mul hMj1 hES
  rw [hN0Eq] at hmul2
  change _ ≤ pb.coeff * (fCoreArg I.m + 2) ^ pb.deg + 1 + (5 + 20 * fCap I.m) + 5 +
      fCap I.m * dryLimbsOfM I.m + ((I.m + 1) * fLM I.m) * (30 * (fLw I.m) ^ 2 + 30 * fLw I.m + 2) +
      (2 + 8 * dryM0OfM I.m + 2 * ((I.m + 1) * fLM I.m))
  linarith only [hCore, hmul1, hmul2, hMj1]

/-- `initConcreteSpace` at `dryCoreInitSpace Psc J` is bounded by a `PolyNat` function of `I.m`. -/
theorem dryInitSpace_le_poly (Psc : DrySparseCorePieces) :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let L := ipmQualityLimbs I.m V k
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        initConcreteSpace I.m (namedInstance I).n L cfg.P.d (dryParamSpace source J) dryCapExp
          (dryCapLimit dryWitnessUsed J) (dryLastSpace J)
          (LinkCut.PathProg.arenaEnd 0 (namedInstance I).n L)
          (20 * LinkCut.PathProg.treeLimbs L + 100)
          (dryCoreInitSpace Psc J) (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1))
          cfg.N₀ ≤ f I.m := by
  obtain ⟨fPar, hfParP, hPar⟩ := dryParamSpace_le_poly
  obtain ⟨fLast, hfLastP, hLast⟩ := dryLastSpace_le_poly
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  obtain ⟨fLvl, hfLvlP, hLvl⟩ := dryDeepLevelSpace_le_poly Psc
  let fL : ℕ → ℕ := dryLimbsOfM
  have hfLP : PolyNat fL := SubpolyNat.toPolyNat dryLimbsOfM_subpoly
  let fCap : ℕ → ℕ := fun M => 12 * dryM0OfM M + 4
  have hfCapP : PolyNat fCap := PolyNat.add_const (PolyNat.const_mul dryM0OfM_poly 12) 4
  let fTot : ℕ → ℕ := fun M =>
    200 + 80 * M + 40 * fL M + 20 * fd M + 11 * fCap M + fCap M * fL M +
    fPar M + fd M * fLvl M + fLast M +
    (4 * M + 5) * (100 + 36 * fL M) +
    M * (60 * (fL M) ^ 2 + 50 * fL M + 10) + M * (20 * (4 * fL M + 8) + 100)
  have hfTotP : PolyNat fTot := by
    have h1 := PolyNat.add
      (PolyNat.add
        (PolyNat.add
          (PolyNat.add (PolyNat.add_const (PolyNat.const_mul PolyNat.id 80) 200) (PolyNat.const_mul hfLP 40))
          (PolyNat.const_mul (SubpolyNat.toPolyNat hfdSub) 20))
        (PolyNat.const_mul hfCapP 11))
      (PolyNat.mul hfCapP hfLP)
    have h2 := PolyNat.add (PolyNat.add hfParP (PolyNat.mul (SubpolyNat.toPolyNat hfdSub) hfLvlP)) hfLastP
    have h3 := PolyNat.mul (PolyNat.add_const (PolyNat.const_mul PolyNat.id 4) 5)
      (PolyNat.add_const (PolyNat.const_mul hfLP 36) 100)
    have h4 := PolyNat.mul PolyNat.id
      (PolyNat.add (PolyNat.const_mul (PolyNat.pow hfLP 2) 60) (PolyNat.add_const (PolyNat.const_mul hfLP 50) 10))
    have h5 := PolyNat.mul PolyNat.id
      (PolyNat.add_const (PolyNat.const_mul (PolyNat.add_const (PolyNat.const_mul hfLP 4) 8) 20) 100)
    exact PolyNat.mono (fun M => by
      dsimp only [fTot]
      have ha : 100 + 36 * fL M = 36 * fL M + 100 := by omega
      have hb : 60 * (fL M) ^ 2 + 50 * fL M + 10 = 60 * (fL M) ^ 2 + (50 * fL M + 10) := by omega
      rw [ha, hb]; omega)
      (PolyNat.add (PolyNat.add (PolyNat.add h1 h2) h3) (PolyNat.add h4 h5))
  refine ⟨fTot, hfTotP, fun source J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hL : L ≤ fL I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hGnEq : (namedInstance I).n = I.n := by simp [namedInstance, MGraph.n]
  have hInLe : I.n ≤ 2 * I.m + 2 := by
    have hIn : I.n = J.n + 1 := by
      simp [I, solverConnectedAugmented, connectedInitialInstance, instanceOfArrays,
        Circulation.toInstance]
    have hJmLe : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCap).1
    omega
  have hSum : (∑ i ∈ Finset.range cfg.P.d,
      ordLevelSpace L dryCapExp (dryCapLimit dryWitnessUsed J) (dryCoreInitSpace Psc J i)
        (levelM cfg.TP cfg.P i) cfg.N₀ (levelM cfg.TP cfg.P (i + 1))) ≤ fd I.m * fLvl I.m := by
    calc _ ≤ ∑ _ ∈ Finset.range cfg.P.d, fLvl I.m :=
          Finset.sum_le_sum fun i hi => hLvl J hJn hJm hCap i (Finset.mem_range.mp hi)
      _ = cfg.P.d * fLvl I.m := by simp
      _ ≤ fd I.m * fLvl I.m := Nat.mul_le_mul_right _ (hfd J hJn hJm hCap)
  have hArena : LinkCut.PathProg.arenaEnd 0 I.n L ≤
      (8 * I.m + 16) + (4 * I.m + 5) * (100 + 36 * fL I.m) := by
    unfold LinkCut.PathProg.arenaEnd LinkCut.PathProg.arenaNb LinkCut.PathProg.recW
      LinkCut.PathProg.treeLimbs
    have h1 : (13 + 9 * (4 * L + 8)) * (2 * I.n + 1) ≤ (100 + 36 * fL I.m) * (4 * I.m + 5) :=
      Nat.mul_le_mul (by omega) (by omega)
    rw [Nat.mul_comm (4 * I.m + 5)]
    omega
  have hEdgeRec : I.m * initEdgeRecordSpace L ≤ I.m * (60 * (fL I.m) ^ 2 + 50 * fL I.m + 10) := by
    apply Nat.mul_le_mul_left
    unfold initEdgeRecordSpace Num.fixedDivideSpace Num.integerDivideSpace Num.unsignedDivideSpace
    have hsq := Nat.pow_le_pow_left hL 2
    nlinarith only [hL, hsq]
  have hLinkSp : I.m * (20 * LinkCut.PathProg.treeLimbs L + 100) ≤
      I.m * (20 * (4 * fL I.m + 8) + 100) := by
    unfold LinkCut.PathProg.treeLimbs; exact Nat.mul_le_mul_left _ (by omega)
  unfold initConcreteSpace ordInitLevelsSpace initPostTailSpace initLinkChainSpace dynGraphSize
  dsimp only
  rw [hGnEq]
  have hPar' : dryParamSpace source J ≤ fPar I.m := hPar source J hJn hJm hCap
  have hLast' : dryLastSpace J ≤ fLast I.m := hLast J hJn hJm hCap
  have hd' : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
  have hCapEq : dryCapLimit dryWitnessUsed J = fCap I.m := rfl
  have hCapL : dryCapLimit dryWitnessUsed J * L ≤ fCap I.m * fL I.m := by
    rw [hCapEq]; exact Nat.mul_le_mul_left _ hL
  dsimp only [fTot]
  change 16 + (L + 1) + 6 + dryParamSpace source J + (4 + 7 * I.n + 9 * dryCapLimit dryWitnessUsed J) +
      (1 + 4 * I.n + 2 * dryCapLimit dryWitnessUsed J) + dryCapLimit dryWitnessUsed J * L +
      (4 * cfg.P.d + 4) + 18 + (cfg.P.d + 1) + (cfg.P.d + 1) +
      ((∑ i ∈ Finset.range cfg.P.d,
          ordLevelSpace L dryCapExp (dryCapLimit dryWitnessUsed J) (dryCoreInitSpace Psc J i)
            (levelM cfg.TP cfg.P i) cfg.N₀ (levelM cfg.TP cfg.P (i + 1))) + dryLastSpace J) +
      (4 * (cfg.P.d + 1) + 1) + 1 + 3 * I.m + LinkCut.PathProg.arenaEnd 0 I.n L +
      (I.m + 2 * I.n + 2 * I.n + I.m + I.m + I.m + 3 * L + I.m * initEdgeRecordSpace L +
        (6 * cfg.P.d + 4 + I.m * (20 * LinkCut.PathProg.treeLimbs L + 100))) ≤ _
  rw [hCapEq] at hCapL hSum ⊢
  linarith only [hPar', hLast', hd', hSum, hArena, hEdgeRec, hLinkSp, hInLe, hL, hCapL]

/-- `dryDeepSpace Psc J` is unconditionally bounded by a `PolyNat` function of `I.m`, closing the
op-1 restart space term via `dryDeepRestartSpace_le_bound` and `dryDeepRestartSpaceBound_poly`. -/
theorem dryDeepSpace_le_poly (Psc : DrySparseCorePieces) :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        dryDeepSpace Psc J ≤ f (solverConnectedAugmented J).m := by
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  obtain ⟨fLvl, hfLvlP, hLvl⟩ := dryDeepLevelSpace_le_poly Psc
  obtain ⟨fLast, hfLastP, hLast⟩ := dryLastSpace_le_poly
  let fRestart := dryDeepRestartSpaceBound Psc
  have hfRestartP : PolyNat fRestart := dryDeepRestartSpaceBound_poly Psc
  let fCap : ℕ → ℕ := fun M => 12 * dryM0OfM M + 4
  have hfCapP : PolyNat fCap := PolyNat.add_const (PolyNat.const_mul dryM0OfM_poly 12) 4
  let fTot : ℕ → ℕ := fun M =>
    20 * fd M + 20 + (5 + 11 * fCap M + 18 * (fCap M) ^ 2) + fRestart M +
    fd M * fLvl M + fLast M + 24 * dryM0OfM M +
    ((fd M + 1) * (4 * M + 4)) * (2 + (40 * (4 * dryLimbsOfM M + 8) + 10 * dryLimbsOfM M + 210))
  have hfTotP : PolyNat fTot := by
    have hfLP := SubpolyNat.toPolyNat dryLimbsOfM_subpoly
    have h1 := PolyNat.add_const (PolyNat.const_mul (SubpolyNat.toPolyNat hfdSub) 20) 20
    have h2 := PolyNat.add (PolyNat.add_const (PolyNat.const_mul hfCapP 11) 5)
      (PolyNat.const_mul (PolyNat.pow hfCapP 2) 18)
    have h3 := PolyNat.add (PolyNat.add hfRestartP (PolyNat.mul (SubpolyNat.toPolyNat hfdSub) hfLvlP)) hfLastP
    have h4 := PolyNat.const_mul dryM0OfM_poly 24
    have h5 := PolyNat.mul
      (PolyNat.mul (PolyNat.add_const (SubpolyNat.toPolyNat hfdSub) 1)
        (PolyNat.add_const (PolyNat.const_mul PolyNat.id 4) 4))
      (PolyNat.add_const
        (PolyNat.add
          (PolyNat.const_mul (PolyNat.add_const (PolyNat.const_mul hfLP 4) 8) 40)
          (PolyNat.add_const (PolyNat.const_mul hfLP 10) 210)) 2)
    exact PolyNat.mono (fun M => by
      dsimp only [fTot]
      have h5eq : 2 + (40 * (4 * dryLimbsOfM M + 8) + 10 * dryLimbsOfM M + 210) =
          40 * (4 * dryLimbsOfM M + 8) + (10 * dryLimbsOfM M + 210) + 2 := by omega
      rw [h5eq]
      omega)
      (PolyNat.add (PolyNat.add (PolyNat.add (PolyNat.add h1 h2) h3) h4) h5)
  refine ⟨fTot, hfTotP, fun J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hInLe : I.n ≤ 2 * I.m + 2 := by
    have hIn : I.n = J.n + 1 := by
      simp [I, solverConnectedAugmented, connectedInitialInstance, instanceOfArrays,
        Circulation.toInstance]
    have hJmLe : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCap).1
    omega
  have hFCap : dryDeepFCap J ≤ 5 + 11 * fCap I.m + 18 * (fCap I.m) ^ 2 := by
    unfold dryDeepFCap dynGraphSize; dsimp only [fCap]
    have : dryCapLimit dryWitnessUsed J = 12 * dryM0OfM I.m + 4 := rfl
    rw [this]; omega
  have hIntCap : dryDeepIntCapMax J ≤ 8 * dryM0OfM I.m := by
    unfold dryDeepIntCapMax Ordered.alg2NameBase intRebuildThreshold
    dsimp only
    have hM0ge : I.m ≤ cfg.P.M₀ := le_max_left _ _
    have hThr : cfg.P.M₀ / (cfg.P.k ^ (0 + 1) * Nat.clog 2 (cfg.N₀ + 2) ^ 2) ≤ cfg.P.M₀ :=
      Nat.div_le_self _ _
    have hM0_2 : 2 ≤ cfg.P.M₀ :=
      (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed).trans (le_max_right _ _)
    have hEqM0 : cfg.P.M₀ = dryM0OfM I.m := rfl
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
  have hSum : (Finset.range cfg.P.d).sum (dryDeepLevelSpace Psc J) ≤ fd I.m * fLvl I.m := by
    calc _ ≤ ∑ _ ∈ Finset.range cfg.P.d, fLvl I.m :=
          Finset.sum_le_sum fun j hj => hLvl J hJn hJm hCap j (Finset.mem_range.mp hj)
      _ = cfg.P.d * fLvl I.m := by simp
      _ ≤ fd I.m * fLvl I.m := Nat.mul_le_mul_right _ (hfd J hJn hJm hCap)
  have hFor : dryDeepForestEdgeCap J * (2 + wireTreeSyncEditSpace L) ≤
      ((fd I.m + 1) * (4 * I.m + 4)) *
        (2 + (40 * (4 * dryLimbsOfM I.m + 8) + 10 * dryLimbsOfM I.m + 210)) := by
    unfold dryDeepForestEdgeCap wireTreeSyncEditSpace LinkCut.PathProg.treeLimbs
    have hD1 : cfg.P.d + 1 ≤ fd I.m + 1 := Nat.add_le_add_right (hfd J hJn hJm hCap) 1
    have h2n : 2 * I.n ≤ 4 * I.m + 4 := by omega
    have hCapFor : 2 * (cfg.P.d + 1) * I.n ≤ (fd I.m + 1) * (4 * I.m + 4) := by
      calc 2 * (cfg.P.d + 1) * I.n = (cfg.P.d + 1) * (2 * I.n) := by ring
        _ ≤ (fd I.m + 1) * (4 * I.m + 4) := Nat.mul_le_mul hD1 h2n
    exact Nat.mul_le_mul hCapFor (by omega)
  unfold dryDeepSpace
  dsimp only [fTot]
  have hd' := hfd J hJn hJm hCap
  have hR' : dryDeepRestartSpace Psc J ≤ fRestart I.m :=
    dryDeepRestartSpace_le_bound Psc J hJn hJm hCap
  have hLast' := hLast J hJn hJm hCap
  linarith only [hFCap, hIntCap, hSum, hFor, hd', hR', hLast']

end MinCostFlow.Final.DryRun

end
