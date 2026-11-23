module

public import MinCostFlow.Final.AssemblyDryRunSCInitAsymp
public import MinCostFlow.Final.AssemblyDryRunSCSizes
import Mathlib.Tactic

/-!
# `SubpolyNat` bounds for `deepShiftFixedBound`, `deepShiftToolMulBound`, and `dryToolMul`

Proves the uniform `SubpolyNat` bounds on the deep-shift fixed cost
`deepShiftFixedBound`, deep-shift tool multiplier `deepShiftToolMulBound`, and full `dryToolMul`,
together with the size bound structures `DryOpenSizeBounds` and `DrySelectRebuildSizeBounds`
and shared arithmetic helpers used by `Final/AssemblyDryRunSCBounds.lean`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Open size bounds for select, chain core, and select rebuild overhead -/

/-- Bounds on the parameter sizes `openSz` (`selectRoute` and `ordChainCore`) needed to construct
`dryInnerBounds : OrdSolverInnerBounds` without circularity on `B`. -/
structure DryOpenSizeBounds (openSz : DryOpenSizes) : Prop where
  /-- Monotonicity of `openSz.coreSpace` in the batch length. -/
  hCoreSpaceMono :
    ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
      Monotone (openSz.coreSpace source J)
  /-- `PolyNat` bounds on `selectSpace` and `coreSpace (2 * I.m)` (heap-independent; op `0` of
  `drySCAlloc` is bounded by `drySCOp0Bound`, which is monotone and `PolyNat` via
  `drySCOp0Bound_mono` and `drySCOp0Bound_poly`). -/
  hSpacePoly :
    ∃ (fSelSp fCoreSp : ℕ → ℕ),
      PolyNat fSelSp ∧ PolyNat fCoreSp ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let m := (solverConnectedAugmented J).m
        openSz.selectSpace source J ≤ fSelSp m ∧
        openSz.coreSpace source J (2 * m) ≤ fCoreSp m
  /-- `SubpolyNat` bounds on `selectBudget`, `maxEdges`, `maxPaths`, and linear `coreFixed`. -/
  hRateSubpoly :
    ∃ (fSelBud fME fMP fRho0 fRho1 : ℕ → ℕ),
      SubpolyNat fSelBud ∧ SubpolyNat fME ∧ SubpolyNat fMP ∧
      SubpolyNat fRho0 ∧ SubpolyNat fRho1 ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let m := (solverConnectedAugmented J).m
        openSz.selectBudget source J ≤ fSelBud m ∧
        openSz.maxEdges source J ≤ fME m ∧
        openSz.maxPaths source J ≤ fMP m ∧
        ∀ u ≤ 2 * m, openSz.coreFixed source J u ≤ fRho0 m + fRho1 m * u
  /-- `SubpolyNat` bounds on the extra multipliers `coreToolMul` and `coreTreeMul`. -/
  hCoreMulSubpoly :
    ∃ (fTool fTree : ℕ → ℕ), SubpolyNat fTool ∧ SubpolyNat fTree ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let m := (solverConnectedAugmented J).m
        openSz.coreToolMul source J ≤ fTool m ∧ openSz.coreTreeMul source J ≤ fTree m

/-- Bounds on the chain-core fields `coreSz : DryCoreOpenSizes` (`coreSpace` monotone
and `PolyNat`, `coreFixed` linear with `SubpolyNat` coefficients, `coreToolMul` and `coreTreeMul`
`SubpolyNat`). -/
structure DryCoreOpenSizeBounds (coreSz : DryCoreOpenSizes) : Prop where
  hCoreSpaceMono :
    ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
      Monotone (coreSz.coreSpace source J)
  hCoreSpacePoly :
    ∃ fCoreSp : ℕ → ℕ, PolyNat fCoreSp ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let m := (solverConnectedAugmented J).m
        coreSz.coreSpace source J (2 * m) ≤ fCoreSp m
  hCoreFixedSubpoly :
    ∃ (fRho0 fRho1 : ℕ → ℕ), SubpolyNat fRho0 ∧ SubpolyNat fRho1 ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let m := (solverConnectedAugmented J).m
        ∀ u ≤ 2 * m, coreSz.coreFixed source J u ≤ fRho0 m + fRho1 m * u
  hCoreMulSubpoly :
    ∃ (fTool fTree : ℕ → ℕ), SubpolyNat fTool ∧ SubpolyNat fTree ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let m := (solverConnectedAugmented J).m
        coreSz.coreToolMul source J ≤ fTool m ∧ coreSz.coreTreeMul source J ≤ fTree m

/-- Named `PolyNat` (space) and `SubpolyNat` (cost) bounds on the select-region, select-rebuild,
and re-embedding terms of `DrySelectRebuildSizes` (`initSelectSpace`, `initSelectFixed`,
`termSelectSpace`, `deepSelectSpace`, `deepSelectFixed`, `termSelectFixed`, `keyCost`, `cReemb`,
`selectToolMulExtra`). -/
structure DrySelectRebuildSizeBounds (selSz : DrySelectRebuildSizes) : Prop where
  hInitSelectSpacePoly :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        selSz.initSelectSpace source J ≤ f (solverConnectedAugmented J).m
  hInitSelectFixedSub :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        selSz.initSelectFixed source J ≤
          ((solverConnectedAugmented J).m + 1) * f (solverConnectedAugmented J).m
  hTermSelectSpacePoly :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        selSz.termSelectSpace source J ≤ f (solverConnectedAugmented J).m
  hDeepSelectSpacePoly :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        selSz.deepSelectSpace source J ≤ f (solverConnectedAugmented J).m
  hDeepSelectFixedSub :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        selSz.deepSelectFixed source J ≤ f (solverConnectedAugmented J).m
  hTermSelectFixedSub :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        selSz.termSelectFixed source J ≤ f (solverConnectedAugmented J).m
  hKeyCostSub :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        selSz.keyCost source J ≤ f (solverConnectedAugmented J).m
  hCReembSub :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        selSz.cReemb source J ≤ f (solverConnectedAugmented J).m
  hSelectToolMulExtraSub :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        selSz.selectToolMulExtra source J ≤ f (solverConnectedAugmented J).m

/-- Bounds on the Init select fields `initSel : DryInitSelectSizes`. -/
structure DryInitSelectSizeBounds (initSel : DryInitSelectSizes) : Prop where
  hInitSelectSpacePoly :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        initSel.initSelectSpace source J ≤ f (solverConnectedAugmented J).m
  hInitSelectFixedSub :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        initSel.initSelectFixed source J ≤
          ((solverConnectedAugmented J).m + 1) * f (solverConnectedAugmented J).m

/-- Bounds on the shift select fields `shiftSel : DryShiftSelectSizes`. -/
structure DryShiftSelectSizeBounds (shiftSel : DryShiftSelectSizes) : Prop where
  hTermSelectSpacePoly :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        shiftSel.termSelectSpace source J ≤ f (solverConnectedAugmented J).m
  hDeepSelectSpacePoly :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        shiftSel.deepSelectSpace source J ≤ f (solverConnectedAugmented J).m
  hDeepSelectFixedSub :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        shiftSel.deepSelectFixed source J ≤ f (solverConnectedAugmented J).m
  hTermSelectFixedSub :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        shiftSel.termSelectFixed source J ≤ f (solverConnectedAugmented J).m

/-- Zero select-rebuild overhead trivially satisfies `DrySelectRebuildSizeBounds`. -/
theorem dryZeroSelectRebuildSizeBounds : DrySelectRebuildSizeBounds dryZeroSelectRebuildSizes where
  hInitSelectSpacePoly := ⟨fun _ => 0, PolyNat.const 0, fun _ _ _ _ _ => le_rfl⟩
  hInitSelectFixedSub := ⟨fun _ => 0, SubpolyNat.const 0, fun _ _ _ _ _ => Nat.zero_le _⟩
  hTermSelectSpacePoly := ⟨fun _ => 0, PolyNat.const 0, fun _ _ _ _ _ => le_rfl⟩
  hDeepSelectSpacePoly := ⟨fun _ => 0, PolyNat.const 0, fun _ _ _ _ _ => le_rfl⟩
  hDeepSelectFixedSub := ⟨fun _ => 0, SubpolyNat.const 0, fun _ _ _ _ _ => le_rfl⟩
  hTermSelectFixedSub := ⟨fun _ => 0, SubpolyNat.const 0, fun _ _ _ _ _ => le_rfl⟩
  hKeyCostSub := ⟨fun _ => 0, SubpolyNat.const 0, fun _ _ _ _ _ => le_rfl⟩
  hCReembSub := ⟨fun _ => 0, SubpolyNat.const 0, fun _ _ _ _ _ => le_rfl⟩
  hSelectToolMulExtraSub := ⟨fun _ => 0, SubpolyNat.const 0, fun _ _ _ _ _ => le_rfl⟩

/-! ## 2. Shared arithmetic helpers -/

theorem dry_clog2_le_log2_add_one (n : ℕ) : Nat.clog 2 n ≤ Nat.log 2 n + 1 := by
  by_cases hn : n = 0
  · subst hn; simp
  · exact (Nat.clog_le_iff_le_pow (by decide)).mpr (Nat.lt_pow_succ_log_self (by decide) n).le

theorem dryGn_le_two_mul_m_add_two (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1)
    (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e) :
    (namedInstance (solverConnectedAugmented J)).n ≤ 2 * (solverConnectedAugmented J).m + 2 := by
  have hGn : (namedInstance (solverConnectedAugmented J)).n = (solverConnectedAugmented J).n := by
    simp [namedInstance, MGraph.n]
  have hIn : (solverConnectedAugmented J).n = J.n + 1 := by
    simp [solverConnectedAugmented, connectedInitialInstance, instanceOfArrays, Circulation.toInstance]
  have hJmLe : J.m ≤ (solverConnectedAugmented J).m := (solverConnectedAugmented_size J hJn hJm hCap).1
  omega

theorem dryNfMax_le_two_mul_M0 (J : Circulation) :
    let I := solverConnectedAugmented J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    Ordered.alg2NameBase cfg (namedInstance I) + intRebuildThreshold cfg.P cfg.N₀ 0 ≤
      2 * dryM0OfM I.m := by
  dsimp only
  unfold Ordered.alg2NameBase intRebuildThreshold
  set I := solverConnectedAugmented J
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hM0ge : I.m ≤ cfg.P.M₀ := le_max_left _ _
  have hM0_2 : 2 ≤ cfg.P.M₀ :=
    (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed).trans (le_max_right _ _)
  have hThr : cfg.P.M₀ / (cfg.P.k ^ (0 + 1) * Nat.clog 2 (cfg.N₀ + 2) ^ 2) ≤ cfg.P.M₀ :=
    Nat.div_le_self _ _
  have hBase : max ((namedInstance I).E.sup id + 1) cfg.P.M₀ ≤ cfg.P.M₀ := by
    apply max_le _ le_rfl
    have hSup : (namedInstance I).E.sup id + 1 ≤ max 1 I.m := by
      rcases Nat.eq_zero_or_pos I.m with h0 | hpos
      · have : (namedInstance I).E = ∅ := by simp [namedInstance, h0]
        rw [this]; simp
      · have : (namedInstance I).E.sup id ≤ I.m - 1 :=
          Finset.sup_le fun e he => by
            change e ≤ I.m - 1
            simp [namedInstance] at he; omega
        omega
    omega
  change max ((namedInstance I).E.sup id + 1) cfg.P.M₀ +
      cfg.P.M₀ / (cfg.P.k ^ (0 + 1) * Nat.clog 2 (cfg.N₀ + 2) ^ 2) ≤ 2 * cfg.P.M₀
  omega

theorem dry_chainRebuildCap_eq_mul (cfg : Alg2Config) (C_fac : ℕ) (rc : ℕ → ℕ) :
    chainRebuildCap cfg C_fac rc = C_fac * chainRebuildCap cfg 1 rc := by
  unfold chainRebuildCap; simp only [one_mul]

theorem dryLevelMd_le_two_pow_dryKOfM (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1)
    (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e) :
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    levelM cfg.TP cfg.P cfg.P.d ≤ 2 ^ dryKOfM (solverConnectedAugmented J).m :=
  le_of_lt (lt_of_le_of_lt (Nat.le_succ _)
    (dryWitnessUsed_lastCanonConst_and_levelM_lt J hJn hJm hCap).2)

/-! ## 3. `SubpolyNat` bounds on `deepShiftFixedBound`, `deepShiftToolMulBound`, and `dryToolMul` -/

/-- `deepShiftFixedBound` at `(levelM 0, N₀, d, dryLastMult)` is unconditionally `SubpolyNat`. -/
theorem deepShiftFixedBound_le_subpoly (Psc : DrySparseCorePieces) :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
        deepShiftFixedBound PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d (dryLastMult J) ≤
          f (solverConnectedAugmented J).m := by
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  obtain ⟨fLM, hfLMSub, hfLM⟩ := dryLevelM_le_subpoly
  obtain ⟨fLast, hfLastSub, hfLast⟩ := dryLastMult_le_subpoly
  let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
  let fArgPoly : PolyNat (fun M => (M + 1) * fLM M + 4 * dryM0OfM M) :=
    PolyNat.add (PolyNat.mul (PolyNat.add_const PolyNat.id 1) (SubpolyNat.toPolyNat hfLMSub))
      (PolyNat.const_mul dryM0OfM_poly 4)
  let fB0 : ℕ → ℕ := fun M => (Nat.log 2 (((M + 1) * fLM M + 4 * dryM0OfM M) + 2) + 1) ^ 2
  have hfB0Sub : SubpolyNat fB0 := SubpolyNat.pow (subpolyNat_log_of_poly fArgPoly) 2
  let fTot : ℕ → ℕ := fun M =>
    PscP.mul + 4 * PscP.mul * fB0 M + 2 * PscP.readout +
      fd M * (5 * PscP.mul + 4 * PscP.mul * fB0 M + 2 * PscP.readout + 475) +
      fLast M + 2 * fd M * (PscP.readout + 48) + 210 * (fd M + 1) + 1580
  have hfTotSub : SubpolyNat fTot := by
    have h1 := SubpolyNat.add_const (SubpolyNat.add_const (SubpolyNat.const_mul hfB0Sub (4 * PscP.mul)) PscP.mul) (2 * PscP.readout)
    have h2 := SubpolyNat.mul hfdSub
      (SubpolyNat.add_const (SubpolyNat.add_const (SubpolyNat.const_mul hfB0Sub (4 * PscP.mul)) (5 * PscP.mul)) (2 * PscP.readout + 475))
    have h3 := SubpolyNat.add hfLastSub
      (SubpolyNat.add (SubpolyNat.const_mul hfdSub (2 * (PscP.readout + 48)))
        (SubpolyNat.add_const (SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) 210) 1580))
    exact SubpolyNat.mono (fun M => by
        dsimp only [fTot]
        have heq1 : 2 * fd M * (PscP.readout + 48) = 2 * (PscP.readout + 48) * fd M := by ring
        have heq2 : 5 * PscP.mul + 4 * PscP.mul * fB0 M + 2 * PscP.readout + 475 =
            4 * PscP.mul * fB0 M + 5 * PscP.mul + (2 * PscP.readout + 475) := by omega
        rw [heq1, heq2]; omega)
      (SubpolyNat.add (SubpolyNat.add h1 h2) h3)
  refine ⟨fTot, hfTotSub, fun J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hM0 : levelM cfg.TP cfg.P 0 ≤ (I.m + 1) * fLM I.m := hfLM J hJn hJm hCap 0 (Nat.zero_le _)
  have hN0 : cfg.N₀ = 4 * dryM0OfM I.m := rfl
  have hB0 : SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ ≤ fB0 I.m := by
    unfold SparseCore.bundleLogFactor
    dsimp only [fB0]
    exact Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right (b := 2) (by omega)) 1) 2
  have hd := hfd J hJn hJm hCap
  have hL := hfLast J hJn hJm hCap
  have hmul1 : 4 * PscP.mul * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ ≤
      4 * PscP.mul * fB0 I.m := Nat.mul_le_mul_left _ hB0
  have hmul2 : cfg.P.d * (5 * PscP.mul + 4 * PscP.mul * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ +
        2 * PscP.readout + 475) ≤
      fd I.m * (5 * PscP.mul + 4 * PscP.mul * fB0 I.m + 2 * PscP.readout + 475) :=
    Nat.mul_le_mul hd (by omega)
  have hmul3 : 2 * cfg.P.d * (PscP.readout + 48) ≤ 2 * fd I.m * (PscP.readout + 48) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hd)
  unfold deepShiftFixedBound
  dsimp only [fTot]
  linarith only [hmul1, hmul2, hmul3, hL, hd]

/-- `deepShiftToolMulBound` at `(L, levelM 0, N₀, d, dryLastMult)` is unconditionally `SubpolyNat`. -/
theorem deepShiftToolMulBound_le_subpoly (Psc : DrySparseCorePieces) :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let L := ipmQualityLimbs I.m V k
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
        deepShiftToolMulBound L dryCapExp PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d (dryLastMult J) ≤
          f I.m := by
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  obtain ⟨fLM, hfLMSub, hfLM⟩ := dryLevelM_le_subpoly
  obtain ⟨fLast, hfLastSub, hfLast⟩ := dryLastMult_le_subpoly
  let PscP := drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
  let cLw := dryCapExp + sparseCoreReadout2LimbConst
  let fArgPoly : PolyNat (fun M => (M + 1) * fLM M + 4 * dryM0OfM M) :=
    PolyNat.add (PolyNat.mul (PolyNat.add_const PolyNat.id 1) (SubpolyNat.toPolyNat hfLMSub))
      (PolyNat.const_mul dryM0OfM_poly 4)
  let fLw : ℕ → ℕ := fun M => dryLimbsOfM M + cLw * (Nat.log 2 (((M + 1) * fLM M + 4 * dryM0OfM M) + 2) + 1)
  have hfLwSub : SubpolyNat fLw :=
    SubpolyNat.add dryLimbsOfM_subpoly (SubpolyNat.const_mul (subpolyNat_log_of_poly fArgPoly) cLw)
  let fEdgeC : ℕ → ℕ := fun M => 1400 * (fLw M) ^ 2 + 2100 * fLw M + 850
  have hfEdgeCSub : SubpolyNat fEdgeC :=
    SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.const_mul (SubpolyNat.pow hfLwSub 2) 1400)
      (SubpolyNat.const_mul hfLwSub 2100)) 850
  let fTot : ℕ → ℕ := fun M =>
    fLast M + (5 * PscP.mul + fEdgeC M + 170 * (fd M + 1) + 610)
  have hfTotSub : SubpolyNat fTot :=
    SubpolyNat.add hfLastSub
      (SubpolyNat.add_const (SubpolyNat.add
        (SubpolyNat.mono (fun M => by omega) (SubpolyNat.add_const hfEdgeCSub (5 * PscP.mul)))
        (SubpolyNat.const_mul (SubpolyNat.add_const hfdSub 1) 170)) 610)
  refine ⟨fTot, hfTotSub, fun J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hM0 : levelM cfg.TP cfg.P 0 ≤ (I.m + 1) * fLM I.m := hfLM J hJn hJm hCap 0 (Nat.zero_le _)
  have hN0 : cfg.N₀ = 4 * dryM0OfM I.m := rfl
  have hLw : ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀ ≤ fLw I.m := by
    unfold ordLevelLwMax
    dsimp only [fLw, cLw]
    exact Nat.add_le_add hL (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.log_mono_right (b := 2) (by omega)) 1))
  have hEC : wireCoreLenEdgeCost (ordLevelLwMax L dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀) ≤ fEdgeC I.m := by
    unfold wireCoreLenEdgeCost
    dsimp only [fEdgeC]
    have hsq := Nat.pow_le_pow_left hLw 2
    nlinarith only [hLw, hsq]
  have hd := hfd J hJn hJm hCap
  have hLast' := hfLast J hJn hJm hCap
  unfold deepShiftToolMulBound
  dsimp only [fTot]
  exact max_le (by linarith only [hLast']) (by linarith only [hEC, hd])

/-- `dryToolMul Psc selSz source J` is `SubpolyNat` in `I.m`. -/
theorem dryToolMul_le_subpoly (Psc : DrySparseCorePieces) (selSz : DrySelectRebuildSizes)
    (hSel : DrySelectRebuildSizeBounds selSz) :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        dryToolMul Psc selSz source J ≤ f (solverConnectedAugmented J).m := by
  obtain ⟨fDeepTM, hfDeepTMSub, hDeepTM⟩ := deepShiftToolMulBound_le_subpoly Psc
  obtain ⟨fKey, hfKeySub, hKey⟩ := hSel.hKeyCostSub
  obtain ⟨fReemb, hfReembSub, hReemb⟩ := hSel.hCReembSub
  obtain ⟨fExtra, hfExtraSub, hExtra⟩ := hSel.hSelectToolMulExtraSub
  let Pmul := (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).mul
  let fTot : ℕ → ℕ := fun M => (fDeepTM M + Pmul) + fKey M * (fReemb M + 2) + fExtra M
  have hfTotSub : SubpolyNat fTot :=
    SubpolyNat.add (SubpolyNat.add (SubpolyNat.add_const hfDeepTMSub Pmul)
      (SubpolyNat.mul hfKeySub (SubpolyNat.add_const hfReembSub 2))) hfExtraSub
  refine ⟨fTot, hfTotSub, fun source J hJn hJm hCap => ?_⟩
  unfold dryToolMul
  dsimp only [fTot]
  have h1 := hDeepTM J hJn hJm hCap
  have h2 := Nat.mul_le_mul (hKey source J hJn hJm hCap)
    (Nat.add_le_add_right (hReemb source J hJn hJm hCap) 2)
  have h3 := hExtra source J hJn hJm hCap
  have hmax : max (deepShiftToolMulBound _ _ _ _ _ _ _) Pmul ≤
      fDeepTM (solverConnectedAugmented J).m + Pmul :=
    max_le (h1.trans (Nat.le_add_right _ _)) (Nat.le_add_left _ _)
  linarith only [hmax, h2, h3]

end MinCostFlow.Final.DryRun

end
