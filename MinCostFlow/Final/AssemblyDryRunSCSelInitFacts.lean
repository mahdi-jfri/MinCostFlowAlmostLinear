module

public import MinCostFlow.Final.WireSelectDryFits
public import MinCostFlow.Final.WireInitSelectSizes
public import MinCostFlow.MinRatio.OrdSolverCapDeposit
import MinCostFlow.Final.AssemblyDryRunSCDeepGrid
import MinCostFlow.Final.AssemblyDryRunSCFits
import MinCostFlow.Final.AssemblyDryRunSCConnected
import MinCostFlow.MinRatio.OrdSolverToolCredit
import MinCostFlow.MinRatio.OrdSolverReached
import MinCostFlow.MinRatio.OrdSolverImplementsSel
import MinCostFlow.MinRatio.ShiftDeepModelFacts
import MinCostFlow.LastLevelProgram.RepresentativeGraph
import Mathlib.Tactic

/-!
# Initial-state mathematical invariants for select-aware Init (`AssemblyDryRunSCSelInitFacts`)

Discharges the pure mathematical / fixed-point initial-state hypotheses of
`solverInitWiredSel_runs` (`MinRatio/SelectInitWired.lean`) on `s0 = algorithm2_init cfg
(namedInstance I) grad₀ len₀` under `IPM.LengthsWithin`, `IsDyadicGrid`, and `|grad₀ e| ≤ 2^E`:
* `dryInitSel_hLenFitLast`: proves `hLenFitLast` at `pLast = dryLastStretchP J`.
* `dryInitSel_modelFacts`: proves `SelectModelInv`, `OrdSolverReached`, `totalRuntime ≤
  chainRebuildCap`, `hLastBr`, `hVcap`/`hEcap`/`hFV`/`hFE`/`hGm`/`hFm`/`hFn`, `hLvlM`, `hN0`,
  `hEmbSlot`, `hPhiBdStep`, `hFitPhi`, and `CandidateKeysFit`.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

private lemma fits_of_nonneg_mul_pow_lt {L Q : ℕ} {z : ℤ} {r : ℝ}
    (hcast : (z : ℝ) / (2 : ℝ) ^ Q = r) (hnn : 0 ≤ r)
    (hbd : r * (2 : ℝ) ^ Q < (Num.capacity 4 L : ℝ) / 2) :
    Num.Fits 4 L z := by
  have hQ : (0 : ℝ) < (2 : ℝ) ^ Q := by positivity
  have hzR : (z : ℝ) = r * (2 : ℝ) ^ Q := by rw [← hcast, div_mul_cancel₀ _ hQ.ne']
  have hz0 : (0 : ℝ) ≤ (z : ℝ) := by rw [hzR]; exact mul_nonneg hnn hQ.le
  have hlt2 : 2 * (z : ℝ) < (Num.capacity 4 L : ℝ) := by linarith
  have hz_nn : (0 : ℤ) ≤ z := by exact_mod_cast hz0
  have h2z_lt : 2 * z < (Num.capacity 4 L : ℤ) := by exact_mod_cast hlt2
  unfold Num.Fits
  have hcapPos : (0 : ℤ) ≤ (Num.capacity 4 L : ℤ) := Nat.cast_nonneg _
  omega

private lemma roundStretch_on_grid_le {pw pLast : ℕ} (hle : pw ≤ pLast) (s : ℝ) :
    ∃ wInt : ℤ, (wInt : ℝ) / (2 : ℝ) ^ pLast = roundStretch pw s := by
  refine ⟨(-⌊(-s) * (2 : ℝ) ^ pw⌋) * (2 : ℤ) ^ (pLast - pw), ?_⟩
  unfold roundStretch Num.dyadicFloor
  push_cast
  have hpow : (2 : ℝ) ^ pLast = (2 : ℝ) ^ pw * (2 : ℝ) ^ (pLast - pw) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  rw [hpow]
  have h1 : (2 : ℝ) ^ (pLast - pw) ≠ 0 := by positivity
  field_simp [h1]

/-- Discharges `hLenFitLast` for `s0 = algorithm2_init cfg (namedInstance I) grad₀ len₀` at
`pLast = dryLastStretchP J`. -/
theorem dryInitSel_hLenFitLast
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    (grad₀ len₀ : ℕ → ℝ)
    (hLenWithin :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      IPM.LengthsWithin (namedInstance I) (ipmQualityRangeExponent I.m V k) len₀)
    (hGrid :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      IsDyadicGrid (namedInstance I) (ipmQualityPrecision I.m V k) len₀) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let P := ipmQualityPrecision I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let s0 := Chain.Ordered.algorithm2_init cfg (namedInstance I) grad₀ len₀
    let pLast := dryLastStretchP J
    ∀ e ∈ (s0.chain.G cfg.P.d).E,
      (∃ q0 : ℤ, Num.Fits 4 L (q0 * (2 : ℤ) ^ pLast) ∧
        (q0 : ℝ) / (2 : ℝ) ^ P = s0.chain.toTreeChain.chainLen s0.chain.ℓ cfg.P.d e) ∧
      ∃ q : ℤ, Num.Fits 4 L q ∧
        (q : ℝ) / (2 : ℝ) ^ (P + pLast) =
          s0.chain.toTreeChain.chainLen s0.chain.ℓ (cfg.P.d + 1) e := by
  intro I V k L P cfg s0 pLast e he
  let E := ipmQualityRangeExponent I.m V k
  have hVcfg := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hGV : (namedInstance I).IsValid :=
    namedInstance_valid I (connectedInitialInstance_valid J.toInstance (V : ℤ) J.toInstance_valid)
  have hIm1 : 1 ≤ I.m := lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap).1
  have hEΨ : (E : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  have hlPos : ∀ f ∈ (namedInstance I).E, 0 < len₀ f := fun f hf =>
    lt_of_lt_of_le (by positivity) (hLenWithin f hf).1
  have hℓRange : Chain.Ordered.LenInRange (max 0 cfg.Ψ) (namedInstance I) len₀ := by
    intro f hf
    have hlog := ((abs_log_le_of_two_pow_bounds (hLenWithin f hf).1 (hLenWithin f hf).2).trans hEΨ).trans
      (le_max_right 0 cfg.Ψ)
    rw [abs_le] at hlog
    exact ⟨by simpa [Real.exp_log (hlPos f hf)] using Real.exp_le_exp.mpr hlog.1,
      by simpa [Real.exp_log (hlPos f hf)] using Real.exp_le_exp.mpr hlog.2⟩
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of
    (le_max_left dryWitnessUsed.M_thresh _) (le_max_right dryWitnessUsed.M_thresh _)
    (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed) J hJn hJm hCap
  have hmG : (namedInstance I).m ≤ cfg.P.M₀ := by rw [namedInstance_m]; exact le_max_left _ _
  have hnG : (namedInstance I).n ≤ cfg.N₀ := by
    have hInEq : (namedInstance I).n = I.n := by simp [namedInstance, MGraph.n]
    rw [hInEq]; exact hIn
  have hInit := Chain.Ordered.initialize_preserves_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hVcfg.hTP hVcfg.hLP hVcfg.hT hVcfg.hL hVcfg.hγM₀ hVcfg.hγk (namedInstance I) len₀ grad₀
    hGV hmG hnG hℓRange
  have hbd := drySC_chainLen_bounds J hJn hJm hCap len₀ grad₀ hLenWithin cfg.P.d le_rfl
  obtain ⟨q0, hq0Eq⟩ := hbd.2.2.2.2 hGrid e he
  have hExp : cfg.P.d * (3 * I.m.size + 12) ≤ E :=
    chainLen_exponent_le_rangeExponent I.m V (concreteQualityBudgetWithLast dryWitnessUsed)
      hIm1 cfg.P.hM₀
  have hpLastLe : pLast ≤ 40 * E := by
    have h1 := dryLastStretchP_le_forty_rangeExponent J hJn hJm hCap
    have hmono : (I.m + 1).size ≤ (max I.m (levelM cfg.TP cfg.P cfg.P.d) + 1).size :=
      Nat.size_le_size (Nat.add_le_add_right (le_max_left _ _) 1)
    dsimp only [pLast, dryLastStretchP, E, I, V, k, cfg] at h1 hmono ⊢
    omega
  have h4L : P + 92 * E + 12 * I.m.size + 1480 ≤ 4 * L := by
    dsimp only [L, P, E, ipmQualityLimbs, ipmQualityPrecision, ipmQualityErrorBits]
    omega
  have hLenD_pos : 0 < s0.chain.toTreeChain.chainLen len₀ cfg.P.d e :=
    lt_of_lt_of_le (by positivity) (hbd.2.2.2.1 e he).1
  have hLenD_le : s0.chain.toTreeChain.chainLen len₀ cfg.P.d e ≤ (2 : ℝ) ^ (2 * E) := by
    have hexpLe : E + cfg.P.d * (3 * I.m.size + 12) ≤ 2 * E := by
      dsimp only [E, I, V, k, cfg] at hExp ⊢; omega
    exact (hbd.2.2.2.1 e he).2.trans (pow_le_pow_right₀ (by norm_num) hexpLe)
  have hCap4Eq : (Num.capacity 4 L : ℝ) = (2 : ℝ) ^ (4 * L) := by
    rw [Num.capacity, Num.base, ← pow_mul]
    push_cast; rfl
  have hFit0 : Num.Fits 4 L (q0 * (2 : ℤ) ^ pLast) := by
    refine fits_of_nonneg_mul_pow_lt (Q := P + pLast) ?_ hLenD_pos.le ?_
    · push_cast
      rw [pow_add, mul_div_mul_right _ _ (by positivity)]
      exact hq0Eq
    · have h1 : s0.chain.toTreeChain.chainLen len₀ cfg.P.d e * (2 : ℝ) ^ (P + pLast) ≤
          (2 : ℝ) ^ (2 * E) * (2 : ℝ) ^ (P + 40 * E) :=
        mul_le_mul hLenD_le (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity) (by positivity)
      have h2 : (2 : ℝ) ^ (2 * E) * (2 : ℝ) ^ (P + 40 * E) = (2 : ℝ) ^ (P + 42 * E) := by
        rw [← pow_add]; exact congrArg ((2 : ℝ) ^ ·) (by omega)
      have h3 : (2 : ℝ) ^ (P + 42 * E) * 2 = (2 : ℝ) ^ (P + 42 * E + 1) := (pow_succ 2 _).symm
      have h4 : (2 : ℝ) ^ (P + 42 * E + 1) < (2 : ℝ) ^ (4 * L) :=
        pow_lt_pow_right₀ (by norm_num) (by omega)
      rw [hCap4Eq, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith
  have hGdM : (s0.chain.G cfg.P.d).m ≤ I.m :=
    (Finset.card_le_card hbd.2.2.1).trans (namedInstance_m I).le
  have hLastEq : s0.chain.lastLSFs =
      (dryLastTool.build (s0.chain.G cfg.P.d)
        (s0.chain.toTreeChain.chainLen len₀ cfg.P.d)).2 := by
    have hEq : ToolInitOrdEqOnE cfg.T :=
      sparseCoreBundleRestartToolMachWith_initOrdEqOnE _ _ _ _ _ _
    have hFacts := ordAlgorithm1_initialize_level_facts hEq
      cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ (namedInstance I) len₀ grad₀
    exact congrArg Prod.snd hFacts.2.2.2.1
  have hwstrGrid : ∃ wInt : ℤ,
      (wInt : ℝ) / (2 : ℝ) ^ pLast = (s0.chain.lastLSFs s0.chain.lastBran).wstr e := by
    rw [hLastEq]
    unfold dryLastTool fixedPointLastLevelTool
    dsimp only
    by_cases hne : (nonLoopEdges (s0.chain.G cfg.P.d)).Nonempty
    · simp only [hne, ↓reduceIte]
      by_cases hmem : e ∈ nonLoopEdges (s0.chain.G cfg.P.d)
      · simp only [hmem, ↓reduceIte, stretchQuery]
        set H := representativeGraph (s0.chain.G cfg.P.d)
          (s0.chain.toTreeChain.chainLen len₀ cfg.P.d)
        have hHm : H.m ≤ (s0.chain.G cfg.P.d).m := by
          change (((nonLoopEdges (s0.chain.G cfg.P.d)).image (edgePairKey (s0.chain.G cfg.P.d))).image
            (shortestEdge (s0.chain.G cfg.P.d) (s0.chain.toTreeChain.chainLen len₀ cfg.P.d))).card ≤
            (s0.chain.G cfg.P.d).E.card
          exact (Finset.card_image_le.trans Finset.card_image_le).trans (Finset.card_filter_le _ _)
        have hpwLe : weightPrecision lastCanonConst H ≤ pLast := by
          have h1 := representativeGraph_weightPrecision_le lastCanonConst (s0.chain.G cfg.P.d)
            (s0.chain.toTreeChain.chainLen len₀ cfg.P.d)
          have h2 : (H.m + 1).size ≤ (I.m + 1).size :=
            Nat.size_le_size (Nat.add_le_add_right (hHm.trans hGdM) 1)
          dsimp only [pLast, dryLastStretchP, H, I] at h1 h2 ⊢
          omega
        exact roundStretch_on_grid_le hpwLe _
      · simp only [hmem, ↓reduceIte]
        exact ⟨(2 : ℤ) ^ pLast, by push_cast; exact div_self (by positivity)⟩
    · simp only [hne, ↓reduceIte]
      exact ⟨(2 : ℤ) ^ pLast, by push_cast; exact div_self (by positivity)⟩
  obtain ⟨wInt, hwIntEq⟩ := hwstrGrid
  have hActD : s0.chain.toTreeChain.activeLSF cfg.P.d = s0.chain.lastLSFs s0.chain.lastBran := by
    unfold TreeChain.activeLSF; simp [ChainState.toTreeChain]
  have hLenD1Eq : s0.chain.toTreeChain.chainLen len₀ (cfg.P.d + 1) e =
      (s0.chain.lastLSFs s0.chain.lastBran).wstr e *
        s0.chain.toTreeChain.chainLen len₀ cfg.P.d e := by
    change (s0.chain.toTreeChain.activeLSF cfg.P.d).wstr e *
      s0.chain.toTreeChain.chainLen len₀ cfg.P.d e = _
    rw [hActD]
  have hq0Eq' : (q0 : ℝ) / (2 : ℝ) ^ P = s0.chain.toTreeChain.chainLen len₀ cfg.P.d e := hq0Eq
  have hqCast : ((wInt * q0 : ℤ) : ℝ) / (2 : ℝ) ^ (P + pLast) =
      s0.chain.toTreeChain.chainLen len₀ (cfg.P.d + 1) e := by
    rw [hLenD1Eq, ← hwIntEq, ← hq0Eq', pow_add]
    push_cast; ring
  have hLastH := hInit.1.hLastHolds s0.chain.lastBran hInit.1.hLastBran
  have hHolds := (hInit.1.toTreeChain_holds_noHidden hVcfg.hσ_mwu_mono hVcfg.hTP hVcfg.hLP hVcfg.hMWU
    hVcfg.hEmb hVcfg.hγM₀ hVcfg.hγk).1
  rw [hInit.2.2.1, hInit.2.2.2.1] at hHolds
  have hSubD := s0.chain.toTreeChain.forestsAreSubgraphs_of_holds hHolds cfg.P.d le_rfl
  rw [hActD] at hSubD
  have hwstr_bounds : 1 ≤ (s0.chain.lastLSFs s0.chain.lastBran).wstr e ∧
      (s0.chain.lastLSFs s0.chain.lastBran).wstr e ≤ cfg.LP.σ_last (s0.chain.G cfg.P.d).n := by
    have hnn : ∀ f ∈ (s0.chain.G cfg.P.d).E, 0 ≤ s0.chain.toTreeChain.chainLen len₀ cfg.P.d f :=
      fun f hf => le_trans (by positivity) (hbd.2.2.2.1 f hf).1
    have h1 := one_le_stretch hSubD hnn he
    have h2 := hLastH.2.2.2 e he
    exact ⟨le_trans h1 h2.1, h2.2⟩
  have hLenD1_nn : 0 ≤ s0.chain.toTreeChain.chainLen len₀ (cfg.P.d + 1) e := by
    rw [hLenD1Eq]; exact mul_nonneg (le_trans zero_le_one hwstr_bounds.1) hLenD_pos.le
  have hSigLe : cfg.LP.σ_last (s0.chain.G cfg.P.d).n ≤ (2 : ℝ) ^ (k + 4 * I.m.size + 18) := by
    set nD := (s0.chain.G cfg.P.d).n
    have hGdN : nD ≤ 2 * I.m + 2 := by
      have hInEq : (namedInstance I).n = I.n := by simp [namedInstance, MGraph.n]
      have hImGeJm : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCap).1
      have hInLe : I.n ≤ 2 * I.m + 2 := by change J.n + 1 ≤ 2 * I.m + 2; omega
      exact (Finset.card_le_card hbd.2.1).trans
        (by rw [show (namedInstance I).V.card = (namedInstance I).n from rfl, hInEq]; exact hInLe)
    have hC_lt := (dryWitnessUsed_lastCanonConst_and_levelM_lt J hJn hJm hCap).1
    have h1le : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 4 * I.m.size + 18) := one_le_pow₀ (by norm_num)
    have hDC_eq : max 1 dryLastConstant = 128 * max 1 lastCanonConst := by
      unfold dryLastConstant
      have : (1 : ℝ) ≤ max 1 lastCanonConst := le_max_left 1 _
      exact max_eq_right (by linarith)
    have hDC_le : max 1 dryLastConstant ≤ (2 : ℝ) ^ (k + 7) := by
      rw [hDC_eq, pow_add]; norm_num; linarith
    have hsz := Nat.lt_size_self I.m
    have h2pos : 1 ≤ 2 ^ I.m.size := Nat.one_le_two_pow
    have hn_le : (nD : ℝ) ≤ (2 : ℝ) ^ (I.m.size + 2) := by
      have h1 : nD ≤ 2 ^ (I.m.size + 2) := by
        have hpow : 2 ^ (I.m.size + 2) = 4 * 2 ^ I.m.size := by rw [pow_add]; ring
        omega
      exact_mod_cast h1
    have hlog_le : Real.log ((nD : ℝ) + 2) ≤ (2 : ℝ) ^ (I.m.size + 3) := by
      have h1 : nD + 2 ≤ 2 ^ (I.m.size + 3) := by
        have hpow : 2 ^ (I.m.size + 3) = 8 * 2 ^ I.m.size := by rw [pow_add]; ring
        omega
      have h2 : (nD : ℝ) + 2 ≤ (2 : ℝ) ^ (I.m.size + 3) := by exact_mod_cast h1
      have hposD : (0 : ℝ) < (nD : ℝ) + 2 :=
        add_pos_of_nonneg_of_pos (Nat.cast_nonneg nD) two_pos
      exact (Real.log_le_sub_one_of_pos hposD).trans (by linarith)
    have hlog_nn : 0 ≤ Real.log ((nD : ℝ) + 2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) nD])
    have hmain : 2 * max 1 dryLastConstant * (nD : ℝ) ^ 2 *
        (Real.log ((nD : ℝ) + 2)) ^ 2 ≤ (2 : ℝ) ^ (k + 4 * I.m.size + 18) := by
      have hnsq : (nD : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (I.m.size + 2)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hn_le 2
      have hlsq : (Real.log ((nD : ℝ) + 2)) ^ 2 ≤ ((2 : ℝ) ^ (I.m.size + 3)) ^ 2 :=
        pow_le_pow_left₀ hlog_nn hlog_le 2
      have hmul1 : 2 * max 1 dryLastConstant * (nD : ℝ) ^ 2 ≤
          2 * (2 : ℝ) ^ (k + 7) * ((2 : ℝ) ^ (I.m.size + 2)) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hDC_le zero_le_two) hnsq (sq_nonneg _) (by positivity)
      calc 2 * max 1 dryLastConstant * (nD : ℝ) ^ 2 * (Real.log ((nD : ℝ) + 2)) ^ 2
          ≤ (2 * (2 : ℝ) ^ (k + 7) * ((2 : ℝ) ^ (I.m.size + 2)) ^ 2) *
              ((2 : ℝ) ^ (I.m.size + 3)) ^ 2 :=
            mul_le_mul hmul1 hlsq (sq_nonneg _)
              (mul_nonneg (by positivity) (sq_nonneg _))
        _ = (2 : ℝ) ^ (k + 4 * I.m.size + 18) := by
            rw [← pow_mul, ← pow_mul, ← pow_succ', ← pow_add, ← pow_add]
            exact congrArg ((2 : ℝ) ^ ·) (by omega)
    change max 1 (2 * max 1 dryLastConstant * (nD : ℝ) ^ 2 *
      (Real.log ((nD : ℝ) + 2)) ^ 2) ≤ _
    exact max_le h1le hmain
  have hkE : k ≤ E := by
    have := qualityExponent_le_qualitySlackExponent I.m V k
    dsimp only [E, ipmQualityRangeExponent]; omega
  refine ⟨⟨q0, hFit0, hq0Eq⟩, wInt * q0, ?_, hqCast⟩
  refine fits_of_nonneg_mul_pow_lt hqCast hLenD1_nn ?_
  have hProdLe : s0.chain.toTreeChain.chainLen len₀ (cfg.P.d + 1) e * (2 : ℝ) ^ (P + pLast) ≤
      (2 : ℝ) ^ (P + 43 * E + 4 * I.m.size + 18) := by
    rw [hLenD1Eq]
    have h1 : (s0.chain.lastLSFs s0.chain.lastBran).wstr e *
        s0.chain.toTreeChain.chainLen len₀ cfg.P.d e ≤
        (2 : ℝ) ^ (k + 4 * I.m.size + 18) * (2 : ℝ) ^ (2 * E) :=
      mul_le_mul (hwstr_bounds.2.trans hSigLe) hLenD_le hLenD_pos.le (by positivity)
    have h2 : (2 : ℝ) ^ (P + pLast) ≤ (2 : ℝ) ^ (P + 40 * E) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    calc (s0.chain.lastLSFs s0.chain.lastBran).wstr e *
            s0.chain.toTreeChain.chainLen len₀ cfg.P.d e * (2 : ℝ) ^ (P + pLast)
        ≤ ((2 : ℝ) ^ (k + 4 * I.m.size + 18) * (2 : ℝ) ^ (2 * E)) * (2 : ℝ) ^ (P + 40 * E) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (P + 42 * E + k + 4 * I.m.size + 18) := by
          rw [← pow_add, ← pow_add]; exact congrArg ((2 : ℝ) ^ ·) (by omega)
      _ ≤ (2 : ℝ) ^ (P + 43 * E + 4 * I.m.size + 18) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ (P + 43 * E + 4 * I.m.size + 18) * 2 =
      (2 : ℝ) ^ (P + 43 * E + 4 * I.m.size + 19) := (pow_succ 2 _).symm
  have h3 : (2 : ℝ) ^ (P + 43 * E + 4 * I.m.size + 19) < (2 : ℝ) ^ (4 * L) :=
    pow_lt_pow_right₀ (by norm_num) (by omega)
  rw [hCap4Eq, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- Discharges `hLenFitInt` for `s0 = algorithm2_init cfg (namedInstance I) grad₀ len₀` on all
interior edges `e ∈ (s0.chain.G j).E` (`j < cfg.P.d`). -/
theorem dryInitSel_hLenFitInt
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    (grad₀ len₀ : ℕ → ℝ)
    (hLenWithin :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      IPM.LengthsWithin (namedInstance I) (ipmQualityRangeExponent I.m V k) len₀)
    (hGrid :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      IsDyadicGrid (namedInstance I) (ipmQualityPrecision I.m V k) len₀) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let P := ipmQualityPrecision I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let s0 := Chain.Ordered.algorithm2_init cfg (namedInstance I) grad₀ len₀
    ∀ j < cfg.P.d, ∀ e ∈ (s0.chain.G j).E,
      ∃ q : ℤ, Num.Fits 4 L q ∧
        (q : ℝ) / (2 : ℝ) ^ P = s0.chain.toTreeChain.chainLen s0.chain.ℓ (j + 1) e := by
  intro I V k L P cfg s0 j hj e he
  let E := ipmQualityRangeExponent I.m V k
  have hVcfg := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hGV : (namedInstance I).IsValid :=
    namedInstance_valid I (connectedInitialInstance_valid J.toInstance (V : ℤ) J.toInstance_valid)
  have hIm1 : 1 ≤ I.m := lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap).1
  have hEΨ : (E : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  have hlPos : ∀ f ∈ (namedInstance I).E, 0 < len₀ f := fun f hf =>
    lt_of_lt_of_le (by positivity) (hLenWithin f hf).1
  have hℓRange : Chain.Ordered.LenInRange (max 0 cfg.Ψ) (namedInstance I) len₀ := by
    intro f hf
    have hlog := ((abs_log_le_of_two_pow_bounds (hLenWithin f hf).1 (hLenWithin f hf).2).trans hEΨ).trans
      (le_max_right 0 cfg.Ψ)
    rw [abs_le] at hlog
    exact ⟨by simpa [Real.exp_log (hlPos f hf)] using Real.exp_le_exp.mpr hlog.1,
      by simpa [Real.exp_log (hlPos f hf)] using Real.exp_le_exp.mpr hlog.2⟩
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of
    (le_max_left dryWitnessUsed.M_thresh _) (le_max_right dryWitnessUsed.M_thresh _)
    (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed) J hJn hJm hCap
  have hmG : (namedInstance I).m ≤ cfg.P.M₀ := by rw [namedInstance_m]; exact le_max_left _ _
  have hnG : (namedInstance I).n ≤ cfg.N₀ := by
    have hInEq : (namedInstance I).n = I.n := by simp [namedInstance, MGraph.n]
    rw [hInEq]; exact hIn
  have hInit := Chain.Ordered.initialize_preserves_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hVcfg.hTP hVcfg.hLP hVcfg.hT hVcfg.hL hVcfg.hγM₀ hVcfg.hγk (namedInstance I) len₀ grad₀
    hGV hmG hnG hℓRange
  have hGridInv := dryChainLenGridInv_init J hJn hJm hCap len₀ grad₀ hLenWithin hGrid
  have hbr : s0.chain.bran j < cfg.P.k := hInit.1.hBran j hj
  obtain ⟨hwstr1, hhi, ⟨q, hq⟩⟩ := hGridInv.2.2.2.1 j hj (s0.chain.bran j) hbr e he
  have hcl : s0.chain.toTreeChain.chainLen s0.chain.ℓ (j + 1) e =
      (cfg.T.lsfs (s0.chain.scState j) (s0.chain.bran j)).wstr e *
        s0.chain.toTreeChain.chainLen s0.chain.ℓ j e := by
    rw [TreeChain.chainLen, coreLen]
    congr 1
    simp [TreeChain.activeLSF, ChainState.toTreeChain, hj]
  have hhi' : s0.chain.toTreeChain.chainLen s0.chain.ℓ (j + 1) e ≤
      (2 : ℝ) ^ (E + (j + 1) * (3 * I.m.size + 12)) := by rw [hcl]; exact hhi
  have hq' : (q : ℝ) / (2 : ℝ) ^ P = s0.chain.toTreeChain.chainLen s0.chain.ℓ (j + 1) e := by
    rw [hcl]; exact hq
  have hnn : 0 ≤ s0.chain.toTreeChain.chainLen s0.chain.ℓ (j + 1) e := by
    rw [hcl]
    have hwstr0 : 0 ≤ (cfg.T.lsfs (s0.chain.scState j) (s0.chain.bran j)).wstr e :=
      le_trans (by norm_num) hwstr1
    have hlo : (2 : ℝ) ^ (-(E : ℤ)) ≤ s0.chain.toTreeChain.chainLen s0.chain.ℓ j e :=
      ((hGridInv.2.2.1 j hj.le).1 e he).1
    exact mul_nonneg hwstr0 (le_trans (by positivity) hlo)
  have hExp : cfg.P.d * (3 * I.m.size + 12) ≤ E :=
    chainLen_exponent_le_rangeExponent I.m V (concreteQualityBudgetWithLast dryWitnessUsed)
      hIm1 cfg.P.hM₀
  have hExpJ : (j + 1) * (3 * I.m.size + 12) ≤ E :=
    (Nat.mul_le_mul_right _ hj).trans hExp
  have h4L : P + 2 * E + 1 < 4 * L := by
    dsimp only [L, P, E, ipmQualityLimbs, ipmQualityPrecision, ipmQualityErrorBits]
    omega
  have hCap4Eq : (Num.capacity 4 L : ℝ) = (2 : ℝ) ^ (4 * L) := by
    rw [Num.capacity, Num.base, ← pow_mul]; push_cast; rfl
  refine ⟨q, fits_of_nonneg_mul_pow_lt hq' hnn ?_, hq'⟩
  have h1 : s0.chain.toTreeChain.chainLen s0.chain.ℓ (j + 1) e * (2 : ℝ) ^ P ≤
      (2 : ℝ) ^ (2 * E) * (2 : ℝ) ^ P :=
    mul_le_mul_of_nonneg_right
      (hhi'.trans (pow_le_pow_right₀ (by norm_num) (by omega))) (by positivity)
  have h2 : (2 : ℝ) ^ (2 * E) * (2 : ℝ) ^ P * 2 = (2 : ℝ) ^ (P + 2 * E + 1) := by
    rw [← pow_add, ← pow_succ]; exact congrArg ((2 : ℝ) ^ ·) (by omega)
  have h3 : (2 : ℝ) ^ (P + 2 * E + 1) < (2 : ℝ) ^ (4 * L) :=
    pow_lt_pow_right₀ (by norm_num) h4L
  rw [hCap4Eq, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- Initial-state model invariants for `s0 = algorithm2_init cfg (namedInstance I) grad₀ len₀`
under `IPM.LengthsWithin`, `IsDyadicGrid`, and `|grad₀ e| ≤ 2^E`. -/
theorem dryInitSel_modelFacts
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    (grad₀ len₀ : ℕ → ℝ)
    (hLenWithin :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      IPM.LengthsWithin (namedInstance I) (ipmQualityRangeExponent I.m V k) len₀)
    (hGrid :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      IsDyadicGrid (namedInstance I) (ipmQualityPrecision I.m V k) len₀)
    (hGradWithin :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      ∀ e ∈ (namedInstance I).E, |grad₀ e| ≤ (2 : ℝ) ^ ipmQualityRangeExponent I.m V k) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let P := ipmQualityPrecision I.m V k
    let E := ipmQualityRangeExponent I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    let s0 := Chain.Ordered.algorithm2_init cfg G grad₀ len₀
    (∃ σ σ_mwu γ_ℓ γ_c, SelectModelInv s0 G σ σ_mwu γ_ℓ γ_c) ∧
    OrdSolverReached cfg (1 / (2 : ℝ) ^ k) G s0 ∧
    s0.chain.totalRuntime ≤ chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0) ∧
    s0.chain.lastBran < s0.chain.lastK ∧
    (∀ j ≤ cfg.P.d, ∀ v ∈ (s0.chain.G j).V, v < G.n) ∧
    (∀ j ≤ cfg.P.d, ∀ e ∈ (s0.chain.G j).E, e < initTargetCap cfg G) ∧
    (∀ j ≤ cfg.P.d, ∀ v ∈ (s0.chain.toTreeChain.activeLSF j).F.F.V, v < G.n) ∧
    (∀ j ≤ cfg.P.d, ∀ e ∈ (s0.chain.toTreeChain.activeLSF j).F.F.E, e < initTargetCap cfg G) ∧
    (∀ j ≤ cfg.P.d, (s0.chain.G j).m ≤ I.m) ∧
    (∀ j ≤ cfg.P.d, (s0.chain.toTreeChain.activeLSF j).F.F.m ≤ I.m) ∧
    (∀ j ≤ cfg.P.d, (s0.chain.toTreeChain.activeLSF j).F.F.n ≤ G.n) ∧
    (∀ j < cfg.P.d, s0.chain.lvlM j = levelM cfg.TP cfg.P j) ∧
    s0.chain.N₀ = cfg.N₀ ∧
    (∀ j < cfg.P.d, ∀ e ∈ (s0.chain.toTreeChain.activeCore j).E,
      (mWalkEncode (s0.chain.toTreeChain.activeEmb j e)).length ≤ drySlot I.m) ∧
    (∀ j < cfg.P.d, ∀ e ∈ (s0.chain.toTreeChain.activeCore j).E \ (s0.chain.toTreeChain.activeS j).E,
      (s0.chain.toTreeChain.activeEmb j e).length ≤ dryMaxEmbLen I.m) ∧
    (∀ j ≤ cfg.P.d, ∀ (φ : ℕ → ℕ → ℝ) (φj : ℕ → ℝ),
      (∀ r < j, SelectPotInvAt s0.chain.toTreeChain s0.chain.g φ r) →
      (∀ r < j, SelectPhiBoundedAt s0.chain.toTreeChain φ (2 * I.m + 2) ((2 : ℝ) ^ E) r) →
      (∀ v ∈ (s0.chain.toTreeChain.activeLSF j).F.F.V,
        ∃ r ∈ (s0.chain.toTreeChain.activeLSF j).F.F.V,
          (s0.chain.toTreeChain.activeLSF j).F.F.Connected v r ∧
          φj v = walkInner (potGrad s0.chain.toTreeChain s0.chain.g φ j)
            ((s0.chain.toTreeChain.activeLSF j).F.F.forestPath v r)) →
      ∀ r < j + 1, SelectPhiBoundedAt s0.chain.toTreeChain (Function.update φ j φj)
        (2 * I.m + 2) ((2 : ℝ) ^ E) r) ∧
    (∀ j ≤ cfg.P.d, ∀ φ' : ℕ → ℕ → ℝ,
      (∀ r < j, SelectPotInvAt s0.chain.toTreeChain s0.chain.g φ' r) →
      (∀ r < j, SelectPhiBoundedAt s0.chain.toTreeChain φ' (2 * I.m + 2) ((2 : ℝ) ^ E) r) →
      (∀ e ∈ (s0.chain.toTreeChain.activeLSF j).F.F.E,
        PotGradEvalFits 4 L P s0.chain.toTreeChain s0.chain.g φ' j e) ∧
      ForestWalkFits 4 L P (s0.chain.toTreeChain.activeLSF j).F.F
        (potGrad s0.chain.toTreeChain s0.chain.g φ' j)) ∧
    CandidateKeysFit 4 P (dryLastStretchP J) L s0.chain.toTreeChain s0.chain.g s0.chain.ℓ := by
  intro I V k L P E cfg G s0
  have hVcfg := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hGV : G.IsValid :=
    namedInstance_valid I (connectedInitialInstance_valid J.toInstance (V : ℤ) J.toInstance_valid)
  have hGE : G.E = Finset.range I.m := rfl
  have hInEq : G.n = I.n := by simp [G, namedInstance, MGraph.n]
  have hImEq : G.m = I.m := namedInstance_m I
  have hImGeJm : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCap).1
  have hInLe : I.n ≤ 2 * I.m + 2 := by change J.n + 1 ≤ 2 * I.m + 2; omega
  have hGnLe : G.n ≤ 2 * I.m + 2 := by rw [hInEq]; exact hInLe
  have hVlt : ∀ v ∈ G.V, v < G.n := fun v hv => by rw [hInEq]; exact Finset.mem_range.mp hv
  have hElt : ∀ e ∈ G.E, e < initTargetCap cfg G := fun e he => by
    have heM : e < I.m := Finset.mem_range.mp he
    have hmCap : I.m ≤ initTargetCap cfg G := by
      unfold initTargetCap; rw [hImEq]; omega
    omega
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of
    (le_max_left dryWitnessUsed.M_thresh _) (le_max_right dryWitnessUsed.M_thresh _)
    (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed) J hJn hJm hCap
  have hmG : G.m ≤ cfg.P.M₀ := by rw [hImEq]; exact le_max_left _ _
  have hnG : G.n ≤ cfg.N₀ := by rw [hInEq]; exact hIn
  have hEΨ : (E : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  have hlPos : ∀ e ∈ G.E, 0 < len₀ e := fun e he =>
    lt_of_lt_of_le (by positivity) (hLenWithin e he).1
  have hlR : ∀ e ∈ G.E, |Real.log (len₀ e)| ≤ cfg.Ψ := fun e he =>
    (abs_log_le_of_two_pow_bounds (hLenWithin e he).1 (hLenWithin e he).2).trans hEΨ
  have hℓRange : Chain.Ordered.LenInRange (max 0 cfg.Ψ) G len₀ := by
    intro e he
    have hlog := (hlR e he).trans (le_max_right 0 cfg.Ψ)
    rw [abs_le] at hlog
    exact ⟨by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.1,
      by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.2⟩
  have hInit := Chain.Ordered.initialize_preserves_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hVcfg.hTP hVcfg.hLP hVcfg.hT hVcfg.hL hVcfg.hγM₀ hVcfg.hγk G len₀ grad₀ hGV hmG hnG hℓRange
  have hInv := hInit.1
  have hTH := hInv.toTreeChain_holds_noHidden hVcfg.hσ_mwu_mono hVcfg.hTP hVcfg.hLP hVcfg.hMWU
    hVcfg.hEmb hVcfg.hγM₀ hVcfg.hγk
  have hHolds := hTH.1
  rw [hInit.2.2.1] at hHolds
  have hReach : OrdSolverReached cfg (1 / (2 : ℝ) ^ k) G s0 :=
    ordSolverReached_init cfg (1 / (2 : ℝ) ^ k) G grad₀ len₀ hGV hlPos hlR
  have hRtCap : s0.chain.totalRuntime ≤ chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0) := by
    have h1 := (hReach.runtime_and_tree_le_cap hVcfg hmG hnG).1
    have h2 := (credits_init_le cfg G grad₀ len₀).2.2.2.2.1
    rwa [h2] at h1
  have hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v := drySolverGraph_connected J
  have hShift : Ordered.ShiftLoopChainInv cfg s0.chain :=
    hReach.shiftLoopChainInv hVcfg hmG hnG hConn
  have hLastSpans : s0.chain.toTreeChain.LastLevelSpans := hTH.2.1
  have hbd := drySC_chainLen_bounds J hJn hJm hCap len₀ grad₀ hLenWithin
  have hSubF := s0.chain.toTreeChain.forestsAreSubgraphs_of_holds hHolds
  have hG0 : s0.chain.G 0 = G := hInit.2.2.1
  have hG0n : (s0.chain.G 0).n ≤ 2 * I.m + 2 := by rw [hG0]; exact hGnLe
  have hg0 : ∀ f ∈ (s0.chain.G 0).E, |s0.chain.g f| ≤ (2 : ℝ) ^ E := fun f hf => by
    rw [hG0] at hf; exact hGradWithin f hf
  have hGridInv := dryChainLenGridInv_init J hJn hJm hCap len₀ grad₀ hLenWithin hGrid
  have hpLastLe : dryLastStretchP J ≤ 40 * E := by
    have h1 := dryLastStretchP_le_forty_rangeExponent J hJn hJm hCap
    have hmono : (I.m + 1).size ≤ (max I.m (levelM cfg.TP cfg.P cfg.P.d) + 1).size :=
      Nat.size_le_size (Nat.add_le_add_right (le_max_left _ _) 1)
    dsimp only [dryLastStretchP, E, I, V, k, cfg] at h1 hmono ⊢
    omega
  refine ⟨⟨_, _, _, _, ⟨hHolds, hLastSpans, hInv.hBran,
      fun i hi => levelHistory_sparseCoreOrdInput (Classical.choice (hInv.hHist i hi)),
      hlPos, hVlt⟩⟩,
    hReach, hRtCap, hInv.hLastBran, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun j _ => rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj v hv; exact hVlt v ((hbd j hj).2.1 hv)
  · intro j hj e he; exact hElt e ((hbd j hj).2.2.1 he)
  · intro j hj v hv; exact hVlt v ((hbd j hj).2.1 ((hSubF j hj).1 hv))
  · intro j hj e he; exact hElt e ((hbd j hj).2.2.1 ((hSubF j hj).2.1 he))
  · intro j hj; exact (Finset.card_le_card (hbd j hj).2.2.1).trans hImEq.le
  · intro j hj; exact (Finset.card_le_card ((hSubF j hj).2.1.trans (hbd j hj).2.2.1)).trans hImEq.le
  · intro j hj; exact Finset.card_le_card ((hSubF j hj).1.trans (hbd j hj).2.1)
  · intro j hj e he
    have h1 := (progTool_embLen_le_dryMaxEmbLen_of_shiftLoop J hJn hJm hCap hShift j hj e he).1
    have h2 := mWalkEncode_length (s0.chain.toTreeChain.activeEmb j e)
    dsimp only [I] at h1 ⊢
    unfold drySlot; omega
  · intro j hj e he
    exact (progTool_embLen_le_dryMaxEmbLen_of_shiftLoop J hJn hJm hCap hShift j hj e
      (Finset.mem_sdiff.mp he).1).1
  · intro j hj φ φj hPot hBd hFill r hr
    by_cases hrj : r = j
    · subst hrj
      exact selectPhiBoundedAt_of_phiFill (by positivity) hHolds hj hG0n hg0 hPot hBd hFill
    · have hrLt : r < j := by omega
      intro v hv
      rw [Function.update_of_ne hrj]
      exact hBd r hrLt v hv
  · intro j hj φ' hPot hBd
    exact dry_phiFillFits_of_chainInv J hJn hJm hCap hInv hG0n hj
      (M_g := (2 : ℝ) ^ E) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (show E ≤ 80 * E by omega)) hg0 hBd
  · exact dry_candidateKeysFit_of_chainInv J hJn hJm hCap hInv hGridInv hpLastLe
      (M_g := (2 : ℝ) ^ E) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (show E ≤ 40 * E by omega)) hg0

end MinCostFlow.Final.DryRun

end
