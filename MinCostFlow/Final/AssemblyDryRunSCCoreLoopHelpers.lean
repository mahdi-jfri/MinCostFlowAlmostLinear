module

public import MinCostFlow.Final.AssemblyDryRunSCDeepInv
public import MinCostFlow.Final.AssemblyDryRunSCCoreModelInv
public import MinCostFlow.MinRatio.OrdSolverWiredFull
import MinCostFlow.SparseCore.Program.AssemblyBranchStepReadModel
import MinCostFlow.MinRatio.WireSelectTouchedWstr
import MinCostFlow.MinRatio.WireSelectFwdCost
import MinCostFlow.MinRatio.InitRootECap
import Mathlib.Tactic

/-!
# Dry-run `UpdateLoopModelInv` derivation (`AssemblyDryRunSCCoreLoopModel`)

Derives the full `UpdateLoopModelInv` (`MinRatio/WireChainSpecs.lean:428-516`) — including
`st.updCount idx + curU.length < 2 ^ w` at every level `idx < cfg.P.d` — unconditionally at the
dry-run parameters from the existing premises of `OrdChainUpdateCoreSpecWKFBLSel` together with
the single rebuild-count word bound `∀ i < cfg.P.d, model.chain.rebuildCount i + 1 < 2 ^ w`:

1. `dryWitnessUsed_gammaR_le_two_pow_k`: proves `⌈cfg.TP.γ_r (cfg.P.M₀ ^ 2)⌉₊ ≤ 2 ^ k` from
   `concreteCirculationCfgWithLast_gamma_r` and `integerQualityExponent_bounds`.
2. `dryCoreSel_updCount_add_curU_lt_two_pow_wordSize`: proves `st.updCount idx + curU.length < 2 ^ w`
   at `dryWordSize` for both `idx = 0` (from `RefreshBatch`, `tr.2.2.2.1 ≤ initTargetCap cfg G`,
   and `concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize`) and `idx > 0` (from
   `ChainInv.hRecFwd` on `modelPre.chain`, `dryWitnessUsed_gammaR_le_two_pow_k`,
   `cappedQuality_linear_spec`, and `lt_two_pow_wordSize_of_poly_and_hw`).
3. `dryCoreSel_updateLoopModelInv`: proves all conjuncts of `UpdateLoopModelInv` by induction on
   `rem = cfg.P.d - idx` along `Ordered.updateLoop`, using `ShiftLoopChainInv` before and after
   `Update`, `DryChainLenGridInv`, `progTool_updateOrd_cost_mono`, `drySC_lastLevelBuildEqOnE`,
   `stepBundleTree_U_S_withinCaps`, and `∀ i < cfg.P.d, model.chain.rebuildCount i + 1 < 2 ^ w`.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. `⌈γ_r(M₀²)⌉₊ ≤ 2 ^ k` and `st.updCount idx + curU.length < 2 ^ w` at `dryWordSize` -/

/-- At the dry-run parameters, the rounded recourse factor `⌈γ_r(M₀²)⌉₊` is bounded by `2 ^ k`
where `k = cappedQualityExponent threshold A I.m`. -/
theorem dryWitnessUsed_gammaR_le_two_pow_k (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap1 : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
    let A := concreteQualityBudgetWithLast dryWitnessUsed
    let k := cappedQualityExponent threshold A I.m
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    ⌈cfg.TP.γ_r (cfg.P.M₀ ^ 2)⌉₊ ≤ 2 ^ k := by
  intro I threshold A k cfg
  have hΓ := (concreteCirculationCfgWithLast_gamma_r dryWitnessUsed J hJn hJm hCap1).2
  have hM0Eq : cfg.P.M₀ = max I.m threshold := rfl
  have hL1 : 1 ≤ Real.log ((cfg.P.M₀ : ℝ) + 2) := one_le_log_add_two' cfg.P.hM₀
  have hLL0 : 0 ≤ Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2) :=
    Real.log_nonneg (by linarith)
  have hPowLe : Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) ≤
      Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hCγA : dryWitnessUsed.C_γ + 1 ≤ (A : ℝ) := by
    have h1 : 15 + 5 * dryWitnessUsed.C_γ ≤ (A : ℝ) := Nat.le_ceil _
    have h2 : 3 ≤ dryWitnessUsed.C_γ := dryWitnessUsed.hCγ
    linarith
  have hExpLe : Real.exp ((dryWitnessUsed.C_γ + 1) *
        Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) ≤
      Real.exp ((A : ℝ) * Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := by
    apply Real.exp_le_exp.mpr
    have hCnn : 0 ≤ dryWitnessUsed.C_γ + 1 := by linarith [dryWitnessUsed.hCγ]
    have hPnn : 0 ≤ Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul hCγA hPowLe hPnn (by linarith)) hLL0
  have hIQ := (integerQualityExponent_bounds A cfg.P.M₀).1
  have hkEq : k = integerQualityExponent A cfg.P.M₀ := by
    dsimp only [k, cappedQualityExponent, chainEdgeCap, cfg]
    rw [hM0Eq, max_comm]
  have h2k : Real.exp ((A : ℝ) * Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) *
      Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) ≤ (2 : ℝ) ^ k := by
    rw [hkEq]
    unfold alg2KappaLower at hIQ
    have hpos1 : (0 : ℝ) < (2 : ℝ) ^ integerQualityExponent A cfg.P.M₀ := by positivity
    have hpos2 : (0 : ℝ) < Real.exp ((A : ℝ) * Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := Real.exp_pos _
    rw [Real.exp_neg, ← one_div, one_div_le_one_div hpos1 hpos2] at hIQ
    exact hIQ
  exact_mod_cast (hΓ.trans (hExpLe.trans h2k))

lemma refreshBatch_length_le_three_mul {G H : MGraph} {e2i i2e : ℕ → ℕ} {nf cap : ℕ}
    {U : List Update}
    (hFresh : FreshInv G H e2i i2e nf) (hRef : RefreshBatch G U)
    (hGm : G.m ≤ cap) (hNfCap : (translateBatch G e2i i2e nf U).2.2.2.1 ≤ cap) :
    U.length ≤ 3 * cap := by
  have hCount : ∀ (W : List Update) (Gcur Hcur : MGraph) (f g : ℕ → ℕ) (nf0 : ℕ),
      FreshInv Gcur Hcur f g nf0 → Gcur.BatchIsValid W → (∀ u ∈ W, IsEdgeUpdate u) →
      W.length ≤ Gcur.m + 2 * ((translateBatch Gcur f g nf0 W).2.2.2.1 - nf0) := by
    intro W
    induction W with
    | nil => intro _ _ _ _ _ _ _ _; simp
    | cons u rest ih =>
      intro Gcur Hcur f g nf0 hFr hBV hEd
      have hStep := translateBatch_preserves [u] Gcur Hcur f g nf0 hFr
        (by exact ⟨hBV.1, trivial⟩)
      have huEd := hEd u List.mem_cons_self
      have hRestEd : ∀ x ∈ rest, IsEdgeUpdate x := fun x hx => hEd x (List.mem_cons_of_mem _ hx)
      cases u with
      | insert e a b =>
        simp only [MGraph.BatchIsValid] at hBV
        have hG1 : (Gcur.applyUpdate (.insert e a b)).m = Gcur.m + 1 := by
          unfold MGraph.m MGraph.applyUpdate
          exact Finset.card_insert_of_notMem hBV.1.1
        have hFr1 : FreshInv (Gcur.applyUpdate (.insert e a b))
            (Hcur.applyUpdate (.insert nf0 a b))
            (Function.update f e nf0) (Function.update g nf0 e) (nf0 + 1) := by
          simpa [translateBatch, MGraph.applyBatch] using hStep.2.1
        have hIH := ih (Gcur.applyUpdate (.insert e a b)) (Hcur.applyUpdate (.insert nf0 a b))
          (Function.update f e nf0) (Function.update g nf0 e) (nf0 + 1) hFr1 hBV.2 hRestEd
        have hMono : nf0 + 1 ≤ (translateBatch (Gcur.applyUpdate (.insert e a b))
            (Function.update f e nf0) (Function.update g nf0 e) (nf0 + 1) rest).2.2.2.1 :=
          (translateBatch_nextFresh_bounds rest _ _ _ _).1
        have hNfEq : (translateBatch Gcur f g nf0 (.insert e a b :: rest)).2.2.2.1 =
            (translateBatch (Gcur.applyUpdate (.insert e a b))
              (Function.update f e nf0) (Function.update g nf0 e) (nf0 + 1) rest).2.2.2.1 := rfl
        rw [hG1] at hIH
        rw [hNfEq]
        simp only [List.length_cons]
        omega
      | delete e =>
        simp only [MGraph.BatchIsValid] at hBV
        have hG1 : (Gcur.applyUpdate (.delete e)).m + 1 = Gcur.m := by
          unfold MGraph.m MGraph.applyUpdate
          exact Finset.card_erase_add_one hBV.1
        have hFr1 : FreshInv (Gcur.applyUpdate (.delete e))
            (Hcur.applyUpdate (.delete (f e))) f g nf0 := by
          simpa [translateBatch, MGraph.applyBatch] using hStep.2.1
        have hIH := ih (Gcur.applyUpdate (.delete e)) (Hcur.applyUpdate (.delete (f e)))
          f g nf0 hFr1 hBV.2 hRestEd
        have hNfEq : (translateBatch Gcur f g nf0 (.delete e :: rest)).2.2.2.1 =
            (translateBatch (Gcur.applyUpdate (.delete e)) f g nf0 rest).2.2.2.1 := rfl
        rw [hNfEq]
        simp only [List.length_cons]
        omega
      | split _ _ _ _ => simp [IsEdgeUpdate] at huEd
  have hEd : ∀ u ∈ U, IsEdgeUpdate u := fun u hu => by
    have hns := hRef.2.2 u hu
    cases u with
    | insert _ _ _ => trivial
    | delete _ => trivial
    | split _ _ _ _ => exact absurd hns id
  have h1 := hCount U G H e2i i2e nf hFresh hRef.1 hEd
  omega

lemma chainInv_updCount_le_four_levelM {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    {ch : ChainState T P} (hInv : Ordered.ChainInv T L TP LP P N₀ ch)
    {idx : ℕ} (hidx : idx < P.d) :
    ch.updCount idx ≤ 4 * levelM TP P idx := by
  obtain ⟨H⟩ := hInv.hHist idx hidx
  have h1 : (ch.updCount idx : ℝ) ≤ SparseCoreTool.updateThreshold P.k (levelM TP P idx) N₀ :=
    H.hUpd ▸ H.hThresh
  have h2 : SparseCoreTool.updateThreshold P.k (levelM TP P idx) N₀ ≤
      4 * (levelM TP P idx : ℝ) / (P.k : ℝ) :=
    updateThreshold_le_four_div P.k _ _ P.hk
  have h3 : 4 * (levelM TP P idx : ℝ) / (P.k : ℝ) ≤ 4 * (levelM TP P idx : ℝ) := by
    have hk1 : (1 : ℝ) ≤ P.k := by exact_mod_cast P.hk
    exact div_le_self (by positivity) hk1
  exact_mod_cast h1.trans (h2.trans h3)

/-- **Unconditional dry-run word-size bound `updCount idx + curU.length < 2 ^ w`:**
holds at `dryWordSize` whenever `updCount idx ≤ 4 * levelM idx` and either `idx = 0` with
`curU.length ≤ 3 * initTargetCap cfg G`, or `0 < idx < cfg.P.d` with
`curU.length ≤ chEnd.curFwd (idx - 1)` for a chain `chEnd` satisfying `ChainInv`. -/
theorem dryCoreSel_updCount_add_curU_lt_two_pow_wordSize
    (allocationCoefficient allocationDegree : ℕ)
    (hSCWordCoeff : Classical.choose (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize
      dryWitnessUsed) ≤ allocationCoefficient)
    (source J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCap1 : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source) :
    let I := solverConnectedAugmented J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
    ∀ {chOrig chEnd : ChainState cfg.T cfg.P} {idx curULen : ℕ},
      idx < cfg.P.d →
      Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ chOrig →
      Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ chEnd →
      (idx = 0 → curULen ≤ 3 * initTargetCap cfg G) →
      (0 < idx → curULen ≤ chEnd.curFwd (idx - 1)) →
      chOrig.updCount idx + curULen < 2 ^ w := by
  intro I cfg G w chOrig chEnd idx curULen hidxLt hInvOrig hInvEnd hLen0 hLenPos
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1
  have hUpdLe : chOrig.updCount idx ≤ 4 * levelM cfg.TP cfg.P idx :=
    chainInv_updCount_le_four_levelM hInvOrig hidxLt
  have hSC1 := Classical.choose_spec
    (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed)
    allocationCoefficient allocationDegree hSCWordCoeff source J hJn hJm hCap1 hw
  have hImLe : I.m ≤ 7 * J.m := (solverConnectedAugmented_size J hJn hJm hCap1).2
  have hM0_ge_Im : I.m ≤ cfg.P.M₀ := le_max_left _ _
  let hF := ipmQualityMinRatioFormat I.m V k hw
  have hLge100 : 100 ≤ hF.limbs := by
    dsimp only [hF, ipmQualityMinRatioFormat, ipmQualityLimbs, ipmQualityPrecision,
      ipmQualityRangeExponent, ipmQualityErrorBits]; omega
  have hLCap : ∀ j ≤ cfg.P.d,
      hF.limbs ≤ concreteReadout2LimbMul dryWitnessUsed *
        bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀ := fun j hj =>
    (concrete_sparseCoreCapHyp_uniform dryWitnessUsed J hJn hJm hCap1 j hj 0 0 (by omega)).2
  by_cases h0 : idx = 0
  · subst h0
    have hU3 : curULen ≤ 3 * initTargetCap cfg G := hLen0 rfl
    have hCapLe : initTargetCap cfg G ≤ 4 * cfg.P.M₀ := by
      have hGm : G.m = I.m := namedInstance_m I
      have hImPos : 0 < I.m := lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap1).1
      have hSupLe : G.E.sup id + 1 ≤ I.m := by
        have h1 : G.E.sup id ≤ I.m - 1 := Finset.sup_le fun e he => by
          have hlt : e < I.m := Finset.mem_range.mp he
          dsimp only [id]; omega
        omega
      have hN0 : cfg.N₀ = 4 * cfg.P.M₀ := rfl
      have hEq : initTargetCap cfg G = initRootECap cfg.N₀ cfg.P.k G.m := by
        unfold initTargetCap initRootECap Ordered.alg2NameBase intRebuildThreshold
        have hM04 : cfg.N₀ / 4 = cfg.P.M₀ := by rw [hN0]; omega
        rw [hM04, hGm, max_eq_right (hSupLe.trans hM0_ge_Im)]
        have hsq : Nat.clog 2 (cfg.N₀ + 2) ^ 2 = Nat.clog 2 (cfg.N₀ + 2) * Nat.clog 2 (cfg.N₀ + 2) := sq _
        rw [hsq, Nat.div_div_eq_div_mul]
        ring_nf
      rw [hEq, hN0]
      exact initRootECap_le_four_mul (hGm ▸ hM0_ge_Im)
    have hN0Eq : cfg.N₀ = 4 * cfg.P.M₀ := rfl
    have hW1 := hSC1 1 (by decide) 0 hF.limbs (hLCap 0 (Nat.zero_le _))
    rw [pow_one] at hW1
    have hBound : chOrig.updCount 0 + curULen ≤ (levelM cfg.TP cfg.P 0 + cfg.N₀ + 2) * (hF.limbs + 1) := by
      have h4 : (levelM cfg.TP cfg.P 0 + cfg.N₀ + 2) * 4 ≤
          (levelM cfg.TP cfg.P 0 + cfg.N₀ + 2) * (hF.limbs + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    exact lt_of_le_of_lt hBound hW1
  · have hpos : 0 < idx := Nat.pos_of_ne_zero h0
    have hFwdLe := (hInvEnd.hRecFwd (idx - 1) (by omega)).1
    have hUpdPrev : chEnd.updCount (idx - 1) ≤ 4 * levelM cfg.TP cfg.P (idx - 1) :=
      chainInv_updCount_le_four_levelM hInvEnd (by omega)
    have hΓle2k : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤ (2 ^ k : ℕ) := by
      have h1 : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤ (⌈cfg.TP.γ_r (cfg.P.M₀ ^ 2)⌉₊ : ℝ) := Nat.le_ceil _
      exact h1.trans (by exact_mod_cast dryWitnessUsed_gammaR_le_two_pow_k J hJn hJm hCap1)
    have hCurULe : curULen ≤ 4 * 2 ^ k * levelM cfg.TP cfg.P (idx - 1) := by
      have hReal : (curULen : ℝ) ≤ ((4 * 2 ^ k * levelM cfg.TP cfg.P (idx - 1) : ℕ) : ℝ) := by
        have h1 : (curULen : ℝ) ≤ (chEnd.curFwd (idx - 1) : ℝ) := by exact_mod_cast hLenPos hpos
        have h2 : (chEnd.updCount (idx - 1) : ℝ) ≤ 4 * (levelM cfg.TP cfg.P (idx - 1) : ℝ) := by
          exact_mod_cast hUpdPrev
        have h3 : cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (chEnd.updCount (idx - 1) : ℝ) ≤
            ((2 ^ k : ℕ) : ℝ) * (4 * (levelM cfg.TP cfg.P (idx - 1) : ℝ)) :=
          mul_le_mul hΓle2k h2 (Nat.cast_nonneg _) (by positivity)
        have h4 : ((2 ^ k : ℕ) : ℝ) * (4 * (levelM cfg.TP cfg.P (idx - 1) : ℝ)) =
            ((4 * 2 ^ k * levelM cfg.TP cfg.P (idx - 1) : ℕ) : ℝ) := by push_cast; ring
        linarith
      exact_mod_cast hReal
    let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
    let A := concreteQualityBudgetWithLast dryWitnessUsed
    let Ck := concreteQualityLinearCoeff threshold A
    have h2kLin : 2 ^ k ≤ Ck * (I.m + 2) := cappedQuality_linear_spec threshold A I.m
    have h2kJm : 2 ^ k ≤ 7 * Ck * (J.m + 2) := by
      have h1 : I.m + 2 ≤ 7 * (J.m + 2) := by omega
      calc 2 ^ k ≤ Ck * (I.m + 2) := h2kLin
        _ ≤ Ck * (7 * (J.m + 2)) := Nat.mul_le_mul_left _ h1
        _ = 7 * Ck * (J.m + 2) := by ring
    have hHalfProd : ∀ a b : ℕ, a ^ 2 < 2 ^ w → b ^ 2 < 2 ^ w → a * b < 2 ^ w := by
      intro a b ha hb
      have hsq : (a * b) ^ 2 < (2 ^ w) ^ 2 := by
        rw [Nat.mul_pow, sq (2 ^ w)]
        exact Nat.mul_lt_mul'' ha hb
      by_contra hge
      push Not at hge
      have := Nat.pow_le_pow_left hge 2
      omega
    have h2kSq : (10 * (7 * Ck * (J.m + 2)) + 10) ^ 2 < 2 ^ w := by
      let deg := forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
      have hval : (10 * (7 * Ck * (J.m + 2)) + 10) ^ 2 ≤ (70 * Ck + 10) ^ 2 * (J.m + 2) ^ 2 := by
        have h1 : 10 * (7 * Ck * (J.m + 2)) + 10 ≤ (70 * Ck + 10) * (J.m + 2) := by nlinarith
        calc (10 * (7 * Ck * (J.m + 2)) + 10) ^ 2
            ≤ ((70 * Ck + 10) * (J.m + 2)) ^ 2 := Nat.pow_le_pow_left h1 2
          _ = (70 * Ck + 10) ^ 2 * (J.m + 2) ^ 2 := Nat.mul_pow _ _ 2
      have hdeg : (3 ^ 2 * (70 * Ck + 10) ^ 2) ^ 2 < 2 ^ (3 * (deg + 1)) := by
        have hCkPow : Ck ≤ 2 ^ Nat.clog 2 Ck := Nat.le_pow_clog (by decide) Ck
        have h1 : 70 * Ck + 10 ≤ 80 * 2 ^ Nat.clog 2 Ck := by
          have : 1 ≤ 2 ^ Nat.clog 2 Ck := Nat.one_le_pow _ _ (by decide)
          omega
        have h2 : 3 ^ 2 * (70 * Ck + 10) ^ 2 ≤ 2 ^ (16 + 2 * Nat.clog 2 Ck) := by
          calc 3 ^ 2 * (70 * Ck + 10) ^ 2
              ≤ 9 * (80 * 2 ^ Nat.clog 2 Ck) ^ 2 :=
                Nat.mul_le_mul_left 9 (Nat.pow_le_pow_left h1 2)
            _ = 57600 * (2 ^ Nat.clog 2 Ck) ^ 2 := by ring
            _ ≤ 2 ^ 16 * 2 ^ (2 * Nat.clog 2 Ck) := by
                rw [← pow_mul, mul_comm (Nat.clog 2 Ck) 2]
                exact Nat.mul_le_mul_right _ (by decide)
            _ = 2 ^ (16 + 2 * Nat.clog 2 Ck) := (pow_add 2 _ _).symm
        have h3 : (3 ^ 2 * (70 * Ck + 10) ^ 2) ^ 2 ≤ 2 ^ (32 + 4 * Nat.clog 2 Ck) := by
          calc (3 ^ 2 * (70 * Ck + 10) ^ 2) ^ 2
              ≤ (2 ^ (16 + 2 * Nat.clog 2 Ck)) ^ 2 := Nat.pow_le_pow_left h2 2
            _ = 2 ^ (32 + 4 * Nat.clog 2 Ck) := by rw [← pow_mul]; congr 1; ring
        have hdegLo : 32 + 4 * Nat.clog 2 Ck < 3 * (deg + 1) := by
          dsimp only [deg, forestProgramsScratchDegree, forestScratchDegree]; omega
        exact lt_of_le_of_lt h3 (Nat.pow_lt_pow_right (by decide) hdegLo)
      exact lt_two_pow_wordSize_of_poly_and_hw source J hJm (by decide) hw hval hdeg
    have hLvlSq : (max (levelM cfg.TP cfg.P idx) (levelM cfg.TP cfg.P (idx - 1)) + 1) ^ 2 < 2 ^ w := by
      rcases le_total (levelM cfg.TP cfg.P idx) (levelM cfg.TP cfg.P (idx - 1)) with hle | hle
      · rw [max_eq_right hle]
        have hW2 := hSC1 2 (by decide) (idx - 1) hF.limbs (hLCap (idx - 1) (by omega))
        have hbase : levelM cfg.TP cfg.P (idx - 1) + 1 ≤
            levelM cfg.TP cfg.P (idx - 1) + cfg.N₀ + 2 := by omega
        exact lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
          (lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbase 2)) hW2)
      · rw [max_eq_left hle]
        have hW2 := hSC1 2 (by decide) idx hF.limbs (hLCap idx (by omega))
        have hbase : levelM cfg.TP cfg.P idx + 1 ≤ levelM cfg.TP cfg.P idx + cfg.N₀ + 2 := by omega
        exact lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
          (lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbase 2)) hW2)
    have hSumLe : chOrig.updCount idx + curULen ≤
        (10 * (7 * Ck * (J.m + 2)) + 10) *
          (max (levelM cfg.TP cfg.P idx) (levelM cfg.TP cfg.P (idx - 1)) + 1) := by
      set Mmax := max (levelM cfg.TP cfg.P idx) (levelM cfg.TP cfg.P (idx - 1))
      have h1 : levelM cfg.TP cfg.P idx ≤ Mmax := le_max_left _ _
      have h2 : levelM cfg.TP cfg.P (idx - 1) ≤ Mmax := le_max_right _ _
      have h3 : curULen ≤ 4 * (7 * Ck * (J.m + 2)) * (Mmax + 1) :=
        hCurULe.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 4 h2kJm) (by omega))
      have h4 : chOrig.updCount idx ≤ 4 * (Mmax + 1) := by omega
      have h5 : 4 * (Mmax + 1) + 4 * (7 * Ck * (J.m + 2)) * (Mmax + 1) =
          (4 * (7 * Ck * (J.m + 2)) + 4) * (Mmax + 1) := by ring
      have h6 : (4 * (7 * Ck * (J.m + 2)) + 4) * (Mmax + 1) ≤
          (10 * (7 * Ck * (J.m + 2)) + 10) * (Mmax + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    exact lt_of_le_of_lt hSumLe (hHalfProd _ _ h2kSq hLvlSq)

/-! ## 2. Structural helpers linking intermediate `updateLoop` states to `modelPre.chain` -/

theorem rebuildSuffix_prefix_all (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ),
      let r := Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd
      (∀ j ≤ idx, r.1 j = G j) ∧
      (∀ j < idx,
        r.2.1 j = sc j ∧ r.2.2.1 j = bran j ∧ r.2.2.2.1 j = upd j ∧ r.2.2.2.2.2.2.1 j = cFwd j)
  | 0, _, _, _, _, _, _, _, _ => ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd => by
    dsimp only [Ordered.rebuildSuffix]
    set Cpartial : TreeChain :=
      { d := P.d, k := P.k, G := G, lsfs := fun j => T.lsfs (sc j), bran := bran,
        S := fun j => T.S (sc j), emb := fun j => T.emb (sc j),
        lastK := 1, lastLSFs := fun _ => ⟨G idx, ⟨G idx, ∅⟩, fun _ => 1⟩, lastBran := 0 }
    set sc_i := T.initOrd P.k (lvlM idx) N₀ (G idx) (Cpartial.chainLen ℓ₀ idx)
      (Cpartial.chainGrad g₀ idx) (Ordered.chainLevelOrd T G sc bran idx)
    set G' := fun j => if j = idx + 1 then T.S sc_i 0 else G j
    set sc' := fun j => if j = idx then sc_i else sc j
    set bran' := fun j => if j = idx then 0 else bran j
    set upd' := fun j => if j = idx then 0 else upd j
    set cEnc' := fun j => if j = idx then 0 else cEnc j
    set cDec' := fun j => if j = idx then 0 else cDec j
    set cFwd' := fun j => if j = idx then 0 else cFwd j
    have ih := rebuildSuffix_prefix_all T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1)
      G' sc' bran' upd' cEnc' cDec' cFwd'
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have h1 := ih.1 j (Nat.le_succ_of_le hj)
      simpa [G', show j ≠ idx + 1 by omega] using h1
    · obtain ⟨h1, h2, h3, h4⟩ := ih.2 j (Nat.lt_succ_of_lt hj)
      have hne : j ≠ idx := Nat.ne_of_lt hj
      exact ⟨by simpa [sc', hne] using h1,
        by simpa [bran', hne] using h2,
        by simpa [upd', hne] using h3,
        by simpa [cFwd', hne] using h4⟩

/-- Any non-rebuilt prefix of `updateLoop` agrees with the final chain state `stEnd` on all levels
`< idx` (`G`, `scState`, `bran`, `updCount`, `curFwd`), on `G idx` (when `0 < idx`), and on
`ℓ = ℓ'` (when `0 < idx`). -/
theorem updateLoop_prefix_agrees_end (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ),
      idx + rem = P.d →
      let stEnd := (Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1
      (0 < idx →
        stEnd.ℓ = ℓ' ∧
        stEnd.G idx = curG ∧
        (∀ j < idx, stEnd.G j = st.G j ∧ stEnd.scState j = st.scState j ∧
          stEnd.bran j = st.bran j ∧ stEnd.updCount j = st.updCount j ∧
          stEnd.curFwd j = st.curFwd j)) := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU curEncAcc hsum stEnd hpos
    have hieq : idx = P.d := by omega
    subst hieq
    dsimp only [stEnd]
    unfold Ordered.updateLoop
    split_ifs <;>
      exact ⟨rfl, by simp, fun j hj => ⟨by simp [show j ≠ P.d by omega], rfl, rfl, rfl, rfl⟩⟩
  | succ rem' ih =>
    intro idx st curG curU curEncAcc hsum stEnd hpos
    have hidxLt : idx < P.d := by omega
    dsimp only [stEnd]
    unfold Ordered.updateLoop
    by_cases hOver : intRebuildThreshold P N₀ idx < st.updCount idx + curU.length
    · simp only [hOver, ↓reduceIte]
      have hne0 : idx ≠ 0 := Nat.ne_of_gt hpos
      set stLG : ChainState T P :=
        { st with ℓ := rebuildStartFn idx curG ℓ', g := rebuildStartFn idx curG g' }
      set Ginit := fun j => if j = idx then rebuildStartGraph idx curG else stLG.G j
      obtain ⟨hGpre, hRestPre⟩ := rebuildSuffix_prefix_all T L P stLG.lvlM stLG.N₀
        stLG.ℓ stLG.g (P.d - idx) idx Ginit stLG.scState stLG.bran stLG.updCount
        stLG.curEnc stLG.curDecUpdates stLG.curFwd
      refine ⟨by simp [Ordered.algorithm1_rebuild, hidxLt, stLG, rebuildStartFn, hne0], ?_, fun j hj => ?_⟩
      · simp only [Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte]
        rw [hGpre idx le_rfl]
        simp [Ginit, rebuildStartGraph, hne0]
      · simp only [Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte]
        obtain ⟨hSc, hBr, hUpd, hFwd⟩ := hRestPre j hj
        refine ⟨?_, hSc, hBr, hUpd, hFwd⟩
        rw [hGpre j hj.le]
        simp [Ginit, show j ≠ idx by omega, stLG]
    · simp only [hOver, ↓reduceIte]
      obtain ⟨hℓEnd, _, hPreEnd⟩ := ih (idx + 1) _ _ _ 0 (by omega) (Nat.succ_pos idx)
      refine ⟨hℓEnd, ?_, fun j hj => ?_⟩
      · have h1 := (hPreEnd idx (Nat.lt_succ_self idx)).1
        simpa using h1
      · obtain ⟨h1, h2, h3, h4, h5⟩ := hPreEnd j (Nat.lt_succ_of_lt hj)
        have hne : j ≠ idx := Nat.ne_of_lt hj
        exact ⟨by simpa [hne] using h1, by simpa [hne] using h2, h3,
          by simpa [hne] using h4, by simpa [hne] using h5⟩

theorem chainLen_congr_upto {C₁ C₂ : TreeChain} {ℓ₁ ℓ₂ : ℕ → ℝ} (hℓ : ℓ₁ = ℓ₂) :
    ∀ k, (∀ j < k, C₁.activeLSF j = C₂.activeLSF j) →
      C₁.chainLen ℓ₁ k = C₂.chainLen ℓ₂ k
  | 0, _ => by simpa [TreeChain.chainLen] using hℓ
  | k + 1, h => by
    simp only [TreeChain.chainLen]
    rw [chainLen_congr_upto hℓ k (fun j hj => h j (Nat.lt_succ_of_lt hj)),
      h k (Nat.lt_succ_self k)]

theorem progTool_updateOrd_step_facts {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ} {G₀ G₀' : MGraph} {ℓ ℓh' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {oldCh newCh : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    (hInv0 : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ oldCh)
    (_hInv1 : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ newCh)
    (hH0 : oldCh.toTreeChain.Holds G₀ ℓ σ σ_mwu γ_ℓ γ_c)
    (hH1 : newCh.toTreeChain.Holds G₀' ℓh' σ' σ'_mwu γ'_ℓ γ'_c)
    (hInit : ∀ b < P.k, IsValidLSFInitFor lsfInit C_lsst P.k b)
    {k : ℕ} (hkd : k < P.d) {curU : List Update} {ℓk gk : ℕ → ℝ} {ordNew : ℕ → List End}
    (hGkEq : newCh.G k = (oldCh.G k).applyBatch curU)
    (hBk : (oldCh.G k).BatchIsValid curU)
    (hOrdK : OrderedBatch (oldCh.G k) curU (oldCh.levelOrd k) ordNew)
    (hScEq : newCh.scState k =
      ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd
        (oldCh.scState k) curU ℓk gk ordNew).1)
    (hBrEq : newCh.bran k = oldCh.bran k)
    (hGk1New : newCh.G (k + 1) =
      (sparseCoreProgTool lsfInit C_lsst depth impl).S (newCh.scState k) (oldCh.bran k))
    (_hOrdNewEq : ordNew = newCh.levelOrd k) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let upd := T.updateOrd (oldCh.scState k) curU ℓk gk ordNew
    let nextG := T.S upd.1 (oldCh.bran k)
    let nextU := upd.2 (oldCh.bran k)
    nextG = (oldCh.G (k + 1)).applyBatch nextU ∧
    (oldCh.G (k + 1)).BatchIsValid nextU ∧
    (∀ u ∈ nextU, match u with | .insert e _ _ => e ∈ nextG.E | _ => True) ∧
    (∀ vCap eCap, (∀ x ∈ nextG.V, x < vCap) → (∀ e ∈ nextG.E, e < eCap) →
      BatchWithinCaps vCap eCap nextU) ∧
    OrderedBatch (oldCh.G (k + 1)) nextU (T.rot (oldCh.scState k) (oldCh.bran k))
      (T.rot upd.1 (oldCh.bran k)) ∧
    (∀ e ∈ nextG.E, (∀ u ∈ nextU, ¬ u.Inserts e) →
      e ∈ (oldCh.G (k + 1)).E ∧
      (∀ u ∈ curU, ¬ u.Inserts e) ∧
      (T.lsfs upd.1 (oldCh.bran k)).wstr e = (T.lsfs (oldCh.scState k) (oldCh.bran k)).wstr e) := by
  let T := sparseCoreProgTool lsfInit C_lsst depth impl
  intro T' upd nextG nextU
  have hGk1Old : oldCh.G (k + 1) = T.S (oldCh.scState k) (oldCh.bran k) := hInv0.hGSucc k hkd
  have hNextGEqNew : nextG = newCh.G (k + 1) := by dsimp only [nextG, upd]; rw [← hScEq, hGk1New]
  cases hne : (oldCh.scState k).isNonempty with
  | false =>
    have hup := asm_updateOrd_of_empty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) (oldCh.scState k) hne curU ℓk gk ordNew
    have hSc' : upd.1 = oldCh.scState k := by dsimp only [upd]; rw [hup]
    have hU' : nextU = [] := by dsimp only [nextU, upd]; rw [hup]
    have hNG : nextG = oldCh.G (k + 1) := by dsimp only [nextG]; rw [hSc', hGk1Old]
    have hRot0 : IsRotationOrder (oldCh.G (k + 1)) (T.rot (oldCh.scState k) (oldCh.bran k)) :=
      chainInv_rot_isRotationOrder hInv0 hkd
    obtain ⟨ρ, hρ⟩ := hRot0
    refine ⟨by rw [hNG, hU']; rfl, by rw [hU']; trivial,
      fun u hu => (by rw [hU'] at hu; cases hu),
      fun _ _ _ _ u hu => (by rw [hU'] at hu; cases hu),
      by rw [hU', hSc']; exact ⟨ρ, ρ, hρ, hρ, RotationBatch.nil (fun _ => List.IsRotated.refl _)⟩,
      fun e he _ => ?_⟩
    have hEmptyS : nextG.E = ∅ := by
      rw [hNG, hGk1Old]
      change (if (oldCh.scState k).isNonempty then _ else emptyGraph).E = ∅
      simp [hne, emptyGraph]
    rw [hEmptyS] at he; cases he
  | true =>
    have hup := asm_updateOrd_of_nonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) (oldCh.scState k) hne curU ℓk gk ordNew
    have hne' : upd.1.isNonempty = true := by dsimp only [upd]; rw [hup]; exact hne
    have hOrd0 : (oldCh.scState k).ord = oldCh.levelOrd k :=
      (asm_input_inv _ _ _ _ _ _
        (levelHistory_sparseCoreOrdInput (Classical.choice (hInv0.hHist k hkd)))).2.1 hne
    let tr := (oldCh.scState k).trees (oldCh.bran k)
    let info := stepBundleTree (fun _ => canonicalSparsify impl) tr curU (oldCh.levelOrd k) ordNew
    obtain ⟨ℓ₀, hI, hcsG, hS_V⟩ := progTool_chainInv_level_compLSFInv hInv0 hInit hkd hne
    have hS_eq : oldCh.G (k + 1) = tr.S_cur := by
      rw [hGk1Old]; exact progTool_S_of_nonempty (oldCh.scState k) hne (oldCh.bran k)
    have hS'_eq : nextG = info.state.S_cur := by
      dsimp only [nextG, info, tr]
      rw [progTool_S_of_nonempty _ hne' (oldCh.bran k)]
      dsimp only [upd]; rw [hup, hOrd0]
    have hUS_eq : nextU = info.U_S := by
      dsimp only [nextU, upd, info, tr]; rw [hup, hOrd0]
    have hS_val : tr.S_cur.IsValid := hS_eq ▸ oldCh.toTreeChain.G_isValid hH0 (k + 1) hkd
    have hL_eq : tr.cs.lsf = oldCh.toTreeChain.activeLSF k := by
      simp only [TreeChain.activeLSF, ChainState.toTreeChain, hkd, ↓reduceIte]
      change tr.cs.lsf = if (oldCh.scState k).isNonempty then tr.cs.lsf else emptyLSF
      simp [hne]
    have hSp := ((hH0.2.2.2.2.1 k hkd).2.1 (oldCh.bran k) (hInv0.hBran k hkd)).2
    have hS_sub : (coreGraph tr.cs.G tr.cs.lsf).IsSubgraph tr.S_cur := by
      rw [← hS_eq, hcsG, hL_eq]
      simpa [TreeChain.activeLSF, ChainState.toTreeChain, hkd, hGk1Old] using hSp.1
    have hL'_eq : (compLSFBatch tr.cs curU).lsf = newCh.toTreeChain.activeLSF k := by
      simp only [TreeChain.activeLSF, ChainState.toTreeChain, hkd, ↓reduceIte, hBrEq]
      change (compLSFBatch tr.cs curU).lsf =
        if (newCh.scState k).isNonempty then ((newCh.scState k).trees (oldCh.bran k)).cs.lsf else emptyLSF
      rw [hScEq, ite_eq_left hne']
      change _ = (upd.1.trees (oldCh.bran k)).cs.lsf
      dsimp only [upd]; rw [hup]; rfl
    have hcsG' : (compLSFBatch tr.cs curU).G = newCh.G k := by
      rw [compLSFBatch_G, hcsG, hGkEq]
    have hS_sub' : (coreGraph (compLSFBatch tr.cs curU).G (compLSFBatch tr.cs curU).lsf).IsSubgraph
        info.state.S_cur := by
      have hbr' : newCh.bran k < newCh.toTreeChain.k := (hH1.2.2.2.2.1 k hkd).1
      have hSp' := ((hH1.2.2.2.2.1 k hkd).2.1 (newCh.bran k) hbr').2.1
      rw [← hS'_eq, hNextGEqNew, hcsG', hL'_eq]
      simpa [TreeChain.activeLSF, ChainState.toTreeChain, hkd, hBrEq, hGk1New] using hSp'
    have hReady : OutStepReady (fun _ => canonicalSparsify impl) tr curU (oldCh.levelOrd k) ordNew :=
      ⟨C_lsst, ℓ₀, hI, hcsG.symm ▸ hBk, hcsG.symm ▸ hOrdK, hS_val, hS_V, hS_sub, hS_sub'⟩
    have hBV_US : (oldCh.G (k + 1)).BatchIsValid nextU := by
      rw [hS_eq, hUS_eq]
      exact stepBundleTree_U_S_valid (fun _ => canonicalSparsify impl) hReady
    have hApp_US : nextG = (oldCh.G (k + 1)).applyBatch nextU := by
      rw [hS'_eq, hS_eq, hUS_eq]
      rfl
    obtain ⟨ρS, σS, hρS, hσS, hRotS, _⟩ :=
      outStep_rotations (fun _ => canonicalSparsify impl) tr curU (oldCh.levelOrd k) ordNew hReady
    have hRotOld : T.rot (oldCh.scState k) (oldCh.bran k) = tr.outOrder (oldCh.levelOrd k) := by
      change (if (oldCh.scState k).isNonempty then _ else _) = _
      rw [ite_eq_left hne, hOrd0]
    have hRotNew : T.rot upd.1 (oldCh.bran k) = info.state.outOrder ordNew := by
      change (if upd.1.isNonempty then _ else _) = _
      rw [ite_eq_left hne']
      dsimp only [upd, info, tr]; rw [hup, hOrd0]
    refine ⟨hApp_US, hBV_US, fun u hu => ?_, fun vCap eCap hV' hE' => ?_, ?_, fun e he hNoNext => ?_⟩
    · rw [hUS_eq, stepBundleTree_U_S_split] at hu
      cases u with
      | delete _ => trivial
      | split _ _ _ _ => trivial
      | insert e a c =>
        rw [hS'_eq]
        rcases List.mem_append.mp hu with hpre | hins
        · exfalso
          rcases List.mem_append.mp hpre with hdel | hspl
          · obtain ⟨_, -, h⟩ := List.mem_map.mp hdel; exact Update.noConfusion h
          · exact (by
              have : ∀ (keep : Finset ℕ) (UC : List Update),
                  Update.insert e a c ∉ restrictSplits keep UC := by
                intro keep UC; induction UC with
                | nil => simp [restrictSplits]
                | cons x xs ih =>
                  cases x with
                  | insert _ _ _ => exact ih
                  | delete _ => exact ih
                  | split _ _ _ _ =>
                    simp only [restrictSplits, List.mem_cons, not_or]
                    exact ⟨fun h => Update.noConfusion h, ih⟩
              exact this _ _ hspl)
        · obtain ⟨e', he', heq⟩ := List.mem_map.mp hins
          injection heq with he_eq; subst he_eq
          simp only [outInsList, Finset.mem_sort, Finset.mem_sdiff] at he'
          exact he'.1
    · rw [hS'_eq] at hV' hE'
      rw [hUS_eq]
      exact stepBundleTree_U_S_withinCaps (fun _ => canonicalSparsify impl) hV' hE'
    · refine ⟨hS_eq.symm ▸ ρS, (hS'_eq.symm.trans hApp_US) ▸ σS, ?_, ?_, ?_⟩
      · rw [oupd_rotation_cast_order, hρS, hRotOld]
      · rw [oupd_rotation_cast_order, hσS, hRotNew]
      · exact oupd_rotationBatch_cast hS_eq.symm (hS'_eq.symm.trans hApp_US) hUS_eq.symm
          (h₁ := rfl) (h₂ := rfl)
          (oupd_rotation_cast_order _ _).symm (oupd_rotation_cast_order _ _).symm hRotS
    · have heOld : e ∈ (oldCh.G (k + 1)).E := by
        have h1 : e ∈ ((oldCh.G (k + 1)).applyBatch nextU).E := hApp_US ▸ he
        have hmem : ∀ {H : MGraph} {W : List Update},
            e ∈ (H.applyBatch W).E → (∀ x ∈ W, ¬ x.Inserts e) → e ∈ H.E := by
          intro H W; induction W generalizing H with
          | nil => intro h _; exact h
          | cons x xs ihW =>
            intro hx hnx
            have h2 := ihW hx (fun y hy => hnx y (List.mem_cons_of_mem _ hy))
            have hnx0 := hnx x List.mem_cons_self
            cases x with
            | insert e0 a b =>
              have hne0 : e ≠ e0 := fun heq => hnx0 (by simpa [Update.Inserts] using heq.symm)
              simpa [MGraph.applyUpdate, hne0] using h2
            | delete e0 =>
              simp only [MGraph.applyUpdate, Finset.mem_erase] at h2; exact h2.2
            | split _ _ _ _ => exact h2
        exact hmem h1 hNoNext
      have hNoCur : ∀ u ∈ curU, ¬ u.Inserts e := by
        intro u hu hIns
        have hfGk : e ∈ (oldCh.G k).E :=
          (Finset.mem_sdiff.mp (oldCh.toTreeChain.G_succ_E_subset hH0 hkd heOld)).1
        have hfDel : e ∈ batchDeletes curU :=
          mem_batchDeletes_of_inserts_of_mem_E hBk hfGk ⟨u, hu, hIns⟩
        have hfTgt : e ∈ info.state.S_cur.E := hS'_eq ▸ he
        have hnotKeep : e ∉ ((tr.S_cur.E ∩ info.state.S_cur.E) \ batchDeletes curU) \ info.D_total :=
          fun hk => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hk).1).2 hfDel
        obtain ⟨u1, hu1, hIns1⟩ := buildUSOrd_inserts_of_not_keep
          (coreBatchOf tr.cs (oldCh.levelOrd k) ordNew curU) curU
          (compLSFBatch tr.cs curU) tr.S_cur info.state.S_cur.E info.D_total hfTgt hnotKeep
        have hu1' : u1 ∈ nextU := by
          rw [hUS_eq, stepBundleTree_U_S_eq]
          exact hu1
        exact hNoNext u1 hu1' hIns1
      have hWstrEq : (T.lsfs upd.1 (oldCh.bran k)).wstr e =
          (T.lsfs (oldCh.scState k) (oldCh.bran k)).wstr e := by
        change (if upd.1.isNonempty then _ else emptyLSF).wstr e =
          (if (oldCh.scState k).isNonempty then _ else emptyLSF).wstr e
        rw [ite_eq_left hne', ite_eq_left hne]
        change (upd.1.trees (oldCh.bran k)).cs.lsf.wstr e = tr.cs.lsf.wstr e
        have hcsEq : (upd.1.trees (oldCh.bran k)).cs = compLSFBatch tr.cs curU := by
          dsimp only [upd, tr]; rw [hup]; rfl
        rw [hcsEq]
        exact compLSFBatch_wstr_of_not_inserts tr.cs curU hNoCur
      exact ⟨heOld, hNoCur, hWstrEq⟩

/-! ## 3. Full dry-run `UpdateLoopModelInv` derivation -/

lemma updateRebuildModelInv_of_end (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap1 : ∀ e, 1 ≤ J.capacity e)
    {w wordExp stretchPrec : ℕ}
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤ w)
    (hWordLvl :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      ∀ j < cfg.P.d,
        levelM cfg.TP cfg.P j < 2 ^ w ∧
        (levelM cfg.TP cfg.P j + cfg.N₀ + 2) ^ wordExp * (F.limbs + 1) < 2 ^ w)
    (hStretchLe :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      stretchPrec ≤ 100 * ipmQualityRangeExponent I.m V k)
    {st : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    {first extraEnc : ℕ} {Gstart : MGraph} {ℓstart gstart : ℕ → ℝ}
    (hRebW : st.rebuildCount first + 1 < 2 ^ w)
    (hInvEnd :
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let stLG : ChainState cfg.T cfg.P := { st with ℓ := ℓstart, g := gstart }
      Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
        (Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stLG first Gstart extraEnc).1)
    (hGridEnd :
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let stLG : ChainState cfg.T cfg.P := { st with ℓ := ℓstart, g := gstart }
      DryChainLenGridInv J
        (Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stLG first Gstart extraEnc).1) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    UpdateRebuildModelInv w F.limbs F.fmt.precision wordExp stretchPrec st first Gstart ℓstart
      gstart extraEnc := by
  intro I V k F
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1
  set stLG : ChainState cfg.T cfg.P := { st with ℓ := ℓstart, g := gstart }
  set next := (Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stLG first Gstart extraEnc).1
  have hB := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hInvEnd
  refine ⟨hRebW, hInvEnd.hLastK, fun j _ hj => ?_,
    drySC_lastLevelBuildEqOnE J (next.G cfg.P.d) _ (next.toTreeChain.chainLen next.ℓ cfg.P.d)
      (fun e he => ite_eq_left he),
    fun e he => lt_of_lt_of_le (by positivity) ((hGridEnd.2.2.1 cfg.P.d le_rfl).1 e he).1,
    dryChainLenGridInv_implies_lastStretchFits J hJn hJm hCap1 hInvEnd hGridEnd hStretchLe⟩
  have hLvlM : next.lvlM j = levelM cfg.TP cfg.P j := congrFun hInvEnd.hLvlM j
  have hN0 : next.N₀ = cfg.N₀ := hInvEnd.hN0
  refine ⟨by rw [hLvlM]; exact_mod_cast (hB j hj.le).2.2.1,
    by rw [hN0]; exact (Finset.card_le_card (hB j hj.le).2.1).trans (hInvEnd.hN0 ▸ hInvEnd.hG0n),
    by rw [hLvlM]; exact (hWordLvl j hj).1,
    by rw [hLvlM, hN0]; exact (hWordLvl j hj).2,
    chainInv_levelOrd_isRotationOrder hInvEnd hj,
    fun e he => lt_of_lt_of_le (by positivity) ((hGridEnd.2.2.1 j hj.le).1 e he).1,
    chainInv_G_succ_E_subset hV hInvEnd hj,
    dryChainLenGridInv_implies_coreLenFits J hJn hJm hCap1 hGridEnd j hj⟩


theorem progTool_updateOrd_step_facts_eq {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {T : SparseCoreRestartTool} (hT : T = sparseCoreProgTool lsfInit C_lsst depth impl)
    {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ} {G₀ G₀' : MGraph} {ℓ ℓh' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {oldCh newCh : ChainState T P}
    (hInv0 : Ordered.ChainInv T L TP LP P N₀ oldCh)
    (hInv1 : Ordered.ChainInv T L TP LP P N₀ newCh)
    (hH0 : oldCh.toTreeChain.Holds G₀ ℓ σ σ_mwu γ_ℓ γ_c)
    (hH1 : newCh.toTreeChain.Holds G₀' ℓh' σ' σ'_mwu γ'_ℓ γ'_c)
    (hInitAll : ∀ b < P.k, IsValidLSFInitFor lsfInit C_lsst P.k b)
    {k : ℕ} (hk : k < P.d)
    {curU : List Update} {ℓi gi : ℕ → ℝ} {ordNew : ℕ → List End}
    (hGkEq : newCh.G k = (oldCh.G k).applyBatch curU)
    (hBatchK : (oldCh.G k).BatchIsValid curU)
    (hOrdK : OrderedBatch (oldCh.G k) curU (oldCh.levelOrd k) ordNew)
    (hScEq : newCh.scState k = (T.updateOrd (oldCh.scState k) curU ℓi gi ordNew).1)
    (hBrEq : newCh.bran k = oldCh.bran k)
    (hGk1New : newCh.G (k + 1) = T.S (newCh.scState k) (oldCh.bran k))
    (hOrdNewEq : ordNew = newCh.levelOrd k) :
    let upd := T.updateOrd (oldCh.scState k) curU ℓi gi ordNew
    let nextG := T.S upd.1 (oldCh.bran k)
    let nextU := upd.2 (oldCh.bran k)
    nextG = (oldCh.G (k + 1)).applyBatch nextU ∧
    (oldCh.G (k + 1)).BatchIsValid nextU ∧
    (∀ u ∈ nextU, match u with | .insert e _ _ => e ∈ nextG.E | _ => True) ∧
    (∀ vCap eCap, (∀ x ∈ nextG.V, x < vCap) → (∀ e ∈ nextG.E, e < eCap) →
      BatchWithinCaps vCap eCap nextU) ∧
    OrderedBatch (oldCh.G (k + 1)) nextU
      (T.rot (oldCh.scState k) (oldCh.bran k))
      (T.rot upd.1 (oldCh.bran k)) ∧
    (∀ e ∈ nextG.E, (∀ u ∈ nextU, ¬ u.Inserts e) →
      e ∈ (oldCh.G (k + 1)).E ∧
      (∀ u ∈ curU, ¬ u.Inserts e) ∧
      (T.lsfs upd.1 (oldCh.bran k)).wstr e = (T.lsfs (oldCh.scState k) (oldCh.bran k)).wstr e) := by
  subst hT
  exact progTool_updateOrd_step_facts hInv0 hInv1 hH0 hH1 hInitAll hk hGkEq hBatchK hOrdK hScEq
    hBrEq hGk1New hOrdNewEq

theorem progTool_updateOrd_cost_mono_eq {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {T : SparseCoreRestartTool} (hT : T = sparseCoreProgTool lsfInit C_lsst depth impl)
    (st : T.State) (U : List Update) (ℓ g : ℕ → ℝ) (ordNew : ℕ → List End) :
    T.cost st ≤ T.cost (T.updateOrd st U ℓ g ordNew).1 := by
  subst hT
  exact progTool_updateOrd_cost_mono st U ℓ g ordNew

end MinCostFlow.Final.DryRun
