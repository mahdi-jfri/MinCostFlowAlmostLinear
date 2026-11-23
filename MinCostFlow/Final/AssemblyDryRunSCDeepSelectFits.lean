module

public import MinCostFlow.Final.AssemblyDryRunSCDeepGrid
public import MinCostFlow.Final.AssemblyDryRunSCSelInitFacts
import MinCostFlow.LastLevelProgram.RepresentativeGraph
import Mathlib.Tactic

/-!
# Post-shift fixed-point length fit helpers for `dryDeepSelectCode` (`AssemblyDryRunSCDeepSelectFits`)

Discharges the two post-shift fixed-point length fit hypotheses (`hLenFitInt` and `hLenFitLast`)
of `shiftDeepSelectBody_runs` (`MinRatio/WireShiftDeepSelect.lean`) from `Ordered.ShiftLoopChainInv`
and `DryChainLenGridInv`:

* `dryDeepSel_hLenFitInt`: proves `Num.Fits 4 L q` and `(q : ℝ) / 2 ^ P = chainLen ℓ (j + 1) e`
  for every interior level `j < cfg.P.d` and every edge `e ∈ (ch.G j).E`.
* `dryDeepSel_hLenFitLast`: proves both `Num.Fits 4 L (prevInt * 2 ^ pLast)` and
  `∃ q, Num.Fits 4 L q ∧ (q : ℝ) / 2 ^ (P + pLast) = chainLen ℓ (cfg.P.d + 1) e` for every edge
  `e ∈ (ch'.G cfg.P.d).E` after `Ordered.algorithm1_shift` at `i₀ < cfg.P.d`, at
  `pLast = dryLastStretchP J`.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

private lemma fits_of_nonneg_mul_pow_lt_ds {L Q : ℕ} {z : ℤ} {r : ℝ}
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

private lemma roundStretch_on_grid_le_ds {pw pLast : ℕ} (hle : pw ≤ pLast) (s : ℝ) :
    ∃ wInt : ℤ, (wInt : ℝ) / (2 : ℝ) ^ pLast = roundStretch pw s := by
  refine ⟨(-⌊(-s) * (2 : ℝ) ^ pw⌋) * (2 : ℤ) ^ (pLast - pw), ?_⟩
  unfold roundStretch Num.dyadicFloor
  push_cast
  have hpow : (2 : ℝ) ^ pLast = (2 : ℝ) ^ pw * (2 : ℝ) ^ (pLast - pw) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  rw [hpow]
  have h1 : (2 : ℝ) ^ (pLast - pw) ≠ 0 := by positivity
  field_simp [h1]

/-- Discharges `hLenFitInt` (`shiftDeepSelectBody_runs`) for every interior level `j < cfg.P.d`
and every edge `e ∈ (ch.G j).E` from `Ordered.ChainInv` and `DryChainLenGridInv`. -/
theorem dryDeepSel_hLenFitInt (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hInv : Ordered.ChainInv (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).L
      (concreteCirculationCfgWithLast dryWitnessUsed J).TP
      (concreteCirculationCfgWithLast dryWitnessUsed J).LP
      (concreteCirculationCfgWithLast dryWitnessUsed J).P
      (concreteCirculationCfgWithLast dryWitnessUsed J).N₀ ch)
    (hGridInv : DryChainLenGridInv J ch) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let P := ipmQualityPrecision I.m V k
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    ∀ j < cfg.P.d, ∀ e ∈ (ch.G j).E,
      ∃ q : ℤ, Num.Fits 4 L q ∧
        (q : ℝ) / (2 : ℝ) ^ P = ch.toTreeChain.chainLen ch.ℓ (j + 1) e := by
  intro I V k P L cfg j hj e he
  let E := ipmQualityRangeExponent I.m V k
  have hIm1 : 1 ≤ I.m :=
    Nat.lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap).1
  obtain ⟨_, _, hLvls, hBrs, _⟩ := hGridInv
  obtain ⟨hloJ, _⟩ := (hLvls j hj.le).1 e he
  obtain ⟨hw1, hhi, q, hq⟩ := hBrs j hj (ch.bran j) (hInv.hBran j hj) e he
  have hcl : ch.toTreeChain.chainLen ch.ℓ (j + 1) e =
      (cfg.T.lsfs (ch.scState j) (ch.bran j)).wstr e * ch.toTreeChain.chainLen ch.ℓ j e := by
    change (if j < cfg.P.d then cfg.T.lsfs (ch.scState j) (ch.bran j) else ch.lastLSFs ch.lastBran).wstr e *
      ch.toTreeChain.chainLen ch.ℓ j e = _
    rw [ite_eq_left hj]
  have hnn : 0 ≤ ch.toTreeChain.chainLen ch.ℓ (j + 1) e := by
    rw [hcl]
    exact mul_nonneg (le_trans zero_le_one hw1) (le_trans (by positivity) hloJ)
  have hExp : (j + 1) * (3 * I.m.size + 12) ≤ E :=
    (Nat.mul_le_mul_right _ hj).trans (chainLen_exponent_le_rangeExponent I.m V
      (concreteQualityBudgetWithLast dryWitnessUsed) hIm1 cfg.P.hM₀)
  have h2E : ch.toTreeChain.chainLen ch.ℓ (j + 1) e ≤ (2 : ℝ) ^ (2 * E) := by
    rw [hcl]
    have hsum : E + (j + 1) * (3 * I.m.size + 12) ≤ 2 * E := by omega
    exact hhi.trans (pow_le_pow_right₀ (by norm_num) hsum)
  have hltCap : ch.toTreeChain.chainLen ch.ℓ (j + 1) e * (2 : ℝ) ^ P <
      (Num.capacity 4 L : ℝ) / 2 := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    calc ch.toTreeChain.chainLen ch.ℓ (j + 1) e * (2 : ℝ) ^ P * 2
        = 2 * (ch.toTreeChain.chainLen ch.ℓ (j + 1) e * (2 : ℝ) ^ P) := by ring
      _ ≤ 2 * ((2 : ℝ) ^ (2 * E) * (2 : ℝ) ^ P) := by gcongr
      _ = (2 : ℝ) ^ (P + 2 * E + 1) := by rw [pow_succ, pow_add]; ring
      _ < (Num.capacity 4 L : ℝ) := coreLen_pow_lt_capacity I.m V k
  exact ⟨q, fits_of_nonneg_mul_pow_lt_ds (hq.trans hcl.symm) hnn hltCap, hq.trans hcl.symm⟩

/-- Discharges `hLenFitLast` (`shiftDeepSelectBody_runs`) for the post-shift chain
`ch' = (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1` (`i₀ < cfg.P.d`) at
`pLast = dryLastStretchP J`. -/
theorem dryDeepSel_hLenFitLast (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hShift : Ordered.ShiftLoopChainInv (concreteCirculationCfgWithLast dryWitnessUsed J) ch)
    (hGridInv : DryChainLenGridInv J ch)
    {i₀ : ℕ} (hi₀ : i₀ < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let P := ipmQualityPrecision I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let ch' := (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1
    let pLast := dryLastStretchP J
    ∀ e ∈ (ch'.G cfg.P.d).E,
      (∀ (prevLen : ℕ) (m' : ℕ → ℕ),
        EdgeValuesAt m' prevLen 4 L P (ch'.G cfg.P.d).E (ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d) →
        Num.Fits 4 L (Num.intVal m' (prevLen + e * L) 4 L * (2 : ℤ) ^ pLast)) ∧
      ∃ q : ℤ, Num.Fits 4 L q ∧
        (q : ℝ) / (2 : ℝ) ^ (P + pLast) = ch'.toTreeChain.chainLen ch'.ℓ (cfg.P.d + 1) e := by
  intro I V k L P cfg ch' pLast e he
  let E := ipmQualityRangeExponent I.m V k
  have hVcfg := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hIm1 : 1 ≤ I.m := lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap).1
  have hShift' : Ordered.ShiftLoopChainInv cfg ch' := hShift.shift hVcfg i₀ hi₀.le
  have hInv' := hShift'.1
  have hGrid' : DryChainLenGridInv J ch' := dryChainLenGridInv_shift J hJn hJm hCap hShift hGridInv hi₀.le
  obtain ⟨hG0m', hG0n', hLvls', _, _⟩ := hGrid'
  obtain ⟨hBoundsD, hGridD⟩ := hLvls' cfg.P.d le_rfl
  obtain ⟨q0, hq0Eq⟩ := hGridD e he
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
  have hLenD_pos : 0 < ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d e :=
    lt_of_lt_of_le (by positivity) (hBoundsD e he).1
  have hLenD_le : ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d e ≤ (2 : ℝ) ^ (2 * E) := by
    have hexpLe : E + cfg.P.d * (3 * I.m.size + 12) ≤ 2 * E := by
      dsimp only [E, I, V, k, cfg] at hExp ⊢; omega
    exact (hBoundsD e he).2.trans (pow_le_pow_right₀ (by norm_num) hexpLe)
  have hCap4Eq : (Num.capacity 4 L : ℝ) = (2 : ℝ) ^ (4 * L) := by
    rw [Num.capacity, Num.base, ← pow_mul]
    push_cast; rfl
  have hLenD_mul_lt :
      ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d e * (2 : ℝ) ^ (P + pLast) <
        (Num.capacity 4 L : ℝ) / 2 := by
    have h1 : ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d e * (2 : ℝ) ^ (P + pLast) ≤
        (2 : ℝ) ^ (2 * E) * (2 : ℝ) ^ (P + 40 * E) :=
      mul_le_mul hLenD_le (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity) (by positivity)
    have h2 : (2 : ℝ) ^ (2 * E) * (2 : ℝ) ^ (P + 40 * E) = (2 : ℝ) ^ (P + 42 * E) := by
      rw [← pow_add]; exact congrArg ((2 : ℝ) ^ ·) (by omega)
    have h3 : (2 : ℝ) ^ (P + 42 * E) * 2 = (2 : ℝ) ^ (P + 42 * E + 1) := (pow_succ 2 _).symm
    have h4 : (2 : ℝ) ^ (P + 42 * E + 1) < (2 : ℝ) ^ (4 * L) :=
      pow_lt_pow_right₀ (by norm_num) (by omega)
    rw [hCap4Eq, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hSubE0 : (ch'.G cfg.P.d).E ⊆ (ch'.G 0).E :=
    chainInv_G_E_subset_G0 hVcfg hInv' cfg.P.d le_rfl
  have hGdM : (ch'.G cfg.P.d).m ≤ I.m := (Finset.card_le_card hSubE0).trans hG0m'
  have hB' := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hVcfg.hTP hVcfg.hγM₀ hVcfg.hγk hInv' cfg.P.d le_rfl
  have hGdN : (ch'.G cfg.P.d).n ≤ 2 * I.m + 2 := (Finset.card_le_card hB'.2.1).trans hG0n'
  have hEx := ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P ch hi₀
  have hℓEq : ch'.ℓ = ch.ℓ := hEx.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLastEq : ch'.lastLSFs =
      (dryLastTool.build (ch'.G cfg.P.d) (ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d)).2 := by
    have h := congrArg Prod.snd hEx.2.2.2.2.2.2.2.2.2.1
    rw [← hℓEq] at h
    exact h
  have hwstrGrid : ∃ wInt : ℤ,
      (wInt : ℝ) / (2 : ℝ) ^ pLast = (ch'.lastLSFs ch'.lastBran).wstr e := by
    rw [hLastEq]
    unfold dryLastTool fixedPointLastLevelTool
    dsimp only
    by_cases hne : (nonLoopEdges (ch'.G cfg.P.d)).Nonempty
    · simp only [hne, ↓reduceIte]
      by_cases hmem : e ∈ nonLoopEdges (ch'.G cfg.P.d)
      · simp only [hmem, ↓reduceIte, stretchQuery]
        set H := representativeGraph (ch'.G cfg.P.d) (ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d)
        have hHm : H.m ≤ (ch'.G cfg.P.d).m := by
          change (((nonLoopEdges (ch'.G cfg.P.d)).image (edgePairKey (ch'.G cfg.P.d))).image
            (shortestEdge (ch'.G cfg.P.d) (ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d))).card ≤
            (ch'.G cfg.P.d).E.card
          exact (Finset.card_image_le.trans Finset.card_image_le).trans (Finset.card_filter_le _ _)
        have hpwLe : weightPrecision lastCanonConst H ≤ pLast := by
          have h1 := representativeGraph_weightPrecision_le lastCanonConst (ch'.G cfg.P.d)
            (ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d)
          have h2 : (H.m + 1).size ≤ (I.m + 1).size :=
            Nat.size_le_size (Nat.add_le_add_right (hHm.trans hGdM) 1)
          dsimp only [pLast, dryLastStretchP, H, I] at h1 h2 ⊢
          omega
        exact roundStretch_on_grid_le_ds hpwLe _
      · simp only [hmem, ↓reduceIte]
        exact ⟨(2 : ℤ) ^ pLast, by push_cast; exact div_self (by positivity)⟩
    · simp only [hne, ↓reduceIte]
      exact ⟨(2 : ℤ) ^ pLast, by push_cast; exact div_self (by positivity)⟩
  obtain ⟨wInt, hwIntEq⟩ := hwstrGrid
  have hActD : ch'.toTreeChain.activeLSF cfg.P.d = ch'.lastLSFs ch'.lastBran := by
    unfold TreeChain.activeLSF; simp [ChainState.toTreeChain]
  have hLenD1Eq : ch'.toTreeChain.chainLen ch'.ℓ (cfg.P.d + 1) e =
      (ch'.lastLSFs ch'.lastBran).wstr e * ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d e := by
    change (ch'.toTreeChain.activeLSF cfg.P.d).wstr e *
      ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d e = _
    rw [hActD]
  have hqCast : ((wInt * q0 : ℤ) : ℝ) / (2 : ℝ) ^ (P + pLast) =
      ch'.toTreeChain.chainLen ch'.ℓ (cfg.P.d + 1) e := by
    rw [hLenD1Eq, ← hwIntEq, ← hq0Eq, pow_add]
    push_cast; ring
  have hLastH := hInv'.hLastHolds ch'.lastBran hInv'.hLastBran
  have hHolds := (hInv'.toTreeChain_holds_noHidden hVcfg.hσ_mwu_mono hVcfg.hTP hVcfg.hLP hVcfg.hMWU
    hVcfg.hEmb hVcfg.hγM₀ hVcfg.hγk).1
  have hSubD := ch'.toTreeChain.forestsAreSubgraphs_of_holds hHolds cfg.P.d le_rfl
  rw [hActD] at hSubD
  have hwstr_bounds : 1 ≤ (ch'.lastLSFs ch'.lastBran).wstr e ∧
      (ch'.lastLSFs ch'.lastBran).wstr e ≤ cfg.LP.σ_last (ch'.G cfg.P.d).n := by
    have hnn : ∀ f ∈ (ch'.G cfg.P.d).E, 0 ≤ ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d f :=
      fun f hf => le_trans (by positivity) (hBoundsD f hf).1
    have h1 := one_le_stretch hSubD hnn he
    have h2 := hLastH.2.2.2 e he
    exact ⟨le_trans h1 h2.1, h2.2⟩
  have hLenD1_nn : 0 ≤ ch'.toTreeChain.chainLen ch'.ℓ (cfg.P.d + 1) e := by
    rw [hLenD1Eq]; exact mul_nonneg (le_trans zero_le_one hwstr_bounds.1) hLenD_pos.le
  have hSigLe : cfg.LP.σ_last (ch'.G cfg.P.d).n ≤ (2 : ℝ) ^ (k + 4 * I.m.size + 18) := by
    set nD := (ch'.G cfg.P.d).n
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
  refine ⟨fun prevLen m' hEv => ?_, wInt * q0, ?_, hqCast⟩
  · refine fits_of_nonneg_mul_pow_lt_ds (Q := P + pLast) ?_ hLenD_pos.le hLenD_mul_lt
    push_cast
    rw [pow_add, mul_div_mul_right _ _ (by positivity)]
    exact (hEv e he).2
  · refine fits_of_nonneg_mul_pow_lt_ds hqCast hLenD1_nn ?_
    have hProdLe : ch'.toTreeChain.chainLen ch'.ℓ (cfg.P.d + 1) e * (2 : ℝ) ^ (P + pLast) ≤
        (2 : ℝ) ^ (P + 43 * E + 4 * I.m.size + 18) := by
      rw [hLenD1Eq]
      have h1 : (ch'.lastLSFs ch'.lastBran).wstr e *
          ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d e ≤
          (2 : ℝ) ^ (k + 4 * I.m.size + 18) * (2 : ℝ) ^ (2 * E) :=
        mul_le_mul (hwstr_bounds.2.trans hSigLe) hLenD_le hLenD_pos.le (by positivity)
      have h2 : (2 : ℝ) ^ (P + pLast) ≤ (2 : ℝ) ^ (P + 40 * E) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      calc (ch'.lastLSFs ch'.lastBran).wstr e *
              ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d e * (2 : ℝ) ^ (P + pLast)
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

end MinCostFlow.Final.DryRun

end
