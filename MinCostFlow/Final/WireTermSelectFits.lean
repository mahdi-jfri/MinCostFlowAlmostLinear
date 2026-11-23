module

public import MinCostFlow.Final.WireSelectDryFits
public import MinCostFlow.MinRatio.WireSelectHeapLayout
import MinCostFlow.LastLevelProgram.RepresentativeGraph
import Mathlib.Tactic

/-!
# Dry-run terminal-level dyadic stretch grid, length fits, and heap-size bounds (`WireTermSelectFits`)

Supplies the model-level facts required by `shiftTermSelectBody_runs` (`WireShiftTermSelect.lean`)
and by the dry-run terminal shift code block (`AssemblyDryRunSCTermCode.lean`):

* `DryLastWstrDyadic J ch`: every branch `j < ch.lastK` at terminal level `d` has
  `2 ^ (-dryLastStretchP J)`-dyadic stretch estimates on `(ch.G cfg.P.d).E`.
* `dryLastWstrDyadic_of_build`: holds for every `dryLastTool.build G ℓ` when `G.m ≤ I.m`.
* `dryLastWstrDyadic_init`, `dryLastWstrDyadic_shift`: established at `Init` and preserved across
  every `Shift` (deep or terminal).
* `dry_levelD_lenFits_of_shiftLoop`: discharges the level-`d` `hLenFits` hypothesis of
  `shiftTermSelectBody_runs` (`qp * 2 ^ pLast` and `q / 2 ^ (P + pLast) = chainLen (d + 1)`) from
  `ShiftLoopChainInv`, `DryChainLenGridInv`, and `DryLastWstrDyadic`.
* `selectHeap_size_le_G0_m`: under `SelectHeapMatchesChain`, `size ≤ (C.G 0).m`.
* `dry_selectPhiBoundedAt_of_termShift`: preserves `SelectPhiBoundedAt` at all levels `0 .. d`
  across `shiftTermSelectBody_runs` via `selectPhiBoundedAt_of_phiFill`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Scaling.Machine
  MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Terminal-level dyadic stretch invariant (`DryLastWstrDyadic`) -/

/-- Every branch `j < ch.lastK` of the terminal collection has `2 ^ (-dryLastStretchP J)`-dyadic
stretch values on `(ch.G cfg.P.d).E`. -/
def DryLastWstrDyadic (J : Circulation)
    (ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P) : Prop :=
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  ∀ j < ch.lastK, ∀ e ∈ (ch.G cfg.P.d).E,
    ∃ a : ℤ, (a : ℝ) / (2 : ℝ) ^ dryLastStretchP J = (ch.lastLSFs j).wstr e

/-- Any `fixedPointLastLevelTool` build on a graph `G` with `G.m ≤ (solverConnectedAugmented J).m`
produces `2 ^ (-dryLastStretchP J)`-dyadic stretch values on every edge of `G`. -/
theorem dryLastWstrDyadic_of_build (J : Circulation) (G : MGraph) (ℓ : ℕ → ℝ)
    (hGm : G.m ≤ (solverConnectedAugmented J).m) :
    let res := (concreteCirculationCfgWithLast dryWitnessUsed J).L.build G ℓ
    ∀ j < res.1, ∀ e : ℕ,
      ∃ a : ℤ, (a : ℝ) / (2 : ℝ) ^ dryLastStretchP J = (res.2 j).wstr e := by
  intro res j _ e
  change ∃ a : ℤ, (a : ℝ) / (2 : ℝ) ^ dryLastStretchP J =
    (((fixedPointLastLevelTool lastOracle lastCanonConst).build G ℓ).2 j).wstr e
  unfold fixedPointLastLevelTool
  dsimp only
  split_ifs with hne
  · by_cases heNL : e ∈ nonLoopEdges G
    · simp only [heNL, ↓reduceIte]
      let H := representativeGraph G ℓ
      let Pw := weightPrecision lastCanonConst H
      have hHm : H.m ≤ G.m := by
        rw [show H.m = ((nonLoopEdges G).image (edgePairKey G)).card from representativeGraph_m G ℓ]
        exact Finset.card_image_le.trans (Finset.card_le_card (Finset.filter_subset _ _))
      have hPwLe : Pw ≤ dryLastStretchP J := by
        have h1 : Pw ≤ (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (H.m + 1).size :=
          representativeGraph_weightPrecision_le lastCanonConst G ℓ
        have h2 : (H.m + 1).size ≤ ((solverConnectedAugmented J).m + 1).size :=
          Nat.size_le_size (by omega)
        unfold dryLastStretchP
        omega
      set z : ℤ := -⌊-(treeStretch H (lastOracle H (LSF.safeLen H ℓ)
        (weights Pw (roundedScale lastCanonConst H) (stretchQuery lastOracle H ℓ Pw) j))
        (LSF.safeLen H ℓ) (shortestEdge G ℓ (edgePairKey G e))) * (2 : ℝ) ^ Pw⌋
      refine ⟨z * (2 : ℤ) ^ (dryLastStretchP J - Pw), ?_⟩
      have hpow : (2 : ℝ) ^ dryLastStretchP J = (2 : ℝ) ^ Pw * (2 : ℝ) ^ (dryLastStretchP J - Pw) := by
        rw [← pow_add, Nat.add_sub_of_le hPwLe]
      rw [hpow, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, mul_div_mul_right _ _ (by positivity)]
      simp only [z, H, Pw, stretchQuery, roundStretch, Num.dyadicFloor, Int.cast_neg, neg_div]
    · simp only [heNL, ↓reduceIte]
      refine ⟨(2 : ℤ) ^ dryLastStretchP J, ?_⟩
      rw [Int.cast_pow, Int.cast_ofNat, div_self (by positivity)]
  · refine ⟨(2 : ℤ) ^ dryLastStretchP J, ?_⟩
    rw [Int.cast_pow, Int.cast_ofNat, div_self (by positivity)]

/-- `DryLastWstrDyadic` follows directly from `DryChainLenGridInv`. -/
theorem dryLastWstrDyadic_of_gridInv (J : Circulation)
    {ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hGrid : DryChainLenGridInv J ch) :
    DryLastWstrDyadic J ch := by
  obtain ⟨Gd, ℓd, hGdm, hBuild⟩ := hGrid.2.2.2.2
  intro j hj e _
  have hres := dryLastWstrDyadic_of_build J Gd ℓd hGdm
  have hkEq : ch.lastK = ((concreteCirculationCfgWithLast dryWitnessUsed J).L.build Gd ℓd).1 :=
    congrArg Prod.fst hBuild
  have hlEq : ch.lastLSFs = ((concreteCirculationCfgWithLast dryWitnessUsed J).L.build Gd ℓd).2 :=
    congrArg Prod.snd hBuild
  rw [hlEq]
  exact hres j (hkEq ▸ hj) e

/-- `DryLastWstrDyadic` holds immediately after `algorithm1_initialize` when `(ch0.G d).m ≤ I.m`. -/
theorem dryLastWstrDyadic_init (J : Circulation) (ℓ₀ g₀ : ℕ → ℝ)
    (hGdM :
      let I := solverConnectedAugmented J
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let ch0 := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
        (levelM cfg.TP cfg.P) cfg.N₀ (namedInstance I) ℓ₀ g₀).1
      (ch0.G cfg.P.d).m ≤ I.m) :
    let I := solverConnectedAugmented J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let ch0 := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
      (levelM cfg.TP cfg.P) cfg.N₀ (namedInstance I) ℓ₀ g₀).1
    DryLastWstrDyadic J ch0 := by
  intro I cfg ch0
  have hBuilt : (ch0.lastK, ch0.lastLSFs) =
      cfg.L.build (ch0.G cfg.P.d) (ch0.toTreeChain.chainLen ℓ₀ cfg.P.d) :=
    (ordAlgorithm1_initialize_level_facts
      (sparseCoreBundleRestartToolMachWith_initOrdEqOnE _ _ _ _ _ _)
      cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ (namedInstance I) ℓ₀ g₀).2.2.2.1
  intro j hj e he
  have hres := dryLastWstrDyadic_of_build J (ch0.G cfg.P.d)
    (ch0.toTreeChain.chainLen ℓ₀ cfg.P.d) hGdM
  have hkEq : ch0.lastK = (cfg.L.build (ch0.G cfg.P.d) (ch0.toTreeChain.chainLen ℓ₀ cfg.P.d)).1 :=
    congrArg Prod.fst hBuilt
  have hlEq : ch0.lastLSFs = (cfg.L.build (ch0.G cfg.P.d) (ch0.toTreeChain.chainLen ℓ₀ cfg.P.d)).2 :=
    congrArg Prod.snd hBuilt
  change ∃ a : ℤ, (a : ℝ) / (2 : ℝ) ^ dryLastStretchP J = (ch0.lastLSFs j).wstr e
  rw [hlEq]
  exact hres j (hkEq ▸ hj) e

/-- `DryLastWstrDyadic` is preserved across `algorithm1_shift` at every level `i₀ ≤ cfg.P.d`
(both deep shifts `i₀ < cfg.P.d` and terminal shifts `i₀ = cfg.P.d`). -/
theorem dryLastWstrDyadic_shift (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hShift : Chain.Ordered.ShiftLoopChainInv (concreteCirculationCfgWithLast dryWitnessUsed J) ch)
    (hG0m : (ch.G 0).m ≤ (solverConnectedAugmented J).m)
    (hDy : DryLastWstrDyadic J ch)
    {i₀ : ℕ} (hi₀ : i₀ ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.d) :
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    DryLastWstrDyadic J (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1 := by
  intro cfg
  by_cases hid : i₀ < cfg.P.d
  · have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
    have hInv' := hShift.shift hV i₀ hi₀
    have hTH' := hInv'.1.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
      hV.hγM₀ hV.hγk
    set ch' := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1
    have hEx := ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P ch hid
    have hG0eq : ch'.G 0 = ch.G 0 := hEx.1 0 (Nat.zero_le _)
    have hGdM : (ch'.G cfg.P.d).m ≤ (solverConnectedAugmented J).m :=
      (Finset.card_le_card (ch'.toTreeChain.G_E_subset_of_le hTH'.1 (Nat.zero_le _) le_rfl)).trans
        (by simpa [ChainState.toTreeChain, MGraph.m, hG0eq] using hG0m)
    have hBuilt : (ch'.lastK, ch'.lastLSFs) =
        cfg.L.build (ch'.G cfg.P.d) (ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d) := by
      have hres := hEx.2.2.2.2.2.2.2.2.2.1
      have hℓeq : ch'.ℓ = ch.ℓ := hEx.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simpa [ch', hℓeq] using hres
    intro j hj e he
    have hres := dryLastWstrDyadic_of_build J (ch'.G cfg.P.d)
      (ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d) hGdM
    have hkEq : ch'.lastK = (cfg.L.build (ch'.G cfg.P.d) (ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d)).1 :=
      congrArg Prod.fst hBuilt
    have hlEq : ch'.lastLSFs = (cfg.L.build (ch'.G cfg.P.d) (ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d)).2 :=
      congrArg Prod.snd hBuilt
    change ∃ a : ℤ, (a : ℝ) / (2 : ℝ) ^ dryLastStretchP J = (ch'.lastLSFs j).wstr e
    rw [hlEq]
    exact hres j (hkEq ▸ hj) e
  · have hi₀' : i₀ ≤ cfg.P.d := hi₀
    have hiEq : i₀ = cfg.P.d := by omega
    subst hiEq
    intro j hj e he
    simpa [Chain.Ordered.algorithm1_shift] using hDy j (by simpa [Chain.Ordered.algorithm1_shift] using hj)
      e (by simpa [Chain.Ordered.algorithm1_shift] using he)

/-! ## 2. Level-`d` fixed-point length fits (`dry_levelD_lenFits_of_shiftLoop`) -/

private theorem two_pow_lt_cap4_half {a L : ℕ} (hlt : a + 1 < 4 * L) :
    (2 : ℝ) ^ a < (Num.capacity 4 L : ℝ) / 2 := by
  have hnat : 2 ^ (a + 1) < Num.capacity 4 L := by
    rw [Num.capacity, Num.base, ← pow_mul]
    exact Nat.pow_lt_pow_right (by decide) hlt
  have hr : (2 : ℝ) ^ (a + 1) < (Num.capacity 4 L : ℝ) := by exact_mod_cast hnat
  rw [pow_succ] at hr
  linarith

private theorem fits4_of_nonneg_lt_half {L : ℕ} {z : ℤ} (hL : 0 < L)
    (h0 : 0 ≤ z) (hlt : (z : ℝ) < (Num.capacity 4 L : ℝ) / 2) :
    Num.Fits 4 L z := by
  have hcapEven : 2 ∣ Num.capacity 4 L := by
    rw [Num.capacity, Num.base, ← pow_mul]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨t, ht⟩ := hcapEven
  have htHalf : (Num.capacity 4 L : ℝ) / 2 = (t : ℝ) := by
    rw [ht]; push_cast; ring
  have hltR : (z : ℝ) < (t : ℝ) := by linarith
  have hltZ : z < (t : ℤ) := by exact_mod_cast hltR
  unfold Num.Fits
  rw [ht]
  push_cast
  omega

private theorem dryLast_sigmaLast_le_aux (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {n : ℕ} (hn : n ≤ 2 * (solverConnectedAugmented J).m + 2) :
    let I := solverConnectedAugmented J
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    cfg.LP.σ_last n ≤ (2 : ℝ) ^ (k + 4 * I.m.size + 18) := by
  intro I k cfg
  have hC_lt : max 1 lastCanonConst < (2 : ℝ) ^ k :=
    (dryWitnessUsed_lastCanonConst_and_levelM_lt J hJn hJm hCap).1
  have hDC_eq : max 1 dryLastConstant = 128 * max 1 lastCanonConst := by
    unfold dryLastConstant
    have : (1 : ℝ) ≤ max 1 lastCanonConst := le_max_left 1 _
    exact max_eq_right (by linarith)
  have hDC_le : max 1 dryLastConstant ≤ (2 : ℝ) ^ (k + 7) := by
    rw [hDC_eq, pow_add]; norm_num; linarith
  have hsz := Nat.lt_size_self I.m
  have h1 : 1 ≤ 2 ^ I.m.size := Nat.one_le_two_pow
  have hn' : n ≤ 2 * I.m + 2 := hn
  have hn_nat : n ≤ 2 ^ (I.m.size + 2) := by
    have hpow : 2 ^ (I.m.size + 2) = 4 * 2 ^ I.m.size := by rw [pow_add]; ring
    omega
  have hn_le : (n : ℝ) ≤ (2 : ℝ) ^ (I.m.size + 2) := by exact_mod_cast hn_nat
  have hn2 : (n : ℝ) + 2 ≤ (2 : ℝ) ^ (I.m.size + 3) := by
    have hnat : n + 2 ≤ 2 ^ (I.m.size + 3) := by
      have hpow : 2 ^ (I.m.size + 3) = 8 * 2 ^ I.m.size := by rw [pow_add]; ring
      omega
    exact_mod_cast hnat
  have hlog : Real.log ((n : ℝ) + 2) ≤ (2 : ℝ) ^ (I.m.size + 3) := by
    have h2 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 2)
    linarith
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have h1le : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 4 * I.m.size + 18) := one_le_pow₀ (by norm_num)
  have hmain : 2 * max 1 dryLastConstant * (n : ℝ) ^ 2 * (Real.log ((n : ℝ) + 2)) ^ 2 ≤
      (2 : ℝ) ^ (k + 4 * I.m.size + 18) := by
    have hnsq : (n : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (I.m.size + 2)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hn_le 2
    have hlsq : (Real.log ((n : ℝ) + 2)) ^ 2 ≤ ((2 : ℝ) ^ (I.m.size + 3)) ^ 2 :=
      pow_le_pow_left₀ hlog0 hlog 2
    calc 2 * max 1 dryLastConstant * (n : ℝ) ^ 2 * (Real.log ((n : ℝ) + 2)) ^ 2
        ≤ 2 * (2 : ℝ) ^ (k + 7) * ((2 : ℝ) ^ (I.m.size + 2)) ^ 2 * ((2 : ℝ) ^ (I.m.size + 3)) ^ 2 := by
          gcongr
      _ = (2 : ℝ) ^ (k + 4 * I.m.size + 18) := by
          rw [← pow_succ', ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
          exact congrArg ((2 : ℝ) ^ ·) (by omega)
  change max 1 (2 * max 1 dryLastConstant * (n : ℝ) ^ 2 * (Real.log ((n : ℝ) + 2)) ^ 2) ≤ _
  exact max_le h1le hmain

/-- Discharges the level-`d` `hLenFits` hypothesis of `shiftTermSelectBody_runs` on `dryWitnessUsed`
at `pLast := dryLastStretchP J` from `ShiftLoopChainInv`, `DryChainLenGridInv`, and
`DryLastWstrDyadic`. -/
theorem dry_levelD_lenFits_of_shiftLoop
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hShift : Chain.Ordered.ShiftLoopChainInv (concreteCirculationCfgWithLast dryWitnessUsed J) ch)
    (hGrid : DryChainLenGridInv J ch)
    (hDy : DryLastWstrDyadic J ch) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let P := ipmQualityPrecision I.m V k
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let pLast := dryLastStretchP J
    ∀ e ∈ (ch.G cfg.P.d).E,
      let prev := ch.toTreeChain.chainLen ch.ℓ cfg.P.d e
      let cur := ch.toTreeChain.chainLen ch.ℓ (cfg.P.d + 1) e
      (∃ qp : ℤ, Num.Fits 4 L (qp * (2 : ℤ) ^ pLast) ∧ (qp : ℝ) / (2 : ℝ) ^ P = prev) ∧
      (∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ (P + pLast) = cur) := by
  intro I V k P L cfg pLast e he
  let E := ipmQualityRangeExponent I.m V k
  have hIm1 : 1 ≤ I.m :=
    Nat.lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap).1
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hTH := hShift.1.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk
  have hpLast40 : pLast ≤ 40 * E := by
    have h1 : (1024 * ⌈max 1 lastCanonConst⌉₊).size +
        3 * (max I.m (levelM cfg.TP cfg.P cfg.P.d) + 1).size ≤ 40 * E :=
      dryLastStretchP_le_forty_rangeExponent J hJn hJm hCap
    have h2 : (I.m + 1).size ≤ (max I.m (levelM cfg.TP cfg.P cfg.P.d) + 1).size :=
      Nat.size_le_size (by omega)
    change (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (I.m + 1).size ≤ 40 * E
    omega
  have hExp : cfg.P.d * (3 * I.m.size + 12) ≤ E :=
    chainLen_exponent_le_rangeExponent I.m V (concreteQualityBudgetWithLast dryWitnessUsed)
      hIm1 cfg.P.hM₀
  have hkE : k ≤ E := by
    have hk1 := qualityExponent_le_qualitySlackExponent I.m V k
    dsimp only [E, ipmQualityRangeExponent]; omega
  have h4L : P + 92 * E + 12 * I.m.size + 1480 ≤ 4 * L := by
    change ipmQualityPrecision I.m V k + 92 * ipmQualityRangeExponent I.m V k +
      12 * I.m.size + 1480 ≤ 4 * ipmQualityLimbs I.m V k
    unfold ipmQualityLimbs ipmQualityPrecision ipmQualityErrorBits
    omega
  have hLPos : 0 < L := by omega
  obtain ⟨_, hG0n, hLvls, _, _⟩ := hGrid
  obtain ⟨hPrevLo, hPrevHi⟩ := (hLvls cfg.P.d le_rfl).1 e he
  obtain ⟨qp, hqpEq⟩ := (hLvls cfg.P.d le_rfl).2 e he
  have hPrevPos : 0 < ch.toTreeChain.chainLen ch.ℓ cfg.P.d e :=
    lt_of_lt_of_le (by positivity) hPrevLo
  have hPrevNN : 0 ≤ ch.toTreeChain.chainLen ch.ℓ cfg.P.d e := hPrevPos.le
  have hPrevLe2E : ch.toTreeChain.chainLen ch.ℓ cfg.P.d e ≤ (2 : ℝ) ^ (2 * E) :=
    hPrevHi.trans (pow_le_pow_right₀ (by norm_num) (by linarith only [hExp]))
  have hqpNN : (0 : ℤ) ≤ qp := by
    have h1 : (0 : ℝ) ≤ (qp : ℝ) / (2 : ℝ) ^ P := hqpEq.symm ▸ hPrevNN
    have h2 : (0 : ℝ) ≤ (qp : ℝ) := (div_nonneg_iff.mp h1).elim And.left fun h => by
      exfalso; linarith [pow_pos (by norm_num : (0 : ℝ) < 2) P]
    exact_mod_cast h2
  have hqpShiftLt : ((qp * (2 : ℤ) ^ pLast : ℤ) : ℝ) < (Num.capacity 4 L : ℝ) / 2 := by
    have heq : ((qp * (2 : ℤ) ^ pLast : ℤ) : ℝ) =
        ch.toTreeChain.chainLen ch.ℓ cfg.P.d e * (2 : ℝ) ^ (P + pLast) := by
      have hqpEq' : (qp : ℝ) / (2 : ℝ) ^ P = ch.toTreeChain.chainLen ch.ℓ cfg.P.d e := hqpEq
      rw [← hqpEq', pow_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
      field_simp [pow_ne_zero P (by norm_num : (2 : ℝ) ≠ 0)]
    rw [heq]
    calc ch.toTreeChain.chainLen ch.ℓ cfg.P.d e * (2 : ℝ) ^ (P + pLast)
        ≤ (2 : ℝ) ^ (2 * E) * (2 : ℝ) ^ (P + pLast) :=
          mul_le_mul_of_nonneg_right hPrevLe2E (by positivity)
      _ = (2 : ℝ) ^ (2 * E + P + pLast) := by
          rw [← pow_add]; exact congrArg ((2 : ℝ) ^ ·) (by omega)
      _ < (Num.capacity 4 L : ℝ) / 2 := two_pow_lt_cap4_half (by linarith only [h4L, hpLast40])
  have hqpFit : Num.Fits 4 L (qp * (2 : ℤ) ^ pLast) :=
    fits4_of_nonneg_lt_half hLPos (mul_nonneg hqpNN (by positivity)) hqpShiftLt
  refine ⟨⟨qp, hqpFit, hqpEq⟩, ?_⟩
  obtain ⟨a, haEq⟩ := hDy ch.lastBran hShift.1.hLastBran e he
  have hLastH := hShift.1.hLastHolds ch.lastBran hShift.1.hLastBran
  have hwstrBounds := hLastH.2.2.2 e he
  have hwstrNN : 0 ≤ (ch.lastLSFs ch.lastBran).wstr e := by
    refine le_trans ?_ hwstrBounds.1
    have hwlNN : ∀ W : List (ℕ × Bool), (∀ x ∈ W, x.1 ∈ (ch.G cfg.P.d).E) →
        0 ≤ walkLength (ch.toTreeChain.chainLen ch.ℓ cfg.P.d) W := by
      intro W hW
      unfold walkLength
      refine Finset.sum_nonneg fun f _ => ?_
      by_cases hf : f ∈ (ch.G cfg.P.d).E
      · exact mul_nonneg (le_trans (by positivity) ((hLvls cfg.P.d le_rfl).1 f hf).1) (abs_nonneg _)
      · have hwf0 : walkFlow W f = 0 := by
          unfold walkFlow
          have hnil : ∀ x ∈ W, (if x.1 = f then (if x.2 then (1 : ℝ) else -1) else 0) = 0 :=
            fun x hx => by
              have hne : x.1 ≠ f := fun heq => hf (heq ▸ hW x hx)
              simp [hne]
          rw [List.sum_eq_zero]
          intro y hy
          rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
          exact hnil x hx
        rw [hwf0, abs_zero, mul_zero]
    have hSubD : (ch.lastLSFs ch.lastBran).F.F.E ⊆ (ch.G cfg.P.d).E := by
      have h := (ch.toTreeChain.forestsAreSubgraphs_of_holds hTH.1 cfg.P.d le_rfl).2.1
      simpa [TreeChain.activeLSF, ChainState.toTreeChain, cfg] using h
    have hFPSub : ∀ a b : ℕ, ∀ x ∈ (ch.lastLSFs ch.lastBran).F.F.forestPath a b,
        x.1 ∈ (ch.G cfg.P.d).E := by
      intro a b x hx
      simp only [MGraph.forestPath] at hx
      split_ifs at hx with h
      · exact hSubD (MGraph.isWalk_edges_mem (Classical.choose_spec h).1 x hx)
      · exact False.elim (List.not_mem_nil hx)
    unfold RootedForest.stretch
    dsimp only
    split_ifs
    · have h0 := hwlNN _ (hFPSub ((ch.G cfg.P.d).tail e) ((ch.G cfg.P.d).head e))
      have hdiv : 0 ≤ walkLength (ch.toTreeChain.chainLen ch.ℓ cfg.P.d)
          ((ch.lastLSFs ch.lastBran).F.F.forestPath ((ch.G cfg.P.d).tail e) ((ch.G cfg.P.d).head e)) /
          ch.toTreeChain.chainLen ch.ℓ cfg.P.d e := div_nonneg h0 hPrevNN
      linarith
    · have h1 := hwlNN _ (hFPSub ((ch.G cfg.P.d).tail e)
        ((ch.lastLSFs ch.lastBran).F.root ((ch.G cfg.P.d).tail e)))
      have h2 := hwlNN _ (hFPSub ((ch.G cfg.P.d).head e)
        ((ch.lastLSFs ch.lastBran).F.root ((ch.G cfg.P.d).head e)))
      have hdiv : 0 ≤ (walkLength (ch.toTreeChain.chainLen ch.ℓ cfg.P.d)
            ((ch.lastLSFs ch.lastBran).F.F.forestPath ((ch.G cfg.P.d).tail e)
              ((ch.lastLSFs ch.lastBran).F.root ((ch.G cfg.P.d).tail e))) +
          walkLength (ch.toTreeChain.chainLen ch.ℓ cfg.P.d)
            ((ch.lastLSFs ch.lastBran).F.F.forestPath ((ch.G cfg.P.d).head e)
              ((ch.lastLSFs ch.lastBran).F.root ((ch.G cfg.P.d).head e)))) /
          ch.toTreeChain.chainLen ch.ℓ cfg.P.d e := div_nonneg (add_nonneg h1 h2) hPrevNN
      linarith
  have hGdN : (ch.G cfg.P.d).n ≤ 2 * I.m + 2 :=
    (Finset.card_le_card (ch.toTreeChain.G_V_subset_of_le hTH.1 (Nat.zero_le _) le_rfl)).trans hG0n
  have hsig : cfg.LP.σ_last (ch.G cfg.P.d).n ≤ (2 : ℝ) ^ (k + 4 * I.m.size + 18) :=
    dryLast_sigmaLast_le_aux J hJn hJm hCap hGdN
  have hcurEq : ch.toTreeChain.chainLen ch.ℓ (cfg.P.d + 1) e =
      (ch.lastLSFs ch.lastBran).wstr e * ch.toTreeChain.chainLen ch.ℓ cfg.P.d e := by
    have hact : ch.toTreeChain.activeLSF cfg.P.d = ch.lastLSFs ch.lastBran := by
      unfold TreeChain.activeLSF; simp [ChainState.toTreeChain, cfg]
    change (ch.toTreeChain.activeLSF cfg.P.d).wstr e * ch.toTreeChain.chainLen ch.ℓ cfg.P.d e = _
    rw [hact]
  have hqVal : ((a * qp : ℤ) : ℝ) / (2 : ℝ) ^ (P + pLast) =
      ch.toTreeChain.chainLen ch.ℓ (cfg.P.d + 1) e := by
    have hqpEq' : (qp : ℝ) / (2 : ℝ) ^ P = ch.toTreeChain.chainLen ch.ℓ cfg.P.d e := hqpEq
    have haEq' : (a : ℝ) / (2 : ℝ) ^ pLast = (ch.lastLSFs ch.lastBran).wstr e := haEq
    rw [hcurEq, ← haEq', ← hqpEq', pow_add, Int.cast_mul]
    field_simp [pow_ne_zero P (by norm_num : (2 : ℝ) ≠ 0),
      pow_ne_zero pLast (by norm_num : (2 : ℝ) ≠ 0)]
  have hcurNN : 0 ≤ ch.toTreeChain.chainLen ch.ℓ (cfg.P.d + 1) e := by
    rw [hcurEq]; exact mul_nonneg hwstrNN hPrevNN
  have hqNN : (0 : ℤ) ≤ a * qp := by
    have h1 : (0 : ℝ) ≤ ((a * qp : ℤ) : ℝ) / (2 : ℝ) ^ (P + pLast) := hqVal.symm ▸ hcurNN
    have h2 : (0 : ℝ) ≤ ((a * qp : ℤ) : ℝ) := (div_nonneg_iff.mp h1).elim And.left fun h => by
      exfalso; linarith [pow_pos (by norm_num : (0 : ℝ) < 2) (P + pLast)]
    exact_mod_cast h2
  have hqLt : ((a * qp : ℤ) : ℝ) < (Num.capacity 4 L : ℝ) / 2 := by
    have heq : ((a * qp : ℤ) : ℝ) =
        ch.toTreeChain.chainLen ch.ℓ (cfg.P.d + 1) e * (2 : ℝ) ^ (P + pLast) := by
      rw [← hqVal, div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num))]
    rw [heq, hcurEq]
    calc (ch.lastLSFs ch.lastBran).wstr e * ch.toTreeChain.chainLen ch.ℓ cfg.P.d e *
            (2 : ℝ) ^ (P + pLast)
        ≤ (2 : ℝ) ^ (k + 4 * I.m.size + 18) * (2 : ℝ) ^ (2 * E) * (2 : ℝ) ^ (P + pLast) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (hwstrBounds.2.trans hsig) hPrevLe2E hPrevNN (by positivity))
            (by positivity)
      _ = (2 : ℝ) ^ (P + pLast + 2 * E + k + 4 * I.m.size + 18) := by
          rw [← pow_add, ← pow_add]; exact congrArg ((2 : ℝ) ^ ·) (by omega)
      _ < (Num.capacity 4 L : ℝ) / 2 :=
          two_pow_lt_cap4_half (by linarith only [h4L, hpLast40, hkE])
  exact ⟨a * qp, fits4_of_nonneg_lt_half hLPos hqNN hqLt, hqVal⟩

/-! ## 3. Select-heap size bound and `SelectPhiBoundedAt` preservation on terminal shift -/

/-- Under `SelectHeapMatchesChain`, the heap size is at most `(C.G 0).m`. -/
theorem selectHeap_size_le_G0_m {mem : ℕ → ℕ} {loc : SelectHeapLoc} {h P size : ℕ}
    {C : TreeChain} {g ℓ : ℕ → ℝ}
    (hm : SelectHeapMatchesChain mem loc h P C g ℓ size) :
    size ≤ (C.G 0).m := by
  obtain ⟨⟨_, ⟨_, hArrCap, hPosBij, _⟩, _, _, _⟩, _, hmem, _⟩ := hm
  have hInj : ∀ i ∈ Finset.range size, ∀ j ∈ Finset.range size,
      mem (loc.arrPtr + i) = mem (loc.arrPtr + j) → i = j := by
    intro i hi j hj heq
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have h1 := hPosBij i hi'
    have h2 := hPosBij j hj'
    rw [heq] at h1
    omega
  have hMapSub : (Finset.range size).image (fun i => mem (loc.arrPtr + i)) ⊆ (C.G 0).E := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    have hi' := Finset.mem_range.mp hi
    have hpos : mem (loc.posPtr + mem (loc.arrPtr + i)) ≠ 0 := by
      have := hPosBij i hi'; omega
    have hmemE := (hmem _).mp ⟨hArrCap i hi', hpos⟩
    exact (Finset.mem_sdiff.mp hmemE).1
  have hCardEq : ((Finset.range size).image (fun i => mem (loc.arrPtr + i))).card = size := by
    rw [Finset.card_image_of_injOn hInj, Finset.card_range]
  exact hCardEq ▸ Finset.card_le_card hMapSub

/-- Preserves `SelectPhiBoundedAt` at all levels `k ≤ cfg.P.d` across a terminal shift
(`alg2LoopShiftStep cfg model (Fin.last cfg.P.d)`) from the `hPhiLt` and `hPhiD` postconditions
of `shiftTermSelectBody_runs`. -/
theorem dry_selectPhiBoundedAt_of_termShift
    {cfg : Alg2Config} {model : Alg2State cfg} {G₀' : MGraph}
    {σ' σ'_mwu γ'_ℓ γ'_c M_g : ℝ} {φ φ' : ℕ → ℕ → ℝ} {N : ℕ}
    (hM : 0 ≤ M_g)
    (hH' : (alg2LoopShiftStep cfg model (Fin.last cfg.P.d)).chain.toTreeChain.Holds
      G₀' model.chain.ℓ σ' σ'_mwu γ'_ℓ γ'_c)
    (hN : (model.chain.G 0).n ≤ N)
    (hg : ∀ f ∈ (model.chain.G 0).E, |model.chain.g f| ≤ M_g)
    (hPot' : SelectPotInv (alg2LoopShiftStep cfg model (Fin.last cfg.P.d)).chain.toTreeChain
      model.chain.g φ')
    (hBd : ∀ k < cfg.P.d, SelectPhiBoundedAt model.chain.toTreeChain φ N M_g k)
    (hPhiLt : ∀ k < cfg.P.d, φ' k = φ k)
    (hPhiD :
      let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
      let F' := (model'.chain.lastLSFs model'.chain.lastBran).F.F
      ∀ v ∈ F'.V, ∃ r ∈ F'.V, F'.Connected v r ∧
        φ' cfg.P.d v = walkInner (potGrad model'.chain.toTreeChain model'.chain.g φ cfg.P.d)
          (F'.forestPath v r)) :
    let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
    ∀ k ≤ cfg.P.d, SelectPhiBoundedAt model'.chain.toTreeChain φ' N M_g k := by
  intro model' k hk
  have hGeq : ∀ j, model'.chain.G j = model.chain.G j := fun j => by
    simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift]
  have hgeq : model'.chain.g = model.chain.g := by
    simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift]
  by_cases hlt : k < cfg.P.d
  · intro v hv
    rw [hPhiLt k hlt]
    exact hBd k hlt v (by simpa [ChainState.toTreeChain, hGeq k] using hv)
  · have hkEq : k = cfg.P.d := by omega
    subst hkEq
    have hBdPre : ∀ r < cfg.P.d, SelectPhiBoundedAt model'.chain.toTreeChain φ N M_g r := by
      intro r hr v hv
      exact hBd r hr v (by simpa [ChainState.toTreeChain, hGeq r] using hv)
    have hPotPre : ∀ r < cfg.P.d, SelectPotInvAt model'.chain.toTreeChain model'.chain.g φ r := by
      intro r hr
      have hp := hPot' r (by change r ≤ cfg.P.d; omega)
      have hpg : potGrad model'.chain.toTreeChain model.chain.g φ' r =
          potGrad model'.chain.toTreeChain model.chain.g φ r := by
        funext e; rw [potGrad_eq_sum, potGrad_eq_sum]
        congr 1; refine Finset.sum_congr rfl fun t ht => ?_
        have htd : t < cfg.P.d := lt_trans (Finset.mem_range.mp ht) hr
        rw [hPhiLt t htd]
      rw [hgeq]
      intro a b hab
      have h1 := hp a b hab
      rw [hpg, hPhiLt r hr] at h1
      exact h1
    have hActD : model'.chain.toTreeChain.activeLSF cfg.P.d =
        model'.chain.lastLSFs model'.chain.lastBran := by
      unfold TreeChain.activeLSF; simp [ChainState.toTreeChain]
    have hStep := selectPhiBoundedAt_of_phiFill (C := model'.chain.toTreeChain)
      (G := G₀') (ℓ := model.chain.ℓ) (g := model'.chain.g)
      (φ := φ) (φj := φ' cfg.P.d) (N := N) (j := cfg.P.d)
      hM hH' le_rfl (by simpa [ChainState.toTreeChain, hGeq 0] using hN)
      (by simpa [ChainState.toTreeChain, hGeq 0, hgeq] using hg)
      hPotPre hBdPre (by simpa [hActD] using hPhiD)
    intro v hv
    simpa [Function.update_self] using hStep v hv

end MinCostFlow.Final.DryRun

end
