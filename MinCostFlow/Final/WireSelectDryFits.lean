module

public import MinCostFlow.Final.WireSelectEmbLen
public import MinCostFlow.MinRatio.SelectPhiBounded
public import MinCostFlow.MinRatio.WireSelectEvalKeyProofs

import Mathlib.Tactic

/-!
# Dry-run fixed-point fit bounds for select-heap keys and forest potentials (`WireSelectDryFits`)

Proves the fixed-point no-overflow fit bounds for the concrete dry-run witness
`dryWitnessUsed` (`Final/AssemblyDryRun.lean`):

1. **`CandidateKeysFit`** (`dry_candidateKeysFit_of_chainInv`, `dry_candidateKeysFit_of_shiftLoop`,
   `dry_candidateKeysFit_of_reachedInv`):
   on `dryWitnessUsed` with `ChainInv` / `ShiftLoopChainInv` / `OrdSolverReachedInv`,
   `DryChainLenGridInv`, and `∀ e ∈ (ch.G 0).E, |ch.g e| ≤ M_g` for any `0 ≤ M_g ≤ 2 ^ (80 * E)`
   (including the IPM stored gradient bound `M_g = 2 ^ E`), every candidate cycle at every level
   `lvl ≤ cfg.P.d` has both its scaled numerator and scaled denominator strictly below
   `Num.capacity 4 L / 2`.
2. **`PotGradEvalFits` and `ForestWalkFits`** (`dry_phiFillFits_of_chainInv`,
   `dry_phiFillFits_of_shiftLoop`, `dry_phiFillFits_of_reachedInv`):
   on `dryWitnessUsed` at every level `j ≤ cfg.P.d`, given `SelectPhiBoundedAt` on earlier levels
   `k < j` (preserved across valid batches by `splitPot_abs_le_of_batchIsValid` and across fills
   by `selectPhiBoundedAt_of_phiFill`), both `PotGradEvalFits` on every active forest edge
   `f ∈ (C.activeLSF j).F.F.E` and `ForestWalkFits` on `(C.activeLSF j).F.F` for
   `potGrad C ch.g φ j` hold.
-/

@[expose] public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Scaling.Machine
  MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Concrete format and last-level stretch helpers -/

private theorem ipmQuality_four_limbs_margin (m V k : ℕ) :
    let E := ipmQualityRangeExponent m V k
    let P := ipmQualityPrecision m V k
    let L := ipmQualityLimbs m V k
    P + 92 * E + 12 * m.size + 1480 ≤ 4 * L := by
  intro E P L
  dsimp only [L, P, ipmQualityLimbs, ipmQualityPrecision, ipmQualityErrorBits]
  omega

private theorem two_pow_lt_capacity4 {a L : ℕ} (hlt : a < 4 * L) :
    (2 : ℝ) ^ a < (Num.capacity 4 L : ℝ) := by
  have hnat : 2 ^ a < Num.capacity 4 L := by
    rw [Num.capacity, Num.base, ← pow_mul]
    exact Nat.pow_lt_pow_right (by decide) hlt
  exact_mod_cast hnat

private theorem two_mul_pow_add_one (a : ℕ) :
    (2 : ℝ) * (2 : ℝ) ^ a = (2 : ℝ) ^ (a + 1) := by
  rw [pow_succ, mul_comm]

/-- Concrete upper bound on `cfg.LP.σ_last n` for `dryWitnessUsed` when `n ≤ 2 * I.m + 2`:
bounded by `(2 : ℝ) ^ (k + 4 * I.m.size + 18)`. -/
private theorem dryLast_sigmaLast_le (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {n : ℕ} (hn : n ≤ 2 * (solverConnectedAugmented J).m + 2) :
    let I := solverConnectedAugmented J
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    (concreteCirculationCfgWithLast dryWitnessUsed J).LP.σ_last n ≤
      (2 : ℝ) ^ (k + 4 * I.m.size + 18) := by
  intro I k
  have hC_lt : max 1 lastCanonConst < (2 : ℝ) ^ k :=
    (dryWitnessUsed_lastCanonConst_and_levelM_lt J hJn hJm hCap).1
  have h1le : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 4 * I.m.size + 18) := one_le_pow₀ (by norm_num)
  have hDC_eq : max 1 dryLastConstant = 128 * max 1 lastCanonConst := by
    unfold dryLastConstant
    have : (1 : ℝ) ≤ max 1 lastCanonConst := le_max_left 1 _
    exact max_eq_right (by linarith)
  have hDC_le : max 1 dryLastConstant ≤ (2 : ℝ) ^ (k + 7) := by
    rw [hDC_eq, pow_add]; norm_num; linarith
  have hsz := Nat.lt_size_self I.m
  have h2pos : 1 ≤ 2 ^ I.m.size := Nat.one_le_two_pow
  have hn' : n ≤ 2 * I.m + 2 := hn
  have hn_nat : n ≤ 2 ^ (I.m.size + 2) := by
    have hpow : 2 ^ (I.m.size + 2) = 4 * 2 ^ I.m.size := by rw [pow_add]; ring
    omega
  have hn_le : (n : ℝ) ≤ (2 : ℝ) ^ (I.m.size + 2) := by exact_mod_cast hn_nat
  have hn2_nat : n + 2 ≤ 2 ^ (I.m.size + 3) := by
    have hpow : 2 ^ (I.m.size + 3) = 8 * 2 ^ I.m.size := by rw [pow_add]; ring
    omega
  have hlog_le : Real.log ((n : ℝ) + 2) ≤ (2 : ℝ) ^ (I.m.size + 3) := by
    have h2 : (n : ℝ) + 2 ≤ (2 : ℝ) ^ (I.m.size + 3) := by exact_mod_cast hn2_nat
    exact (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hlog_nn : 0 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hmain : 2 * max 1 dryLastConstant * (n : ℝ) ^ 2 * (Real.log ((n : ℝ) + 2)) ^ 2 ≤
      (2 : ℝ) ^ (k + 4 * I.m.size + 18) := by
    have hnsq : (n : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (I.m.size + 2)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hn_le 2
    have hlsq : (Real.log ((n : ℝ) + 2)) ^ 2 ≤ ((2 : ℝ) ^ (I.m.size + 3)) ^ 2 :=
      pow_le_pow_left₀ hlog_nn hlog_le 2
    calc 2 * max 1 dryLastConstant * (n : ℝ) ^ 2 * (Real.log ((n : ℝ) + 2)) ^ 2
        ≤ 2 * (2 : ℝ) ^ (k + 7) * ((2 : ℝ) ^ (I.m.size + 2)) ^ 2 *
            ((2 : ℝ) ^ (I.m.size + 3)) ^ 2 := by
          gcongr
      _ = (2 : ℝ) ^ (k + 4 * I.m.size + 18) := by
          rw [← pow_mul, ← pow_mul, two_mul_pow_add_one, ← pow_add, ← pow_add]
          exact congrArg ((2 : ℝ) ^ ·) (by omega)
  change max 1 (2 * max 1 dryLastConstant * (n : ℝ) ^ 2 * (Real.log ((n : ℝ) + 2)) ^ 2) ≤ _
  exact max_le h1le hmain

/-! ## 2. Concrete dry-run `CandidateKeysFit` -/

/-- The dry-run last-level stretch precision `(1024 * ⌈max 1 lastCanonConst⌉₊).size +
3 * (max I.m (levelM cfg.TP cfg.P cfg.P.d) + 1).size` is at most `40 * E`. -/
theorem dryLastStretchP_le_forty_rangeExponent
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
    let A := concreteQualityBudgetWithLast dryWitnessUsed
    let k := cappedQualityExponent threshold A I.m
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let E := ipmQualityRangeExponent I.m V k
    (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (max I.m (levelM cfg.TP cfg.P cfg.P.d) + 1).size ≤
      40 * E := by
  intro I V threshold A k cfg E
  obtain ⟨hC_lt, hM_lt⟩ := dryWitnessUsed_lastCanonConst_and_levelM_lt J hJn hJm hCap
  have hceil_le : ⌈max 1 lastCanonConst⌉₊ ≤ 2 ^ k :=
    Nat.ceil_le.mpr (by exact_mod_cast hC_lt.le)
  have h1024_lt : 1024 * ⌈max 1 lastCanonConst⌉₊ < 2 ^ (k + 11) := by
    calc 1024 * ⌈max 1 lastCanonConst⌉₊
        ≤ 1024 * 2 ^ k := Nat.mul_le_mul_left 1024 hceil_le
      _ = 2 ^ (k + 10) := by rw [pow_add, mul_comm]; norm_num
      _ < 2 ^ (k + 11) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hsz1 : (1024 * ⌈max 1 lastCanonConst⌉₊).size ≤ k + 11 := Nat.size_le.mpr h1024_lt
  have hszM : (levelM cfg.TP cfg.P cfg.P.d + 1).size ≤ k := Nat.size_le.mpr hM_lt
  have hszI : (I.m + 1).size ≤ I.m.size + 1 := by
    rw [Nat.size_le, pow_succ]
    have h1 := Nat.lt_size_self I.m
    have h2 : 1 ≤ 2 ^ I.m.size := Nat.one_le_two_pow
    omega
  have hszMax : (max I.m (levelM cfg.TP cfg.P cfg.P.d) + 1).size ≤ max (I.m.size + 1) k := by
    rcases le_total I.m (levelM cfg.TP cfg.P cfg.P.d) with h | h
    · rw [max_eq_right h]; exact hszM.trans (le_max_right _ _)
    · rw [max_eq_left h]; exact hszI.trans (le_max_left _ _)
  have hkE : k ≤ E := by
    have hk1 := qualityExponent_le_qualitySlackExponent I.m V k
    dsimp only [E, ipmQualityRangeExponent]; omega
  have hImE : I.m.size ≤ E := by
    have h1 : I.m.size ≤ (I.m.size + V.size) ^ 2 :=
      le_trans (Nat.le_add_right _ _) (Nat.le_self_pow (by decide : 2 ≠ 0) _)
    have h2 := slackRangeExponent_le_qualitySlackExponent I.m V k
    dsimp only [E, ipmQualityRangeExponent]
    unfold slackRangeExponent at h2
    omega
  have hE100 : 100 ≤ E := by dsimp only [E, ipmQualityRangeExponent]; omega
  omega

/-- Core `CandidateKeysFit` theorem on `ChainInv` + `DryChainLenGridInv` for `dryWitnessUsed`,
at any last-level stretch precision `pLast ≤ 40 * E` (including `dryLastStretchP`) and gradient
magnitude bound `M_g ≤ 2 ^ (40 * E)` (including the IPM stored bound `2 ^ E`). -/
theorem dry_candidateKeysFit_of_chainInv
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hInv : Ordered.ChainInv (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).L
      (concreteCirculationCfgWithLast dryWitnessUsed J).TP
      (concreteCirculationCfgWithLast dryWitnessUsed J).LP
      (concreteCirculationCfgWithLast dryWitnessUsed J).P
      (concreteCirculationCfgWithLast dryWitnessUsed J).N₀ ch)
    (hGridInv : DryChainLenGridInv J ch)
    {pLast : ℕ}
    (hpLast :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      pLast ≤ 40 * ipmQualityRangeExponent I.m V k)
    {M_g : ℝ} (hM0 : 0 ≤ M_g)
    (hMle :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      M_g ≤ (2 : ℝ) ^ (40 * ipmQualityRangeExponent I.m V k))
    (hg : ∀ e ∈ (ch.G 0).E, |ch.g e| ≤ M_g) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    CandidateKeysFit 4 (ipmQualityPrecision I.m V k) pLast (ipmQualityLimbs I.m V k)
      ch.toTreeChain ch.g ch.ℓ := by
  intro I V k
  let E := ipmQualityRangeExponent I.m V k
  let P := ipmQualityPrecision I.m V k
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hpLast' : pLast ≤ 40 * E := hpLast
  have hMle' : M_g ≤ (2 : ℝ) ^ (40 * E) := hMle
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hIm1 : 1 ≤ I.m :=
    Nat.lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap).1
  have hTH := hInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk
  have hH := hTH.1
  have hSpan := hTH.2.1
  have hγ := dryWitnessUsed_gammaEll_le_dryMaxEmbLen J hJn hJm hCap
  have hEmbBd := embLen_le_of_holds hH hγ
  have hExp : cfg.P.d * (3 * I.m.size + 12) ≤ E :=
    chainLen_exponent_le_rangeExponent I.m V (concreteQualityBudgetWithLast dryWitnessUsed)
      hIm1 cfg.P.hM₀
  have hkE : k ≤ E := by
    have hk1 := qualityExponent_le_qualitySlackExponent I.m V k
    dsimp only [E, ipmQualityRangeExponent]; omega
  have h4L : P + 92 * E + 12 * I.m.size + 1480 ≤ 4 * L := ipmQuality_four_limbs_margin I.m V k
  obtain ⟨hG0m, hG0n, hLvls, hBran, _⟩ := hGridInv
  intro lvl hlvl e he
  have hlvl' : lvl ≤ cfg.P.d := hlvl
  have heCore : e ∈ (ch.toTreeChain.activeCore lvl).E := (Finset.mem_sdiff.mp he).1
  have heGlvl : e ∈ (ch.G lvl).E := (Finset.mem_sdiff.mp heCore).1
  have hCycLen : (ch.toTreeChain.sparsifierCycle lvl e).length ≤ 2 ^ (k + 1) := by
    unfold TreeChain.sparsifierCycle
    rw [List.length_cons, walkRev_length]
    by_cases hlt : lvl < ch.toTreeChain.d
    · have h1 : (ch.toTreeChain.activeEmb lvl e).length ≤ dryMaxEmbLen I.m := hEmbBd lvl hlt e heCore
      have h2k1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have hdm : dryMaxEmbLen I.m = 2 ^ k := rfl
      rw [pow_succ]; omega
    · have hnil : ch.toTreeChain.activeEmb lvl e = [] := by
        unfold TreeChain.activeEmb; simp [hlt]
      rw [hnil, List.length_nil]
      exact Nat.one_le_two_pow
  have hQle : coreLenPrec ch.toTreeChain.d P pLast lvl ≤ P + pLast := by
    unfold coreLenPrec; split_ifs <;> omega
  have h2Q_le : (2 : ℝ) ^ coreLenPrec ch.toTreeChain.d P pLast lvl ≤ (2 : ℝ) ^ (P + pLast) :=
    pow_le_pow_right₀ (by norm_num) hQle
  constructor
  · -- Numerator bound
    have hNum := abs_walkInner_sparsifierCycle_le hM0 hH hSpan hg hlvl he
    have hn1_nat : (ch.G 0).n + 1 ≤ 2 ^ (I.m.size + 2) := by
      have hsz := Nat.lt_size_self I.m
      have h2pos : 1 ≤ 2 ^ I.m.size := Nat.one_le_two_pow
      have hG0n' : (ch.G 0).n ≤ 2 * I.m + 2 := hG0n
      have hpow : 2 ^ (I.m.size + 2) = 4 * 2 ^ I.m.size := by rw [pow_add]; ring
      omega
    have hn1 : ((ch.G 0).n : ℝ) + 1 ≤ (2 : ℝ) ^ (I.m.size + 2) := by exact_mod_cast hn1_nat
    have hclR : ((ch.toTreeChain.sparsifierCycle lvl e).length : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      exact_mod_cast hCycLen
    have hNumProd : ((ch.toTreeChain.sparsifierCycle lvl e).length : ℝ) *
        (((ch.G 0).n : ℝ) + 1) * M_g ≤
        (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (I.m.size + 2) * (2 : ℝ) ^ (40 * E) := by
      have h1 : ((ch.toTreeChain.sparsifierCycle lvl e).length : ℝ) * (((ch.G 0).n : ℝ) + 1) ≤
          (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (I.m.size + 2) :=
        mul_le_mul hclR hn1 (by positivity) (by positivity)
      exact mul_le_mul h1 hMle' hM0 (by positivity)
    have hNumLe : |walkInner (ch.toTreeChain.chainGrad ch.g (lvl + 1))
          (ch.toTreeChain.sparsifierCycle lvl e)| *
          (2 : ℝ) ^ coreLenPrec ch.toTreeChain.d P pLast lvl ≤
        (2 : ℝ) ^ (P + pLast + 40 * E + k + I.m.size + 3) := by
      calc |walkInner (ch.toTreeChain.chainGrad ch.g (lvl + 1))
              (ch.toTreeChain.sparsifierCycle lvl e)| *
              (2 : ℝ) ^ coreLenPrec ch.toTreeChain.d P pLast lvl
          ≤ (((ch.toTreeChain.sparsifierCycle lvl e).length : ℝ) * (((ch.G 0).n : ℝ) + 1) * M_g) *
              (2 : ℝ) ^ (P + pLast) :=
            mul_le_mul hNum h2Q_le (by positivity) (by positivity)
        _ ≤ ((2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (I.m.size + 2) * (2 : ℝ) ^ (40 * E)) *
              (2 : ℝ) ^ (P + pLast) :=
            mul_le_mul_of_nonneg_right hNumProd (by positivity)
        _ = (2 : ℝ) ^ (P + pLast + 40 * E + k + I.m.size + 3) := by
            rw [← pow_add, ← pow_add, ← pow_add]
            exact congrArg ((2 : ℝ) ^ ·) (by omega)
    have hPowLt : (2 : ℝ) ^ (P + pLast + 40 * E + k + I.m.size + 4) < (Num.capacity 4 L : ℝ) :=
      two_pow_lt_capacity4 (by omega)
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hmul2 : (2 : ℝ) ^ (P + pLast + 40 * E + k + I.m.size + 3) * 2 =
        (2 : ℝ) ^ (P + pLast + 40 * E + k + I.m.size + 4) := (pow_succ 2 _).symm
    linarith
  · -- Denominator bound
    have hWlenLe : ch.toTreeChain.wlenAt ch.ℓ lvl e ≤ (2 : ℝ) ^ (2 * E + k + 4 * I.m.size + 18) := by
      by_cases hlt : lvl < cfg.P.d
      · have hClosed := ch.toTreeChain.sparsifierCycle_isClosedWalk hH hSpan hlvl he
        have hstepB : ∀ x ∈ ch.toTreeChain.sparsifierCycle lvl e,
            0 ≤ ch.toTreeChain.chainLen ch.ℓ (lvl + 1) x.1 ∧
            ch.toTreeChain.chainLen ch.ℓ (lvl + 1) x.1 ≤ (2 : ℝ) ^ (2 * E) := by
          intro x hx
          have hxCore : x.1 ∈ (ch.toTreeChain.activeCore lvl).E := MGraph.isWalk_edges_mem hClosed x hx
          have hxGlvl : x.1 ∈ (ch.G lvl).E := (Finset.mem_sdiff.mp hxCore).1
          have hblt : ch.bran lvl < cfg.P.k := hInv.hBran lvl hlt
          have hB := hBran lvl hlt (ch.bran lvl) hblt x.1 hxGlvl
          have hL0 := (hLvls lvl hlvl').1 x.1 hxGlvl
          have hCL_eq : ch.toTreeChain.chainLen ch.ℓ (lvl + 1) x.1 =
              (cfg.T.lsfs (ch.scState lvl) (ch.bran lvl)).wstr x.1 *
                ch.toTreeChain.chainLen ch.ℓ lvl x.1 := by
            have hact : ch.toTreeChain.activeLSF lvl = cfg.T.lsfs (ch.scState lvl) (ch.bran lvl) := by
              unfold TreeChain.activeLSF
              exact ite_eq_left hlt
            change (ch.toTreeChain.activeLSF lvl).wstr x.1 * ch.toTreeChain.chainLen ch.ℓ lvl x.1 = _
            rw [hact]
          rw [hCL_eq]
          have hnn : 0 ≤ ch.toTreeChain.chainLen ch.ℓ lvl x.1 := le_trans (by positivity) hL0.1
          refine ⟨mul_nonneg (le_trans zero_le_one hB.1) hnn, ?_⟩
          have hexpLe : E + (lvl + 1) * (3 * I.m.size + 12) ≤ 2 * E := by
            have hm1 : (lvl + 1) * (3 * I.m.size + 12) ≤ cfg.P.d * (3 * I.m.size + 12) :=
              Nat.mul_le_mul_right _ hlt
            omega
          exact hB.2.1.trans (pow_le_pow_right₀ (by norm_num) hexpLe)
        have hwl : ch.toTreeChain.wlenAt ch.ℓ lvl e ≤
            ((ch.toTreeChain.sparsifierCycle lvl e).length : ℝ) * (2 : ℝ) ^ (2 * E) := by
          unfold TreeChain.wlenAt
          have haux : ∀ W : List (ℕ × Bool),
              (∀ x ∈ W, ch.toTreeChain.chainLen ch.ℓ (lvl + 1) x.1 ≤ (2 : ℝ) ^ (2 * E)) →
              (W.map fun x => ch.toTreeChain.chainLen ch.ℓ (lvl + 1) x.1).sum ≤
                (W.length : ℝ) * (2 : ℝ) ^ (2 * E) := by
            intro W hW
            induction W with
            | nil => simp
            | cons x xs ih =>
              simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
              have h1 := hW x List.mem_cons_self
              have h2 := ih fun y hy => hW y (List.mem_cons_of_mem _ hy)
              linarith
          exact haux _ fun x hx => (hstepB x hx).2
        have hclR : ((ch.toTreeChain.sparsifierCycle lvl e).length : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
          exact_mod_cast hCycLen
        calc ch.toTreeChain.wlenAt ch.ℓ lvl e
            ≤ ((ch.toTreeChain.sparsifierCycle lvl e).length : ℝ) * (2 : ℝ) ^ (2 * E) := hwl
          _ ≤ (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * E) :=
              mul_le_mul_of_nonneg_right hclR (by positivity)
          _ = (2 : ℝ) ^ (2 * E + k + 1) := by rw [← pow_add]; exact congrArg ((2 : ℝ) ^ ·) (by omega)
          _ ≤ (2 : ℝ) ^ (2 * E + k + 4 * I.m.size + 18) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
      · have heq : lvl = cfg.P.d := by omega
        subst heq
        have hCycSing : ch.toTreeChain.sparsifierCycle cfg.P.d e = [(e, true)] := by
          unfold TreeChain.sparsifierCycle TreeChain.activeEmb
          simp [ChainState.toTreeChain, walkRev, cfg]
        have hLenD : ch.toTreeChain.chainLen ch.ℓ cfg.P.d e ≤ (2 : ℝ) ^ (2 * E) := by
          have h1 := ((hLvls cfg.P.d le_rfl).1 e heGlvl).2
          have hsum : E + cfg.P.d * (3 * I.m.size + 12) ≤ 2 * E := by omega
          exact h1.trans (pow_le_pow_right₀ (by norm_num) hsum)
        have hLenD_nn : 0 ≤ ch.toTreeChain.chainLen ch.ℓ cfg.P.d e :=
          le_trans (by positivity) ((hLvls cfg.P.d le_rfl).1 e heGlvl).1
        have hLastH := hInv.hLastHolds ch.lastBran hInv.hLastBran
        have hwstr_le : (ch.toTreeChain.activeLSF cfg.P.d).wstr e ≤ cfg.LP.σ_last (ch.G cfg.P.d).n := by
          have hact : ch.toTreeChain.activeLSF cfg.P.d = ch.lastLSFs ch.lastBran := by
            unfold TreeChain.activeLSF
            simp [ChainState.toTreeChain, cfg]
          rw [hact]
          exact (hLastH.2.2.2 e heGlvl).2
        have hGd_n : (ch.G cfg.P.d).n ≤ 2 * I.m + 2 := by
          have hsubV : (ch.G cfg.P.d).V ⊆ (ch.G 0).V :=
            ch.toTreeChain.G_V_subset_of_le hH (Nat.zero_le _) le_rfl
          exact (Finset.card_le_card hsubV).trans hG0n
        have hsig := dryLast_sigmaLast_le J hJn hJm hCap hGd_n
        have hwlEq : ch.toTreeChain.wlenAt ch.ℓ cfg.P.d e =
            (ch.toTreeChain.activeLSF cfg.P.d).wstr e * ch.toTreeChain.chainLen ch.ℓ cfg.P.d e := by
          unfold TreeChain.wlenAt
          rw [hCycSing]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          rfl
        rw [hwlEq]
        calc (ch.toTreeChain.activeLSF cfg.P.d).wstr e * ch.toTreeChain.chainLen ch.ℓ cfg.P.d e
            ≤ cfg.LP.σ_last (ch.G cfg.P.d).n * (2 : ℝ) ^ (2 * E) :=
              mul_le_mul hwstr_le hLenD hLenD_nn (le_trans zero_le_one (hV.hLP.1 _))
          _ ≤ (2 : ℝ) ^ (k + 4 * I.m.size + 18) * (2 : ℝ) ^ (2 * E) :=
              mul_le_mul_of_nonneg_right hsig (by positivity)
          _ = (2 : ℝ) ^ (2 * E + k + 4 * I.m.size + 18) := by
              rw [← pow_add]; exact congrArg ((2 : ℝ) ^ ·) (by omega)
    have hPowLt : (2 : ℝ) ^ (P + pLast + 2 * E + k + 4 * I.m.size + 19) < (Num.capacity 4 L : ℝ) :=
      two_pow_lt_capacity4 (by omega)
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hmul : ch.toTreeChain.wlenAt ch.ℓ lvl e *
        (2 : ℝ) ^ coreLenPrec ch.toTreeChain.d P pLast lvl * 2 ≤
        (2 : ℝ) ^ (P + pLast + 2 * E + k + 4 * I.m.size + 19) := by
      have h1 : ch.toTreeChain.wlenAt ch.ℓ lvl e *
          (2 : ℝ) ^ coreLenPrec ch.toTreeChain.d P pLast lvl ≤
          (2 : ℝ) ^ (2 * E + k + 4 * I.m.size + 18) * (2 : ℝ) ^ (P + pLast) := by
        have hwl_nn : 0 ≤ ch.toTreeChain.wlenAt ch.ℓ lvl e := by
          unfold TreeChain.wlenAt
          refine List.sum_nonneg fun r hr => ?_
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
          have hClosed := ch.toTreeChain.sparsifierCycle_isClosedWalk hH hSpan hlvl he
          have hfCore : x.1 ∈ (ch.toTreeChain.activeCore lvl).E :=
            MGraph.isWalk_edges_mem hClosed x hx
          have hfGlvl : x.1 ∈ (ch.G lvl).E := (Finset.mem_sdiff.mp hfCore).1
          have hL0 := le_trans (by positivity) ((hLvls lvl hlvl').1 x.1 hfGlvl).1
          have hW0 : 0 ≤ (ch.toTreeChain.activeLSF lvl).wstr x.1 := by
            have hact := ch.toTreeChain.activeLSF_holds hH hlvl
            have hSub := ch.toTreeChain.forestsAreSubgraphs_of_holds hH
            have hstr := one_le_stretch (hSub lvl hlvl)
              (fun g hg => le_trans (by positivity) ((hLvls lvl hlvl').1 g hg).1) hfGlvl
            linarith [(hact.2.2.2 x.1 hfGlvl).1]
          exact mul_nonneg hW0 hL0
        exact mul_le_mul hWlenLe h2Q_le (by positivity) (by positivity)
      calc ch.toTreeChain.wlenAt ch.ℓ lvl e *
              (2 : ℝ) ^ coreLenPrec ch.toTreeChain.d P pLast lvl * 2
          ≤ (2 : ℝ) ^ (2 * E + k + 4 * I.m.size + 18) * (2 : ℝ) ^ (P + pLast) * 2 :=
            mul_le_mul_of_nonneg_right h1 (by norm_num)
        _ = (2 : ℝ) ^ (P + pLast + 2 * E + k + 4 * I.m.size + 19) := by
            rw [← pow_add, ← pow_succ]
            exact congrArg ((2 : ℝ) ^ ·) (by omega)
    linarith

/-- **`CandidateKeysFit` on `ShiftLoopChainInv` for `dryWitnessUsed`.** -/
theorem dry_candidateKeysFit_of_shiftLoop
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hShift : Ordered.ShiftLoopChainInv (concreteCirculationCfgWithLast dryWitnessUsed J) ch)
    (hGridInv : DryChainLenGridInv J ch)
    {pLast : ℕ}
    (hpLast :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      pLast ≤ 40 * ipmQualityRangeExponent I.m V k)
    {M_g : ℝ} (hM0 : 0 ≤ M_g)
    (hMle :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      M_g ≤ (2 : ℝ) ^ (40 * ipmQualityRangeExponent I.m V k))
    (hg : ∀ e ∈ (ch.G 0).E, |ch.g e| ≤ M_g) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    CandidateKeysFit 4 (ipmQualityPrecision I.m V k) pLast (ipmQualityLimbs I.m V k)
      ch.toTreeChain ch.g ch.ℓ :=
  dry_candidateKeysFit_of_chainInv J hJn hJm hCap hShift.1 hGridInv hpLast hM0 hMle hg

/-- **`CandidateKeysFit` on `OrdSolverReachedInv` for `dryWitnessUsed`.** -/
theorem dry_candidateKeysFit_of_reachedInv
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {L : ℕ} {Rcore : DSRep (SparseCoreOrdAbs (concreteCirculationCfgWithLast dryWitnessUsed J).T)}
    {κ : ℝ} {G : MGraph} {P : ℕ}
    {model : Alg2State (concreteCirculationCfgWithLast dryWitnessUsed J)}
    {tok : SolverToken (concreteCirculationCfgWithLast dryWitnessUsed J) L Rcore}
    (hm : G.m ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.M₀)
    (hn : G.n ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).N₀)
    (h : OrdSolverReachedInv κ G P model tok)
    (hGridInv : DryChainLenGridInv J model.chain)
    {pLast : ℕ}
    (hpLast :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      pLast ≤ 40 * ipmQualityRangeExponent I.m V k)
    {M_g : ℝ} (hM0 : 0 ≤ M_g)
    (hMle :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      M_g ≤ (2 : ℝ) ^ (40 * ipmQualityRangeExponent I.m V k))
    (hg : ∀ e ∈ (model.chain.G 0).E, |model.chain.g e| ≤ M_g) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    CandidateKeysFit 4 (ipmQualityPrecision I.m V k) pLast (ipmQualityLimbs I.m V k)
      model.chain.toTreeChain model.chain.g model.chain.ℓ := by
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  obtain ⟨D, η, op, T_step, hHist, hEdgeD, hLenD, hGD, hEq⟩ := h.2.1
  have hUncond := (Ordered.algorithm2_uncond_preserves_with (η := η) κ hV hHist hEdgeD hLenD
    (fun t ht => by rw [hGD t ht]; exact hm) (fun t ht => by rw [hGD t ht]; exact hn)).1 T_step le_rfl
  rw [← hEq] at hUncond
  exact dry_candidateKeysFit_of_chainInv J hJn hJm hCap hUncond.1 hGridInv hpLast hM0 hMle hg

/-! ## 3. Concrete dry-run `PotGradEvalFits` and `ForestWalkFits` -/

/-- Core `PotGradEvalFits` and `ForestWalkFits` theorem at level `j ≤ cfg.P.d` on `ChainInv` for
`dryWitnessUsed`, assuming `SelectPhiBoundedAt` on earlier levels `k < j`. -/
theorem dry_phiFillFits_of_chainInv
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hInv : Ordered.ChainInv (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).L
      (concreteCirculationCfgWithLast dryWitnessUsed J).TP
      (concreteCirculationCfgWithLast dryWitnessUsed J).LP
      (concreteCirculationCfgWithLast dryWitnessUsed J).P
      (concreteCirculationCfgWithLast dryWitnessUsed J).N₀ ch)
    (hGn : (ch.G 0).n ≤ 2 * (solverConnectedAugmented J).m + 2)
    {j : ℕ} (hj : j ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    {φ : ℕ → ℕ → ℝ} {M_g : ℝ} (hM0 : 0 ≤ M_g)
    (hMle :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      M_g ≤ (2 : ℝ) ^ (80 * ipmQualityRangeExponent I.m V k))
    (hg : ∀ e ∈ (ch.G 0).E, |ch.g e| ≤ M_g)
    (hPhiBd : ∀ k < j, SelectPhiBoundedAt ch.toTreeChain φ
      (2 * (solverConnectedAugmented J).m + 2) M_g k) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let P := ipmQualityPrecision I.m V k
    let L := ipmQualityLimbs I.m V k
    let C := ch.toTreeChain
    (∀ f ∈ (C.activeLSF j).F.F.E, PotGradEvalFits 4 L P C ch.g φ j f) ∧
    ForestWalkFits 4 L P (C.activeLSF j).F.F (potGrad C ch.g φ j) := by
  intro I V k P L C
  let E := ipmQualityRangeExponent I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let N := 2 * I.m + 2
  have hMle' : M_g ≤ (2 : ℝ) ^ (80 * E) := hMle
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hIm1 : 1 ≤ I.m :=
    Nat.lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap).1
  have hTH := hInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk
  have hH := hTH.1
  have hSub := C.forestsAreSubgraphs_of_holds hH
  have hRFj := (C.activeLSF_holds hH hj).2.1
  have hExp : cfg.P.d * (3 * I.m.size + 12) ≤ E :=
    chainLen_exponent_le_rangeExponent I.m V (concreteQualityBudgetWithLast dryWitnessUsed)
      hIm1 cfg.P.hM₀
  have h4L : P + 92 * E + 12 * I.m.size + 1480 ≤ 4 * L := ipmQuality_four_limbs_margin I.m V k
  have hj' : j ≤ cfg.P.d := hj
  have h2dE : 2 * cfg.P.d + 1 ≤ E := by
    have h1 : 12 * cfg.P.d ≤ cfg.P.d * (3 * I.m.size + 12) := by
      calc 12 * cfg.P.d = cfg.P.d * 12 := Nat.mul_comm _ _
        _ ≤ cfg.P.d * (3 * I.m.size + 12) := Nat.mul_le_mul_left cfg.P.d (by omega)
    have hE100 : 100 ≤ E := by dsimp only [E, ipmQualityRangeExponent]; omega
    omega
  have hN_nat : N ≤ 2 ^ (I.m.size + 2) := by
    have hsz := Nat.lt_size_self I.m
    have h2pos : 1 ≤ 2 ^ I.m.size := Nat.one_le_two_pow
    have hpow : 2 ^ (I.m.size + 2) = 4 * 2 ^ I.m.size := by rw [pow_add]; ring
    dsimp only [N]; omega
  have hNle : (N : ℝ) ≤ (2 : ℝ) ^ (I.m.size + 2) := by exact_mod_cast hN_nat
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have h3pow : (3 : ℝ) ^ j ≤ (2 : ℝ) ^ E := by
    calc (3 : ℝ) ^ j ≤ (4 : ℝ) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
      _ = ((2 : ℝ) ^ 2) ^ j := by norm_num
      _ = (2 : ℝ) ^ (2 * j) := (pow_mul 2 2 j).symm
      _ ≤ (2 : ℝ) ^ E := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2j1 : ((2 * j + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ E := by
    have h1 : 2 * j + 1 ≤ E := by omega
    have h2 : E ≤ 2 ^ E := Nat.le_of_lt Nat.lt_two_pow_self
    exact_mod_cast h1.trans h2
  let B : ℝ := (3 : ℝ) ^ j * (N : ℝ) * M_g
  have hB0 : 0 ≤ B := by positivity
  have hB_le : B ≤ (2 : ℝ) ^ (81 * E + I.m.size + 2) := by
    have h3N : (3 : ℝ) ^ j * (N : ℝ) ≤ (2 : ℝ) ^ E * (2 : ℝ) ^ (I.m.size + 2) :=
      mul_le_mul h3pow hNle (Nat.cast_nonneg _) (by positivity)
    calc B = (3 : ℝ) ^ j * (N : ℝ) * M_g := rfl
      _ ≤ ((2 : ℝ) ^ E * (2 : ℝ) ^ (I.m.size + 2)) * (2 : ℝ) ^ (80 * E) :=
          mul_le_mul h3N hMle' hM0 (by positivity)
      _ = (2 : ℝ) ^ (81 * E + I.m.size + 2) := by
          rw [← pow_add, ← pow_add]
          exact congrArg ((2 : ℝ) ^ ·) (by omega)
  have hphiK : ∀ k < j, ∀ f ∈ (C.activeLSF j).F.F.E,
      |φ k ((C.G k).head f)| ≤ B ∧ |φ k ((C.G k).tail f)| ≤ B := by
    intro k hkj f hf
    have hfGj : f ∈ (C.G j).E := (hSub j hj).2.1 hf
    have hfGk : f ∈ (C.G k).E := C.G_E_subset_of_le hH hkj.le hj hfGj
    have hEnds := C.G_isValid hH k (hkj.le.trans hj) f hfGk
    have hpow_le : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hkj.le
    refine ⟨(hPhiBd k hkj _ hEnds.2).trans ?_, (hPhiBd k hkj _ hEnds.1).trans ?_⟩ <;>
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow_le (Nat.cast_nonneg _)) hM0
  have hgF : ∀ f ∈ (C.activeLSF j).F.F.E, |ch.g f| ≤ B := by
    intro f hf
    have hfGj : f ∈ (C.G j).E := (hSub j hj).2.1 hf
    have hfG0 : f ∈ (C.G 0).E := C.G_E_subset_of_le hH (Nat.zero_le j) hj hfGj
    have h3ge1 : (1 : ℝ) ≤ (3 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have h3Nge1 : (1 : ℝ) ≤ (3 : ℝ) ^ j * (N : ℝ) := by
      simpa using mul_le_mul h3ge1 hNge1 zero_le_one (by positivity)
    have h1B : M_g ≤ B := by
      calc M_g = 1 * M_g := (one_mul _).symm
        _ ≤ ((3 : ℝ) ^ j * (N : ℝ)) * M_g := mul_le_mul_of_nonneg_right h3Nge1 hM0
    exact (hg f hfG0).trans h1B
  constructor
  · intro f hf
    refine potGradEvalFits_of_bound hB0 (hgF f hf) (fun k hkj => hphiK k hkj f hf) ?_
    have hPowLt : (2 : ℝ) ^ (P + 82 * E + I.m.size + 3) < (Num.capacity 4 L : ℝ) :=
      two_pow_lt_capacity4 (by omega)
    have h1 : ((2 * j + 1 : ℕ) : ℝ) * B ≤ (2 : ℝ) ^ E * (2 : ℝ) ^ (81 * E + I.m.size + 2) :=
      mul_le_mul h2j1 hB_le hB0 (by positivity)
    have hle : 2 * (((2 * j + 1 : ℕ) : ℝ) * B * (2 : ℝ) ^ P) ≤
        (2 : ℝ) ^ (P + 82 * E + I.m.size + 3) := by
      calc 2 * (((2 * j + 1 : ℕ) : ℝ) * B * (2 : ℝ) ^ P)
          ≤ 2 * (((2 : ℝ) ^ E * (2 : ℝ) ^ (81 * E + I.m.size + 2)) * (2 : ℝ) ^ P) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity)) zero_le_two
        _ = (2 : ℝ) ^ (P + 82 * E + I.m.size + 3) := by
            rw [← pow_add, ← pow_add, two_mul_pow_add_one]
            exact congrArg ((2 : ℝ) ^ ·) (by omega)
    exact lt_of_le_of_lt hle hPowLt
  · have hFm_nat : (C.activeLSF j).F.F.m ≤ N := by
      have h1 : (C.activeLSF j).F.F.m ≤ (C.activeLSF j).F.F.n := forest_m_le_n hRFj.1
      have h2 : (C.activeLSF j).F.F.n = (C.G j).n := congrArg Finset.card hRFj.2.1
      have h3 : (C.G j).n ≤ (C.G 0).n :=
        Finset.card_le_card (C.G_V_subset_of_le hH (Nat.zero_le j) hj)
      have h4 : (C.G 0).n ≤ N := hGn
      omega
    have hFmLe : ((C.activeLSF j).F.F.m : ℝ) ≤ (2 : ℝ) ^ (I.m.size + 2) :=
      (by exact_mod_cast hFm_nat : ((C.activeLSF j).F.F.m : ℝ) ≤ (N : ℝ)).trans hNle
    have hpgLe : ∀ e ∈ (C.activeLSF j).F.F.E,
        |potGrad C ch.g φ j e| ≤ ((2 * j + 1 : ℕ) : ℝ) * B := by
      intro e he
      rw [potGrad_eq_sum]
      have hsum : |∑ k ∈ Finset.range j, (φ k ((C.G k).head e) - φ k ((C.G k).tail e))| ≤
          ((2 * j : ℕ) : ℝ) * B := by
        calc |∑ k ∈ Finset.range j, (φ k ((C.G k).head e) - φ k ((C.G k).tail e))|
            ≤ ∑ k ∈ Finset.range j, |φ k ((C.G k).head e) - φ k ((C.G k).tail e)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _k ∈ Finset.range j, (2 * B) := by
              refine Finset.sum_le_sum fun k hk => ?_
              have hpk := hphiK k (Finset.mem_range.mp hk) e he
              exact (abs_sub _ _).trans (by linarith [hpk.1, hpk.2])
          _ = ((2 * j : ℕ) : ℝ) * B := by simp; ring
      have hcast : ((2 * j + 1 : ℕ) : ℝ) * B = B + ((2 * j : ℕ) : ℝ) * B := by push_cast; ring
      rw [hcast]
      exact (abs_add_le _ _).trans (add_le_add (hgF e he) hsum)
    refine forestWalkFits_of_bound (B := ((2 * j + 1 : ℕ) : ℝ) * B) (by positivity) hpgLe ?_
    have hPowLt : (2 : ℝ) ^ (P + 82 * E + 2 * I.m.size + 5) < (Num.capacity 4 L : ℝ) :=
      two_pow_lt_capacity4 (by omega)
    have h1 : ((2 * j + 1 : ℕ) : ℝ) * B ≤ (2 : ℝ) ^ E * (2 : ℝ) ^ (81 * E + I.m.size + 2) :=
      mul_le_mul h2j1 hB_le hB0 (by positivity)
    have h2 : ((C.activeLSF j).F.F.m : ℝ) * (((2 * j + 1 : ℕ) : ℝ) * B) ≤
        (2 : ℝ) ^ (I.m.size + 2) * ((2 : ℝ) ^ E * (2 : ℝ) ^ (81 * E + I.m.size + 2)) :=
      mul_le_mul hFmLe h1 (by positivity) (by positivity)
    have hle : 2 * (((C.activeLSF j).F.F.m : ℝ) * (((2 * j + 1 : ℕ) : ℝ) * B) * (2 : ℝ) ^ P) ≤
        (2 : ℝ) ^ (P + 82 * E + 2 * I.m.size + 5) := by
      calc 2 * (((C.activeLSF j).F.F.m : ℝ) * (((2 * j + 1 : ℕ) : ℝ) * B) * (2 : ℝ) ^ P)
          ≤ 2 * (((2 : ℝ) ^ (I.m.size + 2) * ((2 : ℝ) ^ E * (2 : ℝ) ^ (81 * E + I.m.size + 2))) *
              (2 : ℝ) ^ P) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (by positivity)) zero_le_two
        _ = (2 : ℝ) ^ (P + 82 * E + 2 * I.m.size + 5) := by
            rw [← pow_add, ← pow_add, ← pow_add, two_mul_pow_add_one]
            exact congrArg ((2 : ℝ) ^ ·) (by omega)
    exact lt_of_le_of_lt hle hPowLt

/-- **`PotGradEvalFits` and `ForestWalkFits` on `ShiftLoopChainInv` for `dryWitnessUsed`.** -/
theorem dry_phiFillFits_of_shiftLoop
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hShift : Ordered.ShiftLoopChainInv (concreteCirculationCfgWithLast dryWitnessUsed J) ch)
    (hGn : (ch.G 0).n ≤ 2 * (solverConnectedAugmented J).m + 2)
    {j : ℕ} (hj : j ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    {φ : ℕ → ℕ → ℝ} {M_g : ℝ} (hM0 : 0 ≤ M_g)
    (hMle :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      M_g ≤ (2 : ℝ) ^ (80 * ipmQualityRangeExponent I.m V k))
    (hg : ∀ e ∈ (ch.G 0).E, |ch.g e| ≤ M_g)
    (hPhiBd : ∀ k < j, SelectPhiBoundedAt ch.toTreeChain φ
      (2 * (solverConnectedAugmented J).m + 2) M_g k) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let P := ipmQualityPrecision I.m V k
    let L := ipmQualityLimbs I.m V k
    let C := ch.toTreeChain
    (∀ f ∈ (C.activeLSF j).F.F.E, PotGradEvalFits 4 L P C ch.g φ j f) ∧
    ForestWalkFits 4 L P (C.activeLSF j).F.F (potGrad C ch.g φ j) :=
  dry_phiFillFits_of_chainInv J hJn hJm hCap hShift.1 hGn hj hM0 hMle hg hPhiBd

/-- **`PotGradEvalFits` and `ForestWalkFits` on `OrdSolverReachedInv` for `dryWitnessUsed`.** -/
theorem dry_phiFillFits_of_reachedInv
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {L : ℕ} {Rcore : DSRep (SparseCoreOrdAbs (concreteCirculationCfgWithLast dryWitnessUsed J).T)}
    {κ : ℝ} {G : MGraph} {P : ℕ}
    {model : Alg2State (concreteCirculationCfgWithLast dryWitnessUsed J)}
    {tok : SolverToken (concreteCirculationCfgWithLast dryWitnessUsed J) L Rcore}
    (hm : G.m ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.M₀)
    (hn : G.n ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).N₀)
    (h : OrdSolverReachedInv κ G P model tok)
    (hGn : (model.chain.G 0).n ≤ 2 * (solverConnectedAugmented J).m + 2)
    {j : ℕ} (hj : j ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    {φ : ℕ → ℕ → ℝ} {M_g : ℝ} (hM0 : 0 ≤ M_g)
    (hMle :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      M_g ≤ (2 : ℝ) ^ (80 * ipmQualityRangeExponent I.m V k))
    (hg : ∀ e ∈ (model.chain.G 0).E, |model.chain.g e| ≤ M_g)
    (hPhiBd : ∀ k < j, SelectPhiBoundedAt model.chain.toTreeChain φ
      (2 * (solverConnectedAugmented J).m + 2) M_g k) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let Pq := ipmQualityPrecision I.m V k
    let Lq := ipmQualityLimbs I.m V k
    let C := model.chain.toTreeChain
    (∀ f ∈ (C.activeLSF j).F.F.E, PotGradEvalFits 4 Lq Pq C model.chain.g φ j f) ∧
    ForestWalkFits 4 Lq Pq (C.activeLSF j).F.F (potGrad C model.chain.g φ j) := by
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  obtain ⟨D, η, op, T_step, hHist, hEdgeD, hLenD, hGD, hEq⟩ := h.2.1
  have hUncond := (Ordered.algorithm2_uncond_preserves_with (η := η) κ hV hHist hEdgeD hLenD
    (fun t ht => by rw [hGD t ht]; exact hm) (fun t ht => by rw [hGD t ht]; exact hn)).1 T_step le_rfl
  rw [← hEq] at hUncond
  exact dry_phiFillFits_of_chainInv J hJn hJm hCap hUncond.1 hGn hj hM0 hMle hg hPhiBd

end MinCostFlow.Final.DryRun
