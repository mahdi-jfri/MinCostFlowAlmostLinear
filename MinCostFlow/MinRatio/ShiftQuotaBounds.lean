module

public import MinCostFlow.MinRatio.ShiftQuotaWriter
public import MinCostFlow.MinRatio.ShiftLoopSpaceBound
public import MinCostFlow.MinRatio.ShiftQuotaDeposit
public import MinCostFlow.MinRatio.ShiftInitQuota
public import MinCostFlow.Chain.Ordered.Algorithm2Facts
public import MinCostFlow.Final.ConcreteChainModelWithLast
public import MinCostFlow.Final.ForestConcreteProgramBase
public import MinCostFlow.IPM.Iteration
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Polynomial bounds and word-size discharge for shift quotas

Proves that the shift-quota powers `(10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * cfg.P.k) ^ (i + 1)`, the
pass limit `⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊`, and the full shift quotas
`shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i` along any IPM-length
history are bounded by explicit low-degree polynomials in `J.m + 2` (hence in `J.n + J.m + 2`) for
the concrete parameters of `Final.concreteCirculationCfgWithLast`.

Then discharges the `< 2 ^ w` word-size bounds directly at the final solver word size
`w = wordSize (Final.scratchWordMultiplier 1 deg) source.solverWords` under
`hw : IPM.Machine.ipmQualityParameterWordBits I.m V k ≤ w` (for arbitrary `source` and `J`, matching
`Final.DyadicWithVConcretePrograms.supported`), whenever `allocationCoefficient` exceeds the
witness-dependent constant `C`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM IPM.Machine Scaling Final

/-! ## Part A: Polynomial bound on the base powers `(10 * Ψ_game * k)^(i+1)` -/

private theorem log_twenty_le : Real.log 20 ≤ 3 := by
  have h20 : (20 : ℝ) ≤ Real.exp 3 := by
    have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    have he : (2.718 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc (20 : ℝ) ≤ 2.718 ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he 3
  calc Real.log 20 ≤ Real.log (Real.exp 3) := Real.log_le_log (by norm_num) h20
    _ = 3 := Real.log_exp 3

private theorem twenty_psi_pow_le_exp {M₀ d : ℕ} (hM : 1 ≤ M₀) {psi C_ψ : ℝ} (hpsi : 1 ≤ psi)
    (hd : d = chosenD (23 / 24) M₀)
    (hψ : psi ≤ Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((M₀ : ℝ) + 2) + 2))) :
    (20 * psi) ^ (d + 1) ≤ Real.exp (3 * (3 + C_ψ) * logShape M₀) := by
  have hL1 := one_le_log_add_two' hM
  have hLL1 := one_le_log_log_add_two hL1
  obtain ⟨_, _, hdHi⟩ := chosenD_bounds (β := 23 / 24) (by norm_num) hM
  rw [← hd, show ((1 : ℝ) - 23 / 24) / 2 = 1 / 48 by norm_num] at hdHi
  have hr1 : 1 ≤ Real.log ((M₀ : ℝ) + 2) ^ (1 / 48 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hL23 : 1 ≤ Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hsplit : Real.log ((M₀ : ℝ) + 2) ^ (1 / 48 : ℝ) *
      Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) = Real.log ((M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have hlogψ : Real.log psi ≤ C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((M₀ : ℝ) + 2) + 2) :=
    (Real.log_le_log (by linarith) hψ).trans (le_of_eq (Real.log_exp _))
  have hlog20ψ : Real.log (20 * psi) ≤ (3 + C_ψ) *
      (Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) * Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have h1 : (1 : ℝ) ≤ Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2) := one_le_mul_of_one_le_of_one_le hL23 hLL1
    nlinarith [log_twenty_le]
  have hlog0 : 0 ≤ Real.log (20 * psi) := Real.log_nonneg (by linarith)
  have hpos : (0 : ℝ) < 20 * psi := by linarith
  rw [← Real.exp_log (pow_pos hpos (d + 1)), Real.log_pow]
  apply Real.exp_le_exp.mpr
  push_cast
  calc ((d : ℝ) + 1) * Real.log (20 * psi)
      ≤ 3 * Real.log ((M₀ : ℝ) + 2) ^ (1 / 48 : ℝ) *
          ((3 + C_ψ) * (Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
            Real.log (Real.log ((M₀ : ℝ) + 2) + 2))) :=
        mul_le_mul (by linarith) hlog20ψ hlog0 (by linarith)
    _ = 3 * (3 + C_ψ) *
          ((Real.log ((M₀ : ℝ) + 2) ^ (1 / 48 : ℝ) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ)) *
            Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) := by ring
    _ = 3 * (3 + C_ψ) * logShape M₀ := by rw [hsplit]; rfl

/-- The shift-quota base power `(10 * Ψ_game * k)^(d + 1)` is bounded by
`M₀^2 * exp(3 * (3 + C_ψ) * logShape M₀)`. -/
theorem shiftQuotaBasePow_le_exp (cfg : Alg2Config) {C_ψ : ℝ}
    (hd : cfg.P.d = chosenD (23 / 24) cfg.P.M₀)
    (hψ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤ Real.exp (C_ψ * Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2))) :
    ((shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) : ℕ) : ℝ) ≤
      (cfg.P.M₀ : ℝ) ^ 2 * Real.exp (3 * (3 + C_ψ) * logShape cfg.P.M₀) := by
  set ψ := alg2PsiGame cfg.Ψ cfg.P.M₀
  have hψ1 : 1 ≤ ψ := alg2PsiGame_ge_one _ _
  have hcast : ((shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k : ℕ) : ℝ) = 10 * ψ * (cfg.P.k : ℝ) := by
    unfold shiftQuotaBase
    rw [show ψ = (alg2PsiGameNat ⌈cfg.Ψ⌉₊ cfg.P.M₀ : ℝ) from alg2PsiGame_eq_natCast _ _]
    push_cast; ring
  have hk := chainParams_k_pow_le cfg.P
  have h20 := twenty_psi_pow_le_exp cfg.P.hM₀ hψ1 hd hψ
  calc ((shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) : ℕ) : ℝ)
      = (10 * ψ * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1) := by rw [Nat.cast_pow, hcast]
    _ = (10 * ψ) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) ^ (cfg.P.d + 1) := mul_pow _ _ _
    _ ≤ (10 * ψ) ^ (cfg.P.d + 1) * (2 ^ (cfg.P.d + 1) * (cfg.P.M₀ : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
    _ = (20 * ψ) ^ (cfg.P.d + 1) * (cfg.P.M₀ : ℝ) ^ 2 := by
        rw [show (20 * ψ) = (10 * ψ) * 2 by ring, mul_pow (10 * ψ) 2]; ring
    _ ≤ Real.exp (3 * (3 + C_ψ) * logShape cfg.P.M₀) * (cfg.P.M₀ : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right h20 (by positivity)
    _ = (cfg.P.M₀ : ℝ) ^ 2 * Real.exp (3 * (3 + C_ψ) * logShape cfg.P.M₀) := by ring

/-- **The base powers `(10 * Ψ_game * k)^(i+1)` are `O((m + 2)^3)`** when `M₀ = max m T`,
`d = chosenD (23/24) M₀`, and `Ψ_game ≤ exp(C_ψ L^{23/24} log(L + 2))`. -/
theorem shiftQuotaBasePow_poly {C_ψ : ℝ} (hCψ : 0 ≤ C_ψ) (T : ℕ) :
    ∃ a : ℕ, ∀ (cfg : Alg2Config) (m : ℕ), cfg.P.M₀ = max m T →
      cfg.P.d = chosenD (23 / 24) cfg.P.M₀ →
      alg2PsiGame cfg.Ψ cfg.P.M₀ ≤ Real.exp (C_ψ * Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) →
      ∀ i ≤ cfg.P.d,
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (i + 1) ≤ a * (m + 2) ^ 3 := by
  set E : ℝ := 3 * (3 + C_ψ)
  have hE : 0 ≤ E := by positivity
  obtain ⟨B, _, hB⟩ := alg2TimeFactor_le_rpow (C := E) (a := 47 / 48) (δ := 1)
    (by norm_num) (by norm_num) (by norm_num)
  set B' : ℝ := B + alg2TimeFactor E (47 / 48) 0
  have hB'm : ∀ m : ℕ, alg2TimeFactor E (47 / 48) m ≤ B' * ((m : ℝ) + 2) := by
    intro m
    have h0 : 0 < alg2TimeFactor E (47 / 48) 0 := alg2TimeFactor_pos _ _ _
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.cast_zero, zero_add]; nlinarith
    · have h := hB m hm; rw [Real.rpow_one] at h
      have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
  set K : ℝ := ((T : ℝ) + 1) ^ 2 * alg2TimeFactor E (47 / 48) T * B'
  refine ⟨⌈K⌉₊, fun cfg m hM hd hψ i hi => ?_⟩
  have hbase1 : 1 ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k :=
    le_trans (by decide) (shiftQuotaBase_ge_ten _ _ cfg.P.hk)
  have hpowLe : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (i + 1) ≤
      shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
    Nat.pow_le_pow_right hbase1 (Nat.succ_le_succ hi)
  refine hpowLe.trans ?_
  have h2 := shiftQuotaBasePow_le_exp cfg hd hψ
  rw [← alg2TimeFactor_eq_exp_logShape] at h2
  have h2' : ((shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) : ℕ) : ℝ) ≤
      ((max m T : ℕ) : ℝ) ^ 2 * alg2TimeFactor E (47 / 48) (max m T) := by
    have hEq : (cfg.P.M₀ : ℝ) ^ 2 * alg2TimeFactor (3 * (3 + C_ψ)) (47 / 48) cfg.P.M₀ =
        ((max m T : ℕ) : ℝ) ^ 2 * alg2TimeFactor E (47 / 48) (max m T) := by
      rw [hM]
    exact h2.trans (le_of_eq hEq)
  have hmax := alg2TimeFactor_max_le hE m T
  have hT0 : 0 ≤ alg2TimeFactor E (47 / 48) T := (alg2TimeFactor_pos _ _ _).le
  have hMle : ((max m T : ℕ) : ℝ) ≤ ((T : ℝ) + 1) * ((m : ℝ) + 2) := by
    have : (max m T : ℕ) ≤ m + T := max_le (by omega) (by omega)
    have h' : ((max m T : ℕ) : ℝ) ≤ (m : ℝ) + T := by exact_mod_cast this
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hT0' : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    nlinarith
  have hreal : ((shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) : ℕ) : ℝ) ≤
      K * ((m : ℝ) + 2) ^ 3 := by
    have hsq : ((max m T : ℕ) : ℝ) ^ 2 ≤ (((T : ℝ) + 1) * ((m : ℝ) + 2)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hMle 2
    have hfac : alg2TimeFactor E (47 / 48) (max m T) ≤
        alg2TimeFactor E (47 / 48) T * (B' * ((m : ℝ) + 2)) :=
      hmax.trans (mul_le_mul_of_nonneg_left (hB'm m) hT0)
    calc ((shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) : ℕ) : ℝ)
        ≤ ((max m T : ℕ) : ℝ) ^ 2 * alg2TimeFactor E (47 / 48) (max m T) := h2'
      _ ≤ (((T : ℝ) + 1) * ((m : ℝ) + 2)) ^ 2 *
            (alg2TimeFactor E (47 / 48) T * (B' * ((m : ℝ) + 2))) :=
          mul_le_mul hsq hfac (alg2TimeFactor_pos _ _ _).le (by positivity)
      _ = K * ((m : ℝ) + 2) ^ 3 := by ring
  have hK : K * ((m : ℝ) + 2) ^ 3 ≤ (⌈K⌉₊ : ℝ) * ((m : ℝ) + 2) ^ 3 :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil K) (by positivity)
  have hcast : ((shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) : ℕ) : ℝ) ≤
      ((⌈K⌉₊ * (m + 2) ^ 3 : ℕ) : ℝ) :=
    hreal.trans (hK.trans (le_of_eq (by push_cast; ring)))
  exact_mod_cast hcast

theorem ceil_two_mul_alg2PsiGame_le_basePow (cfg : Alg2Config) :
    ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ ≤
      shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) := by
  rw [ceil_two_mul_alg2PsiGame]
  have hB1 : 1 ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k :=
    le_trans (by decide) (shiftQuotaBase_ge_ten _ _ cfg.P.hk)
  have hleB : 2 * alg2PsiGameNat ⌈cfg.Ψ⌉₊ cfg.P.M₀ ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k := by
    unfold shiftQuotaBase
    have hk : 1 ≤ cfg.P.k := cfg.P.hk
    calc 2 * alg2PsiGameNat ⌈cfg.Ψ⌉₊ cfg.P.M₀
        ≤ 10 * alg2PsiGameNat ⌈cfg.Ψ⌉₊ cfg.P.M₀ := by omega
      _ ≤ 10 * alg2PsiGameNat ⌈cfg.Ψ⌉₊ cfg.P.M₀ * cfg.P.k := Nat.le_mul_of_pos_right _ hk
  calc 2 * alg2PsiGameNat ⌈cfg.Ψ⌉₊ cfg.P.M₀
      ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ 1 := by simpa using hleB
    _ ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
        Nat.pow_le_pow_right hB1 (by omega)

/-! ## Part B: Bounding `shiftQuotaWord` by rebuild counts and history length -/

/-- Every level's shift quota is at most `(1 + ∑_{j ≤ d} reb j) * B^(d + 1)`. -/
theorem shiftQuotaWord_le_one_add_sum_rebuilds (cfg : Alg2Config) (reb : ℕ → ℕ)
    {i : ℕ} (hi : i ≤ cfg.P.d) :
    shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) reb i ≤
      (1 + ∑ j ∈ Finset.range (cfg.P.d + 1), reb j) *
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) := by
  rw [shiftQuotaWord_eq_gameShiftBoundNat]
  set B := shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k
  have hB1 : 1 ≤ B := le_trans (by decide) (shiftQuotaBase_ge_ten _ _ cfg.P.hk)
  unfold gameShiftBoundNat
  have h1 : B ^ (i + 1) ≤ B ^ (cfg.P.d + 1) := Nat.pow_le_pow_right hB1 (by omega)
  have hsum : ∑ j ∈ Finset.range (i + 1), reb j * B ^ (i + 1 - j) ≤
      (∑ j ∈ Finset.range (cfg.P.d + 1), reb j) * B ^ (cfg.P.d + 1) := by
    rw [Finset.sum_mul]
    calc ∑ j ∈ Finset.range (i + 1), reb j * B ^ (i + 1 - j)
        ≤ ∑ j ∈ Finset.range (i + 1), reb j * B ^ (cfg.P.d + 1) :=
          Finset.sum_le_sum fun j _ =>
            Nat.mul_le_mul_left (reb j) (Nat.pow_le_pow_right hB1 (by omega))
      _ ≤ ∑ j ∈ Finset.range (cfg.P.d + 1), reb j * B ^ (cfg.P.d + 1) :=
          Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  rw [Nat.add_mul, one_mul]
  exact Nat.add_le_add h1 hsum

/-- One `Ordered.algorithm2_updateWith` step increases `∑_{j ≤ d} rebuildCount j` by at most `1`. -/
theorem ordered_algorithm2_updateWith_sum_rebuildCount (cfg : Alg2Config) (κ : ℝ)
    (st : Alg2State cfg) (U : List Update) (g' ℓ' : ℕ → ℝ) (η : ℝ) :
    ∑ j ∈ Finset.range (cfg.P.d + 1),
        (Ordered.algorithm2_updateWith cfg κ st U g' ℓ' η).1.chain.rebuildCount j ≤
      (∑ j ∈ Finset.range (cfg.P.d + 1), st.chain.rebuildCount j) + 1 := by
  set tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh U
  set ch1 := (Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
    (fun e' => g' (tb.2.2.1 e')) (fun e' => ℓ' (tb.2.2.1 e'))).1
  set ren := Ordered.level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount
  set G₀' := (st.chain.G 0).applyBatch tb.2.2.2.2
  set bp1 := match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
    | none => (st.branD, st.passes)
    | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
  set lp := Ordered.algorithm2_loopWith cfg κ tb.1 (Ordered.level0E2I ren G₀' tb.2.1) g' ℓ' ch1
    bp1.1 bp1.2 (st.lctUpdateOps + U.length)
  have hloopReb : lp.1.rebuildCount = ch1.rebuildCount :=
    (algorithm2_loopWith_updCount_le cfg κ tb.1 (Ordered.level0E2I ren G₀' tb.2.1) g' ℓ'
      (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch1) ch1 bp1.1 bp1.2
      (st.lctUpdateOps + U.length) le_rfl).1
  have hupdReb : (Ordered.algorithm2_updateWith cfg κ st U g' ℓ' η).1.chain.rebuildCount =
      ch1.rebuildCount := by
    have hcases := Ordered.algorithm2_updateWith_eq_of_loop κ st U g' ℓ' η
    cases hlp : lp.2.2.2.2 with
    | none =>
      have h := hcases.1 hlp
      rw [h]; exact hloopReb
    | some Δ =>
      have h := hcases.2 Δ hlp
      rw [h]; exact hloopReb
  rw [hupdReb]
  set st0 : ChainState cfg.T cfg.P :=
    { st.chain with
      recUpdates := fun j => if j = 0 then st.chain.recUpdates 0 + tb.2.2.2.2.length else st.chain.recUpdates j }
  have hloopCases := Ordered.updateLoop_rebuildCount_cases cfg.T cfg.L cfg.TP cfg.P cfg.N₀
    (fun e' => ℓ' (tb.2.2.1 e')) (fun e' => g' (tb.2.2.1 e')) cfg.P.d 0 st0 G₀'
    tb.2.2.2.2 ((st.chain.G 0).batchEnc tb.2.2.2.2) (by omega)
  have hch1Eq : ch1 = (Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀
      (fun e' => ℓ' (tb.2.2.1 e')) (fun e' => g' (tb.2.2.1 e')) cfg.P.d 0 st0 G₀'
      tb.2.2.2.2 ((st.chain.G 0).batchEnc tb.2.2.2.2)).1 := rfl
  rcases hloopCases with heq | ⟨iStar, _, hiLt, heq⟩
  · have hrc : ch1.rebuildCount = st.chain.rebuildCount := by rw [hch1Eq]; exact heq
    rw [hrc]; omega
  · have hch1 : ch1.rebuildCount = fun j => if j = iStar then st.chain.rebuildCount iStar + 1
        else st.chain.rebuildCount j := by rw [hch1Eq]; exact heq
    rw [hch1]
    have hsumEq : ∑ j ∈ Finset.range (cfg.P.d + 1),
        (if j = iStar then st.chain.rebuildCount iStar + 1 else st.chain.rebuildCount j) =
        ∑ j ∈ Finset.range (cfg.P.d + 1),
          (st.chain.rebuildCount j + if j = iStar then 1 else 0) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with h <;> [subst h; skip] <;> omega
    rw [hsumEq, Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (cfg.P.d + 1)) iStar]
    simp [Finset.mem_range.mpr (by omega : iStar < cfg.P.d + 1)]

/-- Along any history of length `T` of ordered Algorithm 2, total rebuilds across all levels
`0..d` are at most `T`. -/
theorem ordered_history_sum_rebuildCount_le (cfg : Alg2Config) (κ : ℝ)
    (D : DynamicInstance) (η : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) :
    ∑ j ∈ Finset.range (cfg.P.d + 1),
      (minRatioFailState (Ordered.algorithm2_dsWith cfg κ) D η op T).chain.rebuildCount j ≤ T := by
  induction T with
  | zero =>
    have h0 : (Ordered.algorithm2_init cfg (D.G 0) (D.g 0) (D.ℓ 0)).chain.rebuildCount =
        fun _ => 0 :=
      (algorithm1_initialize_counts cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀
        (D.G 0) (D.ℓ 0) (D.g 0)).2.1
    change ∑ j ∈ Finset.range (cfg.P.d + 1),
      (Ordered.algorithm2_init cfg (D.G 0) (D.g 0) (D.ℓ 0)).chain.rebuildCount j ≤ 0
    rw [h0]; simp
  | succ t ih =>
    rw [minRatioFailState.eq_2]
    cases h : op (t + 1)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih.trans (Nat.le_succ t)
    · simp only [↓reduceIte]
      exact (ordered_algorithm2_updateWith_sum_rebuildCount cfg κ _ _ _ _ _).trans
        (Nat.add_le_add_right ih 1)

/-! ## Part C: Concrete polynomial bounds for `concreteCirculationCfgWithLast` -/

/-- For the concrete configuration `concreteCirculationCfgWithLast W J`, both the base powers
`(10 * Ψ_game * k)^(i + 1)` and `⌈2 * Ψ_game⌉₊` are bounded by `a * (J.m + 2) ^ 3` with a constant
`a` depending only on `W`. -/
theorem concrete_shiftQuotaBasePow_poly
    {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (SparseCore.lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec) :
    ∃ a : ℕ, ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
      let cfg := concreteCirculationCfgWithLast W J
      (∀ i ≤ cfg.P.d,
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (i + 1) ≤ a * (J.m + 2) ^ 3) ∧
      ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ ≤ a * (J.m + 2) ^ 3 := by
  let threshold := concreteEdgeThresholdWithLast W
  obtain ⟨a₀, ha₀⟩ := shiftQuotaBasePow_poly (C_ψ := 1) zero_le_one threshold
  refine ⟨343 * a₀, fun J hJn hJm hCap => ?_⟩
  dsimp only
  set cfg := concreteCirculationCfgWithLast W J
  set I := solverConnectedAugmented J
  obtain ⟨_, _, hPsi, _, _⟩ := concreteCirculation_bounds_of (le_max_left W.M_thresh _)
    (le_max_right W.M_thresh _) (concreteEdgeThresholdWithLast_ge_two W) J hJn hJm hCap
  have hM0 : cfg.P.M₀ = max I.m threshold := rfl
  have hd : cfg.P.d = chosenD (23 / 24) cfg.P.M₀ := rfl
  have hImLe : I.m ≤ 7 * J.m := (solverConnectedAugmented_size J hJn hJm hCap).2
  have hIm2 : I.m + 2 ≤ 7 * (J.m + 2) := by omega
  have hcube : (I.m + 2) ^ 3 ≤ 343 * (J.m + 2) ^ 3 := by
    calc (I.m + 2) ^ 3 ≤ (7 * (J.m + 2)) ^ 3 := Nat.pow_le_pow_left hIm2 3
      _ = 343 * (J.m + 2) ^ 3 := by ring
  have hpow : ∀ i ≤ cfg.P.d,
      shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (i + 1) ≤ 343 * a₀ * (J.m + 2) ^ 3 := by
    intro i hi
    have h1 := ha₀ cfg I.m hM0 hd hPsi i hi
    calc shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (i + 1)
        ≤ a₀ * (I.m + 2) ^ 3 := h1
      _ ≤ a₀ * (343 * (J.m + 2) ^ 3) := Nat.mul_le_mul_left a₀ hcube
      _ = 343 * a₀ * (J.m + 2) ^ 3 := by ring
  exact ⟨hpow, (ceil_two_mul_alg2PsiGame_le_basePow cfg).trans (hpow cfg.P.d le_rfl)⟩

/-- The IPM iteration limit at the concrete parameters is `O((J.m + 2)^4)`. -/
theorem concrete_ipm_iterationLimit_poly
    {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (SparseCore.lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec) :
    ∃ c_iter : ℕ, ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
      IPM.iterationLimit I V (1 / (2 : ℝ) ^ k) ≤ c_iter * (J.m + 2) ^ 4 := by
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let Ck := concreteQualityLinearCoeff threshold A
  refine ⟨7000000000 * (Ck + 1) ^ 2 + 1, fun J hJn hJm hCap => ?_⟩
  dsimp only
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent threshold A I.m
  have hImLe : I.m ≤ 7 * J.m := (solverConnectedAugmented_size J hJn hJm hCap).2
  have hVLe : V ≤ 16 * J.m ^ 81 := solverPenalty_le J.m hJm
  have h2k : (2 : ℕ) ^ k ≤ Ck * (I.m + 2) := cappedQuality_linear_spec threshold A I.m
  have h2k_le : (2 : ℕ) ^ k ≤ 7 * (Ck + 1) * (J.m + 2) := by
    have h1 : I.m + 2 ≤ 7 * (J.m + 2) := by omega
    calc (2 : ℕ) ^ k ≤ Ck * (I.m + 2) := h2k
      _ ≤ (Ck + 1) * (7 * (J.m + 2)) := Nat.mul_le_mul (Nat.le_succ _) h1
      _ = 7 * (Ck + 1) * (J.m + 2) := by ring
  -- Bound `Real.log (I.m * V) ≤ 100 * (J.m + 2)`
  have hlog_le : Real.log ((I.m : ℝ) * (V : ℝ)) ≤ 100 * ((J.m : ℝ) + 2) := by
    by_cases hprod : (I.m : ℝ) * (V : ℝ) ≤ 1
    · have : Real.log ((I.m : ℝ) * (V : ℝ)) ≤ 0 := by
        rcases le_or_gt ((I.m : ℝ) * (V : ℝ)) 0 with h0 | hpos
        · rcases eq_or_lt_of_le h0 with h0' | hneg
          · rw [h0', Real.log_zero]
          · exact False.elim (by linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) I.m) (Nat.cast_nonneg (α := ℝ) V)])
        · exact Real.log_nonpos hpos.le hprod
      linarith [Nat.cast_nonneg (α := ℝ) J.m]
    · push Not at hprod
      have hJm2 : (1 : ℝ) ≤ (J.m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) J.m]
      have hIV : (I.m : ℝ) * (V : ℝ) ≤ ((J.m : ℝ) + 2) ^ 90 := by
        have h1 : (I.m : ℝ) ≤ 7 * (J.m : ℝ) := by exact_mod_cast hImLe
        have h2 : (V : ℝ) ≤ 16 * (J.m : ℝ) ^ 81 := by exact_mod_cast hVLe
        have h3 : (7 : ℝ) * 16 ≤ ((J.m : ℝ) + 2) ^ 8 := by
          have : (2 : ℝ) ≤ (J.m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) J.m]
          calc (7 : ℝ) * 16 = 112 := by norm_num
            _ ≤ 2 ^ 8 := by norm_num
            _ ≤ ((J.m : ℝ) + 2) ^ 8 := pow_le_pow_left₀ (by norm_num) this 8
        have h4 : (J.m : ℝ) ^ 82 ≤ ((J.m : ℝ) + 2) ^ 82 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 82
        calc (I.m : ℝ) * (V : ℝ)
            ≤ (7 * (J.m : ℝ)) * (16 * (J.m : ℝ) ^ 81) :=
              mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
          _ = (7 * 16) * (J.m : ℝ) ^ 82 := by ring
          _ ≤ ((J.m : ℝ) + 2) ^ 8 * ((J.m : ℝ) + 2) ^ 82 :=
              mul_le_mul h3 h4 (by positivity) (by positivity)
          _ = ((J.m : ℝ) + 2) ^ 90 := by ring
      have hlog1 := Real.log_le_log (by linarith) hIV
      rw [Real.log_pow] at hlog1
      have hlogx : Real.log ((J.m : ℝ) + 2) ≤ (J.m : ℝ) + 2 :=
        (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      push_cast at hlog1
      linarith
  unfold IPM.iterationLimit
  rw [Nat.ceil_le]
  have hdiv : 200000 * (I.m : ℝ) * Real.log ((I.m : ℝ) * (V : ℝ)) / (1 / (2 : ℝ) ^ k) ^ 2 =
      200000 * (I.m : ℝ) * Real.log ((I.m : ℝ) * (V : ℝ)) * ((2 : ℝ) ^ k) ^ 2 := by
    field_simp
  rw [hdiv]
  have h2k_r : (2 : ℝ) ^ k ≤ 7 * ((Ck : ℝ) + 1) * ((J.m : ℝ) + 2) := by exact_mod_cast h2k_le
  have h2k_sq : ((2 : ℝ) ^ k) ^ 2 ≤ 49 * ((Ck : ℝ) + 1) ^ 2 * ((J.m : ℝ) + 2) ^ 2 := by
    calc ((2 : ℝ) ^ k) ^ 2 ≤ (7 * ((Ck : ℝ) + 1) * ((J.m : ℝ) + 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h2k_r 2
      _ = 49 * ((Ck : ℝ) + 1) ^ 2 * ((J.m : ℝ) + 2) ^ 2 := by ring
  have hIm_r : (I.m : ℝ) ≤ 7 * ((J.m : ℝ) + 2) := by
    have : (I.m : ℝ) ≤ 7 * (J.m : ℝ) := by exact_mod_cast hImLe
    linarith
  have hlog_nn : 0 ≤ max 0 (Real.log ((I.m : ℝ) * (V : ℝ))) := le_max_left _ _
  have hlog_le' : max 0 (Real.log ((I.m : ℝ) * (V : ℝ))) ≤ 100 * ((J.m : ℝ) + 2) :=
    max_le (by positivity) hlog_le
  have hstep1 : 200000 * (I.m : ℝ) * Real.log ((I.m : ℝ) * (V : ℝ)) * ((2 : ℝ) ^ k) ^ 2 ≤
      200000 * (I.m : ℝ) * max 0 (Real.log ((I.m : ℝ) * (V : ℝ))) * ((2 : ℝ) ^ k) ^ 2 := by
    gcongr
    exact le_max_right _ _
  have hstep2 : 200000 * (I.m : ℝ) * max 0 (Real.log ((I.m : ℝ) * (V : ℝ))) * ((2 : ℝ) ^ k) ^ 2 ≤
      200000 * (7 * ((J.m : ℝ) + 2)) * (100 * ((J.m : ℝ) + 2)) *
        (49 * ((Ck : ℝ) + 1) ^ 2 * ((J.m : ℝ) + 2) ^ 2) := by
    gcongr
  refine hstep1.trans (hstep2.trans ?_)
  push_cast
  have hpow4 : (0 : ℝ) ≤ ((J.m : ℝ) + 2) ^ 4 := by positivity
  have hck2 : (0 : ℝ) ≤ ((Ck : ℝ) + 1) ^ 2 := by positivity
  nlinarith

/-- **Full shift quotas along any IPM-length history are `O((J.m + 2)^7)`** (hence
`O((J.n + J.m + 2)^7)`) for `concreteCirculationCfgWithLast W J`, with a constant depending only
on `W`. -/
theorem concrete_shiftQuotaWord_ipm_poly
    {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (SparseCore.lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec) :
    ∃ C_q : ℕ, ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
      let cfg := concreteCirculationCfgWithLast W J
      ∀ (D : DynamicInstance) (η : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (κ : ℝ),
        T ≤ 2 * IPM.iterationLimit I V (1 / (2 : ℝ) ^ k) + 1 →
        let model := minRatioFailState (Ordered.algorithm2_dsWith cfg κ) D η op T
        (∀ i ≤ cfg.P.d,
          shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i ≤
            C_q * (J.m + 2) ^ 7) ∧
        ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ ≤ C_q * (J.m + 2) ^ 7 := by
  obtain ⟨a, ha⟩ := concrete_shiftQuotaBasePow_poly W
  obtain ⟨c_iter, hc_iter⟩ := concrete_ipm_iterationLimit_poly W
  refine ⟨(2 * c_iter + 2) * a, fun J hJn hJm hCap => ?_⟩
  dsimp only
  intro D η op T κ hT
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
  set cfg := concreteCirculationCfgWithLast W J
  set model := minRatioFailState (Ordered.algorithm2_dsWith cfg κ) D η op T
  obtain ⟨hbase, hceil⟩ := ha J hJn hJm hCap
  have hiter := hc_iter J hJn hJm hCap
  have hsumReb := ordered_history_sum_rebuildCount_le cfg κ D η op T
  have h1T : 1 + T ≤ (2 * c_iter + 2) * (J.m + 2) ^ 4 := by
    have hpow1 : 1 ≤ (J.m + 2) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have hiter' : IPM.iterationLimit I V (1 / (2 : ℝ) ^ k) ≤ c_iter * (J.m + 2) ^ 4 := hiter
    calc 1 + T ≤ 2 * IPM.iterationLimit I V (1 / (2 : ℝ) ^ k) + 2 := by omega
      _ ≤ 2 * (c_iter * (J.m + 2) ^ 4) + 2 * (J.m + 2) ^ 4 := by omega
      _ = (2 * c_iter + 2) * (J.m + 2) ^ 4 := by ring
  refine ⟨fun i hi => ?_, ?_⟩
  · calc shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i
        ≤ (1 + ∑ j ∈ Finset.range (cfg.P.d + 1), model.chain.rebuildCount j) *
            shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
          shiftQuotaWord_le_one_add_sum_rebuilds cfg model.chain.rebuildCount hi
      _ ≤ (1 + T) * (a * (J.m + 2) ^ 3) :=
          Nat.mul_le_mul (Nat.add_le_add_left hsumReb 1) (hbase cfg.P.d le_rfl)
      _ ≤ ((2 * c_iter + 2) * (J.m + 2) ^ 4) * (a * (J.m + 2) ^ 3) :=
          Nat.mul_le_mul_right _ h1T
      _ = (2 * c_iter + 2) * a * (J.m + 2) ^ 7 := by ring
  · have h4 : (J.m + 2) ^ 3 ≤ (J.m + 2) ^ 7 := Nat.pow_le_pow_right (by omega) (by decide)
    calc ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊
        ≤ a * (J.m + 2) ^ 3 := hceil
      _ ≤ (2 * c_iter + 2) * a * (J.m + 2) ^ 7 := by
          have : a ≤ (2 * c_iter + 2) * a := Nat.le_mul_of_pos_left a (by omega)
          exact Nat.mul_le_mul this h4

/-! ## Part D: Discharging `< 2 ^ w` from the final program's word size -/

/-- Any quantity bounded by `C * (J.m + 2) ^ D` with `D ≤ 40` fits below `2 ^ w` at the final
solver word size `w = wordSize (scratchWordMultiplier 1 deg) source.solverWords` whenever
`hw : ipmQualityParameterWordBits I.m V k ≤ w` holds and `(3 ^ D * C) ^ 2 < 2 ^ (3 * (deg + 1))`.

For large `J.m`, `hw` alone gives `J.m ^ 81 ≤ V < 2 ^ w`. For small `J.m`, `source.solverWords`
has length at least `2`, giving `w ≥ 3 * (deg + 1)` and hence `(3 ^ D * C) ^ 2 < 2 ^ w`. -/
theorem lt_two_pow_wordSize_of_poly_and_hw (source J : Circulation) (hJm : 0 < J.m)
    {deg k C D val : ℕ} (hD : D ≤ 40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) k ≤
      wordSize (scratchWordMultiplier 1 deg) source.solverWords)
    (hval : val ≤ C * (J.m + 2) ^ D)
    (hdeg : (3 ^ D * C) ^ 2 < 2 ^ (3 * (deg + 1))) :
    val < 2 ^ wordSize (scratchWordMultiplier 1 deg) source.solverWords := by
  set w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
  set K := 3 ^ D * C
  have hvalK : val ≤ K * J.m ^ D := by
    have hjm : J.m + 2 ≤ 3 * J.m := by omega
    calc val ≤ C * (J.m + 2) ^ D := hval
      _ ≤ C * (3 * J.m) ^ D := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hjm D)
      _ = K * J.m ^ D := by rw [Nat.mul_pow]; ring
  by_cases hbig : K < J.m ^ (81 - D)
  · have hVlt : solverPenalty J.m < 2 ^ w :=
      (ipm_quality_parameter_words_fit _ _ _ hw).2.2.2.2.2.2.2
    have hVge : J.m ^ 81 ≤ solverPenalty J.m := by
      unfold solverPenalty solverCapacityBound
      have hcap : J.m ^ 40 ≤ max 2 (J.m ^ 40) := le_max_right _ _
      calc J.m ^ 81 = 1 * J.m * (J.m ^ 40) ^ 2 := by ring
        _ ≤ 4 * J.m * (max 2 (J.m ^ 40)) ^ 2 :=
            Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hcap 2)
    have hlt81 : val < J.m ^ 81 := by
      calc val ≤ K * J.m ^ D := hvalK
        _ < J.m ^ (81 - D) * J.m ^ D := Nat.mul_lt_mul_of_pos_right hbig (Nat.pow_pos hJm)
        _ = J.m ^ 81 := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
    exact lt_of_lt_of_le hlt81 (hVge.trans_lt hVlt).le
  · push Not at hbig
    have hJmD : J.m ^ D ≤ K :=
      (Nat.pow_le_pow_right hJm (by omega : D ≤ 81 - D)).trans hbig
    have hvalSq : val ≤ K ^ 2 := by
      calc val ≤ K * J.m ^ D := hvalK
        _ ≤ K * K := Nat.mul_le_mul_left K hJmD
        _ = K ^ 2 := (pow_two K).symm
    have hsrcLen : 2 ≤ source.solverWords.length := by
      rw [Circulation.solverWords_length]; omega
    have hlog2 : 2 ≤ Nat.log 2 (source.solverWords.length + source.solverWords.foldr max 0 + 2) := by
      have h4 : 2 ^ 2 ≤ source.solverWords.length + source.solverWords.foldr max 0 + 2 := by omega
      exact (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr h4
    have hmult : deg + 1 ≤ scratchWordMultiplier 1 deg := by
      unfold scratchWordMultiplier; omega
    have hwLo : 3 * (deg + 1) ≤ w := by
      unfold w wordSize
      calc 3 * (deg + 1) = (deg + 1) * 3 := by ring
        _ ≤ scratchWordMultiplier 1 deg *
            (Nat.log 2 (source.solverWords.length + source.solverWords.foldr max 0 + 2) + 1) :=
          Nat.mul_le_mul hmult (by omega)
    exact lt_of_le_of_lt hvalSq (hdeg.trans_le (Nat.pow_le_pow_right (by decide) hwLo))

/-- When `C ≤ allocationCoefficient`, `forestProgramsScratchDegree allocationCoefficient
allocationDegree Ck` automatically satisfies `(3 ^ 7 * C) ^ 2 < 2 ^ (3 * (deg + 1))`. -/
theorem forestProgramsScratchDegree_covers_shiftQuota (allocationCoefficient allocationDegree Ck C : ℕ)
    (hC : C ≤ allocationCoefficient) :
    (3 ^ 7 * C) ^ 2 < 2 ^ (3 * (forestProgramsScratchDegree allocationCoefficient allocationDegree Ck + 1)) := by
  set deg := forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
  have hclog : Nat.clog 2 C ≤ Nat.clog 2 (forestSpaceCoeff allocationCoefficient * 8 ^ forestSpaceDeg allocationDegree) := by
    apply Nat.clog_mono_right
    have h1 : C ≤ forestSpaceCoeff allocationCoefficient := hC.trans (le_max_left _ _)
    have h2 : 1 ≤ 8 ^ forestSpaceDeg allocationDegree := Nat.one_le_pow _ _ (by decide)
    exact h1.trans (Nat.le_mul_of_pos_right _ h2)
  have hdegLo : 10 * Nat.clog 2 C + 2400 ≤ deg := by
    dsimp only [deg, forestProgramsScratchDegree, forestScratchDegree]
    omega
  have hexp : 24 + 2 * Nat.clog 2 C < 3 * (deg + 1) := by omega
  have hCpow : C ≤ 2 ^ Nat.clog 2 C := Nat.le_pow_clog (by decide) C
  have h37 : 3 ^ 7 ≤ 2 ^ 12 := by decide
  calc (3 ^ 7 * C) ^ 2
      ≤ (2 ^ 12 * 2 ^ Nat.clog 2 C) ^ 2 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul h37 hCpow) 2
    _ = 2 ^ (24 + 2 * Nat.clog 2 C) := by
        rw [Nat.mul_pow, ← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
    _ < 2 ^ (3 * (deg + 1)) := Nat.pow_lt_pow_right (by decide) hexp

/-- **Word-size discharge for the final assembly.** For any chain witness `W`, there is a constant
`C_q` (depending only on `W`) such that whenever `C_q ≤ allocationCoefficient`, at the final
solver word size `w = wordSize (scratchWordMultiplier 1 deg) source.solverWords` with
`hw : ipmQualityParameterWordBits I.m V k ≤ w`:
1. `⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ < 2 ^ w` (discharging `hpsiLimW`);
2. every base power `(10 * Ψ_game * k)^(i+1)` fits in `< 2 ^ w`;
3. every shift quota `shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i`
   for a state `model` reached within `2 * iterationLimit I V (1 / 2 ^ k) + 1` stages fits in
   `< 2 ^ w`. -/
theorem concrete_shiftQuota_lt_two_pow_wordSize
    {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (SparseCore.lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec) :
    ∃ C_q : ℕ, ∀ (allocationCoefficient allocationDegree : ℕ),
      C_q ≤ allocationCoefficient →
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let threshold := concreteEdgeThresholdWithLast W
        let A := concreteQualityBudgetWithLast W
        let Ck := concreteQualityLinearCoeff threshold A
        let deg := forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent threshold A I.m
        let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
        let cfg := concreteCirculationCfgWithLast W J
        ipmQualityParameterWordBits I.m V k ≤ w →
        ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ < 2 ^ w ∧
        (∀ i ≤ cfg.P.d, shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (i + 1) < 2 ^ w) ∧
        (∀ (D : DynamicInstance) (η : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (κ : ℝ),
          T ≤ 2 * IPM.iterationLimit I V (1 / (2 : ℝ) ^ k) + 1 →
          let model := minRatioFailState (Ordered.algorithm2_dsWith cfg κ) D η op T
          ∀ i ≤ cfg.P.d,
            shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i < 2 ^ w) := by
  obtain ⟨C_q, hCq⟩ := concrete_shiftQuotaWord_ipm_poly W
  obtain ⟨a, ha⟩ := concrete_shiftQuotaBasePow_poly W
  refine ⟨max C_q a, fun allocCoeff allocDeg hle source J hJn hJm hCap hw => ?_⟩
  dsimp only
  set threshold := concreteEdgeThresholdWithLast W
  set A := concreteQualityBudgetWithLast W
  set Ck := concreteQualityLinearCoeff threshold A
  set deg := forestProgramsScratchDegree allocCoeff allocDeg Ck
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent threshold A I.m
  set cfg := concreteCirculationCfgWithLast W J
  have hdeg7 := forestProgramsScratchDegree_covers_shiftQuota allocCoeff allocDeg Ck (max C_q a) hle
  obtain ⟨hbase, hceil⟩ := ha J hJn hJm hCap
  have hbase7 : ∀ i ≤ cfg.P.d,
      shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (i + 1) ≤ max C_q a * (J.m + 2) ^ 7 := fun i hi =>
    (hbase i hi).trans (Nat.mul_le_mul (le_max_right _ _) (Nat.pow_le_pow_right (by omega) (by decide)))
  have hceil7 : ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ ≤ max C_q a * (J.m + 2) ^ 7 :=
    hceil.trans (Nat.mul_le_mul (le_max_right _ _) (Nat.pow_le_pow_right (by omega) (by decide)))
  refine ⟨lt_two_pow_wordSize_of_poly_and_hw source J hJm (by decide) hw hceil7 hdeg7,
    fun i hi => lt_two_pow_wordSize_of_poly_and_hw source J hJm (by decide) hw (hbase7 i hi) hdeg7,
    fun D η op T κ hT i hi => ?_⟩
  have hq := (hCq J hJn hJm hCap D η op T κ hT).1 i hi
  exact lt_two_pow_wordSize_of_poly_and_hw source J hJm (by decide) hw
    (hq.trans (Nat.mul_le_mul_right _ (le_max_left _ _))) hdeg7

/-- The step budget `shiftQuotaWriterBudget (chosenD (23 / 24) M₀) M₀` is `O(log (M₀ + 2))`
(in fact at most `200 * (Nat.clog 2 (M₀ + 2) + 1)`). -/
theorem shiftQuotaWriterBudget_le_log {M₀ : ℕ} (hM : 1 ≤ M₀) :
    shiftQuotaWriterBudget (chosenD (23 / 24) M₀) M₀ ≤ 200 * (Nat.clog 2 (M₀ + 2) + 1) := by
  have hL1 := one_le_log_add_two' hM
  obtain ⟨_, _, hdHi⟩ := chosenD_bounds (β := 23 / 24) (by norm_num) hM
  rw [show ((1 : ℝ) - 23 / 24) / 2 = 1 / 48 by norm_num] at hdHi
  have hrpow : Real.log ((M₀ : ℝ) + 2) ^ (1 / 48 : ℝ) ≤ Real.log ((M₀ : ℝ) + 2) := by
    calc Real.log ((M₀ : ℝ) + 2) ^ (1 / 48 : ℝ)
        ≤ Real.log ((M₀ : ℝ) + 2) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = Real.log ((M₀ : ℝ) + 2) := Real.rpow_one _
  have hlogLeClog : Real.log ((M₀ : ℝ) + 2) ≤ (Nat.clog 2 (M₀ + 2) : ℝ) := by
    have hpow : ((M₀ + 2 : ℕ) : ℝ) ≤ ((2 ^ Nat.clog 2 (M₀ + 2) : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_pow_clog (by decide) (M₀ + 2)
    push_cast at hpow
    have h1 := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow] at h1
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.clog 2 (M₀ + 2))]
  have hdLe : chosenD (23 / 24) M₀ ≤ 2 * Nat.clog 2 (M₀ + 2) := by
    have hreal : (chosenD (23 / 24) M₀ : ℝ) ≤ ((2 * Nat.clog 2 (M₀ + 2) : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast hreal
  have hclogMono : Nat.clog 2 (M₀ + 1) ≤ Nat.clog 2 (M₀ + 2) :=
    Nat.clog_mono_right 2 (by omega)
  unfold shiftQuotaWriterBudget
  omega

end MinCostFlow.MinRatio
