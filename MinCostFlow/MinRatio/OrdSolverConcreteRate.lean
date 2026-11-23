module

public import MinCostFlow.MinRatio.ShiftForwardWeightBound
public import MinCostFlow.MinRatio.OrdSolverToolCredit
public import MinCostFlow.Final.ConcreteChainModelWithLast
import Mathlib.Tactic

/-!
# Concrete `m^{o(1)}` rate bounds for `fwdWeight` and the dual tool/tree credits

1. **Concrete `fwdWeight` rate bound (`concrete_fwdWeight_le_timeFactor`)**:
   Discharges the `fwdGamma` premise (`1 ≤ Γ ≤ exp(C_γ L^{23/24} log(L + 2))`) of
   `fwdWeight_le_timeFactor_edges` (`ShiftForwardWeightBound.lean`) for the concrete configuration
   `Final.concreteCirculationCfgWithLast W J`, using `Final.concreteCirculationCfgWithLast_gamma_r`
   and `Final.concreteCirculation_bounds_of`.

2. **Subpolynomial `m^{o(1)}` bounds for the dual-credit deposit and initial cap**:
   - `capDeposit_le` and `capDeposit_le_timeFactor`: by the exact exponent cancellation
     `k ^ (i - i₀) * powTerm P i ≤ 2 ^ (i - i₀) * powTerm P i₀` and
     `k ^ (i₀ + 1) * powTerm P i₀ ≤ 2 ^ (i₀ + 1) * M₀ * M₀ ^ (1 / d)`, each `capDeposit cfg i₀`
     has the same `exp(O(logShape M₀))` bound as `shiftDeposit`.
   - `capFwdWeight_le_timeFactor` and `concrete_capFwdWeight_le_timeFactor`: the per-update dual-credit
     weight `capFwdWeight cfg (fwdGamma cfg) 0` is at most `C * alg2TimeFactor E (47 / 48) I.m`.
   - `initRebuildCap_le_M0_timeFactor` and `concrete_initRebuildCap_le_timeFactor`: the initial
     unit cap `chainRebuildCap cfg 1 (fun _ => 0)` is at most
     `M₀ * C * alg2TimeFactor E (47 / 48) I.m`, so its per-edge `Init` cost is `m^{o(1)}`.
-/

public section

namespace MinCostFlow.MinRatio

open Chain IPM IPM.Machine Scaling Final SparseCore

/-! ## 1. Concrete `fwdWeight` bound (`fwdGamma` discharged) -/

/-- **Concrete `fwdWeight` is `m^{o(1)}`**: for every concrete chain witness `W`, there are
constants `C, E` (independent of `J`) such that on every valid circulation `J`,
`fwdWeight cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) 0 ≤
C * alg2TimeFactor E (47 / 48) (solverConnectedAugmented J).m`. -/
theorem concrete_fwdWeight_le_timeFactor
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) :
    ∃ C E : ℝ, 0 ≤ E ∧ ∀ (J : Circulation),
      J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
      let cfg := concreteCirculationCfgWithLast W J
      (fwdWeight cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) 0 : ℝ) ≤
        C * alg2TimeFactor E (47 / 48) (solverConnectedAugmented J).m := by
  have hCγ : 0 ≤ W.C_γ + 1 := by linarith [W.hCγ]
  obtain ⟨C, E, hE, hbound⟩ := fwdWeight_le_timeFactor_edges
    (C_ψ := 1) (C_N := 4) (C_γ := W.C_γ + 1) zero_le_one (by norm_num) hCγ
    (concreteEdgeThresholdWithLast W)
  refine ⟨C, E, hE, fun J hJn hJm hCap => ?_⟩
  let I := solverConnectedAugmented J
  let cfg := concreteCirculationCfgWithLast W J
  obtain ⟨_, hN₀, hPsi, _, _⟩ := concreteCirculation_bounds_of
    (le_max_left W.M_thresh _) (le_max_right W.M_thresh _)
    (concreteEdgeThresholdWithLast_ge_two W) J hJn hJm hCap
  obtain ⟨hΓ1, hΓ⟩ := concreteCirculationCfgWithLast_gamma_r W J hJn hJm hCap
  have hM0Eq : cfg.P.M₀ = max I.m (concreteEdgeThresholdWithLast W) := rfl
  have hdEq : cfg.P.d = chosenD (23 / 24) cfg.P.M₀ := rfl
  have hN : Real.log ((cfg.N₀ : ℝ) + 2) ≤ 4 * Real.log ((cfg.P.M₀ : ℝ) + 2) := by
    have : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ 4 * Real.log ((cfg.P.M₀ : ℝ) + 2) := hN₀
    linarith
  exact hbound cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) I.m
    hM0Eq cfg.P.hM₀ (alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀) hdEq hN hPsi hΓ1 hΓ

/-! ## 2. Exact exponent cancellation for `capDeposit` and initial `chainRebuildCap` -/

private theorem k_pow_mul_powTerm_le (P : ChainParams) {i₀ i : ℕ} (hle : i₀ ≤ i) :
    (P.k : ℝ) ^ (i - i₀) * powTerm P i ≤ (2 : ℝ) ^ (i - i₀) * powTerm P i₀ := by
  have hM : (0 : ℝ) < P.M₀ := by exact_mod_cast P.hM₀
  have hd : (0 : ℝ) < P.d := by exact_mod_cast P.hd
  have hk0 : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  have hkp : (P.k : ℝ) ^ (i - i₀) ≤ (2 : ℝ) ^ (i - i₀) * (P.M₀ : ℝ) ^ (((i - i₀ : ℕ) : ℝ) / (P.d : ℝ)) := by
    calc (P.k : ℝ) ^ (i - i₀)
        ≤ (2 * (P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ (i - i₀) :=
          pow_le_pow_left₀ hk0 P.hk_upper (i - i₀)
      _ = (2 : ℝ) ^ (i - i₀) * ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ (i - i₀) := mul_pow _ _ _
      _ = (2 : ℝ) ^ (i - i₀) * (P.M₀ : ℝ) ^ (1 / (P.d : ℝ) * ((i - i₀ : ℕ) : ℝ)) := by
          rw [← Real.rpow_natCast ((P.M₀ : ℝ) ^ _), ← Real.rpow_mul hM.le]
      _ = (2 : ℝ) ^ (i - i₀) * (P.M₀ : ℝ) ^ (((i - i₀ : ℕ) : ℝ) / (P.d : ℝ)) := by
          congr 2; ring
  have hpt : (P.M₀ : ℝ) ^ (((i - i₀ : ℕ) : ℝ) / (P.d : ℝ)) * powTerm P i = powTerm P i₀ := by
    unfold powTerm
    rw [← Real.rpow_add hM]
    congr 1
    have hsub : ((i - i₀ : ℕ) : ℝ) = (i : ℝ) - (i₀ : ℝ) := Nat.cast_sub hle
    rw [hsub]
    field_simp
    ring
  have hptNN : 0 ≤ powTerm P i := by unfold powTerm; positivity
  calc (P.k : ℝ) ^ (i - i₀) * powTerm P i
      ≤ (2 : ℝ) ^ (i - i₀) * (P.M₀ : ℝ) ^ (((i - i₀ : ℕ) : ℝ) / (P.d : ℝ)) * powTerm P i :=
        mul_le_mul_of_nonneg_right hkp hptNN
    _ = (2 : ℝ) ^ (i - i₀) * ((P.M₀ : ℝ) ^ (((i - i₀ : ℕ) : ℝ) / (P.d : ℝ)) * powTerm P i) := by ring
    _ = (2 : ℝ) ^ (i - i₀) * powTerm P i₀ := by rw [hpt]

private theorem k_pow_succ_mul_powTerm_le (P : ChainParams) (i₀ : ℕ) :
    (P.k : ℝ) ^ (i₀ + 1) * powTerm P i₀ ≤
      (2 : ℝ) ^ (i₀ + 1) * (P.M₀ : ℝ) * (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) := by
  have h1 := k_pow_mul_powTerm_le P (Nat.zero_le i₀)
  simp only [Nat.sub_zero, powTerm_zero] at h1
  have hptNN : 0 ≤ powTerm P i₀ := by unfold powTerm; positivity
  have hk0 : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  calc (P.k : ℝ) ^ (i₀ + 1) * powTerm P i₀
      = (P.k : ℝ) * ((P.k : ℝ) ^ i₀ * powTerm P i₀) := by rw [pow_succ']; ring
    _ ≤ (2 * (P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) * ((2 : ℝ) ^ i₀ * (P.M₀ : ℝ)) :=
        mul_le_mul P.hk_upper h1 (mul_nonneg (pow_nonneg hk0 _) hptNN) (by positivity)
    _ = (2 : ℝ) ^ (i₀ + 1) * (P.M₀ : ℝ) * (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) := by
        rw [pow_succ']; ring

private theorem shiftQuotaBase_cast_eq (cfg : Alg2Config) :
    (shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k : ℝ) =
      10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ) := by
  unfold shiftQuotaBase
  push_cast
  rw [← alg2PsiGame_eq_natCast]

private theorem rebuildCapUnitGain_le (cfg : Alg2Config) {i₀ : ℕ} (hi₀ : i₀ ≤ cfg.P.d) :
    (rebuildCapUnitGain cfg i₀ : ℝ) ≤
      2 * ((cfg.P.d : ℝ) + 2) * (10 * alg2PsiGame cfg.Ψ cfg.P.M₀) ^ (cfg.P.d + 1) *
        (2 : ℝ) ^ (cfg.P.d + 1) * (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) * powTerm cfg.P i₀ := by
  set psi := alg2PsiGame cfg.Ψ cfg.P.M₀
  have hpsi : 1 ≤ psi := alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀
  have hM1 : (1 : ℝ) ≤ cfg.P.M₀ := by exact_mod_cast cfg.P.hM₀
  have hd : (0 : ℝ) < cfg.P.d := by exact_mod_cast cfg.P.hd
  have hroot1 : (1 : ℝ) ≤ (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) := Real.one_le_rpow hM1 (by positivity)
  have hpt0 : 1 ≤ powTerm cfg.P i₀ := one_le_powTerm cfg.P hi₀
  have hceil_le : ∀ i ≤ cfg.P.d, (⌈powTerm cfg.P i⌉₊ : ℝ) ≤ 2 * powTerm cfg.P i := fun i hi => by
    have h1 := one_le_powTerm cfg.P hi
    have h2 : (⌈powTerm cfg.P i⌉₊ : ℝ) < powTerm cfg.P i + 1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hterm_le : ∀ i ∈ Finset.range (cfg.P.d + 1),
      ((if i₀ ≤ i then
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (i + 1 - i₀) * ⌈powTerm cfg.P i⌉₊ else 0 : ℕ) : ℝ) ≤
      2 * (10 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 1) *
        (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) * powTerm cfg.P i₀ := by
    intro i hi
    have hiLe : i ≤ cfg.P.d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    split_ifs with hle
    · push_cast
      rw [shiftQuotaBase_cast_eq]
      have hexp : i + 1 - i₀ = (i - i₀) + 1 := by omega
      rw [hexp, mul_pow, pow_succ (cfg.P.k : ℝ)]
      have h1 := k_pow_mul_powTerm_le cfg.P hle
      have h2 := hceil_le i hiLe
      have h3 : (10 * psi) ^ (i - i₀ + 1) ≤ (10 * psi) ^ (cfg.P.d + 1) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      have h4 : (2 : ℝ) ^ (i - i₀) * 2 ≤ (2 : ℝ) ^ (cfg.P.d + 1) := by
        rw [← pow_succ]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hk_prod : (cfg.P.k : ℝ) ^ (i - i₀) * (cfg.P.k : ℝ) * (⌈powTerm cfg.P i⌉₊ : ℝ) ≤
          2 * (2 : ℝ) ^ (cfg.P.d + 1) * (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) * powTerm cfg.P i₀ := by
        calc (cfg.P.k : ℝ) ^ (i - i₀) * (cfg.P.k : ℝ) * (⌈powTerm cfg.P i⌉₊ : ℝ)
            ≤ (cfg.P.k : ℝ) ^ (i - i₀) * (cfg.P.k : ℝ) * (2 * powTerm cfg.P i) := by
              gcongr
          _ = 2 * (cfg.P.k : ℝ) * ((cfg.P.k : ℝ) ^ (i - i₀) * powTerm cfg.P i) := by ring
          _ ≤ 2 * (2 * (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ))) * ((2 : ℝ) ^ (i - i₀) * powTerm cfg.P i₀) := by
              have hnn1 : 0 ≤ (cfg.P.k : ℝ) ^ (i - i₀) * powTerm cfg.P i := by
                unfold powTerm; positivity
              have hnn2 : 0 ≤ 2 * (cfg.P.k : ℝ) := by positivity
              have ha := mul_le_mul_of_nonneg_left cfg.P.hk_upper (by norm_num : (0 : ℝ) ≤ 2)
              exact mul_le_mul ha h1 hnn1 (by positivity)
          _ = 2 * ((2 : ℝ) ^ (i - i₀) * 2) * (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) * powTerm cfg.P i₀ := by
              ring
          _ ≤ 2 * (2 : ℝ) ^ (cfg.P.d + 1) * (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) * powTerm cfg.P i₀ := by
              have hnn : 0 ≤ (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) * powTerm cfg.P i₀ := by
                unfold powTerm; positivity
              nlinarith
      calc (10 * psi) ^ (i - i₀ + 1) * ((cfg.P.k : ℝ) ^ (i - i₀) * (cfg.P.k : ℝ)) *
              (⌈powTerm cfg.P i⌉₊ : ℝ)
          = (10 * psi) ^ (i - i₀ + 1) *
              ((cfg.P.k : ℝ) ^ (i - i₀) * (cfg.P.k : ℝ) * (⌈powTerm cfg.P i⌉₊ : ℝ)) := by ring
        _ ≤ (10 * psi) ^ (cfg.P.d + 1) *
              (2 * (2 : ℝ) ^ (cfg.P.d + 1) * (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) * powTerm cfg.P i₀) := by
            refine mul_le_mul h3 hk_prod (by positivity) (by positivity)
        _ = _ := by ring
    · simp only [Nat.cast_zero]
      unfold powTerm; positivity
  unfold rebuildCapUnitGain
  rw [ite_eq_left hi₀]
  push_cast
  have hsum := Finset.sum_le_sum hterm_le
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hsum
  have hlead : (⌈powTerm cfg.P i₀⌉₊ : ℝ) ≤
      2 * (10 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 1) *
        (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) * powTerm cfg.P i₀ := by
    have h1 := hceil_le i₀ hi₀
    have h10 : (1 : ℝ) ≤ (10 * psi) ^ (cfg.P.d + 1) := one_le_pow₀ (by linarith)
    have h2p : (1 : ℝ) ≤ (2 : ℝ) ^ (cfg.P.d + 1) := one_le_pow₀ (by norm_num)
    have hprod : 1 ≤ (10 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 1) *
        (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h10 h2p) hroot1
    nlinarith
  push_cast at hsum
  calc _ ≤ 2 * (10 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 1) *
          (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) * powTerm cfg.P i₀ +
        ((cfg.P.d : ℝ) + 1) * (2 * (10 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 1) *
          (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) * powTerm cfg.P i₀) :=
        add_le_add hlead hsum
    _ = 2 * ((cfg.P.d : ℝ) + 2) * (10 * psi) ^ (cfg.P.d + 1) *
          (2 : ℝ) ^ (cfg.P.d + 1) * (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) * powTerm cfg.P i₀ := by ring

private theorem capDeposit_mul_le (cfg : Alg2Config) (i : ℕ) :
    capDeposit cfg i * cfg.P.M₀ ≤
      rebuildCapUnitGain cfg i * (cfg.P.k ^ (i + 1) * Nat.clog 2 (cfg.N₀ + 2) ^ 2) + cfg.P.M₀ := by
  set K := cfg.P.k ^ (i + 1) * Nat.clog 2 (cfg.N₀ + 2) ^ 2
  set Q := rebuildCapUnitGain cfg i
  have hc : 1 ≤ Nat.clog 2 (cfg.N₀ + 2) := Nat.succ_le_of_lt (Nat.clog_pos (by omega) (by omega))
  have hKpos : 0 < K := Nat.mul_pos (Nat.pow_pos cfg.P.hk) (Nat.pow_pos hc)
  have ht : intRebuildThreshold cfg.P cfg.N₀ i = cfg.P.M₀ / K := rfl
  set t := cfg.P.M₀ / K
  unfold capDeposit
  rw [ht]
  set D := (Q + t) / (t + 1)
  have h1 : cfg.P.M₀ < (t + 1) * K := by
    have := Nat.lt_div_mul_add (a := cfg.P.M₀) hKpos
    rw [Nat.add_mul, one_mul]; exact this
  have h2 : D * (t + 1) ≤ Q + t := Nat.div_mul_le_self _ _
  have h3 : t * K ≤ cfg.P.M₀ := Nat.div_mul_le_self _ _
  calc D * cfg.P.M₀ ≤ D * ((t + 1) * K) := Nat.mul_le_mul_left _ h1.le
    _ = D * (t + 1) * K := by ring
    _ ≤ (Q + t) * K := Nat.mul_le_mul_right _ h2
    _ = Q * K + t * K := by ring
    _ ≤ Q * K + cfg.P.M₀ := Nat.add_le_add_left h3 _

/-- **Subpolynomial bound on `capDeposit`**: under the paper's parameter relations, each
`capDeposit cfg i₀` (`i₀ ≤ d`) is at most `C * alg2TimeFactor E (47 / 48) cfg.P.M₀`. -/
theorem capDeposit_le_timeFactor (cfg : Alg2Config) {C_ψ C_N : ℝ}
    (hCψ : 0 ≤ C_ψ) (hCN : 0 ≤ C_N) (hd : cfg.P.d = chosenD (23 / 24) cfg.P.M₀)
    (hN : Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2))
    (hψ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤ Real.exp (C_ψ * Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    {i₀ : ℕ} (hi₀ : i₀ ≤ cfg.P.d) :
    (capDeposit cfg i₀ : ℝ) ≤
      (4 * (1 + 2 * C_N) ^ 2 + 1) * alg2TimeFactor (28 + 3 * C_ψ) (47 / 48) cfg.P.M₀ := by
  set psi := alg2PsiGame cfg.Ψ cfg.P.M₀
  have hpsi : 1 ≤ psi := alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀
  have hM : (0 : ℝ) < cfg.P.M₀ := by exact_mod_cast cfg.P.hM₀
  have hmulR : (capDeposit cfg i₀ : ℝ) * (cfg.P.M₀ : ℝ) ≤
      (rebuildCapUnitGain cfg i₀ : ℝ) *
        ((cfg.P.k : ℝ) ^ (i₀ + 1) * (Nat.clog 2 (cfg.N₀ + 2) : ℝ) ^ 2) + (cfg.P.M₀ : ℝ) := by
    exact_mod_cast capDeposit_mul_le cfg i₀
  have hgain := rebuildCapUnitGain_le cfg hi₀
  have hkpt := k_pow_succ_mul_powTerm_le cfg.P i₀
  have h2root : (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) * (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) =
      (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) := by
    rw [← Real.rpow_add hM]; congr 1; ring
  have h2pow : (2 : ℝ) ^ (i₀ + 1) ≤ (2 : ℝ) ^ (cfg.P.d + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h10_11 : (10 * psi) ^ (cfg.P.d + 1) ≤ (11 * psi) ^ (cfg.P.d + 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hd2 : ((cfg.P.d : ℝ) + 2) ≤ 2 * ((cfg.P.d : ℝ) + 1) := by linarith
  have hprod : (rebuildCapUnitGain cfg i₀ : ℝ) *
        ((cfg.P.k : ℝ) ^ (i₀ + 1) * (Nat.clog 2 (cfg.N₀ + 2) : ℝ) ^ 2) ≤
      (cfg.P.M₀ : ℝ) * (4 * (2 : ℝ) ^ (cfg.P.d + 1) *
        (((cfg.P.d : ℝ) + 1) * (11 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 2) *
          (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) * (Nat.clog 2 (cfg.N₀ + 2) : ℝ) ^ 2)) := by
    have hnn1 : 0 ≤ (cfg.P.k : ℝ) ^ (i₀ + 1) * (Nat.clog 2 (cfg.N₀ + 2) : ℝ) ^ 2 := by positivity
    calc (rebuildCapUnitGain cfg i₀ : ℝ) *
          ((cfg.P.k : ℝ) ^ (i₀ + 1) * (Nat.clog 2 (cfg.N₀ + 2) : ℝ) ^ 2)
        ≤ (2 * ((cfg.P.d : ℝ) + 2) * (10 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 1) *
            (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) * powTerm cfg.P i₀) *
          ((cfg.P.k : ℝ) ^ (i₀ + 1) * (Nat.clog 2 (cfg.N₀ + 2) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hgain hnn1
      _ = 2 * ((cfg.P.d : ℝ) + 2) * (10 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 1) *
            (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) * ((cfg.P.k : ℝ) ^ (i₀ + 1) * powTerm cfg.P i₀) *
            (Nat.clog 2 (cfg.N₀ + 2) : ℝ) ^ 2 := by ring
      _ ≤ 2 * ((cfg.P.d : ℝ) + 2) * (10 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 1) *
            (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) *
            ((2 : ℝ) ^ (i₀ + 1) * (cfg.P.M₀ : ℝ) * (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ))) *
            (Nat.clog 2 (cfg.N₀ + 2) : ℝ) ^ 2 := by gcongr
      _ = (cfg.P.M₀ : ℝ) * (2 * ((cfg.P.d : ℝ) + 2) * (10 * psi) ^ (cfg.P.d + 1) *
            (2 : ℝ) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (i₀ + 1) *
            ((cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) * (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ))) *
            (Nat.clog 2 (cfg.N₀ + 2) : ℝ) ^ 2) := by ring
      _ ≤ (cfg.P.M₀ : ℝ) * (2 * (2 * ((cfg.P.d : ℝ) + 1)) * (11 * psi) ^ (cfg.P.d + 1) *
            (2 : ℝ) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 2) *
            (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) * (Nat.clog 2 (cfg.N₀ + 2) : ℝ) ^ 2) := by
            rw [h2root]
            have h2i : (2 : ℝ) ^ (i₀ + 1) ≤ (2 : ℝ) ^ (cfg.P.d + 2) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
            gcongr
      _ = _ := by ring
  have hdiv : (capDeposit cfg i₀ : ℝ) ≤
      4 * (2 : ℝ) ^ (cfg.P.d + 1) *
        (((cfg.P.d : ℝ) + 1) * (11 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 2) *
          (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) * (Nat.clog 2 (cfg.N₀ + 2) : ℝ) ^ 2) + 1 := by
    have h1 : (capDeposit cfg i₀ : ℝ) * (cfg.P.M₀ : ℝ) ≤
        (4 * (2 : ℝ) ^ (cfg.P.d + 1) *
          (((cfg.P.d : ℝ) + 1) * (11 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 2) *
            (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) * (Nat.clog 2 (cfg.N₀ + 2) : ℝ) ^ 2) + 1) *
        (cfg.P.M₀ : ℝ) := by linarith
    exact le_of_mul_le_mul_right h1 hM
  have hBase := shiftDepositBound_le_exp cfg.P cfg.N₀ hpsi hCN hd hN hψ
  have h2exp : (2 : ℝ) ^ (cfg.P.d + 1) ≤ Real.exp (9 * logShape cfg.P.M₀) := by
    have h11 := eleven_psi_pow_le_exp cfg.P.hM₀ (psi := 1) (C_ψ := 0) le_rfl hd (by simp)
    have h2_11 : (2 : ℝ) ^ (cfg.P.d + 1) ≤ (11 * (1 : ℝ)) ^ (cfg.P.d + 1) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    calc (2 : ℝ) ^ (cfg.P.d + 1) ≤ (11 * (1 : ℝ)) ^ (cfg.P.d + 1) := h2_11
      _ ≤ Real.exp (3 * (3 + 0) * logShape cfg.P.M₀) := h11
      _ = Real.exp (9 * logShape cfg.P.M₀) := by ring_nf
  have hT1 : 1 ≤ alg2TimeFactor (28 + 3 * C_ψ) (47 / 48) cfg.P.M₀ := by
    rw [alg2TimeFactor_eq_exp_logShape]
    have hA1 := one_le_logShape cfg.P.hM₀
    exact Real.one_le_exp (by nlinarith)
  calc (capDeposit cfg i₀ : ℝ)
      ≤ 4 * (2 : ℝ) ^ (cfg.P.d + 1) *
          (((cfg.P.d : ℝ) + 1) * (11 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 2) *
            (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) * (Nat.clog 2 (cfg.N₀ + 2) : ℝ) ^ 2) + 1 := hdiv
    _ ≤ 4 * Real.exp (9 * logShape cfg.P.M₀) *
          ((1 + 2 * C_N) ^ 2 * Real.exp ((19 + 3 * C_ψ) * logShape cfg.P.M₀)) + 1 := by
        gcongr
    _ = 4 * (1 + 2 * C_N) ^ 2 * alg2TimeFactor (28 + 3 * C_ψ) (47 / 48) cfg.P.M₀ + 1 := by
        rw [alg2TimeFactor_eq_exp_logShape,
          show (28 + 3 * C_ψ) * logShape cfg.P.M₀ =
            9 * logShape cfg.P.M₀ + (19 + 3 * C_ψ) * logShape cfg.P.M₀ by ring, Real.exp_add]
        ring
    _ ≤ (4 * (1 + 2 * C_N) ^ 2 + 1) * alg2TimeFactor (28 + 3 * C_ψ) (47 / 48) cfg.P.M₀ := by
        linarith

/-- **Subpolynomial bound on `capFwdWeight cfg Γ 0`**: the dual-credit update charge per unit
batch length is `m^{o(1)}`. -/
theorem capFwdWeight_le_timeFactor (cfg : Alg2Config) {C_ψ C_N C_γ : ℝ} {Γ : ℕ}
    (hCψ : 0 ≤ C_ψ) (hCN : 0 ≤ C_N) (hd : cfg.P.d = chosenD (23 / 24) cfg.P.M₀)
    (hN : Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2))
    (hψ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤ Real.exp (C_ψ * Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΓ1 : 1 ≤ Γ) (hΓ : (Γ : ℝ) ≤ Real.exp (C_γ * Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2))) :
    (capFwdWeight cfg Γ 0 : ℝ) ≤
      (4 * (1 + 2 * C_N) ^ 2 + 1) *
        alg2TimeFactor (28 + 3 * C_ψ + 3 * (3 + C_γ)) (47 / 48) cfg.P.M₀ := by
  set K : ℝ := 4 * (1 + 2 * C_N) ^ 2 + 1 with hK
  set S : ℝ := K * alg2TimeFactor (28 + 3 * C_ψ) (47 / 48) cfg.P.M₀ with hS
  have hKpos : 0 < K := by positivity
  have hΓ1' : (1 : ℝ) ≤ Γ := by exact_mod_cast hΓ1
  have hsum : (capFwdWeight cfg Γ 0 : ℝ) ≤ (cfg.P.d : ℝ) * ((Γ : ℝ) ^ cfg.P.d * S) := by
    unfold capFwdWeight
    push_cast
    calc ∑ j ∈ Finset.Ico 0 cfg.P.d, (Γ : ℝ) ^ (j - 0) * (capDeposit cfg j : ℝ)
        ≤ ∑ _j ∈ Finset.Ico 0 cfg.P.d, (Γ : ℝ) ^ cfg.P.d * S := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := (Finset.mem_Ico.mp hj).2
          have h1 := capDeposit_le_timeFactor cfg hCψ hCN hd hN hψ hj'.le
          have h2 : (Γ : ℝ) ^ (j - 0) ≤ (Γ : ℝ) ^ cfg.P.d :=
            pow_le_pow_right₀ hΓ1' (by omega)
          exact mul_le_mul h2 h1 (Nat.cast_nonneg _) (by positivity)
      _ = (cfg.P.d : ℝ) * ((Γ : ℝ) ^ cfg.P.d * S) := by simp
  have hd11 : (cfg.P.d : ℝ) ≤ 11 ^ (cfg.P.d + 1) := by
    have h : cfg.P.d ≤ 11 ^ (cfg.P.d + 1) :=
      calc cfg.P.d ≤ 2 ^ cfg.P.d := Nat.lt_two_pow_self.le
        _ ≤ 11 ^ cfg.P.d := Nat.pow_le_pow_left (by norm_num) _
        _ ≤ 11 ^ (cfg.P.d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast h
  have hpow : (cfg.P.d : ℝ) * (Γ : ℝ) ^ cfg.P.d ≤ (11 * (Γ : ℝ)) ^ (cfg.P.d + 1) := by
    rw [mul_pow]
    exact mul_le_mul hd11 (pow_le_pow_right₀ hΓ1' (by omega)) (by positivity) (by positivity)
  have h11 := eleven_psi_pow_le_exp cfg.P.hM₀ hΓ1' hd hΓ
  have hSpos : 0 ≤ S := mul_nonneg hKpos.le (by
    rw [alg2TimeFactor_eq_exp_logShape]; exact (Real.exp_pos _).le)
  calc (capFwdWeight cfg Γ 0 : ℝ)
      ≤ ((cfg.P.d : ℝ) * (Γ : ℝ) ^ cfg.P.d) * S := by rw [mul_assoc]; exact hsum
    _ ≤ Real.exp (3 * (3 + C_γ) * logShape cfg.P.M₀) * S :=
        mul_le_mul_of_nonneg_right (hpow.trans h11) hSpos
    _ = K * alg2TimeFactor (28 + 3 * C_ψ + 3 * (3 + C_γ)) (47 / 48) cfg.P.M₀ := by
        rw [hS, hK, alg2TimeFactor_eq_exp_logShape, alg2TimeFactor_eq_exp_logShape,
          show (28 + 3 * C_ψ + 3 * (3 + C_γ)) * logShape cfg.P.M₀ =
            (28 + 3 * C_ψ) * logShape cfg.P.M₀ + 3 * (3 + C_γ) * logShape cfg.P.M₀ by ring,
          Real.exp_add]
        ring

/-- **Concrete `capFwdWeight` is `m^{o(1)}`**: on every valid circulation `J`, the dual-credit
update weight `capFwdWeight cfg (fwdGamma cfg) 0` is at most
`C * alg2TimeFactor E (47 / 48) (solverConnectedAugmented J).m`. -/
theorem concrete_capFwdWeight_le_timeFactor
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) :
    ∃ C E : ℝ, 0 ≤ E ∧ ∀ (J : Circulation),
      J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
      let cfg := concreteCirculationCfgWithLast W J
      (capFwdWeight cfg (fwdGamma cfg) 0 : ℝ) ≤
        C * alg2TimeFactor E (47 / 48) (solverConnectedAugmented J).m := by
  let E : ℝ := 28 + 3 * 1 + 3 * (3 + (W.C_γ + 1))
  have hE : 0 ≤ E := by dsimp only [E]; linarith [W.hCγ]
  let T := concreteEdgeThresholdWithLast W
  refine ⟨(4 * (1 + 2 * (4 : ℝ)) ^ 2 + 1) * alg2TimeFactor E (47 / 48) T, E, hE,
    fun J hJn hJm hCap => ?_⟩
  let I := solverConnectedAugmented J
  let cfg := concreteCirculationCfgWithLast W J
  obtain ⟨_, hN₀, hPsi, _, _⟩ := concreteCirculation_bounds_of
    (le_max_left W.M_thresh _) (le_max_right W.M_thresh _)
    (concreteEdgeThresholdWithLast_ge_two W) J hJn hJm hCap
  obtain ⟨hΓ1, hΓ⟩ := concreteCirculationCfgWithLast_gamma_r W J hJn hJm hCap
  have hM0Eq : cfg.P.M₀ = max I.m T := rfl
  have hdEq : cfg.P.d = chosenD (23 / 24) cfg.P.M₀ := rfl
  have hN : Real.log ((cfg.N₀ : ℝ) + 2) ≤ 4 * Real.log ((cfg.P.M₀ : ℝ) + 2) := by
    have : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ 4 * Real.log ((cfg.P.M₀ : ℝ) + 2) := hN₀
    linarith
  have h1 := capFwdWeight_le_timeFactor cfg (C_ψ := 1) (C_N := 4) (C_γ := W.C_γ + 1)
    zero_le_one (by norm_num) hdEq hN hPsi hΓ1 hΓ
  rw [hM0Eq] at h1
  have h2 := alg2TimeFactor_max_le hE I.m T
  have hK : (0 : ℝ) ≤ 4 * (1 + 2 * (4 : ℝ)) ^ 2 + 1 := by positivity
  calc (capFwdWeight cfg (fwdGamma cfg) 0 : ℝ)
      ≤ (4 * (1 + 2 * (4 : ℝ)) ^ 2 + 1) * alg2TimeFactor E (47 / 48) (max I.m T) := h1
    _ ≤ (4 * (1 + 2 * (4 : ℝ)) ^ 2 + 1) *
          (alg2TimeFactor E (47 / 48) T * alg2TimeFactor E (47 / 48) I.m) :=
        mul_le_mul_of_nonneg_left h2 hK
    _ = _ := by ring

/-- **Initial `chainRebuildCap` is `M₀ · m^{o(1)}`**: the unit initial cap at `rc = 0` satisfies
`chainRebuildCap cfg 1 (fun _ => 0) ≤ M₀ * (19 * alg2TimeFactor (19 + 3 * C_ψ) (47 / 48) M₀)`. -/
theorem initRebuildCap_le_M0_timeFactor (cfg : Alg2Config) {C_ψ : ℝ}
    (hCψ : 0 ≤ C_ψ) (hd : cfg.P.d = chosenD (23 / 24) cfg.P.M₀)
    (hψ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤ Real.exp (C_ψ * Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2))) :
    (chainRebuildCap cfg 1 (fun _ => 0) : ℝ) ≤
      (cfg.P.M₀ : ℝ) * (19 * alg2TimeFactor (19 + 3 * C_ψ) (47 / 48) cfg.P.M₀) := by
  set psi := alg2PsiGame cfg.Ψ cfg.P.M₀
  have hpsi : 1 ≤ psi := alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀
  have hM1 : (1 : ℝ) ≤ cfg.P.M₀ := by exact_mod_cast cfg.P.hM₀
  have hM : (0 : ℝ) < cfg.P.M₀ := by linarith
  have hterm : ∀ i ∈ Finset.range (cfg.P.d + 1),
      ((gameShiftBoundNat (shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k) (fun _ => 0) i + 0) *
        ⌈powTerm cfg.P i⌉₊ : ℝ) ≤
      2 * (cfg.P.M₀ : ℝ) * (11 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 2) *
        (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) := by
    intro i hi
    have hiLe : i ≤ cfg.P.d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hgs : gameShiftBoundNat (shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k) (fun _ => 0) i =
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (i + 1) := by
      unfold gameShiftBoundNat; simp
    rw [hgs, add_zero]
    push_cast
    rw [shiftQuotaBase_cast_eq, mul_pow, pow_succ (cfg.P.k : ℝ)]
    have h1 := k_pow_mul_powTerm_le cfg.P (Nat.zero_le i)
    simp only [Nat.sub_zero, powTerm_zero] at h1
    have hpt1 := one_le_powTerm cfg.P hiLe
    have hceil : (⌈powTerm cfg.P i⌉₊ : ℝ) ≤ 2 * powTerm cfg.P i := by
      have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ powTerm cfg.P i); linarith
    have h10 : (10 * psi) ^ (i + 1) ≤ (11 * psi) ^ (cfg.P.d + 1) :=
      (pow_le_pow_left₀ (by linarith) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) (by omega))
    have h2i : (2 : ℝ) ^ i * 2 ≤ (2 : ℝ) ^ (cfg.P.d + 2) := by
      rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hroot : (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) ≤ (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le hM1 ?_
      have hdpos : (0 : ℝ) < cfg.P.d := by exact_mod_cast cfg.P.hd
      exact div_le_div_of_nonneg_right (by norm_num) hdpos.le
    calc (10 * psi) ^ (i + 1) * ((cfg.P.k : ℝ) ^ i * (cfg.P.k : ℝ)) * (⌈powTerm cfg.P i⌉₊ : ℝ)
        ≤ (10 * psi) ^ (i + 1) * ((cfg.P.k : ℝ) ^ i * (cfg.P.k : ℝ)) * (2 * powTerm cfg.P i) := by
          gcongr
      _ = 2 * (10 * psi) ^ (i + 1) * (cfg.P.k : ℝ) * ((cfg.P.k : ℝ) ^ i * powTerm cfg.P i) := by
          ring
      _ ≤ 2 * (10 * psi) ^ (i + 1) * (2 * (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ))) *
            ((2 : ℝ) ^ i * (cfg.P.M₀ : ℝ)) := by
          have hnn : 0 ≤ (cfg.P.k : ℝ) ^ i * powTerm cfg.P i := by unfold powTerm; positivity
          have ha := mul_le_mul_of_nonneg_left cfg.P.hk_upper
            (by positivity : 0 ≤ 2 * (10 * psi) ^ (i + 1))
          exact mul_le_mul ha h1 hnn (by positivity)
      _ = 2 * (cfg.P.M₀ : ℝ) * (10 * psi) ^ (i + 1) * ((2 : ℝ) ^ i * 2) *
            (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) := by ring
      _ ≤ 2 * (cfg.P.M₀ : ℝ) * (11 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 2) *
            (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) := by gcongr
  have hsum : (chainRebuildCap cfg 1 (fun _ => 0) : ℝ) ≤
      (cfg.P.M₀ : ℝ) +
      2 * (cfg.P.M₀ : ℝ) * (((cfg.P.d : ℝ) + 1) * (11 * psi) ^ (cfg.P.d + 1) *
        (2 : ℝ) ^ (cfg.P.d + 2) * (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ))) := by
    unfold chainRebuildCap
    rw [one_mul]
    push_cast
    have hs := Finset.sum_le_sum hterm
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hs
    linarith
  have hBase := shiftDepositBound_le_exp cfg.P cfg.P.M₀ hpsi (C_N := 1) zero_le_one hd
    (by linarith) hψ
  have hclog1 : (1 : ℝ) ≤ (Nat.clog 2 (cfg.P.M₀ + 2) : ℝ) ^ 2 := by
    have : 1 ≤ Nat.clog 2 (cfg.P.M₀ + 2) := Nat.succ_le_of_lt (Nat.clog_pos (by omega) (by omega))
    have : (1 : ℝ) ≤ (Nat.clog 2 (cfg.P.M₀ + 2) : ℝ) := by exact_mod_cast this
    nlinarith
  have hBase' : ((cfg.P.d : ℝ) + 1) * (11 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 2) *
      (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) ≤
      9 * alg2TimeFactor (19 + 3 * C_ψ) (47 / 48) cfg.P.M₀ := by
    have hnn : 0 ≤ ((cfg.P.d : ℝ) + 1) * (11 * psi) ^ (cfg.P.d + 1) * (2 : ℝ) ^ (cfg.P.d + 2) *
        (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) := by positivity
    rw [alg2TimeFactor_eq_exp_logShape]
    have h1 := le_mul_of_one_le_right hnn hclog1
    have h2 : (1 + 2 * (1 : ℝ)) ^ 2 = 9 := by norm_num
    rw [h2] at hBase
    exact h1.trans hBase
  have hT1 : 1 ≤ alg2TimeFactor (19 + 3 * C_ψ) (47 / 48) cfg.P.M₀ := by
    rw [alg2TimeFactor_eq_exp_logShape]
    have hA1 := one_le_logShape cfg.P.hM₀
    exact Real.one_le_exp (by nlinarith)
  nlinarith

/-- **Concrete initial `chainRebuildCap` is `(I.m + 1) · m^{o(1)}`**: on every valid circulation `J`,
the initial unit cap `chainRebuildCap cfg 1 (fun _ => 0)` is at most
`((I.m + 1 : ℕ) : ℝ) * C * alg2TimeFactor E (47 / 48) I.m`. -/
theorem concrete_initRebuildCap_le_timeFactor
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) :
    ∃ C E : ℝ, 0 ≤ E ∧ ∀ (J : Circulation),
      J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
      let I := solverConnectedAugmented J
      let cfg := concreteCirculationCfgWithLast W J
      (chainRebuildCap cfg 1 (fun _ => 0) : ℝ) ≤
        ((I.m + 1 : ℕ) : ℝ) * (C * alg2TimeFactor E (47 / 48) I.m) := by
  let T := concreteEdgeThresholdWithLast W
  let E : ℝ := 19 + 3 * 1
  have hE : 0 ≤ E := by norm_num [E]
  refine ⟨19 * (T : ℝ) * alg2TimeFactor E (47 / 48) T, E, hE, fun J hJn hJm hCap => ?_⟩
  let I := solverConnectedAugmented J
  let cfg := concreteCirculationCfgWithLast W J
  obtain ⟨_, _, hPsi, _, _⟩ := concreteCirculation_bounds_of
    (le_max_left W.M_thresh _) (le_max_right W.M_thresh _)
    (concreteEdgeThresholdWithLast_ge_two W) J hJn hJm hCap
  have hM0Eq : cfg.P.M₀ = max I.m T := rfl
  have hdEq : cfg.P.d = chosenD (23 / 24) cfg.P.M₀ := rfl
  have h1 := initRebuildCap_le_M0_timeFactor cfg (C_ψ := 1) zero_le_one hdEq hPsi
  rw [hM0Eq] at h1
  have h2 := alg2TimeFactor_max_le hE I.m T
  have hTge : 1 ≤ T := le_trans (by decide) (concreteEdgeThresholdWithLast_ge_two W)
  have hMaxLe : ((max I.m T : ℕ) : ℝ) ≤ ((I.m + 1 : ℕ) : ℝ) * (T : ℝ) := by
    have hnat : max I.m T ≤ (I.m + 1) * T := by
      rcases le_total I.m T with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith
    exact_mod_cast hnat
  have hTfNN : 0 ≤ alg2TimeFactor E (47 / 48) (max I.m T) := by
    rw [alg2TimeFactor_eq_exp_logShape]; exact (Real.exp_pos _).le
  calc (chainRebuildCap cfg 1 (fun _ => 0) : ℝ)
      ≤ ((max I.m T : ℕ) : ℝ) * (19 * alg2TimeFactor E (47 / 48) (max I.m T)) := h1
    _ ≤ (((I.m + 1 : ℕ) : ℝ) * (T : ℝ)) *
          (19 * (alg2TimeFactor E (47 / 48) T * alg2TimeFactor E (47 / 48) I.m)) := by
        gcongr
    _ = ((I.m + 1 : ℕ) : ℝ) * (19 * (T : ℝ) * alg2TimeFactor E (47 / 48) T *
          alg2TimeFactor E (47 / 48) I.m) := by ring

end MinCostFlow.MinRatio
