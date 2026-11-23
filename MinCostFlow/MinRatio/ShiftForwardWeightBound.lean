module

public import MinCostFlow.MinRatio.ShiftForwardPotential
public import MinCostFlow.MinRatio.ShiftDepositAsymptotics
import Mathlib.Tactic

/-!
# The charge per update is `m^{o(1)}`

With the forward potential of `ShiftForwardPotential.lean`, each update of a batch is charged
`W_0 = Σ_{j < d} Γ^j shiftDeposit j` (`fwdWeight … 0`). We bound it as we bounded the deposit in
`ShiftDepositAsymptotics.lean`. Each deposit is at most `K · alg2TimeFactor (19 + 3 C_ψ) (47/48)
M₀` (`shiftDeposit_le_timeFactor`), and `d Γ^d ≤ (11 Γ)^{d+1} ≤ exp (3 (3 + C_γ) A)` by
`eleven_psi_pow_le_exp`, when `Γ ≤ exp (C_γ L^{23/24} log (L + 2))`. The recourse factor
`γ_r(M₀²)` of the concrete parameters has this form (`concrete_params_asymptotics`).
-/

public section

namespace MinCostFlow.MinRatio

open Chain

/-- **The charge per update is `m^{o(1)}`.** Under the hypotheses of `shiftDeposit_le_timeFactor`,
and with `1 ≤ Γ ≤ exp (C_γ L^{23/24} log (L + 2))`, the weight `W_0` is at most
`((1 + 2 C_N)² + 1) · alg2TimeFactor (19 + 3 C_ψ + 3 (3 + C_γ)) (47/48) M₀`. -/
theorem fwdWeight_le_timeFactor (P : ChainParams) (N₀ : ℕ) {psi C_ψ C_N C_γ : ℝ} {Γ : ℕ}
    (hM : 1 ≤ P.M₀) (hpsi : 1 ≤ psi) (hCψ : 0 ≤ C_ψ) (hCN : 0 ≤ C_N)
    (hd : P.d = chosenD (23 / 24) P.M₀)
    (hN : Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((P.M₀ : ℝ) + 2))
    (hψ : psi ≤ Real.exp (C_ψ * Real.log ((P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((P.M₀ : ℝ) + 2) + 2)))
    (hΓ1 : 1 ≤ Γ) (hΓ : (Γ : ℝ) ≤ Real.exp (C_γ * Real.log ((P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((P.M₀ : ℝ) + 2) + 2))) :
    (fwdWeight P N₀ psi Γ 0 : ℝ) ≤
      ((1 + 2 * C_N) ^ 2 + 1) * alg2TimeFactor (19 + 3 * C_ψ + 3 * (3 + C_γ)) (47 / 48) P.M₀ := by
  set K : ℝ := (1 + 2 * C_N) ^ 2 + 1 with hK
  set S : ℝ := K * alg2TimeFactor (19 + 3 * C_ψ) (47 / 48) P.M₀ with hS
  have hKpos : 0 < K := by positivity
  have hΓ1' : (1 : ℝ) ≤ Γ := by exact_mod_cast hΓ1
  -- each term is at most `Γ^d · S`
  have hsum : (fwdWeight P N₀ psi Γ 0 : ℝ) ≤ (P.d : ℝ) * ((Γ : ℝ) ^ P.d * S) := by
    unfold fwdWeight
    push_cast
    calc ∑ j ∈ Finset.Ico 0 P.d, (Γ : ℝ) ^ (j - 0) * (shiftDeposit P N₀ psi j : ℝ)
        ≤ ∑ _j ∈ Finset.Ico 0 P.d, (Γ : ℝ) ^ P.d * S := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := (Finset.mem_Ico.mp hj).2
          have h1 := shiftDeposit_le_timeFactor P N₀ hpsi hCψ hCN hd hN hψ hj'.le
          have h2 : (Γ : ℝ) ^ (j - 0) ≤ (Γ : ℝ) ^ P.d :=
            pow_le_pow_right₀ hΓ1' (by omega)
          exact mul_le_mul h2 h1 (Nat.cast_nonneg _) (by positivity)
      _ = (P.d : ℝ) * ((Γ : ℝ) ^ P.d * S) := by simp
  -- `d Γ^d ≤ (11 Γ)^{d+1}`, since `d < 2^d ≤ 11^{d+1}` and `Γ ≥ 1`
  have hd11 : (P.d : ℝ) ≤ 11 ^ (P.d + 1) := by
    have h : P.d ≤ 11 ^ (P.d + 1) :=
      calc P.d ≤ 2 ^ P.d := Nat.lt_two_pow_self.le
        _ ≤ 11 ^ P.d := Nat.pow_le_pow_left (by norm_num) _
        _ ≤ 11 ^ (P.d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast h
  have hpow : (P.d : ℝ) * (Γ : ℝ) ^ P.d ≤ (11 * (Γ : ℝ)) ^ (P.d + 1) := by
    rw [mul_pow]
    exact mul_le_mul hd11 (pow_le_pow_right₀ hΓ1' (by omega)) (by positivity) (by positivity)
  have h11 := eleven_psi_pow_le_exp hM hΓ1' hd hΓ
  have hSpos : 0 ≤ S := mul_nonneg hKpos.le (by
    rw [alg2TimeFactor_eq_exp_logShape]; exact (Real.exp_pos _).le)
  calc (fwdWeight P N₀ psi Γ 0 : ℝ)
      ≤ ((P.d : ℝ) * (Γ : ℝ) ^ P.d) * S := by rw [mul_assoc]; exact hsum
    _ ≤ Real.exp (3 * (3 + C_γ) * logShape P.M₀) * S :=
        mul_le_mul_of_nonneg_right (hpow.trans h11) hSpos
    _ = K * alg2TimeFactor (19 + 3 * C_ψ + 3 * (3 + C_γ)) (47 / 48) P.M₀ := by
        rw [hS, hK, alg2TimeFactor_eq_exp_logShape, alg2TimeFactor_eq_exp_logShape,
          show (19 + 3 * C_ψ + 3 * (3 + C_γ)) * logShape P.M₀ =
            (19 + 3 * C_ψ) * logShape P.M₀ + 3 * (3 + C_γ) * logShape P.M₀ by ring, Real.exp_add]
        ring

/-- **The charge per update is `m^{o(1)}` in the edge count**, in the form of
`shiftDeposit_le_timeFactor_edges`: when `M₀ = max m T` for a threshold `T` free of the input,
`W_0 ≤ C · alg2TimeFactor E (47/48) m` with `C` and `E` depending only on `C_ψ`, `C_N`, `C_γ`
and `T`. -/
theorem fwdWeight_le_timeFactor_edges {C_ψ C_N C_γ : ℝ} (hCψ : 0 ≤ C_ψ) (hCN : 0 ≤ C_N)
    (hCγ : 0 ≤ C_γ) (T : ℕ) :
    ∃ C E : ℝ, 0 ≤ E ∧ ∀ (P : ChainParams) (N₀ : ℕ) (psi : ℝ) (Γ m : ℕ), P.M₀ = max m T →
      1 ≤ P.M₀ → 1 ≤ psi → P.d = chosenD (23 / 24) P.M₀ →
      Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((P.M₀ : ℝ) + 2) →
      psi ≤ Real.exp (C_ψ * Real.log ((P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((P.M₀ : ℝ) + 2) + 2)) →
      1 ≤ Γ → (Γ : ℝ) ≤ Real.exp (C_γ * Real.log ((P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((P.M₀ : ℝ) + 2) + 2)) →
      (fwdWeight P N₀ psi Γ 0 : ℝ) ≤ C * alg2TimeFactor E (47 / 48) m := by
  have hE : (0 : ℝ) ≤ 19 + 3 * C_ψ + 3 * (3 + C_γ) := by linarith
  refine ⟨((1 + 2 * C_N) ^ 2 + 1) * alg2TimeFactor (19 + 3 * C_ψ + 3 * (3 + C_γ)) (47 / 48) T,
    19 + 3 * C_ψ + 3 * (3 + C_γ), hE, fun P N₀ psi Γ m hMeq hM hpsi hd hN hψ hΓ1 hΓ => ?_⟩
  have h1 := fwdWeight_le_timeFactor P N₀ hM hpsi hCψ hCN hd hN hψ hΓ1 hΓ
  rw [hMeq] at h1
  have h2 := alg2TimeFactor_max_le hE m T
  have hK : (0 : ℝ) ≤ (1 + 2 * C_N) ^ 2 + 1 := by positivity
  calc (fwdWeight P N₀ psi Γ 0 : ℝ)
      ≤ ((1 + 2 * C_N) ^ 2 + 1) *
          alg2TimeFactor (19 + 3 * C_ψ + 3 * (3 + C_γ)) (47 / 48) (max m T) := h1
    _ ≤ ((1 + 2 * C_N) ^ 2 + 1) *
          (alg2TimeFactor (19 + 3 * C_ψ + 3 * (3 + C_γ)) (47 / 48) T *
            alg2TimeFactor (19 + 3 * C_ψ + 3 * (3 + C_γ)) (47 / 48) m) :=
        mul_le_mul_of_nonneg_left h2 hK
    _ = _ := by ring

end MinCostFlow.MinRatio
