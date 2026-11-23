module

public import MinCostFlow.MinRatio.UpdateCycleLoopInd
public import MinCostFlow.MinRatio.ShiftDepositAsymptotics
import Mathlib.Tactic

/-!
# The shift loop of one Update runs a polynomial number of steps

The space of one `Update` has the term `(loopStepBound + 1) · cycleLoopIterSpace`
(`updateSpaceBound`), since each step of the shift loop may allocate memory. Here we show that
`loopStepBound` is bounded by a polynomial in the edge count, for the parameters of the paper.

`loopStepBound` is at most the shift-loop counter, which is below `(⌈2 Ψ_g⌉ k + 1)^{d+1}`
(`Chain.Ordered.loopOdometer_lt_pow`). With `⌈2 Ψ_g⌉ k + 1 ≤ 4 Ψ_g k` and `k^{d+1} ≤ 2^{d+1} M₀²`
(from `k ≤ 2 M₀^{1/d}`, a field of `ChainParams`), this is at most
`M₀² (8 Ψ_g)^{d+1} ≤ M₀² exp (3 (3 + C_ψ) A)`, where `A = L^{47/48} log (L + 2)`
(`eleven_psi_pow_le_exp`). The factor `exp (3 (3 + C_ψ) A)` is the subpolynomial time factor,
which is at most a constant times `m + 2` (`alg2TimeFactor_le_rpow`). So the number of steps is
`O((m + 2)^3)` when `M₀ = max m T` for a fixed threshold `T`.
-/

public section

namespace MinCostFlow.MinRatio

open Chain

/-- `k^{d+1} ≤ 2^{d+1} M₀²` for the branching factor `k ≤ 2 M₀^{1/d}` of `ChainParams`. -/
theorem chainParams_k_pow_le (P : ChainParams) :
    (P.k : ℝ) ^ (P.d + 1) ≤ 2 ^ (P.d + 1) * (P.M₀ : ℝ) ^ 2 := by
  have hM : (0 : ℝ) < P.M₀ := by exact_mod_cast P.hM₀
  have hM1 : (1 : ℝ) ≤ P.M₀ := by exact_mod_cast P.hM₀
  have hd : (0 : ℝ) < P.d := by exact_mod_cast P.hd
  have hroot : (0 : ℝ) ≤ (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) := Real.rpow_nonneg hM.le _
  have hkd : (P.k : ℝ) ^ P.d ≤ 2 ^ P.d * P.M₀ := by
    calc (P.k : ℝ) ^ P.d ≤ (2 * (P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ P.d :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) P.hk_upper _
      _ = 2 ^ P.d * P.M₀ := by
          rw [mul_pow, ← Real.rpow_natCast ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))), ← Real.rpow_mul hM.le,
            one_div_mul_cancel hd.ne', Real.rpow_one]
  have hk1 : (P.k : ℝ) ≤ 2 * P.M₀ := by
    have hle : (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) ≤ (P.M₀ : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hM1 (by
        rw [div_le_one hd]; exact_mod_cast P.hd)
    rw [Real.rpow_one] at hle
    linarith [P.hk_upper]
  calc (P.k : ℝ) ^ (P.d + 1) = (P.k : ℝ) ^ P.d * P.k := pow_succ _ _
    _ ≤ (2 ^ P.d * P.M₀) * (2 * P.M₀) :=
        mul_le_mul hkd hk1 (Nat.cast_nonneg _) (by positivity)
    _ = 2 ^ (P.d + 1) * (P.M₀ : ℝ) ^ 2 := by ring

/-- **The shift-loop counter is `M₀² · exp (O(A))`.** For `d = chosenD (23/24) M₀` and
`Ψ_g ≤ exp (C_ψ L^{23/24} log (L + 2))`,
`(⌈2 Ψ_g⌉ k + 1)^{d+1} ≤ M₀² exp (3 (3 + C_ψ) A)`. -/
theorem loopDigitCap_pow_le (cfg : Alg2Config) {C_ψ : ℝ}
    (hd : cfg.P.d = chosenD (23 / 24) cfg.P.M₀)
    (hψ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤ Real.exp (C_ψ * Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2))) :
    (((Chain.Ordered.loopDigitCap cfg + 1) ^ (cfg.P.d + 1) : ℕ) : ℝ) ≤
      (cfg.P.M₀ : ℝ) ^ 2 * Real.exp (3 * (3 + C_ψ) * logShape cfg.P.M₀) := by
  set ψ := alg2PsiGame cfg.Ψ cfg.P.M₀ with hψdef
  have hψ1 : 1 ≤ ψ := alg2PsiGame_ge_one _ _
  have hk1 : (1 : ℝ) ≤ cfg.P.k := by exact_mod_cast cfg.P.hk
  have hcap : ((Chain.Ordered.loopDigitCap cfg + 1 : ℕ) : ℝ) ≤ 4 * ψ * cfg.P.k := by
    unfold Chain.Ordered.loopDigitCap
    have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * ψ by linarith)
    push_cast
    nlinarith
  have hpow : (((Chain.Ordered.loopDigitCap cfg + 1) ^ (cfg.P.d + 1) : ℕ) : ℝ) ≤
      (4 * ψ) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) ^ (cfg.P.d + 1) := by
    push_cast
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hcap) _
  have hk := chainParams_k_pow_le cfg.P
  have h11 := eleven_psi_pow_le_exp cfg.P.hM₀ hψ1 hd hψ
  have h8 : (8 * ψ) ^ (cfg.P.d + 1) ≤ (11 * ψ) ^ (cfg.P.d + 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  calc (((Chain.Ordered.loopDigitCap cfg + 1) ^ (cfg.P.d + 1) : ℕ) : ℝ)
      ≤ (4 * ψ) ^ (cfg.P.d + 1) * (2 ^ (cfg.P.d + 1) * (cfg.P.M₀ : ℝ) ^ 2) :=
        hpow.trans (mul_le_mul_of_nonneg_left hk (by positivity))
    _ = (8 * ψ) ^ (cfg.P.d + 1) * (cfg.P.M₀ : ℝ) ^ 2 := by
        rw [show (8 * ψ) = 4 * ψ * 2 by ring, mul_pow (4 * ψ) 2]; ring
    _ ≤ Real.exp (3 * (3 + C_ψ) * logShape cfg.P.M₀) * (cfg.P.M₀ : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (h8.trans h11) (by positivity)
    _ = _ := by ring

/-- The number of steps the shift loop may take from `model` is below
`(⌈2 Ψ_g⌉ k + 1)^{d+1}`. -/
theorem loopStepBound_lt_pow (cfg : Alg2Config) (model : Alg2State cfg) :
    loopStepBound cfg model + 1 ≤ (Chain.Ordered.loopDigitCap cfg + 1) ^ (cfg.P.d + 1) := by
  have h := Chain.Ordered.loopOdometer_lt_pow cfg model.chain model.branD model.passes
  have h2 : loopStepBound cfg model ≤
      Chain.Ordered.loopOdometer cfg model.chain model.branD model.passes := min_le_right _ _
  omega

/-- **The shift loop of one Update takes `O((m + 2)^3)` steps.** When the chain is built for
`M₀ = max m T`, with a threshold `T` that does not depend on the input, with the depth of the
paper and `Ψ_g ≤ exp (C_ψ L^{23/24} log (L + 2))`, then `loopStepBound ≤ a (m + 2)^3` for a
constant `a` that depends only on `C_ψ` and `T`. -/
theorem loopStepBound_poly {C_ψ : ℝ} (hCψ : 0 ≤ C_ψ) (T : ℕ) :
    ∃ a : ℕ, ∀ (cfg : Alg2Config) (model : Alg2State cfg) (m : ℕ), cfg.P.M₀ = max m T →
      cfg.P.d = chosenD (23 / 24) cfg.P.M₀ →
      alg2PsiGame cfg.Ψ cfg.P.M₀ ≤ Real.exp (C_ψ * Real.log ((cfg.P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) →
      loopStepBound cfg model ≤ a * (m + 2) ^ 3 := by
  set E : ℝ := 3 * (3 + C_ψ) with hEdef
  have hE : 0 ≤ E := by positivity
  obtain ⟨B, hB1, hB⟩ := alg2TimeFactor_le_rpow (C := E) (a := 47 / 48) (δ := 1)
    (by norm_num) (by norm_num) (by norm_num)
  set B' : ℝ := B + alg2TimeFactor E (47 / 48) 0 with hB'def
  have hB'm : ∀ m : ℕ, alg2TimeFactor E (47 / 48) m ≤ B' * ((m : ℝ) + 2) := by
    intro m
    have h0 : 0 < alg2TimeFactor E (47 / 48) 0 := alg2TimeFactor_pos _ _ _
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [Nat.cast_zero, zero_add]
      nlinarith
    · have h := hB m hm
      rw [Real.rpow_one] at h
      have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
  set K : ℝ := ((T : ℝ) + 1) ^ 2 * alg2TimeFactor E (47 / 48) T * B' with hKdef
  refine ⟨⌈K⌉₊, fun cfg model m hM hd hψ => ?_⟩
  have h1 := loopStepBound_lt_pow cfg model
  have h2 := loopDigitCap_pow_le cfg hd hψ
  have hmax := alg2TimeFactor_max_le hE m T
  rw [← alg2TimeFactor_eq_exp_logShape, hM] at h2
  have hT0 : 0 ≤ alg2TimeFactor E (47 / 48) T := (alg2TimeFactor_pos _ _ _).le
  have hMle : ((max m T : ℕ) : ℝ) ≤ ((T : ℝ) + 1) * ((m : ℝ) + 2) := by
    have : (max m T : ℕ) ≤ m + T := max_le (by omega) (by omega)
    have h' : ((max m T : ℕ) : ℝ) ≤ (m : ℝ) + T := by exact_mod_cast this
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hT0' : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    nlinarith
  have hreal : (loopStepBound cfg model : ℝ) ≤ K * ((m : ℝ) + 2) ^ 3 := by
    have hcast : (loopStepBound cfg model : ℝ) + 1 ≤
        (((Chain.Ordered.loopDigitCap cfg + 1) ^ (cfg.P.d + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    have hsq : ((max m T : ℕ) : ℝ) ^ 2 ≤ (((T : ℝ) + 1) * ((m : ℝ) + 2)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hMle 2
    have hfac : alg2TimeFactor E (47 / 48) (max m T) ≤
        alg2TimeFactor E (47 / 48) T * (B' * ((m : ℝ) + 2)) :=
      hmax.trans (mul_le_mul_of_nonneg_left (hB'm m) hT0)
    calc (loopStepBound cfg model : ℝ)
        ≤ ((max m T : ℕ) : ℝ) ^ 2 * alg2TimeFactor E (47 / 48) (max m T) := by linarith
      _ ≤ (((T : ℝ) + 1) * ((m : ℝ) + 2)) ^ 2 *
            (alg2TimeFactor E (47 / 48) T * (B' * ((m : ℝ) + 2))) :=
          mul_le_mul hsq hfac (alg2TimeFactor_pos _ _ _).le (by positivity)
      _ = K * ((m : ℝ) + 2) ^ 3 := by rw [hKdef]; ring
  have hK : K * ((m : ℝ) + 2) ^ 3 ≤ (⌈K⌉₊ : ℝ) * ((m : ℝ) + 2) ^ 3 :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil K) (by positivity)
  have : (loopStepBound cfg model : ℝ) ≤ ((⌈K⌉₊ * (m + 2) ^ 3 : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast this

end MinCostFlow.MinRatio
