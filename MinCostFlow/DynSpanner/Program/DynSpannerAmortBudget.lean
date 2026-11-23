module

public import MinCostFlow.DynSpanner.ComplexitySum

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The budget of a restart

The sum of Lemma 5.9 (`lemma_5_9_sum_of_step_bounds`) charges a restart (a step at level `j = 0`)
`N₁ · 12 L q K₁ E_L Δ₁ Λ` beyond `(L + 1) Enc(u) + |U_H| + |D|`. In the proof of Lemma 5.9
([chen2022maximum] Section 5.1, used for Theorem 8.2, page 39) a restart costs the call of the
sparsifier on the whole graph, `K_t (n + m γ_ℓ²) log^{p_t}`, plus terms linear in `n`, `m`, the old
and the new spanner, and `L`. Each of these is at most `N₁` times a factor of the budget, since
`n ≤ N₁`, `m ≤ N₁ Δ₀` and the spanners have at most `N₁ (L + 1) K_s γ_ℓ Λ_s` edges.

This file proves that arithmetic once for any cost `f` with such a bound
(`restart_extra_of_le`). The log factor `X` of the sparsifier can be any number at most `Λ`, so
that the lemma applies both to the model's cost and to the cost of the program.
-/

namespace MinCostFlow.DynSpanner.Program

open MinCostFlow.DynSpanner

public section

/-- **The budget of a restart.** If a cost `f` of a restart is at most
`K_t (n_act + m γ_ℓ²) X + n + m + 2 |E(H_new)| + m γ_ℓ + L + 1 + (L + 1) Enc(u) + 2 |E(H_old)| +
|U_H| + |D|`, with `n_act, n ≤ N₁`, `m ≤ N₁ Δ₀`, the spanner sizes bounded as in Lemma 5.9, and
`X ≤ Λ`, then `f` exceeds `(L + 1) Enc(u) + |U_H| + |D|` by at most `N₁ · 12 L q K₁ E_L Δ₁ Λ`. -/
theorem restart_extra_of_le (P : SparsifyParams) {L q maxDeg : ℕ} (hL : 1 ≤ L) (hq : 2 ≤ q)
    {N₁ Λ Λ_s X f enc UH D Hnew Hold nact n m : ℝ}
    (h1N : 1 ≤ N₁) (hnact : nact ≤ N₁) (_hnact0 : 0 ≤ nact) (hn : n ≤ N₁)
    (hm : m ≤ N₁ * (maxDeg : ℝ)) (hm0 : 0 ≤ m)
    (hHnew : Hnew ≤ N₁ * P.K_s * P.γ_ℓ * Λ_s)
    (hHold : Hold ≤ N₁ * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s))
    (hX0 : 0 ≤ X) (hXΛ : X ≤ Λ) (hΛs1 : 1 ≤ Λ_s) (hΛsΛ : Λ_s ≤ Λ)
    (hf : f ≤ P.K_t * (nact + m * P.γ_ℓ ^ 2) * X + n + m + 2 * Hnew + m * P.γ_ℓ +
      (L : ℝ) + 1 + ((L : ℝ) + 1) * enc + 2 * Hold + UH + D) :
    f - ((L : ℝ) + 1) * enc - UH - D ≤
      N₁ * (12 * ((L : ℝ) * (q : ℝ)) * (P.K_t + P.K_s + 1) *
        (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
          P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) * ((maxDeg : ℝ) + 1) * Λ) := by
  set E_L := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
    P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
  set deg1 : ℝ := (maxDeg : ℝ) + 1
  set K1 : ℝ := P.K_t + P.K_s + 1
  have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
  have hL_r : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hq_r : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hLq_ge2 : (2 : ℝ) ≤ (L : ℝ) * (q : ℝ) := by nlinarith [hL_r, hq_r]
  have hL1 : (L : ℝ) + 1 ≤ (L : ℝ) * (q : ℝ) := by nlinarith [hL_r, hq_r]
  have hΛ_ge1 : 1 ≤ Λ := le_trans hΛs1 hΛsΛ
  have hmd : 0 ≤ (maxDeg : ℝ) := Nat.cast_nonneg _
  have hkt : P.K_t * (nact + m * P.γ_ℓ ^ 2) * X ≤
      P.K_t * (N₁ + N₁ * (maxDeg : ℝ) * P.γ_ℓ ^ 2) * X := by
    have h1 := add_le_add hnact (mul_le_mul_of_nonneg_right hm (sq_nonneg P.γ_ℓ))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 P.hK_t) hX0
  have hgm_l : m * P.γ_ℓ ≤ N₁ * (maxDeg : ℝ) * P.γ_ℓ := mul_le_mul_of_nonneg_right hm hγl
  have hL_N1 : (L : ℝ) + 1 ≤ ((L : ℝ) + 1) * N₁ := le_mul_of_one_le_right (by linarith) h1N
  have hex_le : f - ((L : ℝ) + 1) * enc - UH - D ≤ N₁ * (
      P.K_t * (1 + (maxDeg : ℝ) * P.γ_ℓ ^ 2) * X +
      (1 + (maxDeg : ℝ)) +
      2 * P.K_s * P.γ_ℓ * Λ_s +
      (maxDeg : ℝ) * P.γ_ℓ +
      ((L : ℝ) + 1) +
      2 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s)) := by
    have h1 : f - ((L : ℝ) + 1) * enc - UH - D ≤
        P.K_t * (N₁ + N₁ * (maxDeg : ℝ) * P.γ_ℓ ^ 2) * X +
        N₁ + N₁ * (maxDeg : ℝ) + 2 * (N₁ * P.K_s * P.γ_ℓ * Λ_s) +
        N₁ * (maxDeg : ℝ) * P.γ_ℓ + ((L : ℝ) + 1) * N₁ +
        2 * (N₁ * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s)) := by
      linarith only [hf, hkt, hn, hm, hHnew, hgm_l, hL_N1, hHold]
    exact le_trans h1 (le_of_eq (by ring))
  obtain ⟨hEL1, hEL_l, hEL_l2, _⟩ := expFactor_bounds P.hγ_c P.hγ_ℓ L maxDeg
  have hEL_nn : 0 ≤ E_L := by linarith
  have hdeg_le : (maxDeg : ℝ) ≤ deg1 := by dsimp only [deg1]; linarith
  have hdeg1_nn : 0 ≤ deg1 := by dsimp only [deg1]; positivity
  have h1_d : (1 : ℝ) ≤ deg1 := by dsimp only [deg1]; linarith
  have hKt_le : P.K_t ≤ K1 := by dsimp only [K1]; linarith [P.hK_s]
  have hKs_le : P.K_s ≤ K1 := by dsimp only [K1]; linarith [P.hK_t]
  have h1_le : (1 : ℝ) ≤ K1 := by dsimp only [K1]; linarith [P.hK_t, P.hK_s]
  have hK1_nn : 0 ≤ K1 := by linarith
  have hM : 0 ≤ K1 * E_L * deg1 * Λ := by positivity
  have hterm1 : P.K_t * (1 + (maxDeg : ℝ) * P.γ_ℓ ^ 2) * X ≤ 2 * (K1 * E_L * deg1 * Λ) := by
    have h1 : 1 + (maxDeg : ℝ) * P.γ_ℓ ^ 2 ≤ 2 * (E_L * deg1) := by
      have : (maxDeg : ℝ) * P.γ_ℓ ^ 2 ≤ deg1 * E_L :=
        mul_le_mul hdeg_le hEL_l2 (sq_nonneg P.γ_ℓ) hdeg1_nn
      have : (1 : ℝ) ≤ E_L * deg1 := one_le_mul_of_one_le_of_one_le hEL1 h1_d
      linarith
    have hA : P.K_t * (1 + (maxDeg : ℝ) * P.γ_ℓ ^ 2) ≤ K1 * (2 * (E_L * deg1)) :=
      mul_le_mul hKt_le h1 (by positivity) hK1_nn
    have hB : (K1 * (2 * (E_L * deg1))) * X ≤ (K1 * (2 * (E_L * deg1))) * Λ :=
      mul_le_mul_of_nonneg_left hXΛ (by positivity)
    calc P.K_t * (1 + (maxDeg : ℝ) * P.γ_ℓ ^ 2) * X
        ≤ (K1 * (2 * (E_L * deg1))) * X := mul_le_mul_of_nonneg_right hA hX0
      _ ≤ (K1 * (2 * (E_L * deg1))) * Λ := hB
      _ = 2 * (K1 * E_L * deg1 * Λ) := by ring
  have hterm2 : 1 + (maxDeg : ℝ) ≤ K1 * E_L * deg1 * Λ := by
    have h1' : 1 ≤ K1 * E_L * Λ :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1_le hEL1) hΛ_ge1
    calc 1 + (maxDeg : ℝ) = 1 * deg1 := by dsimp only [deg1]; ring
      _ ≤ (K1 * E_L * Λ) * deg1 := mul_le_mul_of_nonneg_right h1' hdeg1_nn
      _ = K1 * E_L * deg1 * Λ := by ring
  have hterm3 : 2 * P.K_s * P.γ_ℓ * Λ_s ≤ 2 * (K1 * E_L * deg1 * Λ) := by
    have hA : 2 * P.K_s * P.γ_ℓ ≤ 2 * K1 * E_L :=
      mul_le_mul (mul_le_mul_of_nonneg_left hKs_le (by norm_num)) hEL_l hγl
        (mul_nonneg (by norm_num) hK1_nn)
    have hB : 2 * K1 * E_L * Λ_s ≤ 2 * K1 * E_L * Λ :=
      mul_le_mul_of_nonneg_left hΛsΛ (mul_nonneg (mul_nonneg (by norm_num) hK1_nn) hEL_nn)
    calc 2 * P.K_s * P.γ_ℓ * Λ_s
        ≤ 2 * K1 * E_L * Λ_s := mul_le_mul_of_nonneg_right hA (by linarith)
      _ ≤ 2 * K1 * E_L * Λ := hB
      _ = 2 * (K1 * E_L * 1 * Λ) := by ring
      _ ≤ 2 * (K1 * E_L * deg1 * Λ) := by gcongr
  have hterm4 : (maxDeg : ℝ) * P.γ_ℓ ≤ K1 * E_L * deg1 * Λ := by
    calc (maxDeg : ℝ) * P.γ_ℓ ≤ deg1 * E_L := mul_le_mul hdeg_le hEL_l hγl hdeg1_nn
      _ = 1 * E_L * deg1 * 1 := by ring
      _ ≤ K1 * E_L * deg1 * Λ := by gcongr
  have h1M : 1 ≤ K1 * E_L * deg1 * Λ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le h1_le hEL1) h1_d) hΛ_ge1
  have hterm5 : (L : ℝ) + 1 ≤ ((L : ℝ) * (q : ℝ)) * (K1 * E_L * deg1 * Λ) :=
    le_trans hL1 (le_mul_of_one_le_right (by linarith) h1M)
  have hterm6 : 2 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) ≤
      2 * ((L : ℝ) * (q : ℝ)) * (K1 * E_L * deg1 * Λ) := by
    have hA : (L + 1 : ℝ) * P.K_s ≤ (L : ℝ) * (q : ℝ) * K1 :=
      mul_le_mul hL1 hKs_le P.hK_s (by linarith)
    have hB : ((L : ℝ) * (q : ℝ) * K1) * P.γ_ℓ ≤ ((L : ℝ) * (q : ℝ) * K1) * E_L :=
      mul_le_mul_of_nonneg_left hEL_l (mul_nonneg (by linarith) hK1_nn)
    have hC : ((L : ℝ) * (q : ℝ) * K1 * E_L) * Λ_s ≤ ((L : ℝ) * (q : ℝ) * K1 * E_L) * Λ :=
      mul_le_mul_of_nonneg_left hΛsΛ (mul_nonneg (mul_nonneg (by linarith) hK1_nn) hEL_nn)
    have hAB := mul_le_mul_of_nonneg_right hA hγl
    have hABE := le_trans (mul_le_mul_of_nonneg_right (le_trans hAB hB) (by linarith)) hC
    calc 2 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s)
        ≤ 2 * ((L : ℝ) * (q : ℝ) * K1 * E_L * Λ) := by linarith only [hABE]
      _ = 2 * ((L : ℝ) * (q : ℝ)) * (K1 * E_L * 1 * Λ) := by ring
      _ ≤ 2 * ((L : ℝ) * (q : ℝ)) * (K1 * E_L * deg1 * Λ) := by gcongr
  have h6M : 6 * (K1 * E_L * deg1 * Λ) ≤ 3 * ((L : ℝ) * (q : ℝ)) * (K1 * E_L * deg1 * Λ) :=
    mul_le_mul_of_nonneg_right (by linarith) hM
  have hsum_coef :
      P.K_t * (1 + (maxDeg : ℝ) * P.γ_ℓ ^ 2) * X + (1 + (maxDeg : ℝ)) +
      2 * P.K_s * P.γ_ℓ * Λ_s + (maxDeg : ℝ) * P.γ_ℓ + ((L : ℝ) + 1) +
      2 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) ≤
      12 * ((L : ℝ) * (q : ℝ)) * K1 * E_L * deg1 * Λ := by
    linarith [hterm1, hterm2, hterm3, hterm4, hterm5, hterm6, h6M]
  exact le_trans hex_le (mul_le_mul_of_nonneg_left hsum_coef (by linarith))

end

end MinCostFlow.DynSpanner.Program
