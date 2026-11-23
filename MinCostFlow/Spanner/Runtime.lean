module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Spanner.ToolCosts
public import MinCostFlow.Spanner.Algorithm
public import MinCostFlow.Spanner.WitnessBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public import MinCostFlow.Spanner.Task2Base
public import MinCostFlow.Spanner.Task3Base

import MinCostFlow.Spanner.Subgraph
import MinCostFlow.Spanner.WitnessProps
import MinCostFlow.Spanner.WitnessLift
import MinCostFlow.Spanner.Claim87
import MinCostFlow.Spanner.Analysis2
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
public import MinCostFlow.Spanner.RuntimeBase

/-!
# Runtime accounting and uniform parameter caps for Algorithm 4 (`Sparsify`)

This file provides:
1. `sparsifyLocalCost` and `sparsifyCost`: total operation counts of Algorithm 4 (`sparsifyLocal`
   and `sparsify`, `spanner.tex`, page 42), combining internal model steps with per-call tool charges
   from `SpannerToolCosts` (`ToolCosts.lean`).
2. `sparsifyLocalCost_le` and `sparsifySparsity_le`: explicit paper-form `Õ(·)` bounds on the
   runtime (`O(n + m γ_ℓ² length(Π_{J → H'}) log(n + m + 2))` plus the `Decompose` call) and
   sparsity (`O(n γ_ℓ log(n + m + 2))`).
3. `DecomposeMonotone`, `PathDSMonotone`, and uniform `M`-cap parameter definitions (`capPhiDS`,
   `capGammaExpPath`, `capGammaDel`, `capGammaL`, `capGammaC`) for graphs with `J.m ≤ M`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-- Explicit **Theorem 8.1** operation-count bound for `sparsifyLocalCost` with multiplicative
query/fallback overhead `γ_t ≥ 1` satisfying `γ_query ≤ γ_t · γ_ExpPath`. -/
theorem sparsifyLocalCost_le_with_time {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (costs : SpannerToolCosts)
    (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hNmax : J.n ≤ N_max)
    (hWmax : 2 * (J.m : ℝ) / tools.decompose.φ_dec (stripLoops J) ≤ W_max)
    (hLen : 1 ≤ J.m → 1 ≤ length J embJH)
    (γ_t : ℝ) (hγt : 1 ≤ γ_t)
    (hγJq : let wd := (sparsifyLocal tools H' J embJH).wd
      tools.pathDS.γ_query wd.φ_dec wd.J0_strip.m ≤ γ_t * wd.γ_ExpPath)
    (hγWq : let wd := (sparsifyLocal tools H' J embJH).wd
      tools.pathDS.γ_query wd.φ_Const wd.M_W ≤ γ_t * wd.γ_ExpPath) :
    let out := sparsifyLocal tools H' J embJH
    let wd := out.wd
    let γ_ℓ := wd.γ_ExpPath ^ 2
    (sparsifyLocalCost tools costs H' J embJH : ℝ) ≤
      (costs.decompose.callCost wd.J0_strip.m : ℝ) +
      sparsifyBaseConst wd.c_deg costs * γ_t *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
  intro out wd γ_ℓ
  have hw := buildWitness_ok tools H' J embJH hJ hembJH hNmax hWmax
  have hc88 := corollary_8_8 tools H' J embJH hJ hembJH hw
  have hc810 := corollary_8_10 tools H' J embJH hJ hw
  have hst2 := task2_stats tools H' J embJH hJ hembJH hw
  have hst3 := task3_stats tools H' J embJH hJ hw
  have hWm_m := W_m_le_m tools H' J embJH hw
  have hvert_m := sum_comps_card_le_m tools H' J embJH hw
  have hwsum := sum_comps_w_le_m tools H' J embJH hw
  have hsum_jm : (wd.comps.map fun c => c.J_sub.m).sum ≤ J.m := by
    have h1 : wd.j0Edges.length + (wd.comps.map fun c => c.J_sub.m).sum ≤ wd.J0_strip.m :=
      sum_comp_j_m_le tools H' J embJH hw
    have h2 : wd.J0_strip.m ≤ J.m := stripLoops_m_le J
    exact Nat.le_trans (Nat.le_add_left _ _) (Nat.le_trans h1 h2)
  have hsum_Wm : (wd.comps.map fun c => c.W_sub.m).sum ≤ wd.W.m := by
    have h1 : wd.W.m = wd.j0Edges.length + (wd.comps.map fun c => c.W_sub.m).sum := hw.W_m_eq
    rw [h1]
    exact Nat.le_add_left _ _
  have hγE_ge2 : 2 ≤ wd.γ_ExpPath := by
    have h1 : (2 : ℝ) ≤ 1 / wd.φ_ds :=
      (le_div_iff₀ hw.φ_ds_pos).mpr (by nlinarith only [hw.φ_ds_half])
    exact le_trans h1 hw.γ_ExpPath_ge
  have hφ_inv : 1 / wd.φ_dec ≤ wd.γ_ExpPath :=
    le_trans (one_div_le_one_div_of_le hw.φ_ds_pos hw.φ_ds_le_dec) hw.γ_ExpPath_ge
  have hcdeg : 1 ≤ wd.c_deg := hw.c_deg_ge
  have hWm_gamma : (wd.W.m : ℝ) ≤ (1 + wd.c_deg / 2) * wd.γ_ExpPath * (J.m : ℝ) := by
    have hWm_m' : (wd.W.m : ℝ) ≤ (J.m : ℝ) + wd.c_deg * (J.m : ℝ) / (2 * wd.φ_dec) := hWm_m
    have hm_nn : (0 : ℝ) ≤ J.m := Nat.cast_nonneg J.m
    have h1 : (J.m : ℝ) ≤ (1 : ℝ) * wd.γ_ExpPath * (J.m : ℝ) := by nlinarith only [hm_nn, hγE_ge2]
    have h2 : wd.c_deg * (J.m : ℝ) / (2 * wd.φ_dec) =
        (wd.c_deg / 2) * (1 / wd.φ_dec) * (J.m : ℝ) := by ring
    have h3 : (wd.c_deg / 2) * (1 / wd.φ_dec) * (J.m : ℝ) ≤
        (wd.c_deg / 2) * wd.γ_ExpPath * (J.m : ℝ) := by
      have h4 : (wd.c_deg / 2) * (1 / wd.φ_dec) ≤ (wd.c_deg / 2) * wd.γ_ExpPath :=
        mul_le_mul_of_nonneg_left hφ_inv (by linarith only [hcdeg])
      exact mul_le_mul_of_nonneg_right h4 hm_nn
    linarith only [hWm_m', h1, h2, h3]
  have hγJ_ge2 : 2 ≤ tools.pathDS.γ_ExpPath wd.φ_dec wd.J0_strip.m := by
    have h1 := tools.pathDS.hφ_half wd.φ_dec wd.J0_strip.m hw.φ_dec_pos
    have h2 := tools.pathDS.hφ_pos wd.φ_dec wd.J0_strip.m hw.φ_dec_pos
    have h3 := tools.pathDS.hγ_ExpPath_ge wd.φ_dec wd.J0_strip.m hw.φ_dec_pos
    have h4 : (2 : ℝ) ≤ 1 / tools.pathDS.φ_out wd.φ_dec wd.J0_strip.m :=
      (le_div_iff₀ h2).mpr (by nlinarith only [h1])
    exact le_trans h4 h3
  have hγJ_le : tools.pathDS.γ_ExpPath wd.φ_dec wd.J0_strip.m ≤ wd.γ_ExpPath := le_max_left _ _
  have hγW_ge2 : 2 ≤ tools.pathDS.γ_ExpPath wd.φ_Const wd.M_W := by
    have h1 := tools.pathDS.hφ_half wd.φ_Const wd.M_W hw.φ_Const_pos
    have h2 := tools.pathDS.hφ_pos wd.φ_Const wd.M_W hw.φ_Const_pos
    have h3 := tools.pathDS.hγ_ExpPath_ge wd.φ_Const wd.M_W hw.φ_Const_pos
    have h4 : (2 : ℝ) ≤ 1 / tools.pathDS.φ_out wd.φ_Const wd.M_W :=
      (le_div_iff₀ h2).mpr (by nlinarith only [h1])
    exact le_trans h4 h3
  have hγW_le : tools.pathDS.γ_ExpPath wd.φ_Const wd.M_W ≤ wd.γ_ExpPath := le_max_right _ _
  -- Split `J.m = 0` vs `1 ≤ J.m`.
  rcases Nat.eq_zero_or_pos J.m with hm0 | hm_pos
  · have hJ0m : wd.J0_strip.m = 0 := by
      have h1 : wd.J0_strip.m ≤ J.m := stripLoops_m_le J
      exact Nat.eq_zero_of_le_zero (hm0 ▸ h1)
    have hWm0 : wd.W.m = 0 := by
      have h1 : (wd.W.m : ℝ) ≤ (1 + wd.c_deg / 2) * wd.γ_ExpPath * (J.m : ℝ) := hWm_gamma
      rw [hm0, Nat.cast_zero, mul_zero] at h1
      exact Nat.cast_eq_zero.mp (le_antisymm h1 (Nat.cast_nonneg _))
    have hcomps0 : wd.comps = [] := by
      have h1 : wd.comps.length ≤ J.m := hst2.2.2.1
      exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (hm0 ▸ h1))
    have hgpJ0 : out.stats.dsGetPathCountJ = 0 := by
      have h1 : out.stats.dsGetPathCountJ ≤ wd.W.m := hst2.2.2.2.2.2.2.2.1
      exact Nat.eq_zero_of_le_zero (hWm0 ▸ h1)
    have hmid1 : out.stats.middleIters1 = 0 := by
      have h1 : out.stats.middleIters1 = out.stats.dsGetPathCountJ := hst2.2.2.2.2.2.2.2.2.1
      exact h1.trans hgpJ0
    have hinn1 : out.stats.innerIters1 = 0 := by
      have h1 : (out.stats.innerIters1 : ℝ) ≤
          (out.stats.dsGetPathCountJ : ℝ) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1)) :=
        hst2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [hgpJ0, Nat.cast_zero, zero_mul] at h1
      exact Nat.cast_eq_zero.mp (le_antisymm h1 (Nat.cast_nonneg _))
    have hvc0 : out.stats.vcongUpdates = 0 := by
      have h1 : (out.stats.vcongUpdates : ℝ) ≤
          (out.stats.dsGetPathCountJ : ℝ) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1)) :=
        hst2.2.2.2.2.2.2.2.2.2.2.1
      rw [hgpJ0, Nat.cast_zero, zero_mul] at h1
      exact Nat.cast_eq_zero.mp (le_antisymm h1 (Nat.cast_nonneg _))
    have hinit1 : out.stats.dsInitCountJ = 0 := by
      have h1 : out.stats.dsInitCountJ = out.stats.η₁ * wd.comps.length := hst2.2.2.2.1
      rw [hcomps0, List.length_nil, Nat.mul_zero] at h1
      exact h1
    have hgpW0 : out.stats.dsGetPathCountW = 0 := by
      have h1 : out.stats.dsGetPathCountW ≤ J.m := hst3.2.2.2.2.2.1
      exact Nat.eq_zero_of_le_zero (hm0 ▸ h1)
    have hmid2 : out.stats.middleIters2 = 0 := by
      have h1 : out.stats.middleIters2 = out.stats.dsGetPathCountW := hst3.2.2.2.2.2.2.1
      exact h1.trans hgpW0
    have hinn2 : out.stats.innerIters2 = 0 := by
      have h1 : (out.stats.innerIters2 : ℝ) ≤ (out.stats.dsGetPathCountW : ℝ) * wd.γ_ExpPath :=
        hst3.2.2.2.2.2.2.2.2.2.1
      rw [hgpW0, Nat.cast_zero, zero_mul] at h1
      exact Nat.cast_eq_zero.mp (le_antisymm h1 (Nat.cast_nonneg _))
    have hec0 : out.stats.econgUpdates = 0 := by
      have h1 : (out.stats.econgUpdates : ℝ) ≤ (out.stats.dsGetPathCountW : ℝ) * wd.γ_ExpPath :=
        hst3.2.2.2.2.2.2.2.2.2.2
      rw [hgpW0, Nat.cast_zero, zero_mul] at h1
      exact Nat.cast_eq_zero.mp (le_antisymm h1 (Nat.cast_nonneg _))
    have hinit2 : out.stats.dsInitCountW = 0 := by
      have h1 : out.stats.dsInitCountW = out.stats.η₂ * wd.comps.length := hst3.2.2.1
      rw [hcomps0, List.length_nil, Nat.mul_zero] at h1
      exact h1
    have hcost_eq : sparsifyLocalCost tools costs H' J embJH = J.n := by
      change J.n + J.m + wd.W.m + costs.decompose.callCost wd.J0_strip.m +
        (wd.comps.map _).sum +
        (out.stats.η₁ * (wd.comps.map _).sum + out.stats.dsGetPathCountJ * _) +
        (out.stats.dsInitCountJ + out.stats.middleIters1 + out.stats.innerIters1 +
          out.stats.vcongUpdates) +
        (out.stats.η₂ * (wd.comps.map _).sum + out.stats.dsGetPathCountW * _) +
        (out.stats.dsInitCountW + out.stats.middleIters2 + out.stats.innerIters2 +
          out.stats.econgUpdates) +
        ((∑ eW ∈ Finset.range wd.W.m, _) + (∑ eJ ∈ Finset.range J.m, _)) = J.n
      rw [hm0, hWm0, hJ0m, hcomps0, costs.decompose.callCost_zero,
        hgpJ0, hmid1, hinn1, hvc0, hinit1, hgpW0, hmid2, hinn2, hec0, hinit2]
      simp
    rw [hcost_eq, hm0, hJ0m, costs.decompose.callCost_zero]
    simp only [Nat.cast_zero, zero_mul, add_zero, zero_add]
    have hL1 : 1 ≤ 1 + Real.log ((J.n : ℝ) + 2) := by
      simpa using one_le_one_add_log J.n 0
    have hK_ge : 1 ≤ sparsifyBaseConst wd.c_deg costs * γ_t := by
      have h0 := sparsifyBaseConst_ge_one hcdeg costs
      nlinarith only [h0, hγt]
    have hn_nn : (0 : ℝ) ≤ J.n := Nat.cast_nonneg J.n
    have hn1 : (J.n : ℝ) ≤ sparsifyBaseConst wd.c_deg costs * γ_t * (J.n : ℝ) :=
      le_mul_of_one_le_left hn_nn hK_ge
    calc (J.n : ℝ) ≤ sparsifyBaseConst wd.c_deg costs * γ_t * (J.n : ℝ) := hn1
      _ ≤ (sparsifyBaseConst wd.c_deg costs * γ_t * (J.n : ℝ)) * (1 + Real.log ((J.n : ℝ) + 2)) :=
          le_mul_of_one_le_right (mul_nonneg (by linarith only [hK_ge]) hn_nn) hL1
      _ = sparsifyBaseConst wd.c_deg costs * γ_t * (J.n : ℝ) * (1 + Real.log ((J.n : ℝ) + 2)) := by ring
  · -- Case `1 ≤ J.m`: hence `1 ≤ length J embJH`.
    have hLen1 : 1 ≤ length J embJH := hLen hm_pos
    have hL_ge1 : (1 : ℝ) ≤ (length J embJH : ℝ) := by exact_mod_cast hLen1
    set L_JH : ℝ := (length J embJH : ℝ)
    set L_log : ℝ := 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)
    have hL_log1 : 1 ≤ L_log := one_le_one_add_log J.n J.m
    have hL_nn : 0 ≤ L_log := by linarith only [hL_log1]
    set γ_E : ℝ := wd.γ_ExpPath
    have hγ_nn : 0 ≤ γ_E := by linarith only [hγE_ge2]
    have hγE_le_γl : γ_E ≤ γ_ℓ := by
      have h1 : γ_E ≤ γ_E * γ_E := le_mul_of_one_le_right hγ_nn (by linarith only [hγE_ge2])
      simpa [γ_ℓ, sq] using h1
    have hγl_ge4 : 4 ≤ γ_ℓ := by
      have h1 : 4 ≤ γ_E * γ_E := le_trans (by norm_num) (mul_le_mul hγE_ge2 hγE_ge2 (by norm_num) hγ_nn)
      simpa [γ_ℓ, sq] using h1
    have hγl_le_sq : γ_ℓ ≤ γ_ℓ ^ 2 := by
      have h1 : γ_ℓ ≤ γ_ℓ * γ_ℓ := le_mul_of_one_le_right (by linarith only [hγl_ge4]) (by linarith only [hγl_ge4])
      simpa [sq] using h1
    have hγE_le_sq : γ_E ≤ γ_ℓ ^ 2 := le_trans hγE_le_γl hγl_le_sq
    have h1_le_sq : (1 : ℝ) ≤ γ_ℓ ^ 2 := le_trans (by linarith only [hγl_ge4]) hγl_le_sq
    have hm_nn : (0 : ℝ) ≤ J.m := Nat.cast_nonneg J.m
    have hn_nn : (0 : ℝ) ≤ J.n := Nat.cast_nonneg J.n
    set M_main : ℝ := (J.m : ℝ) * γ_ℓ ^ 2 * L_JH * L_log
    have hγ2_nn : 0 ≤ γ_ℓ ^ 2 := by linarith only [h1_le_sq]
    have hJ1_le_main : (J.m : ℝ) ≤ M_main := by
      have h1 : (J.m : ℝ) ≤ (J.m : ℝ) * γ_ℓ ^ 2 := le_mul_of_one_le_right hm_nn h1_le_sq
      have h2 : (J.m : ℝ) * γ_ℓ ^ 2 ≤ (J.m : ℝ) * γ_ℓ ^ 2 * L_JH :=
        le_mul_of_one_le_right (mul_nonneg hm_nn hγ2_nn) hL_ge1
      exact le_trans (le_trans h1 h2) (le_mul_of_one_le_right (mul_nonneg (mul_nonneg hm_nn hγ2_nn) (by linarith only [hL_ge1])) hL_log1)
    have hJE_le_main : (J.m : ℝ) * γ_E ≤ M_main := by
      have h1 : (J.m : ℝ) * γ_E ≤ (J.m : ℝ) * γ_ℓ ^ 2 := mul_le_mul_of_nonneg_left hγE_le_sq hm_nn
      have h2 : (J.m : ℝ) * γ_ℓ ^ 2 ≤ (J.m : ℝ) * γ_ℓ ^ 2 * L_JH :=
        le_mul_of_one_le_right (mul_nonneg hm_nn hγ2_nn) hL_ge1
      exact le_trans (le_trans h1 h2) (le_mul_of_one_le_right (mul_nonneg (mul_nonneg hm_nn hγ2_nn) (by linarith only [hL_ge1])) hL_log1)
    have hJsq_le_main : (J.m : ℝ) * γ_E ^ 2 ≤ M_main := by
      have hE2_le : γ_E ^ 2 ≤ γ_ℓ ^ 2 := by simpa [γ_ℓ] using hγl_le_sq
      have h1 : (J.m : ℝ) * γ_E ^ 2 ≤ (J.m : ℝ) * γ_ℓ ^ 2 := mul_le_mul_of_nonneg_left hE2_le hm_nn
      have h2 : (J.m : ℝ) * γ_ℓ ^ 2 ≤ (J.m : ℝ) * γ_ℓ ^ 2 * L_JH :=
        le_mul_of_one_le_right (mul_nonneg hm_nn hγ2_nn) hL_ge1
      exact le_trans (le_trans h1 h2) (le_mul_of_one_le_right (mul_nonneg (mul_nonneg hm_nn hγ2_nn) (by linarith only [hL_ge1])) hL_log1)
    have hJE2L_le_main : (J.m : ℝ) * γ_E ^ 2 * L_log ≤ M_main := by
      have hE2_le : γ_E ^ 2 ≤ γ_ℓ ^ 2 := by simpa [γ_ℓ] using hγl_le_sq
      have h1 : (J.m : ℝ) * γ_E ^ 2 ≤ (J.m : ℝ) * γ_ℓ ^ 2 * L_JH :=
        le_trans (mul_le_mul_of_nonneg_left hE2_le hm_nn)
          (le_mul_of_one_le_right (mul_nonneg hm_nn hγ2_nn) hL_ge1)
      have h2 := mul_le_mul_of_nonneg_right h1 hL_nn
      exact h2
    have hJEL_le_main : (J.m : ℝ) * γ_E * L_log ≤ M_main := by
      have h1 : (J.m : ℝ) * γ_E ≤ (J.m : ℝ) * γ_ℓ ^ 2 * L_JH :=
        le_trans (mul_le_mul_of_nonneg_left hγE_le_sq hm_nn)
          (le_mul_of_one_le_right (mul_nonneg hm_nn hγ2_nn) hL_ge1)
      have h2 := mul_le_mul_of_nonneg_right h1 hL_nn
      exact h2
    have hJELH_le_main : (J.m : ℝ) * γ_E ^ 2 * L_JH ≤ M_main := by
      have hE2_le : γ_E ^ 2 ≤ γ_ℓ ^ 2 := by simpa [γ_ℓ] using hγl_le_sq
      have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE2_le hm_nn) (by linarith only [hL_ge1])
      exact le_trans h1 (le_mul_of_one_le_right (mul_nonneg (mul_nonneg hm_nn hγ2_nn) (by linarith only [hL_ge1])) hL_log1)
    -- 1. `setupSteps = J.n + J.m + wd.W.m`
    have hsetup : ((J.n + J.m + wd.W.m : ℕ) : ℝ) ≤
        (J.n : ℝ) * L_log + (2 + wd.c_deg / 2) * M_main := by
      push_cast
      have hn_le : (J.n : ℝ) ≤ (J.n : ℝ) * L_log := le_mul_of_one_le_right hn_nn hL_log1
      have hm_le1 : (J.m : ℝ) ≤ (J.m : ℝ) * γ_E :=
        le_mul_of_one_le_right hm_nn (by linarith only [hγE_ge2])
      have hw_r : (wd.W.m : ℝ) ≤ (1 + wd.c_deg / 2) * ((J.m : ℝ) * γ_E) := by
        linarith only [hWm_gamma]
      have hw_le : (J.m : ℝ) + (wd.W.m : ℝ) ≤ (2 + wd.c_deg / 2) * ((J.m : ℝ) * γ_E) := by
        linarith only [hm_le1, hw_r]
      have hmul : (2 + wd.c_deg / 2) * ((J.m : ℝ) * γ_E) ≤ (2 + wd.c_deg / 2) * M_main :=
        mul_le_mul_of_nonneg_left hJE_le_main (by linarith only [hcdeg])
      linarith only [hn_le, hw_le, hmul]
    -- 2. `ceCharge`
    have hce :
        ((wd.comps.map fun c =>
          costs.constructExpander.callCost c.X.card
            (∑ k ∈ Finset.range c.X.card,
              ((wd.decomp.graphAt wd.J0_strip c.level).degIn c.X (c.verts.getD k 0) : ℝ) /
                (wd.φ_dec * (2 ^ c.level : ℝ)))).sum : ℝ) ≤
        2 * (costs.constructExpander.K_ce + 1) * M_main := by
      refine r_ceCharge_le costs.constructExpander.K_ce costs.constructExpander.callCost
        costs.constructExpander.hK_ce (fun n w hn hw0 => costs.constructExpander.callCost_le_of_one_le hn hw0)
        wd.decomp wd.J0_strip wd.φ_dec wd.comps J.m γ_E M_main ?_ hw.φ_dec_pos hφ_inv hγE_ge2 hvert_m hwsum
        (by exact le_trans (le_of_eq (by ring)) hJE_le_main)
      intro c hc
      obtain ⟨ci, hci, hceq⟩ := List.mem_iff_getElem.mp hc
      exact hceq ▸ (hw.comp_props ci hci).2.2.2.1
    -- 3. `dsJCharge`
    set C_eta1 : ℝ := 1 + (2 * wd.c_deg + 1) * ((wd.c_deg + 2) / Real.log 2 + 1)
    have hC_eta1_nn : 0 ≤ C_eta1 := by
      have hl2 := log_two_pos'
      exact add_nonneg (by norm_num) (mul_nonneg (by linarith only [hcdeg])
        (add_nonneg (div_nonneg (by linarith only [hcdeg]) hl2.le) (by norm_num)))
    have heta1_le : (out.stats.η₁ : ℝ) ≤ C_eta1 * γ_E * L_log :=
      le_trans (Nat.cast_le.mpr hst2.2.1) (eta1Bound_le_explicit tools H' J embJH hw hm_pos)
    have hgpJ_le : (out.stats.dsGetPathCountJ : ℝ) ≤ (1 + wd.c_deg / 2) * γ_E * (J.m : ℝ) :=
      le_trans (Nat.cast_le.mpr hst2.2.2.2.2.2.2.2.1) hWm_gamma
    have hγJq_ge1 : 1 ≤ tools.pathDS.γ_query wd.φ_dec wd.J0_strip.m :=
      le_trans (by linarith only [hγJ_ge2]) (tools.pathDS.hγ_query_ge wd.φ_dec wd.J0_strip.m hw.φ_dec_pos)
    have hdsJ :
        ((out.stats.η₁ * (wd.comps.map fun c =>
            costs.pathDS.updateCost c.J_sub.m (tools.pathDS.γ_query wd.φ_dec wd.J0_strip.m)).sum +
          out.stats.dsGetPathCountJ *
            costs.pathDS.queryCost (tools.pathDS.γ_query wd.φ_dec wd.J0_strip.m) : ℕ) : ℝ) ≤
        γ_t * (C_eta1 * (costs.pathDS.K_dsUpdate + 1) +
          (1 + wd.c_deg / 2) * (costs.pathDS.K_dsQuery + 1)) * M_main :=
      r_dsJCharge_le_with_time costs.pathDS wd.comps out.stats.η₁ out.stats.dsGetPathCountJ J.m
        (tools.pathDS.γ_query wd.φ_dec wd.J0_strip.m) γ_E wd.c_deg C_eta1 L_log M_main γ_t
        hγJq_ge1 hγJq hγt hγ_nn hsum_jm heta1_le hC_eta1_nn
        (by linarith only [hL_log1]) (by linarith only [hcdeg]) hgpJ_le hJE2L_le_main hJsq_le_main
    -- 4. `task2Steps`
    have htask2 : ((out.stats.dsInitCountJ + out.stats.middleIters1 + out.stats.innerIters1 +
          out.stats.vcongUpdates : ℕ) : ℝ) ≤
        (C_eta1 + (1 + wd.c_deg / 2) + 4 * (1 + wd.c_deg / 2)) * M_main := by
      push_cast
      have hinit_le : (out.stats.dsInitCountJ : ℝ) ≤ C_eta1 * M_main := by
        have h1 : (out.stats.dsInitCountJ : ℝ) = (out.stats.η₁ : ℝ) * (wd.comps.length : ℝ) := by
          exact_mod_cast hst2.2.2.2.1
        have h2 : (wd.comps.length : ℝ) ≤ (J.m : ℝ) := Nat.cast_le.mpr hst2.2.2.1
        have h3 : (out.stats.dsInitCountJ : ℝ) ≤ (C_eta1 * γ_E * L_log) * (J.m : ℝ) := by
          rw [h1]; exact mul_le_mul heta1_le h2 (Nat.cast_nonneg _) (by positivity)
        have heq : (C_eta1 * γ_E * L_log) * (J.m : ℝ) = C_eta1 * ((J.m : ℝ) * γ_E * L_log) := by ring
        rw [heq] at h3
        exact le_trans h3 (mul_le_mul_of_nonneg_left hJEL_le_main hC_eta1_nn)
      have hmid_le : (out.stats.middleIters1 : ℝ) ≤ (1 + wd.c_deg / 2) * M_main := by
        have h1 : (out.stats.middleIters1 : ℝ) = (out.stats.dsGetPathCountJ : ℝ) :=
          Nat.cast_inj.mpr hst2.2.2.2.2.2.2.2.2.1
        rw [h1]
        have heq : (1 + wd.c_deg / 2) * γ_E * (J.m : ℝ) = (1 + wd.c_deg / 2) * ((J.m : ℝ) * γ_E) := by ring
        have h2 : (out.stats.dsGetPathCountJ : ℝ) ≤ (1 + wd.c_deg / 2) * ((J.m : ℝ) * γ_E) := by
          linarith only [hgpJ_le, heq]
        exact le_trans h2 (mul_le_mul_of_nonneg_left hJE_le_main (by linarith only [hcdeg]))
      have hvc_prod : (out.stats.dsGetPathCountJ : ℝ) * (γ_E * (L_JH + 1)) ≤
          2 * (1 + wd.c_deg / 2) * M_main := by
        have hL2 : L_JH + 1 ≤ 2 * L_JH := by linarith only [hL_ge1]
        have h1 : (out.stats.dsGetPathCountJ : ℝ) * (γ_E * (L_JH + 1)) ≤
            ((1 + wd.c_deg / 2) * γ_E * (J.m : ℝ)) * (γ_E * (2 * L_JH)) :=
          mul_le_mul hgpJ_le (mul_le_mul_of_nonneg_left hL2 hγ_nn)
            (mul_nonneg hγ_nn (by linarith only [hL_ge1])) (by positivity)
        have heq : ((1 + wd.c_deg / 2) * γ_E * (J.m : ℝ)) * (γ_E * (2 * L_JH)) =
            2 * (1 + wd.c_deg / 2) * ((J.m : ℝ) * γ_E ^ 2 * L_JH) := by ring
        rw [heq] at h1
        exact le_trans h1 (mul_le_mul_of_nonneg_left hJELH_le_main (by linarith only [hcdeg]))
      have hinn_le : (out.stats.innerIters1 : ℝ) ≤ 2 * (1 + wd.c_deg / 2) * M_main :=
        le_trans hst2.2.2.2.2.2.2.2.2.2.2.2.2 hvc_prod
      have hvc_le : (out.stats.vcongUpdates : ℝ) ≤ 2 * (1 + wd.c_deg / 2) * M_main :=
        le_trans hst2.2.2.2.2.2.2.2.2.2.2.1 hvc_prod
      linarith only [hinit_le, hmid_le, hinn_le, hvc_le]
    -- 5. `dsWCharge`
    set C_eta2 : ℝ := 1 + 2 / Real.log 2
    have hC_eta2_nn : 0 ≤ C_eta2 := by
      have hl2 := log_two_pos'
      exact add_nonneg (by norm_num) (div_nonneg (by norm_num) hl2.le)
    have heta2_le : (out.stats.η₂ : ℝ) ≤ C_eta2 * L_log :=
      le_trans (Nat.cast_le.mpr hst3.2.1) (eta2Bound_le_explicit J)
    have hgpW_le : (out.stats.dsGetPathCountW : ℝ) ≤ (J.m : ℝ) :=
      Nat.cast_le.mpr hst3.2.2.2.2.2.1
    have hγWq_ge1 : 1 ≤ tools.pathDS.γ_query wd.φ_Const wd.M_W :=
      le_trans (by linarith only [hγW_ge2]) (tools.pathDS.hγ_query_ge wd.φ_Const wd.M_W hw.φ_Const_pos)
    have hdsW :
        ((out.stats.η₂ * (wd.comps.map fun c =>
            costs.pathDS.updateCost c.W_sub.m (tools.pathDS.γ_query wd.φ_Const wd.M_W)).sum +
          out.stats.dsGetPathCountW *
            costs.pathDS.queryCost (tools.pathDS.γ_query wd.φ_Const wd.M_W) : ℕ) : ℝ) ≤
        γ_t * (C_eta2 * (costs.pathDS.K_dsUpdate + 1) * (1 + wd.c_deg / 2) +
          (costs.pathDS.K_dsQuery + 1)) * M_main :=
      r_dsWCharge_le_with_time costs.pathDS wd.comps out.stats.η₂ out.stats.dsGetPathCountW wd.W.m J.m
        (tools.pathDS.γ_query wd.φ_Const wd.M_W) γ_E wd.c_deg C_eta2 L_log M_main γ_t
        hγWq_ge1 hγWq hγt hγ_nn hsum_Wm hWm_gamma heta2_le hC_eta2_nn
        (by linarith only [hL_log1]) (by linarith only [hcdeg]) hgpW_le hJE2L_le_main hJE_le_main
    -- 6. `task3Steps`
    have htask3 : ((out.stats.dsInitCountW + out.stats.middleIters2 + out.stats.innerIters2 +
          out.stats.econgUpdates : ℕ) : ℝ) ≤
        (C_eta2 + 1 + 2) * M_main := by
      push_cast
      have hinit_le : (out.stats.dsInitCountW : ℝ) ≤ C_eta2 * M_main := by
        have h1 : (out.stats.dsInitCountW : ℝ) = (out.stats.η₂ : ℝ) * (wd.comps.length : ℝ) := by
          exact_mod_cast hst3.2.2.1
        have h2 : (wd.comps.length : ℝ) ≤ (J.m : ℝ) := Nat.cast_le.mpr hst2.2.2.1
        have h3 : (out.stats.dsInitCountW : ℝ) ≤ (C_eta2 * L_log) * (J.m : ℝ) := by
          rw [h1]; exact mul_le_mul heta2_le h2 (Nat.cast_nonneg _) (by positivity)
        have h4 : (J.m : ℝ) * L_log ≤ M_main := by
          have h5 : (J.m : ℝ) ≤ (J.m : ℝ) * γ_ℓ ^ 2 * L_JH :=
            le_trans (le_mul_of_one_le_right hm_nn h1_le_sq)
              (le_mul_of_one_le_right (mul_nonneg hm_nn hγ2_nn) hL_ge1)
          have h6 := mul_le_mul_of_nonneg_right h5 hL_nn
          exact h6
        have heq : (C_eta2 * L_log) * (J.m : ℝ) = C_eta2 * ((J.m : ℝ) * L_log) := by ring
        rw [heq] at h3
        exact le_trans h3 (mul_le_mul_of_nonneg_left h4 hC_eta2_nn)
      have hmid_le : (out.stats.middleIters2 : ℝ) ≤ 1 * M_main := by
        have h1 : (out.stats.middleIters2 : ℝ) = (out.stats.dsGetPathCountW : ℝ) :=
          Nat.cast_inj.mpr hst3.2.2.2.2.2.2.1
        rw [h1]; linarith only [hgpW_le, hJ1_le_main]
      have hgp_gamma : (out.stats.dsGetPathCountW : ℝ) * γ_E ≤ 1 * M_main := by
        have h1 : (out.stats.dsGetPathCountW : ℝ) * γ_E ≤ (J.m : ℝ) * γ_E :=
          mul_le_mul_of_nonneg_right hgpW_le hγ_nn
        linarith only [h1, hJE_le_main]
      have hinn_le : (out.stats.innerIters2 : ℝ) ≤ 1 * M_main :=
        le_trans hst3.2.2.2.2.2.2.2.2.2.1 hgp_gamma
      have hec_le : (out.stats.econgUpdates : ℝ) ≤ 1 * M_main :=
        le_trans hst3.2.2.2.2.2.2.2.2.2.2 hgp_gamma
      linarith only [hinit_le, hmid_le, hinn_le, hec_le]
    -- 7. `returnSteps`
    have hret :
        (((∑ eW ∈ Finset.range wd.W.m, ((out.embWJ eW).edges.length + 1)) +
          (∑ eJ ∈ Finset.range J.m, ((out.embJJtilde eJ).edges.length + 1)) : ℕ) : ℝ) ≤
        (4 + wd.c_deg) * M_main := by
      have hlen_WJ : (length wd.W out.embWJ : ℝ) ≤ γ_E := hc88.2.2.2
      have hlen_JJtilde : (length J out.embJJtilde : ℝ) ≤ γ_E ^ 2 := by
        have hWJtilde_len : length wd.W out.embWJtilde ≤ length wd.W out.embWJ := by
          rw [length_le_iff]
          intro eW heWm
          change ((out.embWJ eW).mapEdges out.keptEdges.idxOf).edges.length ≤ _
          simp only [Walk.mapEdges, List.length_map]
          exact edges_length_le_length out.embWJ heWm
        have hJJ_nat : length J out.embJJtilde ≤ length J out.embJW * length wd.W out.embWJtilde :=
          length_compose_le fun eJ heJm eW heW => by
            rcases (hc810.1.2 eJ heJm).2.2 with ⟨_, hPe, _⟩ | ⟨_, _, _, _, hedges, _⟩
            · simp [hPe] at heW
            · exact hedges eW heW
        have hJJ_r : (length J out.embJJtilde : ℝ) ≤
            (length J out.embJW : ℝ) * (length wd.W out.embWJ : ℝ) := by
          exact_mod_cast le_trans hJJ_nat (Nat.mul_le_mul_left _ hWJtilde_len)
        have h1 : (length J out.embJW : ℝ) ≤ γ_E := hc810.2.2.2
        calc (length J out.embJJtilde : ℝ)
            ≤ (length J out.embJW : ℝ) * (length wd.W out.embWJ : ℝ) := hJJ_r
          _ ≤ γ_E * γ_E := mul_le_mul h1 hlen_WJ (Nat.cast_nonneg _) hγ_nn
          _ = γ_E ^ 2 := (sq _).symm
      refine r_returnSteps_le wd.W.m J.m out.embWJ out.embJJtilde wd.c_deg γ_E M_main
        hγE_ge2 (by linarith only [hcdeg]) ?_ ?_ hWm_gamma hJsq_le_main
      · intro eW heWm
        have h1 : ((out.embWJ eW).edges.length : ℝ) ≤ (length wd.W out.embWJ : ℝ) :=
          Nat.cast_le.mpr (edges_length_le_length out.embWJ heWm)
        linarith only [h1, hlen_WJ]
      · intro eJ heJm
        have h1 : ((out.embJJtilde eJ).edges.length : ℝ) ≤ (length J out.embJJtilde : ℝ) :=
          Nat.cast_le.mpr (edges_length_le_length out.embJJtilde heJm)
        linarith only [h1, hlen_JJtilde]
    -- Combine all components.
    have hcost_unfold : (sparsifyLocalCost tools costs H' J embJH : ℝ) =
        ((J.n + J.m + wd.W.m : ℕ) : ℝ) +
        (costs.decompose.callCost wd.J0_strip.m : ℝ) +
        ((wd.comps.map fun c =>
          costs.constructExpander.callCost c.X.card
            (∑ k ∈ Finset.range c.X.card,
              ((wd.decomp.graphAt wd.J0_strip c.level).degIn c.X (c.verts.getD k 0) : ℝ) /
                (wd.φ_dec * (2 ^ c.level : ℝ)))).sum : ℝ) +
        ((out.stats.η₁ * (wd.comps.map fun c =>
            costs.pathDS.updateCost c.J_sub.m (tools.pathDS.γ_query wd.φ_dec wd.J0_strip.m)).sum +
          out.stats.dsGetPathCountJ *
            costs.pathDS.queryCost (tools.pathDS.γ_query wd.φ_dec wd.J0_strip.m) : ℕ) : ℝ) +
        ((out.stats.dsInitCountJ + out.stats.middleIters1 + out.stats.innerIters1 +
          out.stats.vcongUpdates : ℕ) : ℝ) +
        ((out.stats.η₂ * (wd.comps.map fun c =>
            costs.pathDS.updateCost c.W_sub.m (tools.pathDS.γ_query wd.φ_Const wd.M_W)).sum +
          out.stats.dsGetPathCountW *
            costs.pathDS.queryCost (tools.pathDS.γ_query wd.φ_Const wd.M_W) : ℕ) : ℝ) +
        ((out.stats.dsInitCountW + out.stats.middleIters2 + out.stats.innerIters2 +
          out.stats.econgUpdates : ℕ) : ℝ) +
        (((∑ eW ∈ Finset.range wd.W.m, ((out.embWJ eW).edges.length + 1)) +
          (∑ eJ ∈ Finset.range J.m, ((out.embJJtilde eJ).edges.length + 1)) : ℕ) : ℝ) := by
      unfold sparsifyLocalCost
      push_cast
      rfl
    have hM_nn : 0 ≤ M_main := le_trans (by positivity) hJ1_le_main
    have hbase_ge1 : 1 ≤ sparsifyBaseConst wd.c_deg costs := sparsifyBaseConst_ge_one hcdeg costs
    have hgt_base : 1 ≤ sparsifyBaseConst wd.c_deg costs * γ_t := by
      nlinarith only [hbase_ge1, hγt]
    have hjn_bound : (J.n : ℝ) * L_log ≤
        sparsifyBaseConst wd.c_deg costs * γ_t * (J.n : ℝ) * L_log := by
      have h1 := le_mul_of_one_le_left (mul_nonneg hn_nn hL_nn) hgt_base
      exact le_trans h1 (le_of_eq (by ring))
    have hsetup' : ((J.n + J.m + wd.W.m : ℕ) : ℝ) ≤
        (J.n : ℝ) * L_log + γ_t * (2 + wd.c_deg / 2) * M_main := by
      have h1 : (2 + wd.c_deg / 2) * M_main ≤ γ_t * (2 + wd.c_deg / 2) * M_main := by
        have hb : 0 ≤ (2 + wd.c_deg / 2) * M_main := mul_nonneg (by linarith only [hcdeg]) hM_nn
        nlinarith only [hγt, hb]
      linarith only [hsetup, h1]
    have hce' :
        ((wd.comps.map fun c =>
          costs.constructExpander.callCost c.X.card
            (∑ k ∈ Finset.range c.X.card,
              ((wd.decomp.graphAt wd.J0_strip c.level).degIn c.X (c.verts.getD k 0) : ℝ) /
                (wd.φ_dec * (2 ^ c.level : ℝ)))).sum : ℝ) ≤
        γ_t * (2 * (costs.constructExpander.K_ce + 1)) * M_main := by
      have hb : 0 ≤ 2 * (costs.constructExpander.K_ce + 1) * M_main :=
        mul_nonneg (mul_nonneg (by norm_num) (by linarith [costs.constructExpander.hK_ce])) hM_nn
      nlinarith only [hce, hγt, hb]
    have htask2' : ((out.stats.dsInitCountJ + out.stats.middleIters1 + out.stats.innerIters1 +
          out.stats.vcongUpdates : ℕ) : ℝ) ≤
        γ_t * (C_eta1 + (1 + wd.c_deg / 2) + 4 * (1 + wd.c_deg / 2)) * M_main := by
      have hb : 0 ≤ (C_eta1 + (1 + wd.c_deg / 2) + 4 * (1 + wd.c_deg / 2)) * M_main :=
        mul_nonneg (by linarith only [hC_eta1_nn, hcdeg]) hM_nn
      nlinarith only [htask2, hγt, hb]
    have htask3' : ((out.stats.dsInitCountW + out.stats.middleIters2 + out.stats.innerIters2 +
          out.stats.econgUpdates : ℕ) : ℝ) ≤
        γ_t * (C_eta2 + 1 + 2) * M_main := by
      have hb : 0 ≤ (C_eta2 + 1 + 2) * M_main :=
        mul_nonneg (by linarith only [hC_eta2_nn]) hM_nn
      nlinarith only [htask3, hγt, hb]
    have hret' :
        (((∑ eW ∈ Finset.range wd.W.m, ((out.embWJ eW).edges.length + 1)) +
          (∑ eJ ∈ Finset.range J.m, ((out.embJJtilde eJ).edges.length + 1)) : ℕ) : ℝ) ≤
        γ_t * (4 + wd.c_deg) * M_main := by
      have hb : 0 ≤ (4 + wd.c_deg) * M_main := mul_nonneg (by linarith only [hcdeg]) hM_nn
      nlinarith only [hret, hγt, hb]
    have h_eq : sparsifyBaseConst wd.c_deg costs * γ_t =
        γ_t * (2 + wd.c_deg / 2) + γ_t * (2 * (costs.constructExpander.K_ce + 1)) +
          γ_t * (C_eta1 * (costs.pathDS.K_dsUpdate + 1) +
            (1 + wd.c_deg / 2) * (costs.pathDS.K_dsQuery + 1)) +
          γ_t * (C_eta1 + (1 + wd.c_deg / 2) + 4 * (1 + wd.c_deg / 2)) +
          γ_t * (C_eta2 * (costs.pathDS.K_dsUpdate + 1) * (1 + wd.c_deg / 2) +
            (costs.pathDS.K_dsQuery + 1)) +
          γ_t * (C_eta2 + 1 + 2) + γ_t * (4 + wd.c_deg) := by
      unfold sparsifyBaseConst
      dsimp only [C_eta1, C_eta2]
      ring
    have hsum_tot : (sparsifyLocalCost tools costs H' J embJH : ℝ) ≤
        (costs.decompose.callCost wd.J0_strip.m : ℝ) +
          sparsifyBaseConst wd.c_deg costs * γ_t * (J.n : ℝ) * L_log +
          sparsifyBaseConst wd.c_deg costs * γ_t * M_main := by
      rw [hcost_unfold]
      rw [h_eq] at hjn_bound ⊢
      linarith only [hsetup', hce', hdsJ, htask2', hdsW, htask3', hret', hjn_bound]
    exact le_trans hsum_tot (le_of_eq (by dsimp only [M_main, L_JH, L_log]; ring))

/-- **Theorem 8.1** operation-count bound when `γ_query = γ_ExpPath` (paper `[CS21]`-only regime). -/
theorem sparsifyLocalCost_le {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (costs : SpannerToolCosts)
    (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hNmax : J.n ≤ N_max)
    (hWmax : 2 * (J.m : ℝ) / tools.decompose.φ_dec (stripLoops J) ≤ W_max)
    (hLen : 1 ≤ J.m → 1 ≤ length J embJH)
    (hγq : ∀ φ M, 0 < φ → tools.pathDS.γ_query φ M = tools.pathDS.γ_ExpPath φ M) :
    let out := sparsifyLocal tools H' J embJH
    let wd := out.wd
    let γ_ℓ := wd.γ_ExpPath ^ 2
    (sparsifyLocalCost tools costs H' J embJH : ℝ) ≤
      (costs.decompose.callCost wd.J0_strip.m : ℝ) +
      sparsifyBaseConst wd.c_deg costs *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
  have hw := buildWitness_ok tools H' J embJH hJ hembJH hNmax hWmax
  let wd := (sparsifyLocal tools H' J embJH).wd
  have hJ_eq : tools.pathDS.γ_query wd.φ_dec wd.J0_strip.m =
      tools.pathDS.γ_ExpPath wd.φ_dec wd.J0_strip.m :=
    hγq wd.φ_dec wd.J0_strip.m hw.φ_dec_pos
  have hW_eq : tools.pathDS.γ_query wd.φ_Const wd.M_W =
      tools.pathDS.γ_ExpPath wd.φ_Const wd.M_W :=
    hγq wd.φ_Const wd.M_W hw.φ_Const_pos
  have h1 := sparsifyLocalCost_le_with_time tools costs H' J embJH hJ hembJH hNmax hWmax hLen
    1 le_rfl (by dsimp only [wd]; rw [hJ_eq, one_mul]; exact le_max_left _ _)
    (by dsimp only [wd]; rw [hW_eq, one_mul]; exact le_max_right _ _)
  simpa only [mul_one] using h1

/-- General **Theorem 8.1** operation-count bound using `γ_t = max γ_query` (honest with fallback). -/
theorem sparsifyLocalCost_le_of_query {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (costs : SpannerToolCosts)
    (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hNmax : J.n ≤ N_max)
    (hWmax : 2 * (J.m : ℝ) / tools.decompose.φ_dec (stripLoops J) ≤ W_max)
    (hLen : 1 ≤ J.m → 1 ≤ length J embJH) :
    let out := sparsifyLocal tools H' J embJH
    let wd := out.wd
    let γ_ℓ := wd.γ_ExpPath ^ 2
    let γ_q := max (tools.pathDS.γ_query wd.φ_dec wd.J0_strip.m)
      (tools.pathDS.γ_query wd.φ_Const wd.M_W)
    (sparsifyLocalCost tools costs H' J embJH : ℝ) ≤
      (costs.decompose.callCost wd.J0_strip.m : ℝ) +
      sparsifyBaseConst wd.c_deg costs * γ_q *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
  have hw := buildWitness_ok tools H' J embJH hJ hembJH hNmax hWmax
  let wd := buildWitness tools H' J embJH
  let γ_q := max (tools.pathDS.γ_query wd.φ_dec wd.J0_strip.m)
    (tools.pathDS.γ_query wd.φ_Const wd.M_W)
  have hγE_ge1 : 1 ≤ wd.γ_ExpPath := by
    have hp : 0 < wd.φ_ds := hw.φ_ds_pos
    have hh : wd.φ_ds ≤ 1 / 2 := hw.φ_ds_half
    have h2 : (2 : ℝ) ≤ 1 / wd.φ_ds := by rw [le_div_iff₀ hp]; nlinarith
    have hge : 1 / wd.φ_ds ≤ wd.γ_ExpPath := hw.γ_ExpPath_ge
    linarith
  have hqJ : tools.pathDS.γ_ExpPath wd.φ_dec wd.J0_strip.m ≤ γ_q :=
    le_trans (tools.pathDS.hγ_query_ge wd.φ_dec wd.J0_strip.m hw.φ_dec_pos) (le_max_left _ _)
  have h1_J : 1 ≤ tools.pathDS.γ_ExpPath wd.φ_dec wd.J0_strip.m := by
    have h2 := tools.pathDS.hγ_ExpPath_ge wd.φ_dec wd.J0_strip.m hw.φ_dec_pos
    have hhalf := tools.pathDS.hφ_half wd.φ_dec wd.J0_strip.m hw.φ_dec_pos
    have hpos := tools.pathDS.hφ_pos wd.φ_dec wd.J0_strip.m hw.φ_dec_pos
    have h12 : (2 : ℝ) ≤ 1 / tools.pathDS.φ_out wd.φ_dec wd.J0_strip.m := by
      rw [le_div_iff₀ hpos]; nlinarith
    linarith
  have hγq_ge1 : 1 ≤ γ_q := le_trans h1_J hqJ
  have hγq_nn : 0 ≤ γ_q := by linarith
  exact sparsifyLocalCost_le_with_time tools costs H' J embJH hJ hembJH hNmax hWmax hLen
    γ_q hγq_ge1
    (le_trans (le_max_left _ _) (le_mul_of_one_le_right hγq_nn hγE_ge1))
    (le_trans (le_max_right _ _) (le_mul_of_one_le_right hγq_nn hγE_ge1))

/-! ## Monotonicity conditions and uniform `M`-cap parameters -/

/-- Lower bound `φ_lb(m) ≤ φ_dec(G)` in terms of `G.m`, needed to obtain uniform parameters
(`γ_c`, `γ_ℓ`) independent of the individual graph `J` for all graphs with `J.m ≤ M`. -/
structure DecomposeMonotone (dec : DecomposeTool) where
  φ_lb : ℕ → ℝ
  hφ_lb_pos : ∀ m, 0 < φ_lb m
  hφ_lb_le : ∀ m, φ_lb m ≤ 1
  hφ_lb_anti : ∀ ⦃m₁ m₂ : ℕ⦄, m₁ ≤ m₂ → φ_lb m₂ ≤ φ_lb m₁
  hφ_dec_ge : ∀ G : Graph, G.IsValid → G.IsLoopless → φ_lb G.m ≤ dec.φ_dec G

/-- Monotonicity of `PathDSTool`'s parameters in `(φ_in, M)`:
`φ_out` is monotone nondecreasing in `φ_in` and antitone in `M`, while `γ_ExpPath`, `γ_query`,
and `γ_del` are antitone in `φ_in` and monotone nondecreasing in `M`. -/
structure PathDSMonotone (pds : PathDSTool) where
  hφ_out_mono : ∀ ⦃φ₁ φ₂ : ℝ⦄ ⦃M₁ M₂ : ℕ⦄,
    0 < φ₁ → φ₁ ≤ φ₂ → φ₂ ≤ 1 → M₁ ≤ M₂ → pds.φ_out φ₁ M₂ ≤ pds.φ_out φ₂ M₁
  hγ_ExpPath_mono : ∀ ⦃φ₁ φ₂ : ℝ⦄ ⦃M₁ M₂ : ℕ⦄,
    0 < φ₁ → φ₁ ≤ φ₂ → φ₂ ≤ 1 → M₁ ≤ M₂ → pds.γ_ExpPath φ₂ M₁ ≤ pds.γ_ExpPath φ₁ M₂
  hγ_query_mono : ∀ ⦃φ₁ φ₂ : ℝ⦄ ⦃M₁ M₂ : ℕ⦄,
    0 < φ₁ → φ₁ ≤ φ₂ → φ₂ ≤ 1 → M₁ ≤ M₂ → pds.γ_query φ₂ M₁ ≤ pds.γ_query φ₁ M₂
  hγ_del_mono : ∀ ⦃φ₁ φ₂ : ℝ⦄ ⦃M₁ M₂ : ℕ⦄,
    0 < φ₁ → φ₁ ≤ φ₂ → φ₂ ≤ 1 → M₁ ≤ M₂ → pds.γ_del φ₂ M₁ ≤ pds.γ_del φ₁ M₂

/-- Worst-case `M_W` cap for witness expanders when `J.m ≤ M` and `φ_min ≤ φ_dec`. -/
noncomputable def capM_W (c_deg φ_min : ℝ) (M : ℕ) : ℕ :=
  Nat.ceil (c_deg * (M : ℝ) / φ_min) + 1

/-- Uniform lower bound on `wd.φ_ds` for graphs with `J.m ≤ M` and `φ_min ≤ φ_dec`. -/
noncomputable def capPhiDS (c_deg φ_Const : ℝ) (pds : PathDSTool) (φ_min : ℝ) (M : ℕ) : ℝ :=
  min (pds.φ_out φ_min M) (pds.φ_out φ_Const (capM_W c_deg φ_min M))

/-- Uniform upper bound on `wd.γ_ExpPath` for graphs with `J.m ≤ M` and `φ_min ≤ φ_dec`. -/
noncomputable def capGammaExpPath (c_deg φ_Const : ℝ) (pds : PathDSTool) (φ_min : ℝ) (M : ℕ) : ℝ :=
  max (pds.γ_ExpPath φ_min M) (pds.γ_ExpPath φ_Const (capM_W c_deg φ_min M))

/-- Uniform upper bound on `γ_query` for graphs with `J.m ≤ M` and `φ_min ≤ φ_dec`. -/
noncomputable def capGammaQuery (c_deg φ_Const : ℝ) (pds : PathDSTool) (φ_min : ℝ) (M : ℕ) : ℝ :=
  max (pds.γ_query φ_min M) (pds.γ_query φ_Const (capM_W c_deg φ_min M))

theorem capGammaExpPath_le_capGammaQuery {c_deg φ_Const : ℝ} {pds : PathDSTool} {φ_min : ℝ}
    (hφC : 0 < φ_Const) (hφm : 0 < φ_min) (M : ℕ) :
    capGammaExpPath c_deg φ_Const pds φ_min M ≤ capGammaQuery c_deg φ_Const pds φ_min M :=
  max_le_max (pds.hγ_query_ge φ_min M hφm) (pds.hγ_query_ge φ_Const _ hφC)

/-- Uniform upper bound on `wd.γ_del` for graphs with `J.m ≤ M` and `φ_min ≤ φ_dec`. -/
noncomputable def capGammaDel (c_deg φ_Const : ℝ) (pds : PathDSTool) (φ_min : ℝ) (M : ℕ) : ℝ :=
  max (pds.γ_del φ_min M) (pds.γ_del φ_Const (capM_W c_deg φ_min M))

/-- Uniform length factor `γ_ℓ = γ_ExpPath²` at edge cap `M`. -/
noncomputable def capGammaL (c_deg φ_Const : ℝ) (pds : PathDSTool) (φ_min : ℝ) (M : ℕ) : ℝ :=
  (capGammaExpPath c_deg φ_Const pds φ_min M) ^ 2

/-- Uniform `η₁` round bound at edge cap `M`. -/
noncomputable def capEta1 (c_deg φ_min : ℝ) (M : ℕ) : ℕ :=
  1 + Nat.ceil (2 * c_deg) * (Nat.log 2 (Nat.ceil (c_deg * (M : ℝ) / (2 * φ_min)) + 1) + 1)

/-- Uniform `η₂` round bound at edge cap `M`. -/
def capEta2 (M : ℕ) : ℕ :=
  1 + 2 * (Nat.log 2 (M + 1) + 1)

/-- Uniform congestion factor `γ_c = 2 (η₁ + 1/2)(η₂ + 1/2) γ_ExpPath² γ_del² / φ_ds²` at edge cap `M`. -/
noncomputable def capGammaC (c_deg φ_Const : ℝ) (pds : PathDSTool) (φ_min : ℝ) (M : ℕ) : ℝ :=
  2 * ((capEta1 c_deg φ_min M : ℝ) + 1 / 2) * ((capEta2 M : ℝ) + 1 / 2) *
    (capGammaExpPath c_deg φ_Const pds φ_min M) ^ 2 *
    (capGammaDel c_deg φ_Const pds φ_min M) ^ 2 /
    (capPhiDS c_deg φ_Const pds φ_min M) ^ 2

theorem capPhiDS_pos {c_deg φ_Const : ℝ} {pds : PathDSTool} {φ_min : ℝ}
    (hφC : 0 < φ_Const) (hφm : 0 < φ_min) (M : ℕ) :
    0 < capPhiDS c_deg φ_Const pds φ_min M :=
  lt_min (pds.hφ_pos φ_min M hφm) (pds.hφ_pos φ_Const _ hφC)

theorem capPhiDS_half {c_deg φ_Const : ℝ} {pds : PathDSTool} {φ_min : ℝ}
    (hφm : 0 < φ_min) (M : ℕ) :
    capPhiDS c_deg φ_Const pds φ_min M ≤ 1 / 2 :=
  le_trans (min_le_left _ _) (pds.hφ_half φ_min M hφm)

theorem two_le_capGammaExpPath {c_deg φ_Const : ℝ} {pds : PathDSTool} {φ_min : ℝ}
    (_hφC : 0 < φ_Const) (hφm : 0 < φ_min) (M : ℕ) :
    2 ≤ capGammaExpPath c_deg φ_Const pds φ_min M := by
  have hpos := pds.hφ_pos φ_min M hφm
  have hhalf := pds.hφ_half φ_min M hφm
  have h1 : (2 : ℝ) ≤ 1 / pds.φ_out φ_min M := by rw [le_div_iff₀ hpos]; nlinarith
  exact le_trans h1 (le_trans (pds.hγ_ExpPath_ge φ_min M hφm) (le_max_left _ _))

theorem one_le_capGammaDel {c_deg φ_Const : ℝ} {pds : PathDSTool} {φ_min : ℝ}
    (hφm : 0 < φ_min) (M : ℕ) :
    1 ≤ capGammaDel c_deg φ_Const pds φ_min M :=
  le_trans (pds.hγ_del_ge φ_min M hφm) (le_max_left _ _)

theorem four_le_capGammaL {c_deg φ_Const : ℝ} {pds : PathDSTool} {φ_min : ℝ}
    (hφC : 0 < φ_Const) (hφm : 0 < φ_min) (M : ℕ) :
    4 ≤ capGammaL c_deg φ_Const pds φ_min M := by
  have h2 := two_le_capGammaExpPath (c_deg := c_deg) (φ_Const := φ_Const) (pds := pds) hφC hφm M
  unfold capGammaL
  nlinarith

theorem one_le_capGammaC {c_deg φ_Const : ℝ} {pds : PathDSTool} {φ_min : ℝ}
    (hφC : 0 < φ_Const) (hφm : 0 < φ_min) (M : ℕ) :
    1 ≤ capGammaC c_deg φ_Const pds φ_min M := by
  unfold capGammaC
  have hφ_pos : 0 < capPhiDS c_deg φ_Const pds φ_min M := capPhiDS_pos hφC hφm M
  have hφ_half : capPhiDS c_deg φ_Const pds φ_min M ≤ 1 / 2 := capPhiDS_half hφm M
  have hγE : 2 ≤ capGammaExpPath c_deg φ_Const pds φ_min M := two_le_capGammaExpPath hφC hφm M
  have hγd : 1 ≤ capGammaDel c_deg φ_Const pds φ_min M := one_le_capGammaDel hφm M
  have hη₁ : (1 : ℝ) ≤ (capEta1 c_deg φ_min M : ℝ) := by
    unfold capEta1; exact_mod_cast (by omega : 1 ≤ 1 + _)
  have hη₂ : (1 : ℝ) ≤ (capEta2 M : ℝ) := by
    unfold capEta2; exact_mod_cast (by omega : 1 ≤ 1 + _)
  have hφ_sq : (capPhiDS c_deg φ_Const pds φ_min M) ^ 2 ≤ 1 / 4 := by nlinarith
  have hnum : 1 ≤ 2 * ((capEta1 c_deg φ_min M : ℝ) + 1 / 2) * ((capEta2 M : ℝ) + 1 / 2) *
      (capGammaExpPath c_deg φ_Const pds φ_min M) ^ 2 *
      (capGammaDel c_deg φ_Const pds φ_min M) ^ 2 := by
    have h1 : 1 ≤ (capGammaExpPath c_deg φ_Const pds φ_min M) ^ 2 := by nlinarith
    have h2 : 1 ≤ (capGammaDel c_deg φ_Const pds φ_min M) ^ 2 := by nlinarith
    have hη : 1 ≤ ((capEta1 c_deg φ_min M : ℝ) + 1 / 2) * ((capEta2 M : ℝ) + 1 / 2) := by nlinarith
    have hγ : 1 ≤ (capGammaExpPath c_deg φ_Const pds φ_min M) ^ 2 *
        (capGammaDel c_deg φ_Const pds φ_min M) ^ 2 := by nlinarith
    nlinarith
  rw [one_le_div (sq_pos_of_pos hφ_pos)]
  linarith

section CapComparison

theorem cap_bounds_of_le {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (_hJ : J.IsValid)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    (hpds : PathDSMonotone tools.pathDS)
    {M : ℕ} {φ_min : ℝ}
    (hJm : J.m ≤ M) (hφ_pos : 0 < φ_min)
    (hφ_dec_ge : φ_min ≤ (buildWitness tools H' J embJH).φ_dec) :
    let wd := buildWitness tools H' J embJH
    capPhiDS wd.c_deg wd.φ_Const tools.pathDS φ_min M ≤ wd.φ_ds ∧
    wd.γ_ExpPath ≤ capGammaExpPath wd.c_deg wd.φ_Const tools.pathDS φ_min M ∧
    wd.γ_del ≤ capGammaDel wd.c_deg wd.φ_Const tools.pathDS φ_min M ∧
    eta1Bound wd J ≤ capEta1 wd.c_deg φ_min M ∧
    eta2Bound J ≤ capEta2 M := by
  intro wd
  have hm_strip : wd.J0_strip.m ≤ M := le_trans (stripLoops_m_le J) hJm
  have hMW_le : wd.M_W ≤ capM_W wd.c_deg φ_min M := by
    have h1 : wd.c_deg * (wd.J0_strip.m : ℝ) / wd.φ_dec ≤ wd.c_deg * (M : ℝ) / φ_min := by
      have hc : 0 ≤ wd.c_deg := le_trans (by norm_num) hw.c_deg_ge
      have hm_r : (wd.J0_strip.m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm_strip
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hm_r hc) hφ_pos hφ_dec_ge
    unfold capM_W
    change Nat.ceil (wd.c_deg * (wd.J0_strip.m : ℝ) / wd.φ_dec) + 1 ≤
      Nat.ceil (wd.c_deg * (M : ℝ) / φ_min) + 1
    exact Nat.add_le_add_right (Nat.ceil_mono h1) 1
  have hφ_J : tools.pathDS.φ_out φ_min M ≤ tools.pathDS.φ_out wd.φ_dec wd.J0_strip.m :=
    hpds.hφ_out_mono hφ_pos hφ_dec_ge hw.φ_dec_le hm_strip
  have hφ_W : tools.pathDS.φ_out wd.φ_Const (capM_W wd.c_deg φ_min M) ≤
      tools.pathDS.φ_out wd.φ_Const wd.M_W :=
    hpds.hφ_out_mono hw.φ_Const_pos le_rfl hw.φ_Const_le hMW_le
  have hφ_ds : capPhiDS wd.c_deg wd.φ_Const tools.pathDS φ_min M ≤ wd.φ_ds :=
    min_le_min hφ_J hφ_W
  have hγE_J : tools.pathDS.γ_ExpPath wd.φ_dec wd.J0_strip.m ≤ tools.pathDS.γ_ExpPath φ_min M :=
    hpds.hγ_ExpPath_mono hφ_pos hφ_dec_ge hw.φ_dec_le hm_strip
  have hγE_W : tools.pathDS.γ_ExpPath wd.φ_Const wd.M_W ≤
      tools.pathDS.γ_ExpPath wd.φ_Const (capM_W wd.c_deg φ_min M) :=
    hpds.hγ_ExpPath_mono hw.φ_Const_pos le_rfl hw.φ_Const_le hMW_le
  have hγE : wd.γ_ExpPath ≤ capGammaExpPath wd.c_deg wd.φ_Const tools.pathDS φ_min M :=
    max_le_max hγE_J hγE_W
  have hγd_J : tools.pathDS.γ_del wd.φ_dec wd.J0_strip.m ≤ tools.pathDS.γ_del φ_min M :=
    hpds.hγ_del_mono hφ_pos hφ_dec_ge hw.φ_dec_le hm_strip
  have hγd_W : tools.pathDS.γ_del wd.φ_Const wd.M_W ≤
      tools.pathDS.γ_del wd.φ_Const (capM_W wd.c_deg φ_min M) :=
    hpds.hγ_del_mono hw.φ_Const_pos le_rfl hw.φ_Const_le hMW_le
  have hγd : wd.γ_del ≤ capGammaDel wd.c_deg wd.φ_Const tools.pathDS φ_min M :=
    max_le_max hγd_J hγd_W
  have heta1 : eta1Bound wd J ≤ capEta1 wd.c_deg φ_min M := by
    unfold eta1Bound capEta1
    have hdiv : wd.c_deg * (J.m : ℝ) / (2 * wd.φ_dec) ≤ wd.c_deg * (M : ℝ) / (2 * φ_min) := by
      have hc : 0 ≤ wd.c_deg := le_trans (by norm_num) hw.c_deg_ge
      have hm_r : (J.m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hJm
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hm_r hc)
        (by linarith) (by linarith)
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (Nat.log_mono_right (Nat.add_le_add_right (Nat.ceil_mono hdiv) 1)) 1)) 1
  have heta2 : eta2Bound J ≤ capEta2 M := by
    unfold eta2Bound capEta2
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.add_le_add_right
      (Nat.log_mono_right (by omega)) 1)) 1
  exact ⟨hφ_ds, hγE, hγd, heta1, heta2⟩

theorem capGammaQuery_bounds_of_le {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    (hpds : PathDSMonotone tools.pathDS)
    {φ_min : ℝ} {M : ℕ} (hJm : J.m ≤ M)
    (hφ_pos : 0 < φ_min) (hφ_dec_ge : φ_min ≤ (buildWitness tools H' J embJH).φ_dec) :
    let wd := buildWitness tools H' J embJH
    tools.pathDS.γ_query wd.φ_dec wd.J0_strip.m ≤
      capGammaQuery wd.c_deg wd.φ_Const tools.pathDS φ_min M ∧
    tools.pathDS.γ_query wd.φ_Const wd.M_W ≤
      capGammaQuery wd.c_deg wd.φ_Const tools.pathDS φ_min M := by
  intro wd
  have hJ0_m : wd.J0_strip.m ≤ M := le_trans (stripLoops_m_le J) hJm
  have hMW_le : wd.M_W ≤ capM_W wd.c_deg φ_min M := by
    unfold capM_W
    have hdiv : wd.c_deg * (wd.J0_strip.m : ℝ) / wd.φ_dec ≤ wd.c_deg * (M : ℝ) / φ_min := by
      have hc : 0 ≤ wd.c_deg := le_trans (by norm_num) hw.c_deg_ge
      have hm_r : (wd.J0_strip.m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hJ0_m
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hm_r hc)
        hφ_pos hφ_dec_ge
    change Nat.ceil (wd.c_deg * (wd.J0_strip.m : ℝ) / wd.φ_dec) + 1 ≤
      Nat.ceil (wd.c_deg * (M : ℝ) / φ_min) + 1
    exact Nat.add_le_add_right (Nat.ceil_mono hdiv) 1
  have _ := hJ
  have hqJ : tools.pathDS.γ_query wd.φ_dec wd.J0_strip.m ≤
      capGammaQuery wd.c_deg wd.φ_Const tools.pathDS φ_min M :=
    le_trans (hpds.hγ_query_mono hφ_pos hφ_dec_ge hw.φ_dec_le hJ0_m) (le_max_left _ _)
  have hqW : tools.pathDS.γ_query wd.φ_Const wd.M_W ≤
      capGammaQuery wd.c_deg wd.φ_Const tools.pathDS φ_min M :=
    le_trans (hpds.hγ_query_mono hw.φ_Const_pos le_rfl hw.φ_Const_le hMW_le) (le_max_right _ _)
  exact ⟨hqJ, hqW⟩

end CapComparison

end MinCostFlow.Spanner
