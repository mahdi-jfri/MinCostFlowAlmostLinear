module

public import MinCostFlow.SparseCore.CompLSFBridge
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# MWU Average Stretch Bound for General `LSFInit` (`CompLSFMWUWith`)

Generalizes `compLSF_mwu_bound` (`MinCostFlow.SparseCore.CompLSFBridge`) to any `lsfInit : LSFInit`
satisfying `IsApproxMWUInit lsfInit C_lsst α K_σ K_ρ` (`1 ≤ K_ρ`), via `LSF.lemma_5_5_approx_explicit`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain

@[expose] public section

private lemma log_three_ge_one_mwu : (1 : ℝ) ≤ Real.log 3 := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])

/-- MWU average stretch bound for `initCompLSFWith lsfInit` under `IsApproxMWUInit`. -/
theorem compLSF_mwu_bound_with
    (lsfInit : LSFInit) (C_lsst α K_σ K_ρ : ℝ) (hKρ : 1 ≤ K_ρ)
    (hApprox : IsApproxMWUInit lsfInit C_lsst α K_σ K_ρ)
    (G₀ : MGraph) (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (ℓ₀ : ℕ → ℝ) (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    (k : ℕ) (hk : 1 ≤ k) (U : List Update) (hU : G₀.BatchIsValid U) :
    let K₀ := max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240)
    let K := 3 * K_ρ * K₀
    let cs := fun j => compLSFBatch (initCompLSFWith lsfInit G₀ ℓ₀ k j) U
    ∀ e ∈ (G₀.applyBatch U).E,
      ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (cs j).wstrGlobal e ≤
        K * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 * Real.log ((G₀.m : ℝ) + 2) := by
  intro K₀ K cs e he
  classical
  have hI0 : ∀ j < k, CompLSFInv (max C_lsst (K_σ / 6272)) ℓ₀ (initCompLSFWith lsfInit G₀ ℓ₀ k j) :=
    fun j hj => compLSFInv_initWith (hApprox.toValidLSFInitFor hj) hG₀ hV₀ hℓ₀ hk
  have hsp0 := fun j (hj : j < k) => compLSFBatch_step_props U (hI0 j hj) hU
  have he_0 : e ∈ (cs 0).G.E := by rwa [compLSFBatch_G]
  have h2240_le : (2240 : ℝ) ≤ K₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hn₀_pos : 1 ≤ G₀.n := Finset.card_pos.mpr hV₀
  have hlog3 : (1 : ℝ) ≤ Real.log ((G₀.n : ℝ) + 2) := by
    refine le_trans log_three_ge_one_mwu (Real.log_le_log (by norm_num) ?_)
    have : (1 : ℝ) ≤ G₀.n := by exact_mod_cast hn₀_pos
    linarith
  have hlog6 : (1 : ℝ) ≤ (Real.log ((G₀.n : ℝ) + 2)) ^ 6 := one_le_pow₀ hlog3
  have hlogm : (1 / 2 : ℝ) < Real.log ((G₀.m : ℝ) + 2) := half_lt_log_add_two G₀.m
  by_cases heI : e ∈ (cs 0).insertedGlobal
  · have heIj : ∀ j, e ∈ (cs j).insertedGlobal := fun j => by
      have h0 : (cs 0).insertedGlobal = U.foldl updateInserted ∅ :=
        compLSFBatch_insertedGlobal _ U
      have hj : (cs j).insertedGlobal = U.foldl updateInserted ∅ :=
        compLSFBatch_insertedGlobal _ U
      rwa [hj, ← h0]
    have hw1 : ∀ j ∈ Finset.range k, (cs j).wstrGlobal e = 1 := fun j hj =>
      ((hsp0 j (Finset.mem_range.mp hj)).1.hIns_wstr_R e (heIj j)).1
    have hsum1 : ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (cs j).wstrGlobal e = 1 := by
      calc ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (cs j).wstrGlobal e
          = ∑ _ ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) :=
            Finset.sum_congr rfl fun j hj => by rw [hw1 j hj, mul_one]
        _ = (k : ℝ) * ((1 : ℝ) / (k : ℝ)) := by simp
        _ = 1 := mul_one_div_cancel hk_pos.ne'
    rw [hsum1]
    have hK_ge : 128 ≤ K := by dsimp [K]; nlinarith
    have hK_log6 : 128 ≤ K * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 := by nlinarith
    nlinarith
  · obtain ⟨C, hC_G0, heC0, hniC0, _⟩ := (hsp0 0 hk).1.hWstr_surv e he_0 heI
    have hC : C ∈ components G₀ := by
      rwa [compLSFBatch_G₀ (initCompLSFWith lsfInit G₀ ℓ₀ k 0) U] at hC_G0
    have hCG₀ : e ∈ (compGraph G₀ C).E := by
      have hs := ((hsp0 0 hk).1.hCompLSF C hC_G0).1.hsurv_edge e heC0 hniC0 |>.1
      rwa [((hsp0 0 hk).1.hCompLSF C hC_G0).2.1, compLSFBatch_G₀] at hs
    set U_C := projCompBatchG G₀ (compGraph G₀ C) U
    have hGC_val := compGraph_isValid hG₀ hC
    have hGC_ne := compGraph_nonempty hC
    set ℓs := safeLen G₀ ℓ₀
    have hℓC : ∀ f ∈ (compGraph G₀ C).E, 0 < ℓs f := fun f hf => by
      have hfG : f ∈ G₀.E := Finset.filter_subset _ _ hf
      rw [show ℓs f = ℓ₀ f from safeLen_eq_of_mem ℓ₀ hfG]
      exact hℓ₀ f hfG
    have hG_comp0 : ((initCompLSFWith lsfInit G₀ ℓ₀ k 0).compSt C).G = compGraph G₀ C :=
      (initCompLSFWith_compSt_basic (hApprox.toValidLSFInitFor hk) hG₀ hℓ₀ hk hC).2.1
    have hBU_C : (compGraph G₀ C).BatchIsValid U_C := by
      have h1 := (compLSFBatch_compSt (hI0 0 hk) hU hC).2.2.1
      change ((initCompLSFWith lsfInit G₀ ℓ₀ k 0).compSt C).G.BatchIsValid
        (projCompBatchG G₀ ((initCompLSFWith lsfInit G₀ ℓ₀ k 0).compSt C).G U) at h1
      rwa [hG_comp0] at h1
    have he_UC : e ∈ ([U_C].foldl MGraph.applyBatch (compGraph G₀ C)).E := by
      rw [List.foldl_cons, List.foldl_nil]
      have hGeq := (compLSFBatch_compSt (hI0 0 hk) hU hC).2.1
      change e ∈ ((cs 0).compSt C).G.E at heC0
      rw [hGeq] at heC0
      change e ∈ (((initCompLSFWith lsfInit G₀ ℓ₀ k 0).compSt C).G.applyBatch
        (projCompBatchG G₀ ((initCompLSFWith lsfInit G₀ ℓ₀ k 0).compSt C).G U)).E at heC0
      rwa [hG_comp0] at heC0
    let ℓ_C : ℕ → ℝ := fun f =>
      if f ∈ (compGraph G₀ C).E ∧ f ∉ batchesInserted [U_C] then ℓs f else 1
    have hℓ_pos : ∀ f ∈ ([U_C].foldl MGraph.applyBatch (compGraph G₀ C)).E, 0 < ℓ_C f :=
      fun f _ => by dsimp only [ℓ_C]; split_ifs with hf; exact hℓC f hf.1; exact zero_lt_one
    have hℓ_orig : ∀ f ∈ (compGraph G₀ C).E,
        f ∈ ([U_C].foldl MGraph.applyBatch (compGraph G₀ C)).E →
        f ∉ batchesInserted [U_C] → ℓ_C f = ℓs f :=
      fun f hf _ hni => by simp [ℓ_C, hf, hni]
    obtain ⟨thresh, ρ, δ, v, T_raw, r₀, C_reps, π, W_T, hρ_lo, hρ_hi, hδ0, hδ1, hv0, hv_pos,
      hp, hv_step, hInitEq⟩ := hApprox (compGraph G₀ C) ℓs k hGC_val hGC_ne hℓC hk
    have hw_eq : ∀ j < k, (cs j).wstrGlobal e =
        (applyLSFBatches (initLSFWith (compGraph G₀ C) ℓs (v j) (k : ℝ) (T_raw j) (r₀ j)
          (C_reps j) (π j) (W_T j) thresh) [U_C]).wstr e := by
      intro j hj
      have heIj : e ∉ (cs j).insertedGlobal := by
        have h0 : (cs 0).insertedGlobal = U.foldl updateInserted ∅ :=
          compLSFBatch_insertedGlobal _ U
        have hj' : (cs j).insertedGlobal = U.foldl updateInserted ∅ :=
          compLSFBatch_insertedGlobal _ U
        rwa [hj', ← h0]
      have he_j : e ∈ (cs j).G.E := by rwa [compLSFBatch_G]
      obtain ⟨Cj, hCj_G0, heCj, hniCj, hwCj⟩ := (hsp0 j hj).1.hWstr_surv e he_j heIj
      have hCj : Cj ∈ components G₀ := by
        rwa [compLSFBatch_G₀ (initCompLSFWith lsfInit G₀ ℓ₀ k j) U] at hCj_G0
      have heGCj : e ∈ compEdgeSet G₀ Cj := by
        have hs := ((hsp0 j hj).1.hCompLSF Cj hCj_G0).1.hsurv_edge e heCj hniCj |>.1
        rwa [((hsp0 j hj).1.hCompLSF Cj hCj_G0).2.1, compLSFBatch_G₀] at hs
      have hCeq : Cj = C := by
        by_contra hne
        exact Finset.disjoint_left.mp (compEdgeSet_pairwiseDisjoint G₀ hCj hC hne) heGCj hCG₀
      rw [hCeq] at hwCj
      have hcomp := (compLSFBatch_compSt (hI0 j hj) hU hC).1
      have hG_compj : ((initCompLSFWith lsfInit G₀ ℓ₀ k j).compSt C).G = compGraph G₀ C :=
        (initCompLSFWith_compSt_basic (hApprox.toValidLSFInitFor hj) hG₀ hℓ₀ hk hC).2.1
      rw [hwCj, hcomp]
      change (applyLSFBatch (lsfInit (compGraph G₀ C) ℓs k j)
        (projCompBatchG G₀ ((initCompLSFWith lsfInit G₀ ℓ₀ k j).compSt C).G U)).wstr e = _
      rw [hG_compj, hInitEq j hj]
      rfl
    have hmwu := (lemma_5_5_approx_explicit C_lsst α K_σ K_ρ hKρ (compGraph G₀ C) hGC_val hGC_ne
      ℓs hℓC k hk [U_C] ⟨hBU_C, trivial⟩ ℓ_C hℓ_pos hℓ_orig thresh ρ δ hρ_lo hρ_hi ⟨hδ0, hδ1⟩
      v T_raw r₀ C_reps π W_T hv0 hv_pos hp hv_step).2.2 e he_UC
    have hnC_le : (compGraph G₀ C).n ≤ G₀.n := compGraph_n_le hC
    have hmC_le : (compGraph G₀ C).m ≤ G₀.m := compGraph_m_le
    have hlogC : Real.log (((compGraph G₀ C).n : ℝ) + 2) ≤ Real.log ((G₀.n : ℝ) + 2) := by
      refine Real.log_le_log (by positivity) ?_
      have : ((compGraph G₀ C).n : ℝ) ≤ G₀.n := by exact_mod_cast hnC_le
      linarith
    have hlogC_nn : 0 ≤ Real.log (((compGraph G₀ C).n : ℝ) + 2) := by
      linarith [half_lt_log_add_two (compGraph G₀ C).n]
    have hlogCm : Real.log (((compGraph G₀ C).m : ℝ) + 2) ≤ Real.log ((G₀.m : ℝ) + 2) := by
      refine Real.log_le_log (by positivity) ?_
      have : ((compGraph G₀ C).m : ℝ) ≤ G₀.m := by exact_mod_cast hmC_le
      linarith
    have hlogCm_nn : 0 ≤ Real.log (((compGraph G₀ C).m : ℝ) + 2) := by
      linarith [half_lt_log_add_two (compGraph G₀ C).m]
    have hK_nn : 0 ≤ K := by dsimp [K]; positivity
    have hpow6 := pow_le_pow_left₀ hlogC_nn hlogC 6
    have hmono : K * (Real.log (((compGraph G₀ C).n : ℝ) + 2)) ^ 6 *
          Real.log (((compGraph G₀ C).m : ℝ) + 2) ≤
        K * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 * Real.log ((G₀.m : ℝ) + 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow6 hK_nn) hlogCm hlogCm_nn (by positivity)
    calc ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (cs j).wstrGlobal e
        = ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) *
            (applyLSFBatches (initLSFWith (compGraph G₀ C) ℓs (v j) (k : ℝ) (T_raw j) (r₀ j)
              (C_reps j) (π j) (W_T j) thresh) [U_C]).wstr e :=
          Finset.sum_congr rfl fun j hj => by rw [hw_eq j (Finset.mem_range.mp hj)]
      _ ≤ K * (Real.log (((compGraph G₀ C).n : ℝ) + 2)) ^ 6 *
            Real.log (((compGraph G₀ C).m : ℝ) + 2) := hmwu
      _ ≤ K * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 * Real.log ((G₀.m : ℝ) + 2) := hmono

end

end MinCostFlow.SparseCore
