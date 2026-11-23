module

public import MinCostFlow.LSF.Lemma54With
public import MinCostFlow.LSF.Lemma55
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma 5.5 for Parameterized `initLSFWith` and Approximate Weights

This file generalizes `lemma_5_5` (`MinCostFlow.LSF.Lemma55`) to:
* Parameterized LSF states `initLSFWith` satisfying `ValidLSFParams` at each MWU step `j < k`.
* Any scaling parameter `ρ` in `[10 * U, K_ρ * U]`, where
  `U = K₀ * k * log^6(G₀.n + 2)` and `K₀ = max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240)`.
* Approximate multiplicative weight updates within relative step error `δ ≤ 1 / (20 * k)`:
  `(1 - δ) * v j e * exp((S₀ j).wstr e / ρ) ≤ v (j + 1) e ≤ (1 + δ) * v j e * exp((S₀ j).wstr e / ρ)`
  (which also implies cumulative `1 ± 1/10` agreement with exact exponentials via
  `mwu_weights_within_tenth`).

It also provides `lemma_5_5_approx` (existential constant form) and `lemma_5_5_of_approx`
recovering `lemma_5_5` as the exact (`δ = 0, K_ρ = 10`) special case.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Helpers on inserted edges and elementary exponential inequalities -/

private lemma applyLSFUpdate_insertedEdges' (S : LSFState) (u : Update) :
    (applyLSFUpdate S u).insertedEdges = updateInserted S.insertedEdges u := by
  cases u <;> rfl

private lemma applyLSFBatch_insertedEdges' (U : List Update) (S : LSFState) :
    (U.foldl applyLSFUpdate S).insertedEdges = U.foldl updateInserted S.insertedEdges := by
  induction U generalizing S with
  | nil => rfl
  | cons u us ih => simp [List.foldl, applyLSFUpdate_insertedEdges', ih]

private lemma applyLSFBatches_insertedEdges' (Us : List (List Update)) (S : LSFState) :
    (applyLSFBatches S Us).insertedEdges =
      Us.foldl (fun I U => U.foldl updateInserted I) S.insertedEdges := by
  unfold applyLSFBatches
  induction Us generalizing S with
  | nil => rfl
  | cons U Us ih =>
    simpa [List.foldl, applyLSFBatch, applyLSFBatch_insertedEdges'] using
      ih (U.foldl applyLSFUpdate S)

private lemma exp_le_one_add_two_mul' {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + 2 * x := by
  have h1mx : 0 < 1 - x := by linarith
  have hexp_neg : 1 - x ≤ Real.exp (-x) := by
    simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-x)
  rw [Real.exp_neg] at hexp_neg
  have hexp_le_inv : Real.exp x ≤ (1 - x)⁻¹ := by
    have hpos : 0 < Real.exp x := Real.exp_pos x
    rw [← inv_inv (Real.exp x)]
    exact inv_anti₀ h1mx hexp_neg
  have hinv_le : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_eq_one_div, div_le_iff₀ h1mx]
    nlinarith
  exact hexp_le_inv.trans hinv_le

private lemma exp_neg_two_mul_le_one_sub {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) :
    Real.exp (-2 * δ) ≤ 1 - δ := by
  have h1mδ : 0 < 1 - δ := by linarith
  have hprod : 1 ≤ (1 - δ) * (1 + 2 * δ) := by nlinarith
  have hexp : 1 + 2 * δ ≤ Real.exp (2 * δ) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * δ)
  have hprod_exp : 1 ≤ (1 - δ) * Real.exp (2 * δ) :=
    hprod.trans (mul_le_mul_of_nonneg_left hexp h1mδ.le)
  have h1 : Real.exp (-2 * δ) = (Real.exp (2 * δ))⁻¹ := by
    rw [show (-2 * δ : ℝ) = -(2 * δ) by ring, Real.exp_neg]
  rw [h1, inv_eq_one_div, div_le_iff₀ (Real.exp_pos (2 * δ))]
  linarith

/-! ## Weight approximation guarantees (`1 ± 1/10`) -/

/-- Under stepwise relative error `0 ≤ δ ≤ 1 / (20 * k)`, weights `v j e` stay within
`[9/10, 11/10]` (`1 ± 1/10`) of the exact exponential `exp (∑ i < j, wstr i / ρ)` for all
`j ≤ k`. -/
lemma mwu_weights_within_tenth {k : ℕ} (hk : 1 ≤ k) {G₀ : MGraph} {w : ℕ → ℕ → ℝ} {ρ δ : ℝ}
    (hδ : 0 ≤ δ ∧ δ ≤ 1 / (20 * (k : ℝ))) {v : ℕ → ℕ → ℝ}
    (hv0 : ∀ e ∈ G₀.E, v 0 e = 1)
    (hv_step : ∀ j < k, ∀ e ∈ G₀.E,
      (1 - δ) * v j e * Real.exp (w j e / ρ) ≤ v (j + 1) e ∧
      v (j + 1) e ≤ (1 + δ) * v j e * Real.exp (w j e / ρ)) :
    ∀ j ≤ k, ∀ e ∈ G₀.E,
      (9 / 10 : ℝ) * Real.exp (∑ i ∈ Finset.range j, w i e / ρ) ≤ v j e ∧
      v j e ≤ (11 / 10 : ℝ) * Real.exp (∑ i ∈ Finset.range j, w i e / ρ) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hδ_half : δ ≤ 1 / 2 := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h1 : 1 / (20 * (k : ℝ)) ≤ 1 / 20 :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    linarith [hδ.2]
  have hbound : ∀ j ≤ k, ∀ e ∈ G₀.E,
      Real.exp (-2 * (j : ℝ) * δ + ∑ i ∈ Finset.range j, w i e / ρ) ≤ v j e ∧
      v j e ≤ Real.exp ((j : ℝ) * δ + ∑ i ∈ Finset.range j, w i e / ρ) := by
    intro j
    induction j with
    | zero =>
      intro _ e he
      simp [hv0 e he]
    | succ j ih =>
      intro hj_succ e he
      have hj_lt : j < k := Nat.lt_of_succ_le hj_succ
      have ⟨ih_lo, ih_hi⟩ := ih hj_lt.le e he
      have ⟨hs_lo, hs_hi⟩ := hv_step j hj_lt e he
      have hlo_e : Real.exp (-2 * δ) ≤ 1 - δ := exp_neg_two_mul_le_one_sub hδ.1 hδ_half
      have hhi_e : 1 + δ ≤ Real.exp δ := by simpa [add_comm] using Real.add_one_le_exp δ
      have hexp_pos : 0 < Real.exp (w j e / ρ) := Real.exp_pos _
      have hv_pos : 0 ≤ v j e := (Real.exp_pos _).le.trans ih_lo
      constructor
      · have h1 : Real.exp (-2 * δ) * Real.exp (-2 * (j : ℝ) * δ + ∑ i ∈ Finset.range j, w i e / ρ) *
            Real.exp (w j e / ρ) ≤ (1 - δ) * v j e * Real.exp (w j e / ρ) := by
          refine mul_le_mul_of_nonneg_right ?_ hexp_pos.le
          exact mul_le_mul hlo_e ih_lo (Real.exp_pos _).le (by linarith)
        have hEq : Real.exp (-2 * δ) * Real.exp (-2 * (j : ℝ) * δ + ∑ i ∈ Finset.range j, w i e / ρ) *
              Real.exp (w j e / ρ) =
            Real.exp (-2 * ((j + 1 : ℕ) : ℝ) * δ + ∑ i ∈ Finset.range (j + 1), w i e / ρ) := by
          rw [← Real.exp_add, ← Real.exp_add, Finset.sum_range_succ]
          congr 1; push_cast; ring
        exact (hEq ▸ h1).trans hs_lo
      · have h1 : (1 + δ) * v j e * Real.exp (w j e / ρ) ≤
            Real.exp δ * Real.exp ((j : ℝ) * δ + ∑ i ∈ Finset.range j, w i e / ρ) *
              Real.exp (w j e / ρ) := by
          refine mul_le_mul_of_nonneg_right ?_ hexp_pos.le
          exact mul_le_mul hhi_e ih_hi hv_pos (Real.exp_pos _).le
        have hEq : Real.exp δ * Real.exp ((j : ℝ) * δ + ∑ i ∈ Finset.range j, w i e / ρ) *
              Real.exp (w j e / ρ) =
            Real.exp (((j + 1 : ℕ) : ℝ) * δ + ∑ i ∈ Finset.range (j + 1), w i e / ρ) := by
          rw [← Real.exp_add, ← Real.exp_add, Finset.sum_range_succ]
          congr 1; push_cast; ring
        exact hs_hi.trans (hEq ▸ h1)
  intro j hj e he
  obtain ⟨hlo, hhi⟩ := hbound j hj e he
  have hjk : (j : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hj
  have hjkδ : (j : ℝ) * δ ≤ 1 / 20 := by
    calc (j : ℝ) * δ ≤ (k : ℝ) * δ := mul_le_mul_of_nonneg_right hjk hδ.1
      _ ≤ (k : ℝ) * (1 / (20 * (k : ℝ))) := mul_le_mul_of_nonneg_left hδ.2 hk_pos.le
      _ = 1 / 20 := by field_simp [ne_of_gt hk_pos]
  have hlo9 : (9 / 10 : ℝ) ≤ Real.exp (-2 * (j : ℝ) * δ) := by
    have hneg1 : (-1 / 10 : ℝ) ≤ -2 * (j : ℝ) * δ := by linarith
    have h9 : (9 / 10 : ℝ) ≤ Real.exp (-1 / 10) := by
      simpa [show (-1 / 10 : ℝ) + 1 = 9 / 10 by norm_num] using Real.add_one_le_exp (-1 / 10 : ℝ)
    exact h9.trans (Real.exp_le_exp.mpr hneg1)
  have hhi11 : Real.exp ((j : ℝ) * δ) ≤ 11 / 10 := by
    have h1 : Real.exp ((j : ℝ) * δ) ≤ Real.exp (1 / 20) := Real.exp_le_exp.mpr hjkδ
    have h2 : Real.exp (1 / 20 : ℝ) ≤ 11 / 10 :=
      (exp_le_one_add_two_mul' (by norm_num : (0 : ℝ) ≤ 1 / 20)
        (by norm_num : (1 / 20 : ℝ) ≤ 1 / 2)).trans_eq (by norm_num)
    exact h1.trans h2
  rw [Real.exp_add] at hlo hhi
  constructor
  · exact (mul_le_mul_of_nonneg_right hlo9 (Real.exp_pos _).le).trans hlo
  · exact hhi.trans (mul_le_mul_of_nonneg_right hhi11 (Real.exp_pos _).le)

/-! ## Generalized Lemma 5.5 -/

open Classical in
/-- Explicit-constant Lemma 5.5 for parameterized `initLSFWith`, scaling `ρ ∈ [10 U, K_ρ U]`,
and stepwise approximate weights `v j e` within `(1 ± δ)` (`δ ≤ 1 / (20 * k)`). -/
theorem lemma_5_5_approx_explicit (C_lsst α K_σ K_ρ : ℝ) (hKρ : 1 ≤ K_ρ)
    (G₀ : MGraph) (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (ℓ₀ : ℕ → ℝ) (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    (k : ℕ) (hk : 1 ≤ k)
    (Us : List (List Update)) (hUs : BatchesIsValid G₀ Us)
    (ℓ : ℕ → ℝ)
    (hℓ : ∀ e ∈ (Us.foldl MGraph.applyBatch G₀).E, 0 < ℓ e)
    (hℓ_orig : ∀ e ∈ G₀.E, e ∈ (Us.foldl MGraph.applyBatch G₀).E →
      e ∉ batchesInserted Us → ℓ e = ℓ₀ e)
    (thresh ρ δ : ℝ)
    (hρ_lo : 10 * (max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240)) * (k : ℝ) *
      (Real.log ((G₀.n : ℝ) + 2)) ^ 6 ≤ ρ)
    (hρ_hi : ρ ≤ K_ρ * (max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240)) * (k : ℝ) *
      (Real.log ((G₀.n : ℝ) + 2)) ^ 6)
    (hδ : 0 ≤ δ ∧ δ ≤ 1 / (20 * (k : ℝ)))
    (v : ℕ → ℕ → ℝ) (T_raw : ℕ → MGraph) (r₀ : ℕ → ℕ)
    (C_reps : ℕ → Finset ℕ) (π : ℕ → ℕ → ℕ) (W_T : ℕ → Finset (Finset ℕ))
    (hv0 : ∀ e ∈ G₀.E, v 0 e = 1)
    (hv_pos : ∀ j ≤ k, ∀ e ∈ G₀.E, 0 < v j e)
    (hp : ∀ j < k, ValidLSFParams C_lsst α thresh K_σ G₀ ℓ₀ (v j) (k : ℝ)
      (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j))
    (hv_step : ∀ j < k, ∀ e ∈ G₀.E,
      (1 - δ) * v j e * Real.exp
          ((initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh).wstr e / ρ)
        ≤ v (j + 1) e ∧
      v (j + 1) e ≤ (1 + δ) * v j e * Real.exp
          ((initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh).wstr e / ρ)) :
    let K₀ := max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240)
    let K := 3 * K_ρ * K₀
    let G := Us.foldl MGraph.applyBatch G₀
    let q := totalUpdates Us
    let S₀ : ℕ → LSFState := fun j =>
      initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh
    let S : ℕ → LSFState := fun j => applyLSFBatches (S₀ j) Us
    0 < K ∧
    (∀ j < k,
      S j = applyLSFBatches (S₀ j) Us ∧
      (S j).G = G ∧
      (S j).insertedEdges = batchesInserted Us ∧
      (S j).RF.F.E ⊆ (S₀ j).RF.F.E ∧
      G.IsSubgraph (S j).RF.F ∧
      (S j).T.IsSubgraph (S j).RF.F ∧
      (∀ e ∈ (S j).insertedEdges, (S j).wstr e = 1) ∧
      (∀ e ∈ G.E, e ∉ (S j).insertedEdges → (S j).wstr e = (S₀ j).wstr e) ∧
      ((components (S₀ j).RF.F).card : ℝ) ≤
        (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
          else ((components G₀).card : ℝ) * K * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
          K * ((G₀.E.card : ℝ) / (k : ℝ)) ∧
      ((components (S j).RF.F).card : ℝ) ≤ ((components (S₀ j).RF.F).card : ℝ) +
        K * (q : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ∧
      (S j).lsf.Holds G ℓ (K * (k : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 6) ∧
      ((S j).W_init.card : ℝ) ≤
        6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
          else ((components G₀).card : ℝ) * K * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
          K * ((G₀.E.card : ℝ) / (k : ℝ)) ∧
      (S j).W_init.biUnion (inducedEdges (S₀ j).RF.F) = (S₀ j).RF.F.E ∧
      (∀ W₁ ∈ (S j).W_init, ∀ W₂ ∈ (S j).W_init, W₁ ≠ W₂ →
        Disjoint (inducedEdges (S₀ j).RF.F W₁) (inducedEdges (S₀ j).RF.F W₂)) ∧
      boundary (S j).W_init ⊆ (S j).R ∧
      ∀ W ∈ (S j).W_init, PathConvex (S j).T₀ W ∧ W ⊆ G.V ∧
        (pieceBoundary (S j).W_init W).card ≤ 1 ∧
        (G.vol (W \ (S j).R) : ℝ) ≤ K * (k : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) ∧
    ∀ e ∈ G.E,
      ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (S j).wstr e ≤
        K * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by
  intro K₀ K G q S₀ S
  have h2240_le : (2240 : ℝ) ≤ K₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hK₀_pos : 0 < K₀ := by linarith
  have hK_pos : 0 < K := by positivity
  have hK₀_le_K : K₀ ≤ K := by nlinarith
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hk_real
  have hL : (1 / 2 : ℝ) < Real.log ((G₀.n : ℝ) + 2) := half_lt_log_add_two G₀.n
  have hL_pos : 0 < Real.log ((G₀.n : ℝ) + 2) := by linarith
  have hLm : (1 / 2 : ℝ) < Real.log ((G₀.E.card : ℝ) + 2) := half_lt_log_add_two G₀.E.card
  have hLm_pos : 0 < Real.log ((G₀.E.card : ℝ) + 2) := by linarith
  let L := Real.log ((G₀.n : ℝ) + 2)
  let W := K₀ * L ^ 4
  let U := K₀ * (k : ℝ) * L ^ 6
  have hU_pos : 0 < U := mul_pos (mul_pos hK₀_pos hk_pos) (pow_pos hL_pos 6)
  have hρ_pos : 0 < ρ := by linarith
  have hins_eq : ∀ j, (S j).insertedEdges = batchesInserted Us := by
    intro j
    rw [show (S j).insertedEdges = (applyLSFBatches (S₀ j) Us).insertedEdges from rfl,
      applyLSFBatches_insertedEdges']
    rfl
  refine ⟨hK_pos, ?_, ?_⟩
  · intro j hj
    have hℓ_orig' : ∀ e ∈ G₀.E, e ∈ G.E → e ∉ (S j).insertedEdges → ℓ e = ℓ₀ e := by
      intro e he₀ heG hn
      rw [hins_eq j] at hn
      exact hℓ_orig e he₀ heG hn
    have hsp := lemma_5_4_with_explicit C_lsst α K_σ G₀ hG₀ hV₀ ℓ₀ (v j) hℓ₀ (hv_pos j hj.le)
      (k : ℝ) hk_real (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh (hp j hj) Us hUs ℓ hℓ
      hℓ_orig'
    rcases hsp with ⟨_, hSG, hFE, hGsubF, hTsubF, hinsw, hsurvw, hR₀_card, hR_card, hholds,
      _, hW_card, hcov, hdisj, hb_sub, hW_props⟩
    have hK₀_le' : max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240) ≤ K := hK₀_le_K
    have hmono : ∀ a : ℝ, 0 ≤ a →
        max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240) * a ≤ K * a := fun a ha =>
      mul_le_mul_of_nonneg_right hK₀_le' ha
    refine ⟨rfl, hSG, hins_eq j, hFE, hGsubF, hTsubF, hinsw, hsurvw, ?_, ?_, ?_, ?_, hcov, hdisj,
      hb_sub, ?_⟩
    · have hcomp_mono : (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then (1 : ℝ)
          else ((components G₀).card : ℝ) *
            max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240) * L ^ 2) ≤
          (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
          else ((components G₀).card : ℝ) * K * L ^ 2) := by
        split_ifs
        · exact le_rfl
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK₀_le' (Nat.cast_nonneg _))
            (sq_nonneg _)
      exact hR₀_card.trans (add_le_add hcomp_mono (hmono _ (div_nonneg (Nat.cast_nonneg _) hk_pos.le)))
    · exact hR_card.trans (add_le_add le_rfl (by
        have := hmono ((q : ℝ) * L ^ 2) (mul_nonneg (Nat.cast_nonneg q) (sq_nonneg _))
        linarith [this]))
    · refine ⟨hholds.1, hholds.2.1, hholds.2.2.1, fun e he => ⟨(hholds.2.2.2 e he).1, ?_⟩⟩
      exact (hholds.2.2.2 e he).2.trans (by
        have := hmono ((k : ℝ) * L ^ 6) (mul_nonneg hk_pos.le (pow_nonneg hL_pos.le 6))
        linarith [this])
    · have hcomp_mono : (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then (1 : ℝ)
          else ((components G₀).card : ℝ) *
            max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240) * L ^ 2) ≤
          (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
          else ((components G₀).card : ℝ) * K * L ^ 2) := by
        split_ifs
        · exact le_rfl
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK₀_le' (Nat.cast_nonneg _))
            (sq_nonneg _)
      exact hW_card.trans (add_le_add (add_le_add le_rfl hcomp_mono)
        (hmono _ (div_nonneg (Nat.cast_nonneg _) hk_pos.le)))
    · intro Wp hWp
      have hw := hW_props Wp hWp
      exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.trans (by
        have := hmono ((k : ℝ) * L ^ 2) (mul_nonneg hk_pos.le (sq_nonneg _))
        linarith [this])⟩
  · intro e heG
    by_cases he_ins : e ∈ batchesInserted Us
    · have hw_eq : ∀ j ∈ Finset.range k, (S j).wstr e = 1 := by
        intro j hj
        have hj_lt : j < k := Finset.mem_range.mp hj
        have hI := initLSFWith_inv hG₀ hV₀ hℓ₀ (hv_pos j hj_lt.le) hk_real (hp j hj_lt)
        exact (((applyLSFBatches_inv_with Us hI hUs).1).hins_wstr e (hins_eq j ▸ he_ins)).1
      rw [Finset.sum_congr rfl (fun j hj => by rw [hw_eq j hj, mul_one]),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div_cancel (ne_of_gt hk_pos)]
      have hL6 : (1 : ℝ) ≤ 64 * L ^ 6 := by
        have hL2 : 1 ≤ 4 * L ^ 2 := by nlinarith
        have hpow : 1 ≤ (4 * L ^ 2) ^ 3 := one_le_pow₀ hL2
        linarith [show (4 * L ^ 2) ^ 3 = 64 * L ^ 6 by ring]
      have h128 : (1 : ℝ) ≤ 128 * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by
        have : 1 ≤ (64 * L ^ 6) * (2 * Real.log ((G₀.E.card : ℝ) + 2)) := by nlinarith
        linarith
      have h128_le : (128 : ℝ) ≤ K := by nlinarith
      exact h128.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h128_le (pow_nonneg hL_pos.le 6)) hLm_pos.le)
    · have he_surv_all : ∀ j < k, e ∈ G₀.E ∧ (S j).wstr e = (S₀ j).wstr e := by
        intro j hj
        have he_nins : e ∉ (S j).insertedEdges := by rwa [hins_eq j]
        have hsp := lemma_5_4_with_explicit C_lsst α K_σ G₀ hG₀ hV₀ ℓ₀ (v j) hℓ₀ (hv_pos j hj.le)
          (k : ℝ) hk_real (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh (hp j hj) Us hUs ℓ hℓ
          (fun f hf₀ hfG hn => hℓ_orig f hf₀ hfG (by rwa [hins_eq j] at hn))
        have heG₀ : e ∈ G₀.E := by
          have hI₀ := initLSFWith_inv hG₀ hV₀ hℓ₀ (hv_pos j hj.le) hk_real (hp j hj)
          have hb := applyLSFBatches_inv_with Us hI₀ hUs
          have hG₀_eq : (applyLSFBatches (S₀ j) Us).G₀ = G₀ := hb.2.2.1
          exact hG₀_eq ▸ (hb.1.hsurv_edge e (hsp.2.1.symm ▸ heG) he_nins).1
        exact ⟨heG₀, hsp.2.2.2.2.2.2.1 e heG he_nins⟩
      have heG₀ : e ∈ G₀.E := (he_surv_all 0 hk).1
      let Φ : ℕ → ℝ := fun j => ∑ f ∈ G₀.E, v j f
      have hΦ0 : Φ 0 = (G₀.E.card : ℝ) := by
        dsimp only [Φ]
        rw [Finset.sum_congr rfl (fun f hf => hv0 f hf), Finset.sum_const, nsmul_eq_mul, mul_one]
      have hstep : ∀ j < k, Φ (j + 1) ≤ (1 + δ) * (1 + 2 * W / ρ) * Φ j := by
        intro j hj
        have hspec := initLSFWith_spec hG₀ hV₀ hℓ₀ (hv_pos j hj.le) hk_real (hp j hj)
        have hwtd : ∑ f ∈ G₀.E, v j f * (S₀ j).wstr f ≤ K₀ * G₀.norm1 (v j) * L ^ 4 := by
          have hw_le : 112 * (1 + α) * max 1 C_lsst ≤ K₀ := (le_max_left _ _).trans (le_max_right _ _)
          have hnorm0 : 0 ≤ G₀.norm1 (v j) := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
          exact hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw_le hnorm0) (pow_nonneg hL_pos.le 4))
        have hnorm_eq : G₀.norm1 (v j) = Φ j := by
          unfold MGraph.norm1
          exact Finset.sum_congr rfl (fun f hf => abs_of_pos (hv_pos j hj.le f hf))
        rw [hnorm_eq] at hwtd
        have hterm : ∀ f ∈ G₀.E, v (j + 1) f ≤
            (1 + δ) * (v j f + (2 / ρ) * (v j f * (S₀ j).wstr f)) := by
          intro f hf
          have h0 : (0 : ℝ) ≤ (S₀ j).wstr f := by
            have hI₀ := initLSFWith_inv hG₀ hV₀ hℓ₀ (hv_pos j hj.le) hk_real (hp j hj)
            by_cases hth : thresh ≤ levelStretchBound (S₀ j).T₀ (S₀ j).r₀ (S₀ j).π G₀
                (safeLen G₀ ℓ₀) f
            · linarith [(hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 f hf).2 hth |>.1]
            · rw [(hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 f hf).1 (not_le.mp hth)]
              have hlen := levelStretchBound_ge_two hspec.2.2.2.2.2.2.2.2.2.1 (S₀ j).π G₀
                (fun g _ => safeLen_nonneg hℓ₀ g) (by rw [safeLen_eq_of_mem ℓ₀ hf]; exact hℓ₀ f hf)
              linarith
          have hU_bd : (S₀ j).wstr f ≤ U :=
            (hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 f hf).trans
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hk_pos.le)
                (pow_nonneg hL_pos.le 6))
          have hx0 : 0 ≤ (S₀ j).wstr f / ρ := div_nonneg h0 hρ_pos.le
          have hx1 : (S₀ j).wstr f / ρ ≤ 1 / 2 := by
            rw [div_le_iff₀ hρ_pos]; linarith
          have hexp := exp_le_one_add_two_mul' hx0 hx1
          have h1 := (hv_step j hj f hf).2
          have h2 : (1 + δ) * v j f * Real.exp ((S₀ j).wstr f / ρ) ≤
              (1 + δ) * v j f * (1 + 2 * ((S₀ j).wstr f / ρ)) :=
            mul_le_mul_of_nonneg_left hexp (mul_nonneg (by linarith [hδ.1]) (hv_pos j hj.le f hf).le)
          linarith [h1.trans h2,
            show (1 + δ) * v j f * (1 + 2 * ((S₀ j).wstr f / ρ)) =
              (1 + δ) * (v j f + (2 / ρ) * (v j f * (S₀ j).wstr f)) by ring]
        calc Φ (j + 1)
            ≤ ∑ f ∈ G₀.E, (1 + δ) * (v j f + (2 / ρ) * (v j f * (S₀ j).wstr f)) :=
              Finset.sum_le_sum hterm
          _ = (1 + δ) * (Φ j + (2 / ρ) * ∑ f ∈ G₀.E, v j f * (S₀ j).wstr f) := by
              rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
          _ ≤ (1 + δ) * (Φ j + (2 / ρ) * (K₀ * L ^ 4 * Φ j)) := by
              refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by linarith [hδ.1])
              refine mul_le_mul_of_nonneg_left ?_ (div_nonneg zero_le_two hρ_pos.le)
              linarith [hwtd]
          _ = (1 + δ) * (1 + 2 * W / ρ) * Φ j := by dsimp only [W]; ring
      have hΦ_exp : ∀ j ≤ k, Φ j ≤ Φ 0 * Real.exp ((j : ℝ) * (δ + 4 / (5 * (k : ℝ)))) := by
        intro j hj
        induction j with
        | zero => simp
        | succ j ih =>
          have hj_lt : j < k := Nat.lt_of_succ_le hj
          have h1 : (1 + δ) * (1 + 2 * W / ρ) ≤ Real.exp (δ + 4 / (5 * (k : ℝ))) := by
            have hW_bd : 2 * W / ρ ≤ 4 / (5 * (k : ℝ)) := by
              have hL2 : 1 ≤ 4 * L ^ 2 := by nlinarith
              have hprod : 2 * W * (5 * (k : ℝ)) ≤ 4 * ρ := by
                have h2K : 2 * (K₀ * L ^ 4) * (5 * (k : ℝ)) =
                    10 * K₀ * (k : ℝ) * L ^ 4 := by ring
                have h4U : 4 * (10 * K₀ * (k : ℝ) * L ^ 6) =
                    (4 * L ^ 2) * (10 * K₀ * (k : ℝ) * L ^ 4) := by ring
                have hnn : 0 ≤ 10 * K₀ * (k : ℝ) * L ^ 4 := by positivity
                calc 2 * W * (5 * (k : ℝ))
                    = 1 * (10 * K₀ * (k : ℝ) * L ^ 4) := by dsimp only [W]; linarith
                  _ ≤ (4 * L ^ 2) * (10 * K₀ * (k : ℝ) * L ^ 4) :=
                      mul_le_mul_of_nonneg_right hL2 hnn
                  _ = 4 * (10 * K₀ * (k : ℝ) * L ^ 6) := h4U.symm
                  _ ≤ 4 * ρ := mul_le_mul_of_nonneg_left hρ_lo (by positivity)
              rw [div_le_div_iff₀ hρ_pos (by positivity)]
              exact hprod
            have he1 : 1 + δ ≤ Real.exp δ := by simpa [add_comm] using Real.add_one_le_exp δ
            have he2 : 1 + 2 * W / ρ ≤ Real.exp (4 / (5 * (k : ℝ))) := by
              linarith [hW_bd, Real.add_one_le_exp (4 / (5 * (k : ℝ)))]
            calc (1 + δ) * (1 + 2 * W / ρ)
                ≤ Real.exp δ * Real.exp (4 / (5 * (k : ℝ))) :=
                  mul_le_mul he1 he2 (by positivity) (Real.exp_pos _).le
              _ = Real.exp (δ + 4 / (5 * (k : ℝ))) := (Real.exp_add _ _).symm
          have hΦ_nn : 0 ≤ Φ j := Finset.sum_nonneg (fun f hf => (hv_pos j hj_lt.le f hf).le)
          calc Φ (j + 1)
              ≤ (1 + δ) * (1 + 2 * W / ρ) * Φ j := hstep j hj_lt
            _ ≤ Real.exp (δ + 4 / (5 * (k : ℝ))) * Φ j :=
                mul_le_mul_of_nonneg_right h1 hΦ_nn
            _ ≤ Real.exp (δ + 4 / (5 * (k : ℝ))) *
                  (Φ 0 * Real.exp ((j : ℝ) * (δ + 4 / (5 * (k : ℝ))))) :=
                mul_le_mul_of_nonneg_left (ih hj_lt.le) (Real.exp_pos _).le
            _ = Φ 0 * Real.exp (((j + 1 : ℕ) : ℝ) * (δ + 4 / (5 * (k : ℝ)))) := by
                rw [mul_left_comm, ← Real.exp_add]; push_cast; ring_nf
      have hΦk : Φ k ≤ (G₀.E.card : ℝ) * Real.exp (17 / 20) := by
        have hbase := hΦ_exp k le_rfl
        rw [hΦ0] at hbase
        have hk_exp : (k : ℝ) * (δ + 4 / (5 * (k : ℝ))) ≤ 17 / 20 := by
          have hkδ : (k : ℝ) * δ ≤ 1 / 20 := by
            calc (k : ℝ) * δ ≤ (k : ℝ) * (1 / (20 * (k : ℝ))) :=
                  mul_le_mul_of_nonneg_left hδ.2 hk_pos.le
              _ = 1 / 20 := by field_simp [ne_of_gt hk_pos]
          have hEq : (k : ℝ) * (4 / (5 * (k : ℝ))) = 4 / 5 := by
            field_simp [ne_of_gt hk_pos]
          linarith [show (k : ℝ) * (δ + 4 / (5 * (k : ℝ))) =
            (k : ℝ) * δ + (k : ℝ) * (4 / (5 * (k : ℝ))) by ring]
        exact hbase.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hk_exp) (Nat.cast_nonneg _))
      have hv_lo := (mwu_weights_within_tenth hk hδ hv0
        (fun j hj f hf => hv_step j hj f hf) k le_rfl e heG₀).1
      have hvk_le_Φ : v k e ≤ Φ k :=
        Finset.single_le_sum (fun f hf => (hv_pos k le_rfl f hf).le) heG₀
      have hExp_sum_le : Real.exp (∑ j ∈ Finset.range k, (S₀ j).wstr e / ρ) ≤
          Real.exp (Real.log ((G₀.E.card : ℝ) + 2) + 1) := by
        have h2 : (9 / 10 : ℝ) * Real.exp (∑ j ∈ Finset.range k, (S₀ j).wstr e / ρ) ≤
            (G₀.E.card : ℝ) * Real.exp (17 / 20) := hv_lo.trans (hvk_le_Φ.trans hΦk)
        have h19 : Real.exp (17 / 20 : ℝ) / (9 / 10 : ℝ) ≤ Real.exp 1 := by
          have hinv_le : (9 / 10 : ℝ)⁻¹ ≤ Real.exp (3 / 20 : ℝ) := by
            have h11 : Real.exp (3 / 20 : ℝ) ≥ 1 + 3 / 20 := by
              simpa [add_comm] using Real.add_one_le_exp (3 / 20 : ℝ)
            linarith [show (9 / 10 : ℝ)⁻¹ = 10 / 9 by norm_num,
              show (1 + 3 / 20 : ℝ) = 23 / 20 by norm_num,
              show (10 / 9 : ℝ) ≤ 23 / 20 by norm_num]
          rw [div_eq_mul_inv]
          calc Real.exp (17 / 20 : ℝ) * (9 / 10 : ℝ)⁻¹
              ≤ Real.exp (17 / 20 : ℝ) * Real.exp (3 / 20 : ℝ) :=
                mul_le_mul_of_nonneg_left hinv_le (Real.exp_pos _).le
            _ = Real.exp 1 := by rw [← Real.exp_add]; norm_num
        have h3 : Real.exp (∑ j ∈ Finset.range k, (S₀ j).wstr e / ρ) ≤
            ((G₀.E.card : ℝ) + 2) * Real.exp 1 := by
          have hm_le : (G₀.E.card : ℝ) ≤ (G₀.E.card : ℝ) + 2 := by linarith
          calc Real.exp (∑ j ∈ Finset.range k, (S₀ j).wstr e / ρ)
              ≤ (G₀.E.card : ℝ) * (Real.exp (17 / 20) / (9 / 10)) := by
                rw [mul_div_assoc', le_div_iff₀ (by norm_num)]; linarith [h2]
            _ ≤ ((G₀.E.card : ℝ) + 2) * Real.exp 1 :=
                mul_le_mul hm_le h19 (by positivity) (by positivity)
        rwa [Real.exp_add, Real.exp_log (by positivity)]
      have hlog_sum : ∑ j ∈ Finset.range k, (S₀ j).wstr e / ρ ≤
          Real.log ((G₀.E.card : ℝ) + 2) + 1 := Real.exp_le_exp.mp hExp_sum_le
      have hsum_bd : ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (S₀ j).wstr e ≤
          K * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by
        have hlog3 : Real.log ((G₀.E.card : ℝ) + 2) + 1 ≤ 3 * Real.log ((G₀.E.card : ℝ) + 2) := by
          linarith [hLm]
        have hrew : ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (S₀ j).wstr e =
            (ρ / (k : ℝ)) * ∑ j ∈ Finset.range k, (S₀ j).wstr e / ρ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          field_simp [ne_of_gt hk_pos, ne_of_gt hρ_pos]
        rw [hrew]
        have hρ_div : ρ / (k : ℝ) ≤ K_ρ * K₀ * L ^ 6 := by
          rw [div_le_iff₀ hk_pos]
          linarith [hρ_hi]
        calc (ρ / (k : ℝ)) * ∑ j ∈ Finset.range k, (S₀ j).wstr e / ρ
            ≤ (K_ρ * K₀ * L ^ 6) * (3 * Real.log ((G₀.E.card : ℝ) + 2)) :=
              mul_le_mul hρ_div (hlog_sum.trans hlog3)
                (Finset.sum_nonneg (fun j hj => by
                  have hj_lt : j < k := Finset.mem_range.mp hj
                  have hspecj := initLSFWith_spec hG₀ hV₀ hℓ₀
                    (hv_pos j hj_lt.le) hk_real (hp j hj_lt)
                  have h0 : 0 ≤ (S₀ j).wstr e := by
                    by_cases hth : thresh ≤ levelStretchBound (S₀ j).T₀ (S₀ j).r₀ (S₀ j).π G₀
                        (safeLen G₀ ℓ₀) e
                    · linarith [(hspecj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e heG₀).2 hth |>.1]
                    · rw [(hspecj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e heG₀).1 (not_le.mp hth)]
                      have hlen := levelStretchBound_ge_two hspecj.2.2.2.2.2.2.2.2.2.1 (S₀ j).π G₀
                        (fun g _ => safeLen_nonneg hℓ₀ g)
                        (by rw [safeLen_eq_of_mem ℓ₀ heG₀]; exact hℓ₀ e heG₀)
                      linarith
                  exact div_nonneg h0 hρ_pos.le))
                (by positivity)
          _ = K * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by dsimp only [K]; ring
      rw [Finset.sum_congr rfl (fun j hj => by
        rw [(he_surv_all j (Finset.mem_range.mp hj)).2])]
      exact hsum_bd

open Classical in
/-- Existential uniform version of `lemma_5_5_approx_explicit` over fixed `(C_lsst, α, K_σ, K_ρ)`. -/
theorem lemma_5_5_approx (C_lsst α K_σ K_ρ : ℝ) (hKρ : 1 ≤ K_ρ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (G₀ : MGraph), G₀.IsValid → G₀.V.Nonempty →
        ∀ (ℓ₀ : ℕ → ℝ), (∀ e ∈ G₀.E, 0 < ℓ₀ e) →
        ∀ (k : ℕ), 1 ≤ k →
        ∀ (Us : List (List Update)), BatchesIsValid G₀ Us →
        ∀ (ℓ : ℕ → ℝ),
        (∀ e ∈ (Us.foldl MGraph.applyBatch G₀).E, 0 < ℓ e) →
        (∀ e ∈ G₀.E, e ∈ (Us.foldl MGraph.applyBatch G₀).E →
          e ∉ batchesInserted Us → ℓ e = ℓ₀ e) →
        ∀ (thresh ρ δ : ℝ),
        10 * (max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240)) * (k : ℝ) *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 6 ≤ ρ →
        ρ ≤ K_ρ * (max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240)) * (k : ℝ) *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 6 →
        0 ≤ δ → δ ≤ 1 / (20 * (k : ℝ)) →
        ∀ (v : ℕ → ℕ → ℝ) (T_raw : ℕ → MGraph) (r₀ : ℕ → ℕ)
          (C_reps : ℕ → Finset ℕ) (π : ℕ → ℕ → ℕ) (W_T : ℕ → Finset (Finset ℕ)),
        (∀ e ∈ G₀.E, v 0 e = 1) →
        (∀ j ≤ k, ∀ e ∈ G₀.E, 0 < v j e) →
        (∀ j < k, ValidLSFParams C_lsst α thresh K_σ G₀ ℓ₀ (v j) (k : ℝ)
          (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j)) →
        (∀ j < k, ∀ e ∈ G₀.E,
          (1 - δ) * v j e * Real.exp
              ((initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh).wstr e / ρ)
            ≤ v (j + 1) e ∧
          v (j + 1) e ≤ (1 + δ) * v j e * Real.exp
              ((initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh).wstr e / ρ)) →
        let G := Us.foldl MGraph.applyBatch G₀
        let q := totalUpdates Us
        let S₀ : ℕ → LSFState := fun j =>
          initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh
        let S : ℕ → LSFState := fun j => applyLSFBatches (S₀ j) Us
        (∀ j < k,
          S j = applyLSFBatches (S₀ j) Us ∧
          (S j).G = G ∧
          (S j).insertedEdges = batchesInserted Us ∧
          (S j).RF.F.E ⊆ (S₀ j).RF.F.E ∧
          G.IsSubgraph (S j).RF.F ∧
          (S j).T.IsSubgraph (S j).RF.F ∧
          (∀ e ∈ (S j).insertedEdges, (S j).wstr e = 1) ∧
          (∀ e ∈ G.E, e ∉ (S j).insertedEdges → (S j).wstr e = (S₀ j).wstr e) ∧
          ((components (S₀ j).RF.F).card : ℝ) ≤
            (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
              else ((components G₀).card : ℝ) * K * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
              K * ((G₀.E.card : ℝ) / (k : ℝ)) ∧
          ((components (S j).RF.F).card : ℝ) ≤ ((components (S₀ j).RF.F).card : ℝ) +
            K * (q : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ∧
          (S j).lsf.Holds G ℓ (K * (k : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 6) ∧
          ((S j).W_init.card : ℝ) ≤
            6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
              else ((components G₀).card : ℝ) * K * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
              K * ((G₀.E.card : ℝ) / (k : ℝ)) ∧
          (S j).W_init.biUnion (inducedEdges (S₀ j).RF.F) = (S₀ j).RF.F.E ∧
          (∀ W₁ ∈ (S j).W_init, ∀ W₂ ∈ (S j).W_init, W₁ ≠ W₂ →
            Disjoint (inducedEdges (S₀ j).RF.F W₁) (inducedEdges (S₀ j).RF.F W₂)) ∧
          boundary (S j).W_init ⊆ (S j).R ∧
          ∀ W ∈ (S j).W_init, PathConvex (S j).T₀ W ∧ W ⊆ G.V ∧
            (pieceBoundary (S j).W_init W).card ≤ 1 ∧
            (G.vol (W \ (S j).R) : ℝ) ≤ K * (k : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) ∧
        ∀ e ∈ G.E,
          ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (S j).wstr e ≤
            K * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by
  let K₀ := max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240)
  have hK_pos : 0 < 3 * K_ρ * K₀ := by
    have : (2240 : ℝ) ≤ K₀ := (le_max_right _ _).trans (le_max_right _ _)
    positivity
  refine ⟨3 * K_ρ * K₀, hK_pos, ?_⟩
  intro G₀ hG₀ hV₀ ℓ₀ hℓ₀ k hk Us hUs ℓ hℓ hℓ_orig thresh ρ δ hρ_lo hρ_hi hδ0 hδ1
    v T_raw r₀ C_reps π W_T hv0 hv_pos hp hv_step
  exact (lemma_5_5_approx_explicit C_lsst α K_σ K_ρ hKρ G₀ hG₀ hV₀ ℓ₀ hℓ₀ k hk Us hUs
    ℓ hℓ hℓ_orig thresh ρ δ hρ_lo hρ_hi ⟨hδ0, hδ1⟩ v T_raw r₀ C_reps π W_T hv0 hv_pos hp
    hv_step).2

/-! ## Exact `lemma_5_5` as the `δ = 0`, `K_ρ = 10` special case -/

private noncomputable def exactMWUWeights (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C_lsst : ℝ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k : ℕ) (ρ : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | j + 1, e =>
    let vj := exactMWUWeights oracle C_lsst G₀ ℓ₀ k ρ j
    let Sj := initLSF oracle C_lsst G₀ ℓ₀ vj (k : ℝ)
    vj e * Real.exp (Sj.wstr e / ρ)

private lemma exactMWUWeights_pos (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C_lsst : ℝ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k : ℕ) (ρ : ℝ) (j e : ℕ) :
    0 < exactMWUWeights oracle C_lsst G₀ ℓ₀ k ρ j e := by
  induction j generalizing e with
  | zero => exact zero_lt_one
  | succ j ih => exact mul_pos (ih e) (Real.exp_pos _)

open Classical in
/-- Exact `lemma_5_5` derived directly from `lemma_5_5_approx` at `δ = 0, K_ρ = 10, α = 1`. -/
theorem lemma_5_5_of_approx (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hLSST : HasLSSTSpec oracle C_lsst) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (G₀ : MGraph), G₀.IsValid → G₀.V.Nonempty →
        ∀ (ℓ₀ : ℕ → ℝ), (∀ e ∈ G₀.E, 0 < ℓ₀ e) →
        ∀ (k : ℕ), 1 ≤ k →
        ∀ (Us : List (List Update)), BatchesIsValid G₀ Us →
        ∀ (ℓ : ℕ → ℝ),
        (∀ e ∈ (Us.foldl MGraph.applyBatch G₀).E, 0 < ℓ e) →
        (∀ e ∈ G₀.E, e ∈ (Us.foldl MGraph.applyBatch G₀).E →
          e ∉ batchesInserted Us → ℓ e = ℓ₀ e) →
        let G := Us.foldl MGraph.applyBatch G₀
        let q := totalUpdates Us
        ∃ S₀ S : ℕ → LSFState,
          (∀ j < k,
            S j = applyLSFBatches (S₀ j) Us ∧
            (S j).G = G ∧
            (S j).insertedEdges = batchesInserted Us ∧
            (S j).RF.F.E ⊆ (S₀ j).RF.F.E ∧
            G.IsSubgraph (S j).RF.F ∧
            (S j).T.IsSubgraph (S j).RF.F ∧
            (∀ e ∈ (S j).insertedEdges, (S j).wstr e = 1) ∧
            (∀ e ∈ G.E, e ∉ (S j).insertedEdges → (S j).wstr e = (S₀ j).wstr e) ∧
            ((components (S₀ j).RF.F).card : ℝ) ≤
              (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
                else ((components G₀).card : ℝ) * K * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
                K * ((G₀.E.card : ℝ) / (k : ℝ)) ∧
            ((components (S j).RF.F).card : ℝ) ≤ ((components (S₀ j).RF.F).card : ℝ) +
              K * (q : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ∧
            (S j).lsf.Holds G ℓ (K * (k : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 6) ∧
            ((S j).W_init.card : ℝ) ≤
              6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
                else ((components G₀).card : ℝ) * K * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
                K * ((G₀.E.card : ℝ) / (k : ℝ)) ∧
            (S j).W_init.biUnion (inducedEdges (S₀ j).RF.F) = (S₀ j).RF.F.E ∧
            (∀ W₁ ∈ (S j).W_init, ∀ W₂ ∈ (S j).W_init, W₁ ≠ W₂ →
              Disjoint (inducedEdges (S₀ j).RF.F W₁) (inducedEdges (S₀ j).RF.F W₂)) ∧
            boundary (S j).W_init ⊆ (S j).R ∧
            ∀ W ∈ (S j).W_init, PathConvex (S j).T₀ W ∧ W ⊆ G.V ∧
              (pieceBoundary (S j).W_init W).card ≤ 1 ∧
              (G.vol (W \ (S j).R) : ℝ) ≤ K * (k : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) ∧
          ∀ e ∈ G.E,
            ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (S j).wstr e ≤
              K * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by
  obtain ⟨K, hK_pos, h55⟩ := lemma_5_5_approx C_lsst 1 (6272 * max 1 C_lsst) 10 (by norm_num)
  refine ⟨K, hK_pos, ?_⟩
  intro G₀ hG₀ hV₀ ℓ₀ hℓ₀ k hk Us hUs ℓ hℓ hℓ_orig
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  let K₀ := max (6272 * max 1 C_lsst) (max (112 * (1 + 1) * max 1 C_lsst) 2240)
  let ρ := 10 * K₀ * (k : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 6
  let v := exactMWUWeights oracle C_lsst G₀ ℓ₀ k ρ
  let G_v : ℕ → MGraph := fun j => weightedCopyGraph G₀ (v j)
  let ℓ_v := weightedCopyLen G₀ ℓ₀
  let T_raw : ℕ → MGraph := fun j =>
    if G₀.E.Nonempty then oracle (G_v j) ℓ_v (fun _ => 1) else oracle G₀ (fun _ => 1) (fun _ => 1)
  let T₀ : ℕ → MGraph := fun j => projectTree G₀ (v j) (T_raw j)
  let r₀ : ℕ → ℕ := fun _ => pickRoot G₀
  let π : ℕ → ℕ → ℕ := fun j =>
    if G₀.E.Nonempty then congOrder (T₀ j) (congestion (G_v j) (T₀ j) ℓ_v)
    else congOrder (T₀ j) (congestion G₀ (T₀ j) (fun _ => 1))
  let W_T : ℕ → Finset (Finset ℕ) := fun j => pickDecomp G₀ (T₀ j) (r₀ j) (k : ℝ)
  let thresh := wstrThresh C_lsst G₀.n (k : ℝ)
  have hp : ∀ j < k, ValidLSFParams C_lsst 1 thresh (6272 * max 1 C_lsst) G₀ ℓ₀ (v j) (k : ℝ)
      (T_raw j) (r₀ j) (compReps G₀ (r₀ j)) (π j) (W_T j) := fun j _ =>
    validLSFParams_initLSF hLSST hG₀ hV₀ hℓ₀ (fun e _ => exactMWUWeights_pos _ _ _ _ _ _ j e) hk_real
  have hS_eq : ∀ j, initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j)
      (compReps G₀ (r₀ j)) (π j) (W_T j) thresh =
      initLSF oracle C_lsst G₀ ℓ₀ (v j) (k : ℝ) := fun j =>
    (initLSF_eq_initLSFWith oracle C_lsst G₀ ℓ₀ (v j) (k : ℝ)).symm
  refine ⟨fun j => initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j)
      (compReps G₀ (r₀ j)) (π j) (W_T j) thresh,
    fun j => applyLSFBatches (initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j)
      (compReps G₀ (r₀ j)) (π j) (W_T j) thresh) Us, ?_⟩
  exact h55 G₀ hG₀ hV₀ ℓ₀ hℓ₀ k hk Us hUs ℓ hℓ hℓ_orig thresh ρ 0 le_rfl le_rfl le_rfl
    (by positivity) v T_raw r₀ (fun j => compReps G₀ (r₀ j)) π W_T
    (fun _ _ => rfl) (fun j _ e _ => exactMWUWeights_pos _ _ _ _ _ _ j e) hp
    (fun j _ e _ => by
      have hv_def : v (j + 1) e = v j e * Real.exp ((initLSF oracle C_lsst G₀ ℓ₀ (v j) (k : ℝ)).wstr e / ρ) := rfl
      rw [hS_eq j]
      simp only [sub_zero, add_zero, one_mul, ← hv_def]
      exact ⟨le_rfl, le_rfl⟩)

end MinCostFlow.LSF
