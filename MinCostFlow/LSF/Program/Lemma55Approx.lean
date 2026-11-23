module

public import MinCostFlow.LSF.Lemma55
public import MinCostFlow.LSF.Lemma54With
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Approximate-Weight Multiplicative Weights Update for Lemma 5.5 (`Lemma55Approx`)

Generalizes `MinCostFlow.LSF.lemma_5_5` (`Lemma 5.5`, `arXiv:2309.16629v1` page 17 and Appendix A.2
pages 48–49) in three ways required by the deterministic Word-RAM implementation:

1. Works directly with `initLSFWith` and `ValidLSFParams` (`Lemma54With`), matching `lsfInitPost`
   without requiring a single fixed oracle.
2. Allows an arbitrary step denominator `ρ` with `10 * U ≤ ρ ≤ C_ρ * U` (so the Word-RAM program
   can use an integer `ρ_nat` built from `Nat.log 2 (n + 2) + 1`).
3. Allows fixed-point rounding in every weight update:
   `(1 - δ) * v_j(e) * exp(wstr_j(e) / ρ) ≤ v_{j+1}(e) ≤ (1 + δ) * v_j(e) * exp(wstr_j(e) / ρ)`
   with `0 ≤ δ ≤ 1 / (4 * k)`.

Also proves the uniform weight envelope `1 / 2 ≤ v_j(e) ≤ 8 * m₀` for all `j ≤ k` and `e ∈ G₀.E`
(`approx_mwu_weight_bounds`), guaranteeing that all intermediate weights stay in `O(log m₀)` integer
bits independent of `k`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF

/-! ## Elementary exponential-rounding inequalities -/

private lemma one_sub_ge_exp_neg_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-(2 * x)) ≤ 1 - x := by
  have hpos : 0 < 1 - x := by linarith
  have h3 : (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
    have h4 : 1 / (1 - x) = (1 - x)⁻¹ := one_div _
    rw [← h4]
    have hquad : 1 / (1 - x) ≤ 1 + 2 * x := by
      rw [div_le_iff₀ hpos]; nlinarith
    exact hquad.trans (by linarith [Real.add_one_le_exp (2 * x)])
  have h4 : (Real.exp (2 * x))⁻¹ ≤ 1 - x := by
    have := inv_anti₀ (inv_pos.mpr hpos) h3
    simpa only [inv_inv] using this
  rwa [Real.exp_neg]

private lemma exp_le_one_add_two_mul' {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + 2 * x := by
  have hsub : 0 < 1 - x := by linarith
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h2 : Real.exp x ≤ (1 - x)⁻¹ := by
    have := inv_anti₀ hsub h1
    simpa [Real.exp_neg] using this
  have h3 : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_le_iff_one_le_mul₀' hsub]
    nlinarith
  exact h2.trans h3

private lemma exp_half_lt_two' : Real.exp (1 / 2 : ℝ) < 2 := by
  have h1 : (3 / 4 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) := by linarith [Real.add_one_le_exp (-(1 / 4 : ℝ))]
  have h2 : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
    rw [show (1 / 4 : ℝ) = -(-(1 / 4 : ℝ)) by ring, Real.exp_neg]
    calc (Real.exp (-(1 / 4 : ℝ)))⁻¹ ≤ (3 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h1
      _ = 4 / 3 := by norm_num
  have hsq : Real.exp (1 / 4 : ℝ) ^ 2 = Real.exp (1 / 2 : ℝ) := by
    rw [← Real.exp_nat_mul]; norm_num
  have hle := pow_le_pow_left₀ (Real.exp_pos _).le h2 2
  rw [hsq] at hle
  norm_num at hle
  linarith

private lemma exp_two_le_eight' : Real.exp (2 : ℝ) ≤ 8 := by
  have h1 : (15 / 16 : ℝ) ≤ Real.exp (-(1 / 16 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(1 / 16 : ℝ))]
  have h2 : Real.exp (1 / 16 : ℝ) ≤ 16 / 15 := by
    rw [show (1 / 16 : ℝ) = -(-(1 / 16 : ℝ)) by ring, Real.exp_neg]
    calc (Real.exp (-(1 / 16 : ℝ)))⁻¹ ≤ (15 / 16 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h1
      _ = 16 / 15 := by norm_num
  have hpow : Real.exp (1 / 16 : ℝ) ^ 32 = Real.exp (2 : ℝ) := by
    rw [← Real.exp_nat_mul]; norm_num
  have hle := pow_le_pow_left₀ (Real.exp_pos _).le h2 32
  rw [hpow] at hle
  norm_num at hle
  linarith

private lemma half_lt_log_add_two' (n : ℕ) : (1 / 2 : ℝ) < Real.log ((n : ℝ) + 2) := by
  have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rw [← Real.exp_lt_exp, Real.exp_log (by linarith)]
  linarith [exp_half_lt_two']

private lemma applyLSFBatches_insertedEdges' (Us : List (List Update)) (S : LSFState) :
    (applyLSFBatches S Us).insertedEdges = Us.foldl (List.foldl updateInserted) S.insertedEdges := by
  induction Us generalizing S with
  | nil => rfl
  | cons U Us ih =>
    have h1 : ∀ (V : List Update) (T : LSFState),
        (applyLSFBatch T V).insertedEdges = V.foldl updateInserted T.insertedEdges := by
      intro V
      induction V with
      | nil => intro _; rfl
      | cons u V ihV =>
        intro T
        change (applyLSFBatch (applyLSFUpdate T u) V).insertedEdges = _
        rw [ihV]
        cases u <;> rfl
    change (applyLSFBatches (applyLSFBatch S U) Us).insertedEdges = _
    rw [ih, h1]
    rfl

private lemma batches_E_surv_orig' (G₀ : MGraph) (Us : List (List Update)) :
    ∀ e ∈ (Us.foldl MGraph.applyBatch G₀).E, e ∉ batchesInserted Us → e ∈ G₀.E := by
  have hstep : ∀ (G : MGraph) (I : Finset ℕ) (u : Update) (e : ℕ),
      e ∈ (G.applyUpdate u).E → e ∉ updateInserted I u → e ∈ G.E ∧ e ∉ I := by
    intro G I u e he hn
    cases u with
    | insert e_new _ _ =>
      dsimp only [MGraph.applyUpdate] at he; dsimp only [updateInserted] at hn
      rw [Finset.mem_insert] at he hn
      obtain ⟨hne, hI⟩ := not_or.mp hn
      exact ⟨he.resolve_left hne, hI⟩
    | delete e_del =>
      dsimp only [MGraph.applyUpdate] at he; dsimp only [updateInserted] at hn
      rw [Finset.mem_erase] at he
      exact ⟨he.2, fun h => hn (Finset.mem_erase.mpr ⟨he.1, h⟩)⟩
    | split _ _ _ _ => exact ⟨he, hn⟩
  have hbatch : ∀ (U : List Update) (G : MGraph) (I : Finset ℕ),
      (∀ f ∈ G.E, f ∉ I → f ∈ G₀.E) →
      ∀ f ∈ (G.applyBatch U).E, f ∉ U.foldl updateInserted I → f ∈ G₀.E := by
    intro U
    induction U with
    | nil => intro G I h f hf hn; exact h f hf hn
    | cons u U ih =>
      intro G I h f hf hn
      exact ih (G.applyUpdate u) (updateInserted I u)
        (fun x hx hxn => let p := hstep G I u x hx hxn; h x p.1 p.2) f hf hn
  have hgo : ∀ (Vs : List (List Update)) (G : MGraph) (I : Finset ℕ),
      (∀ f ∈ G.E, f ∉ I → f ∈ G₀.E) →
      ∀ f ∈ (Vs.foldl MGraph.applyBatch G).E,
        f ∉ Vs.foldl (List.foldl updateInserted) I → f ∈ G₀.E := by
    intro Vs
    induction Vs with
    | nil => intro G I h f hf hn; exact h f hf hn
    | cons V Vs ih =>
      intro G I h f hf hn
      exact ih (G.applyBatch V) (V.foldl updateInserted I) (hbatch V G I h) f hf hn
  exact hgo Us G₀ ∅ (fun _ hf _ => hf)

/-! ## Explicit `K₀` for `ValidLSFParams` and uniform weight envelope -/

lemma one_le_stretch_safeLen' {RF : RootedForest} {G₀ : MGraph} {ℓ₀ : ℕ → ℝ}
    (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) {e : ℕ} (he : e ∈ G₀.E) :
    1 ≤ RF.stretch G₀ (safeLen G₀ ℓ₀) e := by
  unfold RootedForest.stretch
  dsimp only
  have he_pos : 0 < safeLen G₀ ℓ₀ e := by
    rw [safeLen_eq_of_mem ℓ₀ he]
    exact hℓ₀ e he
  have hw_nn : ∀ P, 0 ≤ walkLength (safeLen G₀ ℓ₀) P := fun P =>
    Finset.sum_nonneg fun f _ => mul_nonneg (safeLen_nonneg hℓ₀ f) (abs_nonneg _)
  split_ifs
  · exact le_add_of_nonneg_right (div_nonneg (hw_nn _) he_pos.le)
  · exact le_add_of_nonneg_right (div_nonneg (add_nonneg (hw_nn _) (hw_nn _)) he_pos.le)

/-- Explicit Lemma 5.4 constant matching `lemma_5_4_with_explicit`. -/
noncomputable def lemma54K0 (C_lsst α K_σ : ℝ) : ℝ :=
  max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240)

lemma lemma54K0_ge (C_lsst α K_σ : ℝ) : 2240 ≤ lemma54K0 C_lsst α K_σ :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- Uniform weight lower and upper bounds across `j ≤ k` steps of approximate MWU:
every active edge weight stays inside `[1 / 2, 8 * m₀]` (independent of `k`!), and the `L¹`-norm
satisfies `‖v j‖₁ ≤ exp(j * (δ + 2 * W / ρ)) * m₀`. -/
theorem approx_mwu_weight_bounds
    {G₀ : MGraph} {k : ℕ} (hk : 1 ≤ k)
    {W U ρ δ : ℝ} (hW_nn : 0 ≤ W) (hU_pos : 0 < U)
    (hρ_ge : 10 * U ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / (4 * (k : ℝ)))
    (hWU : (k : ℝ) * (2 * W / ρ) ≤ 1)
    {v : ℕ → ℕ → ℝ} {wstr : ℕ → ℕ → ℝ}
    (hv0 : ∀ e ∈ G₀.E, v 0 e = 1)
    (hv_pos : ∀ j ≤ k, ∀ e ∈ G₀.E, 0 < v j e)
    (hw_bd : ∀ j < k, ∀ e ∈ G₀.E, 1 ≤ wstr j e ∧ wstr j e ≤ U)
    (hw_sum : ∀ j < k, ∑ e ∈ G₀.E, v j e * wstr j e ≤ W * G₀.norm1 (v j))
    (hv_step : ∀ j < k, ∀ e ∈ G₀.E,
      (1 - δ) * v j e * Real.exp (wstr j e / ρ) ≤ v (j + 1) e ∧
      v (j + 1) e ≤ (1 + δ) * v j e * Real.exp (wstr j e / ρ)) :
    (∀ j ≤ k, G₀.norm1 (v j) ≤ Real.exp ((j : ℝ) * (δ + 2 * W / ρ)) * (G₀.E.card : ℝ)) ∧
    (∀ j ≤ k, ∀ e ∈ G₀.E,
      Real.exp (-(2 * (j : ℝ) * δ) + (∑ i ∈ Finset.range j, wstr i e) / ρ) ≤ v j e) ∧
    (∀ j ≤ k, ∀ e ∈ G₀.E, (1 / 2 : ℝ) ≤ v j e ∧ v j e ≤ 8 * (G₀.E.card : ℝ)) := by
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hρ_pos : 0 < ρ := by linarith
  have hδ_half : δ ≤ 1 / 2 := by
    have : 1 / (4 * (k : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    exact hδ_le.trans this
  have hnorm1_eq : ∀ j ≤ k, G₀.norm1 (v j) = ∑ e ∈ G₀.E, v j e := fun j hj =>
    Finset.sum_congr rfl fun e he => abs_of_pos (hv_pos j hj e he)
  have hnorm1_le : ∀ j ≤ k, G₀.norm1 (v j) ≤ Real.exp ((j : ℝ) * (δ + 2 * W / ρ)) * (G₀.E.card : ℝ) := by
    intro j hj
    induction j with
    | zero =>
      rw [hnorm1_eq 0 (Nat.zero_le _)]
      simp only [Nat.cast_zero, zero_mul, Real.exp_zero, one_mul]
      rw [Finset.sum_congr rfl fun e he => hv0 e he]
      simp
    | succ j ih =>
      have hj_lt : j < k := hj
      have hpt : ∀ e ∈ G₀.E, v (j + 1) e ≤ Real.exp δ * (v j e + (2 / ρ) * (v j e * wstr j e)) := by
        intro e he
        have hb := hw_bd j hj_lt e he
        have hx0 : 0 ≤ wstr j e / ρ := div_nonneg (by linarith) hρ_pos.le
        have hx1 : wstr j e / ρ ≤ 1 / 2 := by rw [div_le_iff₀ hρ_pos]; linarith [hb.2]
        have hexp := exp_le_one_add_two_mul' hx0 hx1
        have h1d : 1 + δ ≤ Real.exp δ := by linarith [Real.add_one_le_exp δ]
        have hvj := (hv_pos j (Nat.le_of_lt hj_lt) e he).le
        have hstep_u := (hv_step j hj_lt e he).2
        calc v (j + 1) e
            ≤ (1 + δ) * v j e * Real.exp (wstr j e / ρ) := hstep_u
          _ ≤ Real.exp δ * v j e * (1 + 2 * (wstr j e / ρ)) := by
              have hA : (1 + δ) * v j e ≤ Real.exp δ * v j e := mul_le_mul_of_nonneg_right h1d hvj
              have hB : 0 ≤ (1 + δ) * v j e := by positivity
              exact mul_le_mul hA hexp (Real.exp_pos _).le (by positivity)
          _ = Real.exp δ * (v j e + (2 / ρ) * (v j e * wstr j e)) := by ring
      have hsum : G₀.norm1 (v (j + 1)) ≤ Real.exp δ * (G₀.norm1 (v j) + (2 / ρ) * (W * G₀.norm1 (v j))) := by
        calc G₀.norm1 (v (j + 1))
            = ∑ e ∈ G₀.E, v (j + 1) e := hnorm1_eq (j + 1) hj
          _ ≤ ∑ e ∈ G₀.E, Real.exp δ * (v j e + (2 / ρ) * (v j e * wstr j e)) := Finset.sum_le_sum hpt
          _ = Real.exp δ * ((∑ e ∈ G₀.E, v j e) + (2 / ρ) * ∑ e ∈ G₀.E, v j e * wstr j e) := by
              rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.mul_sum]
          _ = Real.exp δ * (G₀.norm1 (v j) + (2 / ρ) * ∑ e ∈ G₀.E, v j e * wstr j e) := by
              rw [← hnorm1_eq j (Nat.le_of_lt hj_lt)]
          _ ≤ Real.exp δ * (G₀.norm1 (v j) + (2 / ρ) * (W * G₀.norm1 (v j))) := by
              refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (Real.exp_pos _).le
              exact mul_le_mul_of_nonneg_left (hw_sum j hj_lt) (div_nonneg zero_le_two hρ_pos.le)
      have hnorm_nn : 0 ≤ G₀.norm1 (v j) := by
        rw [hnorm1_eq j (Nat.le_of_lt hj_lt)]
        exact Finset.sum_nonneg fun e he => (hv_pos j (Nat.le_of_lt hj_lt) e he).le
      have hstep_norm : G₀.norm1 (v (j + 1)) ≤ Real.exp (δ + 2 * W / ρ) * G₀.norm1 (v j) := by
        have hfac : G₀.norm1 (v j) + (2 / ρ) * (W * G₀.norm1 (v j)) = (1 + 2 * W / ρ) * G₀.norm1 (v j) := by ring
        have hexp1 : 1 + 2 * W / ρ ≤ Real.exp (2 * W / ρ) := by linarith [Real.add_one_le_exp (2 * W / ρ)]
        rw [hfac] at hsum
        calc G₀.norm1 (v (j + 1))
            ≤ Real.exp δ * ((1 + 2 * W / ρ) * G₀.norm1 (v j)) := hsum
          _ ≤ Real.exp δ * (Real.exp (2 * W / ρ) * G₀.norm1 (v j)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp1 hnorm_nn) (Real.exp_pos _).le
          _ = Real.exp (δ + 2 * W / ρ) * G₀.norm1 (v j) := by rw [← mul_assoc, ← Real.exp_add]
      calc G₀.norm1 (v (j + 1))
          ≤ Real.exp (δ + 2 * W / ρ) * G₀.norm1 (v j) := hstep_norm
        _ ≤ Real.exp (δ + 2 * W / ρ) * (Real.exp ((j : ℝ) * (δ + 2 * W / ρ)) * (G₀.E.card : ℝ)) :=
            mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hj_lt)) (Real.exp_pos _).le
        _ = Real.exp (((j + 1 : ℕ) : ℝ) * (δ + 2 * W / ρ)) * (G₀.E.card : ℝ) := by
            push_cast; rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  have hv_lb : ∀ j ≤ k, ∀ e ∈ G₀.E,
      Real.exp (-(2 * (j : ℝ) * δ) + (∑ i ∈ Finset.range j, wstr i e) / ρ) ≤ v j e := by
    intro j hj e he
    induction j with
    | zero => simp [hv0 e he]
    | succ j ih =>
      have hj_lt : j < k := hj
      have h1md : Real.exp (-(2 * δ)) ≤ 1 - δ := one_sub_ge_exp_neg_two hδ0 hδ_half
      have hstep_l := (hv_step j hj_lt e he).1
      have hih := ih (Nat.le_of_lt hj_lt)
      calc Real.exp (-(2 * ((j + 1 : ℕ) : ℝ) * δ) + (∑ i ∈ Finset.range (j + 1), wstr i e) / ρ)
          = Real.exp (-(2 * δ)) *
            Real.exp (-(2 * (j : ℝ) * δ) + (∑ i ∈ Finset.range j, wstr i e) / ρ) *
            Real.exp (wstr j e / ρ) := by
              rw [Finset.sum_range_succ, add_div, ← Real.exp_add, ← Real.exp_add]
              congr 1; push_cast; ring
        _ ≤ (1 - δ) * v j e * Real.exp (wstr j e / ρ) := by
              have hA := mul_le_mul h1md hih (Real.exp_pos _).le (by linarith)
              exact mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
        _ ≤ v (j + 1) e := hstep_l
  refine ⟨hnorm1_le, hv_lb, fun j hj e he => ⟨?_, ?_⟩⟩
  · -- `1 / 2 ≤ v j e`
    have hsum_nn : 0 ≤ (∑ i ∈ Finset.range j, wstr i e) / ρ :=
      div_nonneg (Finset.sum_nonneg fun i hi => by linarith [(hw_bd i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj) e he).1])
        hρ_pos.le
    have hj_le_k : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hj
    have h2jd : 2 * (j : ℝ) * δ ≤ 1 / 2 := by
      have h1 : 2 * (j : ℝ) * δ ≤ 2 * (k : ℝ) * (1 / (4 * (k : ℝ))) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hj_le_k zero_le_two) hδ_le hδ0 (by positivity)
      have h2 : 2 * (k : ℝ) * (1 / (4 * (k : ℝ))) = 1 / 2 := by field_simp [ne_of_gt hk_pos]; ring
      linarith
    have hhalf : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
      have h1 := one_sub_ge_exp_neg_two (x := 1 / 4) (by norm_num) (by norm_num)
      have : -(2 * (1 / 4 : ℝ)) = -(1 / 2) := by norm_num
      linarith [Real.add_one_le_exp (-(1 / 2 : ℝ))]
    calc (1 / 2 : ℝ)
        ≤ Real.exp (-(1 / 2)) := hhalf
      _ ≤ Real.exp (-(2 * (j : ℝ) * δ) + (∑ i ∈ Finset.range j, wstr i e) / ρ) :=
          Real.exp_le_exp.mpr (by linarith)
      _ ≤ v j e := hv_lb j hj e he
  · -- `v j e ≤ 8 * m₀`
    have hj_le_k : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hj
    have hkd : (k : ℝ) * δ ≤ 1 / 4 := by
      have h1 := mul_le_mul_of_nonneg_left hδ_le hk_pos.le
      have h2 : (k : ℝ) * (1 / (4 * (k : ℝ))) = 1 / 4 := by field_simp [ne_of_gt hk_pos]
      linarith
    have hrate_nn : 0 ≤ δ + 2 * W / ρ := add_nonneg hδ0 (div_nonneg (by linarith) hρ_pos.le)
    have hexp_arg : (j : ℝ) * (δ + 2 * W / ρ) ≤ 2 := by
      calc (j : ℝ) * (δ + 2 * W / ρ)
          ≤ (k : ℝ) * (δ + 2 * W / ρ) := mul_le_mul_of_nonneg_right hj_le_k hrate_nn
        _ = (k : ℝ) * δ + (k : ℝ) * (2 * W / ρ) := by ring
        _ ≤ 1 / 4 + 1 := add_le_add hkd hWU
        _ ≤ 2 := by norm_num
    have hexp2_le_8 : Real.exp 2 ≤ 8 := exp_two_le_eight'
    have hle_norm : v j e ≤ G₀.norm1 (v j) := by
      rw [hnorm1_eq j hj]
      exact Finset.single_le_sum (fun f hf => (hv_pos j hj f hf).le) he
    calc v j e
        ≤ G₀.norm1 (v j) := hle_norm
      _ ≤ Real.exp ((j : ℝ) * (δ + 2 * W / ρ)) * (G₀.E.card : ℝ) := hnorm1_le j hj
      _ ≤ Real.exp 2 * (G₀.E.card : ℝ) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp_arg) (Nat.cast_nonneg _)
      _ ≤ 8 * (G₀.E.card : ℝ) := mul_le_mul_of_nonneg_right hexp2_le_8 (Nat.cast_nonneg _)

/-! ## Approximate-weight Lemma 5.5 -/

open Classical in
/-- Approximate-weight version of Lemma 5.5 (`arXiv:2309.16629v1` page 17, Appendix A.2 pages 48–49)
for `k` `initLSFWith` copies initialized with approximate multiplicative weights `v_j` satisfying
relative error `δ ≤ 1 / (4 * k)` per step and denominator `10 * U ≤ ρ ≤ C_ρ * U`. -/
theorem lemma_5_5_approx (C_lsst α K_σ C_ρ : ℝ) (hCρ : 10 ≤ C_ρ) :
    let K₀ := lemma54K0 C_lsst α K_σ
    let K := (16 + 4 * C_ρ) * K₀ + 128
    0 < K ∧
    ∀ (G₀ : MGraph) (_hG₀ : G₀.IsValid) (_hV₀ : G₀.V.Nonempty)
      (ℓ₀ : ℕ → ℝ) (_hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
      (k : ℕ) (_hk : 1 ≤ k)
      (ρ δ : ℝ)
      (_hρ_ge : 10 * (K₀ * (k : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 6) ≤ ρ)
      (_hρ_le : ρ ≤ C_ρ * (K₀ * (k : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 6))
      (_hδ0 : 0 ≤ δ) (_hδ_le : δ ≤ 1 / (4 * (k : ℝ)))
      (v : ℕ → ℕ → ℝ) (S₀ : ℕ → LSFState)
      (_hv0 : ∀ e ∈ G₀.E, v 0 e = 1)
      (_hv_pos : ∀ j ≤ k, ∀ e ∈ G₀.E, 0 < v j e)
      (_hinit : ∀ j < k, ∃ T_raw r₀ C_reps π W_T thresh,
        ValidLSFParams C_lsst α thresh K_σ G₀ ℓ₀ (v j) (k : ℝ) T_raw r₀ C_reps π W_T ∧
        S₀ j = initLSFWith G₀ ℓ₀ (v j) (k : ℝ) T_raw r₀ C_reps π W_T thresh)
      (_hv_step : ∀ j < k, ∀ e ∈ G₀.E,
        (1 - δ) * v j e * Real.exp ((S₀ j).wstr e / ρ) ≤ v (j + 1) e ∧
        v (j + 1) e ≤ (1 + δ) * v j e * Real.exp ((S₀ j).wstr e / ρ))
      (Us : List (List Update)) (_hUs : BatchesIsValid G₀ Us)
      (ℓ : ℕ → ℝ)
      (_hℓ : ∀ e ∈ (Us.foldl MGraph.applyBatch G₀).E, 0 < ℓ e)
      (_hℓ_orig : ∀ e ∈ G₀.E, e ∈ (Us.foldl MGraph.applyBatch G₀).E →
        e ∉ batchesInserted Us → ℓ e = ℓ₀ e),
      let G := Us.foldl MGraph.applyBatch G₀
      let q := totalUpdates Us
      let S : ℕ → LSFState := fun j => applyLSFBatches (S₀ j) Us
      (∀ j < k,
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
  set K₀ := lemma54K0 C_lsst α K_σ
  set K := (16 + 4 * C_ρ) * K₀ + 128
  have hK₀_2240 : 2240 ≤ K₀ := lemma54K0_ge C_lsst α K_σ
  have hK₀_pos : 0 < K₀ := by linarith
  have hK₀_le_K : K₀ ≤ K := by nlinarith
  refine ⟨by nlinarith, ?_⟩
  intro G₀ hG₀ hV₀ ℓ₀ hℓ₀ k hk ρ δ hρ_ge hρ_le hδ0 hδ_le v S₀ hv0 hv_pos hinit hv_step
    Us hUs ℓ hℓ hℓ_orig G q S
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hL : (1 / 2 : ℝ) < Real.log ((G₀.n : ℝ) + 2) := half_lt_log_add_two' G₀.n
  have hL_pos : 0 < Real.log ((G₀.n : ℝ) + 2) := by linarith
  have hLm : (1 / 2 : ℝ) < Real.log ((G₀.E.card : ℝ) + 2) := half_lt_log_add_two' G₀.E.card
  have hLm_pos : 0 < Real.log ((G₀.E.card : ℝ) + 2) := by linarith
  set L := Real.log ((G₀.n : ℝ) + 2)
  set W := K₀ * L ^ 4
  set U := K₀ * (k : ℝ) * L ^ 6
  have hU_pos : 0 < U := mul_pos (mul_pos hK₀_pos hk_pos) (pow_pos hL_pos 6)
  have hρ_pos : 0 < ρ := by linarith
  have hins_eq : ∀ j < k, (S j).insertedEdges = batchesInserted Us := by
    intro j hj
    obtain ⟨T_raw, r₀, C_reps, π, W_T, thresh, _, hS₀⟩ := hinit j hj
    dsimp only [S]
    rw [applyLSFBatches_insertedEdges', hS₀]; rfl
  have h54_j : ∀ j < k,
      let Sj := S j
      Sj.G = G ∧
      Sj.RF.F.E ⊆ (S₀ j).RF.F.E ∧
      G.IsSubgraph Sj.RF.F ∧
      Sj.T.IsSubgraph Sj.RF.F ∧
      (∀ e ∈ Sj.insertedEdges, Sj.wstr e = 1) ∧
      (∀ e ∈ G.E, e ∉ Sj.insertedEdges → Sj.wstr e = (S₀ j).wstr e) ∧
      ((components (S₀ j).RF.F).card : ℝ) ≤
        (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
          else ((components G₀).card : ℝ) * K₀ * L ^ 2) + K₀ * ((G₀.E.card : ℝ) / (k : ℝ)) ∧
      ((components Sj.RF.F).card : ℝ) ≤ ((components (S₀ j).RF.F).card : ℝ) + K₀ * (q : ℝ) * L ^ 2 ∧
      Sj.lsf.Holds G ℓ (K₀ * (k : ℝ) * L ^ 6) ∧
      ∑ e ∈ G₀.E, v j e * (S₀ j).wstr e ≤ K₀ * G₀.norm1 (v j) * L ^ 4 ∧
      (Sj.W_init.card : ℝ) ≤
        6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
          else ((components G₀).card : ℝ) * K₀ * L ^ 2) + K₀ * ((G₀.E.card : ℝ) / (k : ℝ)) ∧
      Sj.W_init.biUnion (inducedEdges (S₀ j).RF.F) = (S₀ j).RF.F.E ∧
      (∀ W₁ ∈ Sj.W_init, ∀ W₂ ∈ Sj.W_init, W₁ ≠ W₂ →
        Disjoint (inducedEdges (S₀ j).RF.F W₁) (inducedEdges (S₀ j).RF.F W₂)) ∧
      boundary Sj.W_init ⊆ Sj.R ∧
      ∀ Wp ∈ Sj.W_init, PathConvex Sj.T₀ Wp ∧ Wp ⊆ G.V ∧
        (pieceBoundary Sj.W_init Wp).card ≤ 1 ∧ (G.vol (Wp \ Sj.R) : ℝ) ≤ K₀ * (k : ℝ) * L ^ 2 := by
    intro j hj
    obtain ⟨T_raw, r₀, C_reps, π, W_T, thresh, hp, hS₀⟩ := hinit j hj
    have hsp := (lemma_5_4_with_explicit C_lsst α K_σ G₀ hG₀ hV₀ ℓ₀ (v j) hℓ₀
      (hv_pos j (Nat.le_of_lt hj)) (k : ℝ) hk_real T_raw r₀ C_reps π W_T thresh hp Us hUs ℓ hℓ
      (fun e he₀ heG hn => hℓ_orig e he₀ heG (by rwa [← hins_eq j hj, show S j = applyLSFBatches (S₀ j) Us from rfl, hS₀]))).2
    simpa only [← hS₀, S, K₀, lemma54K0] using hsp
  refine ⟨?_, ?_⟩
  · intro j hj
    obtain ⟨hG_eq, hFE_sub, hG_sub, hT_sub, hins_w, hsurv_w, hcomp₀, hcomp_gr,
      hholds, _, hW_card, hcov, hdisj, hb_W, hW_props⟩ := h54_j j hj
    have hC0 : 0 ≤ (G₀.E.card : ℝ) / (k : ℝ) := div_nonneg (Nat.cast_nonneg _) hk_pos.le
    have hqL2 : 0 ≤ (q : ℝ) * L ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hkL6 : 0 ≤ (k : ℝ) * L ^ 6 := mul_nonneg hk_pos.le (pow_nonneg hL_pos.le 6)
    have hkL2 : 0 ≤ (k : ℝ) * L ^ 2 := mul_nonneg hk_pos.le (sq_nonneg _)
    have hcomp_if : (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then (1 : ℝ)
        else ((components G₀).card : ℝ) * K₀ * L ^ 2) ≤
        (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
        else ((components G₀).card : ℝ) * K * L ^ 2) := by
      split_ifs
      · exact le_rfl
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hK₀_le_K (Nat.cast_nonneg _)) (sq_nonneg _)
    refine ⟨hG_eq, hins_eq j hj, hFE_sub, hG_sub, hT_sub, hins_w, hsurv_w,
      hcomp₀.trans (add_le_add hcomp_if (mul_le_mul_of_nonneg_right hK₀_le_K hC0)),
      hcomp_gr.trans (add_le_add le_rfl (by nlinarith [mul_le_mul_of_nonneg_right hK₀_le_K hqL2])),
      ⟨hholds.1, hholds.2.1, hholds.2.2.1, fun e he =>
        ⟨(hholds.2.2.2 e he).1, (hholds.2.2.2 e he).2.trans (by nlinarith [mul_le_mul_of_nonneg_right hK₀_le_K hkL6])⟩⟩,
      hW_card.trans (add_le_add (add_le_add le_rfl hcomp_if) (mul_le_mul_of_nonneg_right hK₀_le_K hC0)),
      hcov, hdisj, hb_W, fun Wp hWp =>
        ⟨(hW_props Wp hWp).1, (hW_props Wp hWp).2.1, (hW_props Wp hWp).2.2.1,
          (hW_props Wp hWp).2.2.2.trans (by nlinarith [mul_le_mul_of_nonneg_right hK₀_le_K hkL2])⟩⟩
  · -- Average stretch bound
    have hsafe_pos : ∀ e ∈ G₀.E, 0 < safeLen G₀ ℓ₀ e := fun e he => by
      rw [safeLen_eq_of_mem ℓ₀ he]; exact hℓ₀ e he
    have hw₀_bd : ∀ j < k, ∀ e ∈ G₀.E, 1 ≤ (S₀ j).wstr e ∧ (S₀ j).wstr e ≤ U := by
      intro j hj e he
      obtain ⟨T_raw, r₀, C_reps, π, W_T, thresh, hp, hS₀⟩ := hinit j hj
      have hsp0 := (lemma_5_4_with_explicit C_lsst α K_σ G₀ hG₀ hV₀ ℓ₀ (v j) hℓ₀
        (hv_pos j (Nat.le_of_lt hj)) (k : ℝ) hk_real T_raw r₀ C_reps π W_T thresh hp [] trivial
        (safeLen G₀ ℓ₀) hsafe_pos (fun f hf _ _ => safeLen_eq_of_mem ℓ₀ hf)).2
      have hholds0 := hsp0.2.2.2.2.2.2.2.2.1
      rw [← hS₀] at hholds0
      have hstr := hholds0.2.2.2 e he
      exact ⟨(one_le_stretch_safeLen' hℓ₀ he).trans hstr.1, hstr.2⟩
    have hw₀_sum : ∀ j < k, ∑ e ∈ G₀.E, v j e * (S₀ j).wstr e ≤ W * G₀.norm1 (v j) := by
      intro j hj
      have hbd := (h54_j j hj).2.2.2.2.2.2.2.2.2.1
      linarith [show K₀ * G₀.norm1 (v j) * L ^ 4 = W * G₀.norm1 (v j) by ring]
    have hWU : (k : ℝ) * (2 * W / ρ) ≤ 1 := by
      have hL2_ge : (1 / 4 : ℝ) ≤ L ^ 2 := by nlinarith
      have h1 : (k : ℝ) * (2 * W) ≤ (2 / 10) * (1 / L ^ 2) * (10 * U) := by
        have hEq : (2 / 10 : ℝ) * (1 / L ^ 2) * (10 * (K₀ * (k : ℝ) * L ^ 6)) = 2 * (K₀ * L ^ 4) * (k : ℝ) := by
          field_simp [ne_of_gt hL_pos]
        dsimp only [W, U]; linarith
      have h2 : (2 / 10 : ℝ) * (1 / L ^ 2) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]; nlinarith
      have h3 : (k : ℝ) * (2 * W) ≤ 1 * ρ := by
        calc (k : ℝ) * (2 * W)
            ≤ (2 / 10) * (1 / L ^ 2) * (10 * U) := h1
          _ ≤ 1 * (10 * U) := mul_le_mul_of_nonneg_right h2 (by linarith)
          _ ≤ 1 * ρ := by linarith
      rw [mul_div_assoc', div_le_one hρ_pos]; linarith
    have hW_nn : 0 ≤ W := mul_nonneg hK₀_pos.le (pow_nonneg hL_pos.le 4)
    obtain ⟨hnorm1_le, hv_lb, _⟩ :=
      approx_mwu_weight_bounds hk hW_nn hU_pos hρ_ge hδ0 hδ_le hWU hv0 hv_pos hw₀_bd hw₀_sum hv_step
    have hnorm1_k : G₀.norm1 (v k) = ∑ f ∈ G₀.E, v k f :=
      Finset.sum_congr rfl fun f hf => abs_of_pos (hv_pos k le_rfl f hf)
    intro e heG
    by_cases hins : e ∈ batchesInserted Us
    · have havg_one : ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (S j).wstr e = 1 := by
        have hcongr : ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (S j).wstr e =
            ∑ _j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hj' := Finset.mem_range.mp hj
          have hse := (h54_j j hj').2.2.2.2.1 e (by rw [hins_eq j hj']; exact hins)
          rw [hse, mul_one]
        rw [hcongr, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp [ne_of_gt hk_pos]
      rw [havg_one]
      have hpow6 : (1 / 64 : ℝ) ≤ L ^ 6 := by
        have hsq : (1 / 2 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL.le 6
        linarith [show (1 / 2 : ℝ) ^ 6 = 1 / 64 by norm_num]
      have h1_le_128 : (1 : ℝ) ≤ 128 * (L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2)) := by
        nlinarith [mul_le_mul hpow6 hLm.le (by norm_num) (pow_nonneg hL_pos.le 6)]
      have hK128 : (128 : ℝ) ≤ K := by nlinarith
      have hnonneg : 0 ≤ L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) :=
        mul_nonneg (pow_nonneg hL_pos.le 6) hLm_pos.le
      calc (1 : ℝ)
          ≤ 128 * (L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2)) := h1_le_128
        _ ≤ K * (L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2)) := mul_le_mul_of_nonneg_right hK128 hnonneg
        _ = K * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by ring
    · have heG₀ : e ∈ G₀.E := batches_E_surv_orig' G₀ Us e heG hins
      have hcard_pos : (0 : ℝ) < (G₀.E.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨e, heG₀⟩
      have hle_norm : v k e ≤ G₀.norm1 (v k) := by
        rw [hnorm1_k]; exact Finset.single_le_sum (fun f hf => (hv_pos k le_rfl f hf).le) heG₀
      have hexp_le : Real.exp (-(2 * (k : ℝ) * δ) + (∑ j ∈ Finset.range k, (S₀ j).wstr e) / ρ) ≤
          Real.exp ((k : ℝ) * (δ + 2 * W / ρ) + Real.log (G₀.E.card : ℝ)) := by
        conv_rhs => rw [Real.exp_add, Real.exp_log hcard_pos]
        exact (hv_lb k le_rfl e heG₀).trans (hle_norm.trans (hnorm1_le k le_rfl))
      have hlog_le : (∑ j ∈ Finset.range k, (S₀ j).wstr e) / ρ ≤
          3 * (k : ℝ) * δ + (k : ℝ) * (2 * W / ρ) + Real.log (G₀.E.card : ℝ) := by
        linarith [Real.exp_le_exp.mp hexp_le]
      have havg_orig : ((1 : ℝ) / (k : ℝ)) * ∑ j ∈ Finset.range k, (S₀ j).wstr e ≤
          2 * W + 3 * δ * ρ + (ρ / (k : ℝ)) * Real.log (G₀.E.card : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hlog_le (div_nonneg hρ_pos.le hk_pos.le)
        calc ((1 : ℝ) / (k : ℝ)) * ∑ j ∈ Finset.range k, (S₀ j).wstr e
            = (ρ / (k : ℝ)) * ((∑ j ∈ Finset.range k, (S₀ j).wstr e) / ρ) := by
                field_simp [ne_of_gt hk_pos, ne_of_gt hρ_pos]
          _ ≤ (ρ / (k : ℝ)) * (3 * (k : ℝ) * δ + (k : ℝ) * (2 * W / ρ) + Real.log (G₀.E.card : ℝ)) := hmul
          _ = 2 * W + 3 * δ * ρ + (ρ / (k : ℝ)) * Real.log (G₀.E.card : ℝ) := by
                field_simp [ne_of_gt hk_pos, ne_of_gt hρ_pos]; ring
      have hL2_ge : (1 : ℝ) ≤ 4 * L ^ 2 := by nlinarith
      have hLm_ge : (1 : ℝ) ≤ 2 * Real.log ((G₀.E.card : ℝ) + 2) := by linarith
      have hlog_m : Real.log (G₀.E.card : ℝ) ≤ Real.log ((G₀.E.card : ℝ) + 2) :=
        Real.log_le_log hcard_pos (by linarith)
      have h2W_le : 2 * W ≤ 16 * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by
        calc 2 * W
            = 2 * K₀ * L ^ 4 * 1 * 1 := by ring
          _ ≤ 2 * K₀ * L ^ 4 * (4 * L ^ 2) * (2 * Real.log ((G₀.E.card : ℝ) + 2)) := by
              have h4nn : 0 ≤ 2 * K₀ * L ^ 4 := mul_nonneg (by linarith) (pow_nonneg hL_pos.le 4)
              exact mul_le_mul (mul_le_mul_of_nonneg_left hL2_ge h4nn) hLm_ge zero_le_one
                (mul_nonneg h4nn (by positivity))
          _ = 16 * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by ring
      have hρk_le : ρ / (k : ℝ) ≤ C_ρ * K₀ * L ^ 6 := by
        rw [div_le_iff₀ hk_pos]
        linarith [show C_ρ * K₀ * L ^ 6 * (k : ℝ) = C_ρ * U by dsimp [U]; ring]
      have h3δρ_le : 3 * δ * ρ ≤ 2 * C_ρ * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by
        have h1 : 3 * δ * ρ ≤ 3 * (1 / (4 * (k : ℝ))) * ρ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ_le (by norm_num)) hρ_pos.le
        have h2 : 3 * (1 / (4 * (k : ℝ))) * ρ = (3 / 4) * (ρ / (k : ℝ)) := by ring
        have h3 : (3 / 4 : ℝ) * (ρ / (k : ℝ)) ≤ C_ρ * K₀ * L ^ 6 := by nlinarith [hρk_le, hρ_pos]
        have h4 : C_ρ * K₀ * L ^ 6 ≤ 2 * C_ρ * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by
          have hnn : 0 ≤ C_ρ * K₀ * L ^ 6 := mul_nonneg (mul_nonneg (by linarith) hK₀_pos.le) (pow_nonneg hL_pos.le 6)
          calc C_ρ * K₀ * L ^ 6 = (C_ρ * K₀ * L ^ 6) * 1 := (mul_one _).symm
            _ ≤ (C_ρ * K₀ * L ^ 6) * (2 * Real.log ((G₀.E.card : ℝ) + 2)) := mul_le_mul_of_nonneg_left hLm_ge hnn
            _ = 2 * C_ρ * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by ring
        linarith
      have hρ_term : (ρ / (k : ℝ)) * Real.log (G₀.E.card : ℝ) ≤
          C_ρ * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by
        have h1 : (ρ / (k : ℝ)) * Real.log (G₀.E.card : ℝ) ≤ (ρ / (k : ℝ)) * Real.log ((G₀.E.card : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hlog_m (div_nonneg hρ_pos.le hk_pos.le)
        exact h1.trans (mul_le_mul_of_nonneg_right hρk_le hLm_pos.le)
      have havg_eq : ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (S j).wstr e =
          ((1 : ℝ) / (k : ℝ)) * ∑ j ∈ Finset.range k, (S₀ j).wstr e := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' := Finset.mem_range.mp hj
        have hsurv := (h54_j j hj').2.2.2.2.2.1 e heG (by rw [hins_eq j hj']; exact hins)
        rw [hsurv]
      rw [havg_eq]
      have hnonneg : 0 ≤ L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) :=
        mul_nonneg (pow_nonneg hL_pos.le 6) hLm_pos.le
      have hK_ge : (16 + 3 * C_ρ) * K₀ ≤ K := by
        dsimp only [K]; clear * - hCρ hK₀_pos; nlinarith
      calc ((1 : ℝ) / (k : ℝ)) * ∑ j ∈ Finset.range k, (S₀ j).wstr e
          ≤ 2 * W + 3 * δ * ρ + (ρ / (k : ℝ)) * Real.log (G₀.E.card : ℝ) := havg_orig
        _ ≤ 16 * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) +
            2 * C_ρ * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) +
            C_ρ * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := add_le_add (add_le_add h2W_le h3δρ_le) hρ_term
        _ = (16 + 3 * C_ρ) * K₀ * (L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2)) := by ring
        _ ≤ K * (L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_right hK_ge hnonneg
        _ = K * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by ring

end MinCostFlow.LSF.Program
