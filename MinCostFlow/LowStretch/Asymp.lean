module

public import MinCostFlow.LowStretch.Bound

/-!
# The factor is `O(log n log log n)`

Write `ℓ = log(n + 2)`. Then `ℓ ≥ log 3 > 40/39`, so `log ℓ ≥ 1/40`. The number of buckets is
`L ≤ 162 log ℓ`, and each of `Λ`, `G0` and `λ0 = 2^L` is at most a constant times `ℓ`. So the
factor of the bound is at most `K0 · ℓ · log ℓ` (`Afac_le`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open MinCostFlow.Cited Real

theorem log_two_gt : (0.69 : ℝ) < log 2 := by
  have := Real.log_two_gt_d9; linarith

theorem log_three_gt : (40 / 39 : ℝ) < log 3 := by
  have h1 : log 3 = log 2 + log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 : 1 - (3 / 2 : ℝ)⁻¹ ≤ log (3 / 2) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have := Real.log_two_gt_d9
  rw [h1]; norm_num at h2; linarith

/-- `ℓ = log(n + 2)`. -/
noncomputable def ell (n : ℕ) : ℝ := log ((n : ℝ) + 2)

theorem ell_ge {n : ℕ} (hn : 1 ≤ n) : 40 / 39 < ell n := by
  unfold ell
  have : log 3 ≤ log ((n : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                                      linarith)
  linarith [log_three_gt]

theorem log_ell_ge {n : ℕ} (hn : 1 ≤ n) : 1 / 40 ≤ log (ell n) := by
  have h := ell_ge hn
  have h2 := Real.one_sub_inv_le_log_of_pos (show 0 < ell n by linarith)
  have : (ell n)⁻¹ ≤ 39 / 40 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  linarith

/-- `⌊log₂ x⌋ ≤ log x / log 2`. -/
theorem natLog_le {x : ℕ} (hx : 1 ≤ x) : (Nat.log 2 x : ℝ) ≤ log x / log 2 := by
  rw [le_div_iff₀ (by positivity)]
  have h : ((2 ^ Nat.log 2 x : ℕ) : ℝ) ≤ x := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have := Real.log_le_log (by positivity) h
  rw [Nat.cast_pow, Real.log_pow] at this
  push_cast at this
  linarith

theorem inv_log_two_le : 1 / log 2 ≤ 1.45 := by
  rw [div_le_iff₀ (by positivity)]; linarith [log_two_gt]

theorem pa_le (n : ℕ) : (pa n : ℝ) ≤ 1.45 * ell n + 1 := by
  unfold pa ell
  have h := natLog_le (x := n + 2) (by omega)
  push_cast at h ⊢
  have h2 : log ((n : ℝ) + 2) / log 2 ≤ 1.45 * log ((n : ℝ) + 2) := by
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right inv_log_two_le
      (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith))
  linarith

theorem twoa_le {n : ℕ} (hn : 1 ≤ n) : ((2 * pa n + 2 : ℕ) : ℝ) ≤ 7 * ell n := by
  have := pa_le n
  have := ell_ge hn
  push_cast
  linarith

theorem pL_le {n : ℕ} (hn : 1 ≤ n) : (pL n : ℝ) ≤ 162 * log (ell n) := by
  unfold pL
  have h := natLog_le (x := 2 * pa n + 2) (by omega)
  have h7 := twoa_le hn
  have hℓ := ell_ge hn
  have hlog : log ((2 * pa n + 2 : ℕ) : ℝ) ≤ log 7 + log (ell n) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by positivity) h7
  have hlog7 : log 7 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hl1 := log_ell_ge hn
  have hnn : 0 ≤ log 7 + log (ell n) := by
    have : 0 ≤ log 7 := Real.log_nonneg (by norm_num)
    linarith
  have h2 : log ((2 * pa n + 2 : ℕ) : ℝ) / log 2 ≤ 1.45 * (log 7 + log (ell n)) := by
    rw [div_eq_mul_one_div, mul_comm]
    calc 1 / log 2 * log ((2 * pa n + 2 : ℕ) : ℝ) ≤ 1 / log 2 * (log 7 + log (ell n)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ 1.45 * (log 7 + log (ell n)) := mul_le_mul_of_nonneg_right inv_log_two_le hnn
  push_cast at h h2 ⊢
  linarith

theorem lam0_le {n : ℕ} (hn : 1 ≤ n) : ((2 ^ pL n : ℕ) : ℝ) ≤ 14 * ell n := by
  have h : 2 ^ pL n ≤ 2 * (2 * pa n + 2) := by
    unfold pL
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (by omega))
  have h7 := twoa_le hn
  have : ((2 ^ pL n : ℕ) : ℝ) ≤ 2 * ((2 * pa n + 2 : ℕ) : ℝ) := by exact_mod_cast h
  linarith

theorem pB_le {n : ℕ} (hn : 1 ≤ n) : (pB n : ℝ) ≤ 952 * ell n ^ 2 := by
  have hL : pL n ≤ 2 ^ pL n := (Nat.lt_two_pow_self).le
  have h1 := lam0_le hn
  have hℓ := ell_ge hn
  have hLr : (pL n : ℝ) ≤ ((2 ^ pL n : ℕ) : ℝ) := by exact_mod_cast hL
  unfold pB
  push_cast
  have h0 : (0 : ℝ) ≤ pL n := Nat.cast_nonneg _
  have h2 : ((2 : ℝ) ^ pL n) + 3 ≤ 17 * ell n := by push_cast at h1; linarith
  have h3 : (pL n : ℝ) ≤ 14 * ell n := by linarith
  calc 4 * (pL n : ℝ) * ((2 : ℝ) ^ pL n + 3) ≤ 4 * (14 * ell n) * (17 * ell n) := by
        apply mul_le_mul (by linarith) h2 (by positivity) (by linarith)
    _ = 952 * ell n ^ 2 := by ring

theorem ell_le {n : ℕ} : ell n ≤ (n : ℝ) + 2 := by
  unfold ell
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n + 2 by positivity)
  linarith

variable {G : WGraph}

theorem Lam_le (h : Allowed G) :
    Lam (pgOf G) (par G.n G.m) ≤ 5 * ell G.n := by
  have hn := h.conn.1
  have hκ : (0 : ℝ) < pκ G.n G.m := by unfold pκ; positivity
  have hm : G.m < G.n ^ 2 * pκ G.n G.m := by
    unfold pκ; exact Nat.lt_mul_div_succ _ (by positivity)
  have hV : Vmax (pgOf G) (par G.n G.m) / pκ G.n G.m ≤ ((G.n : ℝ) + 2) ^ 2 := by
    rw [Vmax_eq, div_le_iff₀ hκ]
    simp only [pgOf, toPG.n_eq, toPG.m_eq]
    have : (G.n + 1) * pκ G.n G.m + G.m ≤ (G.n + 2) ^ 2 * pκ G.n G.m := by
      have : (G.n + 1) * pκ G.n G.m + G.n ^ 2 * pκ G.n G.m ≤ (G.n + 2) ^ 2 * pκ G.n G.m := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by nlinarith)
      omega
    exact_mod_cast this
  have hpos : 0 < Vmax (pgOf G) (par G.n G.m) / pκ G.n G.m := by
    apply div_pos _ hκ
    rw [Vmax_eq]; positivity
  unfold Lam
  have h1 := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hV
  have h2 : logb 2 (((G.n : ℝ) + 2) ^ 2) ≤ 2.9 * ell G.n := by
    unfold logb ell
    rw [Real.log_pow]
    push_cast
    have : 0 ≤ log ((G.n : ℝ) + 2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) G.n; linarith)
    rw [div_le_iff₀ (by positivity)]
    nlinarith [log_two_gt]
  have hℓ := ell_ge hn
  show logb 2 (Vmax (pgOf G) (par G.n G.m) / ((par G.n G.m).κ : ℝ)) + 2 ≤ _
  have e : ((par G.n G.m).κ : ℝ) = pκ G.n G.m := rfl
  rw [e]
  linarith

theorem G0_le (h : Allowed G) : G0 (pgOf G) (par G.n G.m) ≤ 129 * ell G.n := by
  have hn := h.conn.1
  have hℓ := ell_ge hn
  have hB := pB_le hn
  have hB1 : (1 : ℝ) ≤ pB G.n := by exact_mod_cast pB_pos G.n
  have hn1 : (1 : ℝ) ≤ G.n := by exact_mod_cast hn
  unfold G0
  simp only [pgOf, toPG.n_eq, par]
  push_cast
  set ℓ := ell G.n
  have harg : (32 : ℝ) * pB G.n * (512 * pB G.n * G.n ^ 2) * G.n ^ 2 ≤
      2 ^ 34 * ((G.n : ℝ) + 2) ^ 8 := by
    have hl := ell_le (n := G.n)
    have e : (32 : ℝ) * pB G.n * (512 * pB G.n * G.n ^ 2) * G.n ^ 2 =
        16384 * (pB G.n : ℝ) ^ 2 * (G.n : ℝ) ^ 4 := by ring
    rw [e]
    have h1 : (pB G.n : ℝ) ^ 2 ≤ (952 * ℓ ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) hB 2
    have h2 : ℓ ^ 4 ≤ ((G.n : ℝ) + 2) ^ 4 := pow_le_pow_left₀ (by linarith) hl 4
    have h3 : (G.n : ℝ) ^ 4 ≤ ((G.n : ℝ) + 2) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    have h4 : (16384 : ℝ) * 952 ^ 2 ≤ 2 ^ 34 := by norm_num
    calc 16384 * (pB G.n : ℝ) ^ 2 * (G.n : ℝ) ^ 4 ≤ 16384 * (952 * ℓ ^ 2) ^ 2 * (G.n : ℝ) ^ 4 := by
          gcongr
      _ = 16384 * 952 ^ 2 * ℓ ^ 4 * (G.n : ℝ) ^ 4 := by ring
      _ ≤ 2 ^ 34 * ((G.n : ℝ) + 2) ^ 4 * ((G.n : ℝ) + 2) ^ 4 := by
          gcongr
      _ = 2 ^ 34 * ((G.n : ℝ) + 2) ^ 8 := by ring
  have hpos : (0 : ℝ) < 32 * pB G.n * (512 * pB G.n * G.n ^ 2) * G.n ^ 2 := by positivity
  have h1 := Real.logb_le_logb_of_le (b := 4 / 3) (by norm_num) hpos harg
  have h2 : logb (4 / 3) (2 ^ 34 * ((G.n : ℝ) + 2) ^ 8) ≤ 128 * ℓ := by
    unfold logb
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have hl43 : (1 / 4 : ℝ) ≤ log (4 / 3) := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
      norm_num at this ⊢; linarith
    have hl2 : log 2 ≤ 0.7 := by
      have := Real.log_two_lt_d9; linarith
    have e : log ((G.n : ℝ) + 2) = ℓ := rfl
    rw [e, div_le_iff₀ (by linarith)]
    push_cast
    nlinarith
  linarith

/-- **The factor is `O(log n log log n)`.** -/
theorem Afac_le (h : Allowed G) : Afac G ≤ 1146265800 * logLogFactor G.n := by
  have hn := h.conn.1
  have hℓ := ell_ge hn
  have hlℓ := log_ell_ge hn
  have hL := pL_le hn
  have hΛ := Lam_le h
  have hG := G0_le h
  have hlm := lam0_le hn
  have hΛ0 := Cl.Lam_ge (G := pgOf G) (P := par G.n G.m) (by simp [par, pκ])
  have hG00 := Cl.G0_ge (G := pgOf G) (P := par G.n G.m)
  have hlam0 : (0 : ℝ) ≤ ((2 ^ pL G.n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hin : 26 * Lam (pgOf G) (par G.n G.m) + 18 * G0 (pgOf G) (par G.n G.m) +
      12 * ((2 ^ pL G.n : ℕ) : ℝ) + 144 ≤ 2764 * ell G.n := by linarith
  have hin0 : 0 ≤ 26 * Lam (pgOf G) (par G.n G.m) + 18 * G0 (pgOf G) (par G.n G.m) +
      12 * ((2 ^ pL G.n : ℕ) : ℝ) + 144 := by linarith
  have hL0 : (0 : ℝ) ≤ pL G.n := Nat.cast_nonneg _
  have h1 : (pL G.n : ℝ) * (26 * Lam (pgOf G) (par G.n G.m) + 18 * G0 (pgOf G) (par G.n G.m) +
      12 * ((2 ^ pL G.n : ℕ) : ℝ) + 144) ≤ 162 * log (ell G.n) * (2764 * ell G.n) :=
    mul_le_mul hL hin hin0 (by linarith)
  have h2 : (5 : ℝ) ≤ 200 * (ell G.n * log (ell G.n)) := by nlinarith
  unfold Afac logLogFactor
  have e : log ((G.n : ℝ) + 2) = ell G.n := rfl
  rw [e]
  nlinarith

end MinCostFlow.LowStretch
