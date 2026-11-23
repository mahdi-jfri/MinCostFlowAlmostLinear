module

public import MinCostFlow.LowStretch.Transfer

/-!
# The potential of the first cluster

With volume weight `1` for every pair, the potential of a cluster is at most
`m (5 + 2560 L (26 Λ + 18 G0 + 12 λ0 + 144))` (`pot_le`). Each part of the potential is bounded
separately: the weights of the pairs by `m`, the entropy by `Vmax Λ`, the levels by `G0 m`, and
the sizes by `6 m`, using `n κ ≤ 3 m` and `Vmax ≤ 6 m` when `1 ≤ m` and `n ≤ m + 1`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open MinCostFlow.Cited Real

variable {G : WGraph}

/-- The factor of the bound. -/
noncomputable def Afac (G : WGraph) : ℝ :=
  5 + 2560 * (pL G.n : ℝ) * (26 * Lam (pgOf G) (par G.n G.m) + 18 * G0 (pgOf G) (par G.n G.m) +
    12 * (2 ^ pL G.n : ℕ) + 144)

theorem nκ_le (hm : 1 ≤ G.m) (hn : 1 ≤ G.n) (hnm : G.n ≤ G.m + 1) :
    G.n * pκ G.n G.m ≤ 3 * G.m := by
  unfold pκ
  have h1 : G.n * (G.m / G.n ^ 2) ≤ G.m := by
    calc G.n * (G.m / G.n ^ 2) ≤ G.n ^ 2 * (G.m / G.n ^ 2) :=
          Nat.mul_le_mul_right _ (by nlinarith)
      _ ≤ G.m := Nat.mul_div_le _ _
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem κ_le (hm : 1 ≤ G.m) : pκ G.n G.m ≤ 2 * G.m := by
  unfold pκ
  have := Nat.div_le_self G.m (G.n ^ 2)
  omega

theorem Vmax_le (hm : 1 ≤ G.m) (hn : 1 ≤ G.n) (hnm : G.n ≤ G.m + 1) :
    Vmax (pgOf G) (par G.n G.m) ≤ 6 * G.m := by
  rw [Vmax_eq]
  simp only [pgOf, toPG.n_eq, toPG.m_eq]
  have h1 := nκ_le hm hn hnm
  have h2 := κ_le (G := G) hm
  have : (G.n + 1) * pκ G.n G.m + G.m ≤ 6 * G.m := by rw [Nat.add_mul, one_mul]; omega
  exact_mod_cast this

/-- **The potential is at most `m · Afac`.** -/
theorem pot_le (h : Allowed G) {c : Cl} (hc : c.Inv (pgOf G) (par G.n G.m)) (hm : 1 ≤ G.m)
    (hnm : G.n ≤ G.m + 1) : c.Pot (pgOf G) (par G.n G.m) ≤ G.m * Afac G := by
  classical
  set P := par G.n G.m with hPdef
  set H := pgOf G with hH
  have hP := h.fit
  have hn := h.conn.1
  have hmH : H.m = G.m := by simp [hH, pgOf]
  have hκ1 : (1 : ℝ) ≤ P.κ := by exact_mod_cast hP.κ
  have hκr : (0 : ℝ) < P.κ := by linarith
  have hΛ := Cl.Lam_ge (G := H) (P := P) hP.κ
  have hG0 := Cl.G0_ge (G := H) (P := P)
  have hmr : (1 : ℝ) ≤ G.m := by exact_mod_cast hm
  -- the weights of the pairs
  have h1 : ∑ p ∈ H.ins c.X, (P.cw p : ℝ) ≤ G.m := by
    simp only [hPdef, par, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (H.ins c.X).card ≤ G.m := by
      have := Finset.card_le_card (show H.ins c.X ⊆ Finset.range H.m from
        fun p hp => Finset.mem_range.mpr (PG.mem_ins.mp hp).1)
      rwa [Finset.card_range, hmH] at this
    exact_mod_cast this
  -- the entropy
  have hVm := Vmax_le hm hn hnm
  rw [← hH, ← hPdef] at hVm
  have h2 : Fe P.κ (c.V H P) ≤ 6 * G.m * Lam H P := by
    have hle : c.V H P ≤ Vmax H P := Cl.V_le_Vmax
    have := Fe_mono hκr Cl.V_ge hle
    have hF : Fe P.κ (Vmax H P) ≤ Vmax H P * Lam H P := by
      unfold Fe Lam
      have : 0 ≤ Vmax H P := le_trans hκr.le (le_trans Cl.V_ge hle)
      nlinarith
    have : Vmax H P * Lam H P ≤ 6 * G.m * Lam H P :=
      mul_le_mul_of_nonneg_right hVm (by linarith)
    linarith
  -- the light-joined pairs
  have h3 : Cl.inact H P c ≤ G.m := by
    unfold Cl.inact
    simp only [hPdef, par, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (Cl.lset H c).card ≤ G.m := by
      have := Finset.card_le_card (show Cl.lset H c ⊆ Finset.range H.m from
        Finset.filter_subset _ _)
      rwa [Finset.card_range, hmH] at this
    exact_mod_cast this
  -- the levels
  have h4 : c.gsum H P ≤ G0 H P * G.m := by
    unfold Cl.gsum
    simp only [hPdef, par, Nat.cast_one, one_mul]
    calc ∑ p ∈ c.act H (par G.n G.m), c.gl H (par G.n G.m) p
        ≤ ∑ p ∈ c.act H (par G.n G.m), G0 H (par G.n G.m) :=
          Finset.sum_le_sum fun p hp => Cl.gl_le hP.ok hc hp
      _ = G0 H P * (c.act H P).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ G0 H P * G.m := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have := Finset.card_le_card (show c.act H P ⊆ Finset.range H.m from
            Finset.filter_subset _ _)
          rw [Finset.card_range, hmH] at this
          exact_mod_cast this
  -- the sizes
  have h5 : P.κ * (2 * (c.X.card : ℝ) - 1) ≤ 6 * G.m := by
    have hcard : c.X.card ≤ G.n := by
      have := Finset.card_le_card hc.sub; rwa [Finset.card_range] at this
    have := nκ_le hm hn hnm
    have h' : (P.κ : ℝ) * c.X.card ≤ 3 * G.m := by
      have : pκ G.n G.m * c.X.card ≤ 3 * G.m := by
        calc pκ G.n G.m * c.X.card ≤ pκ G.n G.m * G.n := Nat.mul_le_mul_left _ hcard
          _ = G.n * pκ G.n G.m := mul_comm _ _
          _ ≤ 3 * G.m := this
      have e : P.κ = pκ G.n G.m := rfl
      rw [e]; exact_mod_cast this
    nlinarith
  have hK1 : (0 : ℝ) ≤ 2 * (Cl.lam P 0 : ℕ) + 24 + 2 * Lam H P := by
    have := Nat.cast_nonneg (α := ℝ) (Cl.lam P 0)
    linarith
  have hlam : (Cl.lam P 0 : ℕ) = 2 ^ pL G.n := lam0_eq _ _
  unfold Cl.Pot
  rw [hlam] at hK1 ⊢
  have hL : (0 : ℝ) ≤ 2560 * P.L := by
    have := Nat.cast_nonneg (α := ℝ) P.L
    linarith
  have hin : 2 * Fe P.κ (c.V H P) + (2 * Lam H P + 9 * G0 H P) * Cl.inact H P c +
      9 * c.gsum H P + (2 * ((2 ^ pL G.n : ℕ) : ℝ) + 24 + 2 * Lam H P) * P.κ *
        (2 * (c.X.card : ℝ) - 1) ≤
      G.m * (26 * Lam H P + 18 * G0 H P + 12 * ((2 ^ pL G.n : ℕ) : ℝ) + 144) := by
    have e1 : (2 * Lam H P + 9 * G0 H P) * Cl.inact H P c ≤ (2 * Lam H P + 9 * G0 H P) * G.m :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    have e2 : (2 * ((2 ^ pL G.n : ℕ) : ℝ) + 24 + 2 * Lam H P) * P.κ * (2 * (c.X.card : ℝ) - 1) ≤
        (2 * ((2 ^ pL G.n : ℕ) : ℝ) + 24 + 2 * Lam H P) * (6 * G.m) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h5 hK1
    linarith
  have := mul_le_mul_of_nonneg_left hin hL
  show _ ≤ (G.m : ℝ) * (5 + 2560 * (pL G.n : ℝ) * (26 * Lam H P + 18 * G0 H P +
    12 * ((2 ^ pL G.n : ℕ) : ℝ) + 144))
  have e : (P.L : ℝ) = pL G.n := rfl
  rw [e] at this ⊢
  linarith

end MinCostFlow.LowStretch
