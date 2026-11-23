module

public import MinCostFlow.LowStretch.Stretch4

/-!
# The stretch of a run

We bound the weighted stretch `∑ cw · d_T / ω` of the pairs inside a cluster by a potential
(`Run.stretch`). The potential has five parts:
* `5 ∑ cw` over the pairs inside `X`, which pays the heavy cut pairs;
* `2 F(V)`, the entropy of the volume, which pays region growing;
* `(2 Λ + 9 G0)` times the weight of the light-joined pairs, which pays the new active pairs;
* `9 ∑ cw · g` over the active pairs, which pays the active pairs at each of their levels;
* `K1 κ (2 |X| - 1)`, which pays the petals of small volume and the extra `κ` of each part.
All but the first are multiplied by `C = 2560 L`. At a step, the potential of the cluster is at
least the potentials of its children plus the stretch of its cut pairs.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open Real

variable {G : PG} {P : Par}

namespace Cl

variable (G P) in
/-- The potential of a cluster. -/
noncomputable def Pot (c : Cl) : ℝ :=
  5 * ∑ p ∈ G.ins c.X, (P.cw p : ℝ) +
    2560 * P.L * (2 * Fe P.κ (c.V G P) + (2 * Lam G P + 9 * G0 G P) * inact G P c +
      9 * c.gsum G P + (2 * (lam P 0 : ℕ) + 24 + 2 * Lam G P) * P.κ * (2 * (c.X.card : ℝ) - 1))

theorem Lam_ge (hκ : 1 ≤ P.κ) : 2 ≤ Lam G P := by
  unfold Lam
  have hκr : (0 : ℝ) < P.κ := by exact_mod_cast hκ
  have : (P.κ : ℝ) ≤ Vmax G P := by
    unfold Vmax
    have : (0 : ℝ) ≤ ∑ p ∈ Finset.range G.m, (P.cw p : ℝ) := Finset.sum_nonneg fun _ _ => by
      positivity
    have : (P.κ : ℝ) ≤ (G.n + 1) * P.κ := by nlinarith [(Nat.cast_nonneg G.n : (0 : ℝ) ≤ G.n)]
    linarith
  have := logb_nonneg_of_le hκr this
  linarith

theorem G0_ge : 1 ≤ G0 G P := by
  unfold G0
  have e : (32 * P.B * P.Q * G.n ^ 2 : ℝ) = ((32 * P.B * P.Q * G.n ^ 2 : ℕ) : ℝ) := by push_cast; ring
  rw [e]
  rcases Nat.eq_zero_or_pos (32 * P.B * P.Q * G.n ^ 2) with h | h
  · rw [h]; simp
  · have : (1 : ℝ) ≤ ((32 * P.B * P.Q * G.n ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
    have := logb_nonneg (show (1 : ℝ) < 4 / 3 by norm_num) this
    linarith

theorem inact_nonneg (c : Cl) : 0 ≤ inact G P c := Finset.sum_nonneg fun _ _ => by positivity

theorem gsum_nonneg (hGo : G.Ok) (c : Cl) : 0 ≤ c.gsum G P :=
  Finset.sum_nonneg fun p hp => mul_nonneg (by positivity) (by linarith [gl_ge_one hGo hp])

theorem Pot_nonneg (hGo : G.Ok) (hκ : 1 ≤ P.κ) {c : Cl} (hc : c.Inv G P) : 0 ≤ c.Pot G P := by
  unfold Pot
  have hκr : (0 : ℝ) < P.κ := by exact_mod_cast hκ
  have h1 : (0 : ℝ) ≤ ∑ p ∈ G.ins c.X, (P.cw p : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  have h2 := Fe_nonneg hκr (V_ge (c := c) (G := G) (P := P))
  have h3 := inact_nonneg (G := G) (P := P) c
  have h4 := gsum_nonneg (P := P) hGo c
  have h5 := Lam_ge (G := G) hκ
  have h6 := G0_ge (G := G) (P := P)
  have h7 : (1 : ℝ) ≤ c.X.card := by exact_mod_cast Finset.card_pos.mpr ⟨_, hc.good.conn.1⟩
  have h8 : 0 ≤ (2 * Lam G P + 9 * G0 G P) * inact G P c := mul_nonneg (by linarith) h3
  have h9 : 0 ≤ (2 * (lam P 0 : ℕ) + 24 + 2 * Lam G P) * P.κ * (2 * (c.X.card : ℝ) - 1) :=
    mul_nonneg (mul_nonneg (by positivity) hκr.le) (by linarith)
  have : (0 : ℝ) ≤ 2560 * P.L := by positivity
  have := mul_nonneg this (show 0 ≤ 2 * Fe P.κ (c.V G P) + (2 * Lam G P + 9 * G0 G P) *
    inact G P c + 9 * c.gsum G P + (2 * (lam P 0 : ℕ) + 24 + 2 * Lam G P) * P.κ *
      (2 * (c.X.card : ℝ) - 1) by linarith)
  linarith

variable {c : Cl} {D : Dec}

/-- The radius of a cluster with two or more vertices pays the region growing slack. -/
theorem Δ_ge_L (hc : c.Inv G P) (hX : 2 ≤ c.X.card) (hBL : 8 * P.L * (lam P 0 + 3) ≤ 2 * P.B) :
    8 * P.L * (lam P 0 + 3) ≤ c.Δ G := by
  have hbig : P.B * c.X.card * c.θ ≤ c.Δ G := hc.big.resolve_left (by omega)
  have : P.B * 2 * 1 ≤ P.B * c.X.card * c.θ := Nat.mul_le_mul (Nat.mul_le_mul_left _ hX) hc.one_le
  omega

/-- One step: the potential of a cluster is at least the potentials of its children, plus the
stretch bound `5 ∑ cw + 20 Δ ∑ cost` of its cut pairs. -/
theorem Pot_step (hGo : G.Ok) (hB : 1 ≤ P.B) (hκ : 1 ≤ P.κ)
    (hBL : 8 * P.L * (lam P 0 + 3) ≤ 2 * P.B) (hc : c.Inv G P) (hX : 2 ≤ c.X.card)
    (hD : c.DecOk G P D) {cs : ℕ → Cl} (hn : ∀ k < D.nch, Next G P (c.raw G D k) (cs k)) :
    ∑ k ∈ Finset.range D.nch, (cs k).Pot G P + 5 * ∑ p ∈ c.cut G D, (P.cw p : ℝ) +
      20 * c.Δ G * ∑ k ∈ Finset.range D.ps.length, c.cost G P (c.Z G D k) (D.pd k) ≤
      c.Pot G P := by
  classical
  have hκr : (0 : ℝ) < P.κ := by exact_mod_cast hκ
  have hXk : ∀ k < D.nch, (cs k).X = (c.raw G D k).X := fun k hk => (hn k hk).X_eq
  set ℓ : ℝ := (D.ps.length : ℝ) with hℓ
  have hℓ1 : (1 : ℝ) ≤ ℓ := by
    show (1 : ℝ) ≤ (D.ps.length : ℝ)
    exact_mod_cast len_pos hB hc hX hD
  have hℓn : ℓ ≤ G.n := by
    have h1 := len_le_card (G := G) (P := P) hD
    have h2 : c.X.card ≤ G.n := by
      have := Finset.card_le_card hc.sub; rwa [Finset.card_range] at this
    show (D.ps.length : ℝ) ≤ G.n
    exact_mod_cast h1.trans h2
  have hℓκ : 0 ≤ ℓ * P.κ := by positivity
  have hVm : c.V G P ≤ P.κ + ∑ p ∈ Finset.range G.m, (P.cw p : ℝ) := by
    have := V_add_new_le (G := G) (P := P) (c := c) c
    simp only [Finset.sdiff_self, Finset.sum_empty, add_zero] at this
    exact this
  have hκn : ℓ * P.κ ≤ G.n * P.κ := mul_le_mul_of_nonneg_right hℓn hκr.le
  have hSm : c.V G P + ℓ * P.κ ≤ Vmax G P := by unfold Vmax; linarith
  -- region growing
  have hcost := dcost_sum_le hGo hc.good.conn hD hκ (Δ_ge_L hc hX hBL)
  rw [← hℓ] at hcost
  -- the entropy of the sum `S`
  have hFS : Fe P.κ (c.V G P + ℓ * P.κ) ≤ Fe P.κ (c.V G P) + ℓ * P.κ * Lam G P := by
    have h1 := Fe_sub_le hκr V_ge (show c.V G P ≤ c.V G P + ℓ * P.κ by
      linarith)
    have h2 : logb 2 ((c.V G P + ℓ * P.κ) / P.κ) ≤ logb 2 (Vmax G P / P.κ) := by
      apply logb_le_logb_of_le (by norm_num)
        (div_pos (by linarith [V_ge (c := c) (G := G) (P := P), hℓκ]) hκr)
      exact div_le_div_of_nonneg_right hSm hκr.le
    have h3 : ℓ * P.κ * (logb 2 ((c.V G P + ℓ * P.κ) / P.κ) + 2) ≤ ℓ * P.κ * Lam G P := by
      unfold Lam
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : c.V G P + ℓ * P.κ - c.V G P = ℓ * P.κ := by ring
    rw [e] at h1
    linarith
  -- the entropy of the children
  have hFc : ∑ k ∈ Finset.range D.nch, Fe P.κ ((cs k).V G P) ≤
      ∑ k ∈ Finset.range D.nch, Fe P.κ (c.part G P D k) + Lam G P *
        ∑ k ∈ Finset.range D.nch, ∑ p ∈ (cs k).act G P \ c.act G P, (P.cw p : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    refine Fe_child hκ (hXk k hk') ?_
    have hpS : c.part G P D k ≤ c.V G P + ℓ * P.κ := by
      have hsum := sum_part_le (P := P) (D := D) hGo hc.good.conn
      have := Finset.single_le_sum (f := c.part G P D)
        (fun j _ => by linarith [part_ge (c := c) (G := G) (P := P) (D := D) j])
        (Finset.mem_range.mpr hk')
      linarith
    have := V_add_new_le (G := G) (P := P) (c := c) (cs k)
    unfold Vmax
    linarith
  -- new active pairs and light-joined pairs
  have hin := inact_sum hGo hB hc hX hD hn
  rw [Finset.sum_add_distrib] at hin
  have hin' := mul_le_mul_of_nonneg_left hin
    (show 0 ≤ 2 * Lam G P + 9 * G0 G P by linarith [Lam_ge (G := G) hκ, G0_ge (G := G) (P := P)])
  -- levels
  have hg := gsum_step hGo hB hc hX hD hn
  -- the pairs inside
  have hins := sum_ins (G := G) (c := c) (D := D) fun p => (P.cw p : ℝ)
  have hins' : ∑ k ∈ Finset.range D.nch, ∑ p ∈ G.ins (cs k).X, (P.cw p : ℝ) =
      ∑ k ∈ Finset.range D.nch, ∑ p ∈ G.ins (c.raw G D k).X, (P.cw p : ℝ) :=
    Finset.sum_congr rfl fun k hk => by rw [hXk k (Finset.mem_range.mp hk)]
  -- the sizes
  have hcard : ∑ k ∈ Finset.range D.nch, (2 * ((cs k).X.card : ℝ) - 1) =
      2 * (c.X.card : ℝ) - (ℓ + 1) := by
    have h1 := sum_card_raw (G := G) (c := c) (D := D)
    have h2 : ∑ k ∈ Finset.range D.nch, ((cs k).X.card : ℝ) = c.X.card := by
      rw [← h1, Nat.cast_sum]
      exact Finset.sum_congr rfl fun k hk => by rw [hXk k (Finset.mem_range.mp hk)]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h2, Finset.sum_const, Finset.card_range]
    unfold Dec.nch
    simp [hℓ]
  have hsumPot : ∑ k ∈ Finset.range D.nch, (cs k).Pot G P =
      5 * ∑ k ∈ Finset.range D.nch, ∑ p ∈ G.ins (cs k).X, (P.cw p : ℝ) +
        2560 * P.L * (2 * ∑ k ∈ Finset.range D.nch, Fe P.κ ((cs k).V G P) +
          (2 * Lam G P + 9 * G0 G P) * ∑ k ∈ Finset.range D.nch, inact G P (cs k) +
          9 * ∑ k ∈ Finset.range D.nch, (cs k).gsum G P +
          (2 * (lam P 0 : ℕ) + 24 + 2 * Lam G P) * P.κ *
            ∑ k ∈ Finset.range D.nch, (2 * ((cs k).X.card : ℝ) - 1)) := by
    unfold Pot
    simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  rw [hsumPot, hcard, hins']
  have hVdef : c.V G P = P.κ + ∑ p ∈ c.act G P, (P.cw p : ℝ) := rfl
  unfold Pot
  rw [hins]
  have hLnn : (0 : ℝ) ≤ P.L := by positivity
  -- the inner inequality, before the factor `2560 L`
  have inner : 2 * ℓ * P.κ * ((lam P 0 : ℕ) + 3) + 9 * (c.V G P + ℓ * P.κ) +
      2 * (Fe P.κ (c.V G P + ℓ * P.κ) - ∑ k ∈ Finset.range D.nch, Fe P.κ (c.part G P D k)) +
      (2 * ∑ k ∈ Finset.range D.nch, Fe P.κ ((cs k).V G P) +
        (2 * Lam G P + 9 * G0 G P) * ∑ k ∈ Finset.range D.nch, inact G P (cs k) +
        9 * ∑ k ∈ Finset.range D.nch, (cs k).gsum G P +
        (2 * (lam P 0 : ℕ) + 24 + 2 * Lam G P) * P.κ * (2 * (c.X.card : ℝ) - (ℓ + 1))) ≤
      2 * Fe P.κ (c.V G P) + (2 * Lam G P + 9 * G0 G P) * inact G P c +
        9 * c.gsum G P + (2 * (lam P 0 : ℕ) + 24 + 2 * Lam G P) * P.κ *
          (2 * (c.X.card : ℝ) - 1) := by
    have hκℓ : (P.κ : ℝ) ≤ ℓ * P.κ := by nlinarith
    linarith
  have := mul_le_mul_of_nonneg_left inner (show (0 : ℝ) ≤ 2560 * P.L by positivity)
  linarith

end Cl

open Cl in
/-- **The stretch bound for a run.** The weighted stretch of the pairs inside a cluster of a run
is at most its potential. -/
theorem Run.stretch (hGo : G.Ok) (hB : 1 ≤ P.B) (hκ : 1 ≤ P.κ) (hQ : 512 * P.B * G.n ^ 2 ≤ P.Q)
    (hBL : 8 * P.L * (lam P 0 + 3) ≤ 2 * P.B) {c : Cl} {T : List ℕ} (h : Run G P c T)
    (hc : c.Inv G P) : Str G P c.X T ≤ c.Pot G P := by
  induction h with
  | @leaf c hX =>
    have : Str G P c.X [] = 0 := by
      unfold Str
      refine Finset.sum_eq_zero fun p hp => ?_
      obtain ⟨hm, hu, hv⟩ := PG.mem_ins.mp hp
      exact absurd (Finset.card_le_one.mp hX _ hu _ hv) (hGo p hm).2.2.1
    rw [this]
    exact Pot_nonneg hGo hκ hc
  | @node c D cs Ts hX hD hn hr ih =>
    have hrun := Run.node D cs Ts hX hD hn hr
    set T := (List.range D.nch).flatMap Ts ++ D.portals with hT
    have hinv : ∀ k < D.nch, (cs k).Inv G P := fun k hk => child_inv hGo hB hc hX hD hk (hn k hk)
    have hsub : ∀ k < D.nch, ∀ p ∈ Ts k, p ∈ T := fun k hk p hp =>
      List.mem_append_left _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, hp⟩)
    have hrad := Run.radius hGo hB hrun hc
    unfold Str
    rw [sum_ins (D := D)]
    -- the pairs inside the children
    have hkids : ∀ k ∈ Finset.range D.nch, ∑ p ∈ G.ins (c.raw G D k).X,
        (P.cw p : ℝ) * G.tdist T (G.pu p) (G.pv p) / G.pω p ≤ (cs k).Pot G P := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      refine le_trans ?_ (ih k hk' (hinv k hk'))
      unfold Str
      rw [(hn k hk').X_eq]
      refine Finset.sum_le_sum fun p hp => ?_
      have hrk := Run.radius hGo hB (hr k hk') (hinv k hk')
      have hp' : p ∈ G.ins (cs k).X := by rw [(hn k hk').X_eq]; exact hp
      have htw := hrk.tw hp'
      have hle : G.tdist T (G.pu p) (G.pv p) ≤ G.tdist (Ts k) (G.pu p) (G.pv p) :=
        tdist_mono htw (hsub k hk')
      have hle' : (G.tdist T (G.pu p) (G.pv p) : ℝ) ≤ G.tdist (Ts k) (G.pu p) (G.pv p) := by
        exact_mod_cast hle
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hle' (by positivity)
    have h1 := Finset.sum_le_sum hkids
    -- the cut pairs
    have h2 := cut_sum_le (D := D) hGo hB hc hX hQ hrad
    have h3 := cut_act_le (G := G) (P := P) (c := c) (D := D)
    have hΔ : (0 : ℝ) ≤ 20 * c.Δ G := by positivity
    have h4 := mul_le_mul_of_nonneg_left h3 hΔ
    have h5 := Pot_step hGo hB hκ hBL hc hX hD hn
    linarith


end MinCostFlow.LowStretch
