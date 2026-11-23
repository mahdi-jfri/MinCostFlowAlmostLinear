module

public import MinCostFlow.LowStretch.Stretch3

/-!
# Levels and volumes from a cluster to its children

Two bounds that let the potential telescope.
* *Levels.* An active pair `p` of a cluster has `g(p) = log_{4/3}(Q Δ θ / ω²) + 1 ≥ 1` levels
  left, and at most `G0` (`gl_le`). From a cluster to a child where it is still active, `g` drops
  by at least `1`, because `Δ θ` drops by a factor `3/4`. So the weights of the active pairs of a
  cluster are paid by the drop of `∑ cw · g`, up to `G0` for each new active pair (`gsum_step`).
* *Volumes.* A child has `F(V') ≤ F(part) + Λ · New` for its part and the weight `New` of its new
  active pairs (`Fe_child`), where `Λ = log₂(Vmax / κ) + 2`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open Real

variable (G : PG) (P : Par)

/-- A bound for every volume: `(n + 1) κ` plus the weights of all pairs. -/
noncomputable def Vmax : ℝ := (G.n + 1) * P.κ + ∑ p ∈ Finset.range G.m, (P.cw p : ℝ)

/-- The price of one unit of new volume. -/
noncomputable def Lam : ℝ := logb 2 (Vmax G P / P.κ) + 2

/-- The most levels a pair can have left. -/
noncomputable def G0 : ℝ := logb (4 / 3) (32 * P.B * P.Q * G.n ^ 2) + 1

namespace Cl

/-- The levels left for pair `p` in cluster `c`. -/
noncomputable def gl (c : Cl) (p : ℕ) : ℝ :=
  logb (4 / 3) ((P.Q : ℝ) * (c.Δ G * c.θ) / (G.pω p : ℝ) ^ 2) + 1

/-- The weights of the active pairs, times their levels left. -/
noncomputable def gsum (c : Cl) : ℝ := ∑ p ∈ c.act G P, (P.cw p : ℝ) * c.gl G P p

variable {G P} {c : Cl} {D : Dec}

theorem ratio_ge_one (hGo : G.Ok) {p : ℕ} (hp : p ∈ c.act G P) :
    1 ≤ (P.Q : ℝ) * (c.Δ G * c.θ) / (G.pω p : ℝ) ^ 2 := by
  have ha := mem_act.mp hp
  have hω : (0 : ℝ) < G.pω p := by exact_mod_cast (hGo p ha.1).2.2.2.2
  rw [le_div_iff₀ (by positivity), one_mul]
  exact_mod_cast ha.2.2.2.2

theorem gl_ge_one (hGo : G.Ok) {p : ℕ} (hp : p ∈ c.act G P) : 1 ≤ c.gl G P p := by
  unfold gl
  have := logb_nonneg (show (1 : ℝ) < 4 / 3 by norm_num) (ratio_ge_one hGo hp)
  linarith

theorem gl_le (hGo : G.Ok) (hc : c.Inv G P) {p : ℕ} (hp : p ∈ c.act G P) :
    c.gl G P p ≤ G0 G P := by
  unfold gl G0
  have ha := mem_act.mp hp
  have hω : (0 : ℝ) < G.pω p := by exact_mod_cast (hGo p ha.1).2.2.2.2
  have hθ : (c.θ : ℝ) ≤ G.pω p := by exact_mod_cast ha.not_light
  have hs : (c.Δ G : ℝ) ≤ 32 * P.B * G.n ^ 2 * c.θ := by exact_mod_cast hc.small
  have h1 : (P.Q : ℝ) * (c.Δ G * c.θ) / (G.pω p : ℝ) ^ 2 ≤ 32 * P.B * P.Q * G.n ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (c.θ : ℝ) * c.θ ≤ G.pω p * G.pω p := mul_le_mul hθ hθ (by positivity) hω.le
    have h3 : (c.Δ G : ℝ) * c.θ ≤ 32 * P.B * G.n ^ 2 * (c.θ * c.θ) := by
      have := mul_le_mul_of_nonneg_right hs (show (0 : ℝ) ≤ c.θ by positivity)
      linarith
    have h4 : (0 : ℝ) ≤ 32 * P.B * G.n ^ 2 := by positivity
    have h5 := mul_le_mul_of_nonneg_left h2 h4
    have h6 : (0 : ℝ) ≤ P.Q := by positivity
    nlinarith
  have := logb_le_logb_of_le (show (1 : ℝ) < 4 / 3 by norm_num)
    (lt_of_lt_of_le one_pos (ratio_ge_one hGo hp)) h1
  linarith

theorem gl_child (hGo : G.Ok) {c' : Cl} {p : ℕ} (hp : p ∈ c.act G P) (hp' : p ∈ c'.act G P)
    (hψ : 4 * (c'.Δ G * c'.θ) ≤ 3 * (c.Δ G * c.θ)) : c'.gl G P p ≤ c.gl G P p - 1 := by
  unfold gl
  have ha := mem_act.mp hp
  have hω : (0 : ℝ) < G.pω p := by exact_mod_cast (hGo p ha.1).2.2.2.2
  have h1 := ratio_ge_one hGo hp'
  have hψr : (4 : ℝ) * (c'.Δ G * c'.θ) ≤ 3 * (c.Δ G * c.θ) := by exact_mod_cast hψ
  have h2 : (P.Q : ℝ) * (c'.Δ G * c'.θ) / (G.pω p : ℝ) ^ 2 ≤
      (3 / 4) * ((P.Q : ℝ) * (c.Δ G * c.θ) / (G.pω p : ℝ) ^ 2) := by
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
    have : (0 : ℝ) ≤ P.Q := by positivity
    nlinarith
  have h3 := logb_le_logb_of_le (show (1 : ℝ) < 4 / 3 by norm_num)
    (lt_of_lt_of_le one_pos h1) h2
  rw [logb_mul (by norm_num) (by linarith [ratio_ge_one hGo hp])] at h3
  have e : logb (4 / 3) (3 / 4 : ℝ) = -1 := by
    rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, logb_inv, logb_self_eq_one (by norm_num)]
  linarith

/-- The weights of the active pairs are paid by the drop of `∑ cw · g`, up to `G0` for each new
active pair. -/
theorem gsum_step (hGo : G.Ok) (hB : 1 ≤ P.B) (hc : c.Inv G P) (hX : 2 ≤ c.X.card)
    (hD : c.DecOk G P D) {cs : ℕ → Cl} (hn : ∀ k < D.nch, Next G P (c.raw G D k) (cs k)) :
    ∑ p ∈ c.act G P, (P.cw p : ℝ) + ∑ k ∈ Finset.range D.nch, (cs k).gsum G P ≤
      c.gsum G P + G0 G P * ∑ k ∈ Finset.range D.nch,
        ∑ p ∈ (cs k).act G P \ c.act G P, (P.cw p : ℝ) := by
  classical
  have hinv : ∀ k < D.nch, (cs k).Inv G P := fun k hk => child_inv hGo hB hc hX hD hk (hn k hk)
  -- split each child's sum into old and new active pairs
  have hsplit : ∀ k ∈ Finset.range D.nch, (cs k).gsum G P ≤
      ∑ p ∈ (cs k).act G P ∩ c.act G P, (P.cw p : ℝ) * (c.gl G P p - 1) +
        G0 G P * ∑ p ∈ (cs k).act G P \ c.act G P, (P.cw p : ℝ) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    unfold gsum
    rw [← Finset.sum_inter_add_sum_sdiff ((cs k).act G P) (c.act G P), Finset.mul_sum]
    refine add_le_add (Finset.sum_le_sum fun p hp => ?_) (Finset.sum_le_sum fun p hp => ?_)
    · obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hp
      exact mul_le_mul_of_nonneg_left
        (gl_child hGo h2 h1 (psi_child hGo hB hc hX hD hk' (hn k hk'))) (by positivity)
    · rw [mul_comm (G0 G P)]
      exact mul_le_mul_of_nonneg_left (gl_le hGo (hinv k hk') (Finset.mem_sdiff.mp hp).1)
        (by positivity)
  refine (add_le_add le_rfl (Finset.sum_le_sum hsplit)).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  -- the old active pairs of the children are different active pairs of the cluster
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range D.nch))
      fun k => (cs k).act G P ∩ c.act G P := by
    intro j hj k hk hjk
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpj hpk
    have hj' := Finset.mem_range.mp hj
    have hk' := Finset.mem_range.mp hk
    have hu1 := (act_inside (Finset.mem_inter.mp hpj).1).2.1
    have hu2 := (act_inside (Finset.mem_inter.mp hpk).1).2.1
    rw [(hn j hj').X_eq] at hu1
    rw [(hn k hk').X_eq] at hu2
    exact hjk (raw_eq_of_mem hj' hk' hu1 hu2)
  rw [← Finset.sum_biUnion hdisj]
  have hsub : (Finset.range D.nch).biUnion (fun k => (cs k).act G P ∩ c.act G P) ⊆ c.act G P := by
    intro p hp
    obtain ⟨k, -, hp⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_inter.mp hp).2
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p => (P.cw p : ℝ) * (c.gl G P p - 1)) fun p hp _ => by
      have := gl_ge_one hGo hp
      exact mul_nonneg (by positivity) (by linarith)
  have e : ∑ p ∈ c.act G P, (P.cw p : ℝ) * (c.gl G P p - 1) =
      c.gsum G P - ∑ p ∈ c.act G P, (P.cw p : ℝ) := by
    unfold gsum
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  linarith

/-- The volume of a cluster plus the weight of the new active pairs of another cluster is at most
`κ` plus the weights of all pairs. -/
theorem V_add_new_le (c' : Cl) :
    c.V G P + ∑ p ∈ c'.act G P \ c.act G P, (P.cw p : ℝ) ≤
      P.κ + ∑ p ∈ Finset.range G.m, (P.cw p : ℝ) := by
  classical
  have hsub : c.act G P ⊆ Finset.range G.m := fun p hp =>
    Finset.mem_range.mpr (act_inside hp).1
  have h1 : c'.act G P \ c.act G P ⊆ Finset.range G.m \ c.act G P := fun p hp =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (act_inside (Finset.mem_sdiff.mp hp).1).1,
      (Finset.mem_sdiff.mp hp).2⟩
  have h2 := Finset.sum_le_sum_of_subset_of_nonneg h1 (f := fun p => (P.cw p : ℝ))
    fun _ _ _ => by positivity
  have h3 := Finset.sum_sdiff hsub (f := fun p => (P.cw p : ℝ))
  unfold V
  linarith

/-- A child pays for its new volume at the price `Λ`. -/
theorem Fe_child (hκ : 1 ≤ P.κ) {k : ℕ} {c' : Cl} (hX : c'.X = (c.raw G D k).X)
    (hle : c.part G P D k + ∑ p ∈ c'.act G P \ c.act G P, (P.cw p : ℝ) ≤ Vmax G P) :
    Fe P.κ (c'.V G P) ≤ Fe P.κ (c.part G P D k) +
      Lam G P * ∑ p ∈ c'.act G P \ c.act G P, (P.cw p : ℝ) := by
  set N := ∑ p ∈ c'.act G P \ c.act G P, (P.cw p : ℝ) with hN
  have hκr : (0 : ℝ) < P.κ := by exact_mod_cast hκ
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ => by positivity
  have hp := part_ge (c := c) (G := G) (P := P) (D := D) k
  have h1 := child_V (P := P) hX
  rw [← hN] at h1
  have h2 := Fe_mono hκr V_ge h1
  have h3 := Fe_sub_le hκr hp (show c.part G P D k ≤ c.part G P D k + N by linarith)
  have h4 : logb 2 ((c.part G P D k + N) / P.κ) ≤ logb 2 (Vmax G P / P.κ) := by
    apply logb_le_logb_of_le (by norm_num) (div_pos (by linarith) hκr)
    exact div_le_div_of_nonneg_right hle hκr.le
  have h5 : N * (logb 2 ((c.part G P D k + N) / P.κ) + 2) ≤ N * Lam G P := by
    unfold Lam
    exact mul_le_mul_of_nonneg_left (by linarith) hN0
  have e : c.part G P D k + N - c.part G P D k = N := by ring
  rw [e] at h3
  linarith

end Cl

end MinCostFlow.LowStretch
