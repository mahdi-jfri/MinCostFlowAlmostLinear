module

public import MinCostFlow.LowStretch.Stretch2

/-!
# The stretch of the cut pairs

A cut pair of a cluster has a walk in the tree through the center, of length at most `20 Δ`
(`tdist_cut_le`). A cut pair that is not active is heavy: `ω > 4 Δ` (`heavy`), so its stretch is
at most `5`. The stretch of the active cut pairs is paid by region growing. Together
(`cut_sum_le`): the cut pairs have stretch at most `5 ∑ cw + 20 Δ ∑ cost`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable {G : PG} {P : Par}

variable (G P) in
/-- The weighted stretch of the pairs inside `X` in the tree `T`: `∑ cw · d_T / ω`. -/
noncomputable def Str (X : Finset ℕ) (T : List ℕ) : ℝ :=
  ∑ p ∈ G.ins X, (P.cw p : ℝ) * G.tdist T (G.pu p) (G.pv p) / G.pω p

namespace Cl

variable {c : Cl} {D : Dec}

/-- A pair inside a cluster of a run, with two or more vertices, has tree distance at most
`20 Δ`. -/
theorem tdist_le_20 (hB : 1 ≤ P.B) (hc : c.Inv G P) (hX : 2 ≤ c.X.card) {T : List ℕ}
    (hr : RadOk G P c T) {p : ℕ} (hp : p ∈ G.ins c.X) :
    G.tdist T (G.pu p) (G.pv p) ≤ 20 * c.Δ G := by
  have h := tdist_le (hr.tw hp)
  obtain ⟨-, hu, hv⟩ := PG.mem_ins.mp hp
  have h1 := d_le_Δ (G := G) hu
  have h2 := d_le_Δ (G := G) hv
  have hbig : P.B * c.X.card * c.θ ≤ c.Δ G := hc.big.resolve_left (by omega)
  have h3 : c.X.card * c.θ ≤ P.B * c.X.card * c.θ := by
    calc c.X.card * c.θ = 1 * c.X.card * c.θ := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hB)
  have hA : P.A * c.X.card * c.θ = 4 * (P.B * c.X.card * c.θ) + 4 * (c.X.card * c.θ) := by
    unfold Par.A; ring
  omega

/-- A cut pair that is not active is heavy: `4 Δ < ω`. -/
theorem heavy (hB : 1 ≤ P.B) (hc : c.Inv G P) (hQ : 512 * P.B * G.n ^ 2 ≤ P.Q) {p : ℕ} (hp : p ∈ c.cut G D)
    (hna : p ∉ c.act G P) : 4 * c.Δ G < G.pω p := by
  classical
  unfold cut at hp
  obtain ⟨hpi, hno⟩ := Finset.mem_filter.mp hp
  obtain ⟨hm, hu, hv⟩ := PG.mem_ins.mp hpi
  have hnl : ¬ c.LConn G (G.pu p) (G.pv p) := by
    intro hl
    obtain ⟨k, hk, huk⟩ := exists_piece (D := D) hu
    exact hno ⟨k, hk, huk, (lconn_piece hc.good.conn hl k).mp huk⟩
  have hω : P.Q * (c.Δ G * c.θ) < G.pω p ^ 2 := by
    by_contra hle
    exact hna (mem_act.mpr ⟨hm, hu, hv, hnl, by omega⟩)
  set K := 32 * P.B * G.n ^ 2 with hK
  have h1 : c.Δ G ≤ K * c.θ := hc.small
  have h2 : 16 * K ≤ P.Q := by
    have e : 16 * K = 512 * P.B * G.n ^ 2 := by rw [hK]; ring
    omega
  have h3 : P.Q * (c.Δ G * c.Δ G) ≤ K * (P.Q * (c.Δ G * c.θ)) := by
    calc P.Q * (c.Δ G * c.Δ G) ≤ P.Q * (c.Δ G * (K * c.θ)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
      _ = K * (P.Q * (c.Δ G * c.θ)) := by ring
  have h4 : 16 * K * (c.Δ G * c.Δ G) ≤ P.Q * (c.Δ G * c.Δ G) := Nat.mul_le_mul_right _ h2
  have hKpos : 0 < K := by
    have hn : 0 < G.n := by
      have := hc.sub hc.good.conn.1
      rw [Finset.mem_range] at this; omega
    rw [hK]; positivity
  have h5 : K * (16 * (c.Δ G * c.Δ G)) < K * (G.pω p * G.pω p) := by
    have : K * (P.Q * (c.Δ G * c.θ)) < K * G.pω p ^ 2 := Nat.mul_lt_mul_of_pos_left hω hKpos
    rw [pow_two] at this
    have e : K * (16 * (c.Δ G * c.Δ G)) = 16 * K * (c.Δ G * c.Δ G) := by ring
    omega
  have h6 : (4 * c.Δ G) * (4 * c.Δ G) < G.pω p * G.pω p := by
    have := Nat.lt_of_mul_lt_mul_left h5
    have e : (4 * c.Δ G) * (4 * c.Δ G) = 16 * (c.Δ G * c.Δ G) := by ring
    omega
  exact Nat.mul_self_lt_mul_self_iff.mp h6

/-- The stretch of the cut pairs: at most `5 ∑ cw` over the cut pairs, plus `20 Δ` times the
weight `cw / ω` of the active cut pairs. -/
theorem cut_sum_le (hGo : G.Ok) (hB : 1 ≤ P.B) (hc : c.Inv G P) (hX : 2 ≤ c.X.card)
    (hQ : 512 * P.B * G.n ^ 2 ≤ P.Q) {T : List ℕ} (hr : RadOk G P c T) :
    ∑ p ∈ c.cut G D, (P.cw p : ℝ) * G.tdist T (G.pu p) (G.pv p) / G.pω p ≤
      5 * ∑ p ∈ c.cut G D, (P.cw p : ℝ) +
        20 * c.Δ G * ∑ p ∈ c.cut G D ∩ c.act G P, (P.cw p : ℝ) / G.pω p := by
  classical
  have hΔ : (0 : ℝ) < c.Δ G := by exact_mod_cast hc.Δ_pos hB hX
  have key : ∀ p ∈ c.cut G D, (P.cw p : ℝ) * G.tdist T (G.pu p) (G.pv p) / G.pω p ≤
      5 * P.cw p + (if p ∈ c.act G P then 20 * c.Δ G * ((P.cw p : ℝ) / G.pω p) else 0) := by
    intro p hp
    have hpi : p ∈ G.ins c.X := (Finset.mem_filter.mp (by unfold cut at hp; exact hp)).1
    have hω : 0 < G.pω p := (hGo p (PG.mem_ins.mp hpi).1).2.2.2.2
    have hωr : (0 : ℝ) < G.pω p := by exact_mod_cast hω
    have ht : (G.tdist T (G.pu p) (G.pv p) : ℝ) ≤ 20 * c.Δ G := by
      exact_mod_cast tdist_le_20 hB hc hX hr hpi
    have hcw : (0 : ℝ) ≤ P.cw p := by positivity
    have hmain : (P.cw p : ℝ) * G.tdist T (G.pu p) (G.pv p) / G.pω p ≤
        20 * c.Δ G * ((P.cw p : ℝ) / G.pω p) := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hωr]
      nlinarith
    split_ifs with ha
    · linarith
    · have hh : (4 * c.Δ G : ℝ) < G.pω p := by exact_mod_cast heavy hB hc hQ hp ha
      refine hmain.trans ?_
      rw [add_zero, mul_div_assoc', div_le_iff₀ hωr]
      nlinarith
  refine (Finset.sum_le_sum key).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    ← Finset.mul_sum]

/-- A cluster with two or more vertices in a run has at least one petal. -/
theorem len_pos (hB : 1 ≤ P.B) (hc : c.Inv G P) (hX : 2 ≤ c.X.card) (hD : c.DecOk G P D) :
    0 < D.ps.length := by
  by_contra h0
  have hΔ := hc.Δ_pos hB hX
  obtain ⟨y, hy, he⟩ := exists_eq_Δ (G := G) (c := c) (Finset.card_pos.mp (by omega))
  have hs : y ∈ c.stem G D := by
    unfold stem; rw [show D.ps.length = 0 by omega]; exact hy
  have := hD.2.2.2 y hs
  omega

/-- There are at most `|X|` petals, since each holds its target. -/
theorem len_le_card (hD : c.DecOk G P D) : D.ps.length ≤ c.X.card := by
  have h := sum_card_raw (G := G) (c := c) (D := D)
  unfold Dec.nch at h
  rw [Finset.sum_range_succ'] at h
  have : ∑ k ∈ Finset.range D.ps.length, 1 ≤
      ∑ k ∈ Finset.range D.ps.length, (c.raw G D (k + 1)).X.card := by
    refine Finset.sum_le_sum fun k hk => ?_
    rw [rawP_X]
    have hpk := petalOk hD (Finset.mem_range.mp hk)
    exact Finset.card_pos.mpr ⟨_, hpk.2.2.2.1 0 (Nat.zero_le _)⟩
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at this
  omega

end Cl

end MinCostFlow.LowStretch
