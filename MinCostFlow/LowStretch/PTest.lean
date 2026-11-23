module

public import MinCostFlow.LowStretch.Grow

/-!
# The tests of region growing in integers

The program does not compute the volume and the cost of a petal as real numbers. It keeps, for
the petal `W`, the number `I` of active pairs inside `W`, and over the active pairs that leave
`W` the sums `C = Σ wt` and `V' = Σ wt · ent(inner end)`. Here `wt p = M / ω_p` for a common
multiple `M` of the weights (a power of two). With volume weights `1`,
`8 M vol = 8 M (κ + I) + r C - V'` and `M cost = C` (`vol_scaled`, `cost_scaled`). So both
tests of `PetalOk` are tests on natural numbers (`test1_iff`, `test2_iff`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable {G : PG} {P : Par}

namespace Cl

variable {c : Cl}

open Classical in
/-- The scaled volume. -/
theorem vol_scaled (hcw : ∀ p, P.cw p = 1) {M : ℕ} (wt : ℕ → ℕ)
    (hwt : ∀ p ∈ c.act G P, wt p * G.pω p = M) (hM : 0 < M) (Y : Finset ℕ) (pd : PD)
    (hent : ∀ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y pd) ·),
      c.ent G Y pd (inEnd G (c.carve G Y pd) p) ≤ pd.r) :
    8 * (M : ℝ) * c.vol G P Y pd =
      8 * M * (P.κ + ((c.act G P).filter (Inside G (c.carve G Y pd) ·)).card) +
      pd.r * (∑ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y pd) ·), (wt p : ℝ)) -
      ∑ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y pd) ·),
        (wt p : ℝ) * c.ent G Y pd (inEnd G (c.carve G Y pd) p) := by
  unfold vol
  simp only [hcw, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul]
  have key : ∀ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y pd) ·),
      8 * (M : ℝ) * (((pd.r - c.ent G Y pd (inEnd G (c.carve G Y pd) p) : ℕ) : ℝ) /
        (8 * G.pω p)) =
      pd.r * wt p - wt p * c.ent G Y pd (inEnd G (c.carve G Y pd) p) := by
    intro p hp
    have hpa : p ∈ c.act G P := (Finset.mem_filter.mp hp).1
    have h1 := hwt p hpa
    have hω : 0 < G.pω p := by
      rcases Nat.eq_zero_or_pos (G.pω p) with h | h
      · rw [h, Nat.mul_zero] at h1; omega
      · exact h
    have hωr : (0 : ℝ) < G.pω p := by exact_mod_cast hω
    have hMr : (M : ℝ) = wt p * G.pω p := by exact_mod_cast h1.symm
    rw [Nat.cast_sub (hent p hp), hMr]
    field_simp
    try ring
  rw [mul_add, mul_add, Finset.mul_sum, Finset.sum_congr rfl key, Finset.sum_sub_distrib,
    Finset.mul_sum]
  ring

open Classical in
/-- The scaled cost. -/
theorem cost_scaled (hcw : ∀ p, P.cw p = 1) {M : ℕ} (wt : ℕ → ℕ)
    (hwt : ∀ p ∈ c.act G P, wt p * G.pω p = M) (hM : 0 < M) (Y : Finset ℕ) (pd : PD) :
    (M : ℝ) * c.cost G P Y pd =
      ∑ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y pd) ·), (wt p : ℝ) := by
  unfold cost
  simp only [hcw, Nat.cast_one]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpa : p ∈ c.act G P := (Finset.mem_filter.mp hp).1
  have h1 := hwt p hpa
  have hω : 0 < G.pω p := by
    rcases Nat.eq_zero_or_pos (G.pω p) with h | h
    · rw [h, Nat.mul_zero] at h1; omega
    · exact h
  have hωr : (0 : ℝ) < G.pω p := by exact_mod_cast hω
  have hMr : (M : ℝ) = wt p * G.pω p := by exact_mod_cast h1.symm
  rw [hMr]
  field_simp

open Classical in
/-- **The first test in integers.** Here `I`, `C` and `V'` are the counts and sums above. -/
theorem test1_iff (hcw : ∀ p, P.cw p = 1) {M : ℕ} (wt : ℕ → ℕ)
    (hwt : ∀ p ∈ c.act G P, wt p * G.pω p = M) (hM : 0 < M) (Y : Finset ℕ) (pd : PD)
    (hent : ∀ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y pd) ·),
      c.ent G Y pd (inEnd G (c.carve G Y pd) p) ≤ pd.r) {I C V' s : ℕ}
    (hI : ((c.act G P).filter (Inside G (c.carve G Y pd) ·)).card = I)
    (hC : ∑ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y pd) ·), wt p = C)
    (hV : ∑ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y pd) ·),
      wt p * c.ent G Y pd (inEnd G (c.carve G Y pd) p) = V') :
    V' ≤ pd.r * C ∧
      (c.cost G P Y pd * s ≤ 8 * c.vol G P Y pd ↔ C * s ≤ 8 * M * (P.κ + I) + pd.r * C - V') := by
  have hle : V' ≤ pd.r * C := by
    rw [← hV, ← hC, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [mul_comm (pd.r)]; exact Nat.mul_le_mul_left _ (hent p hp)
  refine ⟨hle, ?_⟩
  have hv := vol_scaled hcw wt hwt hM Y pd hent
  have hc := cost_scaled hcw wt hwt hM Y pd
  rw [hI] at hv
  have hCr : (∑ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y pd) ·), (wt p : ℝ)) = C := by
    rw [← hC]; push_cast; rfl
  have hVr : (∑ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y pd) ·),
      (wt p : ℝ) * c.ent G Y pd (inEnd G (c.carve G Y pd) p)) = V' := by
    rw [← hV]; push_cast; rfl
  rw [hCr, hVr] at hv
  rw [hCr] at hc
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hlhs : (((8 * M * (P.κ + I) + pd.r * C - V' : ℕ)) : ℝ) = 8 * M * c.vol G P Y pd := by
    rw [hv, Nat.cast_sub (le_trans hle (Nat.le_add_left _ _))]
    push_cast; ring
  constructor
  · intro h
    have h2 : ((C * s : ℕ) : ℝ) ≤ ((8 * M * (P.κ + I) + pd.r * C - V' : ℕ) : ℝ) := by
      rw [hlhs]; push_cast; rw [← hc]
      have := mul_le_mul_of_nonneg_left h hMr.le
      linarith
    exact_mod_cast h2
  · intro h
    have h2 : ((C * s : ℕ) : ℝ) ≤ ((8 * M * (P.κ + I) + pd.r * C - V' : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [hlhs] at h2; push_cast at h2; rw [← hc] at h2
    have : (M : ℝ) * (c.cost G P Y pd * s) ≤ M * (8 * c.vol G P Y pd) := by linarith
    exact le_of_mul_le_mul_left this hMr

open Classical in
/-- **The second test in integers**, for bucket `q`. -/
theorem test2_iff (hcw : ∀ p, P.cw p = 1) {M : ℕ} (wt : ℕ → ℕ)
    (hwt : ∀ p ∈ c.act G P, wt p * G.pω p = M) (hM : 0 < M) (Y : Finset ℕ) (pd : PD)
    (hent : ∀ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y pd) ·),
      c.ent G Y pd (inEnd G (c.carve G Y pd) p) ≤ pd.r) {I C V' q : ℕ}
    (hI : ((c.act G P).filter (Inside G (c.carve G Y pd) ·)).card = I)
    (hC : ∑ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y pd) ·), wt p = C)
    (hV : ∑ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y pd) ·),
      wt p * c.ent G Y pd (inEnd G (c.carve G Y pd) p) = V') :
    c.vol G P Y pd ≤ c.T G P q ↔
      (8 * M * (P.κ + I) + pd.r * C - V') * 2 ^ lam P q ≤
        8 * M * (4 * (P.κ + (c.act G P).card) + P.κ * 2 ^ lam P q) := by
  obtain ⟨hle, -⟩ := test1_iff (s := 0) hcw wt hwt hM Y pd hent hI hC hV
  have hv := vol_scaled hcw wt hwt hM Y pd hent
  rw [hI] at hv
  have hCr : (∑ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y pd) ·), (wt p : ℝ)) = C := by
    rw [← hC]; push_cast; rfl
  have hVr : (∑ p ∈ (c.act G P).filter (Leaves G Y (c.carve G Y pd) ·),
      (wt p : ℝ) * c.ent G Y pd (inEnd G (c.carve G Y pd) p)) = V' := by
    rw [← hV]; push_cast; rfl
  rw [hCr, hVr] at hv
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hlhs : (((8 * M * (P.κ + I) + pd.r * C - V' : ℕ)) : ℝ) = 8 * M * c.vol G P Y pd := by
    rw [hv, Nat.cast_sub (le_trans hle (Nat.le_add_left _ _))]
    push_cast; ring
  have hVc : c.V G P = P.κ + (c.act G P).card := by
    unfold V; simp [hcw]
  have hp : (0 : ℝ) < 2 ^ lam P q := by positivity
  unfold T
  rw [hVc]
  constructor
  · intro h
    have h2 : (((8 * M * (P.κ + I) + pd.r * C - V') * 2 ^ lam P q : ℕ) : ℝ) ≤
        ((8 * M * (4 * (P.κ + (c.act G P).card) + P.κ * 2 ^ lam P q) : ℕ) : ℝ) := by
      push_cast
      rw [hlhs]
      have h3 : 8 * (M : ℝ) * c.vol G P Y pd * 2 ^ lam P q ≤
          8 * M * ((4 * (P.κ + (c.act G P).card) / 2 ^ lam P q + P.κ) * 2 ^ lam P q) := by
        have := mul_le_mul_of_nonneg_right h hp.le
        nlinarith
      rw [add_mul, div_mul_cancel₀ _ hp.ne'] at h3
      linarith
    exact_mod_cast h2
  · intro h
    have h2 : (((8 * M * (P.κ + I) + pd.r * C - V') * 2 ^ lam P q : ℕ) : ℝ) ≤
        ((8 * M * (4 * (P.κ + (c.act G P).card) + P.κ * 2 ^ lam P q) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h2
    rw [hlhs] at h2
    have h3 : c.vol G P Y pd * 2 ^ lam P q ≤ 4 * (P.κ + (c.act G P).card) + P.κ * 2 ^ lam P q := by
      have h8 : (0 : ℝ) < 8 * M := by positivity
      nlinarith
    have h4 : c.vol G P Y pd ≤ (4 * (P.κ + (c.act G P).card) + P.κ * 2 ^ lam P q) / 2 ^ lam P q :=
      (le_div_iff₀ hp).mpr h3
    rw [add_div, mul_div_cancel_right₀ _ hp.ne'] at h4
    exact h4

end Cl

end MinCostFlow.LowStretch
