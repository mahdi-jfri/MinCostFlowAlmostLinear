module

public import MinCostFlow.LowStretch.Math
public import MinCostFlow.LowStretch.Work

/-!
# The operation count

**Item 2.** The program does two things. First it reads the graph and rounds each weight `w` to
the power of two `2^(⌊log₂ w⌋ + σ)`. It finds the exponent `⌊log₂ w⌋` by binary search, in
`wsteps W` rounds for weights at most `W`, and it spends a fixed amount per vertex, per edge and
per round. So this part costs at most `A · (m + 1) · (pa n + wsteps W)` for a fixed `A`, where
`pa n = ⌊log₂(n + 2)⌋ + 1` also pays for the union-find steps on each edge. Then it handles the
clusters of a run. A cluster costs `A · pL n` for itself and for each active pair: `pL n` is the
cost of a heap step over the `O(log n)` weight classes of a cluster. This is the relation
`Counted (A · pL n)` of `MinCostFlow/LowStretch/Work.lean`.

The main result is `count_le`: for every `A`, this count is at most
`K · (m + 1) · (log(n+2) log log(n+2) + log(n+2) log(log(W+2)+2))`, the time bound of the
statement.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open MinCostFlow.Cited Real

variable {G : WGraph}

/-- The rounds of a binary search for `⌊log₂ w⌋` when `w ≤ W`. -/
def wsteps (W : ℕ) : ℕ := Nat.log 2 (Nat.log 2 W + 1) + 1

/-- The work of the first cluster is at most `(m + 1) (2 G0 + 2)`. -/
theorem Wk_root_le (h : Allowed G) {θ : ℕ} (hc : (root (pgOf G) θ).Inv (pgOf G) (par G.n G.m))
    (hnm : G.n ≤ G.m + 1) :
    (root (pgOf G) θ).Wk (pgOf G) (par G.n G.m) ≤
      (G.m + 1) * (2 * G0 (pgOf G) (par G.n G.m) + 2) := by
  classical
  set P := par G.n G.m with hPdef
  set H := pgOf G with hH
  set c := root H θ with hcdef
  have hP := h.fit
  have hmH : H.m = G.m := by simp [hH, pgOf]
  have hG0 := Cl.G0_ge (G := H) (P := P)
  have h3 : Cl.inact H P c ≤ G.m := by
    unfold Cl.inact
    simp only [hPdef, par, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (Cl.lset H c).card ≤ G.m := by
      have := Finset.card_le_card (show Cl.lset H c ⊆ Finset.range H.m from
        Finset.filter_subset _ _)
      rwa [Finset.card_range, hmH] at this
    exact_mod_cast this
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
  have hcard : (c.X.card : ℝ) = G.n := by simp [hcdef, root, hH, pgOf]
  have hn : (G.n : ℝ) ≤ G.m + 1 := by exact_mod_cast hnm
  have h5 : G0 H P * Cl.inact H P c ≤ G0 H P * G.m := mul_le_mul_of_nonneg_left h3 (by linarith)
  unfold Cl.Wk
  rw [hcard]
  have hm : (0 : ℝ) ≤ G.m := Nat.cast_nonneg _
  nlinarith

/-- The binary search for the exponents takes `O(log(log(W + 2) + 2))` rounds. -/
theorem wsteps_le (W : ℕ) : (wsteps W : ℝ) ≤ 4 * log (log ((W : ℝ) + 2) + 2) := by
  have hl2 := log_two_gt
  have hW2 : log 2 ≤ log ((W : ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith [
    (Nat.cast_nonneg W : (0 : ℝ) ≤ W)])
  have hLw : log 2 ≤ log (log ((W : ℝ) + 2) + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  -- `⌊log₂ W⌋ ≤ 1.45 log(W + 2)`
  have h1 : (Nat.log 2 W : ℝ) ≤ 1.45 * log ((W : ℝ) + 2) := by
    rcases Nat.eq_zero_or_pos W with hW | hW
    · simp only [hW, Nat.log_zero_right, Nat.cast_zero]; linarith
    · have := natLog_le (x := W) hW
      have hlw : log (W : ℝ) ≤ log ((W : ℝ) + 2) :=
        Real.log_le_log (by exact_mod_cast hW) (by linarith)
      have hlw0 : 0 ≤ log (W : ℝ) := Real.log_nonneg (by exact_mod_cast hW)
      have hi := inv_log_two_le
      have : log (W : ℝ) / log 2 ≤ 1.45 * log ((W : ℝ) + 2) := by
        rw [div_eq_mul_one_div, mul_comm]
        exact mul_le_mul hi hlw hlw0 (by norm_num)
      linarith
  -- `⌊log₂(⌊log₂ W⌋ + 1)⌋ ≤ 1.45 (0.45 + log(log(W + 2) + 2))`
  have h2 := natLog_le (x := Nat.log 2 W + 1) (by omega)
  have hx : ((Nat.log 2 W + 1 : ℕ) : ℝ) ≤ 1.45 * (log ((W : ℝ) + 2) + 2) := by
    push_cast; linarith
  have hpos : (0 : ℝ) < ((Nat.log 2 W + 1 : ℕ) : ℝ) := by positivity
  have h3 : log ((Nat.log 2 W + 1 : ℕ) : ℝ) ≤ log 1.45 + log (log ((W : ℝ) + 2) + 2) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log hpos hx
  have h4 : log (1.45 : ℝ) ≤ 0.45 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.45 by norm_num); linarith
  have h5 : 0 ≤ log ((Nat.log 2 W + 1 : ℕ) : ℝ) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ ((Nat.log 2 W + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ Nat.log 2 W + 1 by omega)
    exact this)
  have h6 : log ((Nat.log 2 W + 1 : ℕ) : ℝ) / log 2 ≤
      1.45 * log ((Nat.log 2 W + 1 : ℕ) : ℝ) := by
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right inv_log_two_le h5
  unfold wsteps
  push_cast
  linarith

/-- **Item 2: the count is within the time bound.** For every `A` there is `K` such that the
cost `A · (m + 1) · (pa n + wsteps W)` of reading and rounding, plus any count of a run from the
first cluster at `A · pL n` per cluster and per active pair, is at most
`K · (m + 1) · (logLogFactor n + weightFactor n W)`. -/
theorem count_le (A : ℕ) : ∃ K : ℝ, ∀ G : WGraph, Allowed G → ∀ θ N : ℕ,
    (root (pgOf G) θ).Inv (pgOf G) (par G.n G.m) →
    Counted (pgOf G) (par G.n G.m) (A * pL G.n) (root (pgOf G) θ) N →
    (N : ℝ) + A * (G.m + 1) * (pa G.n + wsteps G.maxWeight) ≤
      K * (G.m + 1) * (logLogFactor G.n + weightFactor G.n G.maxWeight) := by
  refine ⟨42224 * A, fun G h θ N hc hN => ?_⟩
  have hP := h.fit
  have hn := h.conn.1
  have hℓ := ell_ge hn
  have hlℓ := log_ell_ge hn
  obtain ⟨θ', T, hθ', hT⟩ := exists_tree h
  have hnm := n_le_of_spanning (spanning h hθ' hT)
  -- the clusters
  have h1 := hN.le hP.ok hP.B (fun _ => le_rfl) hc
  have h2 := Wk_root_le h hc hnm
  have hG0 := G0_le h
  have hpL := pL_le hn
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ G.m + 1 := by positivity
  have hLLF : logLogFactor G.n = ell G.n * log (ell G.n) := rfl
  have hLLF0 : 0 ≤ ell G.n * log (ell G.n) := mul_nonneg (by linarith) (by linarith)
  have hW : 2 * G0 (pgOf G) (par G.n G.m) + 2 ≤ 260 * ell G.n := by linarith
  have hWk : (root (pgOf G) θ).Wk (pgOf G) (par G.n G.m) ≤ (G.m + 1) * (260 * ell G.n) :=
    h2.trans (mul_le_mul_of_nonneg_left hW hm)
  have hWk0 : 0 ≤ (root (pgOf G) θ).Wk (pgOf G) (par G.n G.m) := by
    have := Cl.Wk_leaf (P := par G.n G.m) hP.ok hc
    unfold Cl.Wk
    have := Cl.gsum_nonneg (P := par G.n G.m) hP.ok (root (pgOf G) θ)
    have := Cl.inact_nonneg (G := pgOf G) (P := par G.n G.m) (root (pgOf G) θ)
    have := Cl.G0_ge (G := pgOf G) (P := par G.n G.m)
    have : 0 ≤ G0 (pgOf G) (par G.n G.m) * Cl.inact (pgOf G) (par G.n G.m) (root (pgOf G) θ) :=
      mul_nonneg (by linarith) (by assumption)
    have : (1 : ℝ) ≤ (root (pgOf G) θ).X.card := by
      exact_mod_cast Finset.card_pos.mpr ⟨_, hc.good.conn.1⟩
    linarith
  have hN1 : (N : ℝ) ≤ A * (162 * log (ell G.n)) * ((G.m + 1) * (260 * ell G.n)) := by
    have e : ((A * pL G.n : ℕ) : ℝ) = A * (pL G.n : ℝ) := by push_cast; ring
    rw [e] at h1
    refine h1.trans ?_
    have hpL0 : (0 : ℝ) ≤ pL G.n := Nat.cast_nonneg _
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpL hA) hWk hWk0 (by positivity)
  -- reading and rounding
  have hpa : (pa G.n : ℝ) ≤ 100 * (ell G.n * log (ell G.n)) := by
    have := pa_le G.n
    nlinarith
  have hws := wsteps_le G.maxWeight
  have hwF : weightFactor G.n G.maxWeight = ell G.n * log (log ((G.maxWeight : ℝ) + 2) + 2) := rfl
  have hl2 := log_two_gt
  have hLw : log 2 ≤ log (log ((G.maxWeight : ℝ) + 2) + 2) := by
    have : log 2 ≤ log ((G.maxWeight : ℝ) + 2) := Real.log_le_log (by norm_num) (by
      linarith [(Nat.cast_nonneg G.maxWeight : (0 : ℝ) ≤ G.maxWeight)])
    exact Real.log_le_log (by norm_num) (by linarith)
  have hws' : (wsteps G.maxWeight : ℝ) ≤ 4 * weightFactor G.n G.maxWeight := by
    rw [hwF]; nlinarith
  have hwF0 : 0 ≤ weightFactor G.n G.maxWeight := by rw [hwF]; nlinarith
  rw [hLLF]
  have hpre : (A : ℝ) * (G.m + 1) * (pa G.n + wsteps G.maxWeight) ≤
      A * (G.m + 1) * (100 * (ell G.n * log (ell G.n)) + 4 * weightFactor G.n G.maxWeight) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA hm)
  have hN2 : (N : ℝ) ≤ A * (G.m + 1) * (42120 * (ell G.n * log (ell G.n))) := by
    have : A * (162 * log (ell G.n)) * ((G.m + 1) * (260 * ell G.n)) =
        A * (G.m + 1) * (42120 * (ell G.n * log (ell G.n))) := by ring
    linarith
  have hsum : (A : ℝ) * (G.m + 1) * (42120 * (ell G.n * log (ell G.n))) +
      A * (G.m + 1) * (100 * (ell G.n * log (ell G.n)) + 4 * weightFactor G.n G.maxWeight) ≤
      42224 * A * (G.m + 1) * (ell G.n * log (ell G.n) + weightFactor G.n G.maxWeight) := by
    have hAm : 0 ≤ (A : ℝ) * (G.m + 1) := mul_nonneg hA hm
    have : (A : ℝ) * (G.m + 1) * (42120 * (ell G.n * log (ell G.n))) +
        A * (G.m + 1) * (100 * (ell G.n * log (ell G.n)) + 4 * weightFactor G.n G.maxWeight) =
        A * (G.m + 1) * (42220 * (ell G.n * log (ell G.n)) + 4 * weightFactor G.n G.maxWeight) := by
      ring
    rw [this]
    have : 42224 * (A : ℝ) * (G.m + 1) * (ell G.n * log (ell G.n) + weightFactor G.n G.maxWeight) =
        A * (G.m + 1) * (42224 * (ell G.n * log (ell G.n)) + 42224 * weightFactor G.n G.maxWeight) := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hAm
  linarith

end MinCostFlow.LowStretch
