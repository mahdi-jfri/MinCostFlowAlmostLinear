module

public import MinCostFlow.LowStretch.ProgPre
public import MinCostFlow.LowStretch.Count
public import MinCostFlow.LowStretch.Math

/-!
# The cost of the preprocessing

The cost `preCost G` of `preP` is at most `20000 (m + 1) (pa n + wsteps W)` for the largest
weight `W` (`preCost_le`), which is the preprocessing term of `count_le` with `A = 20000`. The
terms with `log n` are at most a constant times `pa n`. The one call of `log2P` on
`S = maxω + 4Bn < 2^(log W + σ + 1)` costs `O(log log W + σ)`, and `σ ≤ 16 pa n`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open MinCostFlow.Cited

variable {G : WGraph}

theorem log_mul_le (a b : ℕ) : Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b + 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) a
  have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) b
  have : a * b < 2 ^ (Nat.log 2 a + Nat.log 2 b + 1 + 1) := by
    calc a * b < 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) := Nat.mul_lt_mul'' h1 h2
      _ = 2 ^ (Nat.log 2 a + Nat.log 2 b + 1 + 1) := by rw [← pow_add]; ring_nf
  exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by positivity) this)

theorem log_sq_le (n : ℕ) : Nat.log 2 (n * n + 2) ≤ 2 * pa n := by
  have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n + 2)
  have : n * n + 2 < 2 ^ (2 * pa n) := by
    unfold pa
    calc n * n + 2 ≤ (n + 2) * (n + 2) := by nlinarith
      _ < 2 ^ (Nat.log 2 (n + 2) + 1) * 2 ^ (Nat.log 2 (n + 2) + 1) := Nat.mul_lt_mul'' h1 h1
      _ = 2 ^ (2 * (Nat.log 2 (n + 2) + 1)) := by rw [← pow_add]; ring_nf
  have := Nat.log_lt_of_lt_pow (by omega) this
  omega

theorem log_le_pa (n : ℕ) : Nat.log 2 n ≤ pa n := by
  unfold pa; have := Nat.log_mono_right (b := 2) (show n ≤ n + 2 by omega); omega

theorem pσ_le_pa (n : ℕ) : pσ n ≤ 16 * pa n := by
  have h3 := pB_le_poly n
  have hx : 8 * pB n * n < 2 ^ (15 + 3 * Nat.log 2 (n + 2)) := by
    have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n + 2)
    have h4 : n + 4 < 2 * 2 ^ (Nat.log 2 (n + 2) + 1) := by omega
    have h5 : n < n + 4 := by omega
    calc 8 * pB n * n ≤ 8 * (64 * (n + 4) ^ 2) * (n + 4) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 8 h3) h5.le
      _ = 512 * (n + 4) ^ 3 := by ring
      _ < 512 * (2 * 2 ^ (Nat.log 2 (n + 2) + 1)) ^ 3 :=
          Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left h4 (by norm_num)) (by norm_num)
      _ = 2 ^ (15 + 3 * Nat.log 2 (n + 2)) := by rw [← pow_succ', ← pow_mul]; norm_num; ring_nf
  have : Nat.log 2 (8 * pB n * n) < 15 + 3 * Nat.log 2 (n + 2) := by
    rcases Nat.eq_zero_or_pos (8 * pB n * n) with h | h
    · rw [h]; simp
    · exact Nat.log_lt_of_lt_pow (by omega) hx
  unfold pσ pa; omega

theorem foldr_max_le {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem maxω_le : (pgOf G).maxω ≤ 2 ^ (Nat.log 2 G.maxWeight + pσ G.n) := by
  unfold PG.maxω
  refine foldr_max_le fun x hx => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  have hp' : p < G.m := by rw [← pgOf_m]; exact List.mem_range.mp hp
  rw [pω_wtOf hp']
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.add_le_add_right (Nat.log_mono_right (wtOf_le_maxWeight hp')) _)

/-- The one call of `log2P` of the record part. -/
theorem log2Cost_S_le :
    log2Cost ((pgOf G).maxω + 4 * pB G.n * G.n) ≤ 50 * (wsteps G.maxWeight + 16 * pa G.n + 3) := by
  have hpσ := pσ_le_pa G.n
  have hm := maxω_le (G := G)
  unfold log2Cost wsteps
  generalize hX : (pgOf G).maxω + 4 * pB G.n * G.n = X
  generalize hL : Nat.log 2 G.maxWeight = L at hm
  have h1 : 4 * pB G.n * G.n < 2 ^ pσ G.n := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (8 * pB G.n * G.n)
    have e : 8 * pB G.n * G.n = 2 * (4 * pB G.n * G.n) := by ring
    unfold pσ; rw [pow_succ]; omega
  have hσ1 : 1 ≤ pσ G.n := by unfold pσ; omega
  generalize pσ G.n = σ at *
  have h2 : 2 ^ σ ≤ 2 ^ (L + σ) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX' : X < 2 ^ (L + σ + 1) := by rw [pow_succ]; omega
  have hlX : Nat.log 2 X ≤ L + σ := by
    rcases Nat.eq_zero_or_pos X with h | h
    · rw [h]; simp
    · exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) hX')
  have h3 : Nat.log 2 X + 1 ≤ 2 * ((L + 1) * σ) := by
    have : L + 1 ≤ (L + 1) * σ := Nat.le_mul_of_pos_right _ hσ1
    have : σ ≤ (L + 1) * σ := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h4 : Nat.log 2 (Nat.log 2 X + 1) ≤ Nat.log 2 (L + 1) + σ + 2 := by
    have := Nat.log_mono_right (b := 2) h3
    have h5 : Nat.log 2 (2 * ((L + 1) * σ)) = Nat.log 2 ((L + 1) * σ) + 1 := by
      rw [mul_comm, Nat.log_mul_base (by norm_num) (by positivity)]
    have h6 := log_mul_le (L + 1) σ
    have h7 : Nat.log 2 σ ≤ σ := (Nat.log_lt_self 2 (by omega)).le
    omega
  omega

/-- **The cost of the preprocessing** is within the preprocessing term of `count_le`. -/
theorem preCost_le (h : Allowed G) :
    preCost G ≤ 20000 * (G.m + 1) * (pa G.n + wsteps G.maxWeight) := by
  obtain ⟨θ, T, hθ, hT⟩ := exists_tree h
  have hnm := n_le_of_spanning (spanning h hθ hT)
  have hS := log2Cost_S_le (G := G)
  have hsq := log_sq_le G.n
  have hlog := log_le_pa G.n
  have hpa : 1 ≤ pa G.n := by unfold pa; omega
  have hw : log2Cost G.maxWeight = 50 * (wsteps G.maxWeight + 1) := by unfold log2Cost wsteps; ring
  unfold preCost wCost kCost gCost
  rw [hw]
  generalize log2Cost ((pgOf G).maxω + 4 * pB G.n * G.n) = C at *
  generalize pa G.n = P at *
  generalize wsteps G.maxWeight = Q at *
  generalize Nat.log 2 (G.n * G.n + 2) = A at *
  generalize Nat.log 2 G.n = B at *
  generalize G.m = m at *
  generalize G.n = n at *
  have e1 : m * A ≤ m * (2 * P) := Nat.mul_le_mul_left m hsq
  have e2 : m * B ≤ m * P := Nat.mul_le_mul_left m hlog
  have e3 : m * 1 ≤ m * P := Nat.mul_le_mul_left m hpa
  have e4 : n * 1 ≤ (m + 1) * P := Nat.mul_le_mul hnm hpa
  have e5 : 1 * 1 ≤ (m + 1) * P := Nat.mul_le_mul (by omega) hpa
  have e6 : Q ≤ (m + 1) * Q := Nat.le_mul_of_pos_left Q (by omega)
  nlinarith

end MinCostFlow.LowStretch
