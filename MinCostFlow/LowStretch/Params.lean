module

public import MinCostFlow.LowStretch.Reduce

/-!
# The constants

The constants depend on `n` and `m` only (see `MinCostFlow/LowStretch/Reduce.lean`). This file
shows that they fit the pair graph of every graph that the statement allows (`fit`), and that the
first cluster is connected (`root_conn`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open MinCostFlow.Cited

/-- `⌊log₂(n + 2)⌋ + 1`. -/
def pa (n : ℕ) : ℕ := Nat.log 2 (n + 2) + 1

/-- The number of buckets: `⌊log₂(2a + 2)⌋ + 1`. -/
def pL (n : ℕ) : ℕ := Nat.log 2 (2 * pa n + 2) + 1

/-- The reset constant. -/
def pB (n : ℕ) : ℕ := 4 * pL n * (2 ^ pL n + 3)

/-- The volume of an empty petal. -/
def pκ (n m : ℕ) : ℕ := m / n ^ 2 + 1

/-- The constants. -/
def par (n m : ℕ) : Par :=
  { cw := fun _ => 1, κ := pκ n m, L := pL n, B := pB n, Q := 512 * pB n * n ^ 2 }

/-- The shift of the weights: `2^σ > 8 B n`. -/
def pσ (n : ℕ) : ℕ := Nat.log 2 (8 * pB n * n) + 1

/-- The pair graph of a weighted graph. -/
def pgOf (G : WGraph) : PG := toPG G (pσ G.n)

theorem pL_pos (n : ℕ) : 1 ≤ pL n := by unfold pL; omega

theorem pB_pos (n : ℕ) : 1 ≤ pB n := by
  unfold pB
  have := pL_pos n
  exact Nat.one_le_iff_ne_zero.mpr (by positivity)

theorem lam0_eq (n m : ℕ) : Cl.lam (par n m) 0 = 2 ^ pL n := by
  simp [Cl.lam, par]

/-- `(n + 2)² ≤ 2^(2^L)`. -/
theorem sq_le_pow (n : ℕ) : (n + 2) ^ 2 ≤ 2 ^ 2 ^ pL n := by
  have h1 : n + 2 < 2 ^ pa n := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : 2 * pa n + 2 < 2 ^ pL n := Nat.lt_pow_succ_log_self (by norm_num) _
  calc (n + 2) ^ 2 ≤ (2 ^ pa n) ^ 2 := Nat.pow_le_pow_left h1.le 2
    _ = 2 ^ (2 * pa n) := by rw [← pow_mul, mul_comm]
    _ ≤ 2 ^ 2 ^ pL n := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem Vmax_eq (G : PG) (n m : ℕ) :
    Vmax G (par n m) = (G.n + 1) * (pκ n m : ℝ) + G.m := by
  simp [Vmax, par]

/-- **The constants fit** the pair graph of every graph that the statement allows. -/
theorem fit {G : WGraph} (hV : G.graph.IsValid) (hL : G.graph.IsLoopless) (hn : 1 ≤ G.n) :
    (par G.n G.m).Fit (pgOf G) := by
  have hσ : 1 ≤ pσ G.n := by unfold pσ; omega
  refine ⟨toPG.ok hV hL hσ, pB_pos _, by simp [par, pκ], pL_pos _, ?_, ?_, ?_, ?_⟩
  · rw [lam0_eq]; simp only [par, pB]; ring_nf; exact le_rfl
  · rw [Vmax_eq, lam0_eq]
    simp only [pgOf, toPG.n_eq, toPG.m_eq, par]
    have hn2 : 0 < G.n ^ 2 := by positivity
    have hm : G.m < G.n ^ 2 * pκ G.n G.m := by
      unfold pκ; exact Nat.lt_mul_div_succ _ hn2
    have key : (G.n + 1) * pκ G.n G.m + G.m ≤ 2 ^ 2 ^ pL G.n * pκ G.n G.m := by
      have h1 := sq_le_pow G.n
      have h2 : (G.n + 1) * pκ G.n G.m + G.n ^ 2 * pκ G.n G.m ≤ (G.n + 2) ^ 2 * pκ G.n G.m := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by nlinarith)
      have h3 := Nat.mul_le_mul_right (pκ G.n G.m) h1
      omega
    exact_mod_cast key
  · intro p hp
    have hp' : p < G.m := by simpa [pgOf] using hp
    simp only [pgOf, toPG.n_eq, par]
    rw [toPG.pω_eq hp']
    have h1 : 8 * pB G.n * G.n < 2 ^ pσ G.n := Nat.lt_pow_succ_log_self (by norm_num) _
    exact h1.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  · simp [par, pgOf]

/-- The first cluster of a connected graph is connected. -/
theorem root_conn {G : WGraph} (hV : G.graph.IsValid) (hc : G.IsConnected) :
    (root (pgOf G) 1).Conn (pgOf G) := by
  refine ⟨by simp [root, pgOf, hc.1], fun y hy => ?_⟩
  have hy' : y < G.n := by simpa [root, pgOf] using hy
  obtain ⟨es, hes⟩ := hc.2 0 hc.1 y hy'
  exact ⟨es, (toPG.walk_of hV hes hy').mono (le_refl _) (Set.subset_univ _)⟩

end MinCostFlow.LowStretch
