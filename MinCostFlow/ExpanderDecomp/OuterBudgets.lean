module

public import MinCostFlow.ExpanderDecomp.OuterSubgraph
public import MinCostFlow.ExpanderDecomp.Params
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cut budgets, child shrinking, and recursion depth

This file proves the pure-integer accounting and depth-halving lemmas for the outer expander
decomposition:

* **Cut-outcome potential**: `cutPotential`, `cutPotential_mono`,
  `cutPotential_step`, and `cutPotential_le_mul_ell`.
* **Child edge shrinking**: `edge_shrink_cut` and
  `edge_shrink_witness`.
* **Integer halving and depth bound**: `two_mul_pred_pow_le_pow`,
  `halving_bound_of_pow`, and `shrink_zero_at_depth`.
* **Combined crossing-edge budget**: `combined_cut_budget`, combining the cut-outcome and
  witness-outcome budgets into `∑_X cut_G(X) ≤ (1 / E) · vol(G)`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- Logarithmic charging potential `e · (⌊log₂ e⌋ + 1)` (with `0` at `e = 0`) for the cut-outcome budget. -/
def cutPotential (e : ℕ) : ℕ :=
  if e = 0 then 0 else e * (Nat.log 2 e + 1)

/-- Number of edges of `G.inside X` not contained in any single part of `parts`. -/
def crossingCount (G : Graph) (X : Finset ℕ) (parts : List (Finset ℕ)) : ℕ :=
  ((G.inside X).filter fun ed => decide (∀ P ∈ parts, ¬ (ed.1 ∈ P ∧ ed.2 ∈ P))).length

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Logarithmic cut-budget potential -/

/-- `cutPotential` is monotone. -/
theorem cutPotential_mono {e₁ e₂ : ℕ} (h : e₁ ≤ e₂) :
    cutPotential e₁ ≤ cutPotential e₂ := by
  unfold cutPotential
  by_cases h1 : e₁ = 0
  · simp [h1]
  · have h2 : e₂ ≠ 0 := by omega
    simp only [h1, h2, ↓reduceIte]
    exact Nat.mul_le_mul h (Nat.add_le_add_right (Nat.log_mono_right h) 1)

private theorem cutPotential_drop {e e₁ e₂ c : ℕ} (hsum : e₁ + e₂ + c = e)
    (hhalf : 2 * e₁ ≤ e) :
    cutPotential e₁ + cutPotential e₂ + e₁ + c ≤ cutPotential e := by
  by_cases he : e = 0
  · have h1 : e₁ = 0 := by omega
    have h2 : e₂ = 0 := by omega
    have hc : c = 0 := by omega
    simp [cutPotential, he, h1, h2, hc]
  · have hpe : cutPotential e = e * (Nat.log 2 e + 1) := by simp [cutPotential, he]
    have h1 : cutPotential e₁ + e₁ ≤ e₁ * (Nat.log 2 e + 1) := by
      by_cases he1 : e₁ = 0
      · simp [cutPotential, he1]
      · have hpe1 : cutPotential e₁ = e₁ * (Nat.log 2 e₁ + 1) := by simp [cutPotential, he1]
        have hlog : Nat.log 2 e₁ + 1 ≤ Nat.log 2 e := by
          have hmul : Nat.log 2 (e₁ * 2) = Nat.log 2 e₁ + 1 :=
            Nat.log_mul_base (by decide) he1
          rw [← hmul]
          exact Nat.log_mono_right (by omega)
        rw [hpe1]
        have hrew : e₁ * (Nat.log 2 e₁ + 1) + e₁ = e₁ * (Nat.log 2 e₁ + 2) := by ring
        rw [hrew]
        exact Nat.mul_le_mul_left e₁ (by omega)
    have h2 : cutPotential e₂ ≤ e₂ * (Nat.log 2 e + 1) := by
      by_cases he2 : e₂ = 0
      · simp [cutPotential, he2]
      · have hpe2 : cutPotential e₂ = e₂ * (Nat.log 2 e₂ + 1) := by simp [cutPotential, he2]
        rw [hpe2]
        exact Nat.mul_le_mul_left e₂ (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1)
    have h3 : c ≤ c * (Nat.log 2 e + 1) := by
      calc c = c * 1 := (mul_one c).symm
        _ ≤ c * (Nat.log 2 e + 1) := Nat.mul_le_mul_left c (by omega)
    have hdist : e * (Nat.log 2 e + 1) =
        e₁ * (Nat.log 2 e + 1) + e₂ * (Nat.log 2 e + 1) + c * (Nat.log 2 e + 1) := by
      calc e * (Nat.log 2 e + 1) = (e₁ + e₂ + c) * (Nat.log 2 e + 1) := by rw [hsum]
        _ = e₁ * (Nat.log 2 e + 1) + e₂ * (Nat.log 2 e + 1) + c * (Nat.log 2 e + 1) := by ring
    rw [hpe, hdist]
    omega

/-- **Cut-outcome charging step**: at any rounded-cut node splitting `X` into `(S, X \ S)` with
`b · |∂_{G[X]} S| ≤ κ · min(vol_{G[X]}(S), vol_{G[X]}(X \ S))`, the cut boundary is paid by the
potential drop: `b · cut + 2κ · Φ(e_S) + 2κ · Φ(e_{X\S}) ≤ 2κ · Φ(e_X)`. -/
theorem cutPotential_step (G : Graph) {X S : Finset ℕ} (hSX : S ⊆ X) {b κ : ℕ}
    (hcut : b * G.cutIn X S ≤ κ * min (G.volIn X S) (G.volIn X (X \ S))) :
    b * G.cutIn X S + 2 * κ * cutPotential (G.inside S).length +
        2 * κ * cutPotential (G.inside (X \ S)).length ≤
      2 * κ * cutPotential (G.inside X).length := by
  set e := (G.inside X).length
  set eS := (G.inside S).length
  set eT := (G.inside (X \ S)).length
  set c := G.cutIn X S
  have hsplit : eS + eT + c = e := inside_length_split G hSX
  have hvS : G.volIn X S = 2 * eS + c := volIn_eq_two_mul_inside_add_cutIn G hSX
  have hvT : G.volIn X (X \ S) = 2 * eT + c := by
    have h := volIn_eq_two_mul_inside_add_cutIn G (Finset.sdiff_subset (s := X) (t := S))
    rwa [cutIn_sdiff G X S hSX] at h
  rcases le_total eS eT with hle | hle
  · have hmin : min (G.volIn X S) (G.volIn X (X \ S)) = 2 * eS + c := by
      rw [hvS, hvT, min_eq_left (by omega)]
    have hdrop := cutPotential_drop hsplit (by omega : 2 * eS ≤ e)
    have hbc : b * c ≤ 2 * κ * (eS + c) := by
      rw [hmin] at hcut
      calc b * c ≤ κ * (2 * eS + c) := hcut
        _ ≤ κ * (2 * (eS + c)) := Nat.mul_le_mul_left κ (by omega)
        _ = 2 * κ * (eS + c) := by ring
    have hmul : 2 * κ * (cutPotential eS + cutPotential eT + eS + c) ≤ 2 * κ * cutPotential e :=
      Nat.mul_le_mul_left (2 * κ) hdrop
    have hdist : 2 * κ * (cutPotential eS + cutPotential eT + eS + c) =
        2 * κ * (eS + c) + 2 * κ * cutPotential eS + 2 * κ * cutPotential eT := by ring
    omega
  · have hmin : min (G.volIn X S) (G.volIn X (X \ S)) = 2 * eT + c := by
      rw [hvS, hvT, min_eq_right (by omega)]
    have hsplit' : eT + eS + c = e := by omega
    have hdrop := cutPotential_drop hsplit' (by omega : 2 * eT ≤ e)
    have hbc : b * c ≤ 2 * κ * (eT + c) := by
      rw [hmin] at hcut
      calc b * c ≤ κ * (2 * eT + c) := hcut
        _ ≤ κ * (2 * (eT + c)) := Nat.mul_le_mul_left κ (by omega)
        _ = 2 * κ * (eT + c) := by ring
    have hmul : 2 * κ * (cutPotential eT + cutPotential eS + eT + c) ≤ 2 * κ * cutPotential e :=
      Nat.mul_le_mul_left (2 * κ) hdrop
    have hdist : 2 * κ * (cutPotential eT + cutPotential eS + eT + c) =
        2 * κ * (eT + c) + 2 * κ * cutPotential eS + 2 * κ * cutPotential eT := by ring
    omega

/-- Bound at the root: `cutPotential M ≤ M * (ell M + 1)`. -/
theorem cutPotential_le_mul_ell (M : ℕ) : cutPotential M ≤ M * (ell M + 1) := by
  unfold cutPotential
  by_cases hM : M = 0
  · simp [hM]
  · simp only [hM, ↓reduceIte]
    have hlog : Nat.log 2 M < ell M := by
      unfold ell
      by_contra hge
      have hle : Nat.clog 2 (2 * M + 2) ≤ Nat.log 2 M := by omega
      have h1 : 2 * M + 2 ≤ 2 ^ Nat.clog 2 (2 * M + 2) :=
        Nat.le_pow_clog (by decide) (2 * M + 2)
      have h2 : 2 ^ Nat.clog 2 (2 * M + 2) ≤ 2 ^ Nat.log 2 M :=
        Nat.pow_le_pow_right (by decide) hle
      have h3 : 2 ^ Nat.log 2 M ≤ M := Nat.pow_log_le_self 2 hM
      omega
    exact Nat.mul_le_mul_left M (by omega)

/-! ### Child shrinking, halving, and recursion depth -/

/-- **Child shrinking, cut outcome**: at a nonterminal cut node with `e > 2 D`,
`z = e / D`, port cut sides at least `z / 2`, and rounded volumes at least half the port sides,
both induced children have at most `e * (1 - 1 / (16 D))` edges (and strictly fewer than `e`). -/
theorem edge_shrink_cut (G : Graph) {X S : Finset ℕ} (hSX : S ⊆ X) {D u₁ u₂ : ℕ}
    (hD : 1 ≤ D) (he : 2 * D < (G.inside X).length)
    (hu₁ : (G.inside X).length / D ≤ 2 * u₁) (hu₂ : (G.inside X).length / D ≤ 2 * u₂)
    (hv₁ : u₁ ≤ 2 * G.volIn X S) (hv₂ : u₂ ≤ 2 * G.volIn X (X \ S)) :
    16 * D * (G.inside S).length ≤ (16 * D - 1) * (G.inside X).length ∧
      16 * D * (G.inside (X \ S)).length ≤ (16 * D - 1) * (G.inside X).length ∧
      (G.inside S).length < (G.inside X).length ∧
      (G.inside (X \ S)).length < (G.inside X).length := by
  set e := (G.inside X).length
  set z := e / D
  have hz_pos : 2 ≤ z := by
    have : 2 * D ≤ e := by omega
    exact (Nat.le_div_iff_mul_le (by omega)).mpr this
  have he_le : e ≤ 2 * D * z := by
    have hdiv : D * z + e % D = e := Nat.div_add_mod e D
    have hmod : e % D < D := Nat.mod_lt e (by omega : 0 < D)
    have hstep : D * z + D ≤ 2 * D * z := by
      have : 1 ≤ z := by omega
      nlinarith
    omega
  have hvS_lb : e ≤ 8 * D * G.volIn X S := by
    have h1 : z ≤ 4 * G.volIn X S := by omega
    calc e ≤ 2 * D * z := he_le
      _ ≤ 2 * D * (4 * G.volIn X S) := Nat.mul_le_mul_left _ h1
      _ = 8 * D * G.volIn X S := by ring
  have hvT_lb : e ≤ 8 * D * G.volIn X (X \ S) := by
    have h1 : z ≤ 4 * G.volIn X (X \ S) := by omega
    calc e ≤ 2 * D * z := he_le
      _ ≤ 2 * D * (4 * G.volIn X (X \ S)) := Nat.mul_le_mul_left _ h1
      _ = 8 * D * G.volIn X (X \ S) := by ring
  have hvsum : G.volIn X S + G.volIn X (X \ S) = 2 * e := volIn_add_volIn_sdiff G X S hSX
  have heS : 2 * (G.inside S).length ≤ G.volIn X S := two_mul_inside_le_volIn G hSX
  have heT : 2 * (G.inside (X \ S)).length ≤ G.volIn X (X \ S) :=
    two_mul_inside_le_volIn G Finset.sdiff_subset
  have h16D_eq : (16 * D - 1) * e + e = 16 * D * e := by
    have : 1 ≤ 16 * D := by omega
    calc (16 * D - 1) * e + e = (16 * D - 1 + 1) * e := by ring
      _ = 16 * D * e := by rw [Nat.sub_add_cancel this]
  have hvol16 : 8 * D * G.volIn X S + 8 * D * G.volIn X (X \ S) = 16 * D * e := by
    calc 8 * D * G.volIn X S + 8 * D * G.volIn X (X \ S)
        = 8 * D * (G.volIn X S + G.volIn X (X \ S)) := by ring
      _ = 8 * D * (2 * e) := by rw [hvsum]
      _ = 16 * D * e := by ring
  have h16D : 16 * D * (G.inside S).length ≤ (16 * D - 1) * e := by
    have h1 : 16 * D * (G.inside S).length ≤ 8 * D * G.volIn X S := by
      have : 16 * D * (G.inside S).length = 8 * D * (2 * (G.inside S).length) := by ring
      rw [this]
      exact Nat.mul_le_mul_left _ heS
    omega
  have h16D' : 16 * D * (G.inside (X \ S)).length ≤ (16 * D - 1) * e := by
    have h1 : 16 * D * (G.inside (X \ S)).length ≤ 8 * D * G.volIn X (X \ S) := by
      have : 16 * D * (G.inside (X \ S)).length = 8 * D * (2 * (G.inside (X \ S)).length) := by ring
      rw [this]
      exact Nat.mul_le_mul_left _ heT
    omega
  have hlt1 : (G.inside S).length < e :=
    Nat.lt_of_mul_lt_mul_left (a := 16 * D) (by omega)
  have hlt2 : (G.inside (X \ S)).length < e :=
    Nat.lt_of_mul_lt_mul_left (a := 16 * D) (by omega)
  exact ⟨h16D, h16D', hlt1, hlt2⟩

/-- **Child shrinking, witness outcome**: if `R ⊆ X` satisfies
`16 * b_out * vol_{G[X]}(X \ R) ≤ e` with `1 ≤ b_out`, `1 ≤ D`, and `1 ≤ e`, then:
1. `32 * b_out * |E(G[X \ R])| ≤ e` and `16 * D * |E(G[X \ R])| ≤ (16 * D - 1) * e`, `< e`;
2. `15 * e ≤ 16 * |E(G[R])|`;
3. `16 * b_out * |∂_{G[X]} R| ≤ e`. -/
theorem edge_shrink_witness (G : Graph) {X R : Finset ℕ} (hRX : R ⊆ X) {bOut D : ℕ}
    (hb : 1 ≤ bOut) (hD : 1 ≤ D) (he : 1 ≤ (G.inside X).length)
    (hvol : 16 * bOut * G.volIn X (X \ R) ≤ (G.inside X).length) :
    32 * bOut * (G.inside (X \ R)).length ≤ (G.inside X).length ∧
      16 * D * (G.inside (X \ R)).length ≤ (16 * D - 1) * (G.inside X).length ∧
      (G.inside (X \ R)).length < (G.inside X).length ∧
      15 * (G.inside X).length ≤ 16 * (G.inside R).length ∧
      16 * bOut * G.cutIn X R ≤ (G.inside X).length := by
  set e := (G.inside X).length
  have h1 : 2 * (G.inside (X \ R)).length ≤ G.volIn X (X \ R) :=
    two_mul_inside_le_volIn G Finset.sdiff_subset
  have h32 : 32 * bOut * (G.inside (X \ R)).length ≤ e := by
    calc 32 * bOut * (G.inside (X \ R)).length
        = 16 * bOut * (2 * (G.inside (X \ R)).length) := by ring
      _ ≤ 16 * bOut * G.volIn X (X \ R) := Nat.mul_le_mul_left _ h1
      _ ≤ e := hvol
  have h32_plain : 32 * (G.inside (X \ R)).length ≤ e := by
    have : 32 * (G.inside (X \ R)).length ≤ 32 * bOut * (G.inside (X \ R)).length := by
      have : 32 * 1 ≤ 32 * bOut := Nat.mul_le_mul_left 32 hb
      calc 32 * (G.inside (X \ R)).length = (32 * 1) * (G.inside (X \ R)).length := by ring
        _ ≤ (32 * bOut) * (G.inside (X \ R)).length := Nat.mul_le_mul_right _ this
    omega
  have h16D : 16 * D * (G.inside (X \ R)).length ≤ (16 * D - 1) * e := by
    have hD2 : 16 * D ≤ 32 * (16 * D - 1) := by omega
    have hmul : 32 * (16 * D * (G.inside (X \ R)).length) ≤ 32 * ((16 * D - 1) * e) := by
      calc 32 * (16 * D * (G.inside (X \ R)).length)
          = (16 * D) * (32 * (G.inside (X \ R)).length) := by ring
        _ ≤ (16 * D) * e := Nat.mul_le_mul_left _ h32_plain
        _ ≤ (32 * (16 * D - 1)) * e := Nat.mul_le_mul_right e hD2
        _ = 32 * ((16 * D - 1) * e) := by ring
    exact Nat.le_of_mul_le_mul_left hmul (by decide)
  have hlt : (G.inside (X \ R)).length < e := by omega
  have hret : 15 * e ≤ 16 * (G.inside R).length := by
    have hdiff := inside_diff_le_volIn G hRX
    have hv16 : 16 * G.volIn X (X \ R) ≤ e := by
      have : 16 * 1 * G.volIn X (X \ R) ≤ 16 * bOut * G.volIn X (X \ R) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 16 hb)
      omega
    omega
  have hcut : 16 * bOut * G.cutIn X R ≤ e := by
    have hcv : G.cutIn X R ≤ G.volIn X (X \ R) := by
      rw [← cutIn_sdiff G X R hRX]
      exact cutIn_le_volIn G X (X \ R)
    exact le_trans (Nat.mul_le_mul_left _ hcv) hvol
  exact ⟨h32, h16D, hlt, hret, hcut⟩

private theorem add_mul_pow_le_mul_succ_pow {a : ℕ} (n : ℕ) :
    (a + n) * a ^ n ≤ a * (a + 1) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : (a + 1) * ((a + k) * a ^ k) ≤ (a + 1) * (a * (a + 1) ^ k) :=
      Nat.mul_le_mul_left (a + 1) ih
    have h2 : (a + (k + 1)) * a ^ (k + 1) ≤ (a + 1) * ((a + k) * a ^ k) := by
      have hring1 : (a + (k + 1)) * a ^ (k + 1) = (a ^ 2 + (k + 1) * a) * a ^ k := by
        rw [Nat.pow_succ]; ring
      have hring2 : (a + 1) * ((a + k) * a ^ k) = (a ^ 2 + (k + 1) * a + k) * a ^ k := by ring
      rw [hring1, hring2]
      exact Nat.mul_le_mul_right _ (by omega)
    have h3 : (a + 1) * (a * (a + 1) ^ k) = a * (a + 1) ^ (k + 1) := by
      rw [Nat.pow_succ]; ring
    omega

/-- Integer halving inequality: for `K ≥ 2`, `2 * (K - 1)^K ≤ K^K`. -/
theorem two_mul_pred_pow_le_pow {K : ℕ} (hK : 2 ≤ K) :
    2 * (K - 1) ^ K ≤ K ^ K := by
  set a := K - 1
  have ha : 1 ≤ a := by omega
  have ha1 : a + 1 = K := by omega
  have h := add_mul_pow_le_mul_succ_pow (a := a) K
  rw [ha1] at h
  have h2 : a * (2 * a ^ K) ≤ (a + K) * a ^ K := by
    have : 2 * a ≤ a + K := by omega
    calc a * (2 * a ^ K) = (2 * a) * a ^ K := by ring
      _ ≤ (a + K) * a ^ K := Nat.mul_le_mul_right _ this
  exact Nat.le_of_mul_le_mul_left (le_trans h2 h) (by omega)

/-- **Halving bound**: if `K ≥ 2` and `K^(K*s) * e ≤ (K-1)^(K*s) * e₀`, then
`2^s * e ≤ e₀`. -/
theorem halving_bound_of_pow {K s e₀ e : ℕ} (hK : 2 ≤ K)
    (hpow : K ^ (K * s) * e ≤ (K - 1) ^ (K * s) * e₀) :
    2 ^ s * e ≤ e₀ := by
  have hstep : 2 ^ s * (K - 1) ^ (K * s) ≤ K ^ (K * s) := by
    rw [Nat.pow_mul, Nat.pow_mul, ← Nat.mul_pow]
    exact Nat.pow_le_pow_left (two_mul_pred_pow_le_pow hK) s
  have h1 : K ^ (K * s) * (2 ^ s * e) ≤ K ^ (K * s) * e₀ := by
    calc K ^ (K * s) * (2 ^ s * e)
        = 2 ^ s * (K ^ (K * s) * e) := by ring
      _ ≤ 2 ^ s * ((K - 1) ^ (K * s) * e₀) := Nat.mul_le_mul_left _ hpow
      _ = (2 ^ s * (K - 1) ^ (K * s)) * e₀ := by ring
      _ ≤ K ^ (K * s) * e₀ := Nat.mul_le_mul_right _ hstep
  have hKpos : 0 < K ^ (K * s) := Nat.pow_pos (by omega)
  exact Nat.le_of_mul_le_mul_left h1 hKpos

/-- After `K * (ell M + 1)` shrinking steps starting from `e₀ ≤ M`, the edge count is `0`. -/
theorem shrink_zero_at_depth {K M e₀ e : ℕ} (hK : 2 ≤ K) (he₀ : e₀ ≤ M)
    (hpow : K ^ (K * (ell M + 1)) * e ≤ (K - 1) ^ (K * (ell M + 1)) * e₀) :
    e = 0 := by
  have h := halving_bound_of_pow hK hpow
  have hpow2 : 2 * M + 2 ≤ 2 ^ ell M := Nat.le_pow_clog (by decide) (2 * M + 2)
  have hpow3 : M < 2 ^ (ell M + 1) := by
    rw [Nat.pow_succ]
    omega
  by_contra hne
  have he1 : 1 ≤ e := by omega
  have : 2 ^ (ell M + 1) ≤ 2 ^ (ell M + 1) * e := Nat.le_mul_of_pos_right _ he1
  omega

/-- Combining the cut-outcome and witness-outcome budgets into `E · (cCut + cWit) ≤ M`: if `8 * E * cCut ≤ M` and
`15 * b_out * cWit ≤ M` with `E ≤ b_out`, then `E * (cCut + cWit) ≤ M`. -/
theorem combined_cut_budget {E bOut M cCut cWit : ℕ} (hEb : E ≤ bOut)
    (hcut : 8 * E * cCut ≤ M) (hwit : 15 * bOut * cWit ≤ M) :
    E * (cCut + cWit) ≤ M := by
  have hwitE : 15 * E * cWit ≤ M := by
    have : 15 * E * cWit ≤ 15 * bOut * cWit :=
      Nat.mul_le_mul_right cWit (Nat.mul_le_mul_left 15 hEb)
    omega
  have h120 : 120 * (E * (cCut + cWit)) ≤ 120 * M := by
    have hrew : 120 * (E * (cCut + cWit)) = 15 * (8 * E * cCut) + 8 * (15 * E * cWit) := by ring
    omega
  exact Nat.le_of_mul_le_mul_left h120 (by decide)

/-! ### Partition, crossing-count, and depth-recursion helpers -/

/-- Singleton parts from a nodup list of isolated vertices form pairwise disjoint nonempty
conductance expanders covering `iso.toFinset`. -/
theorem singleton_parts_spec (G : Graph) (φ : ℝ) {iso : List ℕ} (hnd : iso.Nodup) :
    let ps := iso.map fun v => ({v} : Finset ℕ)
    (∀ P ∈ ps, P.Nonempty ∧ P ⊆ iso.toFinset) ∧
      ps.Pairwise Disjoint ∧
      ps.toFinset.biUnion id = iso.toFinset ∧
      ∀ P ∈ ps, G.IsConductanceExpanderOn P φ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP
    rw [List.mem_map] at hP
    obtain ⟨v, hv, rfl⟩ := hP
    exact ⟨Finset.singleton_nonempty v, Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr hv)⟩
  · rw [List.pairwise_map]
    exact hnd.imp fun hne => Finset.disjoint_singleton.mpr hne
  · ext v
    simp only [Finset.mem_biUnion, id_eq, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, hvu⟩
      rw [Finset.mem_singleton.mp hvu]
      exact hu
    · intro hv
      exact ⟨{v}, ⟨v, hv, rfl⟩, Finset.mem_singleton_self v⟩
  · intro P hP
    rw [List.mem_map] at hP
    obtain ⟨v, _, rfl⟩ := hP
    exact isConductanceExpanderOn_of_card_le_one (by simp) φ

/-- Appending two pairwise-disjoint lists of sets whose unions are disjoint stays pairwise disjoint. -/
theorem pairwise_disjoint_append {l₁ l₂ : List (Finset ℕ)}
    (h₁ : l₁.Pairwise Disjoint) (h₂ : l₂.Pairwise Disjoint)
    (hd : Disjoint (l₁.toFinset.biUnion id) (l₂.toFinset.biUnion id)) :
    (l₁ ++ l₂).Pairwise Disjoint := by
  rw [List.pairwise_append]
  refine ⟨h₁, h₂, fun P hP Q hQ => ?_⟩
  have hPsub : P ⊆ l₁.toFinset.biUnion id :=
    Finset.subset_biUnion_of_mem id (List.mem_toFinset.mpr hP)
  have hQsub : Q ⊆ l₂.toFinset.biUnion id :=
    Finset.subset_biUnion_of_mem id (List.mem_toFinset.mpr hQ)
  exact hd.mono hPsub hQsub

/-- `biUnion id` distributes over `++`. -/
theorem biUnion_append (l₁ l₂ : List (Finset ℕ)) :
    (l₁ ++ l₂).toFinset.biUnion id = l₁.toFinset.biUnion id ∪ l₂.toFinset.biUnion id := by
  rw [List.toFinset_append, Finset.union_biUnion]

/-- Connected components cut zero edges of `G.inside X`. -/
theorem crossingCount_components_eq_zero {H : CompactSubgraph} {G : Graph} {X : Finset ℕ}
    (hH : H.Represents G X) {Q : ℕ} (hQ : 1 ≤ Q) (he : H.edges.length ≤ Q) :
    crossingCount G X H.componentsOf = 0 := by
  obtain ⟨_, _, _, hunion, _, hcut0⟩ := H.componentsOf_spec hH hQ he
  unfold crossingCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro ed hed
  rw [decide_eq_true_iff]
  push Not
  have hmem := mem_inside_iff.mp hed
  have h1 : ed.1 ∈ H.componentsOf.toFinset.biUnion id := hunion.symm ▸ hmem.2.1
  rw [Finset.mem_biUnion] at h1
  obtain ⟨C, hCmem, hed1⟩ := h1
  dsimp only [id_eq] at hed1
  rw [List.mem_toFinset] at hCmem
  refine ⟨C, hCmem, hed1, ?_⟩
  by_contra hed2
  have hpos : 0 < G.cutIn X C := by
    unfold Graph.cutIn
    apply List.length_pos_of_mem
    exact List.mem_filter.mpr ⟨hed, by simp [hed1, hed2]⟩
  have hz := hcut0 C hCmem
  omega

/-- Crossing edges across a cut split `(S, X \ S)` are bounded by `G.cutIn X S` plus the crossing
edges inside each side. -/
theorem crossingCount_split_cut (G : Graph) {X S : Finset ℕ} (hSX : S ⊆ X)
    {parts p₁ p₂ : List (Finset ℕ)}
    (hp₁ : ∀ P ∈ p₁, P ∈ parts) (hp₂ : ∀ P ∈ p₂, P ∈ parts) :
    crossingCount G X parts ≤
      G.cutIn X S + crossingCount G S p₁ + crossingCount G (X \ S) p₂ := by
  have hinsS : G.inside S = (G.inside X).filter fun e => decide (e.1 ∈ S) && decide (e.2 ∈ S) := by
    unfold Graph.inside
    rw [List.filter_filter]
    apply List.filter_congr
    intro e _
    by_cases h1 : e.1 ∈ S <;> by_cases h2 : e.2 ∈ S
    · simp [h1, h2, hSX h1, hSX h2]
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  have hinsT : G.inside (X \ S) =
      (G.inside X).filter fun e => decide (e.1 ∈ X \ S) && decide (e.2 ∈ X \ S) := by
    unfold Graph.inside
    rw [List.filter_filter]
    apply List.filter_congr
    intro e _
    by_cases h1 : e.1 ∈ X <;> by_cases h2 : e.2 ∈ X <;>
      by_cases s1 : e.1 ∈ S <;> by_cases s2 : e.2 ∈ S <;> simp [h1, h2, s1, s2]
  unfold crossingCount
  rw [hinsS, hinsT, List.filter_filter, List.filter_filter,
    cutIn_eq_sum_map, length_filter_eq_sum_map, length_filter_eq_sum_map, length_filter_eq_sum_map]
  suffices h : ∀ l : List (ℕ × ℕ), (∀ e ∈ l, e.1 ∈ X ∧ e.2 ∈ X) →
      (l.map fun ed => if decide (∀ P ∈ parts, ¬(ed.1 ∈ P ∧ ed.2 ∈ P)) then 1 else 0).sum ≤
      (l.map fun ed => if (decide (ed.1 ∈ S) != decide (ed.2 ∈ S)) then 1 else 0).sum +
      (l.map fun ed => if (decide (∀ P ∈ p₁, ¬(ed.1 ∈ P ∧ ed.2 ∈ P)) &&
        (decide (ed.1 ∈ S) && decide (ed.2 ∈ S))) then 1 else 0).sum +
      (l.map fun ed => if (decide (∀ P ∈ p₂, ¬(ed.1 ∈ P ∧ ed.2 ∈ P)) &&
        (decide (ed.1 ∈ X \ S) && decide (ed.2 ∈ X \ S))) then 1 else 0).sum from
    h (G.inside X) (fun e he => (mem_inside_iff.mp he).2)
  intro l hl
  induction l with
  | nil => simp
  | cons e t ih =>
    have he := hl e List.mem_cons_self
    have ht := ih (fun f hf => hl f (List.mem_cons_of_mem _ hf))
    simp only [List.map_cons, List.sum_cons]
    have hpt :
        (if decide (∀ P ∈ parts, ¬(e.1 ∈ P ∧ e.2 ∈ P)) then 1 else 0) ≤
        (if (decide (e.1 ∈ S) != decide (e.2 ∈ S)) then 1 else 0) +
        (if (decide (∀ P ∈ p₁, ¬(e.1 ∈ P ∧ e.2 ∈ P)) &&
          (decide (e.1 ∈ S) && decide (e.2 ∈ S))) then 1 else 0) +
        (if (decide (∀ P ∈ p₂, ¬(e.1 ∈ P ∧ e.2 ∈ P)) &&
          (decide (e.1 ∈ X \ S) && decide (e.2 ∈ X \ S))) then 1 else 0) := by
      by_cases hcr : ∀ P ∈ parts, ¬(e.1 ∈ P ∧ e.2 ∈ P)
      · have hp1 : ∀ P ∈ p₁, ¬(e.1 ∈ P ∧ e.2 ∈ P) := fun P hP => hcr P (hp₁ P hP)
        have hp2 : ∀ P ∈ p₂, ¬(e.1 ∈ P ∧ e.2 ∈ P) := fun P hP => hcr P (hp₂ P hP)
        rw [decide_eq_true hcr, decide_eq_true hp1, decide_eq_true hp2]
        by_cases s1 : e.1 ∈ S <;> by_cases s2 : e.2 ∈ S <;> simp [s1, s2, he.1, he.2]
      · rw [decide_eq_false hcr]; simp
    omega

/-- Crossing edges across a witness split `(R, X \ R)` where `R ∈ parts` are bounded by
`G.cutIn X R` plus the crossing edges inside `X \ R`. -/
theorem crossingCount_split_witness (G : Graph) {X R : Finset ℕ}
    {parts pRest : List (Finset ℕ)} (hR : R ∈ parts)
    (hpRest : ∀ P ∈ pRest, P ∈ parts) :
    crossingCount G X parts ≤ G.cutIn X R + crossingCount G (X \ R) pRest := by
  have hinsT : G.inside (X \ R) =
      (G.inside X).filter fun e => decide (e.1 ∈ X \ R) && decide (e.2 ∈ X \ R) := by
    unfold Graph.inside
    rw [List.filter_filter]
    apply List.filter_congr
    intro e _
    by_cases h1 : e.1 ∈ X <;> by_cases h2 : e.2 ∈ X <;>
      by_cases r1 : e.1 ∈ R <;> by_cases r2 : e.2 ∈ R <;> simp [h1, h2, r1, r2]
  unfold crossingCount
  rw [hinsT, List.filter_filter, cutIn_eq_sum_map, length_filter_eq_sum_map,
    length_filter_eq_sum_map]
  suffices h : ∀ l : List (ℕ × ℕ), (∀ e ∈ l, e.1 ∈ X ∧ e.2 ∈ X) →
      (l.map fun ed => if decide (∀ P ∈ parts, ¬(ed.1 ∈ P ∧ ed.2 ∈ P)) then 1 else 0).sum ≤
      (l.map fun ed => if (decide (ed.1 ∈ R) != decide (ed.2 ∈ R)) then 1 else 0).sum +
      (l.map fun ed => if (decide (∀ P ∈ pRest, ¬(ed.1 ∈ P ∧ ed.2 ∈ P)) &&
        (decide (ed.1 ∈ X \ R) && decide (ed.2 ∈ X \ R))) then 1 else 0).sum from
    h (G.inside X) (fun e he => (mem_inside_iff.mp he).2)
  intro l hl
  induction l with
  | nil => simp
  | cons e t ih =>
    have he := hl e List.mem_cons_self
    have ht := ih (fun f hf => hl f (List.mem_cons_of_mem _ hf))
    simp only [List.map_cons, List.sum_cons]
    have hpt :
        (if decide (∀ P ∈ parts, ¬(e.1 ∈ P ∧ e.2 ∈ P)) then 1 else 0) ≤
        (if (decide (e.1 ∈ R) != decide (e.2 ∈ R)) then 1 else 0) +
        (if (decide (∀ P ∈ pRest, ¬(e.1 ∈ P ∧ e.2 ∈ P)) &&
          (decide (e.1 ∈ X \ R) && decide (e.2 ∈ X \ R))) then 1 else 0) := by
      by_cases hcr : ∀ P ∈ parts, ¬(e.1 ∈ P ∧ e.2 ∈ P)
      · have hpR : ∀ P ∈ pRest, ¬(e.1 ∈ P ∧ e.2 ∈ P) := fun P hP => hcr P (hpRest P hP)
        have hnotBoth : ¬ (e.1 ∈ R ∧ e.2 ∈ R) := hcr R hR
        rw [decide_eq_true hcr, decide_eq_true hpR]
        by_cases r1 : e.1 ∈ R <;> by_cases r2 : e.2 ∈ R
        · exact absurd ⟨r1, r2⟩ hnotBoth
        · simp [r1, r2, he.1, he.2]
        · simp [r1, r2, he.1, he.2]
        · simp [r1, r2, he.1, he.2]
      · rw [decide_eq_false hcr]; simp
    omega

/-- `crossingCount` depends only on `G.inside X`. -/
theorem crossingCount_congr_inside {G : Graph} {X Y : Finset ℕ}
    (h : G.inside X = G.inside Y) (parts : List (Finset ℕ)) :
    crossingCount G X parts = crossingCount G Y parts := by
  unfold crossingCount; rw [h]

/-- Inductive shrinking step for recursion depth: if `K * e₁ ≤ (K - 1) * e`, `1 ≤ e`, and
`1 ≤ d → K^(d-1) ≤ (K-1)^(d-1) * e₁`, then `K^d ≤ (K-1)^d * e`. -/
theorem pow_le_of_step {K d e₁ e : ℕ} (h1 : K * e₁ ≤ (K - 1) * e)
    (he : 1 ≤ e) (hd : 1 ≤ d → K ^ (d - 1) ≤ (K - 1) ^ (d - 1) * e₁) :
    K ^ d ≤ (K - 1) ^ d * e := by
  cases d with
  | zero => simpa using he
  | succ k =>
    have hk := hd (by omega)
    simp only [Nat.add_sub_cancel] at hk
    calc K ^ (k + 1) = K * K ^ k := by rw [Nat.pow_succ]; ring
      _ ≤ K * ((K - 1) ^ k * e₁) := Nat.mul_le_mul_left K hk
      _ = (K - 1) ^ k * (K * e₁) := by ring
      _ ≤ (K - 1) ^ k * ((K - 1) * e) := Nat.mul_le_mul_left _ h1
      _ = (K - 1) ^ (k + 1) * e := by rw [Nat.pow_succ]; ring

/-- Converts the power shrinking invariant into the explicit depth bound `d ≤ K * (ell M + 1)`. -/
theorem depth_le_of_pow {K M e d : ℕ} (hK : 2 ≤ K) (heM : e ≤ M)
    (hpow : 1 ≤ d → K ^ (d - 1) ≤ (K - 1) ^ (d - 1) * e) :
    d ≤ K * (ell M + 1) := by
  by_contra hgt
  have hd1 : 1 ≤ d := by omega
  have hge : K * (ell M + 1) ≤ d - 1 := by omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hge
  have hp := hpow hd1
  rw [ht, Nat.pow_add, Nat.pow_add] at hp
  have ht_le : (K - 1) ^ t ≤ K ^ t := Nat.pow_le_pow_left (by omega) t
  have h1 : K ^ t * (K ^ (K * (ell M + 1)) * 1) ≤ K ^ t * ((K - 1) ^ (K * (ell M + 1)) * e) := by
    calc K ^ t * (K ^ (K * (ell M + 1)) * 1) = K ^ (K * (ell M + 1)) * K ^ t := by ring
      _ ≤ (K - 1) ^ (K * (ell M + 1)) * (K - 1) ^ t * e := hp
      _ = (K - 1) ^ t * ((K - 1) ^ (K * (ell M + 1)) * e) := by ring
      _ ≤ K ^ t * ((K - 1) ^ (K * (ell M + 1)) * e) := Nat.mul_le_mul_right _ ht_le
  have hKpos : 0 < K ^ t := Nat.pow_pos (by omega)
  have h2 := Nat.le_of_mul_le_mul_left h1 hKpos
  have hz := shrink_zero_at_depth hK heM h2
  omega

end MinCostFlow.ExpanderDecomp
