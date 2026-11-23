module

public import MinCostFlow.Statement.Cited.Graphs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MinCostFlow.ExpanderDecomp.Injection
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Round bound for the cut-matching game

This file proves the round bound for the deterministic cut-matching game, with the
constant `70`.

Each round `k` applies a fixed-point-free involution `σ k` on a finite vertex set `V` of size `p`.
We track the pair-averaged probability mass `mass σ k v u` starting from the identity distribution,
and its total entropy `entropy V σ k = ∑ v ∈ V, ∑ u ∈ V, negMulLog (mass σ k v u)`.
* Initially `entropy V σ 0 = 0`, and at every step `entropy V σ k ≤ p * Real.log p`.
* In a round `k` with a cut `C ⊆ V` satisfying `4 * |C| ≥ p`, `σ k (C) ∩ C = ∅`, and at most
  `p / 100` crossing matching pairs from rounds `j < k`, the entropy increases by at least
  `p / 70`.

Hence a game of `T` such rounds satisfies `T ≤ 70 * Real.log p`, so `T < 70 * Real.log p + 1` and
`T < 49 * L + 1` whenever `p < 2 ^ L`.

We also define perfect matchings as edge lists (`IsPerfectMatchingOn`), extract their involution
(`mate`), prove the bridging lemma identifying `crossCount` with `cutIn` of the witness graph built
by appending the round edge lists (`witnessEdges`), and state the round bound directly in terms of
witness-graph cuts for use in `OneShot`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-- A fixed-point-free involution on `V`: a perfect matching given as a map. -/
def IsInvolutionMatching (V : Finset ℕ) (σ : ℕ → ℕ) : Prop :=
  (∀ u ∈ V, σ u ∈ V) ∧ (∀ u ∈ V, σ (σ u) = u) ∧ (∀ u ∈ V, σ u ≠ u)

/-- The number of pairs from rounds `j < k` that cross `C` (one end in `V \ C`, one end in `C`). -/
def crossCount (V : Finset ℕ) (σ : ℕ → ℕ → ℕ) (k : ℕ) (C : Finset ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, ((V \ C).filter fun u => σ j u ∈ C).card

/-- An edge list `E` is a perfect matching on `V`: all ends lie in `V`, no vertex appears twice as
an endpoint, and every vertex of `V` is incident to an edge of `E`. -/
def IsPerfectMatchingOn (V : Finset ℕ) (E : List (ℕ × ℕ)) : Prop :=
  (∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) ∧
    (E.flatMap fun e => [e.1, e.2]).Nodup ∧
    ∀ u ∈ V, ∃ e ∈ E, e.1 = u ∨ e.2 = u

/-- The partner of `u` in an edge list `E` (or `u` itself if `u` does not appear in `E`). -/
def mate : List (ℕ × ℕ) → ℕ → ℕ
  | [], u => u
  | (a, b) :: rest, u => if a = u then b else if b = u then a else mate rest u

/-- The witness edge list after `k` rounds, formed by appending the round matchings `M 0, …, M (k-1)`. -/
def witnessEdges (M : ℕ → List (ℕ × ℕ)) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | k + 1 => witnessEdges M k ++ M k

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Logarithmic and pair-gain inequalities -/

/-- For `z ≥ 1`, `2 * (z - 1) / (z + 1) ≤ Real.log z`, from the odd power series of
`log (1 + t) - log (1 - t)` at `t = (z - 1) / (z + 1)`. -/
private lemma two_mul_sub_div_add_le_log {z : ℝ} (hz : 1 ≤ z) :
    2 * (z - 1) / (z + 1) ≤ Real.log z := by
  have hzpos : 0 < z := by linarith
  have hz1 : 0 < z + 1 := by linarith
  set t : ℝ := (z - 1) / (z + 1)
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hz1.le
  have ht1 : t < 1 := (div_lt_one hz1).mpr (by linarith)
  have habs : |t| < 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have hhs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hlog : Real.log (1 + t) - Real.log (1 - t) = Real.log z := by
    have h1p : 1 + t = 2 * z / (z + 1) := by
      dsimp only [t]; field_simp; ring
    have h1m : 1 - t = 2 / (z + 1) := by
      dsimp only [t]; field_simp; ring
    rw [h1p, h1m, ← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [hlog] at hhs
  have hle := le_hasSum hhs 0 fun k _ => by positivity
  simp only [Nat.cast_zero, mul_zero, zero_add, div_one, pow_one, mul_one] at hle
  simpa only [t, mul_div_assoc] using hle

/-- The entropy gain of averaging a pair `(x, y)` of nonnegative masses. -/
private noncomputable def pairGain (x y : ℝ) : ℝ :=
  2 * Real.negMulLog ((x + y) / 2) - Real.negMulLog x - Real.negMulLog y

private lemma pairGain_symm (x y : ℝ) : pairGain x y = pairGain y x := by
  unfold pairGain
  rw [add_comm x y]
  ring

/-- Core lower bound on `pairGain x y` when `0 ≤ y ≤ x` and `0 < x`. -/
private lemma pairGain_ge_sq_div {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hyx : y ≤ x) :
    (x - y) ^ 2 / (2 * (3 * x + y)) ≤ pairGain x y := by
  rcases eq_or_lt_of_le hy with rfl | hypos
  · unfold pairGain Real.negMulLog
    simp only [add_zero, neg_zero, zero_mul, sub_zero]
    have hlog2 : (2 : ℝ) / 3 ≤ Real.log 2 := by
      have h := two_mul_sub_div_add_le_log (z := 2) (by norm_num)
      norm_num at h
      exact h
    have hrew : 2 * (-(x / 2) * Real.log (x / 2)) - -x * Real.log x = x * Real.log 2 := by
      rw [Real.log_div hx.ne' (by norm_num)]
      ring
    rw [hrew]
    have hden : x ^ 2 / (2 * (3 * x)) = x / 6 := by
      field_simp
      ring
    rw [hden]
    nlinarith
  · set m : ℝ := (x + y) / 2
    have hm : 0 < m := by dsimp only [m]; linarith
    have hgain : pairGain x y = x * Real.log (x / m) + y * Real.log (y / m) := by
      unfold pairGain Real.negMulLog
      rw [Real.log_div hx.ne' hm.ne', Real.log_div hypos.ne' hm.ne']
      dsimp only [m]
      ring
    rw [hgain]
    have hxm : 1 ≤ x / m := (one_le_div hm).mpr (by dsimp only [m]; linarith)
    have h1 : 2 * x * (x - y) / (3 * x + y) ≤ x * Real.log (x / m) := by
      have hlog := two_mul_sub_div_add_le_log hxm
      have hrat : 2 * (x / m - 1) / (x / m + 1) = 2 * (x - y) / (3 * x + y) := by
        dsimp only [m]
        have h3 : 3 * x + y ≠ 0 := by linarith
        have hxy : x + y ≠ 0 := by linarith
        field_simp
        ring
      rw [hrat] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hx.le
      calc 2 * x * (x - y) / (3 * x + y) = x * (2 * (x - y) / (3 * x + y)) := by ring
        _ ≤ x * Real.log (x / m) := hmul
    have h2 : -((x - y) / 2) ≤ y * Real.log (y / m) := by
      have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hypos hm)
      have hmul := mul_le_mul_of_nonneg_left hlog hypos.le
      have hlhs : y * (1 - (y / m)⁻¹) = -((x - y) / 2) := by
        dsimp only [m]
        field_simp
        ring
      linarith
    have hcomb : (x - y) ^ 2 / (2 * (3 * x + y)) = 2 * x * (x - y) / (3 * x + y) - (x - y) / 2 := by
      have h3 : 3 * x + y ≠ 0 := by linarith
      field_simp
      ring
    linarith

private lemma pairGain_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ pairGain x y := by
  wlog hyx : y ≤ x generalizing x y
  · rw [pairGain_symm]
    exact this hy hx (le_of_not_ge hyx)
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · have hy0 : y = 0 := le_antisymm hyx hy
    subst hy0
    simp [pairGain]
  · exact le_trans (div_nonneg (sq_nonneg _) (by linarith)) (pairGain_ge_sq_div hxpos hy hyx)

/-- Key linear lower bound: `x / 8 - y / 4 ≤ pairGain x y` for all `x, y ≥ 0`. -/
private lemma pairGain_ge_linear {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x / 8 - y / 4 ≤ pairGain x y := by
  by_cases hyx : y ≤ x
  · rcases eq_or_lt_of_le hx with rfl | hxpos
    · have hy0 : y = 0 := le_antisymm hyx hy
      subst hy0
      simp [pairGain]
    · have h1 := pairGain_ge_sq_div hxpos hy hyx
      have h3 : 0 < 3 * x + y := by linarith
      have h2 : x / 8 - y / 4 ≤ (x - y) ^ 2 / (2 * (3 * x + y)) := by
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (3 * x + y))]
        have hsq : 0 ≤ (x - 3 / 2 * y) ^ 2 + 15 / 4 * y ^ 2 := by positivity
        nlinarith
      exact le_trans h2 h1
  · have hneg : x / 8 - y / 4 ≤ 0 := by linarith
    exact le_trans hneg (pairGain_nonneg hx hy)

/-- Pointwise bound used for the row entropy upper bound `≤ log p`. -/
private lemma negMulLog_le_linear {p x : ℝ} (hp : 0 < p) (hx : 0 ≤ x) :
    Real.negMulLog x ≤ x * Real.log p + 1 / p - x := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp only [Real.negMulLog_zero, zero_mul, zero_add, sub_zero]
    positivity
  · have hlog := Real.log_le_sub_one_of_pos (div_pos one_pos (mul_pos hp hxpos))
    have hmul := mul_le_mul_of_nonneg_left hlog hxpos.le
    have hlhs : x * Real.log (1 / (p * x)) = Real.negMulLog x - x * Real.log p := by
      unfold Real.negMulLog
      rw [Real.log_div one_ne_zero (mul_pos hp hxpos).ne', Real.log_one, Real.log_mul hp.ne' hxpos.ne']
      ring
    have hrhs : x * (1 / (p * x) - 1) = 1 / p - x := by
      field_simp
    linarith

/-! ### Pair-averaged mass and entropy potential -/

/-- Mass at vertex `u` starting from `v` after `k` rounds of matchings `σ`. -/
private noncomputable def mass (σ : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℝ
  | 0, v, u => if u = v then 1 else 0
  | k + 1, v, u => (mass σ k v u + mass σ k v (σ k u)) / 2

/-- Total entropy potential across all starting vertices `v ∈ V`. -/
private noncomputable def entropy (V : Finset ℕ) (σ : ℕ → ℕ → ℕ) (k : ℕ) : ℝ :=
  ∑ v ∈ V, ∑ u ∈ V, Real.negMulLog (mass σ k v u)

private lemma mass_nonneg (σ : ℕ → ℕ → ℕ) (k v u : ℕ) : 0 ≤ mass σ k v u := by
  induction k generalizing u with
  | zero =>
    unfold mass
    split_ifs <;> norm_num
  | succ k ih =>
    unfold mass
    linarith [ih u, ih (σ k u)]

/-- Summing a function over `V` is invariant under an involution matching on `V`. -/
private lemma sum_comp_involution {V : Finset ℕ} {σ : ℕ → ℕ} (hσ : IsInvolutionMatching V σ)
    (f : ℕ → ℝ) : ∑ u ∈ V, f (σ u) = ∑ u ∈ V, f u := by
  refine Finset.sum_nbij σ ?_ ?_ ?_ ?_
  · intro u hu
    exact hσ.1 u hu
  · intro u₁ hu₁ u₂ hu₂ heq
    have h1 := hσ.2.1 u₁ hu₁
    have h2 := hσ.2.1 u₂ hu₂
    rw [← h1, ← h2, heq]
  · intro u hu
    exact ⟨σ u, Finset.mem_coe.mpr (hσ.1 u hu), hσ.2.1 u hu⟩
  · intro _ _
    rfl

private lemma sum_mass_row {V : Finset ℕ} {σ : ℕ → ℕ → ℕ} {k : ℕ}
    (hσ : ∀ j < k, IsInvolutionMatching V (σ j)) {v : ℕ} (hv : v ∈ V) :
    ∑ u ∈ V, mass σ k v u = 1 := by
  induction k with
  | zero =>
    simp [mass, hv]
  | succ k ih =>
    have hk := hσ k (Nat.lt_succ_self k)
    have hprev := ih (fun j hj => hσ j (Nat.lt_succ_of_lt hj))
    simp only [mass]
    have hsplit : ∑ u ∈ V, (mass σ k v u + mass σ k v (σ k u)) / 2 =
        (∑ u ∈ V, mass σ k v u + ∑ u ∈ V, mass σ k v (σ k u)) / 2 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_div]
    rw [hsplit, sum_comp_involution hk (mass σ k v), hprev]
    norm_num

private lemma sum_mass_col {V : Finset ℕ} {σ : ℕ → ℕ → ℕ} {k : ℕ}
    (hσ : ∀ j < k, IsInvolutionMatching V (σ j)) {u : ℕ} (hu : u ∈ V) :
    ∑ v ∈ V, mass σ k v u = 1 := by
  induction k generalizing u with
  | zero =>
    simp [mass, hu]
  | succ k ih =>
    have hk := hσ k (Nat.lt_succ_self k)
    have hprev1 := ih (fun j hj => hσ j (Nat.lt_succ_of_lt hj)) hu
    have hprev2 := ih (fun j hj => hσ j (Nat.lt_succ_of_lt hj)) (hk.1 u hu)
    simp only [mass]
    have hsplit : ∑ v ∈ V, (mass σ k v u + mass σ k v (σ k u)) / 2 =
        (∑ v ∈ V, mass σ k v u + ∑ v ∈ V, mass σ k v (σ k u)) / 2 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_div]
    rw [hsplit, hprev1, hprev2]
    norm_num

private lemma entropy_zero (V : Finset ℕ) (σ : ℕ → ℕ → ℕ) : entropy V σ 0 = 0 := by
  unfold entropy
  apply Finset.sum_eq_zero
  intro v _
  apply Finset.sum_eq_zero
  intro u _
  unfold mass
  split_ifs <;> simp

private lemma entropy_le {V : Finset ℕ} {σ : ℕ → ℕ → ℕ} {k : ℕ} (hV : V.Nonempty)
    (hσ : ∀ j < k, IsInvolutionMatching V (σ j)) :
    entropy V σ k ≤ (V.card : ℝ) * Real.log (V.card : ℝ) := by
  have hp : (0 : ℝ) < V.card := Nat.cast_pos.mpr hV.card_pos
  unfold entropy
  calc ∑ v ∈ V, ∑ u ∈ V, Real.negMulLog (mass σ k v u)
      ≤ ∑ _v ∈ V, Real.log (V.card : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        have hrow := sum_mass_row hσ hv
        calc ∑ u ∈ V, Real.negMulLog (mass σ k v u)
            ≤ ∑ u ∈ V, (mass σ k v u * Real.log (V.card : ℝ) + 1 / (V.card : ℝ) - mass σ k v u) :=
              Finset.sum_le_sum fun u _ => negMulLog_le_linear hp (mass_nonneg σ k v u)
          _ = (∑ u ∈ V, mass σ k v u) * Real.log (V.card : ℝ) +
                (V.card : ℝ) * (1 / (V.card : ℝ)) - ∑ u ∈ V, mass σ k v u := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
                Finset.sum_const, nsmul_eq_mul]
          _ = Real.log (V.card : ℝ) := by
              rw [hrow]
              have hpne : (V.card : ℝ) ≠ 0 := hp.ne'
              field_simp
              ring
    _ = (V.card : ℝ) * Real.log (V.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Exact one-step entropy gain in terms of `pairGain`. -/
private lemma entropy_step_eq {V : Finset ℕ} {σ : ℕ → ℕ → ℕ} {k : ℕ}
    (hk : IsInvolutionMatching V (σ k)) :
    entropy V σ (k + 1) - entropy V σ k =
      (1 / 2 : ℝ) * ∑ v ∈ V, ∑ u ∈ V, pairGain (mass σ k v u) (mass σ k v (σ k u)) := by
  unfold entropy
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  have hinv := sum_comp_involution hk (fun u => Real.negMulLog (mass σ k v u))
  have h2 : ∑ u ∈ V, pairGain (mass σ k v u) (mass σ k v (σ k u)) =
      2 * (∑ u ∈ V, Real.negMulLog (mass σ (k + 1) v u) -
        ∑ u ∈ V, Real.negMulLog (mass σ k v u)) := by
    simp only [pairGain, mass]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hinv]
    ring
  linarith

/-! ### Mass escaping a cut `C` -/

/-- Total mass starting in `C` that currently sits at `u`. -/
private noncomputable def cutMass (σ : ℕ → ℕ → ℕ) (k : ℕ) (C : Finset ℕ) (u : ℕ) : ℝ :=
  ∑ v ∈ C, mass σ k v u

private lemma cutMass_nonneg (σ : ℕ → ℕ → ℕ) (k : ℕ) (C : Finset ℕ) (u : ℕ) :
    0 ≤ cutMass σ k C u :=
  Finset.sum_nonneg fun v _ => mass_nonneg σ k v u

private lemma cutMass_le_one {V : Finset ℕ} {σ : ℕ → ℕ → ℕ} {k : ℕ}
    (hσ : ∀ j < k, IsInvolutionMatching V (σ j)) {C : Finset ℕ} (hCV : C ⊆ V)
    {u : ℕ} (hu : u ∈ V) : cutMass σ k C u ≤ 1 := by
  calc cutMass σ k C u
      = ∑ v ∈ C, mass σ k v u := rfl
    _ ≤ ∑ v ∈ V, mass σ k v u :=
        Finset.sum_le_sum_of_subset_of_nonneg hCV fun v _ _ => mass_nonneg σ k v u
    _ = 1 := sum_mass_col hσ hu

/-- One step of matching increases the mass outside `C` by at most half the number of pairs crossing
`C` in that round. -/
private lemma outMass_step_le {V : Finset ℕ} {σ : ℕ → ℕ → ℕ} {j : ℕ}
    (hσ : ∀ i ≤ j, IsInvolutionMatching V (σ i)) {C : Finset ℕ} (hCV : C ⊆ V) :
    ∑ u ∈ V \ C, cutMass σ (j + 1) C u ≤
      ∑ u ∈ V \ C, cutMass σ j C u +
        (1 / 2 : ℝ) * (((V \ C).filter fun u => σ j u ∈ C).card : ℝ) := by
  have hj := hσ j (le_refl j)
  have hprev : ∀ i < j, IsInvolutionMatching V (σ i) := fun i hi => hσ i hi.le
  have hstep : ∀ u, cutMass σ (j + 1) C u = (cutMass σ j C u + cutMass σ j C (σ j u)) / 2 := by
    intro u
    unfold cutMass
    simp only [mass]
    rw [← Finset.sum_add_distrib, ← Finset.sum_div]
  simp_rw [hstep]
  have hdiff : ∑ u ∈ V \ C, (cutMass σ j C u + cutMass σ j C (σ j u)) / 2 -
      ∑ u ∈ V \ C, cutMass σ j C u =
      (1 / 2 : ℝ) * ∑ u ∈ V \ C, (cutMass σ j C (σ j u) - cutMass σ j C u) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  -- Split `V \ C` into vertices mapped into `C` and vertices kept in `V \ C`.
  set B := (V \ C).filter fun u => σ j u ∈ C
  set A := (V \ C).filter fun u => σ j u ∉ C
  have hsplit : ∑ u ∈ V \ C, (cutMass σ j C (σ j u) - cutMass σ j C u) =
      ∑ u ∈ B, (cutMass σ j C (σ j u) - cutMass σ j C u) +
        ∑ u ∈ A, (cutMass σ j C (σ j u) - cutMass σ j C u) := by
    exact (Finset.sum_filter_add_sum_filter_not (V \ C) (fun u => σ j u ∈ C) _).symm
  -- On `A`, `σ j` is an involution, so the difference sums to `0`.
  have hA : ∑ u ∈ A, (cutMass σ j C (σ j u) - cutMass σ j C u) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hbij : ∑ u ∈ A, cutMass σ j C (σ j u) = ∑ u ∈ A, cutMass σ j C u := by
      refine Finset.sum_nbij (σ j) ?_ ?_ ?_ ?_
      · intro u hu
        simp only [A, Finset.mem_filter, Finset.mem_sdiff] at hu ⊢
        refine ⟨⟨hj.1 u hu.1.1, hu.2⟩, ?_⟩
        rw [hj.2.1 u hu.1.1]
        exact hu.1.2
      · intro u₁ hu₁ u₂ hu₂ heq
        simp only [A, Finset.mem_coe, Finset.mem_filter, Finset.mem_sdiff] at hu₁ hu₂
        rw [← hj.2.1 u₁ hu₁.1.1, ← hj.2.1 u₂ hu₂.1.1, heq]
      · intro u hu
        simp only [A, Finset.mem_coe, Finset.mem_filter, Finset.mem_sdiff] at hu ⊢
        refine ⟨σ j u, ?_, hj.2.1 u hu.1.1⟩
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_sdiff]
        refine ⟨⟨hj.1 u hu.1.1, hu.2⟩, ?_⟩
        rw [hj.2.1 u hu.1.1]
        exact hu.1.2
      · intro _ _
        rfl
    linarith
  -- On `B`, each term is at most `1`.
  have hB : ∑ u ∈ B, (cutMass σ j C (σ j u) - cutMass σ j C u) ≤ (B.card : ℝ) := by
    calc ∑ u ∈ B, (cutMass σ j C (σ j u) - cutMass σ j C u)
        ≤ ∑ _u ∈ B, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro u hu
          simp only [B, Finset.mem_filter, Finset.mem_sdiff] at hu
          have h1 := cutMass_le_one hprev hCV (hj.1 u hu.1.1)
          have h2 := cutMass_nonneg σ j C u
          linarith
      _ = (B.card : ℝ) := by simp
  linarith

/-- Total mass starting in `C` that lies outside `C` after `k` rounds is at most half the crossing
count of rounds `j < k`. -/
private lemma outMass_le_half_cross {V : Finset ℕ} {σ : ℕ → ℕ → ℕ} {k : ℕ}
    (hσ : ∀ j < k, IsInvolutionMatching V (σ j)) {C : Finset ℕ} (hCV : C ⊆ V) :
    ∑ u ∈ V \ C, cutMass σ k C u ≤ (1 / 2 : ℝ) * (crossCount V σ k C : ℝ) := by
  induction k with
  | zero =>
    have h0 : ∑ u ∈ V \ C, cutMass σ 0 C u = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      apply Finset.sum_eq_zero
      intro v hv
      have hne : u ≠ v := fun h => (Finset.mem_sdiff.mp hu).2 (h ▸ hv)
      simp [mass, hne]
    simp [crossCount, h0]
  | succ k ih =>
    have hprev := ih (fun j hj => hσ j (Nat.lt_succ_of_lt hj))
    have hstep := outMass_step_le (fun i hi => hσ i (Nat.lt_succ_of_le hi)) hCV
    unfold crossCount at hprev ⊢
    rw [Finset.sum_range_succ, Nat.cast_add]
    linarith

/-! ### Round gain and involution round bound -/

/-- A round with a cut `C ⊆ V` satisfying `4 |C| ≥ |V|`, `σ k (C) ∩ C = ∅`, and
`100 * crossCount ≤ |V|` increases the entropy potential by at least `|V| / 70`. -/
private lemma entropy_gain_ge {V : Finset ℕ} {σ : ℕ → ℕ → ℕ} {k : ℕ}
    (hσ : ∀ j ≤ k, IsInvolutionMatching V (σ j)) {C : Finset ℕ} (hCV : C ⊆ V)
    (hCsize : V.card ≤ 4 * C.card) (hdisj : ∀ u ∈ C, σ k u ∉ C)
    (hsparse : 100 * crossCount V σ k C ≤ V.card) :
    (V.card : ℝ) / 70 ≤ entropy V σ (k + 1) - entropy V σ k := by
  have hk := hσ k (le_refl k)
  have hprev : ∀ j < k, IsInvolutionMatching V (σ j) := fun j hj => hσ j hj.le
  rw [entropy_step_eq hk]
  -- Drop nonnegative terms outside `C × C`.
  have hdrop : ∑ v ∈ C, ∑ u ∈ C, pairGain (mass σ k v u) (mass σ k v (σ k u)) ≤
      ∑ v ∈ V, ∑ u ∈ V, pairGain (mass σ k v u) (mass σ k v (σ k u)) := by
    refine le_trans (Finset.sum_le_sum fun v _ => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg hCV fun v _ _ =>
        Finset.sum_nonneg fun u _ => pairGain_nonneg (mass_nonneg _ _ _ _) (mass_nonneg _ _ _ _))
    exact Finset.sum_le_sum_of_subset_of_nonneg hCV fun u _ _ =>
      pairGain_nonneg (mass_nonneg _ _ _ _) (mass_nonneg _ _ _ _)
  -- Apply the linear lower bound on `pairGain`.
  have hlin : (1 / 8 : ℝ) * (∑ v ∈ C, ∑ u ∈ C, mass σ k v u) -
      (1 / 4 : ℝ) * (∑ v ∈ C, ∑ u ∈ C, mass σ k v (σ k u)) ≤
      ∑ v ∈ C, ∑ u ∈ C, pairGain (mass σ k v u) (mass σ k v (σ k u)) := by
    calc (1 / 8 : ℝ) * (∑ v ∈ C, ∑ u ∈ C, mass σ k v u) -
          (1 / 4 : ℝ) * (∑ v ∈ C, ∑ u ∈ C, mass σ k v (σ k u))
        = ∑ v ∈ C, ∑ u ∈ C, (mass σ k v u / 8 - mass σ k v (σ k u) / 4) := by
          simp_rw [Finset.mul_sum]
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro v _
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro u _
          ring
      _ ≤ ∑ v ∈ C, ∑ u ∈ C, pairGain (mass σ k v u) (mass σ k v (σ k u)) :=
          Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun u _ =>
            pairGain_ge_linear (mass_nonneg _ _ _ _) (mass_nonneg _ _ _ _)
  -- Relate both double sums to `out = ∑ u ∈ V \ C, cutMass σ k C u`.
  set out : ℝ := ∑ u ∈ V \ C, cutMass σ k C u
  have hout_eq : out = ∑ v ∈ C, ∑ u ∈ V \ C, mass σ k v u := by
    dsimp only [out, cutMass]
    rw [Finset.sum_comm]
  have hsum1 : ∑ v ∈ C, ∑ u ∈ C, mass σ k v u = (C.card : ℝ) - out := by
    have hrow : ∑ v ∈ C, (∑ u ∈ C, mass σ k v u + ∑ u ∈ V \ C, mass σ k v u) = (C.card : ℝ) := by
      calc ∑ v ∈ C, (∑ u ∈ C, mass σ k v u + ∑ u ∈ V \ C, mass σ k v u)
          = ∑ v ∈ C, ∑ u ∈ V, mass σ k v u := by
            apply Finset.sum_congr rfl
            intro v _
            rw [← Finset.sum_union disjoint_sdiff_self_right, Finset.union_sdiff_of_subset hCV]
        _ = ∑ _v ∈ C, (1 : ℝ) := Finset.sum_congr rfl fun v hv => sum_mass_row hprev (hCV hv)
        _ = (C.card : ℝ) := by simp
    rw [Finset.sum_add_distrib] at hrow
    linarith
  have hsum2 : ∑ v ∈ C, ∑ u ∈ C, mass σ k v (σ k u) ≤ out := by
    rw [hout_eq]
    apply Finset.sum_le_sum
    intro v _
    have hinj : ∀ u₁ ∈ C, ∀ u₂ ∈ C, σ k u₁ = σ k u₂ → u₁ = u₂ := by
      intro u₁ hu₁ u₂ hu₂ heq
      rw [← hk.2.1 u₁ (hCV hu₁), ← hk.2.1 u₂ (hCV hu₂), heq]
    have himg : C.image (σ k) ⊆ V \ C := by
      intro w hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_sdiff.mpr ⟨hk.1 u (hCV hu), hdisj u hu⟩
    calc ∑ u ∈ C, mass σ k v (σ k u)
        = ∑ w ∈ C.image (σ k), mass σ k v w := (Finset.sum_image hinj).symm
      _ ≤ ∑ w ∈ V \ C, mass σ k v w :=
          Finset.sum_le_sum_of_subset_of_nonneg himg fun w _ _ => mass_nonneg _ _ _ _
  have hout_le : out ≤ (V.card : ℝ) / 200 := by
    have h1 := outMass_le_half_cross hprev hCV
    have h2 : (crossCount V σ k C : ℝ) ≤ (V.card : ℝ) / 100 := by
      have hcast : (100 : ℝ) * (crossCount V σ k C : ℝ) ≤ (V.card : ℝ) := by exact_mod_cast hsparse
      linarith
    linarith
  have hCr : (V.card : ℝ) / 4 ≤ (C.card : ℝ) := by
    have hcast : (V.card : ℝ) ≤ 4 * (C.card : ℝ) := by exact_mod_cast hCsize
    linarith
  linarith

/-- **Round bound** (involution form): if a cut-matching game on a nonempty set `V` runs for `T`
rounds, where each round `k < T` uses a fixed-point-free involution `σ k` and has a cut `C ⊆ V`
with `4 |C| ≥ |V|`, `σ k (C) ∩ C = ∅`, and `100 * crossCount V σ k C ≤ |V|`, then
`T ≤ 70 * Real.log |V|`. -/
theorem round_bound_involution {V : Finset ℕ} {σ : ℕ → ℕ → ℕ} {T : ℕ} (hV : V.Nonempty)
    (hσ : ∀ k < T, IsInvolutionMatching V (σ k))
    (hcut : ∀ k < T, ∃ C ⊆ V, V.card ≤ 4 * C.card ∧ (∀ u ∈ C, σ k u ∉ C) ∧
      100 * crossCount V σ k C ≤ V.card) :
    (T : ℝ) ≤ 70 * Real.log (V.card : ℝ) := by
  have hgain : ∀ k ≤ T, (k : ℝ) * ((V.card : ℝ) / 70) ≤ entropy V σ k := by
    intro k hk
    induction k with
    | zero =>
      simp [entropy_zero]
    | succ k ih =>
      have hkT : k < T := hk
      have hprev := ih (Nat.le_of_lt hkT)
      obtain ⟨C, hCV, hCsize, hdisj, hsparse⟩ := hcut k hkT
      have hstep := entropy_gain_ge (fun j hj => hσ j (lt_of_le_of_lt hj hkT))
        hCV hCsize hdisj hsparse
      push_cast
      linarith
  have hlow := hgain T (le_refl T)
  have hhigh := entropy_le hV hσ
  have hp : (0 : ℝ) < V.card := Nat.cast_pos.mpr hV.card_pos
  have hmul : (T : ℝ) * (V.card : ℝ) ≤ 70 * Real.log (V.card : ℝ) * (V.card : ℝ) := by linarith
  exact le_of_mul_le_mul_right hmul hp

/-! ### Bridging edge lists and involutions -/

private lemma not_mem_flatMap_of_nodup_cons {a b : ℕ} {rest : List (ℕ × ℕ)}
    (hnd : (((a, b) :: rest).flatMap fun e => [e.1, e.2]).Nodup) :
    a ≠ b ∧ (∀ e ∈ rest, e.1 ≠ a ∧ e.2 ≠ a ∧ e.1 ≠ b ∧ e.2 ≠ b) := by
  simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons] at hnd
  obtain ⟨ha, hb, _⟩ := hnd
  refine ⟨fun h => ha (by simp [h]), fun e he => ?_⟩
  have h1 : e.1 ≠ a := fun h => ha (List.mem_cons_of_mem b
    (List.mem_flatMap.mpr ⟨e, he, by simp [h]⟩))
  have h2 : e.2 ≠ a := fun h => ha (List.mem_cons_of_mem b
    (List.mem_flatMap.mpr ⟨e, he, by simp [h]⟩))
  have h3 : e.1 ≠ b := fun h => hb (List.mem_flatMap.mpr ⟨e, he, by simp [h]⟩)
  have h4 : e.2 ≠ b := fun h => hb (List.mem_flatMap.mpr ⟨e, he, by simp [h]⟩)
  exact ⟨h1, h2, h3, h4⟩

/-- In a matching edge list, `mate E` swaps the two endpoints of every edge in `E`. -/
theorem mate_eq_of_mem {E : List (ℕ × ℕ)} (hnd : (E.flatMap fun e => [e.1, e.2]).Nodup)
    {a b : ℕ} (hab : (a, b) ∈ E) :
    mate E a = b ∧ mate E b = a := by
  induction E with
  | nil => simp at hab
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    have hcons := not_mem_flatMap_of_nodup_cons hnd
    have hnd' : (rest.flatMap fun e => [e.1, e.2]).Nodup := by
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons] at hnd
      exact hnd.2.2
    rcases List.mem_cons.mp hab with heq | hmem
    · injection heq with hx hy
      subst hx hy
      simp [mate, hcons.1]
    · have hne := hcons.2 (a, b) hmem
      simp only [mate, hne.1.symm, hne.2.1.symm, hne.2.2.1.symm, hne.2.2.2.symm, ↓reduceIte]
      exact ih hnd' hmem

/-- Every perfect matching edge list on `V` induces a fixed-point-free involution `mate E` on `V`. -/
theorem isInvolutionMatching_mate {V : Finset ℕ} {E : List (ℕ × ℕ)}
    (hE : IsPerfectMatchingOn V E) : IsInvolutionMatching V (mate E) := by
  obtain ⟨hmem, hnd, hcov⟩ := hE
  have hne_end : ∀ e ∈ E, e.1 ≠ e.2 := by
    clear hmem hcov
    intro e he
    induction E with
    | nil => simp at he
    | cons p rest ih =>
      rcases p with ⟨x, y⟩
      have hcons := not_mem_flatMap_of_nodup_cons hnd
      have hnd' : (rest.flatMap fun e => [e.1, e.2]).Nodup := by
        simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons] at hnd
        exact hnd.2.2
      rcases List.mem_cons.mp he with rfl | hrest
      · exact hcons.1
      · exact ih hnd' hrest
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨⟨a, b⟩, hab, rfl | rfl⟩ := hcov u hu
    · rw [(mate_eq_of_mem hnd hab).1]; exact (hmem _ hab).2
    · rw [(mate_eq_of_mem hnd hab).2]; exact (hmem _ hab).1
  · intro u hu
    obtain ⟨⟨a, b⟩, hab, rfl | rfl⟩ := hcov u hu
    · rw [(mate_eq_of_mem hnd hab).1, (mate_eq_of_mem hnd hab).2]
    · rw [(mate_eq_of_mem hnd hab).2, (mate_eq_of_mem hnd hab).1]
  · intro u hu
    obtain ⟨⟨a, b⟩, hab, rfl | rfl⟩ := hcov u hu
    · rw [(mate_eq_of_mem hnd hab).1]; exact (hne_end _ hab).symm
    · rw [(mate_eq_of_mem hnd hab).2]; exact hne_end _ hab

private lemma nodup_map_choose_end {E : List (ℕ × ℕ)} (f : ℕ × ℕ → ℕ)
    (hf : ∀ e ∈ E, f e = e.1 ∨ f e = e.2)
    (hnd : (E.flatMap fun e => [e.1, e.2]).Nodup) : (E.map f).Nodup := by
  induction E with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    have hcons := not_mem_flatMap_of_nodup_cons hnd
    have hnd' : (rest.flatMap fun e => [e.1, e.2]).Nodup := by
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons] at hnd
      exact hnd.2.2
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (fun e he => hf e (List.mem_cons_of_mem _ he)) hnd'⟩
    intro hmem
    obtain ⟨e, he, hfe⟩ := List.mem_map.mp hmem
    have hne := hcons.2 e he
    rcases hf (x, y) List.mem_cons_self with hxy | hxy <;>
      rcases hf e (List.mem_cons_of_mem _ he) with he' | he' <;>
      omega

/-- Bridging lemma for one round: the cut of `C` in a perfect matching `E` on `V` equals the number
of vertices `u ∈ V \ C` whose `mate E` lies in `C`. -/
theorem cutIn_eq_card_mate {n : ℕ} {V C : Finset ℕ} {E : List (ℕ × ℕ)}
    (hE : IsPerfectMatchingOn V E) :
    (Graph.mk n E).cutIn V C = ((V \ C).filter fun u => mate E u ∈ C).card := by
  classical
  obtain ⟨hmem, hnd, hcov⟩ := hE
  have hins : (Graph.mk n E).inside V = E := by
    unfold Graph.inside
    apply List.filter_eq_self.mpr
    intro e he
    simp [(hmem e he).1, (hmem e he).2]
  unfold Graph.cutIn
  rw [hins]
  set E_cr := E.filter fun e => decide (e.1 ∈ C) != decide (e.2 ∈ C)
  let outEnd : ℕ × ℕ → ℕ := fun e => if e.1 ∈ C then e.2 else e.1
  have hnd_cr : (E_cr.flatMap fun e => [e.1, e.2]).Nodup :=
    hnd.sublist (List.filter_sublist.flatMap _)
  have hnd_out : (E_cr.map outEnd).Nodup :=
    nodup_map_choose_end outEnd (fun e _ => by dsimp only [outEnd]; split_ifs <;> simp) hnd_cr
  have hset : (E_cr.map outEnd).toFinset = (V \ C).filter fun u => mate E u ∈ C := by
    ext u
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      rw [List.mem_filter] at hab
      have hmate := mate_eq_of_mem hnd hab.1
      have hVab := hmem _ hab.1
      dsimp only [outEnd]
      by_cases ha : a ∈ C
      · have hb : b ∉ C := by
          intro hb
          simp [ha, hb] at hab
        have hif : (if a ∈ C then b else a) = b := ite_eq_left_iff.mpr fun h => absurd ha h
        rw [hif]
        exact ⟨⟨hVab.2, hb⟩, hmate.2.symm ▸ ha⟩
      · have hb : b ∈ C := by
          by_contra hb
          simp [ha, hb] at hab
        have hif : (if a ∈ C then b else a) = a := ite_eq_right_iff.mpr fun h => absurd h ha
        rw [hif]
        exact ⟨⟨hVab.1, ha⟩, hmate.1.symm ▸ hb⟩
    · rintro ⟨⟨huV, huC⟩, hmateC⟩
      obtain ⟨⟨a, b⟩, hab, rfl | rfl⟩ := hcov u huV
      · have hmate := mate_eq_of_mem hnd hab
        rw [hmate.1] at hmateC
        refine ⟨(a, b), List.mem_filter.mpr ⟨hab, by simp [huC, hmateC]⟩, ?_⟩
        simp [outEnd, huC]
      · have hmate := mate_eq_of_mem hnd hab
        rw [hmate.2] at hmateC
        refine ⟨(a, b), List.mem_filter.mpr ⟨hab, by simp [huC, hmateC]⟩, ?_⟩
        simp [outEnd, hmateC]
  calc E_cr.length = (E_cr.map outEnd).length := by simp
    _ = (E_cr.map outEnd).toFinset.card := (List.toFinset_card_of_nodup hnd_out).symm
    _ = ((V \ C).filter fun u => mate E u ∈ C).card := by rw [hset]

/-- The cut of `C` in the accumulated witness graph `witnessEdges M k` is the sum of the cuts in
the individual rounds `j < k`. -/
theorem cutIn_witnessEdges (n : ℕ) (M : ℕ → List (ℕ × ℕ)) (V C : Finset ℕ) (k : ℕ) :
    (Graph.mk n (witnessEdges M k)).cutIn V C =
      ∑ j ∈ Finset.range k, (Graph.mk n (M j)).cutIn V C := by
  induction k with
  | zero => simp [witnessEdges, Graph.cutIn, Graph.inside]
  | succ k ih =>
    rw [witnessEdges, cutIn_append, ih, Finset.sum_range_succ]

/-- Bridging lemma over `k` rounds: `cutIn` of the witness graph built by appending perfect
matching edge lists equals `crossCount` of the induced involutions `mate (M j)`. -/
theorem cutIn_witnessEdges_eq_crossCount {n : ℕ} {V C : Finset ℕ} {M : ℕ → List (ℕ × ℕ)} {k : ℕ}
    (hM : ∀ j < k, IsPerfectMatchingOn V (M j)) :
    (Graph.mk n (witnessEdges M k)).cutIn V C = crossCount V (fun j => mate (M j)) k C := by
  rw [cutIn_witnessEdges]
  unfold crossCount
  apply Finset.sum_congr rfl
  intro j hj
  exact cutIn_eq_card_mate (hM j (Finset.mem_range.mp hj))

/-- If `E` is a perfect matching on `V` whose edges never have both ends in `C`, then `mate E` maps
`C` out of `C`. -/
theorem mate_not_mem_of_disjoint {V C : Finset ℕ} {E : List (ℕ × ℕ)}
    (hE : IsPerfectMatchingOn V E) (hCV : C ⊆ V) (hdisj : ∀ e ∈ E, ¬ (e.1 ∈ C ∧ e.2 ∈ C)) :
    ∀ u ∈ C, mate E u ∉ C := by
  intro u hu
  obtain ⟨⟨a, b⟩, hab, rfl | rfl⟩ := hE.2.2 u (hCV hu)
  · rw [(mate_eq_of_mem hE.2.1 hab).1]
    exact fun hb => hdisj (a, b) hab ⟨hu, hb⟩
  · rw [(mate_eq_of_mem hE.2.1 hab).2]
    exact fun ha => hdisj (a, b) hab ⟨ha, hu⟩

/-! ### Final round bounds for `OneShot` -/

/-- **Round bound** (witness-graph form): a cut-matching game on a nonempty vertex set `V` of size `p`,
where each round `k < T` appends a perfect matching `M k` on `V` crossing a sparse cut `C ⊆ V`
with `4 |C| ≥ p`, no edge of `M k` inside `C`, and `100 * cut_{W_k}(C) ≤ p`, satisfies
`T ≤ 70 * Real.log p` (and in particular `T < 70 * Real.log p + 1`). -/
theorem round_bound_log {n : ℕ} {V : Finset ℕ} {M : ℕ → List (ℕ × ℕ)} {T : ℕ}
    (hV : V.Nonempty) (hM : ∀ k < T, IsPerfectMatchingOn V (M k))
    (hcut : ∀ k < T, ∃ C ⊆ V, V.card ≤ 4 * C.card ∧
      (∀ e ∈ M k, ¬ (e.1 ∈ C ∧ e.2 ∈ C)) ∧
      100 * (Graph.mk n (witnessEdges M k)).cutIn V C ≤ V.card) :
    (T : ℝ) < 70 * Real.log (V.card : ℝ) + 1 := by
  have hle : (T : ℝ) ≤ 70 * Real.log (V.card : ℝ) := by
    refine round_bound_involution hV (fun k hk => isInvolutionMatching_mate (hM k hk)) ?_
    intro k hk
    obtain ⟨C, hCV, hCsize, hdisj, hsparse⟩ := hcut k hk
    refine ⟨C, hCV, hCsize, mate_not_mem_of_disjoint (hM k hk) hCV hdisj, ?_⟩
    rwa [← cutIn_witnessEdges_eq_crossCount (n := n) (fun j hj => hM j (lt_trans hj hk))]
  linarith

/-- **Round bound** (integer form for `OneShot`): under the same hypotheses, if `|V| < 2 ^ L`, then
the game lasts fewer than `49 * L + 1` rounds. -/
theorem round_bound_nat {n L : ℕ} {V : Finset ℕ} {M : ℕ → List (ℕ × ℕ)} {T : ℕ}
    (hV : V.Nonempty) (hVL : V.card < 2 ^ L)
    (hM : ∀ k < T, IsPerfectMatchingOn V (M k))
    (hcut : ∀ k < T, ∃ C ⊆ V, V.card ≤ 4 * C.card ∧
      (∀ e ∈ M k, ¬ (e.1 ∈ C ∧ e.2 ∈ C)) ∧
      100 * (Graph.mk n (witnessEdges M k)).cutIn V C ≤ V.card) :
    T < 49 * L + 1 := by
  have hle : (T : ℝ) ≤ 70 * Real.log (V.card : ℝ) := by
    refine round_bound_involution hV (fun k hk => isInvolutionMatching_mate (hM k hk)) ?_
    intro k hk
    obtain ⟨C, hCV, hCsize, hdisj, hsparse⟩ := hcut k hk
    refine ⟨C, hCV, hCsize, mate_not_mem_of_disjoint (hM k hk) hCV hdisj, ?_⟩
    rwa [← cutIn_witnessEdges_eq_crossCount (n := n) (fun j hj => hM j (lt_trans hj hk))]
  have hp : (0 : ℝ) < V.card := Nat.cast_pos.mpr hV.card_pos
  have hVLr : (V.card : ℝ) < (2 : ℝ) ^ L := by exact_mod_cast hVL
  have hlog : Real.log (V.card : ℝ) < L * Real.log 2 := by
    calc Real.log (V.card : ℝ) < Real.log ((2 : ℝ) ^ L) := Real.log_lt_log hp hVLr
      _ = L * Real.log 2 := Real.log_pow 2 L
  have hlog2 : Real.log 2 < 7 / 10 := by linarith [Real.log_two_lt_d9]
  have hLpos : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hTr : (T : ℝ) < 49 * (L : ℝ) + 1 := by nlinarith
  exact_mod_cast hTr

end MinCostFlow.ExpanderDecomp
