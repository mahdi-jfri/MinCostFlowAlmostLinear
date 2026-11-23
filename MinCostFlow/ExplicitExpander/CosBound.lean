module

public import MinCostFlow.ExplicitExpander.Fourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The pointwise bound of the Margulis proof

The Fourier proof that the Margulis graph expands (Hoory, Linial and Wigderson, Bull. AMS 43
(2006), Section 8) ends with a bound at each point of the torus. A point `(u₁, u₂) ≠ 0` has four
neighbours `(u₁, u₂ ± 2u₁)` and `(u₁ ± 2u₂, u₂)`. Each pair of neighbours gets a weight that depends
on whether the changed coordinate gets smaller or larger in absolute value: `3/2` if the neighbour
is smaller, `2/3` if it is larger, `1` if they are equal. The bound says that the weights, each pair
times `cos(π |u_i| / m)`, sum to at most `15/4`, which is below the trivial `4`.

The survey uses the weights `√2` and `1/√2`; we use `3/2` and `2/3`, which keep all numbers
rational and still give a bound below `4`.

Write `a` and `b` for the absolute values of the two coordinates. The main lemma
`coeff_le_of_le` assumes `a ≤ b` and splits into cases on `a`, `b` and `m`. In each case the
sizes of `b ± 2a` and `a ± 2b` modulo `m` are computed (`sizeI_spec`), which fixes the weights,
and an inequality on cosines ends the case. The main result is `coeff_le`.
-/

public section

namespace MinCostFlow.ExplicitExpander

/-- The weight of a neighbour: `3/2` if its coordinate `b` is smaller than the own coordinate
`a`, `2/3` if it is larger, and `1` if they are equal. -/
@[expose] noncomputable def weight (a b : ℤ) : ℝ := if b < a then 3 / 2 else if a < b then 2 / 3 else 1

/-- The size of an integer `p` modulo `m`: the absolute value of its representative in
`(-m/2, m/2]`. -/
@[expose] def sizeI (m : ℕ) (p : ℤ) : ℤ := |((p : ZMod m)).valMinAbs|

/-- The sum of the weights at a point with coordinates of sizes `a` and `b`. -/
@[expose] noncomputable def coeff (m : ℕ) (a b : ℤ) : ℝ :=
  halfCos m a * (weight b (sizeI m (b - 2 * a)) + weight b (sizeI m (b + 2 * a))) +
    halfCos m b * (weight a (sizeI m (a - 2 * b)) + weight a (sizeI m (a + 2 * b)))

lemma weight_le (a b : ℤ) : weight a b ≤ 3 / 2 := by
  unfold weight; split_ifs <;> norm_num

lemma weight_pos (a b : ℤ) : 0 < weight a b := by
  unfold weight; split_ifs <;> norm_num

lemma weight_mul_weight (a b : ℤ) : weight a b * weight b a = 1 := by
  unfold weight
  split_ifs <;> first | (exfalso; omega) | norm_num

lemma weight_of_lt {a b : ℤ} (h : a < b) : weight a b = 2 / 3 := by
  unfold weight; split_ifs <;> first | rfl | omega

lemma weight_self (a : ℤ) : weight a a = 1 := by
  unfold weight; simp

lemma sizeI_neg (m : ℕ) (p : ℤ) : sizeI m (-p) = sizeI m p := by
  unfold sizeI
  push_cast
  rw [abs_eq_abs, ← Int.natAbs_eq_natAbs_iff, ZMod.natAbs_valMinAbs_neg]

variable {m : ℕ} [NeZero m]

lemma sizeI_eq_of {p q : ℤ} (k : ℤ) (hq : q = p + k * m) (h1 : -(m : ℤ) < 2 * q)
    (h2 : 2 * q ≤ m) : sizeI m p = |q| := by
  unfold sizeI
  congr 1
  rw [ZMod.valMinAbs_spec]
  refine ⟨?_, ?_, ?_⟩
  · rw [hq]; push_cast; simp
  · linarith
  · linarith

/-- The size of `p` modulo `m`, for `|2p| ≤ 3m`: it is `|q|` for one of `q = p, p - m, p + m`
with `2q ∈ (-m, m]`. -/
lemma sizeI_spec (p : ℤ) (h1 : -3 * (m : ℤ) < 2 * p) (h2 : 2 * p ≤ 3 * m) :
    ∃ q, sizeI m p = |q| ∧ (q = p ∨ q = p - m ∨ q = p + m) ∧ -(m : ℤ) < 2 * q ∧ 2 * q ≤ m := by
  by_cases ha : -(m : ℤ) < 2 * p ∧ 2 * p ≤ m
  · exact ⟨p, sizeI_eq_of 0 (by ring) ha.1 ha.2, Or.inl rfl, ha⟩
  · by_cases hb : (m : ℤ) < 2 * p
    · exact ⟨p - m, sizeI_eq_of (-1) (by ring) (by omega) (by omega), Or.inr (Or.inl rfl),
        by omega, by omega⟩
    · exact ⟨p + m, sizeI_eq_of 1 (by ring) (by omega) (by omega), Or.inr (Or.inr rfl),
        by omega, by omega⟩

/-- Solve a goal about one size: compute it with `sizeI_spec`, then `omega`. -/
local macro "size_tac" p:term : tactic =>
  `(tactic| (obtain ⟨q, hq, hqc, hq1, hq2⟩ := sizeI_spec (m := m) $p (by omega) (by omega)
             rw [hq]
             rcases abs_cases q with ⟨hab, _⟩ | ⟨hab, _⟩ <;> rw [hab] <;> omega))

private lemma mpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)

omit [NeZero m] in
lemma halfCos_le_one (a : ℤ) : halfCos m a ≤ 1 := Real.cos_le_one _

omit [NeZero m] in
lemma halfCos_zero : halfCos m 0 = 1 := by simp [halfCos]

lemma halfCos_of_two_mul_eq {b : ℤ} (h : 2 * b = m) : halfCos m b = 0 := by
  unfold halfCos
  have hb : (b : ℝ) = m / 2 := by
    have : (2 : ℝ) * b = m := by exact_mod_cast h
    linarith
  rw [hb, show Real.pi * (m / 2 : ℝ) / m = Real.pi / 2 by field_simp [mpos.ne']]
  exact Real.cos_pi_div_two

lemma halfCos_le_sqrt {a : ℤ} (h1 : m ≤ 4 * a) (h2 : 2 * a ≤ m) :
    halfCos m a ≤ Real.sqrt 2 / 2 := by
  unfold halfCos
  rw [← Real.cos_pi_div_four]
  have hm := mpos (m := m)
  have h1' : (m : ℝ) ≤ 4 * a := by exact_mod_cast h1
  have h2' : 2 * (a : ℝ) ≤ m := by exact_mod_cast h2
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
  · rw [div_le_iff₀ hm]; nlinarith [Real.pi_pos]
  · rw [le_div_iff₀ hm]; nlinarith [Real.pi_pos]

lemma halfCos_le_sin {a b : ℤ} (h0 : 0 ≤ a) (h1 : m ≤ 2 * a + 2 * b) (h2 : 2 * a ≤ m)
    (h3 : 2 * b ≤ m) : halfCos m a ≤ Real.sin (Real.pi * b / m) := by
  unfold halfCos
  rw [← Real.cos_pi_div_two_sub]
  have hm := mpos (m := m)
  have h0' : (0 : ℝ) ≤ a := by exact_mod_cast h0
  have h1' : (m : ℝ) ≤ 2 * a + 2 * b := by exact_mod_cast h1
  have h2' : 2 * (a : ℝ) ≤ m := by exact_mod_cast h2
  have h3' : 2 * (b : ℝ) ≤ m := by exact_mod_cast h3
  have hpb : Real.pi * b / m ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hm]; nlinarith [Real.pi_pos]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by linarith)
  · rw [div_le_iff₀ hm]; nlinarith [Real.pi_pos]
  · have : Real.pi / 2 - Real.pi * b / m = Real.pi * (m / 2 - b) / m := by
      field_simp
    rw [this, div_le_div_iff_of_pos_right hm]
    nlinarith [Real.pi_pos]

private lemma cs_bound {s c : ℝ} (h : s ^ 2 + c ^ 2 = 1) : 3 * s + 13 / 6 * c ≤ 15 / 4 := by
  nlinarith [sq_nonneg (3 * c - 13 / 6 * s), sq_nonneg (3 * s + 13 / 6 * c - 15 / 4)]

/-- The pointwise bound when `a ≤ b`. -/
lemma coeff_le_of_le {a b : ℤ} (h0 : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) (hbm : 2 * b ≤ m) :
    coeff m a b ≤ 15 / 4 := by
  have hcA0 := halfCos_nonneg (m := m) h0 (by omega)
  have hcB0 := halfCos_nonneg (m := m) hb.le hbm
  have hcA1 := halfCos_le_one (m := m) a
  have hcB1 := halfCos_le_one (m := m) b
  have w1 := weight_le b (sizeI m (b - 2 * a))
  have w2 := weight_le b (sizeI m (b + 2 * a))
  have w3 := weight_le a (sizeI m (a - 2 * b))
  have w4 := weight_le a (sizeI m (a + 2 * b))
  have p1 := weight_pos b (sizeI m (b - 2 * a))
  have p2 := weight_pos b (sizeI m (b + 2 * a))
  have p3 := weight_pos a (sizeI m (a - 2 * b))
  have p4 := weight_pos a (sizeI m (a + 2 * b))
  unfold coeff
  rcases (show 2 * b = m ∨ 2 * b < m by omega) with hhalf | hhalf
  · -- `cos(π b / m) = 0`
    rw [halfCos_of_two_mul_eq hhalf]
    nlinarith
  rcases (show a = 0 ∨ 0 < a by omega) with ha | ha
  · -- `a = 0`: the neighbours of the first pair are the point itself
    subst ha
    have e1 : weight b (sizeI m (b - 2 * 0)) = 1 := by
      have : sizeI m (b - 2 * 0) = b := by size_tac (b - 2 * 0)
      rw [this, weight_self]
    have e2 : weight b (sizeI m (b + 2 * 0)) = 1 := by
      have : sizeI m (b + 2 * 0) = b := by size_tac (b + 2 * 0)
      rw [this, weight_self]
    have e3 : weight 0 (sizeI m (0 - 2 * b)) = 2 / 3 := weight_of_lt (by size_tac (0 - 2 * b))
    have e4 : weight 0 (sizeI m (0 + 2 * b)) = 2 / 3 := weight_of_lt (by size_tac (0 + 2 * b))
    rw [e1, e2, e3, e4, halfCos_zero]
    nlinarith
  rcases (show a = b ∨ a < b by omega) with hab' | hab'
  · subst hab'
    have e1 : weight a (sizeI m (a - 2 * a)) = 1 := by
      have : sizeI m (a - 2 * a) = a := by size_tac (a - 2 * a)
      rw [this, weight_self]
    rw [e1]
    rcases (show 4 * a < m ∨ m ≤ 4 * a by omega) with hq | hq
    · have e2 : weight a (sizeI m (a + 2 * a)) = 2 / 3 := weight_of_lt (by size_tac (a + 2 * a))
      rw [e2]
      nlinarith
    · have hs := halfCos_le_sqrt (m := m) hq (by omega)
      have hsqrt : Real.sqrt 2 < 3 / 2 := by
        rw [Real.sqrt_lt' (by norm_num)]; norm_num
      nlinarith
  rcases (show 2 * a + 2 * b < m ∨ m ≤ 2 * a + 2 * b by omega) with hs | hs
  · have e2 : weight b (sizeI m (b + 2 * a)) = 2 / 3 := weight_of_lt (by size_tac (b + 2 * a))
    have e3 : weight a (sizeI m (a - 2 * b)) = 2 / 3 := weight_of_lt (by size_tac (a - 2 * b))
    have e4 : weight a (sizeI m (a + 2 * b)) = 2 / 3 := weight_of_lt (by size_tac (a + 2 * b))
    rw [e2, e3, e4]
    nlinarith
  · have e3 : weight a (sizeI m (a - 2 * b)) = 2 / 3 := weight_of_lt (by size_tac (a - 2 * b))
    rw [e3]
    have hsin := halfCos_le_sin (m := m) h0 hs (by omega) hbm
    have hsc := Real.sin_sq_add_cos_sq (Real.pi * b / m)
    have hcs := cs_bound hsc
    have hcB : halfCos m b = Real.cos (Real.pi * b / m) := rfl
    rw [hcB] at hcB0 ⊢
    have hA : halfCos m a * (weight b (sizeI m (b - 2 * a)) + weight b (sizeI m (b + 2 * a)))
        ≤ 3 * Real.sin (Real.pi * b / m) := by
      have : weight b (sizeI m (b - 2 * a)) + weight b (sizeI m (b + 2 * a)) ≤ 3 := by linarith
      calc _ ≤ halfCos m a * 3 := mul_le_mul_of_nonneg_left this hcA0
        _ ≤ _ := by linarith
    have hB : Real.cos (Real.pi * b / m) * (2 / 3 + weight a (sizeI m (a + 2 * b)))
        ≤ 13 / 6 * Real.cos (Real.pi * b / m) := by nlinarith
    linarith

omit [NeZero m] in
lemma coeff_comm (a b : ℤ) : coeff m a b = coeff m b a := by
  unfold coeff; ring

/-- **The pointwise bound.** For sizes `0 ≤ a, b ≤ m/2`, not both `0`, the weighted sum
`coeff m a b` is at most `15/4`. -/
theorem coeff_le {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ham : 2 * a ≤ m) (hbm : 2 * b ≤ m)
    (hne : 0 < a ∨ 0 < b) : coeff m a b ≤ 15 / 4 := by
  rcases le_total a b with h | h
  · exact coeff_le_of_le ha h (by omega) hbm
  · rw [coeff_comm]
    exact coeff_le_of_le hb h (by omega) ham

end MinCostFlow.ExplicitExpander
