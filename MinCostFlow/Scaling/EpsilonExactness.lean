module

public import MinCostFlow.Scaling.EpsilonOptimal
public import MinCostFlow.Scaling.ShortNegativeWalk
public import MinCostFlow.Scaling.ResidualOptimality
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exactness at small epsilon

Lemma C.5 of Chen et al., arXiv:2203.00671v2, Appendix C, is the stopping
criterion in the proof of Lemma C.3. Every simple residual cycle has at most
`n` arcs. Its reduced cost is greater than `-n/(n+1)`, while its total cost is
an integer. It is therefore nonnegative. Shortening negative closed walks
extends this to all closed walks and yields an exact dual certificate.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Definition C.4 gives the reduced-cost bound on every active residual slot. -/
theorem epsilonOptimalWith_residual (I : Circulation) (f : Fin I.m → ℤ)
    (epsilon : ℝ) (y : Fin I.n → ℝ)
    (h : I.EpsilonOptimalWith (fun e => (f e : ℝ)) epsilon y) :
    ∀ e, 0 < (I.residual f).capacity e →
      -epsilon < (I.residual f).reducedCost y e := by
  intro e
  induction e using Fin.addCases
  · rename_i e
    intro ha
    simp only [Fin.addCases_left] at ha
    have hi : f e < (I.capacity e : ℤ) := by
      change 0 < ((I.capacity e : ℤ) - f e).toNat at ha
      have hh := Int.lt_toNat.mp ha
      omega
    have hr : (f e : ℝ) < I.capacity e := by exact_mod_cast hi
    simpa only [reducedCost, potentialDifference, Fin.addCases_left] using (h.2.2 e).1 hr
  · rename_i e
    intro ha
    simp only [Fin.addCases_right] at ha
    have hi : 0 < f e := by
      change 0 < (f e).toNat at ha
      exact Int.lt_toNat.mp ha
    have hr : 0 < (f e : ℝ) := by exact_mod_cast hi
    have hh := (h.2.2 e).2 hr
    simp only [reducedCost, potentialDifference, Fin.addCases_right, Int.cast_neg]
    dsimp only [reducedCost, potentialDifference] at hh
    linarith only [hh]

/-- Reduced costs telescope along a walk, so an arc bound gives a length bound. -/
theorem DirectedWalk.cost_sub_potential_ge {I : Circulation} {a b : Fin I.n}
    (p : I.DirectedWalk a b) (epsilon : ℝ) (y : Fin I.n → ℝ)
    (h : ∀ e, 0 < I.capacity e → -epsilon ≤ I.reducedCost y e) :
    -(p.length : ℝ) * epsilon ≤ (p.cost : ℝ) - (y a - y b) := by
  induction p with
  | nil =>
    simp only [DirectedWalk.length, DirectedWalk.cost, Nat.cast_zero,
      Int.cast_zero, sub_self, zero_mul, neg_zero]
    exact le_rfl
  | cons e he p ih =>
    have hh := h e he
    simp only [reducedCost, potentialDifference] at hh
    simp only [DirectedWalk.length, DirectedWalk.cost, Nat.cast_add, Nat.cast_one, Int.cast_add]
    linarith only [hh, ih]

/-- Lemma C.5 (Appendix C): an integral `1/(n+1)`-optimal circulation is an
exact minimizer, compared with all feasible real circulations. This supplies
the exactness step used by Lemma C.3. -/
theorem lemma_C_5 (I : Circulation) (f : Fin I.m → ℤ)
    (hf : I.EpsilonOptimal (fun e => (f e : ℝ)) (1 / ((I.n : ℝ) + 1))) :
    I.Optimal (fun e => (f e : ℝ)) := by
  obtain ⟨y, hy⟩ := hf
  apply I.optimal_of_residual_closed_nonneg f hy.2.1
  by_contra hn
  have hex : ∃ v : Fin I.n, ∃ p : (I.residual f).DirectedWalk v v, p.cost < 0 := by
    push Not at hn
    obtain ⟨v, p, hp⟩ := hn
    exact ⟨v, p, hp⟩
  obtain ⟨v, p, hp, hlen⟩ := DirectedWalk.exists_short_negative_closed (I := I.residual f) hex
  have he := I.epsilonOptimalWith_residual f _ y hy
  have hb := p.cost_sub_potential_ge (1 / ((I.n : ℝ) + 1)) y (fun e ha => (he e ha).le)
  simp only [sub_self, sub_zero] at hb
  have hlen' : (p.length : ℝ) ≤ I.n := by exact_mod_cast hlen
  have hnpos : (0 : ℝ) < (I.n : ℝ) + 1 := by positivity
  have hratio : (I.n : ℝ) / ((I.n : ℝ) + 1) < 1 :=
    (div_lt_one hnpos).mpr (by linarith)
  have heps : (0 : ℝ) ≤ 1 / ((I.n : ℝ) + 1) := (one_div_pos.mpr hnpos).le
  have hm := mul_le_mul_of_nonneg_right hlen' heps
  have hcost : (-1 : ℝ) < (p.cost : ℝ) := by
    simp only [mul_one_div] at hb hm
    rw [neg_div] at hb
    linarith only [hb, hm, hratio]
  have hi : (-1 : ℤ) < p.cost := by exact_mod_cast hcost
  omega

end MinCostFlow.Scaling.Circulation
