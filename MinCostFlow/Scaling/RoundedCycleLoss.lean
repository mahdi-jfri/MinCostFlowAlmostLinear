module

public import MinCostFlow.Scaling.RoundedCycleFlow
public import MinCostFlow.Scaling.SolverAdapter
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Objective loss from rounded cycle coefficients

The approximation calculation in Lemma C.12 used by Lemma C.9 of Chen et al.,
arXiv:2203.00671v2, Appendix C, loses less than one unit on each negative
cycle coefficient. Each simple cycle costs at least `-m^11`. Summing over at
most `m` cycles gives objective increase at most `q*m^12`, where `q` is the
capacity unit. This file proves that calculation for the actual floor rounding.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

private theorem rounded_term_loss (q : ℕ) (hq : 0 < q) (a cost M : ℝ)
    (ha : 0 ≤ a) (hc : cost ≤ 0) (hl : -M ≤ cost) :
    (roundCoefficient q a : ℝ) * cost ≤ a * cost + (q : ℝ) * M := by
  have hb := roundCoefficient_bounds q hq a ha
  have hd : a - (roundCoefficient q a : ℝ) ≤ q := by linarith only [hb.2]
  have h1 := mul_le_mul_of_nonneg_right hd (neg_nonneg.mpr hc)
  have h2 := mul_le_mul_of_nonneg_left (show -cost ≤ M by linarith only [hl]) (Nat.cast_nonneg q)
  calc
    (roundCoefficient q a : ℝ) * cost = a * cost +
        (a - (roundCoefficient q a : ℝ)) * (-cost) := by ring
    _ ≤ a * cost + (q : ℝ) * (-cost) := add_le_add le_rfl h1
    _ ≤ a * cost + (q : ℝ) * M := add_le_add le_rfl h2

/-- Rounding coefficients increases the objective by at most one unit times
`m^11` for each cycle. -/
theorem roundCycleTerms_objective_error (I : Circulation) (q : ℕ) (hq : 0 < q)
    (hc : I.CostsBounded (I.m ^ 10)) (terms : List (CycleTerm I))
    (ht : ∀ t ∈ terms, 0 ≤ t.amount ∧ t.walk.cost < 0 ∧ ∀ e, t.walk.count e ≤ 1) :
    I.objective (I.cycleSum (roundCycleTerms q terms)) ≤ I.objective (I.cycleSum terms) +
      (terms.length : ℝ) * ((q : ℝ) * ((I.m ^ 11 : ℕ) : ℝ)) := by
  have hlower (t : CycleTerm I) (ht : ∀ e, t.walk.count e ≤ 1) :
      -((I.m ^ 11 : ℕ) : ℝ) ≤ (t.walk.cost : ℝ) := by
    have he : ∀ e, -((I.m ^ 10 : ℕ) : ℤ) ≤ I.cost e := by
      intro e
      have hh := hc e
      omega
    have hh := t.cost_ge_neg_edges_mul ((I.m ^ 10 : ℕ) : ℤ) (Int.natCast_nonneg _) he ht
    have hpow : (I.m : ℤ) * ((I.m ^ 10 : ℕ) : ℤ) = ((I.m ^ 11 : ℕ) : ℤ) := by
      simp only [Nat.cast_pow]
      ring
    simp only [neg_mul] at hh
    rw [hpow] at hh
    exact_mod_cast hh
  rw [I.cycleSum_objective, I.cycleSum_objective]
  simp only [roundCycleTerms, List.map_map, Function.comp_def]
  induction terms with
  | nil => simp
  | cons t terms ih =>
    have hh := ht t List.mem_cons_self
    have hi := ih (fun u hu => ht u (List.mem_cons_of_mem _ hu))
    have hneg : (t.walk.cost : ℝ) ≤ 0 := by exact_mod_cast hh.2.1.le
    have hl := rounded_term_loss q hq t.amount (t.walk.cost : ℝ) ((I.m ^ 11 : ℕ) : ℝ)
      hh.1 hneg (hlower t hh.2.2)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith only [hi, hl]

/-- With at most `m` terms, the total loss is at most `q*m^12`. -/
theorem roundCycleTerms_objective_loss (I : Circulation) (q : ℕ) (hq : 0 < q)
    (hc : I.CostsBounded (I.m ^ 10)) (terms : List (CycleTerm I)) (hlen : terms.length ≤ I.m)
    (ht : ∀ t ∈ terms, 0 ≤ t.amount ∧ t.walk.cost < 0 ∧ ∀ e, t.walk.count e ≤ 1) :
    I.objective (I.cycleSum (roundCycleTerms q terms)) ≤ I.objective (I.cycleSum terms) +
      (q : ℝ) * ((I.m ^ 12 : ℕ) : ℝ) := by
  have hh := I.roundCycleTerms_objective_error q hq hc terms ht
  have hlen' : (terms.length : ℝ) ≤ I.m := Nat.cast_le.mpr hlen
  have hm := mul_le_mul_of_nonneg_right hlen'
    (mul_nonneg (Nat.cast_nonneg (α := ℝ) q) (Nat.cast_nonneg (α := ℝ) (I.m ^ 11)))
  have he : (I.m : ℝ) * ((q : ℝ) * ((I.m ^ 11 : ℕ) : ℝ)) =
      (q : ℝ) * ((I.m ^ 12 : ℕ) : ℝ) := by simp only [Nat.cast_pow]; ring
  rw [he] at hm
  exact le_trans hh (add_le_add le_rfl hm)

end MinCostFlow.Scaling.Circulation
