module

public import MinCostFlow.Scaling.CoefficientRounding
public import MinCostFlow.Scaling.CycleSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# A feasible rounded cycle-flow witness

The proof of Lemma C.12 in Appendix C of Chen et al., arXiv:2203.00671v2,
rounds every cycle coefficient down to a multiple of the capacity unit.
Even when cycles overlap, the total on an edge is a multiple of that unit
and does not increase. If the original flow is also below the clipping
threshold, the rounded total fits the corrected rounded capacity. This
supplies the missing aggregate feasibility argument in the source's proof.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation
variable {I : Circulation}

/-- Round the coefficients while retaining each cycle's vertices and edges. -/
noncomputable def roundCycleTerms (q : ℕ) (terms : List (CycleTerm I)) : List (CycleTerm I) :=
  terms.map (fun t => { t with amount := (roundCoefficient q t.amount : ℝ) })

/-- The sum in scaled integer units of the rounded cycle coefficients. -/
noncomputable def roundedCycleUnits (q : ℕ) (terms : List (CycleTerm I)) (e : Fin I.m) : ℕ :=
  (terms.map (fun t => ⌊t.amount / (q : ℝ)⌋₊ * t.walk.count e)).sum

/-- The rounded flow is an exact integer multiple of the unit at every edge. -/
theorem roundCycleTerms_flow (I : Circulation) (q : ℕ) (terms : List (CycleTerm I)) (e : Fin I.m) :
    I.cycleSum (roundCycleTerms q terms) e = (q * roundedCycleUnits q terms e : ℕ) := by
  simp only [cycleSum, roundCycleTerms, List.map_map, Function.comp_def, roundCoefficient,
    roundedCycleUnits, Nat.cast_mul, Nat.cast_list_sum]
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  ring

/-- Rounding coefficients down cannot increase any coordinate. -/
theorem roundCycleTerms_flow_le (I : Circulation) (q : ℕ) (hq : 0 < q)
    (terms : List (CycleTerm I)) (ht : ∀ t ∈ terms, 0 ≤ t.amount) (e : Fin I.m) :
    I.cycleSum (roundCycleTerms q terms) e ≤ I.cycleSum terms e := by
  induction terms with
  | nil => exact le_rfl
  | cons t terms ih =>
    have hh := ht t List.mem_cons_self
    have hi := ih (fun u hu => ht u (List.mem_cons_of_mem _ hu))
    have hc := mul_le_mul_of_nonneg_right (roundCoefficient_bounds q hq t.amount hh).1
      (Nat.cast_nonneg (α := ℝ) (t.walk.count e))
    change (roundCoefficient q t.amount : ℝ) * (t.walk.count e : ℝ) +
      I.cycleSum (roundCycleTerms q terms) e ≤ t.amount * (t.walk.count e : ℝ) + I.cycleSum terms e
    exact add_le_add hc hi

/-- Rounded cycle coefficients satisfy the corrected rounded capacities,
using aggregate edge bounds rather than separate per-cycle capacity checks. -/
theorem roundCycleTerms_feasible (I : Circulation) (B : ℕ) (terms : List (CycleTerm I))
    (ht : ∀ t ∈ terms, 0 ≤ t.amount)
    (hf : I.Feasible (I.cycleSum terms))
    (hclip : ∀ e, I.cycleSum terms e ≤ ((B * I.m ^ 20 : ℕ) : ℝ)) :
    (I.capacityRounded B).Feasible (I.cycleSum (roundCycleTerms (capacityUnit I.m B) terms)) := by
  let q := capacityUnit I.m B
  have hq : 0 < q := capacityUnit_pos _ _
  constructor
  · exact I.cycleSum_conserves _
  · intro e
    have hle := I.roundCycleTerms_flow_le q hq terms ht e
    rw [roundCycleTerms_flow I q terms e] at hle
    change 0 ≤ I.cycleSum (roundCycleTerms q terms) e ∧
      I.cycleSum (roundCycleTerms q terms) e ≤ ((I.capacityRounded B).capacity e : ℝ)
    rw [roundCycleTerms_flow I q terms e]
    have horig : q * roundedCycleUnits q terms e ≤ I.capacity e := by
      exact_mod_cast le_trans hle (hf.2 e).2
    have hclipped : q * roundedCycleUnits q terms e ≤ B * I.m ^ 20 := by
      exact_mod_cast le_trans hle (hclip e)
    have h1 : roundedCycleUnits q terms e ≤ I.capacity e / q :=
      (Nat.le_div_iff_mul_le hq).mpr (by simpa only [Nat.mul_comm] using horig)
    have h2 : roundedCycleUnits q terms e ≤ B * I.m ^ 20 / q :=
      (Nat.le_div_iff_mul_le hq).mpr (by simpa only [Nat.mul_comm] using hclipped)
    refine ⟨Nat.cast_nonneg _, ?_⟩
    exact_mod_cast Nat.mul_le_mul_left q (le_min h1 h2)

end MinCostFlow.Scaling.Circulation
