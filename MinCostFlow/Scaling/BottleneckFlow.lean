module

public import MinCostFlow.Scaling.BottleneckTest
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Feasibility of threshold-test flows in the original graph

The unit-capacity tests in Lemma C.10 of Chen et al., arXiv:2203.00671v2,
Appendix C, retain arcs whose original capacities meet the threshold. A
feasible test flow is also feasible in the original graph. Every positive
test-flow edge has original capacity at least the threshold. Integral test
flows have coordinates zero or one, as required by the proved cycle scan.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Positive test flow certifies that an edge survives the capacity threshold. -/
theorem bottleneckGraph_pos_flow (I : Circulation) (u : ℕ) (f : Fin I.m → ℝ)
    (hf : (I.bottleneckGraph u).Feasible f) (e : Fin I.m) (he : 0 < f e) :
    0 < I.capacity e ∧ u ≤ I.capacity e := by
  have hh := (hf.2 e).2
  by_contra hn
  change f e ≤ ((if 0 < I.capacity e ∧ u ≤ I.capacity e then 1 else 0 : ℕ) : ℝ) at hh
  rw [ite_eq_right hn, Nat.cast_zero] at hh
  linarith only [he, hh]

/-- Feasible test flow fits the original capacities and conserves the same demands. -/
theorem bottleneckGraph_feasible (I : Circulation) (u : ℕ) (f : Fin I.m → ℝ)
    (hf : (I.bottleneckGraph u).Feasible f) : I.Feasible f := by
  refine ⟨hf.1, ?_⟩
  intro e
  refine ⟨(hf.2 e).1, ?_⟩
  by_cases he : 0 < f e
  · have hh := I.bottleneckGraph_pos_flow u f hf e he
    have hunit : f e ≤ 1 := le_trans (hf.2 e).2
      (by exact_mod_cast I.bottleneckGraph_capacities u e)
    exact le_trans hunit (by exact_mod_cast hh.1)
  · have hz : f e = 0 := le_antisymm (le_of_not_gt he) (hf.2 e).1
    rw [hz]
    exact Nat.cast_nonneg _

/-- An integral feasible unit test has coordinates in `{0,1}`. -/
theorem bottleneckGraph_unit (I : Circulation) (u : ℕ) (f : Fin I.m → ℤ)
    (hf : (I.bottleneckGraph u).Feasible (fun e => (f e : ℝ))) :
    ∀ e, 0 ≤ f e ∧ f e ≤ 1 := by
  intro e
  have hunit : (f e : ℝ) ≤ 1 := le_trans (hf.2 e).2
    (by exact_mod_cast I.bottleneckGraph_capacities u e)
  exact ⟨Int.cast_nonneg_iff.mp (hf.2 e).1, by exact_mod_cast hunit⟩

end MinCostFlow.Scaling.Circulation
