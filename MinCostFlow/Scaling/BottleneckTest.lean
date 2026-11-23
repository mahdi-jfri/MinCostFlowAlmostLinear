module

public import MinCostFlow.Scaling.BottleneckSearch
public import MinCostFlow.Scaling.ZeroOptimality
public import MinCostFlow.Scaling.CapacityWalkMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Correctness and monotonicity of the bottleneck test

The binary search in Lemma C.10 of Chen et al., arXiv:2203.00671v2,
Appendix C, solves a unit-capacity circulation at each candidate threshold.
Its integral optimum is negative exactly when the threshold graph contains
a negative closed walk. Lowering the threshold retains every such walk.
The supplied solver is used only with its own polynomial input bounds.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The source's bounded primal specification suffices for each unit test. -/
theorem bottleneckTest_optimal (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (hc : I.CostsBounded (I.m ^ 10)) (u : ℕ) :
    (I.bottleneckGraph u).Optimal
      (fun e => (solveWithZeroCapacities solve (I.bottleneckGraph u) e : ℝ)) := by
  apply solveWithZeroCapacities_of_optimal
  apply hsolve
  · exact (I.bottleneckGraph u).positiveInstance_costsBounded _ hc
  · intro e
    have hh := (I.bottleneckGraph u).positiveInstance_capacitiesBounded 1 (by decide)
      (I.bottleneckGraph_capacities u) e
    have hm : 0 < I.m := by have he := e.isLt; change e.val < I.m at he; omega
    have hp : 0 < I.m ^ 40 := Nat.pow_pos hm
    exact ⟨hh.1, le_trans hh.2 (by change 1 ≤ I.m ^ 40; omega)⟩

/-- A returned integral optimum has negative objective exactly when a negative
closed walk exists in the active graph. -/
theorem optimal_integer_negative_iff (I : Circulation) (f : Fin I.m → ℤ)
    (hf : I.Optimal (fun e => (f e : ℝ))) :
    I.integerObjective f < 0 ↔
      ∃ v : Fin I.n, ∃ p : I.DirectedWalk v v, p.cost < 0 := by
  rw [← I.not_zero_optimal_iff_negative_closed]
  have hz : I.objective (fun _ => 0) = 0 := by simp only [objective, mul_zero, Finset.sum_const_zero]
  constructor
  · intro hneg hzero
    have hh := hzero.2 _ hf.1
    rw [hz, ← I.integerObjective_cast f] at hh
    have hi : ¬ I.integerObjective f < 0 := by exact_mod_cast (not_lt_of_ge hh)
    exact hi hneg
  · intro hnot
    by_contra hn
    have hi : 0 ≤ I.integerObjective f := le_of_not_gt hn
    have hr : (0 : ℝ) ≤ I.objective (fun e => (f e : ℝ)) := by
      rw [← I.integerObjective_cast]
      exact_mod_cast hi
    apply hnot
    refine ⟨I.zero_feasible, ?_⟩
    intro g hg
    rw [hz]
    exact le_trans hr (hf.2 g hg)

/-- Every negative closed walk retained at a high threshold remains at a lower one. -/
theorem bottleneck_negative_mono (I : Circulation) (u v : ℕ) (huv : u ≤ v)
    (hneg : ∃ w : Fin I.n, ∃ p : (I.bottleneckGraph v).DirectedWalk w w, p.cost < 0) :
    ∃ w : Fin I.n, ∃ p : (I.bottleneckGraph u).DirectedWalk w w, p.cost < 0 := by
  obtain ⟨w, p, hp⟩ := hneg
  have hactive : ∀ e, 0 < (I.bottleneckGraph v).capacity e →
      0 < (I.bottleneckGraph u).capacity e := by
    intro e he
    change 0 < if 0 < I.capacity e ∧ v ≤ I.capacity e then 1 else 0 at he
    split at he
    · rename_i hv
      change 0 < if 0 < I.capacity e ∧ u ≤ I.capacity e then 1 else 0
      rw [ite_eq_left ⟨hv.1, le_trans huv hv.2⟩]
      decide
    · contradiction
  let q := DirectedWalk.mapCapacities (I := I.bottleneckGraph v) (I.bottleneckGraph u).capacity hactive p
  refine ⟨w, q, ?_⟩
  have heq := DirectedWalk.cost_mapCapacities (I := I.bottleneckGraph v) (I.bottleneckGraph u).capacity hactive p
  exact lt_of_eq_of_lt heq hp

end MinCostFlow.Scaling.Circulation
