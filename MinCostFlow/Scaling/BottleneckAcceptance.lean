module

public import MinCostFlow.Scaling.BottleneckTest

/-!
# The binary search's actual acceptance predicate

The test in Lemma C.10 of Chen et al., arXiv:2203.00671v2, Appendix C,
accepts a threshold exactly when the integral solver output has negative
cost. The predicate below refers to that concrete computation. Its
monotonicity is derived from the bounded solver specification and retained
negative walks, rather than assumed as a separate algorithmic tool.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The objective sign computed by a threshold test. -/
def bottleneckAccepts (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (u : ℕ) : Prop :=
  (I.bottleneckGraph u).integerObjective (solveWithZeroCapacities solve (I.bottleneckGraph u)) < 0

/-- The computed acceptance predicate is monotone as the threshold decreases. -/
theorem bottleneckAccepts_mono (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (hc : I.CostsBounded (I.m ^ 10))
    (u v : ℕ) (huv : u ≤ v) (hv : I.bottleneckAccepts solve v) :
    I.bottleneckAccepts solve u := by
  have hoptv := I.bottleneckTest_optimal solve hsolve hc v
  have hoptu := I.bottleneckTest_optimal solve hsolve hc u
  have hneg := ((I.bottleneckGraph v).optimal_integer_negative_iff _ hoptv).mp hv
  exact ((I.bottleneckGraph u).optimal_integer_negative_iff _ hoptu).mpr
    (I.bottleneck_negative_mono u v huv hneg)

end MinCostFlow.Scaling.Circulation
