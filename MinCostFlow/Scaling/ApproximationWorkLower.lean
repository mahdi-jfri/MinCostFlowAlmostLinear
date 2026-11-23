module

public import MinCostFlow.Scaling.ApproximationModel

/-!
# Work that pays for approximation machine overhead

Each active threshold test already reserves linear work in its edge
count. Summing this through the finite search pays for canonical guest
setup. The approximation's own work also includes the search and at
least one operation beyond its edge count. These lower bounds let the
machine cost be charged directly to the model's counters.
-/

public section
namespace MinCostFlow.Scaling

private theorem rounds_calls_work {α : Type} (step : α → CallResult α) (M : ℕ)
    (hstep : ∀ a,(step a).calls.length*M≤(step a).work) (rounds : ℕ) (a : α) :
    (CallResult.forRounds step rounds a).calls.length*M≤(CallResult.forRounds step rounds a).work := by
  induction rounds with
  | zero => change (0 : ℕ)*M≤0; omega
  | succ rounds ih =>
    simp only [CallResult.forRounds,CallResult.bind,CallResult.charge,List.length_append,Nat.add_mul]
    have hs := hstep (CallResult.forRounds step rounds a).value
    omega

/-- Each actual threshold solve has linear work reserved in the search
counter, even when later iterations are inactive. -/
theorem bottleneckSearch_calls_mul_le_work (solve : (J : Circulation) → Fin J.m → ℤ)
    (J : Circulation) :
    (bottleneckSearch solve J).calls.length*(J.m+1)≤(bottleneckSearch solve J).work := by
  have hstep : ∀ s : BottleneckState J,
      (s.step solve (sortCapacities (List.ofFn J.capacity)).1).calls.length*(J.m+1)≤
        (s.step solve (sortCapacities (List.ofFn J.capacity)).1).work := by
    intro s
    unfold BottleneckState.step
    split <;> simp only [List.length_singleton,List.length_nil,Nat.one_mul,Nat.zero_mul] <;> omega
  have h := rounds_calls_work _ (J.m+1) hstep (Nat.clog 2 (J.m+1)) (⟨0,J.m,none⟩ : BottleneckState J)
  exact h.trans (by change _≤(sortCapacities (List.ofFn J.capacity)).2+_+J.m; omega)

/-- Approximation work contains all search work and exceeds the edge count. -/
theorem polyApproxModel_work_lower (solve : (J : Circulation) → Fin J.m → ℤ) (J : Circulation) :
    (bottleneckSearch solve J).work+1≤(polyApproxModel solve J).work ∧
      J.m+1≤(polyApproxModel solve J).work := by
  have hbase : J.m≤(bottleneckSearch solve J).work := by
    change J.m≤(sortCapacities (List.ofFn J.capacity)).2+_+J.m
    omega
  have hextra : (bottleneckSearch solve J).work+1≤(polyApproxModel solve J).work := by
    unfold polyApproxModel
    dsimp only
    split
    · dsimp only; omega
    · split <;> dsimp only <;> omega
  exact ⟨hextra,by omega⟩

end MinCostFlow.Scaling
