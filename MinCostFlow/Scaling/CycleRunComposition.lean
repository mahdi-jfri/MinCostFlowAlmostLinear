module

public import MinCostFlow.Scaling.CycleExtractionModel

/-!
# Composing finite cycle-scan runs

The proof of the negative-cycle scan in Lemma C.10 of Chen et al.,
arXiv:2203.00671v2, Appendix C, treats each closed-suffix peel as a group of
steps. The finite run's returned state composes across two fuel budgets.
A completed state remains unchanged, including when the scan stops early.
These identities concern the explicit loop rather than machine execution.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.CycleState
variable {I : Circulation}

/-- A completed extraction state remains unchanged under any remaining fuel. -/
theorem run_value_of_done (fuel : ℕ) (s : CycleState I) (hs : s.mode = .done) :
    (run fuel s).1 = s := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [run, hs, ↓reduceIte]

/-- Running two fuel budgets in sequence gives the same final state as their sum. -/
theorem run_value_add (first second : ℕ) (s : CycleState I) :
    (run (first + second) s).1 = (run second (run first s).1).1 := by
  induction first generalizing s with
  | zero => simp only [Nat.zero_add, run]
  | succ first ih =>
    by_cases hs : s.mode = .done
    · rw [run_value_of_done _ s hs, run_value_of_done _ s hs, run_value_of_done _ s hs]
    · simp only [Nat.succ_add, run, hs, ↓reduceIte]
      exact ih s.step

/-- Once a shorter run is complete, every longer budget has the same state. -/
theorem run_value_eq_of_done_prefix (first total : ℕ) (s : CycleState I)
    (hle : first ≤ total) (hdone : (run first s).1.mode = .done) :
    (run total s).1 = (run first s).1 := by
  have heq : total = first + (total - first) := by omega
  rw [heq, run_value_add]
  exact run_value_of_done _ _ hdone

end MinCostFlow.Scaling.Circulation.CycleState
