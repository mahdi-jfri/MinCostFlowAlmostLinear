module

public import MinCostFlow.Scaling.CycleExtractionModel

/-!
# Size of the cycle extraction result

The capacity-scaling reductions of Appendix C of Chen et al.,
arXiv:2203.00671v2, scatter the returned cycle into a flow vector. To count that
work, this file bounds the length of every returned list by the traversal's
fuel. Each step adds at most one edge to the saved closed part or result.
The sharper simple-cycle bound is part of the circulation correctness proof.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation
namespace CycleState

/-- Largest edge list currently saved as a closed part or completed result. -/
def storedSize {I : Circulation} (s : CycleState I) : ℕ :=
  max s.cycleEdges.length (s.result.getD []).length

/-- A step increases the largest saved list by at most one edge. -/
theorem step_storedSize {I : Circulation} (s : CycleState I) :
    s.step.storedSize ≤ s.storedSize + 1 := by
  cases s with
  | mk mode out candidates stack onPath edges cost result =>
    cases mode with
    | done => exact Nat.le_succ _
    | choose =>
      cases candidates with
      | nil => simp only [step, storedSize, Option.getD_none, List.length_nil]; omega
      | cons e rest =>
        simp only [step]
        split <;> simp only [storedSize, List.length_nil] <;> omega
    | walk v =>
      cases ho : out v with
      | nil => simp only [step, ho, storedSize]; omega
      | cons e rest =>
        simp only [step, ho]
        split <;> simp only [storedSize, List.length_nil] <;> omega
    | peel target =>
      cases stack with
      | nil => simp only [step, storedSize, Option.getD_none, List.length_nil]; omega
      | cons e rest =>
        simp only [step]
        split
        · split <;> simp only [storedSize, Option.getD_some, List.length_cons,
            List.length_nil] <;> omega
        · simp only [storedSize, List.length_cons]
          omega

/-- A finite run adds at most its fuel many entries to a saved list. -/
theorem run_storedSize {I : Circulation} (fuel : ℕ) (s : CycleState I) :
    (run fuel s).1.storedSize ≤ s.storedSize + fuel := by
  induction fuel generalizing s with
  | zero => exact le_rfl
  | succ fuel ih =>
    rw [run]
    split
    · dsimp only
      omega
    · dsimp only
      have h := ih s.step
      have hs := s.step_storedSize
      omega

end CycleState

/-- Any returned cycle list has at most `6*m+1` entries, so scattering it costs
linear work even before the simple-cycle correctness argument is used. -/
theorem extractCycleModel_result_length (I : Circulation) (flow : Fin I.m → ℤ)
    (es : List (Fin I.m)) (he : (I.extractCycleModel flow).1.result = some es) :
    es.length ≤ 6 * I.m + 1 := by
  have h := CycleState.run_storedSize (6 * I.m + 1) (I.cycleInitial flow)
  have hi : (I.cycleInitial flow).storedSize = 0 := rfl
  rw [hi, zero_add] at h
  have hs : es.length ≤ (I.extractCycleModel flow).1.storedSize := by
    unfold CycleState.storedSize
    rw [he, Option.getD_some]
    exact le_max_right _ _
  exact le_trans hs h

end MinCostFlow.Scaling.Circulation
