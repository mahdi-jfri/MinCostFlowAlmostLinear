module

public import MinCostFlow.Scaling.CycleExtractionModel

/-!
# The cycle extractor's accumulated integer cost

The unit-flow reduction in Lemma C.10 of Chen et al., arXiv:2203.00671v2,
Appendix C, returns a closed part only when its integer cost is negative.
This file verifies the cost bookkeeping in the actual extraction loop:
the accumulated cost equals the sum over saved edges at every step, and
every returned list has negative cost.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.CycleState
variable {I : Circulation}

/-- Every step preserves exact agreement between the cost accumulator and
its saved edge list. -/
theorem step_cycleCost (s : CycleState I)
    (hc : s.cycleCost = (s.cycleEdges.map I.cost).sum) :
    s.step.cycleCost = (s.step.cycleEdges.map I.cost).sum := by
  cases s with
  | mk mode out candidates stack onPath edges cost result =>
    cases mode with
    | done => exact hc
    | choose =>
      cases candidates with
      | nil => exact hc
      | cons e rest =>
        simp only [step]
        split
        · exact hc
        · rfl
    | walk v =>
      cases ho : out v with
      | nil => simpa only [step, ho] using hc
      | cons e rest =>
        simp only [step, ho]
        split
        · rfl
        · exact hc
    | peel target =>
      cases stack with
      | nil => exact hc
      | cons e rest =>
        simp only [step]
        split
        · split
          · dsimp only
            simp only [List.map_cons, List.sum_cons]
            dsimp only at hc
            omega
          · rfl
        · dsimp only
          simp only [List.map_cons, List.sum_cons]
          dsimp only at hc
          omega

/-- An extraction step creates a new result only with a strictly negative cost. -/
theorem step_result_negative (s : CycleState I)
    (hc : s.cycleCost = (s.cycleEdges.map I.cost).sum)
    (hr : ∀ es, s.result = some es → (es.map I.cost).sum < 0) :
    ∀ es, s.step.result = some es → (es.map I.cost).sum < 0 := by
  cases s with
  | mk mode out candidates stack onPath edges cost result =>
    cases mode with
    | done => exact hr
    | choose =>
      cases candidates with
      | nil => intro es he; cases he
      | cons e rest =>
        simp only [step]
        split <;> exact hr
    | walk v =>
      cases ho : out v with
      | nil => simpa only [step, ho] using hr
      | cons e rest =>
        simp only [step, ho]
        split <;> exact hr
    | peel target =>
      cases stack with
      | nil => intro es he; cases he
      | cons e rest =>
        simp only [step]
        split
        · split
          · rename_i hneg
            intro es he
            have heq : e :: edges = es := Option.some.inj he
            subst es
            simp only [List.map_cons, List.sum_cons]
            dsimp only at hc hneg
            omega
          · exact hr
        · exact hr

/-- The finite extraction run preserves exact cost bookkeeping and negative results. -/
theorem run_cost (fuel : ℕ) (s : CycleState I)
    (hc : s.cycleCost = (s.cycleEdges.map I.cost).sum)
    (hr : ∀ es, s.result = some es → (es.map I.cost).sum < 0) :
    (run fuel s).1.cycleCost = ((run fuel s).1.cycleEdges.map I.cost).sum ∧
      ∀ es, (run fuel s).1.result = some es → (es.map I.cost).sum < 0 := by
  induction fuel generalizing s with
  | zero => exact ⟨hc, hr⟩
  | succ fuel ih =>
    rw [run]
    split
    · exact ⟨hc, hr⟩
    · exact ih s.step (s.step_cycleCost hc) (s.step_result_negative hc hr)

end MinCostFlow.Scaling.Circulation.CycleState

namespace MinCostFlow.Scaling.Circulation

/-- Every edge list returned by the concrete cycle extractor has negative
integral cost. Closure and nonrepetition are proved by its path invariant. -/
theorem extractCycleModel_negative (I : Circulation) (flow : Fin I.m → ℤ)
    (es : List (Fin I.m)) (he : (I.extractCycleModel flow).1.result = some es) :
    (es.map I.cost).sum < 0 := by
  have hh := CycleState.run_cost (6 * I.m + 1) (I.cycleInitial flow) rfl
    (fun _ h => by cases h)
  exact hh.2 es he

end MinCostFlow.Scaling.Circulation
