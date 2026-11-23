module

public import MinCostFlow.Scaling.CycleExtractionModel
public import MinCostFlow.Scaling.SolverAdapter
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Word and length bounds for the cycle traversal

Only peeling adds an edge cost to the running cycle cost. Starting a new
walk or discarding a nonnegative closed part resets the sum to zero.
Thus every permitted step increases its magnitude budget by at most one
edge-cost bound. These estimates justify one-word signed arithmetic.
The remaining-work potential never increases, so it also bounds every
outgoing length throughout the traversal.
-/

public section
namespace MinCostFlow.Scaling.Circulation.CycleState

/-- One cycle-scan step needs at most the previous magnitude budget plus
one edge-cost magnitude. -/
theorem step_cost_bound {J : Circulation} (s : CycleState J) (B C : ℕ)
    (hs : s.cycleCost.natAbs≤B) (hc : J.CostsBounded C) :
    s.step.cycleCost.natAbs≤B+C := by
  have hretain : s.cycleCost.natAbs≤B+C := hs.trans (Nat.le_add_right B C)
  cases hm : s.mode with
  | done => simpa only [step,hm] using hretain
  | choose =>
    cases hcan : s.candidates with
    | nil => simpa only [step,hm,hcan] using hretain
    | cons e es =>
      simp only [step,hm,hcan]
      split
      · exact hretain
      · exact Nat.zero_le _
  | walk v =>
    cases hout : s.outgoing v with
    | nil => simpa only [step,hm,hout] using hretain
    | cons e es =>
      simp only [step,hm,hout]
      split
      · exact Nat.zero_le _
      · exact hretain
  | peel target =>
    cases hstack : s.stack with
    | nil => simpa only [step,hm,hstack] using hretain
    | cons e es =>
      have hadd : (s.cycleCost+J.cost e).natAbs≤B+C :=
        (Int.natAbs_add_le _ _).trans (Nat.add_le_add hs (hc e))
      simp only [step,hm,hstack]
      split
      · split
        · exact hadd
        · exact Nat.zero_le _
      · exact hadd

/-- The complete bounded traversal fits the initial cost budget plus one
edge-cost budget per permitted step. -/
theorem run_cost_bound {J : Circulation} (fuel : ℕ) (s : CycleState J) (B C : ℕ)
    (hs : s.cycleCost.natAbs≤B) (hc : J.CostsBounded C) :
    (run fuel s).1.cycleCost.natAbs≤B+fuel*C := by
  induction fuel generalizing s B with
  | zero => simpa only [run,Nat.zero_mul,Nat.add_zero] using hs
  | succ fuel ih =>
    rw [run]
    split
    · exact hs.trans (Nat.le_add_right _ _)
    · have h := ih s.step (B+C) (step_cost_bound s B C hs hc)
      dsimp only
      rw [Nat.succ_mul]
      omega

/-- A step never increases the model's remaining-work potential, including
steps that enter done mode. -/
theorem step_potential_le {J : Circulation} (s : CycleState J) : s.step.potential≤s.potential := by
  cases hm : s.mode with
  | done => simp only [step,hm]; exact le_rfl
  | choose =>
    cases hcan : s.candidates with
    | nil => simp only [step,hm,hcan,potential,rank,List.length_nil]; exact le_rfl
    | cons e es =>
      simp only [step,hm,hcan]
      split <;> simp only [potential,rank,hm,hcan,List.length_cons,List.length_nil] <;> omega
  | walk v =>
    cases hout : s.outgoing v with
    | nil => simp only [step,hm,hout,potential,rank,List.length_nil]; omega
    | cons e es =>
      have hu := J.adjacencyMass_update s.outgoing v es
      rw [hout,List.length_cons] at hu
      simp only [step,hm,hout]
      split <;> simp only [potential,rank,hm,List.length_cons] <;> omega
  | peel target =>
    cases hstack : s.stack with
    | nil => simp only [step,hm,hstack,potential,rank,List.length_nil]; omega
    | cons e es =>
      simp only [step,hm,hstack]
      split
      · split <;> simp only [potential,rank,hm,hstack,List.length_cons] <;> omega
      · simp only [potential,rank,hm,hstack,List.length_cons]; omega

/-- Every counted run keeps the initial potential as a common length budget. -/
theorem run_potential_le {J : Circulation} (fuel : ℕ) (s : CycleState J) :
    (run fuel s).1.potential≤s.potential := by
  induction fuel generalizing s with
  | zero => exact le_rfl
  | succ fuel ih =>
    rw [run]
    split
    · exact le_rfl
    · exact (ih s.step).trans s.step_potential_le

/-- Each stored outgoing length is covered by the same state budget. -/
theorem outgoing_length_le_potential {J : Circulation} (s : CycleState J) (v : Fin J.n) :
    (s.outgoing v).length≤s.potential := by
  have h : (s.outgoing v).length≤J.adjacencyMass s.outgoing :=
    Finset.single_le_sum (f := fun u : Fin J.n => (s.outgoing u).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  unfold potential
  omega

end MinCostFlow.Scaling.Circulation.CycleState
