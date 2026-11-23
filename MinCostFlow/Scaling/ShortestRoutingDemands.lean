module

public import MinCostFlow.Scaling.ShortestRoutingModel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Demands and capacities of the shortest-routing instance

The direct source arcs in Lemma C.8 of Chen et al., arXiv:2203.00671v2,
Appendix C, route one unit to each old vertex. Their balance is `n` at the
source and minus one elsewhere. Every active slot has capacity `n+1`, so the
sum of simple shortest paths fits the finite model of uncapacitated routing.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The direct starting routing has exactly the source's unit demands. -/
theorem shortestRoutingStart_balance (I : Circulation) (w : Fin (I.n + 1)) :
    I.shortestRoutingGraph.balance (fun e => (I.shortestRoutingStart e : ℝ)) w =
      ((I.n + 1 : ℕ) : ℝ) * (if w = Fin.last I.n then 1 else 0) - 1 := by
  classical
  unfold balance
  rw [Fin.sum_univ_add]
  simp only [shortestRoutingStart, Fin.addCases_left, Fin.addCases_right,
    Int.cast_zero, Int.cast_one, mul_zero, mul_one, Finset.sum_const_zero, zero_add]
  simp only [incidence, Fin.addCases_right]
  change (∑ v : Fin I.n, ((if w = Fin.last I.n then 1 else 0 : ℝ) -
    (if w = v.castSucc then 1 else 0))) = _
  rw [Finset.sum_sub_distrib]
  refine Fin.lastCases ?_ (fun v => ?_) w
  · simp
    intro x hx
    have hh := congrArg Fin.val hx
    simp only [Fin.val_last, Fin.val_castSucc] at hh
    omega
  · simp

/-- All active slots have capacity equal to the enlarged graph's vertex count. -/
theorem shortestRoutingGraph_active_capacity (I : Circulation) :
    ∀ e, I.shortestRoutingGraph.capacity e = 0 ∨
      I.shortestRoutingGraph.n ≤ I.shortestRoutingGraph.capacity e := by
  intro e
  induction e using Fin.addCases
  · rename_i e
    simp only [Fin.addCases_left]
    split
    · exact Or.inr le_rfl
    · exact Or.inl rfl
  · simp only [Fin.addCases_right]
    exact Or.inr le_rfl

end MinCostFlow.Scaling.Circulation
