module

public import MinCostFlow.Scaling.LabelPotential
public import MinCostFlow.Scaling.ShortestRoutingPotential
public import MinCostFlow.Scaling.ShortestRoutingDemands
public import MinCostFlow.Scaling.StrongDuality
import Mathlib.Tactic.Ring

/-!
# Correctness of the computed residual dual potential

Lemma C.8 of Chen et al., arXiv:2203.00671v2, Appendix C, optimizes a rooted
routing by one residual circulation call and propagates labels in its positive
support. The routing has the prescribed unit demands and is no more costly
than the simple-shortest-path witness. The traversal therefore returns a
potential satisfying all original residual inequalities. The only solver
hypothesis below is optimality of the concrete circulation call it executes.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The extra circulation call in dual extraction yields the required
residual potential when its returned flow is optimal. -/
theorem extractDualModel_correct_of_optimal
    (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation) (f : Fin I.m → ℤ)
    (hf : I.Optimal (fun e => (f e : ℝ)))
    (hsolve : let R := I.residual f
      let Q := R.shortestRoutingGraph.residual R.shortestRoutingStart
      Q.Optimal (fun e => (solveWithZeroCapacities solve Q e : ℝ))) :
    ∀ e, 0 < (I.residual f).capacity e →
      (I.extractDualModel solve f).value ((I.residual f).tail e) -
        (I.extractDualModel solve f).value ((I.residual f).head e) ≤ (I.residual f).cost e := by
  let R := I.residual f
  let S := R.shortestRoutingGraph
  let start := R.shortestRoutingStart
  let Q := S.residual start
  let delta := solveWithZeroCapacities solve Q
  let routing : Fin S.m → ℤ := fun e => start e +
    delta (Fin.castAdd S.m e) - delta (Fin.natAdd S.m e)
  have hdelta : Q.Optimal (fun e => (delta e : ℝ)) := hsolve
  have hcast : (fun e => (routing e : ℝ)) = S.augment start (fun e => (delta e : ℝ)) := by
    funext e
    simp only [routing, augment, project, Int.cast_add, Int.cast_sub]
    ring
  have haug := S.augment_optimal_with_demands start R.shortestRoutingStart_bounds
    (fun e => (delta e : ℝ)) hdelta
  have hbalance : ∀ v, S.balance (fun e => (routing e : ℝ)) v =
      (S.n : ℝ) * (if v = Fin.last I.n then 1 else 0) - 1 := by
    intro v
    rw [hcast, haug.1 v]
    exact R.shortestRoutingStart_balance v
  have hbounds : ∀ e, 0 ≤ (routing e : ℝ) ∧ (routing e : ℝ) ≤ S.capacity e := by
    intro e
    rw [congrFun hcast e]
    exact haug.2.1 e
  have hopt : ∀ g : Fin S.m → ℝ,
      (∀ v, S.balance g v = (S.n : ℝ) * (if v = Fin.last I.n then 1 else 0) - 1) →
      (∀ e, 0 ≤ g e ∧ g e ≤ S.capacity e) →
      S.objective (fun e => (routing e : ℝ)) ≤ S.objective g := by
    intro g hb hg
    rw [hcast]
    apply haug.2.2 g _ hg
    intro v
    rw [hb, R.shortestRoutingStart_balance v]
  have hzero := I.zero_residual_optimal f hf
  have hclosed : ∀ v : Fin R.n, ∀ p : R.DirectedWalk v v, 0 ≤ p.cost :=
    fun _ p => p.cost_nonneg_of_zero_optimal hzero
  have hpot := S.propagateLabels_potential (Fin.last I.n)
    (R.shortestRoutingGraph_closed_nonneg hclosed) R.shortestRoutingGraph_reachable
    R.shortestRoutingGraph_active_capacity routing hbounds hbalance hopt
  intro e he
  have ha : 0 < S.capacity (Fin.castAdd R.n e) := by
    simp only [S, Fin.addCases_left]
    rw [ite_eq_left he]
    exact Nat.zero_lt_succ _
  have hh := hpot (Fin.castAdd R.n e) ha
  simp only [S, shortestRoutingGraph, Fin.addCases_left] at hh
  exact hh

end MinCostFlow.Scaling.Circulation
