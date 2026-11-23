module

public import MinCostFlow.Scaling.ShortestRoutingModel
public import MinCostFlow.Scaling.RootedShortestPaths
public import MinCostFlow.Scaling.EpsilonExactness
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# A feasible potential for the shortest-routing graph

In Lemma C.8 of Chen et al., arXiv:2203.00671v2, Appendix C, the graph has
no negative cycles before the super-source is added. Shift its integral
potential to be nonnegative, then give the source potential zero. Every
new source arc has zero cost and nonnegative reduced cost. Consequently
closed walks in the enlarged graph remain nonnegative, and shortest rooted
paths exist to all vertices.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- A feasible integral potential can be shifted to be nonnegative. -/
theorem exists_nonnegative_potential (I : Circulation)
    (hclosed : ∀ v : Fin I.n, ∀ p : I.DirectedWalk v v, 0 ≤ p.cost) :
    ∃ y : Fin I.n → ℤ, (∀ v, 0 ≤ y v) ∧
      ∀ e, 0 < I.capacity e → y (I.tail e) - y (I.head e) ≤ I.cost e := by
  obtain ⟨y, hy⟩ := I.exists_potential_of_closed_nonneg hclosed
  let M : ℤ := ∑ v, |y v|
  refine ⟨fun v => y v + M, ?_, ?_⟩
  · intro v
    have hh : |y v| ≤ M := Finset.single_le_sum
      (fun w _ => abs_nonneg (y w)) (Finset.mem_univ v)
    have hl := neg_abs_le (y v)
    change 0 ≤ y v + M
    omega
  · intro e he
    have hh := hy e he
    dsimp only
    omega

/-- Adding the zero-cost source preserves the absence of negative closed walks. -/
theorem shortestRoutingGraph_closed_nonneg (I : Circulation)
    (hclosed : ∀ v : Fin I.n, ∀ p : I.DirectedWalk v v, 0 ≤ p.cost) :
    ∀ v : Fin I.shortestRoutingGraph.n,
      ∀ p : I.shortestRoutingGraph.DirectedWalk v v, 0 ≤ p.cost := by
  obtain ⟨y, hnon, hy⟩ := I.exists_nonnegative_potential hclosed
  let Y : Fin (I.n + 1) → ℤ := Fin.lastCases 0 y
  have he : ∀ e, 0 < I.shortestRoutingGraph.capacity e →
      Y (I.shortestRoutingGraph.tail e) - Y (I.shortestRoutingGraph.head e) ≤
        I.shortestRoutingGraph.cost e := by
    intro e
    induction e using Fin.addCases
    · rename_i e
      intro ha
      simp only [Fin.addCases_left] at ha
      have hp : 0 < I.capacity e := by
        change 0 < if 0 < I.capacity e then I.n + 1 else 0 at ha
        split at ha
        · assumption
        · contradiction
      simpa only [Y, Fin.addCases_left, Fin.lastCases_castSucc] using hy e hp
    · rename_i v
      intro _
      simp only [Y, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, zero_sub]
      exact neg_nonpos.mpr (hnon v)
  intro v p
  have hh := p.cost_sub_potential_ge 0 (fun v => (Y v : ℝ)) (by
    intro e ha
    have hi := he e ha
    have hr : (Y (I.shortestRoutingGraph.tail e) : ℝ) -
        (Y (I.shortestRoutingGraph.head e) : ℝ) ≤ (I.shortestRoutingGraph.cost e : ℝ) := by
      exact_mod_cast hi
    dsimp only [reducedCost, potentialDifference]
    linarith only [hr])
  simp only [mul_zero, sub_self, sub_zero] at hh
  exact Int.cast_nonneg_iff.mp hh

/-- The new source reaches each vertex by a zero-cost direct arc. -/
theorem shortestRoutingGraph_reachable (I : Circulation) :
    ∀ v : Fin I.shortestRoutingGraph.n,
      Nonempty (I.shortestRoutingGraph.DirectedWalk (Fin.last I.n) v) := by
  intro v
  refine Fin.lastCases ?_ (fun v => ?_) v
  · exact ⟨DirectedWalk.nil (I := I.shortestRoutingGraph) (Fin.last I.n)⟩
  · have ha : 0 < I.shortestRoutingGraph.capacity (Fin.natAdd I.m v) := by
      simp only [Fin.addCases_right]
      exact Nat.zero_lt_succ _
    have p := DirectedWalk.cons (I := I.shortestRoutingGraph) (Fin.natAdd I.m v) ha
      (DirectedWalk.nil (I := I.shortestRoutingGraph)
        (I.shortestRoutingGraph.head (Fin.natAdd I.m v)))
    exact ⟨by simpa only [Fin.addCases_right] using p⟩

end MinCostFlow.Scaling.Circulation
