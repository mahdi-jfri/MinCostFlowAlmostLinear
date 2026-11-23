module

public import MinCostFlow.Scaling.WalkEdgeLists
public import MinCostFlow.Scaling.RemainingAdjacencyFlow
import Mathlib.Tactic.Linarith

/-!
# No premature dead ends in the unit-flow scan

The negative-cycle extraction of Lemma C.10 of Chen et al.,
arXiv:2203.00671v2, Appendix C, follows unused positive-flow arcs. While its
stack is a path from `root` to `current`, unused flow has balance one at
`current` and minus one at `root`. An empty outgoing list therefore forces
`current=root`. A simple closed stack path is empty, so ending a component
does not discard an open path. This is the source's unit-flow balance argument.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.ReverseWalk
variable {I : Circulation} {a b : Fin I.n}

/-- Counts of a stack walk have the usual endpoint balance. -/
theorem balance_count (p : I.ReverseWalk a b) (v : Fin I.n) :
    I.balance (fun e => (p.count e : ℝ)) v =
      (if v = a then 1 else 0) - (if v = b then 1 else 0) := by
  have hh := p.toDirectedWalk.balance_count v
  simpa only [p.count_toDirectedWalk] using hh

/-- At a dead end the current stack is a closed empty simple path. -/
theorem edges_nil_of_no_outgoing (p : I.ReverseWalk a b) (hp : p.vertices.Nodup)
    (out : Fin I.n → List (Fin I.m)) (hout : out b = [])
    (hbalance : ∀ v, I.balance (I.adjacencyFlow out) v =
      (if v = b then 1 else 0) - (if v = a then 1 else 0)) :
    b = a ∧ p.edges = [] := by
  have hnon := I.adjacencyFlow_balance_nonpos out b hout
  have hb := hbalance b
  have heq : b = a := by
    by_contra hn
    simp only [↓reduceIte, hn, sub_zero] at hb
    linarith only [hb, hnon]
  subst b
  exact ⟨rfl, p.edges_eq_nil_of_nodup_closed hp⟩

end MinCostFlow.Scaling.Circulation.ReverseWalk
