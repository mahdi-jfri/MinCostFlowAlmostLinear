module

public import MinCostFlow.Scaling.PeelFrameRun
public import MinCostFlow.Scaling.CycleRunComposition

/-!
# Entering and completing a repeated-vertex peel

The scan used in Lemma C.10 of Chen et al., arXiv:2203.00671v2,
Appendix C, recognizes an edge back to a visited path vertex. Its first
step pushes that edge; its next step moves it to the saved closed part.
The remaining suffix then peels by the proved frame identity. The complete
state agrees exactly with testing that suffix's closed edge list.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.CycleState
variable {I : Circulation} {root : Fin I.n}

/-- The first two repeated-vertex steps either close a loop or enter the
canonical partial peel with the back edge already saved. -/
theorem walk_repeat_two_steps (out : Fin I.n → List (Fin I.m)) (candidates : List (Fin I.m))
    (e : Fin I.m) (rest : List (Fin I.m)) (ho : out (I.tail e) = e :: rest)
    (path : I.ReverseWalk root (I.tail e)) (hseen : I.head e ∈ path.vertices)
    (p : I.ReverseWalk root (I.head e)) (q : I.ReverseWalk (I.head e) (I.tail e))
    (hedges : path.edges = q.edges ++ p.edges)
    (hvertices : path.vertices = q.heads ++ p.vertices) (hq : q.vertices.Nodup) :
    (walkFrame out candidates path).step.step =
      if I.tail e = I.head e then
        finishPeelFrame (Function.update out (I.tail e) rest) candidates p [e]
      else peelFrame (Function.update out (I.tail e) rest) candidates p q [e] := by
  have hflag : markers path.vertices (I.head e) = true := decide_eq_true hseen
  simp only [walkFrame, step, ho, hflag, ↓reduceIte]
  by_cases ht : I.tail e = I.head e
  · have hqnil : q.edges = [] := by
      exact q.edges_nil_of_nodup_end_eq hq ht
    have hheads : q.heads = [] := by simp only [ReverseWalk.heads, hqnil, List.map_nil]
    simp only [ht, ↓reduceIte, hedges, hvertices, hqnil, hheads, List.nil_append,
      finishPeelFrame, walkFrame, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Int.add_zero, Int.zero_add]
  · simp only [ht, ↓reduceIte, hedges, hvertices, peelFrame,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero, Int.zero_add]

/-- The complete repeated-vertex phase takes two setup steps and one step
per old suffix edge, yielding exactly its closed-list test. -/
theorem run_walk_repeat (out : Fin I.n → List (Fin I.m)) (candidates : List (Fin I.m))
    (e : Fin I.m) (rest : List (Fin I.m)) (ho : out (I.tail e) = e :: rest)
    (path : I.ReverseWalk root (I.tail e)) (hseen : I.head e ∈ path.vertices)
    (p : I.ReverseWalk root (I.head e)) (q : I.ReverseWalk (I.head e) (I.tail e))
    (hedges : path.edges = q.edges ++ p.edges)
    (hvertices : path.vertices = q.heads ++ p.vertices) (hq : q.vertices.Nodup)
    (hdisj : ∀ v ∈ q.heads, v ∉ p.vertices) :
    (run (2 + q.edges.length) (walkFrame out candidates path)).1 =
      finishPeelFrame (Function.update out (I.tail e) rest) candidates p
        (q.toDirectedWalk.edges ++ [e]) := by
  have hs := walk_repeat_two_steps out candidates e rest ho path hseen p q hedges hvertices hq
  have hflag : markers path.vertices (I.head e) = true := decide_eq_true hseen
  have htwo : (run 2 (walkFrame out candidates path)).1 = (walkFrame out candidates path).step.step := by
    simp only [run, walkFrame, step, ho, hflag, reduceCtorEq, ↓reduceIte]
  rw [run_value_add, htwo, hs]
  by_cases ht : I.tail e = I.head e
  · rw [ite_eq_left ht]
    have hqnil : q.edges = [] := by
      exact q.edges_nil_of_nodup_end_eq hq ht
    have hforward : q.toDirectedWalk.edges = [] := by rw [q.edges_toDirectedWalk, hqnil, List.reverse_nil]
    simp only [hqnil, hforward, List.length_nil, run, List.nil_append]
  · rw [ite_eq_right ht]
    apply run_peelFrame _ _ p q [e] hq hdisj
    intro hz
    exact ht (q.end_eq_start_of_edges_nil hz)

end MinCostFlow.Scaling.Circulation.CycleState
