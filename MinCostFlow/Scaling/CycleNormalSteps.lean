module

public import MinCostFlow.Scaling.CycleFrames

/-!
# Normal steps of the unit-flow cycle scan

The extraction used by Lemma C.10 of Chen et al., arXiv:2203.00671v2,
Appendix C, either chooses a new component, extends a simple path, or ends
an empty path. These exact identities connect the explicit integer states
with the canonical frames used in the correctness proof. Repeated-vertex
phases are handled separately by the proved peel-run identity.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.CycleState
variable {I : Circulation}

/-- A membership table for the empty list has all flags false. -/
theorem markers_nil : (markers ([] : List (Fin I.n))) = fun _ => false := by
  funext v
  simp only [markers, List.not_mem_nil, decide_false]

/-- Choosing a candidate with no remaining outgoing edge skips that candidate. -/
theorem chooseFrame_skip (out : Fin I.n → List (Fin I.m)) (e : Fin I.m)
    (rest : List (Fin I.m)) (ho : out (I.tail e) = []) :
    (chooseFrame out (e :: rest)).step = chooseFrame out rest := by
  simp only [chooseFrame, step, ho, ↓reduceIte]

/-- A candidate with unused outgoing edges starts a path at its tail. -/
theorem chooseFrame_start (out : Fin I.n → List (Fin I.m)) (e : Fin I.m)
    (rest : List (Fin I.m)) (ho : out (I.tail e) ≠ []) :
    (chooseFrame out (e :: rest)).step =
      walkFrame out rest (ReverseWalk.nil (I := I) (I.tail e)) := by
  simp only [chooseFrame, step, ho, ↓reduceIte, walkFrame, ReverseWalk.edges, ReverseWalk.vertices]
  have hm : Function.update (fun _ : Fin I.n => false) (I.tail e) true = markers [I.tail e] := by
    rw [← markers_nil, markers_cons]
  rw [hm]

/-- Following an unvisited head extends the canonical stack path. -/
theorem walkFrame_extend (out : Fin I.n → List (Fin I.m)) (candidates : List (Fin I.m))
    {root : Fin I.n} (e : Fin I.m) (rest : List (Fin I.m))
    (p : I.ReverseWalk root (I.tail e)) (he : 0 < I.capacity e)
    (ho : out (I.tail e) = e :: rest) (hhead : I.head e ∉ p.vertices) :
    (walkFrame out candidates p).step =
      walkFrame (Function.update out (I.tail e) rest) candidates (ReverseWalk.snoc e he p) := by
  have hh : markers p.vertices (I.head e) = false := decide_eq_false hhead
  simp only [walkFrame, step, ho, hh, Bool.false_eq_true, ↓reduceIte,
    ReverseWalk.edges, ReverseWalk.vertices]
  rw [markers_cons]

/-- Ending a path with empty stack and only its endpoint marked gives the
canonical choosing frame, including clearing the final path flag. -/
theorem walkFrame_end (out : Fin I.n → List (Fin I.m)) (candidates : List (Fin I.m))
    {root current : Fin I.n} (p : I.ReverseWalk root current)
    (ho : out current = []) (he : p.edges = []) (hv : p.vertices = [current]) :
    (walkFrame out candidates p).step = chooseFrame out candidates := by
  simp only [walkFrame, step, ho, he, hv, chooseFrame]
  rw [markers_remove [] current (by simp), markers_nil]

end MinCostFlow.Scaling.Circulation.CycleState
