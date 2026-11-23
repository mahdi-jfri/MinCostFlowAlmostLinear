module

public import MinCostFlow.Scaling.CycleExtractionModel
public import MinCostFlow.Scaling.ReverseWalkSplit

/-!
# Concrete stack frames for cycle extraction

The proof of the negative-cycle scan used in Lemma C.10 of Chen et al.,
arXiv:2203.00671v2, Appendix C, follows a simple path and then peels a
closed suffix. These data constructors spell out the corresponding integer
states: a walking path, a suffix being peeled, and the completed closed-part
test. They store no correctness or optimality assumptions.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.CycleState
variable {I : Circulation}

/-- Boolean membership table for the vertices currently on a path. -/
def markers (vertices : List (Fin I.n)) (v : Fin I.n) : Bool := decide (v ∈ vertices)

/-- A canonical walking state with no saved closed part. -/
def walkFrame (out : Fin I.n → List (Fin I.m)) (candidates : List (Fin I.m))
    {root current : Fin I.n} (p : I.ReverseWalk root current) : CycleState I where
  mode := .walk current
  outgoing := out
  candidates := candidates
  stack := p.edges
  onPath := markers p.vertices
  cycleEdges := []
  cycleCost := 0
  result := none

/-- A canonical choosing state between completed path components. -/
def chooseFrame (out : Fin I.n → List (Fin I.m)) (candidates : List (Fin I.m)) : CycleState I where
  mode := .choose
  outgoing := out
  candidates := candidates
  stack := []
  onPath := fun _ => false
  cycleEdges := []
  cycleCost := 0
  result := none

/-- A retained prefix, a remaining suffix, and the edges already peeled from it. -/
def peelFrame (out : Fin I.n → List (Fin I.m)) (candidates : List (Fin I.m))
    {root target current : Fin I.n} (p : I.ReverseWalk root target)
    (q : I.ReverseWalk target current) (saved : List (Fin I.m)) : CycleState I where
  mode := .peel target
  outgoing := out
  candidates := candidates
  stack := q.edges ++ p.edges
  onPath := markers (q.heads ++ p.vertices)
  cycleEdges := saved
  cycleCost := (saved.map I.cost).sum
  result := none

/-- A negative closed part finishes the scan; a nonnegative one resumes the prefix. -/
def finishPeelFrame (out : Fin I.n → List (Fin I.m)) (candidates : List (Fin I.m))
    {root target : Fin I.n} (p : I.ReverseWalk root target) (saved : List (Fin I.m)) : CycleState I :=
  if (saved.map I.cost).sum < 0 then
    { walkFrame out candidates p with mode := .done, cycleEdges := saved, cycleCost := (saved.map I.cost).sum, result := some saved }
  else walkFrame out candidates p

/-- Adding a vertex updates its membership flag to true. -/
theorem markers_cons (vertices : List (Fin I.n)) (v : Fin I.n) :
    Function.update (markers vertices) v true = markers (v :: vertices) := by
  funext w
  by_cases hw : w = v
  · subst w; simp [markers]
  · simp [markers, hw]

/-- Removing a distinct first vertex clears precisely its flag. -/
theorem markers_remove (vertices : List (Fin I.n)) (v : Fin I.n) (hv : v ∉ vertices) :
    Function.update (markers (v :: vertices)) v false = markers vertices := by
  funext w
  by_cases hw : w = v
  · subst w; simp [markers, hv]
  · simp [markers, hw]

end MinCostFlow.Scaling.Circulation.CycleState
