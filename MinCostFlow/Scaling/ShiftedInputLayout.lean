module

public import MinCostFlow.Scaling.FlowReduction
public import MinCostFlow.Scaling.SolverContract
public import MinCostFlow.Scaling.InputLayout
import Mathlib.Data.List.FinRange

/-!
# Layout of the lower-capacity reduction

The general-flow reduction in Lemma C.1 of Chen et al., arXiv:2203.00671v2,
keeps the original endpoints and costs and replaces a capacity interval by
its nonnegative width. This file identifies the resulting five-word records
with the exact `shiftedGraph` model and the common solver encoding.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine

/-- A lower-capacity-shifted edge in the common circulation layout. -/
def shiftedEdgeWords (e : Edge) : List ℕ :=
  [e.tail, e.head, (e.upper - e.lower).toNat,
    if e.cost < 0 then 1 else 0, e.cost.natAbs]

/-- Each transformed edge occupies five words. -/
theorem shiftedEdgeWords_length (e : Edge) : (shiftedEdgeWords e).length = 5 := rfl

/-- All transformed edge records occupy exactly five words per input edge. -/
theorem shiftedEdges_length (edges : List Edge) :
    (edges.flatMap shiftedEdgeWords).length = 5 * edges.length := by
  induction edges with
  | nil => rfl
  | cons e edges ih =>
    simp only [List.flatMap_cons, List.length_append, shiftedEdgeWords_length,
      List.length_cons, ih]
    omega

/-- Indexing the input edge list visits precisely its original order. -/
theorem instance_edges_finRange (I : Instance) :
    (List.finRange I.m).map I.edge = I.edges :=
  List.map_get_finRange I.edges

/-- The transformed records are exactly the common solver encoding of
`FlowReduction.shiftedGraph`, with the original two-word header. -/
theorem shiftedGraph_solverWords (I : Instance) (hv : I.IsValid) :
    (FlowReduction.shiftedGraph I hv).solverWords =
      I.n :: I.m :: I.edges.flatMap shiftedEdgeWords := by
  change I.n :: I.m :: (List.finRange I.m).flatMap (fun e => shiftedEdgeWords (I.edge e)) = _
  rw [← List.flatMap_map, instance_edges_finRange]

end MinCostFlow.Scaling.Machine
