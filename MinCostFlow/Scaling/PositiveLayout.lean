module

public import MinCostFlow.Scaling.PositiveEdges
public import MinCostFlow.Scaling.SolverContract
import Mathlib.Data.List.FinRange

/-!
# The solver layout after deleting zero-capacity slots

The reductions of Lemma C.1 of Chen et al., arXiv:2203.00671v2, remove zero
capacity edges before calling the circulation scaling loops. The model's
retained indices stay in original order. This file identifies the compacted
record list with the common solver encoding of `withoutZeroEdges`.
-/

public section
namespace MinCostFlow.Scaling.Machine

/-- The retained-index map visits the positive-capacity indices in order. -/
theorem positiveIndex_finRange (J : Circulation) :
    (List.finRange J.positiveEdges.length).map J.positiveIndex = J.positiveEdges :=
  List.map_get_finRange J.positiveEdges

/-- Pruning changes the edge-count header and keeps exactly the selected
original five-word records. -/
theorem withoutZeroEdges_solverWords (J : Circulation) :
    J.withoutZeroEdges.solverWords = J.n :: J.positiveEdges.length ::
      J.positiveEdges.flatMap J.solverEdgeWords := by
  change J.n :: J.positiveEdges.length ::
    (List.finRange J.positiveEdges.length).flatMap (fun e => J.solverEdgeWords (J.positiveIndex e)) = _
  rw [← List.flatMap_map, positiveIndex_finRange]

end MinCostFlow.Scaling.Machine
