module

public import MinCostFlow.Scaling.SolverContract
public import MinCostFlow.Scaling.PositiveCapacities

/-!
# Records of the positive-capacity solver adapter

The zero-capacity adapter retains every edge slot. Each inactive slot is
replaced by a zero-cost unit-capacity loop at the new isolated vertex.
This file identifies both branches in the shared five-word layout, so the
machine scan can copy active records and write the fixed inactive record.
-/

public section
namespace MinCostFlow.Scaling.Machine

/-- An inactive slot becomes a canonical zero-cost loop at vertex `n`. -/
theorem positiveInstance_edgeWords_zero (J : Circulation) (e : Fin J.m)
    (he : J.capacity e = 0) : J.positiveInstance.solverEdgeWords e = [J.n, J.n, 1, 0, 0] := by
  simp only [Circulation.solverEdgeWords, Circulation.positiveInstance, he, ↓reduceIte,
    Fin.val_last, lt_self_iff_false, Int.natAbs_zero]

/-- An active slot retains every word of its original record. -/
theorem positiveInstance_edgeWords_nonzero (J : Circulation) (e : Fin J.m)
    (he : J.capacity e ≠ 0) : J.positiveInstance.solverEdgeWords e = J.solverEdgeWords e := by
  simp only [Circulation.solverEdgeWords, Circulation.positiveInstance, he, ↓reduceIte,
    Fin.val_castSucc]

end MinCostFlow.Scaling.Machine
