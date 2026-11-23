module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Range

/-!
# A uniform allocation bound for the reported-list loop

The min-ratio contract gives Query's allocation as a function of its
concrete arguments. Edges and allocation endpoints are bounded words,
so a finite maximum bounds all Query calls in a list. This maximum is
only an analysis bound: the machine does not enumerate it. When the DS
supplies a uniform Query space bound, the maximum is no larger than
that supplied bound, avoiding any loss in the final workspace estimate.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- Maximum Query allocation over edge names and word-sized endpoints. -/
def queryAllocationBound (w m b : ℕ) (allocation : ℕ → List ℕ → ℕ) : ℕ :=
  (Finset.range m).sup fun e =>
    (Finset.range (2^w)).sup fun heap => allocation 1 [b,e,heap]

/-- Every Query in the reported-list loop lies below the finite bound. -/
theorem query_allocation_le_bound {w m b e heap : ℕ} (allocation : ℕ → List ℕ → ℕ)
    (he : e<m) (hh : heap<2^w) :
    allocation 1 [b,e,heap]≤queryAllocationBound w m b allocation := by
  unfold queryAllocationBound
  exact Finset.le_sup_of_le (Finset.mem_range.mpr he)
    (Finset.le_sup (f:=fun h => allocation 1 [b,e,h]) (Finset.mem_range.mpr hh))

/-- A supplied uniform DS space bound also bounds the analysis maximum.
In particular, constant Query allocation recovers that same bound. -/
theorem queryAllocationBound_le {w m b bound : ℕ} (allocation : ℕ → List ℕ → ℕ)
    (hbound : ∀ e<m,∀ heap<2^w,allocation 1 [b,e,heap]≤bound) :
    queryAllocationBound w m b allocation≤bound := by
  apply Finset.sup_le
  intro e he
  apply Finset.sup_le
  intro heap hh
  exact hbound e (Finset.mem_range.mp he) heap (Finset.mem_range.mp hh)

end MinCostFlow.IPM.Machine
