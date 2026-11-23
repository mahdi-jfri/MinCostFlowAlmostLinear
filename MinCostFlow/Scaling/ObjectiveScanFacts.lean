module

public import MinCostFlow.Scaling.ReductionAlgorithm
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Integer objective scans

The bottleneck test sums signed cost times nonnegative integral flow.
The sum of absolute products bounds every suffix and every intermediate
addition, so the machine can use one-word magnitudes throughout the scan.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Signed objective contribution of an ordered edge list. -/
def objectiveScan (J : Circulation) (f : Fin J.m → ℕ) (es : List (Fin J.m)) : ℤ :=
  (es.map (fun e => J.cost e * (f e : ℤ))).sum

/-- Sum of absolute product magnitudes for the same ordered list. -/
def objectiveScanMass (J : Circulation) (f : Fin J.m → ℕ) (es : List (Fin J.m)) : ℕ :=
  (es.map (fun e => (J.cost e).natAbs * f e)).sum

/-- Splitting one edge exposes the exact arithmetic step of the scan. -/
theorem objectiveScan_cons (J : Circulation) (f : Fin J.m → ℕ) (e : Fin J.m)
    (es : List (Fin J.m)) :
    objectiveScan J f (e::es) = J.cost e * (f e : ℤ)+objectiveScan J f es := by
  simp only [objectiveScan,List.map_cons,List.sum_cons]

/-- The magnitude budget splits over the same first edge. -/
theorem objectiveScanMass_cons (J : Circulation) (f : Fin J.m → ℕ) (e : Fin J.m)
    (es : List (Fin J.m)) :
    objectiveScanMass J f (e::es) = (J.cost e).natAbs*f e+objectiveScanMass J f es := by
  simp only [objectiveScanMass,List.map_cons,List.sum_cons]

/-- Cancellation can only reduce the magnitude of an objective sum. -/
theorem objectiveScan_natAbs_le (J : Circulation) (f : Fin J.m → ℕ)
    (es : List (Fin J.m)) : (objectiveScan J f es).natAbs ≤ objectiveScanMass J f es := by
  induction es with
  | nil => simp only [objectiveScan,objectiveScanMass,List.map_nil,List.sum_nil,Int.natAbs_zero]; exact le_rfl
  | cons e es ih =>
    rw [objectiveScan_cons,objectiveScanMass_cons]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add
      (by simp only [Int.natAbs_mul,Int.natAbs_natCast]; exact le_rfl) ih)

/-- Uniform cost and coordinate bounds give a polynomial arithmetic budget
for every ordered edge scan. -/
theorem objectiveScanMass_le (J : Circulation) (f : Fin J.m → ℕ)
    (es : List (Fin J.m)) (C U : ℕ)
    (hc : ∀ e ∈ es,(J.cost e).natAbs ≤ C) (hf : ∀ e ∈ es,f e ≤ U) :
    objectiveScanMass J f es ≤ es.length*(C*U) := by
  induction es with
  | nil => simp only [objectiveScanMass,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul]; exact le_rfl
  | cons e es ih =>
    rw [objectiveScanMass_cons,List.length_cons,Nat.succ_mul]
    have hhead := Nat.mul_le_mul (hc e List.mem_cons_self) (hf e List.mem_cons_self)
    have htail := ih (fun e' he' => hc e' (List.mem_cons_of_mem e he'))
      (fun e' he' => hf e' (List.mem_cons_of_mem e he'))
    omega

/-- Scanning all edges computes exactly the model's integer objective. -/
theorem objectiveScan_finRange (J : Circulation) (f : Fin J.m → ℕ) :
    objectiveScan J f (List.finRange J.m) = J.integerObjective (fun e => (f e : ℤ)) := by
  rw [objectiveScan,← Fin.sum_univ_def]
  rfl

end MinCostFlow.Scaling
