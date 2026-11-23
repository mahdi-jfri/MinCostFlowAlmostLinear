module

public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Capacity totals at endpoints during initialization

Appendix B.1 of Chen et al., arXiv:2203.00671v2 (page 92,
Lemma 4.12 on page 31), corrects the routing of the midpoint flow.
For a zero-demand circulation instance with zero lower capacities,
twice its routing deficit is incoming capacity minus outgoing capacity.
The initialization scans each edge once into two nonnegative endpoint
tables. This file gives the prefix sums and their one-edge update law,
so unsigned arithmetic suffices until the two tables are subtracted.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open scoped BigOperators

/-- Total weight at a vertex after the first `k` endpoints. -/
def initialEndpointSum (endpoint weight : ℕ → ℕ) (k v : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, if endpoint i = v then weight i else 0

/-- Before the scan, every endpoint total is zero. -/
theorem initialEndpointSum_zero (endpoint weight : ℕ → ℕ) :
    initialEndpointSum endpoint weight 0 = fun _ => 0 := by
  funext v
  simp [initialEndpointSum]

/-- One edge contributes its capacity only at its selected endpoint. -/
theorem initialEndpointSum_succ (endpoint weight : ℕ → ℕ) (k v : ℕ) :
    initialEndpointSum endpoint weight (k+1) v =
      initialEndpointSum endpoint weight k v + if endpoint k = v then weight k else 0 :=
  Finset.sum_range_succ _ k

/-- The scan's in-place addition implements exactly the next prefix. -/
theorem initialEndpointSum_update (endpoint weight : ℕ → ℕ) (k : ℕ) :
    Function.update (initialEndpointSum endpoint weight k) (endpoint k)
      (initialEndpointSum endpoint weight k (endpoint k)+weight k) =
        initialEndpointSum endpoint weight (k+1) := by
  funext v
  by_cases he : v = endpoint k
  · subst v
    simp only [Function.update_self,initialEndpointSum_succ,↓reduceIte]
  · rw [Function.update_of_ne he,initialEndpointSum_succ]
    simp only [Ne.symm he,↓reduceIte,add_zero]

/-- Every prefix endpoint total is bounded by the total input capacity.
This is the fit bound used by the unsigned machine additions. -/
theorem initialEndpointSum_le_total (endpoint weight : ℕ → ℕ) (k m v : ℕ) (hkm : k ≤ m) :
    initialEndpointSum endpoint weight k v ≤ ∑ i ∈ Finset.range m, weight i := by
  calc
    _ ≤ ∑ i ∈ Finset.range k, weight i := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> omega
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.range_mono hkm)

end MinCostFlow.IPM.Machine
