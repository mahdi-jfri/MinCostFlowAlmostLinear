module

public import MinCostFlow.IPM.InitialConstruction
import MinCostFlow.IPM.InitialRouting
import Mathlib.Tactic.Linarith

/-!
# Strict feasibility and half-integral slacks

Appendix B.1 (page 92) of Chen et al., arXiv:2203.00671v2, bounds the barrier by
using the fact that midpoint slacks are positive half-integers. Fixed
edges have already been deleted and zero deficits have no auxiliary
edge. Thus every remaining slack is at least one half. We also verify
that the constructed instance is valid.
-/

public section
namespace MinCostFlow.IPM

/-- Every auxiliary edge has zero lower capacity. -/
theorem starEdge_lower (n : ℕ) (v : Fin n) (z K : ℤ) : (starEdge n v z K).lower = 0 := by
  unfold starEdge
  split_ifs <;> rfl

/-- Every auxiliary edge has upper capacity equal to the absolute twice-deficit. -/
theorem starEdge_upper (n : ℕ) (v : Fin n) (z K : ℤ) : (starEdge n v z K).upper = |z| := by
  unfold starEdge
  split_ifs <;> rfl

/-- Every auxiliary edge has the specified penalty cost. -/
theorem starEdge_cost (n : ℕ) (v : Fin n) (z K : ℤ) : (starEdge n v z K).cost = K := by
  unfold starEdge
  split_ifs <;> rfl

/-- The auxiliary-vertex instance is valid when the original instance is valid. -/
theorem initialInstance_valid (I : Instance) (K : ℤ) (hI : I.IsValid) :
    (initialInstance I K).IsValid := by
  apply valid_instanceOfArrays
  intro e
  refine Fin.addCases (fun j => ?_) (fun j => ?_) e
  · simp only [initialEdgeArray, Fin.addCases_left]
    have hj := hI.1 (I.edge (freeIndex I j).1) (List.getElem_mem ((freeIndex I j).1).2)
    exact ⟨Nat.lt_succ_of_lt hj.1, Nat.lt_succ_of_lt hj.2⟩
  · simp only [initialEdgeArray, Fin.addCases_right]
    have hv := ((deficitIndex I j).1).2
    unfold starEdge
    split_ifs
    · exact ⟨Nat.lt_succ_of_lt hv, Nat.lt_succ_self _⟩
    · exact ⟨Nat.lt_succ_self _, Nat.lt_succ_of_lt hv⟩

/-- Each initial array slack is at least one half. This uses integrality
of original capacity gaps and nonzero integral twice-deficits. -/
theorem initialArrayFlow_slacks (I : Instance) (K : ℤ)
    (e : Fin ((freeEdges I).card+(deficitVertices I).card)) :
    (1/2 : ℝ) ≤ initialArrayFlow I e-(initialEdgeArray I K e).lower ∧
      (1/2 : ℝ) ≤ (initialEdgeArray I K e).upper-initialArrayFlow I e := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) e
  · simp only [initialEdgeArray, initialArrayFlow, Fin.addCases_left]
    have hi : (freeEdgeArray I j).lower+1 ≤ (freeEdgeArray I j).upper :=
      Int.add_one_le_iff.mpr (freeEdgeArray_strict I j)
    have hr : ((freeEdgeArray I j).lower : ℝ)+1 ≤ (freeEdgeArray I j).upper := by exact_mod_cast hi
    constructor <;> linarith only [hr]
  · simp only [initialEdgeArray, initialArrayFlow, Fin.addCases_right, starEdge_lower, starEdge_upper]
    have hz : twiceDeficit I (deficitIndex I j).1 ≠ 0 := (Finset.mem_filter.mp (deficitIndex I j).2).2
    have hzpos : (0 : ℤ) < |twiceDeficit I (deficitIndex I j).1| := abs_pos.mpr hz
    have hzi : (1 : ℤ) ≤ |twiceDeficit I (deficitIndex I j).1| := Int.add_one_le_iff.mpr hzpos
    have hzr : (1 : ℝ) ≤ |(twiceDeficit I (deficitIndex I j).1 : ℝ)| := by exact_mod_cast hzi
    simp only [Int.cast_zero, sub_zero, Int.cast_abs]
    constructor <;> linarith only [hzr]

/-- Every initial flow slack in the actual instance is at least one half. -/
theorem initialFlow_slacks (I : Instance) (K : ℤ) (e : Fin (initialInstance I K).m) :
    (1/2 : ℝ) ≤ initialFlow I K e-((initialInstance I K).edge e).lower ∧
      (1/2 : ℝ) ≤ ((initialInstance I K).edge e).upper-initialFlow I K e := by
  have he : (initialInstance I K).edge e =
      initialEdgeArray I K (arrayIndex (initialEdgeArray I K) (initialDemands I) e) :=
    instanceOfArrays_edge (initialEdgeArray I K) (initialDemands I) e
  rw [he]
  exact initialArrayFlow_slacks I K (arrayIndex (initialEdgeArray I K) (initialDemands I) e)

/-- Fixed-edge deletion ensures strict capacity feasibility at initialization. -/
theorem initialFlow_inside (I : Instance) (K : ℤ) :
    StrictlyInside (initialInstance I K) (initialFlow I K) := by
  intro e
  have ht := initialFlow_slacks I K e
  constructor <;> linarith only [ht.1, ht.2]

/-- The initial flow is feasible after the capacity and total-demand checks. -/
theorem initialFlow_feasible (I : Instance) (K : ℤ) (hI : I.IsValid)
    (hordered : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper)
    (hbal : (∑ v : Fin I.n, (I.d v : ℝ)) = 0) :
    (initialInstance I K).IsFeasible (initialFlow I K) :=
  feasible_of_inside _ _ (initialFlow_routes I K hI hordered hbal) (initialFlow_inside I K)

end MinCostFlow.IPM
