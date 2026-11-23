module

public import MinCostFlow.IPM.Machine.InitialEncodedInstance
import MinCostFlow.IPM.InitialDomain

/-!
# The exact initial flow read from augmented capacities

Lemma 4.12 (Chen et al., arXiv:2203.00671v2, page 31,
Appendix B.1 page 92) uses midpoint flow on both original and auxiliary
edges. On the bounded circulation input all lower capacities are zero.
Thus the verified fixed-point loader, which stores half the unsigned
capacity word, gives exactly `initialFlow` on every augmented edge.
-/

public section
namespace MinCostFlow.IPM.Machine
open Scaling

/-- Every coordinate of the prescribed initial flow is half its augmented
upper capacity on the circulation input. -/
theorem initialFlow_half_upper (J : Circulation) (penalty : ℤ)
    (e : Fin (initialInstance J.toInstance penalty).m) :
    initialFlow J.toInstance penalty e =
      (((initialInstance J.toInstance penalty).edge e).upper : ℝ)/2 := by
  have harr : ∀ j, initialArrayFlow J.toInstance j =
      ((initialEdgeArray J.toInstance penalty j).upper : ℝ)/2 := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [initialArrayFlow,initialEdgeArray,Fin.addCases_left,freeEdgeArray,
        Circulation.toInstance_edge,Circulation.inputEdge,Int.cast_zero,zero_add]
    · simp only [initialArrayFlow,initialEdgeArray,Fin.addCases_right,starEdge_upper,Int.cast_abs]
  have he := instanceOfArrays_edge (initialEdgeArray J.toInstance penalty) (initialDemands J.toInstance) e
  exact (harr (arrayIndex (initialEdgeArray J.toInstance penalty) (initialDemands J.toInstance) e)).trans
    ((congrArg (fun edge : Edge => (edge.upper : ℝ)/2) he).symm)

/-- Dividing the encoded unsigned capacity by two loses no information,
so the numeric loader's scalar output is the exact model initial flow. -/
theorem initialFlow_half_encoded (J : Circulation) (hp : ∀ e, 1 ≤ J.capacity e) (penalty : ℤ)
    (e : Fin (initialInstance J.toInstance penalty).m) :
    ((((initialInstance J.toInstance penalty).edge e).upper.toNat : ℕ) : ℝ)/2 =
      initialFlow J.toInstance penalty e := by
  have hnonneg := ((initialInstance_zeroLower J hp penalty).1 e).2
  have hcast : ((((initialInstance J.toInstance penalty).edge e).upper.toNat : ℕ) : ℝ) =
      (((initialInstance J.toInstance penalty).edge e).upper : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  rw [hcast,initialFlow_half_upper]

end MinCostFlow.IPM.Machine
