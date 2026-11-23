module

public import MinCostFlow.IPM.InitialRecovery
public import MinCostFlow.IPM.RecoveryWalk
import MinCostFlow.IPM.InitialDomain
import Mathlib.Tactic.Linarith

/-!
# Costs of supported augmented arcs

In the real-flow recovery argument for Appendix B.1 (page 92) of Chen et al.,
arXiv:2203.00671v2, compare a feasible flow with zero auxiliary flow to
the augmented optimum. Every supported auxiliary arc then points
backwards and has cost `-K`. Every other supported arc costs at most `U`.
Thus a short supported cycle through an auxiliary edge lowers cost.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM

/-- The actual edge index of an auxiliary edge. -/
def initialAuxiliaryEdge (I : Instance) (K : ℤ) (j : Fin (deficitVertices I).card) :
    Fin (initialInstance I K).m :=
  (arrayIndex (initialEdgeArray I K) (initialDemands I)).symm (Fin.natAdd (freeEdges I).card j)

/-- The edge data at an array index agree with the constructed edge array. -/
theorem initialInstance_edge_array (I : Instance) (K : ℤ)
    (e : Fin ((freeEdges I).card+(deficitVertices I).card)) :
    (initialInstance I K).edge ((arrayIndex (initialEdgeArray I K) (initialDemands I)).symm e) =
      initialEdgeArray I K e := by
  have he : (initialInstance I K).edge
      ((arrayIndex (initialEdgeArray I K) (initialDemands I)).symm e) =
      initialEdgeArray I K ((arrayIndex (initialEdgeArray I K) (initialDemands I))
        ((arrayIndex (initialEdgeArray I K) (initialDemands I)).symm e)) :=
    instanceOfArrays_edge (initialEdgeArray I K) (initialDemands I)
      ((arrayIndex (initialEdgeArray I K) (initialDemands I)).symm e)
  rw [Equiv.apply_symm_apply] at he
  exact he

/-- Auxiliary edge flow in actual instance coordinates. -/
theorem initialAuxiliaryFlow_eq (I : Instance) (K : ℤ)
    (g : Fin (initialInstance I K).m → ℝ) (j : Fin (deficitVertices I).card) :
    initialAuxiliaryFlow I K g j = g (initialAuxiliaryEdge I K j) := rfl

/-- A feasible augmented flow is nonnegative on every auxiliary edge. -/
theorem initialAuxiliaryFlow_nonneg (I : Instance) (K : ℤ)
    (g : Fin (initialInstance I K).m → ℝ) (hg : (initialInstance I K).IsFeasible g)
    (j : Fin (deficitVertices I).card) : 0 ≤ initialAuxiliaryFlow I K g j := by
  have hc := (hg.2 (initialAuxiliaryEdge I K j)).1
  have he : (initialInstance I K).edge (initialAuxiliaryEdge I K j) =
      starEdge I.n (deficitIndex I j).1 (twiceDeficit I (deficitIndex I j).1) K := by
    simpa only [initialAuxiliaryEdge, initialEdgeArray, Fin.addCases_right] using
      initialInstance_edge_array I K (Fin.natAdd (freeEdges I).card j)
  rw [he, starEdge_lower, Int.cast_zero] at hc
  exact hc

/-- Original feasible flows embed with identically zero auxiliary coordinates. -/
theorem embedInitialFlow_auxiliary_zero (I : Instance) (K : ℤ)
    (f : Fin (removeFixed I).m → ℝ) (j : Fin (deficitVertices I).card) :
    initialAuxiliaryFlow I K (embedInitialFlow I K f) j = 0 := by
  simp only [initialAuxiliaryFlow, embedInitialFlow, flowToArray, flowOfArray,
    Equiv.apply_symm_apply, Fin.addCases_right]

/-- Every supported arc has cost at most `U` when auxiliary residual
coordinates are nonpositive and the auxiliary penalty is nonnegative. -/
theorem initial_supported_arc_cost_le (I : Instance) (U : ℝ) (K : ℤ)
    (hU : 0 ≤ U) (hnums : NumbersBounded I U) (hK : 0 ≤ (K : ℝ))
    (d : Fin (initialInstance I K).m → ℝ)
    (hdaux : ∀ j, d (initialAuxiliaryEdge I K j) ≤ 0)
    (a : Fin (initialInstance I K).m × Bool) (ha : ArcSupported d a) :
    (((initialInstance I K).edge a.1).cost : ℝ)*arcSign a ≤ U := by
  rcases a with ⟨e, b⟩
  have hbound : ∀ k : Fin ((freeEdges I).card+(deficitVertices I).card),
      ArcSupported d (((arrayIndex (initialEdgeArray I K) (initialDemands I)).symm k), b) →
      (((initialInstance I K).edge ((arrayIndex (initialEdgeArray I K) (initialDemands I)).symm k)).cost : ℝ)*
        arcSign (((arrayIndex (initialEdgeArray I K) (initialDemands I)).symm k), b) ≤ U := by
    intro k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · intro _
      rw [initialInstance_edge_array]
      simp only [initialEdgeArray, Fin.addCases_left]
      have hc := abs_le.mp (hnums.2 (freeIndex I j).1).2.2
      cases b
      · simpa only [arcSign, Bool.false_eq_true, ↓reduceIte, mul_neg_one, freeEdgeArray] using neg_le.mpr hc.1
      · simpa only [arcSign, ↓reduceIte, mul_one, freeEdgeArray] using hc.2
    · intro hs
      have hd := hdaux j
      cases b
      · rw [initialInstance_edge_array]
        simp only [initialEdgeArray, Fin.addCases_right, starEdge_cost,
          arcSign, Bool.false_eq_true, ↓reduceIte, mul_neg_one]
        exact (neg_nonpos.mpr hK).trans hU
      · have hp : 0 < d (initialAuxiliaryEdge I K j) := by
          simpa only [ArcSupported, arcSign, ↓reduceIte, one_mul, initialAuxiliaryEdge] using hs
        exact False.elim (not_lt_of_ge hd hp)
  have ht := hbound (arrayIndex (initialEdgeArray I K) (initialDemands I) e)
  have hindex : (arrayIndex (initialEdgeArray I K) (initialDemands I)).symm
      ((arrayIndex (initialEdgeArray I K) (initialDemands I)) e) = e :=
    (arrayIndex (initialEdgeArray I K) (initialDemands I)).symm_apply_apply e
  rw [hindex] at ht
  exact ht ha

/-- A backward auxiliary arc has cost exactly minus the penalty. -/
theorem initial_backward_auxiliary_cost (I : Instance) (K : ℤ) (j : Fin (deficitVertices I).card) :
    (((initialInstance I K).edge (initialAuxiliaryEdge I K j)).cost : ℝ)*
      arcSign (initialAuxiliaryEdge I K j, false) = -(K : ℝ) := by
  have he := initialInstance_edge_array I K (Fin.natAdd (freeEdges I).card j)
  change (((initialInstance I K).edge
    ((arrayIndex (initialEdgeArray I K) (initialDemands I)).symm (Fin.natAdd (freeEdges I).card j))).cost : ℝ)*_ = _
  rw [he]
  simp only [initialEdgeArray, Fin.addCases_right, starEdge_cost,
    arcSign, Bool.false_eq_true, ↓reduceIte, mul_neg_one]

end MinCostFlow.IPM
