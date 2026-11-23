module

public import MinCostFlow.IPM.InitialConstruction
import MinCostFlow.IPM.InitialNumbers
public import MinCostFlow.IPM.InitialSize
import MinCostFlow.IPM.InitialDomain
import MinCostFlow.IPM.RemoveFixedBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cost estimates for the initial point

Appendix B.1 (page 92) of Chen et al., arXiv:2203.00671v2, bounds original edge
costs by `mU²` and charges the nonnegative penalty on auxiliary edges.
We retain all nonzero deficit vertices, giving at most `3m` total edges.
The resulting initial cost bound is `17m³U³`; together with the lower
bound on every feasible cost this gives residual at most `18m³U³`.
These constants still imply the source's potential bound of 200.
-/

public section
namespace MinCostFlow.IPM

private theorem freeEdges_card_le (I : Instance) : (freeEdges I).card ≤ I.m := by
  have h := removeFixed_m_le I
  simpa only [removeFixed, instanceOfArrays_m] using h

/-- Cost of a midpoint array edge is bounded in absolute value by `U²`. -/
theorem abs_free_midpoint_cost_le (I : Instance) (U : ℝ) (hU : 0 ≤ U)
    (hnums : NumbersBounded I U) (j : Fin (freeEdges I).card) :
    |((freeEdgeArray I j).cost : ℝ)*
      ((((freeEdgeArray I j).lower : ℝ)+(freeEdgeArray I j).upper)/2)| ≤ U^2 := by
  rw [abs_mul]
  have hc := (hnums.2 (freeIndex I j).1).2.2
  have hf := abs_midpointFlow_le I U hnums (freeIndex I j).1
  have hm := mul_le_mul hc hf (abs_nonneg _) hU
  simpa only [freeEdgeArray, midpointFlow, pow_two] using hm

/-- Cost is the sum of the original-edge and auxiliary-edge costs in
array coordinates. -/
theorem initialInstance_cost_array (I : Instance) (K : ℤ)
    (g : Fin ((freeEdges I).card+(deficitVertices I).card) → ℝ) :
    (initialInstance I K).cost (flowOfArray (initialEdgeArray I K) (initialDemands I) g) =
      (∑ j, ((freeEdgeArray I j).cost : ℝ)*g (Fin.castAdd (deficitVertices I).card j)) +
      ∑ j, (K : ℝ)*g (Fin.natAdd (freeEdges I).card j) := by
  have hc : (initialInstance I K).cost (flowOfArray (initialEdgeArray I K) (initialDemands I) g) =
      ∑ j, ((initialEdgeArray I K j).cost : ℝ)*g j :=
    cost_flowOfArray (initialEdgeArray I K) (initialDemands I) g
  rw [hc, Fin.sum_univ_add]
  simp only [initialEdgeArray, Fin.addCases_left, Fin.addCases_right, starEdge_cost]

/-- The source's initial midpoint cost estimate, allowing all original
endpoint vertices rather than assuming `n ≤ m`. -/
theorem initialFlow_cost_le (I : Instance) (U : ℝ) (K : ℤ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hnums : NumbersBounded I U)
    (hi : IsolatedDemandsZero I) (_hK : 0 ≤ (K : ℝ)) (hK' : (K : ℝ) ≤ 4*I.m*U^2) :
    (initialInstance I K).cost (initialFlow I K) ≤ 17*(I.m : ℝ)^3*U^3 := by
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hm' : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
  have hc_old : (∑ j, ((freeEdgeArray I j).cost : ℝ)*
      ((((freeEdgeArray I j).lower : ℝ)+(freeEdgeArray I j).upper)/2)) ≤ I.m*U^2 := by
    calc
      _ ≤ ∑ _ : Fin (freeEdges I).card, U^2 := by
        apply Finset.sum_le_sum
        intro j _
        exact (le_abs_self _).trans (abs_free_midpoint_cost_le I U hU0 hnums j)
      _ = (freeEdges I).card*U^2 := by simp
      _ ≤ I.m*U^2 := mul_le_mul_of_nonneg_right (by exact_mod_cast freeEdges_card_le I) (sq_nonneg U)
  have hc_new : (∑ j, (K : ℝ)*(|(twiceDeficit I (deficitIndex I j).1 : ℝ)|/2)) ≤
      16*(I.m : ℝ)^3*U^3 := by
    have hterm : ∀ j, (K : ℝ)*(|(twiceDeficit I (deficitIndex I j).1 : ℝ)|/2) ≤
        8*(I.m : ℝ)^2*U^3 := by
      intro j
      have hd := abs_twiceDeficit_le I U hm hU0 hnums (deficitIndex I j).1
      have hprod := mul_le_mul hK' (by linarith only [hd] :
        |(twiceDeficit I (deficitIndex I j).1 : ℝ)|/2 ≤ 2*I.m*U)
        (div_nonneg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2))
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg I.m)) (sq_nonneg U))
      nlinarith only [hprod]
    calc
      _ ≤ ∑ _ : Fin (deficitVertices I).card, 8*(I.m : ℝ)^2*U^3 :=
        Finset.sum_le_sum (fun j _ => hterm j)
      _ = (deficitVertices I).card*(8*(I.m : ℝ)^2*U^3) := by simp
      _ ≤ (2*I.m)*(8*(I.m : ℝ)^2*U^3) := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast deficitVertices_card_le I hi)
        exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (pow_nonneg hU0 _)
      _ = 16*(I.m : ℝ)^3*U^3 := by ring
  have hcost := initialInstance_cost_array I K (initialArrayFlow I)
  simp only [initialArrayFlow, Fin.addCases_left, Fin.addCases_right] at hcost
  have hscale : I.m*U^2 ≤ (I.m : ℝ)^3*U^3 := by
    have hmpow : (1 : ℝ) ≤ (I.m : ℝ)^2 := by nlinarith only [hm']
    have hfactor : 1 ≤ (I.m : ℝ)^2*U := by
      have h := mul_le_mul_of_nonneg_right hmpow hU0
      nlinarith only [h, hU]
    have hprod := mul_le_mul_of_nonneg_left hfactor (mul_nonneg (Nat.cast_nonneg I.m) (sq_nonneg U))
    nlinarith only [hprod]
  change (initialInstance I K).cost (flowOfArray (initialEdgeArray I K) (initialDemands I) (initialArrayFlow I)) ≤ _
  linarith only [hcost, hc_old, hc_new, hscale]

/-- Every feasible augmented flow has cost at least `-mU²`, because its
auxiliary flows and auxiliary costs are nonnegative. -/
theorem initialInstance_cost_ge (I : Instance) (U : ℝ) (K : ℤ)
    (hU : 0 ≤ U) (hnums : NumbersBounded I U) (hK : 0 ≤ (K : ℝ))
    (g : Fin (initialInstance I K).m → ℝ) (hg : (initialInstance I K).IsFeasible g) :
    -(I.m*U^2) ≤ (initialInstance I K).cost g := by
  let f := flowToArray (initialEdgeArray I K) (initialDemands I) g
  have heq : flowOfArray (initialEdgeArray I K) (initialDemands I) f = g :=
    flowOfArray_flowToArray (initialEdgeArray I K) (initialDemands I) g
  have harr := (feasible_flowOfArray_iff (initialEdgeArray I K) (initialDemands I) f).mp (heq.symm ▸ hg)
  have hold : -(I.m*U^2) ≤
      ∑ j, ((freeEdgeArray I j).cost : ℝ)*f (Fin.castAdd (deficitVertices I).card j) := by
    have hterm : ∀ j, -(U^2) ≤
        ((freeEdgeArray I j).cost : ℝ)*f (Fin.castAdd (deficitVertices I).card j) := by
      intro j
      have hcap := harr.2 (Fin.castAdd (deficitVertices I).card j)
      simp only [initialEdgeArray, Fin.addCases_left, freeEdgeArray] at hcap
      have hn := hnums.2 (freeIndex I j).1
      have hl := (abs_le.mp hn.1).1
      have hu := (abs_le.mp hn.2.1).2
      have habs : |f (Fin.castAdd (deficitVertices I).card j)| ≤ U := by
        apply abs_le.mpr
        constructor <;> linarith only [hcap.1, hcap.2, hl, hu]
      have hprod := mul_le_mul hn.2.2 habs (abs_nonneg _) hU
      rw [← abs_mul] at hprod
      have ht := (abs_le.mp hprod).1
      simpa only [pow_two, freeEdgeArray] using ht
    calc
      -(I.m*U^2) ≤ -((freeEdges I).card*U^2) := by
        have h := mul_le_mul_of_nonneg_right (show ((freeEdges I).card : ℝ) ≤ I.m by
          exact_mod_cast freeEdges_card_le I) (sq_nonneg U)
        exact neg_le_neg h
      _ = ∑ _ : Fin (freeEdges I).card, -(U^2) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hterm j)
  have hnew : 0 ≤ ∑ j : Fin (deficitVertices I).card,
      (K : ℝ)*f (Fin.natAdd (freeEdges I).card j) := by
    apply Finset.sum_nonneg
    intro j _
    have hc := (harr.2 (Fin.natAdd (freeEdges I).card j)).1
    simp only [initialEdgeArray, Fin.addCases_right, starEdge_lower, Int.cast_zero] at hc
    exact mul_nonneg hK hc
  have hc := initialInstance_cost_array I K f
  rw [heq] at hc
  linarith only [hold, hnew, hc]

end MinCostFlow.IPM
