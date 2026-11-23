module

public import MinCostFlow.IPM.InitialConstruction
import MinCostFlow.IPM.InitialDomain
import MinCostFlow.IPM.InitialSize
import MinCostFlow.IPM.InitialRouting
import all MinCostFlow.IPM.RemoveFixedBounds
import Mathlib.Tactic.Linarith

/-!
# Bounds on the numbers in the initial instance

Appendix B.1 (page 92) of Chen et al., arXiv:2203.00671v2, requires integral
augmented demands bounded by `2mU`, and costs and capacities bounded by
`4mU²`. The midpoint demand deficit is half-integral. Its twice-deficit
has absolute value at most `4mU`, which bounds each auxiliary capacity.
-/

public section
namespace MinCostFlow.IPM

/-- The midpoint of any ordered interval with endpoints bounded by `U`
has absolute value at most `U`. -/
theorem abs_midpointFlow_le (I : Instance) (U : ℝ) (hnums : NumbersBounded I U)
    (e : Fin I.m) : |midpointFlow I e| ≤ U := by
  have hl := abs_le.mp (hnums.2 e).1
  have hu := abs_le.mp (hnums.2 e).2.1
  apply abs_le.mpr
  dsimp only [midpointFlow]
  constructor <;> linarith only [hl.1, hl.2, hu.1, hu.2]

/-- The absolute midpoint demand routed at a vertex is at most `mU`. -/
theorem abs_midpoint_demand_le (I : Instance) (U : ℝ) (_hU : 0 ≤ U)
    (hnums : NumbersBounded I U) (v : Fin I.n) :
    |∑ e, (I.edge e).b v*midpointFlow I e| ≤ I.m*U := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ e, |(I.edge e).b v*midpointFlow I e|) ≤ ∑ _ : Fin I.m, U := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_mul]
      have h := mul_le_mul (incidence_abs_le_one (I.edge e) v)
        (abs_midpointFlow_le I U hnums e) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simpa only [one_mul] using h
    _ = I.m*U := by simp

/-- The integral twice-deficit, and therefore every auxiliary upper
capacity, is bounded by `4mU`. -/
theorem abs_twiceDeficit_le (I : Instance) (U : ℝ) (hm : 0 < I.m) (hU : 0 ≤ U)
    (hnums : NumbersBounded I U) (v : Fin I.n) : |(twiceDeficit I v : ℝ)| ≤ 4*I.m*U := by
  have ht := abs_sub_le (I.d v : ℝ) 0 (∑ e, (I.edge e).b v*midpointFlow I e)
  simp only [sub_zero, zero_sub, abs_neg] at ht
  have hd := hnums.1 v
  have hb := abs_midpoint_demand_le I U hU hnums v
  have hm' : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
  have hmul := mul_le_mul_of_nonneg_right hm' hU
  rw [twiceDeficit_cast, abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith only [ht, hd, hb, hmul]

/-- The new demands are bounded by `2mU`, as in Lemma 4.12 (page 31). -/
theorem initialDemands_abs_le (I : Instance) (U : ℝ) (hm : 0 < I.m) (hU : 0 ≤ U)
    (hnums : NumbersBounded I U) (v : Fin (I.n+1)) :
    |(initialDemands I v : ℝ)| ≤ 2*I.m*U := by
  refine Fin.lastCases ?_ (fun w => ?_) v
  · simp only [initialDemands, Fin.lastCases_last, Int.cast_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hU
  · simp only [initialDemands, Fin.lastCases_castSucc]
    exact abs_freeDemands_le I U hm hU hnums w

/-- The artificial penalty has the magnitude specified in Lemma 4.12 (page 31). -/
theorem penalty_cast (I : Instance) (U : ℕ) :
    ((4*(I.m : ℤ)*(U : ℤ)^2 : ℤ) : ℝ) = 4*I.m*(U : ℝ)^2 := by
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_pow]

/-- The augmented array capacities and costs are bounded by `4mU²`
when the penalty obeys that same bound. -/
theorem initialEdgeArray_numbers_le (I : Instance) (U : ℝ) (K : ℤ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hnums : NumbersBounded I U)
    (hK : |(K : ℝ)| ≤ 4*I.m*U^2)
    (e : Fin ((freeEdges I).card+(deficitVertices I).card)) :
    |((initialEdgeArray I K e).lower : ℝ)| ≤ 4*I.m*U^2 ∧
      |((initialEdgeArray I K e).upper : ℝ)| ≤ 4*I.m*U^2 ∧
      |((initialEdgeArray I K e).cost : ℝ)| ≤ 4*I.m*U^2 := by
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hm' : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
  have hpow : U ≤ U^2 := by nlinarith only [hU]
  have hbound : U ≤ 4*I.m*U^2 := by
    have h := mul_le_mul_of_nonneg_right hm' (sq_nonneg U)
    nlinarith only [h, hpow, hU0]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) e
  · simp only [initialEdgeArray, Fin.addCases_left]
    have ht := hnums.2 (freeIndex I j).1
    exact ⟨ht.1.trans hbound, ht.2.1.trans hbound, ht.2.2.trans hbound⟩
  · simp only [initialEdgeArray, Fin.addCases_right, starEdge_lower, starEdge_upper,
      starEdge_cost, Int.cast_zero, abs_zero, Int.cast_abs, abs_abs]
    have hd := abs_twiceDeficit_le I U hm hU0 hnums (deficitIndex I j).1
    have hh := mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg I.m))
    exact ⟨le_trans hU0 hbound, hd.trans hh, hK⟩

/-- The numeric bounds for the actual augmented instance. -/
theorem initialInstance_numbers (I : Instance) (U : ℝ) (K : ℤ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hnums : NumbersBounded I U)
    (hK : |(K : ℝ)| ≤ 4*I.m*U^2) :
    (∀ v : Fin (initialInstance I K).n, |((initialInstance I K).d v : ℝ)| ≤ 2*I.m*U) ∧
    (∀ e : Fin (initialInstance I K).m,
      |(((initialInstance I K).edge e).lower : ℝ)| ≤ 4*I.m*U^2 ∧
      |(((initialInstance I K).edge e).upper : ℝ)| ≤ 4*I.m*U^2 ∧
      |(((initialInstance I K).edge e).cost : ℝ)| ≤ 4*I.m*U^2) := by
  constructor
  · intro v
    have hd : (initialInstance I K).d v = initialDemands I v :=
      instanceOfArrays_d (initialEdgeArray I K) (initialDemands I) v
    rw [hd]
    exact initialDemands_abs_le I U hm (le_trans (by norm_num) hU) hnums v
  · intro e
    have he : (initialInstance I K).edge e =
        initialEdgeArray I K (arrayIndex (initialEdgeArray I K) (initialDemands I) e) :=
      instanceOfArrays_edge (initialEdgeArray I K) (initialDemands I) e
    rw [he]
    exact initialEdgeArray_numbers_le I U K hm hU hnums hK _

end MinCostFlow.IPM
