module

public import MinCostFlow.IPM.ConnectedInitialConstruction
public import MinCostFlow.IPM.InitialRecovery
public import MinCostFlow.IPM.InitialNumbers
public import MinCostFlow.Rounding.Rounding
import MinCostFlow.IPM.InitialCost
import MinCostFlow.IPM.InitialOptimalAuxiliary
import Mathlib.Tactic

/-!
# Recovery from the connected augmentation

Appendix B.1 (page 92) of Chen et al., arXiv:2203.00671v2 compares the
penalty of a positive integral auxiliary flow with the total cost range
on the original edges. The same comparison applies to the extra hub edges.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM

/-- Restrict a connected augmented flow to the original augmentation. -/
def restrictConnectedInitialFlow (I : Instance) (K : ℤ)
    (g : Fin (connectedInitialInstance I K).m → ℝ) : Fin (initialInstance I K).m → ℝ :=
  flowOfArray (initialEdgeArray I K) (initialDemands I) (fun j =>
    flowToArray (connectedInitialEdgeArray I K) (initialDemands I) g (Fin.castAdd _ j))

/-- Extend the old augmentation by zero on the added pairs. -/
def extendConnectedInitialFlow (I : Instance) (K : ℤ)
    (f : Fin (initialInstance I K).m → ℝ) : Fin (connectedInitialInstance I K).m → ℝ :=
  flowOfArray (connectedInitialEdgeArray I K) (initialDemands I)
    (Fin.addCases (flowToArray (initialEdgeArray I K) (initialDemands I) f) (fun _ => 0))

/-- The added pairs leave all numeric bounds of Lemma 4.12 unchanged. -/
theorem connectedInitialInstance_numbers (I : Instance) (U : ℝ) (K : ℤ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hnums : NumbersBounded I U)
    (hK : |(K : ℝ)| ≤ 4*I.m*U^2) :
    (∀ v : Fin (connectedInitialInstance I K).n,
      |((connectedInitialInstance I K).d v : ℝ)| ≤ 2*I.m*U) ∧
    (∀ e : Fin (connectedInitialInstance I K).m,
      |(((connectedInitialInstance I K).edge e).lower : ℝ)| ≤ 4*I.m*U^2 ∧
      |(((connectedInitialInstance I K).edge e).upper : ℝ)| ≤ 4*I.m*U^2 ∧
      |(((connectedInitialInstance I K).edge e).cost : ℝ)| ≤ 4*I.m*U^2) := by
  constructor
  · intro v
    rw [show (connectedInitialInstance I K).d v = _ from instanceOfArrays_d _ _ v]
    exact initialDemands_abs_le I U hm (by linarith only [hU]) hnums v
  · intro e
    rw [show (connectedInitialInstance I K).edge e = _ from instanceOfArrays_edge _ _ e]
    generalize arrayIndex (connectedInitialEdgeArray I K) (initialDemands I) e = j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · simp only [connectedInitialEdgeArray, Fin.addCases_left]
      exact initialEdgeArray_numbers_le I U K hm hU hnums hK a
    · have hM : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
      have hU2 : 1 ≤ U^2 := by nlinarith only [hU, sq_nonneg (U-1)]
      have hb := mul_le_mul hM hU2 (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg I.m)
      have h2 : (2 : ℝ) ≤ 4*I.m*U^2 := by linarith only [hb]
      simp only [connectedInitialEdgeArray, Fin.addCases_right]
      refine Fin.addCases (fun b => ?_) (fun b => ?_) a <;>
        simp only [Fin.addCases_left, Fin.addCases_right, starEdge_lower, starEdge_upper,
          starEdge_cost] <;> norm_num <;> exact ⟨by linarith only [h2], h2, hK⟩

/-- Zero flows on the extra pairs preserve both feasibility and the objective. -/
theorem extendConnectedInitialFlow_spec (I : Instance) (K : ℤ)
    (f : Fin (initialInstance I K).m → ℝ) (hf : (initialInstance I K).IsFeasible f) :
    (connectedInitialInstance I K).IsFeasible (extendConnectedInitialFlow I K f) ∧
      (connectedInitialInstance I K).cost (extendConnectedInitialFlow I K f) =
        (initialInstance I K).cost f := by
  let a := flowToArray (initialEdgeArray I K) (initialDemands I) f
  have ha := flowOfArray_flowToArray (initialEdgeArray I K) (initialDemands I) f
  have hf' := (feasible_flowOfArray_iff _ _ a).mp (ha.symm ▸ hf)
  constructor
  · apply (feasible_flowOfArray_iff _ _ _).mpr
    constructor
    · intro v
      rw [Fin.sum_univ_add]
      simpa only [connectedInitialEdgeArray, Fin.addCases_left, Fin.addCases_right, mul_zero,
        Finset.sum_const_zero, add_zero] using hf'.1 v
    · intro e
      refine Fin.addCases (fun j => ?_) (fun j => ?_) e
      · simpa only [connectedInitialEdgeArray, Fin.addCases_left] using hf'.2 j
      · simp only [connectedInitialEdgeArray, Fin.addCases_right]
        refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
          simp only [Fin.addCases_left, Fin.addCases_right, starEdge_lower, starEdge_upper] <;>
          norm_num
  · change (instanceOfArrays _ _ (connectedInitialEdgeArray I K) (initialDemands I)).cost
        (flowOfArray _ _ (Fin.addCases a (fun _ => 0))) =
      (instanceOfArrays _ _ (initialEdgeArray I K) (initialDemands I)).cost f
    rw [cost_flowOfArray, Fin.sum_univ_add, ← ha, cost_flowOfArray]
    simp only [connectedInitialEdgeArray, Fin.addCases_left, Fin.addCases_right, mul_zero,
      Finset.sum_const_zero, add_zero]
    rfl

/-- Restricting a flow with zero added coordinates preserves feasibility and cost. -/
theorem restrictConnectedInitialFlow_spec (I : Instance) (K : ℤ)
    (g : Fin (connectedInitialInstance I K).m → ℝ)
    (hg : (connectedInitialInstance I K).IsFeasible g)
    (hz : ∀ j, flowToArray (connectedInitialEdgeArray I K) (initialDemands I) g
      (Fin.natAdd _ j) = 0) :
    (initialInstance I K).IsFeasible (restrictConnectedInitialFlow I K g) ∧
      (initialInstance I K).cost (restrictConnectedInitialFlow I K g) =
        (connectedInitialInstance I K).cost g := by
  let a := flowToArray (connectedInitialEdgeArray I K) (initialDemands I) g
  have ha := flowOfArray_flowToArray (connectedInitialEdgeArray I K) (initialDemands I) g
  have hg' := (feasible_flowOfArray_iff _ _ a).mp (ha.symm ▸ hg)
  constructor
  · apply (feasible_flowOfArray_iff _ _ _).mpr
    constructor
    · intro v
      have h := hg'.1 v
      rw [Fin.sum_univ_add] at h
      have hzero : ∀ j, a (Fin.natAdd _ j) = 0 := hz
      simpa only [connectedInitialEdgeArray, Fin.addCases_left, Fin.addCases_right, hzero,
        mul_zero, Finset.sum_const_zero, add_zero] using h
    · intro j
      simpa only [connectedInitialEdgeArray, Fin.addCases_left] using
        hg'.2 (Fin.castAdd _ j)
  · change (instanceOfArrays _ _ (initialEdgeArray I K) (initialDemands I)).cost
        (flowOfArray _ _ (fun j => a (Fin.castAdd _ j))) =
      (instanceOfArrays _ _ (connectedInitialEdgeArray I K) (initialDemands I)).cost g
    change flowOfArray (connectedInitialEdgeArray I K) (initialDemands I) a = g at ha
    rw [← ha, cost_flowOfArray, cost_flowOfArray]
    conv_rhs => rw [Fin.sum_univ_add]
    have hzero : ∀ j, a (Fin.natAdd _ j) = 0 := hz
    simp only [connectedInitialEdgeArray, Fin.addCases_left, Fin.addCases_right, hzero,
      mul_zero, Finset.sum_const_zero, add_zero]

/-- The original-edge cost in any feasible flow is between `-mU²` and `mU²`. -/
theorem retained_cost_abs_le (I : Instance) (U : ℝ) (hU : 0 ≤ U)
    (hn : NumbersBounded I U) (f : Fin (freeEdges I).card → ℝ)
    (hf : ∀ j, ((freeEdgeArray I j).lower : ℝ) ≤ f j ∧ f j ≤ (freeEdgeArray I j).upper) :
    |∑ j, ((freeEdgeArray I j).cost : ℝ) * f j| ≤ I.m*U^2 := by
  have hc : (freeEdges I).card ≤ I.m := by
    simpa using Finset.card_le_card (Finset.subset_univ (freeEdges I))
  calc
    _ ≤ ∑ j, |((freeEdgeArray I j).cost : ℝ) * f j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin (freeEdges I).card, U^2 := by
      apply Finset.sum_le_sum
      intro j _
      obtain ⟨hl, hu, hcost⟩ := hn.2 (freeIndex I j).1
      change |((freeEdgeArray I j).lower : ℝ)| ≤ U at hl
      change |((freeEdgeArray I j).upper : ℝ)| ≤ U at hu
      have habs : |f j| ≤ U :=
        abs_le.mpr ⟨(abs_le.mp hl).1.trans (hf j).1, (hf j).2.trans (abs_le.mp hu).2⟩
      rw [abs_mul, pow_two]
      exact mul_le_mul hcost habs (abs_nonneg _) hU
    _ = (freeEdges I).card*U^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (sq_nonneg _)

/-- At a rounded optimum, any positive flow on an added pair edge costs at
least the penalty, which exceeds the entire range of retained-edge costs. -/
theorem connectedInitial_extra_zero (I : Instance) (U : ℝ) (K : ℤ)
    (hI : I.IsValid) (hU : 0 ≤ U) (hn : NumbersBounded I U)
    (hK : 2*I.m*U^2 < (K : ℝ)) (f : Fin I.m → ℝ) (hf : I.IsFeasible f)
    (g : Fin (connectedInitialInstance I K).m → ℝ)
    (hg : (connectedInitialInstance I K).IsMinCostFlow g) (hi : Rounding.IsIntegral g) :
    ∀ j, flowToArray (connectedInitialEdgeArray I K) (initialDemands I) g
      (Fin.natAdd _ j) = 0 := by
  let a := flowToArray (connectedInitialEdgeArray I K) (initialDemands I) g
  have ha := flowOfArray_flowToArray (connectedInitialEdgeArray I K) (initialDemands I) g
  have hg' := (feasible_flowOfArray_iff _ _ a).mp (ha.symm ▸ hg.1)
  let left := fun i => a (Fin.castAdd _ i)
  let right := fun i => a (Fin.natAdd _ i)
  let original := fun i => left (Fin.castAdd _ i)
  have hcap (i) : ((freeEdgeArray I i).lower : ℝ) ≤ original i ∧
      original i ≤ (freeEdgeArray I i).upper := by
    simpa only [original, left, connectedInitialEdgeArray, initialEdgeArray, Fin.addCases_left]
      using hg'.2 (Fin.castAdd _ (Fin.castAdd _ i))
  have hlo := (abs_le.mp (retained_cost_abs_le I U hU hn original hcap)).1
  have hKpos : 0 < (K : ℝ) :=
    lt_of_le_of_lt (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _)) hK
  have hdef (i) : 0 ≤ left (Fin.natAdd (freeEdges I).card i) := by
    simpa only [left, connectedInitialEdgeArray, initialEdgeArray, Fin.addCases_left,
      Fin.addCases_right, starEdge_lower, Int.cast_zero] using
      (hg'.2 (Fin.castAdd _ (Fin.natAdd (freeEdges I).card i))).1
  have hpair : ∀ i, (connectedInitialEdgeArray I K (Fin.natAdd _ i)).lower = 0 ∧
      (connectedInitialEdgeArray I K (Fin.natAdd _ i)).cost = K := by
    intro i
    simp only [connectedInitialEdgeArray, Fin.addCases_right]
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;>
      simp only [Fin.addCases_left, Fin.addCases_right, starEdge_lower, starEdge_cost, and_self]
  have hright (i) : 0 ≤ right i := by
    simpa only [right, (hpair i).1, Int.cast_zero] using (hg'.2 (Fin.natAdd _ i)).1
  let f₀ := embedInitialFlow I K (projectFreeFlow I f)
  have hf₀ := embedInitialFlow_feasible I K hI _ (feasible_projectFreeFlow I f hf)
  have hExt := extendConnectedInitialFlow_spec I K f₀ hf₀
  have hopt := hg.2 _ hExt.1
  rw [hExt.2, cost_embedInitialFlow] at hopt
  let b := flowToArray (freeEdgeArray I) (freeDemands I) (projectFreeFlow I f)
  have hb := flowOfArray_flowToArray (freeEdgeArray I) (freeDemands I) (projectFreeFlow I f)
  have hbcap := ((feasible_flowOfArray_iff _ _ b).mp
    (hb.symm ▸ feasible_projectFreeFlow I f hf)).2
  have hup := (abs_le.mp (retained_cost_abs_le I U hU hn b hbcap)).2
  have hcostB : (removeFixed I).cost (projectFreeFlow I f) =
      ∑ j, ((freeEdgeArray I j).cost : ℝ) * b j := by
    have hc := cost_flowOfArray (freeEdgeArray I) (freeDemands I) b
    rwa [hb] at hc
  rw [hcostB] at hopt
  intro j
  by_contra hj
  have hj' : right j ≠ 0 := hj
  obtain ⟨z, hz⟩ := hi ((arrayIndex (connectedInitialEdgeArray I K) (initialDemands I)).symm
    (Fin.natAdd _ j))
  change right j = (z : ℝ) at hz
  have hzPos : (0 : ℝ) < z := hz ▸ lt_of_le_of_ne (hright j) (Ne.symm hj')
  have hzInt : (0 : ℤ) < z := by exact_mod_cast hzPos
  have hone : (1 : ℝ) ≤ right j := by
    rw [hz]
    exact_mod_cast (Int.add_one_le_iff.mpr hzInt)
  have hsum : (K : ℝ) ≤ ∑ i, (K : ℝ)*right i := by
    have hsingle : (K : ℝ)*right j ≤ ∑ i, (K : ℝ)*right i :=
      Finset.single_le_sum (fun i _ => mul_nonneg hKpos.le (hright i)) (Finset.mem_univ j)
    nlinarith only [hsingle, mul_le_mul_of_nonneg_left hone hKpos.le]
  have hdefsum : 0 ≤ ∑ i, (K : ℝ)*left (Fin.natAdd (freeEdges I).card i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg hKpos.le (hdef i))
  have hgcost := cost_flowOfArray (connectedInitialEdgeArray I K) (initialDemands I) a
  rw [ha, Fin.sum_univ_add, Fin.sum_univ_add] at hgcost
  simp only [show ∀ i, (connectedInitialEdgeArray I K (Fin.natAdd _ i)).cost = K from
    fun i => (hpair i).2] at hgcost
  simp only [connectedInitialEdgeArray, initialEdgeArray, Fin.addCases_left,
    Fin.addCases_right, starEdge_cost] at hgcost
  change (connectedInitialInstance I K).cost g = _ at hgcost
  change -(I.m*U^2) ≤ ∑ i, ((freeEdgeArray I i).cost : ℝ) *
    a (Fin.castAdd _ (Fin.castAdd _ i)) at hlo
  change (K : ℝ) ≤ ∑ i, (K : ℝ)*a (Fin.natAdd _ i) at hsum
  change 0 ≤ ∑ i, (K : ℝ)*a (Fin.castAdd _ (Fin.natAdd (freeEdges I).card i)) at hdefsum
  linarith only [hgcost, hopt, hup, hlo, hsum, hdefsum, hK]

/-- Lemma 4.12 (page 31) recovery for a rounded optimum of the connected
augmentation. The added pairs can be discarded, and the old recovery
then removes the original artificial edges. -/
theorem connectedInitial_optimum_recovery (I : Instance) (U : ℝ) (K : ℤ)
    (hI : I.IsValid) (hU : 0 ≤ U) (hn : NumbersBounded I U)
    (hK : 2*I.m*U^2 < (K : ℝ)) (hK' : 2*I.m*U < (K : ℝ))
    (hordered : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper)
    (g : Fin (connectedInitialInstance I K).m → ℝ)
    (hg : (connectedInitialInstance I K).IsMinCostFlow g) (hi : Rounding.IsIntegral g) :
    I.IsMinCostFlow (recoverInitialFlow I K (restrictConnectedInitialFlow I K g)) ∨
      ¬ ∃ f, I.IsFeasible f := by
  by_cases hfeasible : ∃ f, I.IsFeasible f
  · obtain ⟨f, hf⟩ := hfeasible
    have hz := connectedInitial_extra_zero I U K hI hU hn hK f hf g hg hi
    have hr := restrictConnectedInitialFlow_spec I K g hg.1 hz
    have hopt : (initialInstance I K).IsMinCostFlow (restrictConnectedInitialFlow I K g) := by
      refine ⟨hr.1, fun p hp => ?_⟩
      have he := extendConnectedInitialFlow_spec I K p hp
      rw [hr.2, ← he.2]
      exact hg.2 _ he.1
    have hpos : 0 ≤ (K : ℝ) :=
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hU).trans hK'.le
    exact initial_optimum_recovery I U K hI hordered hU hn hpos hK' _ hopt
  · exact Or.inr hfeasible

end MinCostFlow.IPM
