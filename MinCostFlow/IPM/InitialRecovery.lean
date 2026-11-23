module

public import MinCostFlow.IPM.InitialConstruction
import MinCostFlow.IPM.InitialCost
import MinCostFlow.IPM.InitialDomain
import MinCostFlow.IPM.InitialRouting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Recovery from an augmented flow with zero auxiliary flow

Appendix B.1 (page 92) of Chen et al., arXiv:2203.00671v2, recovers the original
solution by discarding the auxiliary edges. This file proves that step
for real flows when those edges are zero. Feasible original flows embed
with zero auxiliary flow and unchanged reduced cost, so optimality is
preserved by projection and by reinserting fixed edges.
-/

@[expose] public section
namespace MinCostFlow.IPM

/-- The original retained part of an augmented flow. -/
def initialOriginalFlow (I : Instance) (K : ℤ) (g : Fin (initialInstance I K).m → ℝ) :
    Fin (removeFixed I).m → ℝ :=
  flowOfArray (freeEdgeArray I) (freeDemands I) (fun j =>
    flowToArray (initialEdgeArray I K) (initialDemands I) g (Fin.castAdd (deficitVertices I).card j))

/-- The auxiliary part of an augmented flow. -/
def initialAuxiliaryFlow (I : Instance) (K : ℤ) (g : Fin (initialInstance I K).m → ℝ)
    (j : Fin (deficitVertices I).card) : ℝ :=
  flowToArray (initialEdgeArray I K) (initialDemands I) g (Fin.natAdd (freeEdges I).card j)

/-- Embed a reduced original flow with zero auxiliary flows. -/
def embedInitialFlow (I : Instance) (K : ℤ) (f : Fin (removeFixed I).m → ℝ) :
    Fin (initialInstance I K).m → ℝ :=
  flowOfArray (initialEdgeArray I K) (initialDemands I)
    (Fin.addCases (flowToArray (freeEdgeArray I) (freeDemands I) f) (fun _ => 0))

/-- The recovered original flow, including its forced-capacity edges. -/
def recoverInitialFlow (I : Instance) (K : ℤ) (g : Fin (initialInstance I K).m → ℝ) :
    Fin I.m → ℝ := liftFreeFlow I (initialOriginalFlow I K g)

private theorem augmented_array_feasible (I : Instance) (K : ℤ)
    (g : Fin (initialInstance I K).m → ℝ) (hg : (initialInstance I K).IsFeasible g) :
    (∀ v : Fin (I.n+1), ∑ e, (initialEdgeArray I K e).b v*
      flowToArray (initialEdgeArray I K) (initialDemands I) g e = (initialDemands I v : ℝ)) ∧
    ∀ e, ((initialEdgeArray I K e).lower : ℝ) ≤
        flowToArray (initialEdgeArray I K) (initialDemands I) g e ∧
      flowToArray (initialEdgeArray I K) (initialDemands I) g e ≤ (initialEdgeArray I K e).upper := by
  have heq : flowOfArray (initialEdgeArray I K) (initialDemands I)
      (flowToArray (initialEdgeArray I K) (initialDemands I) g) = g :=
    flowOfArray_flowToArray (initialEdgeArray I K) (initialDemands I) g
  exact (feasible_flowOfArray_iff _ _ _).mp (heq.symm ▸ hg)

/-- Removing zero auxiliary flows gives a feasible reduced original flow. -/
theorem initialOriginalFlow_feasible (I : Instance) (K : ℤ)
    (g : Fin (initialInstance I K).m → ℝ) (hg : (initialInstance I K).IsFeasible g)
    (hzero : ∀ j, initialAuxiliaryFlow I K g j = 0) :
    (removeFixed I).IsFeasible (initialOriginalFlow I K g) := by
  have harr := augmented_array_feasible I K g hg
  apply (feasible_flowOfArray_iff (freeEdgeArray I) (freeDemands I) _).mpr
  constructor
  · intro v
    have hr := harr.1 v.castSucc
    rw [Fin.sum_univ_add] at hr
    simp only [initialEdgeArray, Fin.addCases_left, Fin.addCases_right, Fin.val_castSucc,
      initialDemands, Fin.lastCases_castSucc] at hr
    have hz : ∀ j, flowToArray (initialEdgeArray I K) (initialDemands I) g
        (Fin.natAdd (freeEdges I).card j) = 0 := hzero
    simpa only [hz, mul_zero, Finset.sum_const_zero, add_zero] using hr
  · intro j
    have hc := harr.2 (Fin.castAdd (deficitVertices I).card j)
    simpa only [initialEdgeArray, Fin.addCases_left] using hc

/-- A feasible reduced original flow embeds into the augmented instance. -/
theorem embedInitialFlow_feasible (I : Instance) (K : ℤ) (hI : I.IsValid)
    (f : Fin (removeFixed I).m → ℝ) (hf : (removeFixed I).IsFeasible f) :
    (initialInstance I K).IsFeasible (embedInitialFlow I K f) := by
  let g := flowToArray (freeEdgeArray I) (freeDemands I) f
  have heq : flowOfArray (freeEdgeArray I) (freeDemands I) g = f :=
    flowOfArray_flowToArray (freeEdgeArray I) (freeDemands I) f
  have harr := (feasible_flowOfArray_iff (freeEdgeArray I) (freeDemands I) g).mp (heq.symm ▸ hf)
  apply (feasible_flowOfArray_iff (initialEdgeArray I K) (initialDemands I) _).mpr
  constructor
  · intro v
    refine Fin.lastCases ?_ (fun w => ?_) v
    · simp only [Fin.val_last, initialDemands, Fin.lastCases_last, Int.cast_zero]
      rw [Fin.sum_univ_add]
      simp only [initialEdgeArray, Fin.addCases_left, Fin.addCases_right,
        mul_zero, Finset.sum_const_zero, add_zero]
      apply Finset.sum_eq_zero
      intro j _
      have ht := hI.1 (I.edge (freeIndex I j).1) (List.getElem_mem ((freeIndex I j).1).2)
      have htail : I.n ≠ (freeEdgeArray I j).tail := (Nat.ne_of_lt ht.1).symm
      have hhead : I.n ≠ (freeEdgeArray I j).head := (Nat.ne_of_lt ht.2).symm
      simp only [Edge.b, htail, hhead, ↓reduceIte, sub_self, zero_mul]
    · simp only [Fin.val_castSucc, initialDemands, Fin.lastCases_castSucc]
      rw [Fin.sum_univ_add]
      simpa only [initialEdgeArray, Fin.addCases_left, Fin.addCases_right,
        mul_zero, Finset.sum_const_zero, add_zero] using harr.1 w
  · intro e
    refine Fin.addCases (fun j => ?_) (fun j => ?_) e
    · simpa only [initialEdgeArray, Fin.addCases_left] using harr.2 j
    · simp only [initialEdgeArray, Fin.addCases_right, starEdge_lower, starEdge_upper, Int.cast_zero, le_refl, true_and]
      exact_mod_cast abs_nonneg (twiceDeficit I (deficitIndex I j).1)

/-- Embedding adds no cost. -/
theorem cost_embedInitialFlow (I : Instance) (K : ℤ) (f : Fin (removeFixed I).m → ℝ) :
    (initialInstance I K).cost (embedInitialFlow I K f) = (removeFixed I).cost f := by
  have hc := initialInstance_cost_array I K
    (Fin.addCases (flowToArray (freeEdgeArray I) (freeDemands I) f) (fun _ => 0))
  simp only [Fin.addCases_left, Fin.addCases_right, mul_zero, Finset.sum_const_zero, add_zero] at hc
  have hfree : (removeFixed I).cost f = ∑ j, ((freeEdgeArray I j).cost : ℝ)*
      flowToArray (freeEdgeArray I) (freeDemands I) f j := by
    have ht := cost_flowOfArray (freeEdgeArray I) (freeDemands I)
      (flowToArray (freeEdgeArray I) (freeDemands I) f)
    have heq : flowOfArray (freeEdgeArray I) (freeDemands I)
        (flowToArray (freeEdgeArray I) (freeDemands I) f) = f :=
      flowOfArray_flowToArray (freeEdgeArray I) (freeDemands I) f
    rw [heq] at ht
    exact ht
  exact hc.trans hfree.symm

/-- Projection of zero auxiliary flow preserves cost. -/
theorem cost_initialOriginalFlow (I : Instance) (K : ℤ)
    (g : Fin (initialInstance I K).m → ℝ) (hzero : ∀ j, initialAuxiliaryFlow I K g j = 0) :
    (removeFixed I).cost (initialOriginalFlow I K g) = (initialInstance I K).cost g := by
  have hc := initialInstance_cost_array I K (flowToArray (initialEdgeArray I K) (initialDemands I) g)
  have heq : flowOfArray (initialEdgeArray I K) (initialDemands I)
      (flowToArray (initialEdgeArray I K) (initialDemands I) g) = g :=
    flowOfArray_flowToArray (initialEdgeArray I K) (initialDemands I) g
  rw [heq] at hc
  have hz : ∀ j, flowToArray (initialEdgeArray I K) (initialDemands I) g
      (Fin.natAdd (freeEdges I).card j) = 0 := hzero
  simp only [hz, mul_zero, Finset.sum_const_zero, add_zero] at hc
  have hfree := cost_flowOfArray (freeEdgeArray I) (freeDemands I)
    (fun j => flowToArray (initialEdgeArray I K) (initialDemands I) g (Fin.castAdd (deficitVertices I).card j))
  exact hfree.trans hc.symm

/-- The zero-auxiliary-flow branch of Lemma 4.12 (page 31)'s recovery, for arbitrary
real optimal flows on the augmented instance. -/
theorem recoverInitialFlow_minCost (I : Instance) (K : ℤ) (hI : I.IsValid)
    (hordered : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper)
    (g : Fin (initialInstance I K).m → ℝ) (hg : (initialInstance I K).IsMinCostFlow g)
    (hzero : ∀ j, initialAuxiliaryFlow I K g j = 0) : I.IsMinCostFlow (recoverInitialFlow I K g) := by
  apply minCostFlow_liftFreeFlow I _ hordered
  refine ⟨initialOriginalFlow_feasible I K g hg.1 hzero, ?_⟩
  intro f hf
  have hopt := hg.2 (embedInitialFlow I K f) (embedInitialFlow_feasible I K hI f hf)
  rw [cost_embedInitialFlow] at hopt
  rw [cost_initialOriginalFlow I K g hzero]
  exact hopt

end MinCostFlow.IPM
