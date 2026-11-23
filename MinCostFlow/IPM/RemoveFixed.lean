module

public import MinCostFlow.IPM.InstanceArrays
public import Mathlib.Data.Finset.Sort
import MinCostFlow.IPM.CapacityPreprocessing
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Removing fixed-capacity edges before initialization

Appendix B.1 (page 92) of Chen et al., arXiv:2203.00671v2, uses midpoints with
positive slacks. Before that construction we keep precisely the edges
with lower capacity strictly below upper capacity. Every removed edge
has its forced lower-capacity flow. Its integral demand contribution is
subtracted from the demand vector, and its cost is a fixed offset.
The edge enumeration is increasing, so it is a specified construction.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM

/-- The integer incidence coefficient underlying `Edge.b`. -/
def incidenceInt (e : Edge) (v : ℕ) : ℤ :=
  (if v = e.tail then 1 else 0) - (if v = e.head then 1 else 0)

/-- Integer incidence agrees with the real incidence used for routing. -/
theorem incidenceInt_cast (e : Edge) (v : ℕ) : (incidenceInt e v : ℝ) = e.b v := by
  simp only [incidenceInt, Edge.b, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero]

/-- The edges that remain after fixed-capacity preprocessing. -/
def freeEdges (I : Instance) : Finset (Fin I.m) :=
  Finset.univ.filter fun e => (I.edge e).lower < (I.edge e).upper

/-- The increasing index map for the remaining edges. -/
def freeIndex (I : Instance) : Fin (freeEdges I).card ≃ {e // e ∈ freeEdges I} :=
  ((freeEdges I).orderIsoOfFin rfl).toEquiv

/-- The integral fixed flow on removed edges, zero on retained edges. -/
def fixedFlow (I : Instance) (e : Fin I.m) : ℤ :=
  if e ∈ freeEdges I then 0 else (I.edge e).lower

/-- Demands after subtracting the forced routing contributions. -/
def freeDemands (I : Instance) (v : Fin I.n) : ℤ :=
  I.d v - ∑ e, incidenceInt (I.edge e) v*fixedFlow I e

/-- The retained edge array. -/
def freeEdgeArray (I : Instance) (e : Fin (freeEdges I).card) : Edge :=
  I.edge (freeIndex I e).1

/-- The instance with fixed-capacity edges removed. Reversed capacity
intervals must first be rejected using `infeasible_of_reversed_capacity`. -/
def removeFixed (I : Instance) : Instance :=
  instanceOfArrays I.n (freeEdges I).card (freeEdgeArray I) (freeDemands I)

/-- Insert the forced flows around the retained flow coordinates. -/
def expandFreeFlow (I : Instance) (g : Fin (freeEdges I).card → ℝ) (e : Fin I.m) : ℝ :=
  if he : e ∈ freeEdges I then g ((freeIndex I).symm ⟨e, he⟩) else (I.edge e).lower

/-- Project an original flow to the instance with fixed edges removed. -/
def projectFreeFlow (I : Instance) (f : Fin I.m → ℝ) : Fin (removeFixed I).m → ℝ :=
  flowOfArray (freeEdgeArray I) (freeDemands I) (fun e => f (freeIndex I e).1)

/-- Reconstruct an original flow from a flow on the reduced instance. -/
def liftFreeFlow (I : Instance) (g : Fin (removeFixed I).m → ℝ) : Fin I.m → ℝ :=
  expandFreeFlow I (flowToArray (freeEdgeArray I) (freeDemands I) g)

/-- The constant objective offset from removed edges. -/
def fixedCost (I : Instance) : ℝ := ∑ e, ((I.edge e).cost : ℝ)*fixedFlow I e

/-- A retained edge has strictly ordered capacities. -/
theorem freeEdgeArray_strict (I : Instance) (e : Fin (freeEdges I).card) :
    (freeEdgeArray I e).lower < (freeEdgeArray I e).upper :=
  (Finset.mem_filter.mp (freeIndex I e).2).2

/-- The fixed contribution to a demand after casting to real numbers. -/
theorem freeDemands_cast (I : Instance) (v : Fin I.n) :
    (freeDemands I v : ℝ) = I.d v - ∑ e, (I.edge e).b v*(fixedFlow I e : ℝ) := by
  simp only [freeDemands, Int.cast_sub, Int.cast_sum, Int.cast_mul, incidenceInt_cast]

/-- A linear sum on an expanded flow splits into the retained contribution
and the fixed contribution. This is used for both routing and cost. -/
theorem sum_expandFreeFlow (I : Instance) (w : Fin I.m → ℝ)
    (g : Fin (freeEdges I).card → ℝ) :
    (∑ e, w e*expandFreeFlow I g e) =
      (∑ j, w (freeIndex I j).1*g j) + ∑ e, w e*(fixedFlow I e : ℝ) := by
  have hpoint : ∀ e, w e*expandFreeFlow I g e = w e*(fixedFlow I e : ℝ) +
      (if he : e ∈ freeEdges I then w e*g ((freeIndex I).symm ⟨e, he⟩) else 0) := by
    intro e
    by_cases he : e ∈ freeEdges I <;> simp only [expandFreeFlow, fixedFlow, he, ↓reduceDIte,
      ↓reduceIte, Int.cast_zero, mul_zero, zero_add, add_zero]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, add_comm]
  congr 1
  calc
    (∑ e, if he : e ∈ freeEdges I then w e*g ((freeIndex I).symm ⟨e, he⟩) else 0) =
        ∑ e : {e // e ∈ freeEdges I}, w e.1*g ((freeIndex I).symm e) := by
      rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach_eq_sum_dite]
    _ = ∑ j, w (freeIndex I j).1*g j := by
      simpa only [Equiv.symm_apply_apply] using
        ((freeIndex I).sum_comp (fun e => w e.1*g ((freeIndex I).symm e))).symm

/-- Reconstruction after projection recovers every feasible original flow. -/
theorem expand_project_feasible (I : Instance) (f : Fin I.m → ℝ) (hf : I.IsFeasible f) :
    expandFreeFlow I (fun e => f (freeIndex I e).1) = f := by
  funext e
  by_cases he : e ∈ freeEdges I
  · simp only [expandFreeFlow, he, ↓reduceDIte, Equiv.apply_symm_apply]
  · have hn : ¬ (I.edge e).lower < (I.edge e).upper := by
      intro h
      exact he (Finset.mem_filter.mpr ⟨Finset.mem_univ e, h⟩)
    have hlo : ((I.edge e).lower : ℝ) ≤ (I.edge e).upper := (hf.2 e).1.trans (hf.2 e).2
    have hi : (I.edge e).lower = (I.edge e).upper := le_antisymm (by exact_mod_cast hlo) (not_lt.mp hn)
    simp only [expandFreeFlow, he, ↓reduceDIte]
    exact (flow_eq_of_fixed_capacity I e hi f hf).symm

/-- Every feasible reduced flow reconstructs to a feasible original flow,
provided reversed capacity intervals have been rejected. -/
theorem feasible_liftFreeFlow (I : Instance) (g : Fin (removeFixed I).m → ℝ)
    (hordered : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper)
    (hg : (removeFixed I).IsFeasible g) : I.IsFeasible (liftFreeFlow I g) := by
  have heq := flowOfArray_flowToArray (freeEdgeArray I) (freeDemands I) g
  have harr := (feasible_flowOfArray_iff (freeEdgeArray I) (freeDemands I)
    (flowToArray (freeEdgeArray I) (freeDemands I) g)).mp (heq.symm ▸ hg)
  constructor
  · intro v
    have ht := sum_expandFreeFlow I (fun e => (I.edge e).b v)
      (flowToArray (freeEdgeArray I) (freeDemands I) g)
    have hr := harr.1 v
    rw [freeDemands_cast] at hr
    dsimp only [freeEdgeArray] at hr
    dsimp only [liftFreeFlow]
    linarith only [ht, hr]
  · intro e
    by_cases he : e ∈ freeEdges I
    · have ht := harr.2 ((freeIndex I).symm ⟨e, he⟩)
      simpa only [liftFreeFlow, expandFreeFlow, he, ↓reduceDIte, freeEdgeArray,
        Equiv.apply_symm_apply] using ht
    · simp only [liftFreeFlow, expandFreeFlow, he, ↓reduceDIte, le_refl, true_and]
      exact_mod_cast hordered e

/-- Every feasible original flow projects to a feasible reduced flow. -/
theorem feasible_projectFreeFlow (I : Instance) (f : Fin I.m → ℝ) (hf : I.IsFeasible f) :
    (removeFixed I).IsFeasible (projectFreeFlow I f) := by
  apply (feasible_flowOfArray_iff (freeEdgeArray I) (freeDemands I)
    (fun e => f (freeIndex I e).1)).mpr
  constructor
  · intro v
    have ht := sum_expandFreeFlow I (fun e => (I.edge e).b v) (fun e => f (freeIndex I e).1)
    rw [expand_project_feasible I f hf] at ht
    rw [freeDemands_cast]
    dsimp only [freeEdgeArray]
    have hr := hf.1 v
    linarith only [ht, hr]
  · intro e
    exact hf.2 (freeIndex I e).1

/-- Reconstructing a projected feasible flow gives the original flow. -/
theorem lift_projectFreeFlow (I : Instance) (f : Fin I.m → ℝ) (hf : I.IsFeasible f) :
    liftFreeFlow I (projectFreeFlow I f) = f := by
  dsimp only [liftFreeFlow, projectFreeFlow, flowToArray, flowOfArray]
  exact expand_project_feasible I f hf

/-- The reconstruction changes the objective by exactly the fixed cost. -/
theorem cost_liftFreeFlow (I : Instance) (g : Fin (removeFixed I).m → ℝ) :
    I.cost (liftFreeFlow I g) = (removeFixed I).cost g+fixedCost I := by
  have ht := sum_expandFreeFlow I (fun e => ((I.edge e).cost : ℝ))
    (flowToArray (freeEdgeArray I) (freeDemands I) g)
  have hc := cost_flowOfArray (freeEdgeArray I) (freeDemands I)
    (flowToArray (freeEdgeArray I) (freeDemands I) g)
  have heq : flowOfArray (freeEdgeArray I) (freeDemands I)
      (flowToArray (freeEdgeArray I) (freeDemands I) g) = g :=
    flowOfArray_flowToArray (freeEdgeArray I) (freeDemands I) g
  rw [heq] at hc
  dsimp only [freeEdgeArray] at hc
  exact ht.trans (congrArg (fun x => x+fixedCost I) hc.symm)

/-- Projecting a feasible flow subtracts exactly the fixed cost. -/
theorem cost_projectFreeFlow (I : Instance) (f : Fin I.m → ℝ) (hf : I.IsFeasible f) :
    (removeFixed I).cost (projectFreeFlow I f)+fixedCost I = I.cost f := by
  rw [← cost_liftFreeFlow, lift_projectFreeFlow I f hf]

/-- Optimal solutions of the reduced instance recover optimal solutions
of the original instance. This step needs no integrality theorem. -/
theorem minCostFlow_liftFreeFlow (I : Instance) (g : Fin (removeFixed I).m → ℝ)
    (hordered : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper)
    (hg : (removeFixed I).IsMinCostFlow g) : I.IsMinCostFlow (liftFreeFlow I g) := by
  refine ⟨feasible_liftFreeFlow I g hordered hg.1, ?_⟩
  intro f hf
  have hopt := hg.2 (projectFreeFlow I f) (feasible_projectFreeFlow I f hf)
  rw [cost_liftFreeFlow]
  have hc := cost_projectFreeFlow I f hf
  linarith only [hopt, hc]

/-- The reduced instance is infeasible only if the original is infeasible. -/
theorem infeasible_of_removeFixed (I : Instance)
    (hno : ¬ ∃ g, (removeFixed I).IsFeasible g) : ¬ ∃ f, I.IsFeasible f := by
  rintro ⟨f, hf⟩
  exact hno ⟨projectFreeFlow I f, feasible_projectFreeFlow I f hf⟩

end MinCostFlow.IPM
