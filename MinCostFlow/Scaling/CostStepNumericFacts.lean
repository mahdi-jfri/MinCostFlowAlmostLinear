module

public import MinCostFlow.Scaling.CapacityPositiveContract
public import MinCostFlow.Scaling.CostLoopBounds
import MinCostFlow.Scaling.CapacityScalingCorrectness
import MinCostFlow.Scaling.CapacityNumericFacts
import MinCostFlow.Scaling.LabelBounds

/-!
# Numerical facts for the measured cost-state update

The actual inner capacity model gives an optimal positive-instance flow.
Erasing dummy slots gives a feasible rounded residual correction, so the
new primal flow respects the original capacities. Separately, the integer
label traversal adds at most one cost magnitude per allowed step. This
bounds the extracted dual numerators needed by the potential-table update.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The exact positive adapter of the capacity model is optimal whenever
its input has its own polynomial cost bound and the supplied capacity bound. -/
theorem capacityPositive_optimal (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (U : ℕ) (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤U) (hU : 1≤U) :
    J.Optimal (fun e => ((J.invokePositive
      (fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U)).value e : ℝ)) := by
  let solve := canonicalSolver solver entry T hproc
  have hsolve := fun K (_ : K.CostsBounded (K.m^10))
    (_ : ∀ e,1≤K.capacity e ∧ K.capacity e≤K.m^40) => canonicalSolver_optimal solver entry T hproc K
  have hposCap := J.positiveInstance_capacitiesBounded U hU hu
  have hopt := lemma_C_9 solve hsolve J.positiveInstance U (J.positiveInstance_costsBounded _ hc)
    (fun e => (hposCap e).2)
  exact Circulation.solveWithZeroCapacities_of_optimal (fun K => (capacityScalingModel solve K U).value) J hopt

/-- Labels propagated from the zero vector have magnitude at most one
edge-cost bound per allowed traversal step. -/
theorem propagateLabels_natAbs_le (J : Circulation) (flow : Fin J.m → ℤ) (root : Fin J.n) (C : ℕ)
    (hc : J.CostsBounded C) :
    ∀ v,((J.propagateLabels flow root).1.labels v).natAbs≤J.m*C := by
  have h := Circulation.LabelState.run_labels_bound J.m (J.initialLabelState flow root) 0 C
    (fun _ => le_rfl) hc
  simpa only [Circulation.propagateLabels,Nat.zero_add] using h

/-- Measured dual extraction bounds every returned potential numerator
by the source-routing edge count times the original cost bound. -/
theorem extractDualMeasured_natAbs_le
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ)) (J : Circulation)
    (flow : Fin J.m → ℤ) (C : ℕ) (hc : J.CostsBounded C) :
    ∀ v,((J.extractDualMeasured inner flow).value v).natAbs≤(2*J.m+J.n)*C := by
  let R := J.residual flow
  let S := R.shortestRoutingGraph
  let delta := (R.shortestRoutingGraph.residual R.shortestRoutingStart).invokePositive inner
  let routing : Fin S.m → ℤ := fun e => R.shortestRoutingStart e+
    delta.value (Fin.castAdd S.m e)-delta.value (Fin.natAdd S.m e)
  have hcostS := R.shortestRoutingGraph_costsBounded C (J.residual_costsBounded flow C hc)
  have h := propagateLabels_natAbs_le S routing (Fin.last J.n) C hcostS
  intro v
  have hv := h v.castSucc
  change ((J.extractDualMeasured inner flow).value v).natAbs≤(J.m+J.m+J.n)*C at hv
  simpa only [Nat.two_mul] using hv

/-- The rounded residual's capacities stay within the original capacity
bound whenever the current integral flow respects those capacities. -/
theorem costRounded_capacities_le {J : Circulation} (s : CostState J) (C U : ℕ)
    (hf : ∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e) (hu : ∀ e,J.capacity e≤U) :
    ∀ e,(s.roundedInstance C).capacity e≤U :=
  J.residual_capacities_le s.flow (integral_capacity_bounds_cast J s.flow hf) U hu

/-- The actual capacity-backed measured cost step preserves all integral
capacity constraints, even without assuming conservation of the current flow. -/
theorem costStepMeasured_flow_bounds (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    {J : Circulation} (s : CostState J) (C U : ℕ)
    (hf : ∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e) (hu : ∀ e,J.capacity e≤U) (hU : 1≤U) :
    ∀ e,0≤(CostState.stepMeasured (fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U) C s).value.flow e ∧
      (CostState.stepMeasured (fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U) C s).value.flow e≤J.capacity e := by
  let K := s.roundedInstance C
  let delta := (K.invokePositive (fun L => capacityScalingModel (canonicalSolver solver entry T hproc) L U)).value
  have hopt := capacityPositive_optimal solver entry T hproc K U (s.roundedInstance_polynomialCosts C)
    (costRounded_capacities_le s C U hf hu) hU
  have hfeas : (J.residual s.flow).Feasible (fun e => (delta e : ℝ)) := hopt.1
  exact residualAugment_integral_bounds J s.flow delta hf hfeas

end MinCostFlow.Scaling.Machine
