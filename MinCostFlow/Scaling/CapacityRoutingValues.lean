module

public import MinCostFlow.Scaling.CapacityPositiveContract
public import MinCostFlow.Scaling.RoutingCorrectionBounds
import MinCostFlow.Scaling.CapacityScalingCorrectness
import MinCostFlow.Scaling.RoutingResidualBounds

/-!
# Exact routing values for capacity-backed dual extraction

Name the correction and augmented routing that occur in the measured cost
model when its inner procedure is capacity scaling. The actual capacity
model is optimal on the positive routing residual, so dummy erasure gives
a feasible correction. Its augmented routing and unsigned scan therefore
satisfy the same elementary capacity bounds used by label propagation.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The correction in the measured dual model's actual inner capacity call. -/
noncomputable def capacityRoutingCorrection (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch)) (J : Circulation) (U : ℕ) :
    Fin ((J.m+J.n)+(J.m+J.n)) → ℤ :=
  let Q := J.shortestRoutingGraph.residual J.shortestRoutingStart
  (Q.invokePositive (fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U)).value

/-- The measured model augments its direct routing by forward minus reverse correction. -/
noncomputable def capacitySolvedRouting (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch)) (J : Circulation) (U : ℕ) :
    Fin (J.m+J.n) → ℤ :=
  let delta := capacityRoutingCorrection solver entry T hproc J U
  fun e => J.shortestRoutingStart e+delta (Fin.castAdd (J.m+J.n) e)-delta (Fin.natAdd (J.m+J.n) e)

/-- The actual routing correction is optimal under the routing input's
polynomial cost bound and its supplied capacity bound. -/
theorem capacityRoutingCorrection_optimal (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch)) (J : Circulation) (U : ℕ)
    (hc : J.CostsBounded (J.m^10)) (hu : J.n+1≤U) :
    (J.shortestRoutingGraph.residual J.shortestRoutingStart).Optimal
      (fun e => (capacityRoutingCorrection solver entry T hproc J U e : ℝ)) := by
  let solve := canonicalSolver solver entry T hproc
  let Q := J.shortestRoutingGraph.residual J.shortestRoutingStart
  have hsolve := fun K (_ : K.CostsBounded (K.m^10))
    (_ : ∀ e,1≤K.capacity e ∧ K.capacity e≤K.m^40) => canonicalSolver_optimal solver entry T hproc K
  have hcap : ∀ e,Q.capacity e≤U := by
    have h := J.shortestRoutingGraph.residual_capacities_le J.shortestRoutingStart
      J.shortestRoutingStart_bounds (J.n+1) J.shortestRoutingGraph_capacities
    exact fun e => (h e).trans hu
  have hposCap := Q.positiveInstance_capacitiesBounded U (by omega) hcap
  have hposCost := Q.positiveInstance_costsBounded _ (routingResidual_cost_bound J hc)
  have hopt := lemma_C_9 solve hsolve Q.positiveInstance U hposCost (fun e => (hposCap e).2)
  exact Circulation.solveWithZeroCapacities_of_optimal (fun K => (capacityScalingModel solve K U).value) Q hopt

/-- The model's actual augmented routing lies within its graph's capacities. -/
theorem capacitySolvedRouting_bounds (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch)) (J : Circulation) (U : ℕ)
    (hc : J.CostsBounded (J.m^10)) (hu : J.n+1≤U) :
    ∀ e,0≤capacitySolvedRouting solver entry T hproc J U e ∧
      capacitySolvedRouting solver entry T hproc J U e≤(J.shortestRoutingGraph.capacity e : ℤ) :=
  (routingCorrection_bounds J _ (capacityRoutingCorrection_optimal solver entry T hproc J U hc hu).1).2

/-- A fitting `n+2` budget covers every intermediate unsigned augmentation
sum for the actual capacity-model correction. -/
theorem capacitySolvedRouting_scan_bounds (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch)) (J : Circulation) (U w : ℕ)
    (hc : J.CostsBounded (J.m^10)) (hu : J.n+1≤U) (hw : J.n+2<2^w) :
    let delta := capacityRoutingCorrection solver entry T hproc J U
    ∀ e,(J.shortestRoutingStart e).toNat+(delta (Fin.castAdd (J.m+J.n) e)).toNat<2^w ∧
      (delta (Fin.natAdd (J.m+J.n) e)).toNat<2^w :=
  routingCorrection_scan_bounds J w _ (capacityRoutingCorrection_optimal solver entry T hproc J U hc hu).1 hw

end MinCostFlow.Scaling.Machine
