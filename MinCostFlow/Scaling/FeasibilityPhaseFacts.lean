module

public import MinCostFlow.Scaling.FeasibilityPhaseContract
import MinCostFlow.Scaling.PrunedScalingOutputBounds

/-!
# Arithmetic facts for the complete feasibility solve

The auxiliary circulation has costs zero on original edges and minus one
on artificial edges. Its exact restored optimum is therefore nonnegative
and capacity bounded. Those input bounds also bound every objective-scan
product and the total absolute shifted demand. These are the numerical
premises used by the already proved threshold and conversion procedures.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Feasibility circulation costs have absolute value at most one,
independently of the original instance's costs. -/
theorem buildFeasibility_costs_le_one (I : Instance) (hv : I.IsValid) :
    (FlowReduction.buildFeasibilityInstance I hv).CostsBounded 1 := by
  intro e
  change ((Fin.addCases (fun _ : Fin I.m => (0 : ℤ))
    (fun _ : Fin (I.n+I.n) => -1) : Fin (I.m+(I.n+I.n)) → ℤ) e).natAbs≤1
  induction e using Fin.addCases
  · simp only [Fin.addCases_left,Int.natAbs_zero]; omega
  · simp only [Fin.addCases_right]; decide

/-- The shifted demand mass fits the vertex count times the static
capacity budget used by the composed solver. -/
theorem shiftedDemands_mass_le (I : Instance) (hv : I.IsValid) (U : ℕ)
    (hd : ∀ v : Fin I.n,(I.d v).natAbs≤U)
    (hl : ∀ e : Fin I.m,(I.edge e).lower.natAbs≤U) :
    ((List.ofFn (FlowReduction.buildShiftedDemands I hv)).map Int.natAbs).sum≤
      I.n*FlowReduction.scalingCapacityBudget I U := by
  rw [List.map_ofFn,List.sum_ofFn]
  calc
    _ ≤ ∑ _ : Fin I.n,FlowReduction.scalingCapacityBudget I U := by
      apply Finset.sum_le_sum
      intro v _
      change (FlowReduction.buildShiftedDemands I hv v).natAbs≤_
      rw [FlowReduction.buildShiftedDemands_eq]
      have hb := FlowReduction.shiftedDemand_natAbs_le I U hd hl v
      unfold FlowReduction.scalingCapacityBudget
      have hh := Nat.mul_le_mul_right U (show I.m+1≤2*(I.m+1) by omega)
      omega
    _ = _ := by simp

/-- Converting the signed magnitudes of a nonnegative vector gives
exactly its unsigned solver-layout coordinates. -/
theorem nonnegative_magnitudes_eq_unsigned {n : ℕ} (f : Fin n → ℤ) (hf : ∀ e,0≤f e) :
    (List.ofFn f).map Int.natAbs=List.ofFn (fun e => (f e).toNat) := by
  rw [List.map_ofFn]
  congr 1
  funext e
  have he := congrArg Int.natAbs (Int.toNat_of_nonneg (hf e))
  simpa only [Int.natAbs_natCast,Function.comp_def] using he.symm

/-- The exact pruned feasibility solution's absolute-product scan budget
is at most the number of auxiliary edges times its static capacity bound. -/
theorem feasibilityObjective_mass_le (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) (C U : ℕ) (hC : 1≤C)
    (hd : ∀ v : Fin I.n,(I.d v).natAbs≤U)
    (hl : ∀ e : Fin I.m,(I.edge e).lower.natAbs≤U)
    (hu : ∀ e : Fin I.m,(I.edge e).upper.natAbs≤U) :
    let P := FlowReduction.buildFeasibilityInstance I hv
    let B := FlowReduction.scalingCapacityBudget I U
    let g := (Circulation.invokePruned
      (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C B) P).value
    objectiveScanMass P (fun e => (g e).toNat) (List.finRange P.m)≤P.m*B := by
  dsimp only
  let P := FlowReduction.buildFeasibilityInstance I hv
  let B := FlowReduction.scalingCapacityBudget I U
  have hcost : P.CostsBounded C := fun e => (buildFeasibility_costs_le_one I hv e).trans hC
  have hcap := FlowReduction.buildFeasibilityInstance_capacity_le I hv U hd hl hu
  have hb : 1≤B := by unfold B FlowReduction.scalingCapacityBudget; omega
  have hf := prunedScalingModel_output_bounds solver entry T hproc P C B hcost hcap hb
  let g := (Circulation.invokePruned
    (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C B) P).value
  have hg : ∀ e,(g e).toNat≤B := by
    intro e
    exact (Int.toNat_le_toNat (hf e).2).trans
      (by simpa only [Int.toNat_natCast] using hcap e)
  have h := objectiveScanMass_le P (fun e => (g e).toNat) (List.finRange P.m) 1 B
    (fun e _ => buildFeasibility_costs_le_one I hv e) (fun e _ => hg e)
  simpa only [List.length_finRange,Nat.one_mul] using h

end MinCostFlow.Scaling.Machine
