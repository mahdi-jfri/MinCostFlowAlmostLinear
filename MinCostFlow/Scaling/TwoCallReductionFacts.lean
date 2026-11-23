module

public import MinCostFlow.Scaling.FeasibilityPhaseContract
import MinCostFlow.Scaling.FeasibilityPhaseFacts
import MinCostFlow.Scaling.PrunedScalingOutputBounds

/-!
# Passing the first circulation's flow to residual optimization

The feasibility circulation places the original edges first, with exactly
the shifted graph's capacities. Its optimal pruned solution therefore
gives an edgewise bounded shifted starting flow by restriction. The same
restriction is a prefix of the stored unsigned flow array, without a copy.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Restricting the actual first-solve output to original edges gives the
input capacity bounds required by residual optimization. -/
theorem feasibilityPhase_restrict_bounds (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) (C U : ℕ) (hC : 1≤C)
    (hd : ∀ v : Fin I.n,(I.d v).natAbs≤U)
    (hl : ∀ e,(I.edge e).lower.natAbs≤U) (hu : ∀ e,(I.edge e).upper.natAbs≤U) :
    let P := FlowReduction.buildFeasibilityInstance I hv
    let B := FlowReduction.scalingCapacityBudget I U
    let g := (Circulation.invokePruned
      (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C B) P).value
    ∀ e,0≤g (Fin.castAdd (I.n+I.n) e) ∧
      g (Fin.castAdd (I.n+I.n) e)≤((FlowReduction.shiftedGraph I hv).capacity e : ℤ) := by
  dsimp only
  let P := FlowReduction.buildFeasibilityInstance I hv
  let B := FlowReduction.scalingCapacityBudget I U
  have hPC : P.CostsBounded C := fun e => (buildFeasibility_costs_le_one I hv e).trans hC
  have hcap := FlowReduction.buildFeasibilityInstance_capacity_le I hv U hd hl hu
  have hB : 1≤B := by unfold B FlowReduction.scalingCapacityBudget; omega
  have h := prunedScalingModel_output_bounds solver entry T hproc P C B hPC hcap hB
  intro e
  have he := h (Fin.castAdd (I.n+I.n) e)
  have hcapacity : P.capacity (Fin.castAdd (I.n+I.n) e)=
      (FlowReduction.shiftedGraph I hv).capacity e := by
    simp only [P,Fin.addCases_left]
  rw [hcapacity] at he
  exact he

/-- Restriction to the first edge block reads the exact unsigned prefix
of the first circulation's stored flow, with no added machine work. -/
theorem unsignedFlow_castAdd_prefix {m n : ℕ} {mem : ℕ → ℕ} {a : ℕ}
    (g : Fin (m+n) → ℤ) (hat : ListAt mem a (List.ofFn (fun e => (g e).toNat))) :
    ListAt mem a (List.ofFn (fun e : Fin m => (g (Fin.castAdd n e)).toNat)) := by
  intro i hi
  have hi' : i<m := by simpa only [List.length_ofFn] using hi
  have h := hat i (by rw [List.length_ofFn]; omega)
  rw [List.getElem_ofFn] at h ⊢
  exact h

end MinCostFlow.Scaling.Machine
