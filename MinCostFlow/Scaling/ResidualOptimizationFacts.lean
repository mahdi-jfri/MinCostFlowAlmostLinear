module

public import MinCostFlow.Scaling.ResidualOptimizationContract
import MinCostFlow.Scaling.PrunedScalingOutputBounds
import MinCostFlow.Scaling.CapacityNumericFacts
import Mathlib.Tactic.Ring

/-!
# Coordinate bounds for residual optimization

The shifted capacities are at most twice the original absolute capacity
bound. A bounded starting flow gives the same bound on both residual
halves. Exact optimality of the actual pruned residual solve then bounds
its correction and ensures that augmentation remains nonnegative and
within the shifted capacities. These facts pay for every unsigned sum
and the final signed lower-capacity addition.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The actual residual correction and augmented shifted flow fit the
original twice-capacity budget, using only the bounded solver contract. -/
theorem residualOptimization_bounds (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (C U : ℕ)
    (hf : ∀ e,0≤f e ∧ f e≤((FlowReduction.shiftedGraph I hv).capacity e : ℤ))
    (hC : ∀ e,(I.edge e).cost.natAbs≤C)
    (hl : ∀ e,(I.edge e).lower.natAbs≤U) (hu : ∀ e,(I.edge e).upper.natAbs≤U) :
    let J := FlowReduction.shiftedGraph I hv
    let R := J.residual f
    let B := FlowReduction.scalingCapacityBudget I U
    let delta := (Circulation.invokePruned
      (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C B) R).value
    (∀ e,R.capacity e≤2*U) ∧ (∀ e,0≤delta e ∧ (delta e).toNat≤2*U) ∧
      ∀ e,0≤f e+delta (Fin.castAdd I.m e)-delta (Fin.natAdd I.m e) ∧
        f e+delta (Fin.castAdd I.m e)-delta (Fin.natAdd I.m e)≤(2*U : ℕ) := by
  dsimp only
  let J := FlowReduction.shiftedGraph I hv
  let R := J.residual f
  let B := FlowReduction.scalingCapacityBudget I U
  let delta := (Circulation.invokePruned
    (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C B) R).value
  have hJcap := FlowReduction.shiftedGraph_capacity_le I hv U hl hu
  have hRcap : ∀ e,R.capacity e≤2*U := J.residual_capacities_le f
    (integral_capacity_bounds_cast J f hf) (2*U) hJcap
  have h2B : 2*U≤B := by
    have hh := Nat.mul_le_mul_right U (show 2≤2*(I.m+1) by omega)
    unfold B FlowReduction.scalingCapacityBudget
    omega
  have hRC : R.CostsBounded C := J.residual_costsBounded f C hC
  have hRB : ∀ e,R.capacity e≤B := fun e => (hRcap e).trans h2B
  have hB : 1≤B := by unfold B FlowReduction.scalingCapacityBudget; omega
  have hopt := prunedScalingModel_optimal solver entry T hproc R C B hRC hRB hB
  have hd := feasible_unsigned_bounds R delta (2*U) hopt.1 hRcap
  have ha := residualAugment_integral_bounds J f delta hf hopt.1
  refine ⟨hRcap,hd,?_⟩
  intro e
  exact ⟨(ha e).1,(ha e).2.trans (by exact_mod_cast hJcap e)⟩

/-- Original edge records are exactly the edge projection of a paired
restoration list in original edge order. -/
theorem lowerRestore_entries_edges (I : Instance) (s : Fin I.m → ℕ) :
    (List.ofFn (fun e => (I.edge e,s e))).map Prod.fst=I.edges := by
  rw [List.map_ofFn]
  exact List.ofFn_get I.edges

/-- Restoring a nonnegative augmented coordinate gives exactly the
integer expression in the counted reduction, including its signs. -/
theorem lowerRestore_entries_value (I : Instance) (f : Fin I.m → ℤ)
    (delta : Fin (I.m+I.m) → ℤ)
    (ha : ∀ e,0≤f e+delta (Fin.castAdd I.m e)-delta (Fin.natAdd I.m e)) :
    ((List.ofFn (fun e => (I.edge e,
      (f e+delta (Fin.castAdd I.m e)-delta (Fin.natAdd I.m e)).toNat))).map
        (fun x => x.1.lower+(x.2 : ℤ))).flatMap encodeInt=
      (List.ofFn (fun e => (I.edge e).lower+f e+delta (Fin.castAdd I.m e)-delta (Fin.natAdd I.m e))).flatMap encodeInt := by
  rw [List.map_ofFn]
  congr 2
  funext e
  dsimp only [Function.comp_def]
  rw [Int.toNat_of_nonneg (ha e)]
  ring

end MinCostFlow.Scaling.Machine
