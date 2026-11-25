module

public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Scaling.VertexCompression
public import MinCostFlow.Scaling.MeasuredReduction
public import MinCostFlow.Scaling.DemandBoundCheck

/-!
# Definitions for the outer narrow-word minimum-cost flow model

This file defines:
- `narrowCircModel`: compresses isolated vertices (`Circulation.compress`),
  handles the `m = 0` case, and invokes Stage 1 (`narrowCostSolve` and
  `narrowCostSolverCalls`);
- `narrowOuterModel`: plugs `narrowCircModel` into the checked, pruned
  two-circulation reduction `FlowReduction.checkedMeasured`;
- `narrowArbitraryDemandModel`: wraps `narrowOuterModel` with the initial
  demand-magnitude rejection `FlowReduction.demandBoundCheck` so that call
  counts depend only on `U` (capacities) and `C` (costs), even for infeasible
  instances with huge demands.
-/

@[expose] public section

namespace MinCostFlow.Narrow

open MinCostFlow.Scaling

/-- Circulation solver using vertex compression and Stage 1 narrow-word cost
scaling (`narrowCostSolve`), recording all positive-capacity bounded-solver
calls made across all rounds and phases. -/
def narrowCircModel (solve : (K : Circulation) → Fin K.m → ℤ)
    (J : Circulation) : CallResult (Fin J.m → ℤ) :=
  if J.m = 0 then
    ⟨fun _ => 0, [], 0⟩
  else
    let C := J.compress
    ⟨narrowCostSolve solve C, narrowCostSolverCalls solve C, 0⟩

/-- General minimum-cost flow model on a valid `Instance`, plugging
`narrowCircModel` into the checked, pruned two-call reduction
`FlowReduction.checkedMeasured`. -/
def narrowOuterModel (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Instance) (hv : I.IsValid) : CallResult (Option (Fin I.m → ℤ)) :=
  FlowReduction.checkedMeasured (narrowCircModel solve) I hv

/-- Arbitrary-demand wrapper around `narrowOuterModel`: rejects instances whose
demands exceed `I.m * U` before invoking the reduction, matching
`FlowReduction.arbitraryDemandScalingModel`. -/
def narrowArbitraryDemandModel (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Instance) (hv : I.IsValid) (U : ℕ) : CallResult (Option (Fin I.m → ℤ)) :=
  if FlowReduction.demandBoundCheck I U then
    narrowOuterModel solve I hv
  else
    ⟨none, [], 0⟩

/-- The two-factor logarithmic product bounding the solver call count of the
narrow-word outer model: `(clog₂(U+1) + clog₂(m+1) + 1) * (clog₂(C+2) + clog₂(m+1) + 1)`. -/
def narrowOuterLogFactor (m C U : ℕ) : ℕ :=
  (Nat.clog 2 (U + 1) + Nat.clog 2 (m + 1) + 1) *
    (Nat.clog 2 (C + 2) + Nat.clog 2 (m + 1) + 1)

end MinCostFlow.Narrow
