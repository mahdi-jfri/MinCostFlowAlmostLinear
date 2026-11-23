module

public import MinCostFlow.ExpanderDecomp.OuterProgMain
public import MinCostFlow.ExpanderDecomp.ProgStepB

/-!
# `ExpanderDecompositionUsed` from a Multi-Pair Router Alone (`UsedFromRouter`)

Plugs the concrete Step B module `stepBModule` (`ProgStepB.lean`) and the concrete outer
decomposition module `outerDecompModule` (`OuterProgMain.lean`) together with `Core`
(`CoreProg.lean`), `CoreOuterParams.lean`, and `CoreOuter.lean` via
`OuterProgMain.expanderDecompositionUsed_of_router_and_stepB`.

Main results:
* `assembledDecompProgOfRouter`: the complete Word-RAM program parameterized only by a
  `MultiPairRouterModule`.
* `assembledDecompProgOfRouter_noRand`: determinism (`NoRand`) whenever the router module is
  deterministic.
* `expanderDecompositionUsed_of_router`: proves `ExpanderDecompositionUsed` from a
  `MultiPairRouterModule` alone.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM

/-- Complete assembled Word-RAM program for `ExpanderDecompositionUsed`, parameterized solely by
a multi-pair static router module `hRoute`. -/
noncomputable def assembledDecompProgOfRouter (hRoute : MultiPairRouterModule) : Program :=
  let hStepB := stepBModule hRoute.C_rt hRoute.C_sp
  assembledDecompProg hRoute hStepB
    (outerDecompModule hStepB.K_B hRoute.C_rt hStepB.S_B hRoute.C_sp)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM

/-- Every procedure in `assembledDecompProgOfRouter hRoute` is deterministic (`NoRand`) whenever
every procedure in `hRoute` is deterministic. -/
theorem assembledDecompProgOfRouter_noRand (hRoute : MultiPairRouterModule)
    (hRouteNR : ∀ b s, s ∈ hRoute.procs b → s.NoRand) :
    ∀ s ∈ (assembledDecompProgOfRouter hRoute).procs, s.NoRand :=
  assembledDecompProg_noRand hRoute
    (stepBModule hRoute.C_rt hRoute.C_sp)
    (outerDecompModule (stepBModule hRoute.C_rt hRoute.C_sp).K_B hRoute.C_rt
      (stepBModule hRoute.C_rt hRoute.C_sp).S_B hRoute.C_sp)
    hRouteNR
    (stepBModule_noRand hRoute.C_rt hRoute.C_sp)
    (outerDecompModule_noRand (stepBModule hRoute.C_rt hRoute.C_sp).K_B hRoute.C_rt
      (stepBModule hRoute.C_rt hRoute.C_sp).S_B hRoute.C_sp)

/-- `ExpanderDecompositionUsed` from a multi-pair static router module alone, instantiating Step B
with `ProgStepB.stepBModule` and the outer decomposition with `OuterProgMain.outerDecompModule`. -/
theorem expanderDecompositionUsed_of_router (hRoute : MultiPairRouterModule) :
    ExpanderDecompositionUsed :=
  expanderDecompositionUsed_of_router_and_stepB hRoute (stepBModule hRoute.C_rt hRoute.C_sp)

end MinCostFlow.ExpanderDecomp
