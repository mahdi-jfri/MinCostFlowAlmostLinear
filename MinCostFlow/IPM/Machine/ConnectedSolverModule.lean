module

public import MinCostFlow.IPM.Machine.SolverModule
public import MinCostFlow.IPM.Machine.ConnectedGraph

/-!
# Procedures of the connected bounded solver

Place the connected graph builder at the startup graph entry and
place every later procedure after its complete module.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- Driver entries with a supplied quality selection statement. -/
def connectedSolverControl (b : ℕ) (e : SolverDispatch) : List Stmt :=
  let graph := b+14
  let alpha := graph+(connectedGraphModule graph).length
  let flow := alpha+(qualityPrecisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModule search e.cycleInit e.cycleOp).length
  [boundedIPMBody (b+1),
   solverPositiveRuntimeBody e.quality (b+2) (b+13) (b+3),
   solverPenaltyBody,
   solverAfterInitBody (b+4) (b+6) (b+7) (b+10),
   solverSearchSetupBody named coefficients (b+5),
   solverGuardTablesBody signed norm,
   workspaceBody,
   solverLimitsBody (b+11) (b+8) (b+9),
   targetTestLimitBody (b+12),
   targetSearchRoundsBody (b+11),
   solverSearchRecoverBody search recover,
   Num.IPM.bitLengthBody (b+11),
   iterationBudgetBody]

/-- Initialization, preparation, search and recovery modules. -/
def connectedSolverOwnModules (b : ℕ) (e : SolverDispatch) : List Stmt :=
  let graph := b+14
  let alpha := graph+(connectedGraphModule graph).length
  let flow := alpha+(qualityPrecisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModule search e.cycleInit e.cycleOp).length
  [solverQualityInitializeBody e.quality (b+2) graph alpha flow] ++ (connectedGraphModule graph ++ (qualityPrecisionAlphaModule alpha ++ (initialFlowModule flow 4 ++ (namedGraphModule named ++ (coefficientTablesModule coefficients 4 ++ (signedGuardConstantsModule signed ++ (normalizationModule norm ++ (solverSearchModule search e.cycleInit e.cycleOp ++ (solverRoundModule recover e.forestInit e.forestOp)))))))))

/-- A runtime solver whose initializer selects the format from quality. -/
def boundedConnectedIPMRuntimeModule (b : ℕ) (e : SolverDispatch) : List Stmt :=
  connectedSolverControl b e ++ connectedSolverOwnModules b e

/-- All the solver's own statements are deterministic. The two
supplied data structures can be linked as deterministic programs. -/
theorem boundedConnectedIPMRuntimeModule_noRand (b : ℕ) (e : SolverDispatch) :
    ∀ body∈boundedConnectedIPMRuntimeModule b e,body.NoRand := by
  intro body h
  simp only [boundedConnectedIPMRuntimeModule,connectedSolverOwnModules,List.mem_append,List.mem_singleton] at h
  rcases h with h | rfl | h | h | h | h | h | h | h | h | h
  · simp only [connectedSolverControl,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact boundedIPMBody_noRand _
    · exact solverPositiveRuntimeBody_noRand _ _ _ _
    · exact solverPenaltyBody_noRand
    · exact solverAfterInitBody_noRand _ _ _ _
    · exact solverSearchSetupBody_noRand _ _ _
    · exact solverGuardTablesBody_noRand _ _
    · exact workspace_noRand
    · exact solverLimitsBody_noRand _ _ _
    · exact targetTestLimit_noRand _
    · exact targetSearchRounds_noRand _
    · exact solverSearchRecoverBody_noRand _ _
    · exact Num.IPM.bitLengthModule_noRand _ _ List.mem_cons_self
    · exact iterationBudget_noRand
  · exact solverQualityInitializeBody_noRand _ _ _ _ _
  · exact connectedGraphModule_noRand _ _ h
  · exact qualityPrecisionAlphaModule_noRand _ _ h
  · exact initialFlowModule_noRand _ _ _ h
  · exact namedGraphModule_noRand _ _ h
  · exact coefficientTablesModule_noRand _ _ _ h
  · exact signedGuardConstantsModule_noRand _ _ h
  · exact normalizationModule_noRand _ _ h
  · exact solverSearchModule_noRand _ _ _ _ h
  · exact solverRoundModule_noRand _ _ _ _ h


/-- `V`-passing driver entries for the connected bounded solver. -/
def connectedSolverControlWithV (b : ℕ) (e : SolverDispatch) : List Stmt :=
  let graph := b+14
  let alpha := graph+(connectedGraphModule graph).length
  let flow := alpha+(qualityPrecisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModuleWithV search e.cycleInit e.cycleOp).length
  [boundedIPMBody (b+1),
   solverPositiveRuntimeBody e.quality (b+2) (b+13) (b+3),
   solverPenaltyBody,
   solverAfterInitBodyWithV (b+4) (b+6) (b+7) (b+10),
   solverSearchSetupBody named coefficients (b+5),
   solverGuardTablesBody signed norm,
   workspaceBody,
   solverLimitsBody (b+11) (b+8) (b+9),
   targetTestLimitBody (b+12),
   targetSearchRoundsBody (b+11),
   solverSearchRecoverBodyWithV search recover,
   Num.IPM.bitLengthBody (b+11),
   iterationBudgetBody]

/-- `V`-passing connected initialization, preparation, search and recovery modules. -/
def connectedSolverOwnModulesWithV (b : ℕ) (e : SolverDispatch) : List Stmt :=
  let graph := b+14
  let alpha := graph+(connectedGraphModule graph).length
  let flow := alpha+(qualityPrecisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModuleWithV search e.cycleInit e.cycleOp).length
  [solverQualityInitializeBody e.quality (b+2) graph alpha flow] ++ (connectedGraphModule graph ++ (qualityPrecisionAlphaModule alpha ++ (initialFlowModule flow 4 ++ (namedGraphModule named ++ (coefficientTablesModule coefficients 4 ++ (signedGuardConstantsModule signed ++ (normalizationModule norm ++ (solverSearchModuleWithV search e.cycleInit e.cycleOp ++ (solverRoundModule recover e.forestInit e.forestOp)))))))))

/-- `V`-passing runtime connected solver whose initializer selects the format from quality. -/
def boundedConnectedIPMRuntimeModuleWithV (b : ℕ) (e : SolverDispatch) : List Stmt :=
  connectedSolverControlWithV b e ++ connectedSolverOwnModulesWithV b e

theorem boundedConnectedIPMRuntimeModuleWithV_noRand (b : ℕ) (e : SolverDispatch) :
    ∀ body∈boundedConnectedIPMRuntimeModuleWithV b e,body.NoRand := by
  intro body h
  simp only [boundedConnectedIPMRuntimeModuleWithV,connectedSolverOwnModulesWithV,List.mem_append,List.mem_singleton] at h
  rcases h with h | rfl | h | h | h | h | h | h | h | h | h
  · simp only [connectedSolverControlWithV,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact boundedIPMBody_noRand _
    · exact solverPositiveRuntimeBody_noRand _ _ _ _
    · exact solverPenaltyBody_noRand
    · exact solverAfterInitBodyWithV_noRand _ _ _ _
    · exact solverSearchSetupBody_noRand _ _ _
    · exact solverGuardTablesBody_noRand _ _
    · exact workspace_noRand
    · exact solverLimitsBody_noRand _ _ _
    · exact targetTestLimit_noRand _
    · exact targetSearchRounds_noRand _
    · exact solverSearchRecoverBodyWithV_noRand _ _
    · exact Num.IPM.bitLengthModule_noRand _ _ List.mem_cons_self
    · exact iterationBudget_noRand
  · exact solverQualityInitializeBody_noRand _ _ _ _ _
  · exact connectedGraphModule_noRand _ _ h
  · exact qualityPrecisionAlphaModule_noRand _ _ h
  · exact initialFlowModule_noRand _ _ _ h
  · exact namedGraphModule_noRand _ _ h
  · exact coefficientTablesModule_noRand _ _ _ h
  · exact signedGuardConstantsModule_noRand _ _ h
  · exact normalizationModule_noRand _ _ h
  · exact solverSearchModuleWithV_noRand _ _ _ _ h
  · exact solverRoundModule_noRand _ _ _ _ h

end MinCostFlow.IPM.Machine
