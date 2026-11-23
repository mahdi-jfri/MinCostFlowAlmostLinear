module

public import MinCostFlow.IPM.Machine.SolverDriver
public import MinCostFlow.IPM.Machine.SolverSearchLinkWithV
import MinCostFlow.Num.ModulePlacement
import Mathlib.Tactic

/-!
# Linking the bounded-circulation solver

The driver, graph and precision initialization, numeric kernels,
search and rounder occupy one contiguous module. The only calls
outside this module are to the supplied min-ratio and forest entries.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Driver entries with a supplied quality selection statement. -/
def solverControlWith (b : ℕ) (choose : Stmt) (e : SolverDispatch) : List Stmt :=
  let graph := b+14
  let alpha := graph+(initialGraphModule graph).length
  let flow := alpha+(precisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModule search e.cycleInit e.cycleOp).length
  [boundedIPMBody (b+1),
   solverPositiveBodyWith choose (b+2) (b+13) (b+3),
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

/-- Driver entries with fixed quality. -/
def solverControl (b k : ℕ) (e : SolverDispatch) : List Stmt :=
  solverControlWith b (.assign 24 (.const k)) e

/-- Driver entries that call the quality procedure at runtime. -/
def solverRuntimeControl (b : ℕ) (e : SolverDispatch) : List Stmt :=
  solverControlWith b (.call 24 e.quality [.reg 8]) e

/-- Initialization, preparation, search and recovery modules. -/
def solverOwnModules (b : ℕ) (e : SolverDispatch) : List Stmt :=
  let graph := b+14
  let alpha := graph+(initialGraphModule graph).length
  let flow := alpha+(precisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModule search e.cycleInit e.cycleOp).length
  [solverInitializeBody (b+2) graph alpha flow] ++ (initialGraphModule graph ++ (precisionAlphaModule alpha ++ (initialFlowModule flow 4 ++ (namedGraphModule named ++ (coefficientTablesModule coefficients 4 ++ (signedGuardConstantsModule signed ++ (normalizationModule norm ++ (solverSearchModule search e.cycleInit e.cycleOp ++ (solverRoundModule recover e.forestInit e.forestOp)))))))))

/-- The bounded solver starts at address `b`. -/
def boundedIPMModule (b k : ℕ) (e : SolverDispatch) : List Stmt :=
  solverControl b k e ++ solverOwnModules b e

/-- The runtime solver contains only the address of the quality procedure. -/
def boundedIPMRuntimeModule (b : ℕ) (e : SolverDispatch) : List Stmt :=
  solverRuntimeControl b e ++ solverOwnModules b e

private theorem solverControl_noRand (b k : ℕ) (e : SolverDispatch) :
    ∀ body∈solverControl b k e,body.NoRand := by
  intro body h
  simp only [solverControl,solverControlWith,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact boundedIPMBody_noRand _
  · exact solverPositiveBody_noRand _ _ _ _
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

/-- All the solver's own statements are deterministic. The two
supplied data structures can be linked as deterministic programs. -/
theorem boundedIPMModule_noRand (b k : ℕ) (e : SolverDispatch) :
    ∀ body∈boundedIPMModule b k e,body.NoRand := by
  intro body h
  simp only [boundedIPMModule,solverOwnModules,List.mem_append,List.mem_singleton] at h
  rcases h with h | rfl | h | h | h | h | h | h | h | h | h
  · exact solverControl_noRand b k e body h
  · exact solverInitializeBody_noRand _ _ _ _
  · exact initialGraphModule_noRand _ _ h
  · exact precisionAlphaModule_noRand _ _ h
  · exact initialFlowModule_noRand _ _ _ h
  · exact namedGraphModule_noRand _ _ h
  · exact coefficientTablesModule_noRand _ _ _ h
  · exact signedGuardConstantsModule_noRand _ _ h
  · exact normalizationModule_noRand _ _ h
  · exact solverSearchModule_noRand _ _ _ _ h
  · exact solverRoundModule_noRand _ _ _ _ h


/-- The runtime solver's own code has no random instruction. -/
theorem boundedIPMRuntimeModule_noRand (b : ℕ) (e : SolverDispatch) :
    ∀ body ∈ boundedIPMRuntimeModule b e, body.NoRand := by
  intro body h
  simp only [boundedIPMRuntimeModule, List.mem_append] at h
  rcases h with h | h
  · simp only [solverRuntimeControl, solverControlWith, List.mem_cons, List.not_mem_nil, or_false] at h
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
  · exact boundedIPMModule_noRand b 0 e body (List.mem_append_right _ h)

/-- Initialization, preparation, search and recovery modules. -/
def solverQualityOwnModules (b : ℕ) (e : SolverDispatch) : List Stmt :=
  let graph := b+14
  let alpha := graph+(initialGraphModule graph).length
  let flow := alpha+(qualityPrecisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModule search e.cycleInit e.cycleOp).length
  [solverQualityInitializeBody e.quality (b+2) graph alpha flow] ++ (initialGraphModule graph ++ (qualityPrecisionAlphaModule alpha ++ (initialFlowModule flow 4 ++ (namedGraphModule named ++ (coefficientTablesModule coefficients 4 ++ (signedGuardConstantsModule signed ++ (normalizationModule norm ++ (solverSearchModule search e.cycleInit e.cycleOp ++ (solverRoundModule recover e.forestInit e.forestOp)))))))))

/-- A runtime solver whose initializer selects the format from quality. -/
def boundedIPMQualityRuntimeModule (b : ℕ) (e : SolverDispatch) : List Stmt :=
  solverRuntimeControl b e ++ solverQualityOwnModules b e

/-- All the solver's own statements are deterministic. The two
supplied data structures can be linked as deterministic programs. -/
theorem boundedIPMQualityRuntimeModule_noRand (b : ℕ) (e : SolverDispatch) :
    ∀ body∈boundedIPMQualityRuntimeModule b e,body.NoRand := by
  intro body h
  simp only [boundedIPMQualityRuntimeModule,solverQualityOwnModules,List.mem_append,List.mem_singleton] at h
  rcases h with h | rfl | h | h | h | h | h | h | h | h | h
  · exact boundedIPMRuntimeModule_noRand b e body (List.mem_append_left _ h)
  · exact solverQualityInitializeBody_noRand _ _ _ _ _
  · exact initialGraphModule_noRand _ _ h
  · exact qualityPrecisionAlphaModule_noRand _ _ h
  · exact initialFlowModule_noRand _ _ _ h
  · exact namedGraphModule_noRand _ _ h
  · exact coefficientTablesModule_noRand _ _ _ h
  · exact signedGuardConstantsModule_noRand _ _ h
  · exact normalizationModule_noRand _ _ h
  · exact solverSearchModule_noRand _ _ _ _ h
  · exact solverRoundModule_noRand _ _ _ _ h


/-- `V`-passing driver entries with a supplied quality selection statement. -/
def solverControlWithV (b : ℕ) (choose : Stmt) (e : SolverDispatch) : List Stmt :=
  let graph := b+14
  let alpha := graph+(initialGraphModule graph).length
  let flow := alpha+(precisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModuleWithV search e.cycleInit e.cycleOp).length
  [boundedIPMBody (b+1),
   solverPositiveBodyWith choose (b+2) (b+13) (b+3),
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

/-- `V`-passing driver entries with fixed quality. -/
def solverControlWithV_fixed (b k : ℕ) (e : SolverDispatch) : List Stmt :=
  solverControlWithV b (.assign 24 (.const k)) e

/-- `V`-passing driver entries that call the quality procedure at runtime. -/
def solverRuntimeControlWithV (b : ℕ) (e : SolverDispatch) : List Stmt :=
  solverControlWithV b (.call 24 e.quality [.reg 8]) e

/-- `V`-passing initialization, preparation, search and recovery modules. -/
def solverOwnModulesWithV (b : ℕ) (e : SolverDispatch) : List Stmt :=
  let graph := b+14
  let alpha := graph+(initialGraphModule graph).length
  let flow := alpha+(precisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModuleWithV search e.cycleInit e.cycleOp).length
  [solverInitializeBody (b+2) graph alpha flow] ++ (initialGraphModule graph ++ (precisionAlphaModule alpha ++ (initialFlowModule flow 4 ++ (namedGraphModule named ++ (coefficientTablesModule coefficients 4 ++ (signedGuardConstantsModule signed ++ (normalizationModule norm ++ (solverSearchModuleWithV search e.cycleInit e.cycleOp ++ (solverRoundModule recover e.forestInit e.forestOp)))))))))

/-- `V`-passing bounded solver starting at address `b`. -/
def boundedIPMModuleWithV (b k : ℕ) (e : SolverDispatch) : List Stmt :=
  solverControlWithV_fixed b k e ++ solverOwnModulesWithV b e

/-- `V`-passing runtime solver containing only the address of the quality procedure. -/
def boundedIPMRuntimeModuleWithV (b : ℕ) (e : SolverDispatch) : List Stmt :=
  solverRuntimeControlWithV b e ++ solverOwnModulesWithV b e

private theorem solverControlWithV_noRand (b k : ℕ) (e : SolverDispatch) :
    ∀ body∈solverControlWithV_fixed b k e,body.NoRand := by
  intro body h
  simp only [solverControlWithV_fixed,solverControlWithV,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact boundedIPMBody_noRand _
  · exact solverPositiveBody_noRand _ _ _ _
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

theorem boundedIPMModuleWithV_noRand (b k : ℕ) (e : SolverDispatch) :
    ∀ body∈boundedIPMModuleWithV b k e,body.NoRand := by
  intro body h
  simp only [boundedIPMModuleWithV,solverOwnModulesWithV,List.mem_append,List.mem_singleton] at h
  rcases h with h | rfl | h | h | h | h | h | h | h | h | h
  · exact solverControlWithV_noRand b k e body h
  · exact solverInitializeBody_noRand _ _ _ _
  · exact initialGraphModule_noRand _ _ h
  · exact precisionAlphaModule_noRand _ _ h
  · exact initialFlowModule_noRand _ _ _ h
  · exact namedGraphModule_noRand _ _ h
  · exact coefficientTablesModule_noRand _ _ _ h
  · exact signedGuardConstantsModule_noRand _ _ h
  · exact normalizationModule_noRand _ _ h
  · exact solverSearchModuleWithV_noRand _ _ _ _ h
  · exact solverRoundModule_noRand _ _ _ _ h

theorem boundedIPMRuntimeModuleWithV_noRand (b : ℕ) (e : SolverDispatch) :
    ∀ body ∈ boundedIPMRuntimeModuleWithV b e, body.NoRand := by
  intro body h
  simp only [boundedIPMRuntimeModuleWithV, List.mem_append] at h
  rcases h with h | h
  · simp only [solverRuntimeControlWithV, solverControlWithV, List.mem_cons, List.not_mem_nil, or_false] at h
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
  · exact boundedIPMModuleWithV_noRand b 0 e body (List.mem_append_right _ h)

/-- `V`-passing quality initialization, preparation, search and recovery modules. -/
def solverQualityOwnModulesWithV (b : ℕ) (e : SolverDispatch) : List Stmt :=
  let graph := b+14
  let alpha := graph+(initialGraphModule graph).length
  let flow := alpha+(qualityPrecisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModuleWithV search e.cycleInit e.cycleOp).length
  [solverQualityInitializeBody e.quality (b+2) graph alpha flow] ++ (initialGraphModule graph ++ (qualityPrecisionAlphaModule alpha ++ (initialFlowModule flow 4 ++ (namedGraphModule named ++ (coefficientTablesModule coefficients 4 ++ (signedGuardConstantsModule signed ++ (normalizationModule norm ++ (solverSearchModuleWithV search e.cycleInit e.cycleOp ++ (solverRoundModule recover e.forestInit e.forestOp)))))))))

/-- `V`-passing runtime solver whose initializer selects the format from quality. -/
def boundedIPMQualityRuntimeModuleWithV (b : ℕ) (e : SolverDispatch) : List Stmt :=
  solverRuntimeControlWithV b e ++ solverQualityOwnModulesWithV b e

theorem boundedIPMQualityRuntimeModuleWithV_noRand (b : ℕ) (e : SolverDispatch) :
    ∀ body∈boundedIPMQualityRuntimeModuleWithV b e,body.NoRand := by
  intro body h
  simp only [boundedIPMQualityRuntimeModuleWithV,solverQualityOwnModulesWithV,List.mem_append,List.mem_singleton] at h
  rcases h with h | rfl | h | h | h | h | h | h | h | h | h
  · exact boundedIPMRuntimeModuleWithV_noRand b e body (List.mem_append_left _ h)
  · exact solverQualityInitializeBody_noRand _ _ _ _ _
  · exact initialGraphModule_noRand _ _ h
  · exact qualityPrecisionAlphaModule_noRand _ _ h
  · exact initialFlowModule_noRand _ _ _ h
  · exact namedGraphModule_noRand _ _ h
  · exact coefficientTablesModule_noRand _ _ _ h
  · exact signedGuardConstantsModule_noRand _ _ h
  · exact normalizationModule_noRand _ _ h
  · exact solverSearchModuleWithV_noRand _ _ _ _ h
  · exact solverRoundModule_noRand _ _ _ _ h

end MinCostFlow.IPM.Machine
