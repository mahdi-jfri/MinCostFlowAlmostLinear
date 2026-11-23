module

public import MinCostFlow.Final.AssemblyDryRunSCParam
import Mathlib.Tactic

/-!
# The inner procedures given as parameters, without the parameter setup (`AssemblyDryRunSCParamOpen`)

`SolverInnerOpenNoParam` holds the inner procedures that are given as parameters, other than the
parameter setup.
`SolverInnerOpenNoParam.toSolverInnerOpen` installs `dryParamProcs` at offset `0` of
`SolverInnerOpen`. Determinism (`toSolverInnerOpen_isDeterministic`) and the placement hypothesis
of `dryParamSetup_discharges_hParam` (`dryParamProcs_hasAt`) then hold with no extra hypothesis.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Scaling.Machine
  MinRatio DynSpanner.Program

/-! ## Convenience wrapper closing `paramSetup` inside `SolverInnerOpen` -/

/-- The other five inner-level procedures, given as parameters, once `dryParamProcs` is installed after them at
offset `len`. Placing `dryParamProcs` at the tail avoids assuming `(dryParamProcs b).length` is
independent of `b`. -/
structure SolverInnerOpenNoParam where
  procs : SolverInnerEnv → List Stmt
  len : ℕ
  hlen : ∀ env, (procs env).length = len
  ordChainCoreOff : ℕ
  selectRouteOff : ℕ
  evalCycleOff : ℕ
  shiftTermChainOff : ℕ
  shiftDeepChainOff : ℕ

/-- Determinism of the five inner-level procedures given as parameters. -/
def SolverInnerOpenNoParam.IsDeterministic (rem : SolverInnerOpenNoParam) : Prop :=
  ∀ env, ∀ s ∈ rem.procs env, s.NoRand

/-- Install `rem.procs` at offset `0` of `SolverInnerOpen` and `dryParamProcs` immediately after
at offset `rem.len`. -/
def SolverInnerOpenNoParam.toSolverInnerOpen
    (rem : SolverInnerOpenNoParam) : SolverInnerOpen where
  procs env :=
    rem.procs env ++ dryParamProcs (env.innerBase + rem.len)
  paramSetupOff := rem.len
  ordChainCoreOff := rem.ordChainCoreOff
  selectRouteOff := rem.selectRouteOff
  evalCycleOff := rem.evalCycleOff
  shiftTermChainOff := rem.shiftTermChainOff
  shiftDeepChainOff := rem.shiftDeepChainOff

/-- Determinism of `rem.toSolverInnerOpen` from determinism of `rem` alone. -/
theorem SolverInnerOpenNoParam.toSolverInnerOpen_isDeterministic
    {rem : SolverInnerOpenNoParam} (hrem : rem.IsDeterministic) :
    rem.toSolverInnerOpen.IsDeterministic := by
  intro env s hs
  simp only [SolverInnerOpenNoParam.toSolverInnerOpen, List.mem_append] at hs
  rcases hs with h1 | h2
  · exact hrem _ s h1
  · exact dryParamProcs_noRand _ s h2

/-- Automatic placement of `dryParamProcs` at `dryParamSetupProc Psc.sc rem.toSolverInnerOpen`
inside `dryLinkedProgram`. -/
theorem SolverInnerOpenNoParam.dryParamProcs_hasAt
    (Psc : DrySparseCorePieces) (rem : SolverInnerOpenNoParam) :
    let openInner := rem.toSolverInnerOpen
    (dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode).HasAt
      (dryParamSetupProc Psc.sc openInner)
      (dryParamProcs (dryParamSetupProc Psc.sc openInner)) := by
  intro openInner
  have hInner := dryInner_hasAt (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed)
    (mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase)
      (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc openInner.toInnerCode).length)
    Psc.sc openInner.toInnerCode
    (dynLctForestBodies 4 (mrdsCycleBase +
      (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc openInner.toInnerCode).length))
  have hTail := Num.hasAt_append_right hInner
  rw [dryInitConcreteProcs_length] at hTail
  have hRight := Num.hasAt_append_right hTail
  rw [rem.hlen] at hRight
  have hBase : (dryTailLay Psc.sc openInner.toInnerCode).innerBase + dryInitConcreteLen + rem.len =
      dryParamSetupProc Psc.sc openInner := rfl
  have hEnv : (solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
      Psc.sc solverTailBase).innerBase =
      (dryTailLay Psc.sc openInner.toInnerCode).innerBase := rfl
  rw [hEnv, hBase] at hRight
  exact hRight

end MinCostFlow.Final.DryRun

end
