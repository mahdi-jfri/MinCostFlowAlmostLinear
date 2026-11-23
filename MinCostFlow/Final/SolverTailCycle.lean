module

public import MinCostFlow.Final.SolverTail
public import MinCostFlow.Final.ForestConcretePrograms

/-!
# Placing `solverOpsProcs` and `solverTail` in the linked solver program

Assembles the full cycle procedure list `solverCycle`: the 183 operation procedures
`solverOpsProcs` placed at `mrdsCycleBase`, immediately followed by `solverTail` at
`solverTailBase := mrdsCycleBase + 183`.

In `linkedCappedSolverProgramWithV threshold A dispatch (solverCycle …) forest`, the IPM runtime
module sits at `[0, mrdsCycleBase)` (`boundedConnectedIPMRuntimeModuleWithV_length`),
`solverOpsProcs` sits at `[mrdsCycleBase, solverTailBase)` (`solverCycle_ops_hasAt`), and
`solverTail` sits at `solverTailBase` (`solverCycle_tail_hasAt`). Consequently every `HasAt`,
`MeetsContract`, and `DSRep.Implements` fact proved in `Final/SolverTail.lean` transfers directly
to the linked solver program.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final

open WordRAM MinRatio SparseCore SparseCore.Program DynSpanner.Program LastLevelProgram Chain
  IPM.Machine Scaling.Machine

/-- Base index of `solverTail` inside the linked solver program: immediately after
`boundedConnectedIPMRuntimeModuleWithV` (`mrdsCycleBase`) and `solverOpsProcs` (length `183`). -/
def solverTailBase : ℕ := mrdsCycleBase + 183

/-- The four fixed entry indices of `solverTail` inside `linkedCappedSolverProgramWithV`:
`cycleInit`, `chainRefresh`, `findCycle`, and `shiftLevel`. They do not depend on the lengths of
the last-level, sparse-core, or inner-level blocks. -/
def solverCycleInit : ℕ := solverTailBase
def solverCycleChainRefresh : ℕ := solverTailBase + 3
def solverCycleFindCycle : ℕ := solverTailBase + 6
def solverCycleShiftLevel : ℕ := solverTailBase + 7

/-- Complete cycle module `solverOpsProcs ++ solverTail` for the linked solver program. -/
def solverCycle (threshold A : ℕ) (lastGuest : Program) (lastD lastC : ℕ)
    (sc : SparseCoreCode) (inner : SolverInnerCode) : List Stmt :=
  solverOpsProcs mrdsCycleBase solverCycleChainRefresh solverCycleFindCycle solverCycleShiftLevel ++
    solverTail mrdsCycleBase threshold A lastGuest lastD lastC sc inner solverTailBase

end MinCostFlow.Final

end

public section

namespace MinCostFlow.Final

open WordRAM MinRatio SparseCore SparseCore.Program DynSpanner.Program LastLevelProgram Chain
  IPM.Machine Scaling.Machine

/-- Determinism of `solverCycle`: follows from `solverOpsProcs_noRand` and `solverTail_noRand`. -/
theorem solverCycle_noRand (threshold A : ℕ) (lastGuest : Program) (lastD lastC : ℕ)
    {sc : SparseCoreCode} {inner : SolverInnerCode}
    (hsc : sc.prog.IsDeterministic) (hinner : inner.IsDeterministic) :
    ∀ s ∈ solverCycle threshold A lastGuest lastD lastC sc inner, s.NoRand := by
  intro s hs
  rcases List.mem_append.mp hs with h | h
  · exact solverOpsProcs_noRand _ _ _ _ s h
  · exact solverTail_noRand mrdsCycleBase threshold A lastGuest lastD lastC solverTailBase
      hsc hinner s h

/-- The 183 solver operation procedures sit at `mrdsCycleBase` in `linkedCappedSolverProgramWithV`. -/
theorem solverCycle_ops_hasAt (threshold A : ℕ) (dispatch : SolverDispatch)
    (lastGuest : Program) (lastD lastC : ℕ)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (forest : List Stmt) :
    (linkedCappedSolverProgramWithV threshold A dispatch
        (solverCycle threshold A lastGuest lastD lastC sc inner) forest).HasAt mrdsCycleBase
      (solverOpsProcs mrdsCycleBase solverCycleChainRefresh solverCycleFindCycle
        solverCycleShiftLevel) := by
  intro i hi
  have hlen := boundedConnectedIPMRuntimeModuleWithV_length dispatch
  simp only [linkedCappedSolverProgramWithV, solverCycle, List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  simp only [hlen, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hi]
  exact List.getElem?_eq_getElem hi

/-- The solver code tail sits at `solverTailBase` (`mrdsCycleBase + 183`) in
`linkedCappedSolverProgramWithV`. -/
theorem solverCycle_tail_hasAt (threshold A : ℕ) (dispatch : SolverDispatch)
    (lastGuest : Program) (lastD lastC : ℕ)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (forest : List Stmt) :
    (linkedCappedSolverProgramWithV threshold A dispatch
        (solverCycle threshold A lastGuest lastD lastC sc inner) forest).HasAt solverTailBase
      (solverTail mrdsCycleBase threshold A lastGuest lastD lastC sc inner solverTailBase) := by
  intro i hi
  have hlen1 := boundedConnectedIPMRuntimeModuleWithV_length dispatch
  have hlen2 := solverOpsProcs_length mrdsCycleBase solverCycleChainRefresh solverCycleFindCycle
    solverCycleShiftLevel
  simp only [linkedCappedSolverProgramWithV, solverCycle, List.append_assoc]
  rw [List.getElem?_append_right (by dsimp only [solverTailBase]; omega)]
  rw [show solverTailBase + i - (boundedConnectedIPMRuntimeModuleWithV 0 dispatch).length =
      183 + i by dsimp only [solverTailBase]; omega]
  rw [List.getElem?_append_right (by omega)]
  rw [show 183 + i -
      (solverOpsProcs mrdsCycleBase solverCycleChainRefresh solverCycleFindCycle
        solverCycleShiftLevel).length = i by omega]
  rw [List.getElem?_append_left hi]
  exact List.getElem?_eq_getElem hi

/-- The real last-level bodies sit at `lay.lastBase` in `linkedCappedSolverProgramWithV`. -/
theorem solverCycle_lastLevel_hasAt (threshold A : ℕ) (dispatch : SolverDispatch)
    (lastGuest : Program) (lastD lastC : ℕ)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (forest : List Stmt) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner solverTailBase
    (linkedCappedSolverProgramWithV threshold A dispatch
        (solverCycle threshold A lastGuest lastD lastC sc inner) forest).HasAt lay.lastBase
      (packedLastLevelBodies lastGuest lastD lastC lay.lastBase) :=
  solverTail_lastLevel_hasAt
    (solverCycle_tail_hasAt threshold A dispatch lastGuest lastD lastC sc inner forest)

/-- The shifted sparse-core program sits at `lay.scBase` in `linkedCappedSolverProgramWithV`. -/
theorem solverCycle_sparseCore_hasAt (threshold A : ℕ) (dispatch : SolverDispatch)
    (lastGuest : Program) (lastD lastC : ℕ)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (forest : List Stmt) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner solverTailBase
    (linkedCappedSolverProgramWithV threshold A dispatch
        (solverCycle threshold A lastGuest lastD lastC sc inner) forest).HasAt lay.scBase
      (shiftProgramProcs lay.scBase sc.prog) :=
  solverTail_sparseCore_hasAt
    (solverCycle_tail_hasAt threshold A dispatch lastGuest lastD lastC sc inner forest)

/-- `SparseCoreOrdProgramUniform` transfers into `linkedCappedSolverProgramWithV` at
`(lay.scInit, lay.scOp)`. -/
theorem solverCycle_sparseCore_uniform {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit}
    {impl : SparsifyImpl} (threshold A : ℕ) (dispatch : SolverDispatch)
    (lastGuest : Program) (lastD lastC : ℕ)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (forest : List Stmt)
    (hU : SparseCoreOrdProgramUniform C_lsst lsfInit impl sc.prog sc.init sc.op) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner solverTailBase
    SparseCoreOrdProgramUniform C_lsst lsfInit impl
      (linkedCappedSolverProgramWithV threshold A dispatch
        (solverCycle threshold A lastGuest lastD lastC sc inner) forest)
      lay.scInit lay.scOp :=
  solverTail_sparseCore_uniform
    (solverCycle_tail_hasAt threshold A dispatch lastGuest lastD lastC sc inner forest) hU

/-- The inner-level bodies sit at `lay.innerBase` in `linkedCappedSolverProgramWithV`. -/
theorem solverCycle_inner_hasAt (threshold A : ℕ) (dispatch : SolverDispatch)
    (lastGuest : Program) (lastD lastC : ℕ)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (forest : List Stmt) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner solverTailBase
    let env := solverTailInnerEnv mrdsCycleBase lastGuest lastD lastC sc solverTailBase
    (linkedCappedSolverProgramWithV threshold A dispatch
        (solverCycle threshold A lastGuest lastD lastC sc inner) forest).HasAt lay.innerBase
      (inner.procs env) :=
  solverTail_inner_hasAt
    (solverCycle_tail_hasAt threshold A dispatch lastGuest lastD lastC sc inner forest)

end MinCostFlow.Final

end
