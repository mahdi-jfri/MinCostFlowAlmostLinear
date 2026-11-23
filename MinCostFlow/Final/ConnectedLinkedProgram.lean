module

public import MinCostFlow.Final.LinkedProgram
public import MinCostFlow.Final.ConnectedPrograms
import Mathlib.Tactic

/-!
# Outer scaling with the connected solver

The scaling wrapper calls the connected bounded circulation solver.
A monotone time envelope and polynomial scratch cover every call.
-/

public section
namespace MinCostFlow.Final
open IPM.Machine WordRAM Scaling Scaling.Machine

/-- Monotone envelope of the IPM solver's dimension-dependent bound. -/
@[expose] def linkedConnectedSolverTime (r : SolverRuntimeResources) (n m : ℕ) : ℕ :=
  ((Finset.range (n+1)) ×ˢ (Finset.range (m+1))).sup
    (fun nm => connectedSolverRuntimeTime r nm.1 nm.2)

theorem connectedSolverRuntimeTime_le_linkedConnectedSolverTime (r : SolverRuntimeResources) (n m : ℕ) :
    connectedSolverRuntimeTime r n m ≤ linkedConnectedSolverTime r n m := by
  unfold linkedConnectedSolverTime
  apply Finset.le_sup (b := (n,m)) (f := fun nm => connectedSolverRuntimeTime r nm.1 nm.2)
  simp

theorem linkedConnectedSolverTime_mono (r : SolverRuntimeResources) : SolverTimeMonotone (linkedConnectedSolverTime r) := by
  intro n n' m m' hn hm
  apply Finset.sup_mono
  exact Finset.product_subset_product (Finset.range_mono (by omega)) (Finset.range_mono (by omega))

/-- The linked solver followed by the outer scaling procedures. -/
noncomputable def ConnectedDataStructurePrograms.program (P : ConnectedDataStructurePrograms) : Program :=
  scratchOuterScalingProgram P.solver 0 1 P.scratchDegree

/-- Linking the two supplied data structures and applying outer scaling
preserves determinism. -/
theorem ConnectedDataStructurePrograms.program_deterministic (P : ConnectedDataStructurePrograms) :
    P.program.IsDeterministic :=
  scratchOuterScalingProgram_deterministic _ _ _ _ P.solver_deterministic

/-- The constant in the original-input solver time bound. -/
noncomputable def ConnectedDataStructurePrograms.timeConstant (P : ConnectedDataStructurePrograms) : ℕ :=
  scratchWholeScalingConstant P.solver 1 P.scratchDegree

/-- The linked program runs on the original input encoding, returns the
correct answer, and obeys the counted scaling bound. -/
theorem ConnectedDataStructurePrograms.program_runsTo (P : ConnectedDataStructurePrograms)
    (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost,
      RunsTo (wordSize (scratchOuterMultiplier 1 P.scratchDegree) I.encode) P.program I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧
      cost ≤ P.timeConstant*(Nat.clog 2 (I.m+1)+1)*
        (Nat.clog 2 (I.m+1)+Nat.clog 2 (I.maxCapacity+1)+1)*Nat.clog 2 (I.maxCost+2)*
        (linkedConnectedSolverTime P.runtimeResources (P.timeConstant*min I.n I.m) (P.timeConstant*I.m)+I.m)+
        P.timeConstant*I.n := by
  apply outerScaling_runsTo_compressedPolynomialScratch P.solver 0 (linkedConnectedSolverTime P.runtimeResources)
    (connectedSolverRuntimeWorkspace P.runtimeResources) 1 P.scratchDegree
  · intro J
    exact solverContract_raise_time (P.solver_meetsContract J)
      (connectedSolverRuntimeTime_le_linkedConnectedSolverTime P.runtimeResources)
  · intro n m
    simpa only [Nat.one_mul] using P.workspace_le n m
  · exact P.solver_deterministic
  · exact linkedConnectedSolverTime_mono P.runtimeResources
  · exact hv

end MinCostFlow.Final
