module

public import MinCostFlow.Final.AssemblyDryRunSCFirstStep
public import MinCostFlow.SparseCore.Program.AssemblyFsCostTop

/-!
# Cost goal of the first step in the dry run (`AssemblyDryRunSCFirstStepCost`)

Instantiates `asmFirstStep_hCost` (`SparseCore/Program/AssemblyFsCostTop.lean`) at the concrete
program `scProg sparsifyImplUsed dryCompCode asmFsStepCode dryFirstInit` and its root/end-root
witnesses `asmFsRootSc` (`mul = tourMul + 40`) and `asmFsKSc` (`HE.mul = tourMul`) to discharge
`DryFirstStepCost dryFsStepMul` (`Final/AssemblyDryRunSCFirstStep.lean`).
-/

namespace MinCostFlow.Final.DryRun

open MinCostFlow.SparseCore.Program

@[expose] public section

/-- Explicit cost multiplier of the first phase of a branch step in the dry run, obtained from
`asmFsCostMul` at `tourBundleSpec`, `hRoot.mul = tourMul + 40`, and `K.HE.mul = tourMul`. -/
noncomputable def dryFsStepMul (capExp _limbMul : ℕ) : ℕ :=
  asmFsCostMul tourBundleSpec (tourMul + 40) tourMul capExp

end

public section

/-- **Discharge of `DryFirstStepCost`** (`Final/AssemblyDryRunSCFirstStep.lean`): instantiates
`asmFirstStep_hCost` at the concrete dry-run program and roots, with no further premise. -/
theorem dryFirstStep_cost : DryFirstStepCost dryFsStepMul := by
  intro depth _ capExp limbMul w P L_in _
  exact asmFirstStep_hCost

end

end MinCostFlow.Final.DryRun
