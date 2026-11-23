module

public import MinCostFlow.SparseCore.Program.CompAsmWrapInit
public import MinCostFlow.Final.AssemblyDryRunSCComp

/-!
# Concrete P4 implementation in the dry run (`AssemblyDryRunSCCompImpl`)

Instantiates the three sparse-core P4 pieces (`dryCompCode`, `dryCFS`, `dryCF_hyp`) of
`theorem_1_1_skeleton` unconditionally for `dryLSFInitUsed` (`Final/AssemblyDryRun.lean`) using:
* the verified thin wrapper `compAsmCode` / `compAsmSpec` / `compAsmFamilyHyp`
  (`SparseCore/Program/CompAsmWrapInit.lean`),
* `an_fullSpec` and `anRhoConstLog_le` (`Final/AssemblyDryRunWitness.lean`,
  `Final/AssemblyDryRun.lean`),
* `compBatchCost_polylog` (`Final/AssemblyDryRunSCComp.lean`).
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.SparseCore.Program MinCostFlow.DynSpanner.Program

/-- Concrete deterministic P4 code block for the dry run (`anProgram`, `anWordConst`,
`anK`). -/
def dryCompCode : ScCompCode :=
  compAsmCode anProgram anWordConst anK an_fullSpec

/-- Concrete P4 specification (`wordExp 3 = 7 ≤ 39`). -/
def dryCFS : AsmCompFamilySpec :=
  compAsmSpec anProgram anWordConst anK

/-- `dryCFS.wordExp 3 ≤ 39` (`7 ≤ 39`). -/
theorem dryCFS_wordExp_le_39 : dryCFS.wordExp 3 ≤ 39 :=
  compAsmSpec_wordExp_le_39 anProgram anWordConst anK

/-- **Unconditional `ScCompFamilyHyp` for P4 in the dry run:** connects `dryCompCode` and `dryCFS`
to `dryLSFInitUsed` with no further hypothesis. -/
theorem dryCF_hyp :
    ScCompFamilyHyp dryCFS dryLSFInitUsed ⟨dryCompCode.procs⟩
      dryCompCode.fInit dryCompCode.fBatch dryCompCode.fExport dryCompCode.fRoot :=
  compAsmFamilyHyp an_fullSpec anRhoConstLog_le fun _ _ _ _ _ _ _ _ _ hk _ _ _ hI hB hV =>
    compBatchCost_polylog _ hk hI hB hV

end MinCostFlow.Final.DryRun

end
