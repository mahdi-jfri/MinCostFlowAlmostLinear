module

public import MinCostFlow.SparseCore.Program.AssemblyBranchFacts
public import MinCostFlow.SparseCore.Program.OutFlags
import MinCostFlow.SparseCore.CompLSFBridge

/-!
# The model preconditions of P7's step from the facts of a branch (`AssemblyBranchStepModel`)

The output step of P7 (`sig_outStepSmall_runs`) asks for model facts about the old state `tr` of
the branch and the new state `(stepBundleTree sparsify tr U ord ord').state`: the readiness
`OutStepReady`, the flags `OutFlagsOk`, and the bounds on the new roots and the new output edges.
This file derives them from the facts `AsmBrModelFacts` of the old and the new state
(`AssemblyBranchFacts.lean`) and the two facts on the batch that `step_runs` already takes (the
batch is valid and ordered). These are the model steps of the second call of the step program
(`asmBrStepStmt`, `AssemblyBranchStepIface.lean`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

variable {depth : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)

/-- **P7's readiness.** The LSF invariant, the validity of `S_cur`, its vertex set and the old core
graph inside it come from the facts of the old state. The new core graph inside the new `S_cur`
comes from `RestartScurModelInv` of the new state, whose LSF state is `compLSFBatch tr.cs U`. -/
theorem asmBr_outStepReady {impl : SparsifyImpl} {vCap eCap vCap' eCap' : ℕ}
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    (hold : AsmBrModelFacts impl vCap eCap tr ord)
    (hnew : AsmBrModelFacts impl vCap' eCap' (stepBundleTree sparsify tr U ord ord').state ord')
    (hBU : tr.cs.G.BatchIsValid U) (hord : OrderedBatch tr.cs.G U ord ord') :
    OutStepReady sparsify tr U ord ord' := by
  obtain ⟨-, ⟨C, ℓ, hI, -⟩, hS, -, hval, -⟩ := hold
  exact ⟨C, ℓ, hI, hBU, hord, hval, hS.2.1, hS.2.2.2.1, hnew.2.2.1.2.2.2.1⟩

/-- **The new roots are below the vertex cap**: they are vertices of the new graph
(`compLSF_RF_isRSF`), whose names are below `vCap` by the facts of the new state. -/
theorem asmBr_newRoots_lt {impl : SparsifyImpl} {vCap eCap : ℕ}
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    (hnew : AsmBrModelFacts impl vCap eCap (stepBundleTree sparsify tr U ord ord').state ord') :
    ∀ v ∈ (stepBundleTree sparsify tr U ord ord').state.cs.RF.R, v < vCap := by
  obtain ⟨-, ⟨C, ℓ, hI, -⟩, -, -, -, -, -, hV, -⟩ := hnew
  exact fun v hv => hV v ((compLSF_RF_isRSF hI).2.2.1 hv)

/-- **The new output edges are below the edge cap**, by the facts of the new state. -/
theorem asmBr_newOut_lt {impl : SparsifyImpl} {vCap eCap : ℕ}
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    (hnew : AsmBrModelFacts impl vCap eCap (stepBundleTree sparsify tr U ord ord').state ord') :
    ∀ e ∈ (stepBundleTree sparsify tr U ord ord').state.S_cur.E, e < eCap :=
  hnew.2.2.2.2.2.2.2.2.2

/-- **P7's flags** (`outFlagsOk_of`), from the readiness and the bound on the new roots. -/
theorem asmBr_outFlagsOk {impl : SparsifyImpl} {vCap eCap vCap' eCap' : ℕ}
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    (hold : AsmBrModelFacts impl vCap' eCap' tr ord)
    (hnew : AsmBrModelFacts impl vCap eCap (stepBundleTree sparsify tr U ord ord').state ord')
    (hBU : tr.cs.G.BatchIsValid U) (hord : OrderedBatch tr.cs.G U ord ord') :
    OutFlagsOk sparsify tr U ord ord' vCap :=
  outFlagsOk_of sparsify tr U ord ord' (asmBr_outStepReady sparsify hold hnew hBU hord)
    (asmBr_newRoots_lt sparsify hnew)

end MinCostFlow.SparseCore.Program
