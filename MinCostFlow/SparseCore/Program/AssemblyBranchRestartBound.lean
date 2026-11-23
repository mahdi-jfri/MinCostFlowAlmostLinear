module

public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartFrame
public import MinCostFlow.SparseCore.Program.EmbRefresh

/-!
# The refresh term of the restart of a branch (`AssemblyBranchRestartBound`)

The third call of the restart of a branch refreshes the embedding table (`AsmBrEmbRefreshDisjAt`,
`EmbRefresh.lean`). Its cost and its space are at most `embMul` times
`embRefreshSizeAt + slots + 1` on the new spanners (`asmBrEmbBound`). This file defines that
bound and the heap space of the whole restart (`asmBrRestartSpace`), and shows that the bound is
paid by the model's charge of the restart when the side keeps its model facts
(`asmBrEmbBound_le_machCost`, from `embRefresh_restart_cost_le`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The bound on the cost and the space of the refresh of the embedding table after a restart
(`AsmBrEmbRefreshDisjAt`). -/
noncomputable def asmBrEmbBound (embMul : ℕ) (SP : DSParams) {slotCap cap : ℕ}
    (S : Fin slotCap → Option BundleState) (S6 : BucketSpannerState cap) (cs : CompLSFState)
    (ord : ℕ → List End) (k : ℕ) (slots : List ℕ) : ℕ :=
  embMul * (embRefreshSizeAt SP (restartSpanState S6 S cs ord k slots) slots + slots.length + 1)

/-- The heap space of the restart of a branch: the space of the restart of P8, of the reset of P7
and of the refresh of the embedding table. -/
noncomputable def asmBrRestartSpace (bunSpace : ℕ → ℕ) (readMul embMul : ℕ) (OS : OutTourSpec)
    (SP : DSParams) {slotCap cap : ℕ} (S : Fin slotCap → Option BundleState)
    (S6 : BucketSpannerState cap) (cs : CompLSFState) (ord : ℕ → List End) (k : ℕ)
    (slots : List ℕ) (vCap eCap tCap L_w : ℕ) : ℕ :=
  asmBrP8Space bunSpace readMul SP S S6 cs ord k slots vCap tCap L_w +
    outResetSpace OS (2 * eCap) + asmBrEmbBound embMul SP S S6 cs ord k slots

/-- **The refresh is paid by the restart charge.** When the bundle side keeps its model facts,
the refresh with the multiplier `embRefreshMul` of `embRefreshStmt` costs at most
`1200 · singleBundleRestartMachCost` (`embRefresh_restart_cost_le`). -/
theorem asmBrEmbBound_le_machCost
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth L capExp limbMul vCap eCap : ℕ} {tr : BundleTreeState depth}
    {ord : ℕ → List End} {y : AsmBrSide B5 depth} {Ψ : BundleTreeState depth → ℕ}
    (hmod : AsmBrSideModel impl w depth L capExp limbMul Ψ ⟨tr, ord, vCap, eCap⟩ y) :
    asmBrEmbBound embRefreshMul (asmBrSP impl w depth y) y.bunS y.spanS tr.cs ord tr.k y.slots ≤
      1200 * singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord := by
  obtain ⟨hMap, hMatch, -, -, hok, -, -, hPle, hC, hSB, -, -, -⟩ := hmod
  exact embRefresh_restart_cost_le (asmBrSP impl w depth y) (tr := tr) y.spanS ord hMap hMatch
    hok hPle hC hSB

end MinCostFlow.SparseCore.Program
