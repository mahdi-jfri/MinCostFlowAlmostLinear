module

public import MinCostFlow.SparseCore.Program.AssemblyReemb
public import MinCostFlow.SparseCore.Program.OrdEditsBlocks

/-!
# Block-aligned sparse-core contract extension (`AssemblyContractBlocks`)

Extends `sparseCoreOrdMachineContractKF` (`AssemblyStatement.lean`) and
`sparseCoreOrdMachineContractKFR` (`AssemblyReemb.lean`) without modifying
`sparseCoreOrdMachineContractK` or `sparseCoreOrdMachineContractKF` (which `MinRatio/` calls).

The single change adds `OrdEditsForBatch a.G (ordUpdateBatch a args mem) (readOrdEdits mem
(args.getD 4 0))` to the precondition of Update (`op 0`). All other operations (`init`, `op 1`–`5`),
postconditions, costs, and space bounds are definitionally identical.

* `sparseCoreOrdMachineContractKFB`: `sparseCoreOrdMachineContractKF` with `OrdEditsForBatch` in
  `pre 0`.
* `sparseCoreOrdMachineContractKFRB`: `sparseCoreOrdMachineContractKFR` with `OrdEditsForBatch` in
  `pre 0`.
* `dsRep_implements_kfb_of_kfrb`: any implementation of `KFRB` automatically implements `KFB`.
* `SparseCoreOrdProgramUniformReembCapBlocks`, `SparseCoreOrdProgramUniformCapBlocks`, and
  `sparseCoreOrdProgramUniformCapBlocks_of_reemb`: uniform capacity-indexed statements for `KFRB`
  and `KFB`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.LSF

/-- `sparseCoreOrdMachineContractKF` whose Update (`op 0`) precondition also requires the input
order edits to be block-aligned with the input update batch (`OrdEditsForBatch`), and whose
sparsifier readout (`op 3`) returns exact capacities `(vCap, eCap)`. -/
noncomputable def sparseCoreOrdMachineContractKFB {w : ℕ} (fmt : Num.Format w) (L : ℕ)
    (tool : SparseCoreRestartTool) (initialGraph : MGraph) (k M N vCap eCap capExp : ℕ)
    (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ) :
    DataStructure (SparseCoreOrdAbs tool) :=
  let D := sparseCoreOrdMachineContractKF fmt L tool initialGraph k M N vCap eCap capExp P
    allocation
  { D with
    pre := fun i a args mem => match i with
      | 0 => D.pre 0 a args mem ∧
          OrdEditsForBatch a.G (ordUpdateBatch a args mem) (readOrdEdits mem (args.getD 4 0))
      | i => D.pre i a args mem
    post := fun i a args mem a' mem' => match i with
      | 0 => D.post 0 a args mem a' mem' ∧
          (∀ j < k, OrdEditsForBatch (tool.S a.st j) ((ordUpdateModel fmt L a args mem).2 j)
            (readOrdEdits mem' (mem' (heapArg args + 3 + 4 * j)))) ∧
          (∀ j < k, OrdEditsValidFor vCap eCap (tool.rot a.st j)
            (readOrdEdits mem' (mem' (heapArg args + 3 + 4 * j))))
      | 3 =>
        let cur := heapArg args
        let b := args.getD 1 0
        a' = a ∧ ∃ graphVCap graphECap,
          DynGraphAt mem' (mem' cur) graphVCap graphECap (tool.S a.st b) ∧
          graphVCap = vCap ∧ graphECap = eCap
      | i => D.post i a args mem a' mem' }

/-- `sparseCoreOrdMachineContractKFR` (with `reembList` on `op 0`) whose Update (`op 0`)
precondition also requires the input order edits to be block-aligned with the input update batch
(`OrdEditsForBatch`), whose Update postcondition guarantees `OrdEditsForBatch` and
`OrdEditsValidFor` for every branch's output edits, and whose sparsifier readout (`op 3`) returns
exact capacities `(vCap, eCap)`. -/
noncomputable def sparseCoreOrdMachineContractKFRB {w : ℕ} (fmt : Num.Format w) (L : ℕ)
    (tool : SparseCoreRestartTool) (reemb : ToolReembFn tool)
    (initialGraph : MGraph) (k M N vCap eCap capExp : ℕ)
    (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ) :
    DataStructure (SparseCoreOrdAbs tool) :=
  let D := sparseCoreOrdMachineContractKFR fmt L tool reemb initialGraph k M N vCap eCap capExp P
    allocation
  { D with
    pre := fun i a args mem => match i with
      | 0 => D.pre 0 a args mem ∧
          OrdEditsForBatch a.G (ordUpdateBatch a args mem) (readOrdEdits mem (args.getD 4 0))
      | i => D.pre i a args mem
    post := fun i a args mem a' mem' => match i with
      | 0 => D.post 0 a args mem a' mem' ∧
          (∀ j < k, OrdEditsForBatch (tool.S a.st j) ((ordUpdateModel fmt L a args mem).2 j)
            (readOrdEdits mem' (mem' (heapArg args + 3 + 4 * j)))) ∧
          (∀ j < k, OrdEditsValidFor vCap eCap (tool.rot a.st j)
            (readOrdEdits mem' (mem' (heapArg args + 3 + 4 * j))))
      | 3 =>
        let cur := heapArg args
        let b := args.getD 1 0
        a' = a ∧ ∃ graphVCap graphECap,
          DynGraphAt mem' (mem' cur) graphVCap graphECap (tool.S a.st b) ∧
          graphVCap = vCap ∧ graphECap = eCap
      | i => D.post i a args mem a' mem' }

/-- Any implementation of `sparseCoreOrdMachineContractKFRB` automatically implements
`sparseCoreOrdMachineContractKFB` with the same representation, constants, and allocation. -/
theorem dsRep_implements_kfb_of_kfrb {w : ℕ} {fmt : Num.Format w} {L : ℕ}
    {tool : SparseCoreRestartTool} {reemb : ToolReembFn tool}
    {initialGraph : MGraph} {k M N vCap eCap capExp : ℕ}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)}
    (h : R.Implements w p init op
      (sparseCoreOrdMachineContractKFRB fmt L tool reemb initialGraph k M N vCap eCap capExp P
        allocation)) :
    R.Implements w p init op
      (sparseCoreOrdMachineContractKFB fmt L tool initialGraph k M N vCap eCap capExp P
        allocation) := by
  refine ⟨h.1, h.2.1, fun i b s x args mem pos ω hargs hhead hrep hpre hfoot hz hsp => ?_⟩
  obtain ⟨body, hbody, o, st', c, hrun, s', x', hrep', hpost, hresp, hcost⟩ :=
    h.2.2 i b s x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
  refine ⟨body, hbody, o, st', c, hrun, s', x', hrep', ?_, hresp, hcost⟩
  match i with
  | 0 => exact ⟨hpost.1.1, hpost.2⟩
  | 1 => exact hpost
  | 2 => exact hpost
  | 3 => exact hpost
  | _ + 4 => exact hpost

/-- Capacity-indexed uniform statement for `sparseCoreOrdMachineContractKFRB`. -/
def SparseCoreOrdProgramUniformReembCapBlocks (C_lsst : ℝ) (lsfInitAuto : ℕ → LSFInit)
    (impl : SparsifyImpl)
    (brReemb : ∀ depth, BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ)
    (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  ∀ capExp : ℕ, ∃ wordExp : ℕ, ∀ limbMul : ℕ,
    ∃ (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ),
      P.wordExp = wordExp ∧
      ∀ (depth w : ℕ) (fmt : Num.Format w),
        1 ≤ depth →
        ∃ (τ : Type) (phi : ℕ → τ → (ℕ → ℕ) → ℕ) (foot : ℕ → τ → ℕ → Prop),
          ∀ (L vCap eCap : ℕ),
            ∃ rep : ℕ → SparseCoreOrdAbs (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl) →
                τ → (ℕ → ℕ) → Prop,
              let R : DSRep (SparseCoreOrdAbs (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)) :=
                ⟨τ, rep, phi, foot⟩
              R.Local ∧ ∀ (G : MGraph) (k M N : ℕ),
                fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
                depth ≤ M + N + k + L →
                (∀ j < k, IsValidLSFInitFor (lsfInitAuto fmt.precision) C_lsst k j) →
                G.n ≤ G.m + 1 →
                R.Implements w p init op
                  (sparseCoreOrdMachineContractKFRB fmt L
                    (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)
                    (bundleToolReemb (brReemb depth))
                    G k M N vCap eCap capExp P allocation)

/-- Capacity-indexed uniform statement for `sparseCoreOrdMachineContractKFB`. -/
def SparseCoreOrdProgramUniformCapBlocks (C_lsst : ℝ) (lsfInitAuto : ℕ → LSFInit)
    (impl : SparsifyImpl) (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  ∀ capExp : ℕ, ∃ wordExp : ℕ, ∀ limbMul : ℕ,
    ∃ (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ),
      P.wordExp = wordExp ∧
      ∀ (depth w : ℕ) (fmt : Num.Format w),
        1 ≤ depth →
        ∃ (τ : Type) (phi : ℕ → τ → (ℕ → ℕ) → ℕ) (foot : ℕ → τ → ℕ → Prop),
          ∀ (L vCap eCap : ℕ),
            ∃ rep : ℕ → SparseCoreOrdAbs (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl) →
                τ → (ℕ → ℕ) → Prop,
              let R : DSRep (SparseCoreOrdAbs (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)) :=
                ⟨τ, rep, phi, foot⟩
              R.Local ∧ ∀ (G : MGraph) (k M N : ℕ),
                fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
                depth ≤ M + N + k + L →
                (∀ j < k, IsValidLSFInitFor (lsfInitAuto fmt.precision) C_lsst k j) →
                G.n ≤ G.m + 1 →
                R.Implements w p init op
                  (sparseCoreOrdMachineContractKFB fmt L
                    (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)
                    G k M N vCap eCap capExp P allocation)

theorem sparseCoreOrdProgramUniformCapBlocks_of_reemb {C_lsst : ℝ} {lsfInitAuto : ℕ → LSFInit}
    {impl : SparsifyImpl}
    {brReemb : ∀ depth, BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (h : SparseCoreOrdProgramUniformReembCapBlocks C_lsst lsfInitAuto impl brReemb p init op) :
    SparseCoreOrdProgramUniformCapBlocks C_lsst lsfInitAuto impl p init op := fun capExp => by
  obtain ⟨wordExp, hw⟩ := h capExp
  refine ⟨wordExp, fun limbMul => ?_⟩
  obtain ⟨P, allocation, hwe, hP⟩ := hw limbMul
  refine ⟨P, allocation, hwe, fun depth w fmt hdepth => ?_⟩
  obtain ⟨τ, phi, foot, hτ⟩ := hP depth w fmt hdepth
  refine ⟨τ, phi, foot, fun L vCap eCap => ?_⟩
  obtain ⟨rep, hloc, hR⟩ := hτ L vCap eCap
  exact ⟨rep, hloc, fun G k M N hfmt hcap hdle hInit hGn =>
    dsRep_implements_kfb_of_kfrb (hR G k M N hfmt hcap hdle hInit hGn)⟩

end MinCostFlow.SparseCore.Program
