module

public import MinCostFlow.SparseCore.Program.AssemblyContract
public import MinCostFlow.SparseCore.Program.OrdStoreCapContract

/-!
# The statement of the sparse-core program, uniform in the level and the format

A program of the sparse-core tool (Lemma 5.17, page 23, with the bundle repair described in the
README) is
called by the solver at every level of the chain and for every instance. So its constants, and the
representation of its states, must not depend on what changes between levels and instances.

* **The order of the quantifiers.** The constants `P` and `allocation` are chosen before the depth
  `depth` of the tool, the word size, the format and the limb count. The depth of the solver's tool
  is `chosenL (M₀ ^ 2)`, which depends on the input, so constants chosen after it could depend on
  the input. The representation `R` is chosen before the graph, `k`, `M`, `N`, `vCap` and `eCap`,
  since the solver keeps one representation for all levels and all rebuilds, and these differ
  between them.
* **The format.** The LSF initializer is a family `lsfInit : ℕ → ℕ → LSFInit` indexed by the limb
  count and the precision, and the tool of an instance uses the member at the instance's own
  format. One program serves every format, so it must receive the limb count `L` and the precision
  at the initialization: they are the words at positions `7` and `8` of its arguments.
* **The edits.** The precondition of an update constrains the edits only through the order they
  produce (`OrderedBatch` of the batch from the stored order to the result). The order store (piece
  P1) needs more: each edit within the capacities, and an order with every end in at most one list
  after every prefix (`OrdEditsUniqueWithin`). This does not follow
  (`AssemblyUnique.lean`, `not_ordEditsUniqueWithin_of_orderedBatch`), so the precondition of an
  update also asks for it (`OrdEditsValidFor`).

`sparseCoreOrdMachineContractKF` is `sparseCoreOrdMachineContractK` with these two changes, and
`SparseCoreOrdProgramUniform` is the statement in the order above. Only definitions are here.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.MinRatio MinCostFlow.LSF

/-- The edits `edits` can be sent to the order store holding `ord`: each names vertices below
`vCap` and edges below `eCap`, and every prefix leaves an order within the capacities with every
end in at most one list. -/
def OrdEditsValidFor (vCap eCap : ℕ) (ord : ℕ → List End) (edits : List OrdEdit) : Prop :=
  OrdEditsWithin vCap eCap edits ∧ OrdEditsUniqueWithin vCap eCap ord edits

/-- The sparse-core contract of one level, for a program that serves every format. It is
`sparseCoreOrdMachineContractK` with two changes.
* Initialization arguments `[graph, lengths, gradient, ord, k, M, N, L, P_fp, heap]`, with `L` the
  limb count and `P_fp = fmt.precision`. The words at positions `1`–`3` are those of the old
  contract, so `initPost` and `initCost` read the same words.
* An update also asks that its edits can be sent to the order store (`OrdEditsValidFor`). -/
noncomputable def sparseCoreOrdMachineContractKF {w : ℕ} (fmt : Num.Format w) (L : ℕ)
    (tool : SparseCoreRestartTool) (initialGraph : MGraph) (k M N vCap eCap capExp : ℕ)
    (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ) :
    DataStructure (SparseCoreOrdAbs tool) :=
  let D := sparseCoreOrdMachineContractK fmt L tool initialGraph k M N vCap eCap capExp P
    allocation
  { D with
    initPre := fun args mem => ∃ graph lengths gradient ord heap,
      args = [graph, lengths, gradient, ord, k, M, N, L, fmt.precision, heap] ∧
      D.initPre [graph, lengths, gradient, ord, k, M, N, heap] mem
    pre := fun i a args mem => match i with
      | 0 => D.pre 0 a args mem ∧
          OrdEditsValidFor vCap eCap a.ord (readOrdEdits mem (args.getD 4 0))
      | i => D.pre i a args mem }

/-- The tool of the sparse-core program at depth `depth`, for the LSF initializer `lsfInit` and the
sparsifier `canonicalSparsify impl`. -/
noncomputable abbrev sparseCoreProgTool (lsfInit : LSFInit) (C_lsst : ℝ) (depth : ℕ)
    (impl : SparsifyImpl) : SparseCoreRestartTool :=
  sparseCoreBundleRestartToolMachWith lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
    (canonicalSparsifyParams impl) (dsAmortConst impl)

/-- **The statement of the sparse-core program** (piece P9). The program `p` with procedures
`init` and `op 0, …, op 5` implements the contract `sparseCoreOrdMachineContractKF` of the tool
with the machine cost, for the member `lsfInit L fmt.precision` of the family of LSF initializers
and the sparsifier `canonicalSparsify impl`, at limbs of `4` bits and under the split cap/limb
condition `SparseCoreCapHyp capExp limbMul`. The word-size exponent `wordExp` is chosen from
`capExp` alone (before `limbMul`); the cost multiplier `P.mul` and space function `allocation` may
depend on both `capExp` and `limbMul`, before the depth, word size, format, and limb count. -/
def SparseCoreOrdProgramUniform (C_lsst : ℝ) (lsfInit : ℕ → ℕ → LSFInit) (impl : SparsifyImpl)
    (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  ∀ capExp : ℕ, ∃ wordExp : ℕ, ∀ limbMul : ℕ,
    ∃ (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ),
      P.wordExp = wordExp ∧
      ∀ (depth w : ℕ) (fmt : Num.Format w) (L : ℕ),
        ∃ R : DSRep (SparseCoreOrdAbs
            (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)),
          R.Local ∧ ∀ (G : MGraph) (k M N vCap eCap : ℕ),
            fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
            R.Implements w p init op
              (sparseCoreOrdMachineContractKF fmt L
                (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)
                G k M N vCap eCap capExp P allocation)

end MinCostFlow.SparseCore.Program
