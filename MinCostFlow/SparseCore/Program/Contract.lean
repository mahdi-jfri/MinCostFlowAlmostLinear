module

public import MinCostFlow.SparseCore.Program.ContractInput

/-!
# The ordered machine contract of a sparse-core level

`sparseCoreOrdMachineContract` is the `WordRAM.DataStructure` that a program of the sparse-core
tool with orders meets (Lemma 5.17, page 23, with the bundle repair described in the README).
It replaces
`MinRatio.sparseCoreMachineContract` for a tool with `initOrd`, `updateOrd`, `rot` and
`restart`. Its abstract state (`SparseCoreOrdAbs`) is the model state of the tool together with
its input graph, input order and update count, and every operation leaves exactly the model's next
state.

Operations: Update (`0`), Restart (`1`), LSF readout (`2`), sparsifier readout (`3`), embedding
readout (`4`), and output-order readout (`5`). Operations `2`–`4` are those of the contract
without orders.

* **Orders.** The initialization reads the whole input order (`OrdListAt`). An update reads the
  new order as edits of the stored one (`OrdEditsAt`), and writes, for each branch, the batch of
  its output graph and the edits of its output order (`BranchOutAt`). Operation `5` writes the
  whole output order of one branch, for the initialization of the next level.
* **Hypotheses.** The history relation `SparseCoreOrdInput` carries the hypotheses that the
  paper puts on the input of Lemma 5.17 and that the computation of the tool uses: valid graphs
  within the size bounds, positive lengths, ordered batches with split bound two, and at most
  `updateThreshold k M N` updates in all.
* **Cost.** Every operation that changes the state costs `mul` times the increase of the model's
  cost `tool.cost` plus the words it reads, with one constant `mul` free of the input. Since
  `tool.cost` is cumulative, the total machine cost of a level is at most `mul` times its final
  model cost plus the words read, and `IsSpecOrdRestart` bounds the final model cost. The input
  graph and order are part of the abstract state so that the next state, and so the cost, is a
  function of the abstract state and the arguments. Readouts `2`–`4` return pointers to
  owned cells and cost `readout`; readout `5` costs `mul` times the words it writes.
* **Word size.** The initialization asks `(M + N + 2) ^ wordExp < 2 ^ w` for a constant
  `wordExp`, so that the counters and names of the program fit in a word.

The initial graph is a logical parameter, as in the contract without orders: `DynGraphAt` does
not fix the endpoints of names that are not edges. Lengths and gradients are read as the zero
extension of the live-edge tables (`readEdgeValues`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.MinRatio

/-- The constants of the ordered contract: the cost multiplier `mul`, the cost `readout` of a
pointer readout, and the exponent `wordExp` of the word-size condition. All three are free of the
input. -/
structure SparseCoreOrdParams where
  mul : ℕ
  readout : ℕ
  wordExp : ℕ

/-- The words of the whole order stored at `a`. -/
def ordListWords (mem : ℕ → ℕ) (a : ℕ) : ℕ :=
  1 + ordRecordsWords (readOrdRecordsAt mem a)

/-- The abstract state of the ordered contract: the model state of the tool, with the input graph,
the input order and the number of input updates since the initialization. The last three are
logical: a program stores them only as far as it needs them. They make the next state, and so the
cost of an operation, a function of the abstract state and the arguments. -/
structure SparseCoreOrdAbs (tool : SparseCoreRestartTool) where
  st : tool.State
  G : MGraph
  ord : ℕ → List End
  n : ℕ

/-- The batch of an Update call, read on the input graph of `a`. -/
noncomputable def ordUpdateBatch {tool : SparseCoreRestartTool} (a : SparseCoreOrdAbs tool)
    (args : List ℕ) (mem : ℕ → ℕ) : List Update :=
  (decodeBatch mem (args.getD 2 0) a.G).1

/-- The input order after an Update call: the stored order with the edits read at `edits`. -/
def ordUpdateOrder {tool : SparseCoreRestartTool} (a : SparseCoreOrdAbs tool) (args : List ℕ)
    (mem : ℕ → ℕ) : ℕ → List End :=
  applyOrdEdits a.ord (readOrdEdits mem (args.getD 4 0))

/-- The model result of an Update call `[handle, graph, batch, words, edits, editWords, lengths,
gradient, heap]`: the next state and the batches of the output graphs. Lengths and gradients are
the zero extensions of the live-edge tables on the new graph. -/
noncomputable def ordUpdateModel {w : ℕ} (fmt : Num.Format w) (L : ℕ)
    {tool : SparseCoreRestartTool} (a : SparseCoreOrdAbs tool) (args : List ℕ) (mem : ℕ → ℕ) :
    tool.State × (ℕ → List Update) :=
  let U := ordUpdateBatch a args mem
  tool.updateOrd a.st U
    (readEdgeValues mem (args.getD 6 0) fmt.limbBits L fmt.precision (a.G.applyBatch U).E)
    (readEdgeValues mem (args.getD 7 0) fmt.limbBits L fmt.precision (a.G.applyBatch U).E)
    (ordUpdateOrder a args mem)

/-- The abstract state after an Update call. -/
noncomputable def ordUpdateNext {w : ℕ} (fmt : Num.Format w) (L : ℕ)
    {tool : SparseCoreRestartTool} (a : SparseCoreOrdAbs tool) (args : List ℕ) (mem : ℕ → ℕ) :
    SparseCoreOrdAbs tool :=
  ⟨(ordUpdateModel fmt L a args mem).1, a.G.applyBatch (ordUpdateBatch a args mem),
    ordUpdateOrder a args mem, a.n + (ordUpdateBatch a args mem).length⟩

/-- The abstract state after restarting branch `j`. -/
def ordRestartNext {tool : SparseCoreRestartTool} (a : SparseCoreOrdAbs tool) (j : ℕ) :
    SparseCoreOrdAbs tool :=
  ⟨tool.restart a.st j, a.G, a.ord, a.n⟩

/-- The precondition of an Update call `[handle, graph, batch, words, edits, editWords, lengths,
gradient, heap]` on the abstract state `a`: the history is one of the contract, and the graph at
`graph` is its input graph; the batch `U` read at `batch` is valid, within the caps and in compact
form; the edits at `edits` give the new order, and the batch is ordered from the stored order to
it; the update count stays within `updateThreshold k M N`; the new lengths are positive on the new
graph. -/
def SparseCoreOrdUpdateAt {w : ℕ} (fmt : Num.Format w) (L : ℕ)
    (tool : SparseCoreRestartTool) (k M N vCap eCap : ℕ) (a : SparseCoreOrdAbs tool)
    (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ handle graph batch words edits editWords lengths gradient heap,
    args = [handle, graph, batch, words, edits, editWords, lengths, gradient, heap] ∧
    SparseCoreOrdInput tool k M N a.st a.G a.ord a.n ∧ DynGraphAt mem graph vCap eCap a.G ∧
    let U := ordUpdateBatch a args mem
    SmallBatchAt mem batch a.G U words ∧ a.G.BatchIsValid U ∧ BatchWithinCaps vCap eCap U ∧
    OrdEditsAt mem edits (readOrdEdits mem edits) editWords ∧
    OrderedBatch a.G U a.ord (ordUpdateOrder a args mem) ∧
    ((a.n + U.length : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold k M N ∧
    (∀ j < words, mem (batch + j) < 2 ^ w) ∧ (∀ j < editWords, mem (edits + j) < 2 ^ w) ∧
    graph + dynGraphSize vCap eCap ≤ heap ∧ batch + words ≤ heap ∧ edits + editWords ≤ heap ∧
    lengths + eCap * L ≤ heap ∧ gradient + eCap * L ≤ heap ∧
    (∀ e ∈ (a.G.applyBatch U).E, e < eCap ∧
      Num.Valid mem (lengths + e * L) fmt.limbBits L ∧
      Num.Valid mem (gradient + e * L) fmt.limbBits L) ∧
    ∀ e ∈ (a.G.applyBatch U).E,
      0 < readEdgeValues mem lengths fmt.limbBits L fmt.precision (a.G.applyBatch U).E e

/-- The precondition of a call `[handle, branch, heap]` (Restart, sparsifier readout, order
readout) or `[handle, branch, graph, heap]` (LSF and embedding readouts, which also read the input
graph at `graph`). -/
def SparseCoreOrdBranchAt (tool : SparseCoreRestartTool) (k M N vCap eCap : ℕ)
    (a : SparseCoreOrdAbs tool) (withGraph : Bool) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  SparseCoreOrdInput tool k M N a.st a.G a.ord a.n ∧
  if withGraph then ∃ handle branch graph heap, args = [handle, branch, graph, heap] ∧
    branch < k ∧ DynGraphAt mem graph vCap eCap a.G ∧ graph + dynGraphSize vCap eCap ≤ heap
  else ∃ handle branch heap, args = [handle, branch, heap] ∧ branch < k

/-- The words of the output order of branch `j`, written with one record per vertex of its
output graph. -/
def ordRotWords {tool : SparseCoreRestartTool} (a : SparseCoreOrdAbs tool) (j : ℕ) : ℕ :=
  ordWordsOn (tool.S a.st j).V (tool.rot a.st j)

/-- The ordered machine interface of Lemma 5.17 (page 23) with the restart of a branch spanner.
Initialization `[graph, lengths, gradient, ord, heap]` builds `tool.initOrd` on the initial graph,
its zero-extended lengths and gradients, and the order read at `ord`, and writes nothing else.
Update and Restart leave the model's next state; Update writes `BranchOutAt` at the old heap.
Readouts leave the state unchanged. Allocation is a parameter independent of the time bound, as in
`WordRAM.DataStructure`. -/
noncomputable def sparseCoreOrdMachineContract {w : ℕ} (fmt : Num.Format w) (L : ℕ)
    (tool : SparseCoreRestartTool) (initialGraph : MGraph) (k M N vCap eCap : ℕ)
    (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ) :
    DataStructure (SparseCoreOrdAbs tool) where
  initPre args mem := ∃ graph lengths gradient ord heap,
    args = [graph, lengths, gradient, ord, heap] ∧ 0 < k ∧
    (M + N + 2) ^ P.wordExp < 2 ^ w ∧
    DynGraphAt mem graph vCap eCap initialGraph ∧ initialGraph.IsValid ∧
    initialGraph.m ≤ M ∧ initialGraph.n ≤ N ∧
    graph + dynGraphSize vCap eCap ≤ heap ∧
    lengths + eCap * L ≤ heap ∧ gradient + eCap * L ≤ heap ∧
    OrdListAt mem ord (readOrd mem ord) (ordListWords mem ord) ∧
    ord + ordListWords mem ord ≤ heap ∧ (∀ j < ordListWords mem ord, mem (ord + j) < 2 ^ w) ∧
    IsRotationOrder initialGraph (readOrd mem ord) ∧
    (∀ e ∈ initialGraph.E, e < eCap ∧ Num.Valid mem (lengths + e * L) fmt.limbBits L ∧
      Num.Valid mem (gradient + e * L) fmt.limbBits L) ∧
    ∀ e ∈ initialGraph.E,
      0 < readEdgeValues mem lengths fmt.limbBits L fmt.precision initialGraph.E e
  initPost args mem a _ :=
    a = ⟨tool.initOrd k M N initialGraph
      (readEdgeValues mem (args.getD 1 0) fmt.limbBits L fmt.precision initialGraph.E)
      (readEdgeValues mem (args.getD 2 0) fmt.limbBits L fmt.precision initialGraph.E)
      (readOrd mem (args.getD 3 0)), initialGraph, readOrd mem (args.getD 3 0), 0⟩
  initCost args mem :=
    P.mul * (tool.cost (tool.initOrd k M N initialGraph
        (readEdgeValues mem (args.getD 1 0) fmt.limbBits L fmt.precision initialGraph.E)
        (readEdgeValues mem (args.getD 2 0) fmt.limbBits L fmt.precision initialGraph.E)
        (readOrd mem (args.getD 3 0))) +
      initialGraph.n + initialGraph.m + ordListWords mem (args.getD 3 0) + 1)
  initSpace args _ := allocation 6 args
  pre i a args mem := match i with
    | 0 => SparseCoreOrdUpdateAt fmt L tool k M N vCap eCap a args mem
    | 1 | 3 | 5 => SparseCoreOrdBranchAt tool k M N vCap eCap a false args mem
    | 2 | 4 => SparseCoreOrdBranchAt tool k M N vCap eCap a true args mem
    | _ => False
  post i a args mem a' mem' := match i with
    | 0 => a' = ordUpdateNext fmt L a args mem ∧
        BranchOutAt mem' (heapArg args) k (tool.S a.st) (ordUpdateModel fmt L a args mem).2
          (tool.rot a.st) (tool.rot a'.st)
    | 1 => a' = ordRestartNext a (args.getD 1 0)
    | 2 => a' = a ∧ ∃ forestVCap forestECap,
        LSFAt mem' (heapArg args) forestVCap forestECap fmt.limbBits L fmt.precision
          a.G.E (tool.lsfs a.st (args.getD 1 0))
    | 3 => a' = a ∧ ∃ graphVCap graphECap,
        DynGraphAt mem' (mem' (heapArg args)) graphVCap graphECap (tool.S a.st (args.getD 1 0))
    | 4 => a' = a ∧ EmbeddingReadoutAt mem' (heapArg args) (mem' (heapArg args + 1)) a.G
        (tool.lsfs a.st (args.getD 1 0)) (tool.emb a.st (args.getD 1 0))
    | 5 => a' = a ∧ ∃ words,
        OrdListAt mem' (mem' (heapArg args)) (tool.rot a.st (args.getD 1 0)) words ∧
        words ≤ ordRotWords a (args.getD 1 0)
    | _ => False
  cost i a args mem := match i with
    | 0 => P.mul * (tool.cost (ordUpdateNext fmt L a args mem).st - tool.cost a.st +
        args.getD 3 0 + args.getD 5 0 + 1)
    | 1 => P.mul * (tool.cost (tool.restart a.st (args.getD 1 0)) - tool.cost a.st + 1)
    | 2 | 3 | 4 => P.readout
    | 5 => P.mul * (ordRotWords a (args.getD 1 0) + 1)
    | _ => 0
  space i a args _ := match i with
    | 0 => allocation 0 args
    | 1 => allocation 1 args
    | 2 => 4
    | 3 => 1
    | 4 => 2
    | 5 => 1 + ordRotWords a (args.getD 1 0)
    | _ => 0

end MinCostFlow.SparseCore.Program
