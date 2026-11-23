module

public import MinCostFlow.SparseCore.Program.ContractOrder
public import MinCostFlow.MinRatio.SparseCoreContract

/-!
# Inputs and outputs of the ordered sparse-core machine contract

The ordered machine contract (`Contract.lean`) is stated for a model tool `tool` with orders
(`SparseCoreRestartTool`, with `initOrd`, `updateOrd`, `rot` and `restart`; Lemma 5.17, page 23,
with the bundle repair described in the README). This file gives its two pieces of bookkeeping.

* `SparseCoreOrdInput tool k M N s G ord n` records which input graph `G` and input order `ord`
  accompany the model state `s`, and how many input updates `n` it has received since its
  initialization. It is built from the operations, as `MinRatio.SparseCoreInput` is for the
  contract without orders. Each step also records the hypotheses that the paper's statement puts
  on the input and that the computation of the tool needs: a valid graph within the size bounds,
  positive lengths, an order that is a rotation, ordered batches with split bound two
  (`OrderedBatch`), and at most `updateThreshold k M N` updates in all. Restarts keep the graph
  and the order.
* `BranchOutAt` is the output of an update: for each branch `j < k`, the batch of its output
  graph (as `MinRatio.BranchBatchesAt`) and edits that turn its old output order into the new one.

Only definitions are here.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program

/-- The input graphs, input orders and update counts that can accompany a model state after the
operations of the ordered contract. -/
inductive SparseCoreOrdInput (tool : SparseCoreRestartTool) (k M N : ℕ) :
    tool.State → MGraph → (ℕ → List End) → ℕ → Prop
  | init (G : MGraph) (lengths gradient : ℕ → ℝ) (ord : ℕ → List End) (valid : G.IsValid)
      (hm : G.m ≤ M) (hn : G.n ≤ N) (pos : ∀ e ∈ G.E, 0 < lengths e)
      (rotation : IsRotationOrder G ord) :
      SparseCoreOrdInput tool k M N (tool.initOrd k M N G lengths gradient ord) G ord 0
  | update {s : tool.State} {G : MGraph} {ord : ℕ → List End} {n : ℕ}
      (input : SparseCoreOrdInput tool k M N s G ord n) (U : List Update)
      (lengths gradient : ℕ → ℝ) (ord' : ℕ → List End) (valid : G.BatchIsValid U)
      (pos : ∀ e ∈ (G.applyBatch U).E, 0 < lengths e) (ordered : OrderedBatch G U ord ord')
      (threshold : ((n + U.length : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold k M N) :
      SparseCoreOrdInput tool k M N (tool.updateOrd s U lengths gradient ord').1
        (G.applyBatch U) ord' (n + U.length)
  | restart {s : tool.State} {G : MGraph} {ord : ℕ → List End} {n : ℕ}
      (input : SparseCoreOrdInput tool k M N s G ord n) (j : ℕ) (branch : j < k) :
      SparseCoreOrdInput tool k M N (tool.restart s j) G ord n

/-- The output of an update at `a`: the branch count `k`, then four words per branch `j`: the
pointer and word count of the batch of the output graph (read on the old output graph
`oldGraphs j`), and the pointer and word count of edits that turn the old output order
`oldRot j` into the new one `newRot j`. -/
def BranchOutAt (mem : ℕ → ℕ) (a k : ℕ) (oldGraphs : ℕ → MGraph) (batches : ℕ → List Update)
    (oldRot newRot : ℕ → ℕ → List End) : Prop :=
  mem a = k ∧ ∀ j < k,
    SmallBatchAt mem (mem (a + 1 + 4 * j)) (oldGraphs j) (batches j) (mem (a + 2 + 4 * j)) ∧
    ∃ edits : List OrdEdit, OrdEditsAt mem (mem (a + 3 + 4 * j)) edits (mem (a + 4 + 4 * j)) ∧
      applyOrdEdits (oldRot j) edits = newRot j

end MinCostFlow.SparseCore.Program
