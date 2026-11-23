module

public import MinCostFlow.MinRatio.SparseCoreBoundary
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import WordRAM.DataStructure
public import Mathlib.Data.Nat.Log

/-!
# Machine contract for a sparse-core level

Lemma 5.17 (page 23) supplies initialization, updates, and branch readouts.
The restart operation is the fresh-spanner restart in the corrected Shift
procedure. The model's state type is unchanged. Its input graph is related
to that state by the operation history, rather than a new graph projection
required of the model tool.

Operations are Update (0), Restart (1), LSF readout (2), sparsifier readout
(3), and embedding readout (4). Readouts return pointers to owned cells.
Output graphs carry their own capacities. No bound on numeric names is
inferred from the number of edges in a model graph.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM DynSpanner.Program Chain

/-- Explicit factors in the per-level budgets of Lemma 5.17 (page 23).
`rate` bounds the recourse factor; `numeric` pays for fixed-point operations.
The time bound of a caller must bound these factors in the paper's form. -/
structure SparseCoreMachineCosts where
  constant : ℕ
  logExponent : ℕ
  numeric : ℕ
  rate : ℕ → ℕ

/-- The common polylogarithmic factor, using integer binary logarithms. -/
def SparseCoreMachineCosts.factor (costs : SparseCoreMachineCosts) (M N : ℕ) : ℕ :=
  costs.constant * costs.numeric * costs.rate M * (Nat.clog 2 (M + N + 2) + 1) ^ costs.logExponent

/-- A single branch restart has the one-branch initialization
budget from Algorithm 1 (page 24), as in `IsSpecRestart`. -/
def SparseCoreMachineCosts.restartCost (costs : SparseCoreMachineCosts) (M N : ℕ) : ℕ :=
  costs.factor M N * (M + 1)

/-- A state and its current input graph, with that graph in the shared layout. -/
def SparseCoreGraphAt (tool : SparseCoreTool) (restart : tool.State → ℕ → tool.State)
    (k : ℕ) (s : tool.State) (mem : ℕ → ℕ) (graph vCap eCap : ℕ) (G : MGraph) : Prop :=
  SparseCoreInput tool restart k s G ∧ DynGraphAt mem graph vCap eCap G

/-- The shared input conditions of an Update call. The word count is
explicit, so a variable-length split batch is bounded before it is read. -/
def SparseCoreUpdateAt {w : ℕ} (fmt : Num.Format w) (L : ℕ)
    (tool : SparseCoreTool) (restart : tool.State → ℕ → tool.State) (k vCap eCap : ℕ)
    (s : tool.State) (args : List ℕ) (mem : ℕ → ℕ) (G : MGraph) (U : List Update) : Prop :=
  ∃ handle graph batch words lengths gradient heap,
    args = [handle, graph, batch, words, lengths, gradient, heap] ∧
    SparseCoreGraphAt tool restart k s mem graph vCap eCap G ∧
    SmallBatchAt mem batch G U words ∧ G.BatchIsValid U ∧
    BatchWithinCaps vCap eCap U ∧ (∀ j < words, mem (batch + j) < 2 ^ w) ∧
    graph + dynGraphSize vCap eCap ≤ heap ∧ batch + words ≤ heap ∧
    lengths + eCap * L ≤ heap ∧ gradient + eCap * L ≤ heap ∧
    (∀ e ∈ (G.applyBatch U).E, e < eCap ∧
      Num.Valid mem (lengths + e * L) fmt.limbBits L ∧
      Num.Valid mem (gradient + e * L) fmt.limbBits L) ∧
    ∀ e ∈ (G.applyBatch U).E,
      0 < readEdgeValues mem lengths fmt.limbBits L fmt.precision (G.applyBatch U).E e

/-- Machine interface of Lemma 5.17, including the branch-spanner restart.
Initialization writes no readout. Update writes `BranchBatchesAt` at the
old heap. Readouts leave the state unchanged. All numeric arguments are
zero-extended off the current input graph. Allocation is independent of
the time budget, as in `WordRAM.DataStructure`. The initial graph is a
logical parameter because its unused total endpoint values are not encoded
by `DynGraphAt`; initialization still uses exactly that model graph. -/
noncomputable def sparseCoreMachineContract {w : ℕ} (fmt : Num.Format w) (L : ℕ)
    (tool : SparseCoreRestartTool) (initialGraph : MGraph)
    (k M N vCap eCap : ℕ) (costs : SparseCoreMachineCosts)
    (allocation : ℕ → List ℕ → ℕ) : DataStructure tool.State where
  initPre args mem := ∃ graph lengths gradient heap,
    args = [graph, lengths, gradient, heap] ∧ 0 < k ∧
    DynGraphAt mem graph vCap eCap initialGraph ∧ initialGraph.m ≤ M ∧ initialGraph.n ≤ N ∧
    graph + dynGraphSize vCap eCap ≤ heap ∧
    lengths + eCap * L ≤ heap ∧ gradient + eCap * L ≤ heap ∧
    (∀ e ∈ initialGraph.E, Num.Valid mem (lengths + e * L) fmt.limbBits L ∧
      Num.Valid mem (gradient + e * L) fmt.limbBits L) ∧
    ∀ e ∈ initialGraph.E, 0 < readEdgeValues mem lengths fmt.limbBits L fmt.precision initialGraph.E e
  initPost args mem s _ :=
    s = tool.init k M N initialGraph
      (readEdgeValues mem (args.getD 1 0) fmt.limbBits L fmt.precision initialGraph.E)
      (readEdgeValues mem (args.getD 2 0) fmt.limbBits L fmt.precision initialGraph.E)
  initCost _ _ := costs.factor M N * (M + 1) * k
  initSpace args _ := allocation 5 args
  pre i s args mem := match i with
    | 0 => ∃ G U, SparseCoreUpdateAt fmt L tool.toSparseCoreTool tool.restart k vCap eCap s args mem G U
    | 1 => ∃ handle branch heap G, args = [handle, branch, heap] ∧
        branch < k ∧ SparseCoreInput tool.toSparseCoreTool tool.restart k s G
    | 2 | 4 => ∃ handle branch graph heap G, args = [handle, branch, graph, heap] ∧
        branch < k ∧ SparseCoreGraphAt tool.toSparseCoreTool tool.restart k s mem graph vCap eCap G ∧
        graph + dynGraphSize vCap eCap ≤ heap
    | 3 => ∃ handle branch heap G, args = [handle, branch, heap] ∧
        branch < k ∧ SparseCoreInput tool.toSparseCoreTool tool.restart k s G
    | _ => False
  post i s args mem s' mem' := match i with
    | 0 => ∀ G U, SparseCoreUpdateAt fmt L tool.toSparseCoreTool tool.restart k vCap eCap s args mem G U →
        let result := tool.update s U
          (readEdgeValues mem (args.getD 4 0) fmt.limbBits L fmt.precision (G.applyBatch U).E)
          (readEdgeValues mem (args.getD 5 0) fmt.limbBits L fmt.precision (G.applyBatch U).E)
        s' = result.1 ∧ BranchBatchesAt mem' (heapArg args) k (tool.S s) result.2
    | 1 => s' = tool.restart s (args.getD 1 0)
    | 2 => s' = s ∧ ∃ forestVCap forestECap,
        LSFAt mem' (heapArg args) forestVCap forestECap fmt.limbBits L fmt.precision
          (readNamedGraph mem (args.getD 2 0) vCap eCap).E (tool.lsfs s (args.getD 1 0))
    | 3 => s' = s ∧ ∃ graphVCap graphECap,
        DynGraphAt mem' (mem' (heapArg args)) graphVCap graphECap (tool.S s (args.getD 1 0))
    | 4 => s' = s ∧ EmbeddingReadoutAt mem' (heapArg args) (mem' (heapArg args + 1))
        (readNamedGraph mem (args.getD 2 0) vCap eCap)
        (tool.lsfs s (args.getD 1 0)) (tool.emb s (args.getD 1 0))
    | _ => False
  cost i _ args _ := match i with
    | 0 => costs.factor M N * k * (1 + args.getD 3 0)
    | 1 => costs.restartCost M N
    | 2 | 3 | 4 => 64
    | _ => 0
  space i _ args _ := match i with
    | 0 => allocation 0 args
    | 1 => allocation 1 args
    | 2 => 4
    | 3 => 1
    | 4 => 2
    | _ => 0

end MinCostFlow.MinRatio
