module

public import MinCostFlow.MinRatio.GraphRead
public import MinCostFlow.MinRatio.LastLevelContract
public import MinCostFlow.DynSpanner.Program.EmbLayouts
import MinCostFlow.LSF.Lemma54Init

/-!
# Inputs and outputs of a sparse-core level

Lemma 5.17 (page 23) returns one batch per branch. A batch collection has
its branch count followed by pairs of batch pointers and encoded word
counts. Each batch uses the shared compact update layout, interpreted on
the branch's graph before the update.

The model tool's opaque state need not contain a graph projection. The
input relation below records which graph can accompany a state after
initialization, updates, and branch restarts. It adds no data or correctness
property to the state. The restart function is a separate parameter so
that the same boundary applies to the underlying `SparseCoreTool` of a
`SparseCoreRestartTool`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM DynSpanner.Program Chain

/-- Graphs that can accompany the model state after the level's operations.
Restart keeps the input graph. It may change the branch's sparsifier. -/
inductive SparseCoreInput (tool : SparseCoreTool) (restart : tool.State → ℕ → tool.State)
    (k : ℕ) : tool.State → MGraph → Prop
  | init (M N : ℕ) (G : MGraph) (lengths gradient : ℕ → ℝ) (valid : G.IsValid) :
      SparseCoreInput tool restart k (tool.init k M N G lengths gradient) G
  | update {s : tool.State} {G : MGraph} (input : SparseCoreInput tool restart k s G)
      (U : List Update) (lengths gradient : ℕ → ℝ) (valid : G.BatchIsValid U) :
      SparseCoreInput tool restart k (tool.update s U lengths gradient).1 (G.applyBatch U)
  | restart {s : tool.State} {G : MGraph} (input : SparseCoreInput tool restart k s G)
      (j : ℕ) (branch : j < k) : SparseCoreInput tool restart k (restart s j) G

/-- Count-prefixed table of compact output batches. Each branch has a
pointer and word count, so the caller need not scan other branches. -/
def BranchBatchesAt (mem : ℕ → ℕ) (a k : ℕ) (oldGraphs : ℕ → MGraph)
    (batches : ℕ → List Update) : Prop :=
  mem a = k ∧ ∀ j < k,
    SmallBatchAt mem (mem (a + 1 + 2 * j)) (oldGraphs j) (batches j)
      (mem (a + 2 + 2 * j))

/-- An embedding readout is a pointer to the shared edge-name-indexed
embedding layout. Its domain is the core graph's edges (Definition 5.7,
page 19), rather than just the surviving sparsifier edges. -/
def EmbeddingReadoutAt (mem : ℕ → ℕ) (a eCap : ℕ) (G : MGraph) (forest : LSF)
    (emb : Embedding) : Prop :=
  MEmbAt mem (mem a) (coreGraph G forest).E eCap emb

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open Chain

/-- A restart leaves the level's input graph valid as a history view. -/
theorem SparseCoreInput.after_restart {tool : SparseCoreTool}
    {restart : tool.State → ℕ → tool.State} {k j : ℕ} {s : tool.State} {G : MGraph}
    (hs : SparseCoreInput tool restart k s G) (hj : j < k) :
    SparseCoreInput tool restart k (restart s j) G := .restart hs j hj

/-- The boundary input relation is inhabited for every valid initial graph. -/
theorem sparseCoreInput_init {tool : SparseCoreTool}
    (restart : tool.State → ℕ → tool.State) (k M N : ℕ) (G : MGraph)
    (lengths gradient : ℕ → ℝ) (hG : G.IsValid) :
    SparseCoreInput tool restart k (tool.init k M N G lengths gradient) G :=
  .init M N G lengths gradient hG

/-- Every graph supplied by an operation history is valid. -/
theorem SparseCoreInput.valid {tool : SparseCoreTool}
    {restart : tool.State → ℕ → tool.State} {k : ℕ} {s : tool.State} {G : MGraph}
    (hs : SparseCoreInput tool restart k s G) : G.IsValid := by
  induction hs with
  | init _ _ _ _ _ hG => exact hG
  | update _ _ _ _ hU ih => exact LSF.applyBatch_isValid ih hU
  | restart _ _ _ ih => exact ih

end MinCostFlow.MinRatio
