module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSpan
public import MinCostFlow.SparseCore.Program.RestartModelState
public import MinCostFlow.SparseCore.Program.SpanBridge
public import MinCostFlow.SparseCore.BundleRunInvBase

/-!
# The spanners of the init and the model (`AssemblyFirstInitSpanModel`)

`asmFirstInitSpan_runs` starts the spanner of each listed slot `s` on the graph of its bundle,
`asmFirstInitSlotGraph S s`. Here we tie this to the model state `tr` of the init. When the table
`S` matches the bundles of `tr` (`BunTableMatches`), the graph of the slot of an active pair `q` is
the start graph `tr.initBunG q` of the pair (`asmFirstInitSlotGraph_slotOf`). So the spanner of
the slot is the spanner of the model (`asmFirstInit_spanMatch`), which is the third clause of
`AsmBrSideModel`. At the init, the model state is `initBundleTreeWithParams`, and its spanners
are the empty histories on their start graphs (`initTree_initBunG`, `initTree_dyn`).

`AsmBrSideModel` also asks `SpanGraphOK` of the graph `restartSlotGraph` of each slot, which
restarts the bundle of the slot. At the init this restart changes nothing, since the bundle is
already `initBundleFor` on its edges (`restartSlotGraph_slotOf`). So both conditions follow from
`SpanGraphOK` of the start graphs of the active pairs (`asmFirstInit_spanGraphOK`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart

public section

variable {L slotCap cap : ℕ} {tr : BundleTreeState L} {slots : List ℕ}
  {slotOf : Finset ℕ × ℤ → ℕ} {S : Fin slotCap → Option BundleState}

/-- The graph of the slot of an active pair `q` is the start graph of `q`, when the table matches
the bundles of the model and each start graph is the normalized graph of its bundle. -/
theorem asmFirstInitSlotGraph_slotOf (hMatch : BunTableMatches tr slotOf S)
    (hG : ∀ q, tr.initBunG q = normGraph (tr.bun q).graph) {q : Finset ℕ × ℤ}
    (hq : q ∈ activePairs tr) :
    asmFirstInitSlotGraph S (slotOf q) = tr.initBunG q := by
  obtain ⟨hs, B, hSB, hag⟩ := hMatch q hq
  unfold asmFirstInitSlotGraph
  rw [slotB_eq hs hSB, hG]
  exact normGraph_of_bunAgree hag

/-- **The spanners of the init match the model.** After `asmFirstInitSpan_runs` on the slot list
of a good slot map, the slot of each active pair `q` holds the empty history on the start graph
of `q`, whose state is the spanner `tr.dyn q` of the model. -/
theorem asmFirstInit_spanMatch (P : DSParams) {tr : BundleTreeState P.L}
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hG : ∀ q, tr.initBunG q = normGraph (tr.bun q).graph)
    (hdyn : ∀ q, tr.dyn q = DSHist.state P ⟨tr.initBunG q, []⟩) :
    ∀ q ∈ activePairs tr, ∃ (hs : slotOf q < cap) (d : DSHist),
      spanAfter (fun _ => none) (asmFirstInitSlotGraph S) slots ⟨slotOf q, hs⟩ = some d ∧
      d.state P = tr.dyn q ∧ d.G₀ = tr.initBunG q ∧
      (∀ u ∈ d.flat, isDelOrSplit u) ∧ d.G₀.BatchIsValid d.flat ∧
      (∀ B ∈ d.Us, B ≠ []) := by
  intro q hq
  have hmem : slotOf q ∈ slots := hMap.2.1 q hq
  have hs : slotOf q < cap := (hMap.2.2.2.2 _ hmem).2
  have hgr := asmFirstInitSlotGraph_slotOf hMatch hG hq
  refine ⟨hs, ⟨tr.initBunG q, []⟩, ?_, (hdyn q).symm, rfl, by simp [DSHist.flat],
    by simp [DSHist.flat, MGraph.BatchIsValid], by simp⟩
  simp [spanAfter, hmem, hgr]

/-- The start graph of a pair at the init is the normalized graph of its bundle. -/
theorem initTree_initBunG (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ)
    (q : Finset ℕ × ℤ) :
    (initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G₀ ℓ₀ ord j).initBunG q =
      normGraph
        ((initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G₀ ℓ₀ ord j).bun
          q).graph :=
  rfl

/-- The spanner of a pair at the init is the state of the empty history on its start graph, for
the spanner parameters `P` with the split bound of the init. -/
theorem initTree_dyn (P : DSParams) (lsfInit : LSFInit) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ)
    (hSB : P.splitBound = bundleSplitBudget k M) (q : Finset ℕ × ℤ) :
    (initBundleTreeWithParams lsfInit P.L (fun _ => canonicalSparsify P.impl) params spanConst
        k M N G₀ ℓ₀ ord j).dyn q =
      DSHist.state P ⟨(initBundleTreeWithParams lsfInit P.L (fun _ => canonicalSparsify P.impl)
        params spanConst k M N G₀ ℓ₀ ord j).initBunG q, []⟩ := by
  rw [dsHist_state_nil, hSB]
  rfl

/-- At the init, the restart of the bundle of the slot of an active pair `q` gives the start
graph of `q`: the bundle is `initBundleFor` on its edges, and `initBundleFor` keeps the edges. -/
theorem restartSlotGraph_slotOf {ord : ℕ → List End} (hMatch : BunTableMatches tr slotOf S)
    (hG : ∀ q, tr.initBunG q = normGraph (tr.bun q).graph)
    (hrot : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (_ : CompLSFInv C_lsst ℓ₀ tr.cs) (ρ : Rotation tr.cs.G),
      ρ.order = ord)
    (hbun : ∀ q ∈ activePairs tr, ∃ E, tr.bun q = initBundleFor tr.cs ord E tr.k)
    {q : Finset ℕ × ℤ} (hq : q ∈ activePairs tr) :
    restartSlotGraph S tr.cs ord tr.k (slotOf q) = tr.initBunG q := by
  obtain ⟨hs, B, hSB, hag⟩ := hMatch q hq
  obtain ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩ := hrot
  obtain ⟨E, hE⟩ := hbun q hq
  unfold restartSlotGraph restartSlotBundle
  simp only [hs, ↓reduceDIte, hSB]
  rw [hag.2.1, hG, hE, initBundleFor_edges hI hρ]
  rfl

/-- **The conditions of the spanner inits at the init.** If the start graph of each active pair
meets `SpanGraphOK`, then so do the graph of each listed slot and the graph of its restart. -/
theorem asmFirstInit_spanGraphOK (P : DSParams) {ord : ℕ → List End}
    (hMap : SlotMapOK tr slotCap cap slots slotOf) (hMatch : BunTableMatches tr slotOf S)
    (hG : ∀ q, tr.initBunG q = normGraph (tr.bun q).graph)
    (hrot : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (_ : CompLSFInv C_lsst ℓ₀ tr.cs) (ρ : Rotation tr.cs.G),
      ρ.order = ord)
    (hbun : ∀ q ∈ activePairs tr, ∃ E, tr.bun q = initBundleFor tr.cs ord E tr.k)
    (hok : ∀ q ∈ activePairs tr, SpanGraphOK P (tr.initBunG q)) :
    ∀ s ∈ slots, SpanGraphOK P (asmFirstInitSlotGraph S s) ∧
      SpanGraphOK P (restartSlotGraph S tr.cs ord tr.k s) := by
  intro s hs
  obtain ⟨q, hq, rfl⟩ := hMap.2.2.1 s hs
  rw [asmFirstInitSlotGraph_slotOf hMatch hG hq, restartSlotGraph_slotOf hMatch hG hrot hbun hq]
  exact ⟨hok q hq, hok q hq⟩

end

end MinCostFlow.SparseCore.Program
