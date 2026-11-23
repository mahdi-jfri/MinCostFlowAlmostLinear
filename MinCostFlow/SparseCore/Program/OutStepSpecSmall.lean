module

public import MinCostFlow.SparseCore.Program.OutEditsValid

/-!
# The output step, restated for the smaller side

This file restates the output step `sig_outStep_runs` of `OutStepSpec.lean` as
`sig_outStepSmall_runs`, the form that the branch uses. The two statements differ in two ways.

* **Where the tour may grow.** The step writes a record of the batch and of the edits between
  tour calls: an insertion needs the answer of `nextMarked` before its edits can be written. A
  tour call needs the heap after its heap pointer to be zero (`ZeroFrom`). So the step reserves
  the batch and the edits right after the four words at `h`, before any tour call, and the tour
  grows after the edits. In the old statement the tour grew before the batch.
* **The edits.** They are the edits `outStepEditsSmall` with each split written by its smaller
  side, so their encoding size is at most `2 · Enc(U_S) + |T₀|` (it was `4 · Enc(U_S) + |T₀|`).

The pre gains one hypothesis, `OutFlagsOk`: the flag of a leaving edge (`1` when it is still an
edge of the graph after the step, `0` otherwise) tells whether its ends are in the new core lists,
so the step knows which ends it can unmark with `setMark`. At entry, the tour marks are those of
some edge set `E₀` between `outKeep` and `st.S_cur.E` (in particular, `st.S_cur.E \ batchDeletes U`
when the tour's `dropEdge` already cleared marks of edges deleted and reinserted by `U`, or
`st.S_cur.E` when no edge was dropped and reinserted).

The model part of the post holds for `outStepEditsSmall` (`outStepEditsSmall_post`): the edits
give the new output order, meet the size bound, and can be sent to the order store.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program

/-- The flags of the leaving edges tell the step which ends are in the new core lists. An end of
an old output edge that is still an edge of the graph after the step (`cs'.G.E`) is in the new
core list of a vertex below `vCap`, so the step can unmark it. An end of an old output edge that
is not an edge of the graph after the step is in no new core list. This is a fact of the model:
the forest only loses edges within one update, so an old output edge (a core edge) is a new core
edge exactly when it is in the new graph, even when the input batch deletes it and inserts it
again. See `outFlagsOk_of` in `OutFlags.lean`. -/
def OutFlagsOk {L : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) (vCap : ℕ) : Prop :=
  ∀ e ∈ st.S_cur.E, ∀ b : Bool,
    (e ∈ (stepBundleTree sparsify st U ord ord').state.cs.G.E →
      ∃ v < vCap, (e, b) ∈ outCoreOrder (stepBundleTree sparsify st U ord ord').state ord' v) ∧
    (e ∉ (stepBundleTree sparsify st U ord ord').state.cs.G.E →
      ∀ v, (e, b) ∉ outCoreOrder (stepBundleTree sparsify st U ord ord').state ord' v)

/-- **The output step `outStep`** `[outH, tourH, delPtr, splitPtr, insPtr, rotPtr, h]`, restated.
The pre is that of `sig_outStep_runs`, with `OutFlagsOk` added. The post differs in two places: the tour grows only after
the edits (`st'.mem (h + 2) + st'.mem (h + 3) ≤ a`), and the edits have encoding size at most
`2 · Enc(U_S) + |T₀|`. -/
def sig_outStepSmall_runs (HasOutProcs : Program → ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    (outStepIdx : ℕ → ℕ) : Prop :=
  ∃ mul : ℕ, ∀ (S : OutTourSpec) (w vCap eCap : ℕ) (p : Program)
    (b nm sm fm lm : ℕ), HasOutProcs p b nm sm fm lm → (vCap + eCap + 2) ^ 2 < 2 ^ w →
    ∀ (T : OutTourAt S w vCap eCap p nm sm fm lm) (L : ℕ)
      (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
      (Ys : List (List End)) (T₀ : List ℕ) (outH tourH delPtr splitPtr insPtr rotPtr h g : ℕ)
      (s : OutTourAbs) (tx : T.rep.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      let info := stepBundleTree sparsify st U ord ord'
      let n := st.S_cur.batchEnc info.U_S + (Ys.map List.length).sum + T₀.length + 1
      let avoid : ℕ → Prop := fun a =>
        (outGraphRep vCap eCap).foot outH g a ∨ T.rep.foot tourH tx a
      OutStepReady sparsify st U ord ord' → OutFlagsOk sparsify st U ord ord' vCap →
      (∀ v ∈ info.state.cs.RF.R, v < vCap) → (∀ e ∈ info.state.S_cur.E, e < eCap) →
      (∃ E₀ : Finset ℕ, outKeep sparsify st U ord ord' ⊆ E₀ ∧ E₀ ⊆ st.S_cur.E ∧
        OutMarksOf s (outCoreOrder info.state ord') E₀) →
      (outGraphRep vCap eCap).rep outH st.S_cur g mem → T.rep.rep tourH s tx mem →
      OutStepInAt mem delPtr splitPtr insPtr h avoid sparsify st U ord ord' Ys →
      mem rotPtr = T₀.length → ListAt mem (rotPtr + 1) T₀ →
      OutCellsFree rotPtr (1 + T₀.length) h avoid → T₀.Nodup → (∀ v ∈ T₀, v < vCap) →
      OutRotCover sparsify st U ord ord' T₀ →
      (∀ a ∈ [outH, tourH, delPtr, splitPtr, insPtr, rotPtr, h], a < 2 ^ w) →
      (∀ a, (outGraphRep vCap eCap).foot outH g a → a < h) →
      (∀ a, T.rep.foot tourH tx a → a < h) →
      (∀ a, (outGraphRep vCap eCap).foot outH g a → ¬ T.rep.foot tourH tx a) →
      ZeroFrom mem h → h + outStepSpace S vCap eCap < 2 ^ w →
      ∃ body, p.procs[outStepIdx b]? = some body ∧ ∃ o st' c tx' s',
        Runs w p ω body
          (startState [outH, tourH, delPtr, splitPtr, insPtr, rotPtr, h] mem pos) o st' c ∧
        (outGraphRep vCap eCap).rep outH info.state.S_cur g st'.mem ∧
        T.rep.rep tourH s' tx' st'.mem ∧
        OutMarksOf s' (outCoreOrder info.state ord') info.state.S_cur.E ∧
        SmallBatchAt st'.mem (st'.mem h) st.S_cur info.U_S (st'.mem (h + 1)) ∧
        (∃ edits : List OrdEdit, OrdEditsAt st'.mem (st'.mem (h + 2)) edits (st'.mem (h + 3)) ∧
          applyOrdEdits (st.outOrder ord) edits = info.state.outOrder ord' ∧
          ordEditsEnc edits ≤ 2 * st.S_cur.batchEnc info.U_S + T₀.length ∧
          OrdEditsWithin vCap eCap edits ∧ OrdEditsUniqueWithin vCap eCap (st.outOrder ord) edits) ∧
        h + 4 ≤ st'.mem h ∧ st'.mem h + st'.mem (h + 1) ≤ st'.mem (h + 2) ∧
        st'.mem (h + 2) + st'.mem (h + 3) ≤ o.value ∧
        o.value ≤ h + outStepSpace S vCap eCap ∧ ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ (outGraphRep vCap eCap).foot outH g a → ¬ T.rep.foot tourH tx a →
          st'.mem a = mem a) ∧
        (∀ a, T.rep.foot tourH tx' a →
          T.rep.foot tourH tx a ∨ (st'.mem (h + 2) + st'.mem (h + 3) ≤ a ∧ a < o.value)) ∧
        c + T.rep.phi tourH tx' st'.mem ≤
          mul * (S.mul + 1) * n * ordStoreLog eCap + T.rep.phi tourH tx mem

variable {L : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)

/-- **The model part of the post of `sig_outStepSmall_runs`** holds for the edits
`outStepEditsSmall`: they give the new output order, their encoding size is at most
`2 · Enc(U_S) + |T₀|`, and they can be sent to the order store. The old output edges are below
`eCap` because the old output graph is stored in a `DynGraphAt` with these caps. -/
theorem outStepEditsSmall_post {vCap eCap : ℕ} (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) (T₀ : List ℕ) (hready : OutStepReady sparsify st U ord ord')
    (hR : ∀ v ∈ (stepBundleTree sparsify st U ord ord').state.cs.RF.R, v < vCap)
    (hE : ∀ e ∈ st.S_cur.E, e < eCap)
    (hE' : ∀ e ∈ (stepBundleTree sparsify st U ord ord').state.S_cur.E, e < eCap)
    (hT : ∀ v ∈ T₀, v < vCap) (hcov : OutRotCover sparsify st U ord ord' T₀) :
    let edits := outStepEditsSmall sparsify st U ord ord' T₀
    applyOrdEdits (st.outOrder ord) edits = (stepBundleTree sparsify st U ord ord').state.outOrder ord' ∧
      ordEditsEnc edits ≤ 2 * st.S_cur.batchEnc (stepBundleTree sparsify st U ord ord').U_S +
        T₀.length ∧
      OrdEditsWithin vCap eCap edits ∧ OrdEditsUniqueWithin vCap eCap (st.outOrder ord) edits :=
  ⟨stepBundleTree_outStepEditsSmall sparsify st U ord ord' hready T₀ hcov,
    ordEditsEnc_outStepEditsSmall_le sparsify st U ord ord' hready T₀,
    outStepEditsSmall_valid sparsify st U ord ord' hready T₀ hR hE hE' hT⟩

end MinCostFlow.SparseCore.Program
