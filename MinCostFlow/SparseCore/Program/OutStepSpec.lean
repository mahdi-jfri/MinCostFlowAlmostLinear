module

public import MinCostFlow.SparseCore.Program.OutSpec
public import MinCostFlow.SparseCore.Program.OutEditsModel
public import MinCostFlow.SparseCore.Program.OrdStoreCapContract

/-!
# The procedures of piece P7 and what they do

Piece P7 has three procedures. This file states them, for a program `p` that holds
them (`HasOutProcs`) and a tour module that meets the interface `OutTourAt`.

1. **The helper `outSmallSide`** (`sig_outSmallSide_runs`). The assembly calls it right after
   each cut of a core tree (and each split of a core vertex), with the roots `r₁` and `r₂` of the
   two parts. It finds the part with fewer marked ends, by walking the marked ends of both parts
   in turn, so that the walk costs the smaller count. It writes a split record of
   `OutSplitListsAt` and links it after the record `last`. The split of the output graph then
   costs the smaller side, as the encoding size of the output batch asks.
2. **The reset `outReset`** (`sig_outReset_runs`). After a restart of a branch, the output graph
   `S_cur` is a new graph. The reset makes the stored graph equal to the new one, and it makes the
   marked ends of the tour exactly the ends of the new graph.
3. **The output step `outStep`** (`sig_outStep_runs`). One call per branch and update. It reads
   the input record (`OutStepInAt`) and the list `T₀` of the vertices whose lists must be rotated,
   changes the output graph and the marks, and writes the output batch `U_S` and the edits of the
   output order, which are the four words of the branch in `BranchOutAt`.

The rotation list `T₀` must hold every vertex at which the edits of the deletions, splits and
insertions do not already give the new list (`OutRotCover`). Every new root is enough
(`stepBundleTree_outStepEdits_roots`), but its cost is the number of roots.

Only definitions are here.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program

/-- The output order after the edits of the deletions, the splits and the insertions of an
output step, before any `rotateTo` edit. -/
noncomputable def outBaseOrder {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) : ℕ → List End :=
  let st' := (stepBundleTree sparsify st U ord ord').state
  applyOrdEdits (st.outOrder ord)
    (outPrefixEdits (outPrefixBatch sparsify st U ord ord') ++
      outInsertEdits (st'.outOrder ord') st'.S_cur.src (outInsBatch sparsify st U ord ord'))

/-- The list `T₀` holds every vertex at which the edits of the deletions, splits and insertions
do not give the new output list. -/
def OutRotCover {L : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) (T₀ : List ℕ) : Prop :=
  ∀ v, v ∉ T₀ →
    outBaseOrder sparsify st U ord ord' v = (stepBundleTree sparsify st U ord ord').state.outOrder ord' v

/-- The heap space of the helper when the smaller side has at most `k` marked ends: the record,
at most `2 k + 2` tour queries, the list of the tour and its copy. The helper is stated with
`k = 2 eCap`, a bound in fixed sizes. -/
def outSmallSideSpace (S : OutTourSpec) (k : ℕ) : ℕ :=
  (2 * k + 2) * S.querySpace + S.listSpace k + k + 6

/-- The heap space of the reset for `m` edges in all: two mark changes per edge. The reset is
stated with `m = 2 eCap`, a bound in fixed sizes. -/
def outResetSpace (S : OutTourSpec) (m : ℕ) : ℕ :=
  2 * m * S.querySpace + 1

/-- The heap space of an output step, a polynomial in the caps: at most `6 eCap + vCap` tour
queries, and the batch and the edits, each written twice, whose encoding sizes are at most
`2 (vCap + 1) (eCap + 1)` (at most `eCap` deletions and insertions, and at most `vCap` splits,
each of size at most `2 eCap + 1`). -/
def outStepSpace (S : OutTourSpec) (vCap eCap : ℕ) : ℕ :=
  1000 * (vCap + 1) * (eCap + 1) * (S.querySpace + 1)

/-- **The helper `outSmallSide`** `[tourH, r₁, r₂, v, v', last, h]`. The side is `0` when the
list of `r₁` has at most as many marked ends as the list of `r₂`, and `1` otherwise, and `Y` is
the list of marked ends of the chosen root. The helper writes the record
`[v, v', side, ptr, 0]` at `h` and the list `Y` at `ptr`, sets the link word of the record `last`
to `h` (unless `last = 0`), and keeps the tour state. The tour may grow only between the record
and the list, so that later tour calls do not write the record or the list. The cost is the
length of `Y` plus one, times the log factor. -/
def sig_outSmallSide_runs (HasOutProcs : Program → ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    (smallSideIdx : ℕ → ℕ) : Prop :=
  ∃ mul : ℕ, ∀ (S : OutTourSpec) (w vCap eCap : ℕ) (p : Program) (b nm sm fm lm : ℕ),
    HasOutProcs p b nm sm fm lm → (vCap + eCap + 2) ^ 2 < 2 ^ w →
    ∀ (T : OutTourAt S w vCap eCap p nm sm fm lm) (tourH r₁ r₂ v v' last h : ℕ)
      (s : OutTourAbs) (tx : T.rep.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      let side := if (s.markedList r₁).length ≤ (s.markedList r₂).length then 0 else 1
      let Y := s.markedList (if side = 0 then r₁ else r₂)
      (∀ a ∈ [tourH, r₁, r₂, v, v', last, h], a < 2 ^ w) → r₁ < vCap → r₂ < vCap →
      (s.cord r₁).Nodup → (s.cord r₂).Nodup →
      (∀ x ∈ s.markedList r₁ ++ s.markedList r₂, x.1 < eCap) →
      T.rep.rep tourH s tx mem → (∀ a, T.rep.foot tourH tx a → a < h) → 0 < h →
      (last = 0 ∨ (last + 4 < h ∧ ¬ T.rep.foot tourH tx (last + 4))) →
      ZeroFrom mem h → h + outSmallSideSpace S (2 * eCap) < 2 ^ w →
      ∃ body, p.procs[smallSideIdx b]? = some body ∧ ∃ o st' c tx',
        Runs w p ω body (startState [tourH, r₁, r₂, v, v', last, h] mem pos) o st' c ∧
        T.rep.rep tourH s tx' st'.mem ∧
        st'.mem h = v ∧ st'.mem (h + 1) = v' ∧ st'.mem (h + 2) = side ∧ st'.mem (h + 4) = 0 ∧
        EndListAt st'.mem (st'.mem (h + 3)) Y ∧
        Y.length ≤ (s.markedList (if side = 0 then r₂ else r₁)).length ∧
        h + 5 ≤ st'.mem (h + 3) ∧ o.value = st'.mem (h + 3) + 1 + Y.length ∧
        o.value ≤ h + outSmallSideSpace S (2 * eCap) ∧ ZeroFrom st'.mem o.value ∧
        (last ≠ 0 → st'.mem (last + 4) = h) ∧
        (∀ a < h, ¬ T.rep.foot tourH tx a → (last = 0 ∨ a ≠ last + 4) → st'.mem a = mem a) ∧
        (∀ a, T.rep.foot tourH tx' a →
          T.rep.foot tourH tx a ∨ (h + 5 ≤ a ∧ a < st'.mem (h + 3))) ∧
        c + T.rep.phi tourH tx' st'.mem ≤
          mul * (S.mul + 1) * (Y.length + 1) * ordStoreLog eCap + T.rep.phi tourH tx mem

/-- **The reset `outReset`** `[outH, tourH, g₂, h]`. The stored output graph `Sold` becomes the
graph `Snew` held by the `DynGraphAt` at `g₂` (for example the new `S_cur` that piece P10 builds
at a restart), at the same address. The marked ends become the ends of the edges of `Snew`
(`OutMarksOf`), and the lists of the tour do not change. Every end of an edge of either graph
must be in a list of the tour. The cost is the number of edges of both graphs plus one, times
the log factor. -/
def sig_outReset_runs (HasOutProcs : Program → ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    (resetIdx : ℕ → ℕ) : Prop :=
  ∃ mul : ℕ, ∀ (S : OutTourSpec) (w vCap eCap : ℕ) (p : Program) (b nm sm fm lm : ℕ),
    HasOutProcs p b nm sm fm lm → (vCap + eCap + 2) ^ 2 < 2 ^ w →
    ∀ (T : OutTourAt S w vCap eCap p nm sm fm lm) (Sold Snew : MGraph)
      (outH tourH g₂ h g : ℕ) (s : OutTourAbs) (tx : T.rep.τ) (mem : ℕ → ℕ) (pos : ℕ)
      (ω : ℕ → Bool),
      (∀ a ∈ [outH, tourH, g₂, h], a < 2 ^ w) →
      (outGraphRep vCap eCap).rep outH Sold g mem → T.rep.rep tourH s tx mem →
      OutMarksOf s s.cord Sold.E →
      DynGraphAt mem g₂ vCap eCap Snew → Snew.V = Sold.V →
      (∀ e ∈ Sold.E ∪ Snew.E, ∀ t : Bool, ∃ v < vCap, (e, t) ∈ s.cord v) →
      (∀ a, (outGraphRep vCap eCap).foot outH g a → a < h) →
      (∀ a, T.rep.foot tourH tx a → a < h) → g₂ + dynGraphSize vCap eCap ≤ h →
      (∀ a, (outGraphRep vCap eCap).foot outH g a → ¬ T.rep.foot tourH tx a) →
      (∀ a, g₂ ≤ a → a < g₂ + dynGraphSize vCap eCap →
        ¬ (outGraphRep vCap eCap).foot outH g a ∧ ¬ T.rep.foot tourH tx a) →
      ZeroFrom mem h → h + outResetSpace S (2 * eCap) < 2 ^ w →
      ∃ body, p.procs[resetIdx b]? = some body ∧ ∃ o st' c tx' s',
        Runs w p ω body (startState [outH, tourH, g₂, h] mem pos) o st' c ∧
        (outGraphRep vCap eCap).rep outH Snew g st'.mem ∧
        T.rep.rep tourH s' tx' st'.mem ∧ OutMarksOf s' s.cord Snew.E ∧
        h ≤ o.value ∧ o.value ≤ h + outResetSpace S (2 * eCap) ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ (outGraphRep vCap eCap).foot outH g a → ¬ T.rep.foot tourH tx a →
          st'.mem a = mem a) ∧
        (∀ a, T.rep.foot tourH tx' a → T.rep.foot tourH tx a ∨ (h ≤ a ∧ a < o.value)) ∧
        c + T.rep.phi tourH tx' st'.mem ≤
          mul * (S.mul + 1) * (Sold.m + Snew.m + 1) * ordStoreLog eCap + T.rep.phi tourH tx mem

/-- **The output step `outStep`** `[outH, tourH, delPtr, splitPtr, insPtr, rotPtr, h]`. From the
old output graph and the tour with the new core lists and the old output ends marked, the input
record and the list `T₀` (a count, then the vertices, at `rotPtr`), it leaves the new output
graph at the same address and the new marks, and writes at `h` the four words
`[batch, batchWords, edits, editsWords]` of branch `j` of `BranchOutAt`. The edits can be sent
to the order store of the next level: they name vertices below `vCap` and edges below `eCap`,
and after each prefix every end is in at most one list (`OrdEditsWithin` and
`OrdEditsUniqueWithin`, which together are `OrdEditsValidFor` of `AssemblyStatement.lean`). The
batch and the edits lie after all the cells that the tour may take. The cost is the size `n`
(the encoding size of `U_S`, the length of the split lists and of `T₀`, plus one) times the log
factor, and the space is a polynomial in the caps (`outStepSpace`). -/
def sig_outStep_runs (HasOutProcs : Program → ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
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
      OutStepReady sparsify st U ord ord' →
      (∀ v ∈ info.state.cs.RF.R, v < vCap) → (∀ e ∈ info.state.S_cur.E, e < eCap) →
      OutMarksOf s (outCoreOrder info.state ord') st.S_cur.E →
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
          ordEditsEnc edits ≤ 4 * st.S_cur.batchEnc info.U_S + T₀.length ∧
          OrdEditsWithin vCap eCap edits ∧ OrdEditsUniqueWithin vCap eCap (st.outOrder ord) edits) ∧
        h + 4 ≤ st'.mem h ∧ st'.mem h + st'.mem (h + 1) ≤ st'.mem (h + 2) ∧
        st'.mem (h + 2) + st'.mem (h + 3) ≤ o.value ∧
        o.value ≤ h + outStepSpace S vCap eCap ∧ ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ (outGraphRep vCap eCap).foot outH g a → ¬ T.rep.foot tourH tx a →
          st'.mem a = mem a) ∧
        (∀ a, T.rep.foot tourH tx' a → T.rep.foot tourH tx a ∨ (h + 4 ≤ a ∧ a < st'.mem h)) ∧
        c + T.rep.phi tourH tx' st'.mem ≤
          mul * (S.mul + 1) * n * ordStoreLog eCap + T.rep.phi tourH tx mem

end MinCostFlow.SparseCore.Program
