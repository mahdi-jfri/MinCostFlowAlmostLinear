module

public import MinCostFlow.SparseCore.Program.OutTourInterface
public import MinCostFlow.SparseCore.Program.ContractInput
public import MinCostFlow.SparseCore.BundleTool

/-!
# The output step of a branch: the data of piece P7

At each update, every branch of the sparse-core tool changes its output graph `S_cur` by the
batch `U_S = buildUSOrd …` (`stepBundleTree`), and the ordered machine contract asks the program
to write, for each branch, `U_S` and edits from the old output order to the new one
(`BranchOutAt`). The output order at a core vertex is its core rotation list restricted to the
edges of `S_cur` (`BundleTreeState.outOrder`). This file gives the data
that the procedures of piece P7 read and write. Their statements are in `OutStepSpec.lean`.

* **The output graph** is kept as a `DynGraphAt` whose address is stored at a handle
  (`outGraphRep`).
* **Marks.** The tour of piece P2 marks the ends of the output edges (`OutMarksOf`).
* **Input records** of a step (`OutStepInAt`): the leaving edges with a flag that says whether
  they are still edges of the graph after the step (`OutDelAt`), the split lists that the helper
  `outSmallSide` wrote right after each cut (`OutSplitListsAt`), and the entering edges with the
  new roots of their endpoints (`OutInsAt`).
Only definitions, and the locality of `outGraphRep`, are here.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program

/-- The core rotation lists of a branch for the input order `ord`: the list of the tour of each
root (`coreRotation`), and `[]` at every other vertex. The output order `outOrder` is this order
restricted to the edges of `S_cur` (`outOrder_eq_filter`). -/
noncomputable def outCoreOrder {L : ℕ} (st : BundleTreeState L) (ord : ℕ → List End) :
    ℕ → List End :=
  open Classical in
  if h : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (_ : CompLSFInv C_lsst ℓ₀ st.cs) (ρ : Rotation st.cs.G),
      ρ.order = ord then
    let hI := h.choose_spec.choose_spec.choose
    let ρ := h.choose_spec.choose_spec.choose_spec.choose
    (coreRotation (L := st.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)).order
  else fun _ => []

/-- The output order is the core rotation order restricted to the edges of `S_cur`. -/
theorem outOrder_eq_filter {L : ℕ} (st : BundleTreeState L) (ord : ℕ → List End) (v : ℕ) :
    st.outOrder ord v =
      (outCoreOrder st ord v).filter fun x => decide (x.1 ∈ st.S_cur.E) := by
  unfold BundleTreeState.outOrder outCoreOrder
  split <;> simp

/-- The output edges that stay in a step: the edges of the old `S_cur` that are in the new one,
that the input batch does not delete and that are not re-embedded (as in `buildUSOrd`). -/
noncomputable def outKeep {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) : Finset ℕ :=
  let info := stepBundleTree sparsify st U ord ord'
  ((st.S_cur.E ∩ info.state.S_cur.E) \ batchDeletes U) \ info.D_total

/-- The hypotheses of an output step: those under which the output order changes by an ordered
batch (`stepBundleTree_outOrder`). The LSF meets its invariant, the batch is valid and ordered
from `ord` to `ord'`, and the old and new output graphs are valid graphs on the roots that
contain the core graphs. -/
def OutStepReady {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) : Prop :=
  ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ), CompLSFInv C_lsst ℓ₀ st.cs ∧ st.cs.G.BatchIsValid U ∧
    OrderedBatch st.cs.G U ord ord' ∧ st.S_cur.IsValid ∧ st.S_cur.V = st.cs.RF.R ∧
    (coreGraph st.cs.G st.cs.lsf).IsSubgraph st.S_cur ∧
    (coreGraph (compLSFBatch st.cs U).G (compLSFBatch st.cs U).lsf).IsSubgraph
      (stepBundleTree sparsify st U ord ord').state.S_cur

/-- The representation of the output graph of a branch. The word at the handle `outH` is the
address `g` of a `DynGraphAt` of the graph, and the handle lies outside that block. The
representation has no potential. Readout `3` of the contract and piece P10 read the graph at
`mem outH` directly. -/
def outGraphRep (vCap eCap : ℕ) : DSRep MGraph where
  τ := ℕ
  rep outH G g mem := mem outH = g ∧ (outH < g ∨ g + dynGraphSize vCap eCap ≤ outH) ∧
    DynGraphAt mem g vCap eCap G
  phi _ _ _ := 0
  foot outH g a := a = outH ∨ (g ≤ a ∧ a < g + dynGraphSize vCap eCap)

/-- The output graph and its potential depend only on the cells of its footprint. -/
theorem outGraphRep_local (vCap eCap : ℕ) : (outGraphRep vCap eCap).Local := by
  intro outH G g mem mem' hagree
  refine ⟨fun ⟨h1, h2, h3⟩ => ⟨(hagree outH (Or.inl rfl)).symm.trans h1, h2,
    h3.of_agree fun a ha1 ha2 => (hagree a (Or.inr ⟨ha1, ha2⟩)).symm⟩, rfl⟩

/-- The leaving edges of a step at `a`: their count, then for each edge `e` of `delL`, in order,
the pair `[e, flag]`, where `flag` is `1` when `e` is in `E'` (the edges of the graph after the
step) and `0` otherwise. The ends of an edge in `E'` are in the new core lists (so the step can
unmark them); those of an edge not in `E'` are in no new core list. -/
def OutDelAt (mem : ℕ → ℕ) (a : ℕ) (delL : List ℕ) (E' : Finset ℕ) : Prop :=
  mem a = delL.length ∧ ∀ i < delL.length, mem (a + 1 + 2 * i) = delL.getD i 0 ∧
    mem (a + 2 + 2 * i) = if delL.getD i 0 ∈ E' then 1 else 0

/-- The entering edges of a step at `a`: their count, then for each edge `e` of `insL`, in order,
the triple `[e, tl e, hd e]` of the edge and the new roots of its endpoints. -/
def OutInsAt (mem : ℕ → ℕ) (a : ℕ) (insL : List ℕ) (tl hd : ℕ → ℕ) : Prop :=
  mem a = insL.length ∧ ∀ i < insL.length, mem (a + 1 + 3 * i) = insL.getD i 0 ∧
    mem (a + 2 + 3 * i) = tl (insL.getD i 0) ∧ mem (a + 3 + 3 * i) = hd (insL.getD i 0)

/-- The split records of a step, a linked list from the record at `a` (`a = 0` ends the list),
where `P` is the list of restricted core splits and `G` the output graph before the first of
them. A record is five words `[v, v', side, ptr, next]`, below `top` and outside `avoid`, as
the helper `outSmallSide` writes it right after the cut. At `ptr` is a list `Y` of ends
(`EndListAt`), below `top` and outside `avoid`: the marked ends of one of the two sides of the
split. Side `0` is the side that stays at `v`, side `1` the side that moves to `v'`. The list has
no repeats, its ends are ends of edges of `E₀` (the old output graph), and an end of a kept edge
(in `keep`) is in `Y` exactly when it lies at the vertex of its side after the split. -/
def OutSplitListsAt (mem : ℕ → ℕ) (top : ℕ) (avoid : ℕ → Prop) (keep E₀ : Finset ℕ) :
    ℕ → MGraph → List Update → List (List End) → Prop
  | a, _, [], [] => a = 0
  | a, G, .split v v' St Sh :: P, Y :: Ys =>
    0 < a ∧ a + 5 ≤ top ∧ (∀ i < 5, ¬ avoid (a + i)) ∧
      mem a = v ∧ mem (a + 1) = v' ∧ mem (a + 2) ≤ 1 ∧
      EndListAt mem (mem (a + 3)) Y ∧ mem (a + 3) + 1 + Y.length ≤ top ∧
      (∀ i < 1 + Y.length, ¬ avoid (mem (a + 3) + i)) ∧ Y.Nodup ∧ (∀ x ∈ Y, x.1 ∈ E₀) ∧
      (∀ x : End, x.1 ∈ keep →
        (x ∈ Y ↔ (G.applyUpdate (.split v v' St Sh)).src x =
          if mem (a + 2) = 0 then v else v')) ∧
      OutSplitListsAt mem top avoid keep E₀ (mem (a + 4)) (G.applyUpdate (.split v v' St Sh)) P Ys
  | _, _, _, _ => False

/-- The cells from `a` to `a + len` lie below `top` and outside `avoid`. -/
def OutCellsFree (a len top : ℕ) (avoid : ℕ → Prop) : Prop :=
  a + len ≤ top ∧ ∀ i < len, ¬ avoid (a + i)

/-- The input record of an output step, below `top` and outside `avoid`. At `delPtr`: the
leaving edges (the old output edges that are not kept), in increasing order, with their flags
(`OutDelAt`). At `splitPtr`: the first split record (`OutSplitListsAt`, on the output graph
after the deletions), with the split lists `Ys`. At `insPtr`: the entering edges, in increasing
order, with the new roots of their endpoints (`OutInsAt`). -/
def OutStepInAt {L : ℕ} (mem : ℕ → ℕ) (delPtr splitPtr insPtr top : ℕ) (avoid : ℕ → Prop)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (Ys : List (List End)) : Prop :=
  let info := stepBundleTree sparsify st U ord ord'
  let keep := outKeep sparsify st U ord ord'
  let delL := (st.S_cur.E \ keep).sort (· ≤ ·)
  let insL := (info.state.S_cur.E \ keep).sort (· ≤ ·)
  let cs' := info.state.cs
  OutDelAt mem delPtr delL cs'.G.E ∧ OutCellsFree delPtr (1 + 2 * delL.length) top avoid ∧
    OutSplitListsAt mem top avoid keep st.S_cur.E splitPtr
      (st.S_cur.applyBatch (delL.map Update.delete)) (restrictSplits keep info.U_core) Ys ∧
    OutInsAt mem insPtr insL (fun e => cs'.RF.root (cs'.G.tail e))
      (fun e => cs'.RF.root (cs'.G.head e)) ∧
    OutCellsFree insPtr (1 + 3 * insL.length) top avoid

/-- The tour state `s` holds the core lists `cord` and marks exactly the ends of the edges of
`E` that these lists hold. -/
def OutMarksOf (s : OutTourAbs) (cord : ℕ → List End) (E : Finset ℕ) : Prop :=
  s.cord = cord ∧ ∀ z, z ∈ s.marked ↔ (∃ v, z ∈ cord v) ∧ z.1 ∈ E

end MinCostFlow.SparseCore.Program
