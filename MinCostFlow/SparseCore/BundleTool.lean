module

public import MinCostFlow.SparseCore.BundleRun
public import MinCostFlow.Chain.SparseCoreToolOrd

/-!
# The sparse core tool on bundle graphs

`sparseCoreBundleTool` is the tool of Lemma 5.17 with the bundle repair (see the README, 'Where the
proof departs from the paper'): each branch is a
`BundleTreeState`, so the spanners run on bundle graphs. The tool uses
the orders of `SparseCoreTool`. Its state stores the order of ends of the current input graph.
`updateOrd` passes the stored order and the new order to the step of every branch, and then
stores the new order. `rot` returns, for each branch, the tours of the core graph restricted to
the edges of the output graph.

Without orders, `init` and `update` use the sorted orders (`sortedEnds`). These are the orders
used for a graph that has no vertex splits.

The run of the tool with orders is the run of its branches (`sparseCoreBundleTool_runOrdAt`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.Bundle

/-- The state of `sparseCoreBundleTool`: the branches and the order of ends of the current input
graph. -/
structure SparseCoreBundleState (L : ℕ) where
  isNonempty : Bool
  k : ℕ
  ord : ℕ → List End
  trees : ℕ → BundleTreeState L

/-- The order of ends at each vertex of the output graph of a branch: the core rotation of the
input order, restricted to the output edges. It is empty when the
order is not a rotation of the input graph or the LSF does not meet its invariant. -/
noncomputable def BundleTreeState.outOrder {L : ℕ} (st : BundleTreeState L)
    (ord : ℕ → List End) : ℕ → List End :=
  open Classical in
  if h : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (_ : CompLSFInv C_lsst ℓ₀ st.cs) (ρ : Rotation st.cs.G),
      ρ.order = ord then
    let hI := h.choose_spec.choose_spec.choose
    let ρ := h.choose_spec.choose_spec.choose_spec.choose
    fun v => ((coreRotation (L := st.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)).order v).filter
      fun x => decide (x.1 ∈ st.S_cur.E)
  else fun _ => []

/-- Initialize all branches with the order `ord` of ends of `G₀` using an arbitrary LSF
initializer `lsfInit`, static sparsifier parameter family `params`, and constant factor
`spanConst`. -/
noncomputable def initBundleCoreWithParams (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) : SparseCoreBundleState L :=
  open Classical in
  { isNonempty := decide G₀.V.Nonempty
    k := k
    ord := ord
    trees := fun j => initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G₀ ℓ₀ ord j }

/-- Initialize all branches with the order `ord` of ends of `G₀` using an arbitrary LSF
initializer `lsfInit`. -/
noncomputable def initBundleCoreWith (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) : SparseCoreBundleState L :=
  initBundleCoreWithParams lsfInit L sparsify (fun _ => defaultSparsifyParams) 1 k M N G₀ ℓ₀ ord

/-- Initialize all branches with the order `ord` of ends of `G₀`. -/
noncomputable def initBundleCore
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) : SparseCoreBundleState L :=
  initBundleCoreWith (initLSFOnline oracle C_lsst) L sparsify k M N G₀ ℓ₀ ord

/-- Update all branches on the batch `U`, given the order `ord'` after the batch. -/
noncomputable def updateBundleCore {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreBundleState L) (U : List Update) (ord' : ℕ → List End) :
    SparseCoreBundleState L × (ℕ → List Update) :=
  if st.isNonempty then
    let res := fun j => stepBundleTree sparsify (st.trees j) U st.ord ord'
    ({ st with ord := ord', trees := fun j => (res j).state }, fun j => (res j).U_S)
  else
    (st, fun _ => [])

theorem updateBundleCore_of_nonempty {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : SparseCoreBundleState L} (h : st.isNonempty = true) (U : List Update)
    (ord' : ℕ → List End) :
    updateBundleCore sparsify st U ord' =
      ({ st with ord := ord', trees := fun j => (stepBundleTree sparsify (st.trees j) U st.ord ord').state },
        fun j => (stepBundleTree sparsify (st.trees j) U st.ord ord').U_S) := by
  simp only [updateBundleCore, h, ↓reduceIte]

/-- The tool of Lemma 5.17 on bundle graphs with an arbitrary LSF initializer `lsfInit`. -/
noncomputable def sparseCoreBundleToolWith (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) : SparseCoreTool where
  State := SparseCoreBundleState L
  init k M N G₀ ℓ₀ _g₀ := initBundleCoreWith lsfInit L sparsify k M N G₀ ℓ₀ (sortedEnds G₀)
  update st U _ℓ _g :=
    updateBundleCore sparsify st U (sortedEnds ((st.trees 0).cs.G.applyBatch U))
  lsfs st j := if st.isNonempty then (st.trees j).cs.lsf else emptyLSF
  S st j := if st.isNonempty then (st.trees j).S_cur else emptyGraph
  emb st j := if st.isNonempty then (st.trees j).emb else fun _ => []
  cost st := if st.isNonempty then (Finset.range st.k).sum fun j => (st.trees j).cost else 0
  initOrd k M N G₀ ℓ₀ _g₀ ord := initBundleCoreWith lsfInit L sparsify k M N G₀ ℓ₀ ord
  updateOrd st U _ℓ _g ord' := updateBundleCore sparsify st U ord'
  rot st j := if st.isNonempty then (st.trees j).outOrder st.ord else fun _ => []

/-- The tool of Lemma 5.17 on bundle graphs. -/
noncomputable def sparseCoreBundleTool
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) : SparseCoreTool :=
  sparseCoreBundleToolWith (initLSFOnline oracle C_lsst) L sparsify

/-- On a nonempty initial graph, the run of `sparseCoreBundleToolWith` with orders is the run of
its branches. -/
theorem sparseCoreBundleToolWith_runOrdAt (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (hV₀ : (D.G 0).V.Nonempty) :
    ∀ t,
      let r := (sparseCoreBundleToolWith lsfInit L sparsify).runOrdAt k M N D ord t
      r.1.isNonempty = true ∧ r.1.k = k ∧ r.1.ord = ord t ∧
      (∀ j, r.1.trees j = (bundleRunSeqWith lsfInit L sparsify k M N D ord j t).1) ∧
      (1 ≤ t → ∀ j, r.2 j = (bundleRunSeqWith lsfInit L sparsify k M N D ord j t).2) := by
  intro t
  induction t with
  | zero =>
    refine ⟨by simp [SparseCoreTool.runOrdAt, sparseCoreBundleToolWith, initBundleCoreWith,
      initBundleCoreWithParams, hV₀],
      rfl, rfl, fun _ => rfl, fun h => absurd h (by omega)⟩
  | succ s ih =>
    obtain ⟨hne, hk, hord, htr, -⟩ := ih
    have key : ∀ x : SparseCoreBundleState L, x.isNonempty = true → x.k = k → x.ord = ord s →
        (∀ j, x.trees j = (bundleRunSeqWith lsfInit L sparsify k M N D ord j s).1) →
        let r := updateBundleCore sparsify x (D.U (s + 1)) (ord (s + 1))
        r.1.isNonempty = true ∧ r.1.k = k ∧ r.1.ord = ord (s + 1) ∧
        (∀ j, r.1.trees j = (bundleRunSeqWith lsfInit L sparsify k M N D ord j (s + 1)).1) ∧
        (1 ≤ s + 1 → ∀ j, r.2 j = (bundleRunSeqWith lsfInit L sparsify k M N D ord j (s + 1)).2) := by
      intro x hx hxk hxo hxt
      rw [updateBundleCore_of_nonempty hx]
      exact ⟨hx, hxk, rfl, fun j => by dsimp only; rw [hxt j, hxo]; rfl,
        fun _ j => by dsimp only; rw [hxt j, hxo]; rfl⟩
    exact key _ hne hk hord htr

/-- On a nonempty initial graph, the run of the tool with orders is the run of its branches:
the state stores the current order and the branch states, and it emits the branch batches. -/
theorem sparseCoreBundleTool_runOrdAt
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (hV₀ : (D.G 0).V.Nonempty) :
    ∀ t,
      let r := (sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t
      r.1.isNonempty = true ∧ r.1.k = k ∧ r.1.ord = ord t ∧
      (∀ j, r.1.trees j = (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1) ∧
      (1 ≤ t → ∀ j, r.2 j = (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).2) :=
  sparseCoreBundleToolWith_runOrdAt (initLSFOnline oracle C_lsst) L sparsify k M N D ord hV₀

end MinCostFlow.SparseCore
