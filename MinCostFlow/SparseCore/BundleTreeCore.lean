module

public import MinCostFlow.SparseCore.BundleOutBatch
public import MinCostFlow.SparseCore.SplitSpanner
public import MinCostFlow.SparseCore.BundleSpanCharge
public import MinCostFlow.DynSpanner.Reemb

/-!
# One branch of the sparse core on bundle graphs

This is the branch state of `sparseCoreTool` with the quotient graphs replaced by bundle graphs. The
old branch splits every core vertex into one quotient vertex per incident piece, so its split count
per update is the maximum degree plus one. That is where the degree bound of
`SparseCoreInstanceHyps.hDeg_bound` enters. Here each pair of a component of the initial graph and a
length bucket keeps a bundle state (`BundleState`). Its bundles are arcs of at most `k` consecutive
ends of the forest tours, so every bundle has degree at most `k`. A batch of the component-wise LSF
moves the bundles by `bundleCompStep`, which makes at most two bundle splits per new root. So the
split budget of each spanner is twice the root budget `⌈56 M / k⌉` and does not depend on any
degree.

The step needs the order of ends at each vertex before and after the batch (the input rotation).
These orders are arguments here. The tool `sparseCoreBundleTool` stores the current order and passes
both (`BundleTool.lean`).

The output batch follows the ordered core batch of the step (`coreBatchOf`, `buildUSOrd`), so
that the output order changes by ordered updates.

Only the definitions and the cost-free structure are in this file. The proofs that replace the
quotient-graph bounds of `SplitSpannerBounds` and `SparseCoreBounds` come later.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.Bundle

/-- The split budget of each bucket spanner in an epoch: two bundle splits for each of at most
`⌈56 M / k⌉` new roots (paper Lemma 5.4, page 18). -/
noncomputable def bundleSplitBudget (k M : ℕ) : ℕ :=
  2 * Nat.ceil (56 * (M : ℝ) / (k : ℝ))

/-- The core edges of a component and a bucket: the edges of the core graph whose tail lies in
the component and whose initial core length falls in the bucket. -/
noncomputable def bucketCoreEdges (C₀ : MGraph) (origB : ℕ → ℤ) (C : Finset ℕ) (b : ℤ) :
    Finset ℕ :=
  open Classical in
  C₀.E.filter fun e => C₀.tail e ∈ C ∧ origB e = b

/-- The initial bundle state of one component and bucket. When the order is the order of a
rotation of the initial graph and the LSF meets its invariant, the bundles cut the tours of the
core rotation into arcs of at most `k` ends (`initBundleState`).
Otherwise the state is empty. -/
noncomputable def initBundleFor (cs : CompLSFState) (ord : ℕ → List End) (E : Finset ℕ)
    (k : ℕ) : BundleState :=
  open Classical in
  if h : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (_ : CompLSFInv C_lsst ℓ₀ cs) (ρ : Rotation cs.G),
      ρ.order = ord then
    let hI := h.choose_spec.choose_spec.choose
    let ρ := h.choose_spec.choose_spec.choose_spec.choose
    initBundleState (coreRotation (L := cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) E k
  else ⟨∅, ∅, fun _ => 0, fun _ => 0⟩

/-- The log factor `(⌊log₂ (M + N + 2)⌋ + 1)²` of the machine cost. It pays for the search trees
of the order store and of the tours (each operation costs one logarithm of their sizes, which are
at most polynomial in `M + N`), and for the limb count of the fixed-point numbers of the LSF. -/
def bundleLogFactor (M N : ℕ) : ℕ := (Nat.log 2 (M + N + 2) + 1) ^ 2

/-- The size `m_C + n_C + 1` of the LSF initialization of each component `C` of `G₀` that has an
edge, summed over these components. A component without edges is a single vertex, whose LSF is
that vertex alone, so it costs no initialization. -/
noncomputable def lsfInitSize (G₀ : MGraph) : ℕ :=
  open Classical in
  ((components G₀).filter fun C => 1 ≤ (compGraph G₀ C).m).sum fun C =>
    (compGraph G₀ C).m + (compGraph G₀ C).n + 1

/-- The size of the LSF batches of one step: each touched component gets its projected batch
(`projCompBatchG`), and each batch costs its length plus one. -/
noncomputable def lsfBatchSize (cs : CompLSFState) (U : List Update) : ℕ :=
  (touchedCompsBatch cs U).sum fun C => (projCompBatchG cs.G (cs.compSt C).G U).length + 1

/-- The state of one branch with bundle graphs. The field `cost` is the cost of the model, and
`machCost` is the cost that pays for the machine program (`stepBundleTree`, `initBundleTree`). -/
structure BundleTreeState (L : ℕ) where
  k : ℕ
  m₀ : ℕ
  n₀ : ℕ
  splitBound : ℕ
  spanParams : SparsifyParams
  spanConst : ℕ
  cs : CompLSFState
  activeComps : Finset (Finset ℕ)
  origBucket : ℕ → ℤ
  activeBuckets : Finset ℕ → Finset ℤ
  lazyInitCost : Finset ℕ → ℕ
  lazyMachInitCost : Finset ℕ → ℕ
  bun : Finset ℕ × ℤ → BundleState
  initBunG : Finset ℕ × ℤ → MGraph
  dyn : Finset ℕ × ℤ → DynSpannerState L
  S_cur : MGraph
  cost : ℕ
  machCost : ℕ

/-- The embedding of the branch. An edge of the sparsified core embeds as itself. A missing core
edge of an active bundle graph uses its path in the spanner of that bundle graph. Bundle edges
keep the core edge names, and the ends of a bundle lie at its parent core vertex, so this path is
also a path of the core graph. Every other edge embeds as the empty path. -/
noncomputable def BundleTreeState.emb {L : ℕ} (st : BundleTreeState L) : Embedding :=
  open Classical in
  fun e =>
    if e ∈ st.S_cur.E then [(e, true)]
    else if h : ∃ p : Finset ℕ × ℤ, p.1 ∈ st.activeComps ∧ p.2 ∈ st.activeBuckets p.1 ∧
        e ∈ (st.bun p).edges then
      piTotal (st.dyn h.choose) e
    else []

/-- Initialize one branch `j < k` on `(G₀, ℓ₀)` using an arbitrary LSF initializer `lsfInit`,
static sparsifier parameter family `params`, and constant factor `spanConst` (used to charge
bucket-spanner initializations and updates in `machCost`), with size upper bounds `(M, N)` and
the order `ord` of ends at each vertex of `G₀`. Each bucket spanner starts on the normalized
bundle graph `normGraph (bun₀ p).graph`. The initial `machCost` pays the graph setup, a read of
the input order on active vertices (`2 * G₀.m + 2 * (activeSubgraph G₀).n + 1`), the LSF
initialization (`lsfInitSize G₀ * bundleLogFactor M N ^ 2`, giving `bundleLogFactor M N ^ 3` with
the outer factor), and the active bucket-spanner initialization bounds, all times
`bundleLogFactor M N`. -/
noncomputable def initBundleTreeWithParams (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) : BundleTreeState L :=
  open Classical in
  let cs₀ := initCompLSFWith lsfInit G₀ ℓ₀ k j
  let C₀ := coreGraph G₀ cs₀.lsf
  let actComps₀ := largeComps k G₀
  let origB : ℕ → ℤ := fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e)
  let actB : Finset ℕ → Finset ℤ := fun C =>
    (C₀.E.filter fun e => C₀.tail e ∈ C).image origB
  let splitB := bundleSplitBudget k M
  let bun₀ : Finset ℕ × ℤ → BundleState := fun p =>
    initBundleFor cs₀ ord (bucketCoreEdges C₀ origB p.1 p.2) k
  let initG : Finset ℕ × ℤ → MGraph := fun p => normGraph (bun₀ p).graph
  let initCB : Finset ℕ × ℤ → InitOut L := fun p =>
    let Hb₀ := initG p
    DynSpanner.init Hb₀ L (phaseBase (Hb₀.n + splitB) L) (sparsify M)
  let lazyC : Finset ℕ → ℕ := fun C => (actB C).sum fun b => (initCB (C, b)).cost
  let lazyMachC : Finset ℕ → ℕ := fun C =>
    (actB C).sum fun b => spanConst * spanInitBound (params M) L splitB (initG (C, b))
  let S₀_E := actComps₀.biUnion fun C => (actB C).biUnion fun b => (initCB (C, b)).state.H.E
  let S₀_cur : MGraph := { V := cs₀.RF.R, E := S₀_E, tail := C₀.tail, head := C₀.head }
  { k := k
    m₀ := M
    n₀ := N
    splitBound := splitB
    spanParams := params M
    spanConst := spanConst
    cs := cs₀
    activeComps := actComps₀
    origBucket := origB
    activeBuckets := actB
    lazyInitCost := lazyC
    lazyMachInitCost := lazyMachC
    bun := bun₀
    initBunG := initG
    dyn := fun p => (initCB p).state
    S_cur := S₀_cur
    cost := G₀.m + (activeSubgraph G₀).n + 1 + actComps₀.sum lazyC
    machCost := (3 * G₀.m + 3 * (activeSubgraph G₀).n + 2 +
      lsfInitSize G₀ * bundleLogFactor M N ^ 2 + actComps₀.sum lazyMachC) * bundleLogFactor M N }

/-- Initialize one branch `j < k` on `(G₀, ℓ₀)` using an arbitrary LSF initializer `lsfInit`,
with size upper bounds `(M, N)` and the order `ord` of ends at each vertex of `G₀`. -/
noncomputable def initBundleTreeWith (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) : BundleTreeState L :=
  initBundleTreeWithParams lsfInit L sparsify (fun _ => defaultSparsifyParams) 1 k M N G₀ ℓ₀ ord j

/-- Initialize one branch `j < k` on `(G₀, ℓ₀)` with size upper bounds `(M, N)` and the order
`ord` of ends at each vertex of `G₀`. -/
noncomputable def initBundleTree
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) : BundleTreeState L :=
  initBundleTreeWith (initLSFOnline oracle C_lsst) L sparsify k M N G₀ ℓ₀ ord j

/-- Step data of one branch: the new state, the batch of the sparsified core, the core batch it
follows, and the bundle and spanner outputs for the proofs. -/
structure BundleTreeStepInfo (L : ℕ) where
  state : BundleTreeState L
  U_S : List Update
  U_core : List Update
  U_B : Finset ℕ × ℤ → List Update
  stepOut : Finset ℕ × ℤ → StepOut L
  newlyActive : Finset (Finset ℕ)
  D_total : Finset ℕ

/-- Update one branch on the batch `U`, given the orders `ord` before and `ord'` after the batch.
The bundles move by `bundleCompStep`. Each bucket spanner gets the bundle batch. The sparsified
core keeps the spanner edges, the non-forest edges of the components outside the bundle graphs,
and the cross edges, and it reinserts the edges whose embedding changed (paper page 24, line 425
of the source). Its splits are those of the ordered core batch `coreBatchOf` restricted to the
kept edges (`buildUSOrd`). -/
noncomputable def stepBundleTree {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    BundleTreeStepInfo L :=
  open Classical in
  let touched := touchedCompsBatch st.cs U
  let newlyActive := touched \ st.activeComps
  let active' := st.activeComps ∪ newlyActive
  let cs' := compLSFBatch st.cs U
  let bs : Finset ℕ × ℤ → List Update × BundleState := fun p =>
    bundleCompStep st.cs (st.bun p) st.k ord ord' U
  let spOut : Finset ℕ × ℤ → StepOut L := fun p =>
    DynSpanner.update (st.dyn p) (bs p).1 (sparsify st.m₀)
  let dynUnionE' := active'.biUnion fun C =>
    (st.activeBuckets C).biUnion fun b => (spOut (C, b)).state.H.E
  let bunE' := active'.biUnion fun C =>
    (st.activeBuckets C).biUnion fun b => (bs (C, b)).2.edges
  let extraComps' := active'.biUnion fun C =>
    ((cs'.compSt C).G.E \ (cs'.compSt C).RF.F.E) \ bunE'
  let targetE' := dynUnionE' ∪ extraComps' ∪ cs'.crossEdges
  let D_sp := active'.biUnion fun C =>
    (st.activeBuckets C).biUnion fun b => (spOut (C, b)).D
  let D_left := active'.biUnion fun C =>
    (st.activeBuckets C).biUnion fun b =>
      (((st.dyn (C, b)).H.E ∩ (spOut (C, b)).state.G.E) \ (spOut (C, b)).state.H.E).biUnion
        fun e => walkEdges (piTotal (spOut (C, b)).state e)
  let D_tot := D_sp ∪ D_left
  let UC := coreBatchOf st.cs ord ord' U
  let U_S := buildUSOrd UC U cs' st.S_cur targetE' D_tot
  let dynCost := active'.sum fun C =>
    (st.activeBuckets C).sum fun b => (spOut (C, b)).cost
  let lazyCost := newlyActive.sum fun C => st.lazyInitCost C
  let bunCost := active'.sum fun C => (st.activeBuckets C).sum fun b => (bs (C, b)).1.length
  let cStep := U.length + bunCost + U_S.length + dynCost + lazyCost
  let bunEnc := active'.sum fun C =>
    (st.activeBuckets C).sum fun b => (st.dyn (C, b)).G.batchEnc (bs (C, b)).1
  let dynMachCost := active'.sum fun C =>
    (st.activeBuckets C).sum fun b =>
      spanBatchChargeWith st.spanConst st.spanParams L ((st.initBunG (C, b)).n + st.splitBound)
        (st.initBunG (C, b)) (st.dyn (C, b)).G (bs (C, b)).1
  let lazyMachCost := newlyActive.sum fun C => st.lazyMachInitCost C
  let machStep := (U.length + bunEnc + st.S_cur.batchEnc U_S + dynMachCost +
    lsfBatchSize st.cs U + lazyMachCost) * bundleLogFactor st.m₀ st.n₀
  { state :=
      { st with
        cs := cs'
        activeComps := active'
        bun := fun p => (bs p).2
        dyn := fun p => (spOut p).state
        S_cur := st.S_cur.applyBatch U_S
        cost := st.cost + cStep
        machCost := st.machCost + machStep }
    U_S := U_S
    U_core := UC
    U_B := fun p => (bs p).1
    stepOut := spOut
    newlyActive := newlyActive
    D_total := D_tot }

/-- The bundle batch of each bucket meets the specification of `bundleCompStep` on ordered input:
at most two splits per new root and at most one deletion per update, with no degree term. -/
theorem stepBundleTree_bundleSpec {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (p : Finset ℕ × ℤ) (h : BundleStepReady st.cs (st.bun p) st.k ord ord' U) :
    BundleStepSpec st.cs (st.bun p) st.k ord' U ((stepBundleTree sparsify st U ord ord').U_B p)
      ((stepBundleTree sparsify st U ord ord').state.bun p) :=
  bundleCompStep_spec h

/-- The cost of a step splits into the input length, the bundle batches, the output batch, the
spanner updates and the lazy initializations. -/
theorem stepBundleTree_cost {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    let info := stepBundleTree sparsify st U ord ord'
    let active' := info.state.activeComps
    info.state.cost = st.cost + (U.length +
      (active'.sum fun C => (st.activeBuckets C).sum fun b => (info.U_B (C, b)).length) +
      info.U_S.length +
      (active'.sum fun C => (st.activeBuckets C).sum fun b => (info.stepOut (C, b)).cost) +
      info.newlyActive.sum fun C => st.lazyInitCost C) :=
  rfl

/-- The machine cost of a step: the input length, the encodings of the bundle batches (on the
graphs of the bucket spanners) and of the output batch, the spanner update charge
(`spanBatchCharge`), the LSF batches, and the lazy initialization bounds (`lazyMachInitCost`),
all times the log factor `bundleLogFactor`. -/
theorem stepBundleTree_machCost {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    let info := stepBundleTree sparsify st U ord ord'
    let active' := info.state.activeComps
    info.state.machCost = st.machCost + (U.length +
      (active'.sum fun C => (st.activeBuckets C).sum fun b =>
        (st.dyn (C, b)).G.batchEnc (info.U_B (C, b))) +
      st.S_cur.batchEnc info.U_S +
      (active'.sum fun C => (st.activeBuckets C).sum fun b =>
        spanBatchChargeWith st.spanConst st.spanParams L ((st.initBunG (C, b)).n + st.splitBound)
          (st.initBunG (C, b)) (st.dyn (C, b)).G (info.U_B (C, b))) +
      lsfBatchSize st.cs U +
      info.newlyActive.sum fun C => st.lazyMachInitCost C) * bundleLogFactor st.m₀ st.n₀ :=
  rfl

/-- The initial machine cost of one branch carries the outer factor `bundleLogFactor M N` and
includes both graph setup and the active-vertex order-read budget
`2 * G₀.m + 2 * (activeSubgraph G₀).n + 1`. -/
theorem initBundleTreeWithParams_machCost (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ)
    (ord : ℕ → List End) (j : ℕ) :
    let st₀ := initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G₀ ℓ₀ ord j
    st₀.machCost = (3 * G₀.m + 3 * (activeSubgraph G₀).n + 2 +
      lsfInitSize G₀ * bundleLogFactor M N ^ 2 +
      st₀.activeComps.sum st₀.lazyMachInitCost) * bundleLogFactor M N :=
  rfl

/-! ## Per-branch list of edges whose embedding can change in `stepBundleTree` -/

/-- Set of edges of a branch whose `BundleTreeState.emb` can change during `stepBundleTree`:
1. all edges of newly lazily activated components (`C ∈ newlyActive`, `b ∈ activeBuckets C`);
2. all edges re-embedded by active bucket spanners (`DynSpanner.updateReembSet` for
   `C ∈ active'`, `b ∈ activeBuckets C`);
3. edges deleted from `S_cur` in `U_S` (which switch from self-embedding `[(e, true)]` to their
   bundle-spanner embedding). -/
noncomputable def stepBundleTree_reembSet {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) : Finset ℕ :=
  open Classical in
  let info := stepBundleTree sparsify st U ord ord'
  let active' := info.state.activeComps
  let fromLazy := info.newlyActive.biUnion fun C =>
    (st.activeBuckets C).biUnion fun b => (st.bun (C, b)).edges
  let fromDyn := active'.biUnion fun C =>
    (st.activeBuckets C).biUnion fun b =>
      DynSpanner.updateReembSet (st.dyn (C, b)) (info.U_B (C, b)) (sparsify st.m₀)
  let fromDelS := (info.U_S.filterMap fun u => match u with
    | .delete e => some e
    | _ => none).toFinset
  fromLazy ∪ fromDyn ∪ fromDelS

/-- Sorted duplicate-free list of `stepBundleTree_reembSet`: the edges of one branch whose
embedding `stepBundleTree` can change. -/
noncomputable def stepBundleTree_reembList {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) : List ℕ :=
  (stepBundleTree_reembSet sparsify st U ord ord').sort (· ≤ ·)

theorem stepBundleTree_reembList_nodup {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    (stepBundleTree_reembList sparsify st U ord ord').Nodup :=
  (stepBundleTree_reembSet sparsify st U ord ord').sort_nodup (· ≤ ·)

theorem mem_stepBundleTree_reembList {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) (e : ℕ) :
    e ∈ stepBundleTree_reembList sparsify st U ord ord' ↔
      e ∈ stepBundleTree_reembSet sparsify st U ord ord' :=
  Finset.mem_sort (· ≤ ·)

theorem stepBundleTree_reembList_toFinset {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    (stepBundleTree_reembList sparsify st U ord ord').toFinset =
      stepBundleTree_reembSet sparsify st U ord ord' := by
  ext e
  simp [mem_stepBundleTree_reembList]

theorem stepBundleTree_reembList_length {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    (stepBundleTree_reembList sparsify st U ord ord').length =
      (stepBundleTree_reembSet sparsify st U ord ord').card :=
  Finset.length_sort (· ≤ ·)

/-- At initialization `initBundleTreeWith`, every component's lazy initialization cost pays for
all edges in its bucket bundle graphs. -/
theorem initBundleTreeWith_edges_le_lazyInitCost (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) (C : Finset ℕ) :
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j
    ((st₀.activeBuckets C).sum fun b => (st₀.bun (C, b)).edges.card) ≤ st₀.lazyInitCost C := by
  intro st₀
  refine Finset.sum_le_sum fun b _ => ?_
  exact DynSpanner.m_le_init_cost (normGraph (st₀.bun (C, b)).graph) L
    (phaseBase ((normGraph (st₀.bun (C, b)).graph).n + bundleSplitBudget k M) L) (sparsify M)

/-- **Length bound for `stepBundleTree_reembList`.** Whenever the lazy initialization cost of each
newly activated component covers the edges of its initial bucket bundle graphs (which holds along
every run by `initBundleTreeWith_edges_le_lazyInitCost`), the length of `stepBundleTree_reembList`
is at most the step cost `info.state.cost - st.cost`. -/
theorem stepBundleTree_reembList_length_le_cost {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (hLazy : ∀ C ∈ (stepBundleTree sparsify st U ord ord').newlyActive,
      ((st.activeBuckets C).sum fun b => (st.bun (C, b)).edges.card) ≤ st.lazyInitCost C) :
    st.cost + (stepBundleTree_reembList sparsify st U ord ord').length ≤
      (stepBundleTree sparsify st U ord ord').state.cost := by
  classical
  rw [stepBundleTree_reembList_length, stepBundleTree_cost]
  set info := stepBundleTree sparsify st U ord ord'
  set active' := info.state.activeComps
  set fromLazy := info.newlyActive.biUnion fun C =>
    (st.activeBuckets C).biUnion fun b => (st.bun (C, b)).edges
  set fromDyn := active'.biUnion fun C =>
    (st.activeBuckets C).biUnion fun b =>
      DynSpanner.updateReembSet (st.dyn (C, b)) (info.U_B (C, b)) (sparsify st.m₀)
  set delList := info.U_S.filterMap fun u => match u with
    | .delete e => some e
    | _ => none
  have hcard_un : (stepBundleTree_reembSet sparsify st U ord ord').card ≤
      fromLazy.card + fromDyn.card + delList.toFinset.card := by
    unfold stepBundleTree_reembSet
    calc _ ≤ (fromLazy ∪ fromDyn).card + delList.toFinset.card := Finset.card_union_le _ _
      _ ≤ fromLazy.card + fromDyn.card + delList.toFinset.card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hLazy_card : fromLazy.card ≤ info.newlyActive.sum fun C => st.lazyInitCost C := by
    calc fromLazy.card
        ≤ info.newlyActive.sum fun C =>
            ((st.activeBuckets C).biUnion fun b => (st.bun (C, b)).edges).card :=
          Finset.card_biUnion_le
      _ ≤ info.newlyActive.sum fun C =>
            (st.activeBuckets C).sum fun b => (st.bun (C, b)).edges.card :=
          Finset.sum_le_sum fun C _ => Finset.card_biUnion_le
      _ ≤ info.newlyActive.sum fun C => st.lazyInitCost C :=
          Finset.sum_le_sum hLazy
  have hDyn_card : fromDyn.card ≤
      active'.sum fun C => (st.activeBuckets C).sum fun b => (info.stepOut (C, b)).cost := by
    calc fromDyn.card
        ≤ active'.sum fun C =>
            ((st.activeBuckets C).biUnion fun b =>
              DynSpanner.updateReembSet (st.dyn (C, b)) (info.U_B (C, b)) (sparsify st.m₀)).card :=
          Finset.card_biUnion_le
      _ ≤ active'.sum fun C =>
            (st.activeBuckets C).sum fun b =>
              (DynSpanner.updateReembSet (st.dyn (C, b)) (info.U_B (C, b)) (sparsify st.m₀)).card :=
          Finset.sum_le_sum fun C _ => Finset.card_biUnion_le
      _ ≤ active'.sum fun C =>
            (st.activeBuckets C).sum fun b => (info.stepOut (C, b)).cost :=
          Finset.sum_le_sum fun C _ => Finset.sum_le_sum fun b _ =>
            DynSpanner.card_updateReembSet_le_cost (st.dyn (C, b)) (info.U_B (C, b))
              (sparsify st.m₀)
  have hDel_card : delList.toFinset.card ≤ info.U_S.length :=
    (List.toFinset_card_le delList).trans (List.length_filterMap_le _ _)
  omega

private theorem exists_delete_of_mem_sdiff_applyBatch' :
    ∀ (G : MGraph) (U : List Update) {e : ℕ}, e ∈ G.E → e ∉ (G.applyBatch U).E →
      Update.delete e ∈ U
  | _, [], _, he, hne => by simp [MGraph.applyBatch] at hne; exact absurd he hne
  | G, u :: rest, e, he, hne => by
    by_cases hd : u = Update.delete e
    · subst hd; exact List.mem_cons_self
    refine List.mem_cons_of_mem _
      (exists_delete_of_mem_sdiff_applyBatch' (G.applyUpdate u) rest ?_ hne)
    rcases u with ⟨e', a, b⟩ | e' | ⟨v, v', St, Sh⟩
    · exact Finset.mem_insert_of_mem he
    · exact Finset.mem_erase.mpr ⟨fun h => hd (by rw [h]), he⟩
    · exact he

/-- **Coverage of `stepBundleTree_reembList`.** Every surviving off-spanner edge `e ∉ st'.S_cur.E`
whose branch embedding changed (`st'.emb e ≠ st.emb e`) belongs to
`stepBundleTree_reembList sparsify st U ord ord'`. -/
theorem mem_stepBundleTree_reembList_of_emb_ne {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) {e : ℕ}
    (hOff' : e ∉ (stepBundleTree sparsify st U ord ord').state.S_cur.E)
    (hNe : (stepBundleTree sparsify st U ord ord').state.emb e ≠ st.emb e)
    (hBunSub : ∀ p : Finset ℕ × ℤ,
      ((stepBundleTree sparsify st U ord ord').state.bun p).edges ⊆ (st.bun p).edges)
    (hSurv : ∀ p : Finset ℕ × ℤ, p.1 ∈ st.activeComps → p.2 ∈ st.activeBuckets p.1 →
      e ∈ (st.bun p).edges → e ∈ ((stepBundleTree sparsify st U ord ord').state.bun p).edges)
    (hDisj : ∀ p₁ p₂ : Finset ℕ × ℤ,
      p₁.1 ∈ st.activeComps → p₁.2 ∈ st.activeBuckets p₁.1 →
      p₂.1 ∈ st.activeComps → p₂.2 ∈ st.activeBuckets p₂.1 →
      e ∈ (st.bun p₁).edges → e ∈ (st.bun p₂).edges → p₁ = p₂)
    (hDynG : ∀ p : Finset ℕ × ℤ, p.1 ∈ st.activeComps → p.2 ∈ st.activeBuckets p.1 →
      ((stepBundleTree sparsify st U ord ord').stepOut p).state.G.E =
        ((stepBundleTree sparsify st U ord ord').state.bun p).edges)
    (hDynCov : ∀ p : Finset ℕ × ℤ, p.1 ∈ st.activeComps → p.2 ∈ st.activeBuckets p.1 →
      e ∈ ((stepBundleTree sparsify st U ord ord').stepOut p).state.G.E →
      piTotal ((stepBundleTree sparsify st U ord ord').stepOut p).state e ≠ piTotal (st.dyn p) e →
      e ∈ DynSpanner.updateReembSet (st.dyn p)
        ((stepBundleTree sparsify st U ord ord').U_B p) (sparsify st.m₀)) :
    e ∈ stepBundleTree_reembList sparsify st U ord ord' := by
  classical
  rw [mem_stepBundleTree_reembList]
  set info := stepBundleTree sparsify st U ord ord'
  set st' := info.state
  unfold stepBundleTree_reembSet
  by_cases hInOld : e ∈ st.S_cur.E
  · -- Edge left `S_cur`, so `.delete e ∈ info.U_S`.
    have hdel : Update.delete e ∈ info.U_S :=
      exists_delete_of_mem_sdiff_applyBatch' st.S_cur info.U_S hInOld hOff'
    refine Finset.mem_union_right _ ?_
    rw [List.mem_toFinset, List.mem_filterMap]
    exact ⟨Update.delete e, hdel, rfl⟩
  · -- `e ∉ st.S_cur.E` and `e ∉ st'.S_cur.E`.
    have hemb : st.emb e =
        if h : ∃ p : Finset ℕ × ℤ, p.1 ∈ st.activeComps ∧ p.2 ∈ st.activeBuckets p.1 ∧
            e ∈ (st.bun p).edges then
          piTotal (st.dyn h.choose) e
        else [] := by
      unfold BundleTreeState.emb
      simp [hInOld]
    have hemb' : st'.emb e =
        if h : ∃ p : Finset ℕ × ℤ, p.1 ∈ st'.activeComps ∧ p.2 ∈ st'.activeBuckets p.1 ∧
            e ∈ (st'.bun p).edges then
          piTotal (st'.dyn h.choose) e
        else [] := by
      unfold BundleTreeState.emb
      simp [hOff']
    rw [hemb, hemb'] at hNe
    by_cases h' : ∃ p : Finset ℕ × ℤ, p.1 ∈ st'.activeComps ∧ p.2 ∈ st'.activeBuckets p.1 ∧
        e ∈ (st'.bun p).edges
    · set p := h'.choose
      have hp : p.1 ∈ st'.activeComps ∧ p.2 ∈ st'.activeBuckets p.1 ∧ e ∈ (st'.bun p).edges :=
        h'.choose_spec
      have hpB : p.2 ∈ st.activeBuckets p.1 := hp.2.1
      have hpOld : e ∈ (st.bun p).edges := hBunSub p hp.2.2
      by_cases hNew : p.1 ∈ info.newlyActive
      · -- Lazy activation of `p.1`.
        refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
        refine Finset.mem_biUnion.mpr ⟨p.1, hNew, Finset.mem_biUnion.mpr ⟨p.2, hpB, hpOld⟩⟩
      · -- Already active component `p.1 ∈ st.activeComps`.
        have hpAct : p.1 ∈ st.activeComps := by
          have hmem : p.1 ∈ st.activeComps ∪ info.newlyActive := hp.1
          exact (Finset.mem_union.mp hmem).resolve_right hNew
        have h : ∃ q : Finset ℕ × ℤ, q.1 ∈ st.activeComps ∧ q.2 ∈ st.activeBuckets q.1 ∧
            e ∈ (st.bun q).edges := ⟨p, hpAct, hpB, hpOld⟩
        have hch_eq : h.choose = p :=
          hDisj h.choose p h.choose_spec.1 h.choose_spec.2.1 hpAct hpB h.choose_spec.2.2 hpOld
        simp only [h', h, ↓reduceDIte] at hNe
        rw [hch_eq] at hNe
        have hdyn_eq : st'.dyn p = (info.stepOut p).state := rfl
        rw [hdyn_eq] at hNe
        have heG : e ∈ (info.stepOut p).state.G.E := (hDynG p hpAct hpB).symm ▸ hp.2.2
        have hmem_dyn := hDynCov p hpAct hpB heG hNe
        refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        exact Finset.mem_biUnion.mpr ⟨p.1, hp.1, Finset.mem_biUnion.mpr ⟨p.2, hpB, hmem_dyn⟩⟩
    · -- `¬ h'`: then `h` cannot hold either by `hSurv`, contradicting `hNe`.
      have hnot : ¬ ∃ q : Finset ℕ × ℤ, q.1 ∈ st.activeComps ∧ q.2 ∈ st.activeBuckets q.1 ∧
          e ∈ (st.bun q).edges := by
        rintro ⟨q, hq1, hq2, hq3⟩
        exact h' ⟨q, Finset.mem_union_left _ hq1, hq2, hSurv q hq1 hq2 hq3⟩
      simp only [h', hnot, ↓reduceDIte] at hNe
      exact (hNe rfl).elim

end MinCostFlow.SparseCore
