module

public import MinCostFlow.SparseCore.BundleTool
public import MinCostFlow.SparseCore.BundleStageBase
import MinCostFlow.SparseCore.BundleConstantsLemmas
import MinCostFlow.DynSpanner.StepTransition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Concrete Restartable `SparseCoreRestartTool` on Bundle Graphs

Defines `sparseCoreBundleRestartTool`, extending `MinCostFlow.SparseCore.sparseCoreBundleTool`
(repaired Lemma 5.17; paper page 23) with the branch restart
operation `restartBundleTree`: restarting branch `j` re-builds
the bundle states `bun (C, b)` of each active component `C` and bucket `b` on the current tours
(using the stored order `st.ord` and the surviving admitted edges `(tr.bun (C, b)).edges`),
re-initializes the bucketed `DynSpanner` instances `dyn (C, b)` via Theorem 8.2
(`DynSpanner.init`), rebuilds `S_cur` for branch `j`, keeps the stored order `st.ord` and all
LSFs `(T_j, F_j, wstr_j)` unchanged, and leaves every other branch `b ≠ j` completely untouched.

Also defines `BundleBaseFieldsEq`, `bundleLastRestart`, and `epochBundleSeq` for analyzing a
non-restarted suffix `[s₀, t]` of a branch along `runOrdAfterUpdate` and `runOrdAfterRestarts`.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.LSF
open MinCostFlow.Bundle

/-! ## 1. Branch restart on bundle graphs and `sparseCoreBundleRestartTool` -/

/-- Re-built bundle state for `(C, b)` on branch state `tr` during a branch restart, cutting the
current tours for order `ord` restricted to the surviving admitted edges `(tr.bun (C, b)).edges`
into arcs of at most `tr.k` ends. -/
noncomputable def restartBucketBundle {L : ℕ} (tr : BundleTreeState L) (ord : ℕ → List End)
    (C : Finset ℕ) (b : ℤ) : BundleState :=
  initBundleFor tr.cs ord (tr.bun (C, b)).edges tr.k

/-- The cost charged for one restart of branch state `tr` at input order `ord`: scanning the
current graph plus initializing the dynamic spanners on all active component-bucket bundle
graphs. -/
noncomputable def singleBundleRestartCost (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (ord : ℕ → List End) : ℕ :=
  open Classical in
  tr.cs.G.m + 1 + tr.activeComps.sum fun C =>
    (tr.activeBuckets C).sum fun b =>
      let Hb := normGraph (restartBucketBundle tr ord C b).graph
      (DynSpanner.init Hb L (phaseBase (Hb.n + tr.splitBound) L) (sparsify tr.m₀)).cost

/-- The machine cost of one restart: scanning the current graph plus the spanner initialization
bounds (`spanConst * spanInitBound`) of all active component-bucket bundle graphs, all times the
log factor `bundleLogFactor`. -/
noncomputable def singleBundleRestartMachCost (L : ℕ)
    (_sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (ord : ℕ → List End) : ℕ :=
  open Classical in
  (tr.cs.G.m + 1 + tr.activeComps.sum fun C =>
    (tr.activeBuckets C).sum fun b =>
      let Hb := normGraph (restartBucketBundle tr ord C b).graph
      tr.spanConst * spanInitBound tr.spanParams L tr.splitBound Hb) *
    bundleLogFactor tr.m₀ tr.n₀

/-- Restart one branch state `tr : BundleTreeState L` onto fresh bundles of the current tours for
order `ord`: for each active component `C` and bucket `b`, re-build `bun (C, b)` via
`restartBucketBundle`, record its normalized graph in `initBunG`, re-initialize `dyn (C, b)` via
`DynSpanner.init` on `normGraph`, rebuild `S_cur` from the fresh spanners, `extraEdges`, and
`crossEdges`, add `singleBundleRestartCost` to `cost` and `singleBundleRestartMachCost` to
`machCost`, and keep `k`, `m₀`, `n₀`, `splitBound`, `spanParams`, `spanConst`, `cs` (`lsf`, `F`,
`RF`), `activeComps`, `origBucket`, `activeBuckets`, `lazyInitCost`, and `lazyMachInitCost`
unchanged. -/
noncomputable def restartBundleTree (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (ord : ℕ → List End) : BundleTreeState L :=
  open Classical in
  let bun' : Finset ℕ × ℤ → BundleState := fun p =>
    if p.1 ∈ tr.activeComps then restartBucketBundle tr ord p.1 p.2 else tr.bun p
  let initG' : Finset ℕ × ℤ → MGraph := fun p =>
    if p.1 ∈ tr.activeComps then normGraph (restartBucketBundle tr ord p.1 p.2).graph
    else tr.initBunG p
  let initCB : Finset ℕ → ℤ → InitOut L := fun C b =>
    let Hb := normGraph (restartBucketBundle tr ord C b).graph
    DynSpanner.init Hb L (phaseBase (Hb.n + tr.splitBound) L) (sparsify tr.m₀)
  let dyn' : Finset ℕ × ℤ → DynSpannerState L := fun p =>
    if p.1 ∈ tr.activeComps then (initCB p.1 p.2).state else tr.dyn p
  let dynUnionE' : Finset ℕ := tr.activeComps.biUnion fun C =>
    (tr.activeBuckets C).biUnion fun b => (initCB C b).state.H.E
  let extraComps' : Finset ℕ := tr.activeComps.biUnion fun C =>
    ((tr.cs.compSt C).G.E \ (tr.cs.compSt C).RF.F.E) \
      (tr.activeBuckets C).biUnion fun b => (bun' (C, b)).edges
  let targetE' : Finset ℕ := dynUnionE' ∪ extraComps' ∪ tr.cs.crossEdges
  let C_cur := coreGraph tr.cs.G tr.cs.lsf
  let S_cur' : MGraph :=
    { V := tr.cs.RF.R
      E := targetE'
      tail := C_cur.tail
      head := C_cur.head }
  { tr with
    bun := bun'
    initBunG := initG'
    dyn := dyn'
    S_cur := S_cur'
    cost := tr.cost + singleBundleRestartCost L sparsify tr ord
    machCost := tr.machCost + singleBundleRestartMachCost L sparsify tr ord }

/-- Generalized `SparseCoreRestartTool` parameterized by an arbitrary LSF initializer
`lsfInit : LSFInit`, equipping `sparseCoreBundleToolWith` with `restartBundleTree` on branch `j`. -/
noncomputable def sparseCoreBundleRestartToolWith
    (lsfInit : LSFInit) (_C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) :
    SparseCoreRestartTool :=
  open Classical in
  { sparseCoreBundleToolWith lsfInit L sparsify with
    restart := fun st j =>
      if st.isNonempty then
        { st with
          trees := Function.update st.trees j (restartBundleTree L sparsify (st.trees j) st.ord) }
      else st }

/-- Concrete `SparseCoreRestartTool` obtained by equipping `sparseCoreBundleTool`
(`BundleTool.lean`) with `restartBundleTree` on branch `j`, keeping the stored order `st.ord`. -/
noncomputable def sparseCoreBundleRestartTool
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) :
    SparseCoreRestartTool :=
  sparseCoreBundleRestartToolWith (initLSFOnline oracle C_lsst) C_lsst L sparsify

/-- Specializing `sparseCoreBundleRestartToolWith` to `initLSFOnline` recovers
`sparseCoreBundleRestartTool` definitionally. -/
theorem toolWith_initLSFOnline
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut) :
    sparseCoreBundleRestartToolWith (initLSFOnline oracle C_lsst) C_lsst L sparsify =
      sparseCoreBundleRestartTool oracle C_lsst L sparsify :=
  rfl

lemma sparseCoreBundleRestartTool_toSparseCoreTool
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) :
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).toSparseCoreTool =
      sparseCoreBundleToolWith lsfInit L sparsify :=
  rfl

lemma sparseCoreBundleRestartTool_restart_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreBundleState L) (j : ℕ) :
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st j =
      if st.isNonempty = true then
        { isNonempty := st.isNonempty, k := st.k, ord := st.ord,
          trees := Function.update st.trees j (restartBundleTree L sparsify (st.trees j) st.ord) }
      else st := rfl

lemma sparseCoreBundleRestartTool_restart_ord
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreBundleState L) (j : ℕ) :
    ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st j).ord = st.ord := by
  by_cases hne : st.isNonempty = true <;>
    simp [sparseCoreBundleRestartTool_restart_eq, hne]

lemma sparseCoreBundleRestartTool_restart_lsfs
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreBundleState L) (j b : ℕ) :
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).lsfs
        ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st j) b =
      (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).lsfs st b := by
  by_cases hne : st.isNonempty = true
  · by_cases hbj : b = j
    · subst hbj
      simp [sparseCoreBundleRestartToolWith, sparseCoreBundleToolWith, hne, restartBundleTree]
    · simp [sparseCoreBundleRestartToolWith, sparseCoreBundleToolWith, hne, hbj]
  · simp [sparseCoreBundleRestartToolWith, sparseCoreBundleToolWith, hne]

lemma sparseCoreBundleRestartTool_restart_cs
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreBundleState L) (j b : ℕ) :
    (((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st j).trees b).cs =
      (st.trees b).cs := by
  by_cases hne : st.isNonempty = true
  · by_cases hbj : b = j
    · subst hbj
      simp [sparseCoreBundleRestartToolWith, sparseCoreBundleToolWith, hne, restartBundleTree]
    · simp [sparseCoreBundleRestartToolWith, sparseCoreBundleToolWith, hne, hbj]
  · simp [sparseCoreBundleRestartToolWith, sparseCoreBundleToolWith, hne]

lemma sparseCoreBundleRestartTool_restart_other
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreBundleState L) {j b : ℕ} (hbj : b ≠ j) :
    ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st j).trees b = st.trees b ∧
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).S
        ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st j) b =
      (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).S st b ∧
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).emb
        ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st j) b =
      (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).emb st b ∧
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).rot
        ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st j) b =
      (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).rot st b := by
  by_cases hne : st.isNonempty = true
  · simp [sparseCoreBundleRestartToolWith, sparseCoreBundleToolWith, hne, hbj]
  · simp [sparseCoreBundleRestartToolWith, sparseCoreBundleToolWith, hne]

lemma sparseCoreBundleRestartTool_cost_le_restart
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreBundleState L) (j : ℕ) :
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).cost st ≤
      (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).cost
        ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st j) := by
  by_cases hne : st.isNonempty = true
  · simp only [sparseCoreBundleRestartToolWith, sparseCoreBundleToolWith, hne, ↓reduceIte]
    refine Finset.sum_le_sum fun b _ => ?_
    by_cases hbj : b = j
    · subst hbj
      simp [restartBundleTree]
    · simp [hbj]
  · simp [sparseCoreBundleRestartToolWith, sparseCoreBundleToolWith, hne]

lemma sparseCoreBundleRestartTool_initOrd_trees
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) :
    (SparseCoreBundleState.trees
      ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).initOrd k M N G₀ ℓ₀ g₀ ord) j) =
      initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j :=
  rfl

lemma sparseCoreBundleRestartTool_updateOrd_of_nonempty
    {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).State}
    (hne : SparseCoreBundleState.isNonempty st = true)
    (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End) :
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).updateOrd st U ℓ g ord' =
      ({ isNonempty := true, k := SparseCoreBundleState.k st, ord := ord',
         trees := fun j =>
           (stepBundleTree sparsify (SparseCoreBundleState.trees st j) U
             (SparseCoreBundleState.ord st) ord').state },
       fun j =>
         (stepBundleTree sparsify (SparseCoreBundleState.trees st j) U
           (SparseCoreBundleState.ord st) ord').U_S) := by
  change updateBundleCore sparsify st U ord' = _
  rw [updateBundleCore_of_nonempty hne]
  cases st
  dsimp only at hne
  subst hne
  rfl

lemma sparseCoreBundleRestartTool_updateOrd_of_empty
    {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).State}
    (hem : SparseCoreBundleState.isNonempty st = false)
    (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End) :
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).updateOrd st U ℓ g ord' =
      (st, fun _ => []) := by
  change updateBundleCore sparsify st U ord' = _
  simp only [updateBundleCore, hem, Bool.false_eq_true, ↓reduceIte]
  rfl

lemma sparseCoreBundleRestartTool_lsfs_of_nonempty
    {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).State}
    (hne : SparseCoreBundleState.isNonempty st = true) (j : ℕ) :
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).lsfs st j =
      (SparseCoreBundleState.trees st j).cs.lsf := by
  change (if SparseCoreBundleState.isNonempty st = true then _ else _) = _
  simp only [hne, ↓reduceIte]

lemma sparseCoreBundleRestartTool_lsfs_of_empty
    {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).State}
    (hem : SparseCoreBundleState.isNonempty st = false) (j : ℕ) :
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).lsfs st j = emptyLSF := by
  change (if SparseCoreBundleState.isNonempty st = true then _ else _) = _
  simp only [hem, Bool.false_eq_true, ↓reduceIte]

lemma sparseCoreBundleTool_lsfs_of_nonempty
    {lsfInit : LSFInit} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : (sparseCoreBundleToolWith lsfInit L sparsify).State}
    (hne : SparseCoreBundleState.isNonempty st = true) (j : ℕ) :
    (sparseCoreBundleToolWith lsfInit L sparsify).lsfs st j =
      (SparseCoreBundleState.trees st j).cs.lsf := by
  change (if SparseCoreBundleState.isNonempty st = true then _ else _) = _
  simp only [hne, ↓reduceIte]

lemma sparseCoreBundleTool_lsfs_of_empty
    {lsfInit : LSFInit} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : (sparseCoreBundleToolWith lsfInit L sparsify).State}
    (hem : SparseCoreBundleState.isNonempty st = false) (j : ℕ) :
    (sparseCoreBundleToolWith lsfInit L sparsify).lsfs st j = emptyLSF := by
  change (if SparseCoreBundleState.isNonempty st = true then _ else _) = _
  simp only [hem, Bool.false_eq_true, ↓reduceIte]

lemma sparseCoreBundleRestartTool_S_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).State) (j : ℕ) :
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).S st j =
      if SparseCoreBundleState.isNonempty st = true then
        (SparseCoreBundleState.trees st j).S_cur
      else emptyGraph := rfl

lemma sparseCoreBundleRestartTool_emb_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).State) (j : ℕ) :
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).emb st j =
      if SparseCoreBundleState.isNonempty st = true then
        (SparseCoreBundleState.trees st j).emb
      else fun _ => [] := rfl

lemma sparseCoreBundleRestartTool_rot_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).State) (j : ℕ) :
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).rot st j =
      if SparseCoreBundleState.isNonempty st = true then
        (SparseCoreBundleState.trees st j).outOrder (SparseCoreBundleState.ord st)
      else fun _ => [] := rfl

lemma sparseCoreBundleRestartTool_cost_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreBundleState L) :
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).cost st =
      if st.isNonempty = true then ∑ j ∈ Finset.range st.k, (st.trees j).cost else 0 := rfl

/-! ## 2. Structural base-field invariants of `restartBundleTree` and `runOrdAfterRestarts` -/

/-- Equality of all restart-invariant ("base") fields between two `BundleTreeState` values. -/
structure BundleBaseFieldsEq {L : ℕ} (tr₁ tr₂ : BundleTreeState L) : Prop where
  k : tr₁.k = tr₂.k
  m₀ : tr₁.m₀ = tr₂.m₀
  splitBound : tr₁.splitBound = tr₂.splitBound
  cs : tr₁.cs = tr₂.cs
  activeComps : tr₁.activeComps = tr₂.activeComps
  origBucket : tr₁.origBucket = tr₂.origBucket
  activeBuckets : tr₁.activeBuckets = tr₂.activeBuckets
  lazyInitCost : tr₁.lazyInitCost = tr₂.lazyInitCost

lemma BundleBaseFieldsEq.refl {L : ℕ} (tr : BundleTreeState L) : BundleBaseFieldsEq tr tr :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma BundleBaseFieldsEq.symm {L : ℕ} {a b : BundleTreeState L}
    (h : BundleBaseFieldsEq a b) : BundleBaseFieldsEq b a :=
  ⟨h.k.symm, h.m₀.symm, h.splitBound.symm, h.cs.symm, h.activeComps.symm,
   h.origBucket.symm, h.activeBuckets.symm, h.lazyInitCost.symm⟩

lemma BundleBaseFieldsEq.trans {L : ℕ} {a b c : BundleTreeState L}
    (h₁ : BundleBaseFieldsEq a b) (h₂ : BundleBaseFieldsEq b c) : BundleBaseFieldsEq a c :=
  ⟨h₁.k.trans h₂.k, h₁.m₀.trans h₂.m₀, h₁.splitBound.trans h₂.splitBound,
   h₁.cs.trans h₂.cs, h₁.activeComps.trans h₂.activeComps,
   h₁.origBucket.trans h₂.origBucket, h₁.activeBuckets.trans h₂.activeBuckets,
   h₁.lazyInitCost.trans h₂.lazyInitCost⟩

lemma restartBundleTree_base_fields {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (ord : ℕ → List End) :
    BundleBaseFieldsEq (restartBundleTree L sparsify tr ord) tr :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `initBundleFor` is unconditionally idempotent on its own edge set. -/
lemma initBundleFor_edges_idem (cs : CompLSFState) (ord : ℕ → List End) (E : Finset ℕ) (k : ℕ) :
    initBundleFor cs ord (initBundleFor cs ord E k).edges k = initBundleFor cs ord E k := by
  classical
  by_cases h : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (_ : CompLSFInv C_lsst ℓ₀ cs) (ρ : Rotation cs.G),
      ρ.order = ord
  · obtain ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩ := h
    rw [initBundleFor_edges hI hρ]
  · unfold initBundleFor
    rw [dite_eq_right h, dite_eq_right h]

lemma restartBucketBundle_restartBundleTree {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (ord : ℕ → List End) (C : Finset ℕ) (b : ℤ) :
    restartBucketBundle (restartBundleTree L sparsify tr ord) ord C b =
      restartBucketBundle tr ord C b := by
  dsimp only [restartBucketBundle, restartBundleTree]
  by_cases hC : C ∈ tr.activeComps
  · simp only [hC, ↓reduceIte]
    exact initBundleFor_edges_idem tr.cs ord (tr.bun (C, b)).edges tr.k
  · simp only [hC, ↓reduceIte]

lemma restartBundleTree_S_cur_spec {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {tr : BundleTreeState L} {G₀ : MGraph} {ord : ℕ → List End}
    (hG₀_eq : tr.cs.G₀ = G₀) (hI : CompLSFInv C_lsst ℓ₀ tr.cs)
    (hAct : tr.activeComps ⊆ components G₀)
    {actB : Finset ℕ → Finset ℤ} (hactB : tr.activeBuckets = actB)
    (hBun_core : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      (tr.bun (C, b)).edges ⊆ (coreGraph tr.cs.G tr.cs.lsf).E)
    (hInit_sub : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      (DynSpanner.init (normGraph (restartBucketBundle tr ord C b).graph) L
        (phaseBase ((normGraph (restartBucketBundle tr ord C b).graph).n + tr.splitBound) L)
        (sparsify tr.m₀)).state.H.E ⊆ (restartBucketBundle tr ord C b).edges) :
    let tr' := restartBundleTree L sparsify tr ord
    tr'.S_cur.IsValid ∧ tr'.S_cur.V = tr.cs.RF.R ∧
    tr'.S_cur.E =
      (tr.activeComps.biUnion fun C => (actB C).biUnion fun b => (tr'.dyn (C, b)).H.E) ∪
        (tr.activeComps.biUnion fun C => tr'.extraEdges C) ∪
        tr.cs.crossEdges ∧
    (coreGraph tr.cs.G tr.cs.lsf).IsSubgraph tr'.S_cur := by
  intro tr'
  have hRF := compLSF_RF_isRSF hI
  have hTgt_sub : tr'.S_cur.E ⊆ tr.cs.G.E \ tr.cs.RF.F.E := by
    intro e he
    change e ∈ (tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
      (DynSpanner.init (normGraph (restartBucketBundle tr ord C b).graph) L
        (phaseBase ((normGraph (restartBucketBundle tr ord C b).graph).n + tr.splitBound) L)
        (sparsify tr.m₀)).state.H.E) ∪
      (tr.activeComps.biUnion fun C =>
        ((tr.cs.compSt C).G.E \ (tr.cs.compSt C).RF.F.E) \
          (tr.activeBuckets C).biUnion fun b => (tr'.bun (C, b)).edges) ∪
      tr.cs.crossEdges at he
    rcases Finset.mem_union.mp he with he12 | heX
    · rcases Finset.mem_union.mp he12 with heD | heEx
      · rw [Finset.mem_biUnion] at heD
        rcases heD with ⟨C, hCA, heB⟩
        have hC := hAct hCA
        rw [Finset.mem_biUnion] at heB
        rcases heB with ⟨b, hb, heb⟩
        have heHb := hInit_sub C hC b (hactB ▸ hb) heb
        have heBun := initBundleFor_edges_subset tr.cs ord (tr.bun (C, b)).edges tr.k heHb
        exact hBun_core C hC b (hactB ▸ hb) heBun
      · rw [Finset.mem_biUnion] at heEx
        rcases heEx with ⟨C, hCA, heExC⟩
        exact compLSF_comp_sdiff_sub hI (hG₀_eq ▸ hAct hCA) (Finset.mem_sdiff.mp heExC).1
    · exact compLSF_crossEdges_sub hI heX
  have hVal : tr'.S_cur.IsValid := by
    intro e he
    have heG := (Finset.mem_sdiff.mp (hTgt_sub he)).1
    have hth := hI.hG_val e heG
    dsimp only [tr', restartBundleTree, coreGraph]
    exact ⟨(root_mem_R hRF hth.1).1, (root_mem_R hRF hth.2).1⟩
  have hSubC : (coreGraph tr.cs.G tr.cs.lsf).IsSubgraph tr'.S_cur :=
    ⟨Finset.Subset.rfl, hTgt_sub, fun _ _ => ⟨rfl, rfl⟩⟩
  refine ⟨hVal, rfl, ?_, hSubC⟩
  dsimp only [tr', restartBundleTree, BundleTreeState.extraEdges]
  congr 1; congr 1
  refine Finset.biUnion_congr rfl fun C hCA => ?_
  rw [hactB]
  exact Finset.biUnion_congr rfl fun b _ => by simp [hCA]

lemma foldl_bundleRestart_props
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreBundleState L) (xs : List ℕ) :
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    let st' := xs.foldl T.restart st
    st'.isNonempty = st.isNonempty ∧ st'.k = st.k ∧ st'.ord = st.ord ∧
    T.cost st ≤ T.cost st' ∧
    (∀ j, BundleBaseFieldsEq (st'.trees j) (st.trees j)) ∧
    (∀ j, j ∉ xs → st'.trees j = st.trees j) := by
  intro T
  induction xs generalizing st with
  | nil =>
    exact ⟨rfl, rfl, rfl, le_rfl, fun j => BundleBaseFieldsEq.refl (st.trees j), fun _ _ => rfl⟩
  | cons x xs ih =>
    intro st'
    have h1 := ih (T.restart st x)
    have hne1 : (T.restart st x).isNonempty = st.isNonempty := by
      rw [sparseCoreBundleRestartTool_restart_eq]
      by_cases hne : st.isNonempty = true <;> simp [hne]
    have hk1 : (T.restart st x).k = st.k := by
      rw [sparseCoreBundleRestartTool_restart_eq]
      by_cases hne : st.isNonempty = true <;> simp [hne]
    have hord1 : (T.restart st x).ord = st.ord :=
      sparseCoreBundleRestartTool_restart_ord lsfInit C_lsst L sparsify st x
    have hc1 : T.cost st ≤ T.cost (T.restart st x) :=
      sparseCoreBundleRestartTool_cost_le_restart lsfInit C_lsst L sparsify st x
    have hf1 : ∀ j, BundleBaseFieldsEq ((T.restart st x).trees j) (st.trees j) := fun j => by
      rw [sparseCoreBundleRestartTool_restart_eq]
      by_cases hne : st.isNonempty = true
      · simp only [hne, ↓reduceIte]
        by_cases hjx : j = x
        · subst hjx; simp only [Function.update_self]
          exact restartBundleTree_base_fields sparsify _ _
        · simp only [Function.update_of_ne hjx]; exact BundleBaseFieldsEq.refl _
      · simp only [hne, Bool.false_eq_true, ↓reduceIte]; exact BundleBaseFieldsEq.refl _
    refine ⟨h1.1.trans hne1, h1.2.1.trans hk1, h1.2.2.1.trans hord1, le_trans hc1 h1.2.2.2.1,
      fun j => (h1.2.2.2.2.1 j).trans (hf1 j), fun j hj => ?_⟩
    have hne_x : j ≠ x := fun h => hj (h ▸ List.mem_cons_self)
    have hni_xs : j ∉ xs := fun h => hj (List.mem_cons_of_mem x h)
    have htx : (T.restart st x).trees j = st.trees j := by
      rw [sparseCoreBundleRestartTool_restart_eq]
      by_cases hne : st.isNonempty = true <;> simp [hne, Function.update_of_ne hne_x]
    exact (h1.2.2.2.2.2 j hni_xs).trans htx

lemma runOrdAfterRestarts_isNonempty
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ) :
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    ∀ t,
      (T.runOrdAfterUpdate k M N D ord restarts t).1.isNonempty = decide (D.G 0).V.Nonempty ∧
      (T.runOrdAfterRestarts k M N D ord restarts t).isNonempty = decide (D.G 0).V.Nonempty ∧
      (T.runOrdAfterUpdate k M N D ord restarts t).1.k = k ∧
      (T.runOrdAfterRestarts k M N D ord restarts t).k = k ∧
      ((D.G 0).V.Nonempty →
        (T.runOrdAfterUpdate k M N D ord restarts t).1.ord = ord t ∧
        (T.runOrdAfterRestarts k M N D ord restarts t).ord = ord t) := by
  intro T t
  induction t with
  | zero =>
    have h0 : (T.runOrdAfterUpdate k M N D ord restarts 0).1.isNonempty = decide (D.G 0).V.Nonempty ∧
        (T.runOrdAfterUpdate k M N D ord restarts 0).1.k = k ∧
        (T.runOrdAfterUpdate k M N D ord restarts 0).1.ord = ord 0 :=
      ⟨rfl, rfl, rfl⟩
    have hf := foldl_bundleRestart_props lsfInit C_lsst L sparsify
      (T.runOrdAfterUpdate k M N D ord restarts 0).1 (restarts 0)
    exact ⟨h0.1, hf.1.trans h0.1, h0.2.1, hf.2.1.trans h0.2.1,
      fun _ => ⟨h0.2.2, hf.2.2.1.trans h0.2.2⟩⟩
  | succ s ih =>
    have hu : (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.isNonempty =
        (T.runOrdAfterRestarts k M N D ord restarts s).isNonempty ∧
        (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.k =
        (T.runOrdAfterRestarts k M N D ord restarts s).k ∧
        ((T.runOrdAfterRestarts k M N D ord restarts s).isNonempty = true →
          (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.ord = ord (s + 1)) := by
      rw [T.runOrdAfterUpdate_succ]
      dsimp only [T]
      by_cases hne : (SparseCoreRestartTool.runOrdAfterRestarts
          (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify) k M N D ord restarts s).isNonempty = true
      · rw [sparseCoreBundleRestartTool_updateOrd_of_nonempty hne]
        exact ⟨hne.symm, rfl, fun _ => rfl⟩
      · have hem : (SparseCoreRestartTool.runOrdAfterRestarts
            (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify) k M N D ord restarts s).isNonempty = false :=
          Bool.eq_false_iff.mpr hne
        rw [sparseCoreBundleRestartTool_updateOrd_of_empty hem]
        exact ⟨rfl, rfl, fun h => absurd h hne⟩
    have hpre_ne : (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.isNonempty =
        decide (D.G 0).V.Nonempty := hu.1.trans ih.2.1
    have hpre_k : (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.k = k :=
      hu.2.1.trans ih.2.2.2.1
    have hf := foldl_bundleRestart_props lsfInit C_lsst L sparsify
      (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1 (restarts (s + 1))
    refine ⟨hpre_ne, hf.1.trans hpre_ne, hpre_k, hf.2.1.trans hpre_k, fun hV₀ => ?_⟩
    have hord_pre : (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.ord = ord (s + 1) :=
      hu.2.2 (ih.2.1.trans (decide_eq_true hV₀))
    exact ⟨hord_pre, hf.2.2.1.trans hord_pre⟩

lemma runOrdAfterRestarts_empty_case
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hV₀ : ¬ (D.G 0).V.Nonempty) :
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    ∀ t,
      (T.runOrdAfterUpdate k M N D ord restarts t).1.isNonempty = false ∧
      (T.runOrdAfterRestarts k M N D ord restarts t).isNonempty = false ∧
      (T.runOrdAfterUpdate k M N D ord restarts t).2 = (fun _ => []) := by
  intro T t
  have hne := runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts t
  have hfalse : decide (D.G 0).V.Nonempty = false := decide_eq_false hV₀
  refine ⟨hne.1.trans hfalse, hne.2.1.trans hfalse, ?_⟩
  cases t with
  | zero => rfl
  | succ s =>
    rw [T.runOrdAfterUpdate_succ]
    have hs := (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.1.trans hfalse
    dsimp only [T]
    rw [sparseCoreBundleRestartTool_updateOrd_of_empty hs]

lemma stepBundleTree_congr_base {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {st₁ st₂ : BundleTreeState L} (h : BundleBaseFieldsEq st₁ st₂)
    (U : List Update) (ord ord' : ℕ → List End) :
    let i₁ := stepBundleTree sparsify st₁ U ord ord'
    let i₂ := stepBundleTree sparsify st₂ U ord ord'
    BundleBaseFieldsEq i₁.state i₂.state ∧ i₁.U_core = i₂.U_core ∧
      i₁.newlyActive = i₂.newlyActive := by
  intro i₁ i₂
  dsimp only [i₁, i₂, stepBundleTree]
  rw [h.k, h.m₀, h.splitBound, h.cs, h.activeComps, h.origBucket, h.activeBuckets, h.lazyInitCost]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

lemma runOrdAfterRestarts_base_proj
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hV₀ : (D.G 0).V.Nonempty) (j : ℕ) :
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    ∀ t,
      let trPre := (T.runOrdAfterUpdate k M N D ord restarts t).1.trees j
      let trPost := (T.runOrdAfterRestarts k M N D ord restarts t).trees j
      let trBase := (bundleRunSeqWith lsfInit L sparsify k M N D ord j t).1
      BundleBaseFieldsEq trPre trBase ∧ BundleBaseFieldsEq trPost trBase := by
  intro T t
  have hne : ∀ s, (T.runOrdAfterRestarts k M N D ord restarts s).isNonempty = true := fun s =>
    (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.1.trans
      (decide_eq_true hV₀)
  have hord : ∀ s, (T.runOrdAfterRestarts k M N D ord restarts s).ord = ord s := fun s =>
    ((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.2.2.2 hV₀).2
  induction t with
  | zero =>
    have hpre0 : (T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j =
        (bundleRunSeqWith lsfInit L sparsify k M N D ord j 0).1 := rfl
    have hf := (foldl_bundleRestart_props lsfInit C_lsst L sparsify
      (T.runOrdAfterUpdate k M N D ord restarts 0).1 (restarts 0)).2.2.2.2.1 j
    rw [hpre0] at hf ⊢
    exact ⟨BundleBaseFieldsEq.refl _, hf⟩
  | succ s ih =>
    have hpre_eq : (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j =
        (stepBundleTree sparsify ((T.runOrdAfterRestarts k M N D ord restarts s).trees j)
          (D.U (s + 1)) (ord s) (ord (s + 1))).state := by
      rw [T.runOrdAfterUpdate_succ]
      dsimp only [T]
      rw [sparseCoreBundleRestartTool_updateOrd_of_nonempty (hne s), hord s]
    have hcon := stepBundleTree_congr_base sparsify ih.2 (D.U (s + 1)) (ord s) (ord (s + 1))
    have hpre_p : BundleBaseFieldsEq
        ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j)
        (bundleRunSeqWith lsfInit L sparsify k M N D ord j (s + 1)).1 := by
      rw [hpre_eq]
      exact hcon.1
    have hf := (foldl_bundleRestart_props lsfInit C_lsst L sparsify
      (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1 (restarts (s + 1))).2.2.2.2.1 j
    exact ⟨hpre_p, hf.trans hpre_p⟩

/-! ## 3. Last restart index and epoch sequence `epochBundleSeq` -/

/-- Last restart step `≤ t` for branch `j` (`0` if `j` never restarted on `[1, t]`). -/
def bundleLastRestart (restarts : ℕ → List ℕ) (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 => if j ∈ restarts (s + 1) then s + 1 else bundleLastRestart restarts j s

lemma bundleLastRestart_spec (restarts : ℕ → List ℕ) (j t : ℕ) :
    bundleLastRestart restarts j t ≤ t ∧
    (bundleLastRestart restarts j t = 0 ∨ j ∈ restarts (bundleLastRestart restarts j t)) ∧
    ∀ r, bundleLastRestart restarts j t < r → r ≤ t → j ∉ restarts r := by
  induction t with
  | zero =>
    refine ⟨le_rfl, Or.inl rfl, fun r hr1 hr0 => by omega⟩
  | succ s ih =>
    dsimp only [bundleLastRestart]
    split_ifs with hj
    · refine ⟨le_rfl, Or.inr hj, fun r hr1 hr2 => by omega⟩
    · refine ⟨Nat.le_succ_of_le ih.1, ih.2.1, fun r hr1 hr2 => ?_⟩
      by_cases hrs : r = s + 1
      · subst hrs; exact hj
      · exact ih.2.2 r hr1 (by omega)

/-- Epoch state sequence on `[s₀, t]` for branch `j` when `∀ r, s₀ < r → r < t → j ∉ restarts r`:
uses `(post (s₀ + δ)).trees j` on `0 ≤ δ` except `(pre t).trees j` at `s₀ + δ = t` (`s₀ < t`). -/
noncomputable def epochBundleSeq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (s₀ t j δ : ℕ) : BundleTreeState L :=
  let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
  if s₀ + δ = t ∧ s₀ < t then (T.runOrdAfterUpdate k M N D ord restarts t).1.trees j
  else (T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)).trees j

lemma epochBundleSeq_steps
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hV₀ : (D.G 0).V.Nonempty) (s₀ t j : ℕ) (hst : s₀ ≤ t)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r) :
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    let st := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j
    (∀ δ ≤ t - s₀,
      BundleBaseFieldsEq (st δ) (bundleRunSeqWith lsfInit L sparsify k M N D ord j (s₀ + δ)).1) ∧
    (∀ δ < t - s₀,
      st (δ + 1) = (stepBundleTree sparsify (st δ) (D.U (s₀ + δ + 1))
        (ord (s₀ + δ)) (ord (s₀ + δ + 1))).state ∧
      (T.runOrdAfterUpdate k M N D ord restarts (s₀ + δ + 1)).2 j =
        (stepBundleTree sparsify (st δ) (D.U (s₀ + δ + 1))
          (ord (s₀ + δ)) (ord (s₀ + δ + 1))).U_S) := by
  intro T st
  have hne : ∀ s, (T.runOrdAfterRestarts k M N D ord restarts s).isNonempty = true := fun s =>
    (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.1.trans
      (decide_eq_true hV₀)
  have hord : ∀ s, (T.runOrdAfterRestarts k M N D ord restarts s).ord = ord s := fun s =>
    ((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.2.2.2 hV₀).2
  refine ⟨fun δ _ => ?_, fun δ hδ => ?_⟩
  · have hb := runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts hV₀ j (s₀ + δ)
    dsimp only [st, epochBundleSeq]
    split_ifs with hEq
    · rw [hEq.1] at hb ⊢; exact hb.1
    · exact hb.2
  · have hδ_ne : ¬ (s₀ + δ = t ∧ s₀ < t) := by omega
    have hst_δ : st δ = (T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)).trees j := by
      dsimp only [st, epochBundleSeq, T]
      simp only [hδ_ne, ↓reduceIte]
    have hpre_s1 : (T.runOrdAfterUpdate k M N D ord restarts (s₀ + δ + 1)).1.trees j =
        (stepBundleTree sparsify (st δ) (D.U (s₀ + δ + 1)) (ord (s₀ + δ)) (ord (s₀ + δ + 1))).state ∧
        (T.runOrdAfterUpdate k M N D ord restarts (s₀ + δ + 1)).2 j =
        (stepBundleTree sparsify (st δ) (D.U (s₀ + δ + 1)) (ord (s₀ + δ)) (ord (s₀ + δ + 1))).U_S := by
      rw [T.runOrdAfterUpdate_succ]
      dsimp only [T] at hst_δ ⊢
      rw [sparseCoreBundleRestartTool_updateOrd_of_nonempty (hne (s₀ + δ)), hord (s₀ + δ)]
      dsimp only
      rw [← hst_δ]
      exact ⟨rfl, rfl⟩
    refine ⟨?_, hpre_s1.2⟩
    dsimp only [T] at hpre_s1 ⊢
    by_cases ht_eq : s₀ + (δ + 1) = t
    · have hlt : s₀ < t := by omega
      have h1 : st (δ + 1) = ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterUpdate
          k M N D ord restarts t).1.trees j := by
        dsimp only [st, epochBundleSeq, T]
        simp only [ht_eq, hlt, and_self, ↓reduceIte]
      have h2 : ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterUpdate
          k M N D ord restarts t).1.trees j =
          ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterUpdate
            k M N D ord restarts (s₀ + δ + 1)).1.trees j := by
        rw [← ht_eq, Nat.add_assoc]
      rw [h1, h2, hpre_s1.1]
    · have hnot : ¬ (s₀ + (δ + 1) = t ∧ s₀ < t) := fun h => ht_eq h.1
      have hni : j ∉ restarts (s₀ + (δ + 1)) := hNoRest (s₀ + (δ + 1)) (by omega) (by omega)
      have h1 : st (δ + 1) = ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterRestarts
          k M N D ord restarts (s₀ + (δ + 1))).trees j := by
        dsimp only [st, epochBundleSeq, T]
        simp only [hnot, ↓reduceIte]
      have hf := (foldl_bundleRestart_props lsfInit C_lsst L sparsify
        ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterUpdate k M N D ord restarts
          (s₀ + (δ + 1))).1 (restarts (s₀ + (δ + 1)))).2.2.2.2.2 j hni
      rw [h1]
      change ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterRestarts
        k M N D ord restarts (s₀ + (δ + 1))).trees j = _
      unfold SparseCoreRestartTool.runOrdAfterRestarts
      rw [hf, ← Nat.add_assoc, hpre_s1.1]

lemma epochBundleSeq_eq_post
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (s₀ t j : ℕ) (hst : s₀ ≤ t) :
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    let ep := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j
    (∀ r < t - s₀, ep r = (T.runOrdAfterRestarts k M N D ord restarts (s₀ + r)).trees j) ∧
    (j ∉ restarts t ∨ s₀ = t →
      ep (t - s₀) = (T.runOrdAfterRestarts k M N D ord restarts t).trees j) ∧
    (s₀ < t → ep (t - s₀) = (T.runOrdAfterUpdate k M N D ord restarts t).1.trees j) := by
  intro T ep
  refine ⟨fun r hr => ?_, fun hnor => ?_, fun hlt => ?_⟩
  · have hcond : ¬ (s₀ + r = t ∧ s₀ < t) := by omega
    dsimp only [ep, epochBundleSeq, T]
    simp only [hcond, ↓reduceIte]
  · rcases hnor with hni | rfl
    · by_cases heq : s₀ = t
      · subst heq
        simp only [Nat.sub_self]
        dsimp only [ep, epochBundleSeq, T]
        simp
      · have hlt : s₀ < t := by omega
        have hcond : s₀ + (t - s₀) = t ∧ s₀ < t := ⟨by omega, hlt⟩
        dsimp only [ep, epochBundleSeq, T]
        simp only [hcond]
        have hf := (foldl_bundleRestart_props lsfInit C_lsst L sparsify
          (T.runOrdAfterUpdate k M N D ord restarts t).1 (restarts t)).2.2.2.2.2 j hni
        exact hf.symm
    · simp only [Nat.sub_self]
      dsimp only [ep, epochBundleSeq, T]
      simp
  · have hcond : s₀ + (t - s₀) = t ∧ s₀ < t := ⟨by omega, hlt⟩
    dsimp only [ep, epochBundleSeq, T]
    simp only [hcond, and_self, ↓reduceIte]

end MinCostFlow.Chain

end
