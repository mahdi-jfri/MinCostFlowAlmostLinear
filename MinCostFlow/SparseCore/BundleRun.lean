module

public import MinCostFlow.SparseCore.BundleTreeCore
public import MinCostFlow.Bundle.Ordered

/-!
# The run of one branch on bundle graphs

`bundleRunSeq` runs one branch of the sparse core on bundle graphs (`BundleTreeState`) along a
dynamic instance, with the order of ends at every stage given as data `ord : ℕ → ℕ → List End`
(stage, then vertex). It is the analogue of `treeRunSeq` for `TreeCoreState`. The input is
ordered with split bound two when `OrderedUpTo D τ 2 ord` holds.
`bundleBatchList` lists the batches that the spanner of one component and bucket receives.

Only the definitions and their unfolding lemmas are here.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.Bundle

/-- The states and output batches of branch `j` along `D` with orders `ord`, using an arbitrary
LSF initializer `lsfInit`, at size bounds `(M, N)`. -/
noncomputable def bundleRunSeqWith (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ) :
    ℕ → BundleTreeState L × List Update
  | 0 => (initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j, [])
  | t + 1 =>
    let info := stepBundleTree sparsify
      (bundleRunSeqWith lsfInit L sparsify k M N D ord j t).1 (D.U (t + 1)) (ord t) (ord (t + 1))
    (info.state, info.U_S)

/-- The step data of stage `t + 1` of `bundleRunSeqWith`. -/
noncomputable abbrev bundleRunInfoWith (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j t : ℕ) :
    BundleTreeStepInfo L :=
  stepBundleTree sparsify (bundleRunSeqWith lsfInit L sparsify k M N D ord j t).1
    (D.U (t + 1)) (ord t) (ord (t + 1))

theorem bundleRunSeqWith_zero (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ) :
    bundleRunSeqWith lsfInit L sparsify k M N D ord j 0 =
      (initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j, []) :=
  rfl

theorem bundleRunSeqWith_succ (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j t : ℕ) :
    bundleRunSeqWith lsfInit L sparsify k M N D ord j (t + 1) =
      ((bundleRunInfoWith lsfInit L sparsify k M N D ord j t).state,
        (bundleRunInfoWith lsfInit L sparsify k M N D ord j t).U_S) :=
  rfl

/-- The batches that the spanner of component `C` and bucket `b` receives in the first `τ`
steps of `bundleRunSeqWith`. -/
noncomputable def bundleBatchListWith (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ) (C : Finset ℕ)
    (b : ℤ) : List (List Update) :=
  (List.range τ).map fun t => (bundleRunInfoWith lsfInit L sparsify k M N D ord j t).U_B (C, b)

theorem bundleBatchListWith_getElem? (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ) (C : Finset ℕ)
    (b : ℤ) {t : ℕ} (ht : t < τ) :
    (bundleBatchListWith lsfInit L sparsify k M N τ D ord j C b)[t]? =
      some ((bundleRunInfoWith lsfInit L sparsify k M N D ord j t).U_B (C, b)) := by
  simp [bundleBatchListWith, ht]

/-- The component-wise LSF of `bundleRunSeqWith` is the LSF run on the input batches. -/
theorem bundleRunSeqWith_cs (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ) :
    ∀ t, (bundleRunSeqWith lsfInit L sparsify k M N D ord j (t + 1)).1.cs =
      compLSFBatch (bundleRunSeqWith lsfInit L sparsify k M N D ord j t).1.cs (D.U (t + 1)) :=
  fun _ => rfl

/-- The states and output batches of branch `j` along `D` with orders `ord`, at size bounds
`(M, N)`. Stage `0` is the initialization and stage `t + 1` applies the batch `D.U (t + 1)` with
the orders `ord t` before and `ord (t + 1)` after it. -/
noncomputable def bundleRunSeq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ) :
    ℕ → BundleTreeState L × List Update :=
  bundleRunSeqWith (initLSFOnline oracle C_lsst) L sparsify k M N D ord j

/-- The step data of stage `t + 1` of `bundleRunSeq`. -/
noncomputable abbrev bundleRunInfo
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j t : ℕ) :
    BundleTreeStepInfo L :=
  bundleRunInfoWith (initLSFOnline oracle C_lsst) L sparsify k M N D ord j t

theorem bundleRunSeq_zero
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ) :
    bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0 =
      (initBundleTree oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j, []) :=
  rfl

theorem bundleRunSeq_succ
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j t : ℕ) :
    bundleRunSeq oracle C_lsst L sparsify k M N D ord j (t + 1) =
      ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j t).state,
        (bundleRunInfo oracle C_lsst L sparsify k M N D ord j t).U_S) :=
  rfl

/-- The batches that the spanner of component `C` and bucket `b` receives in the first `τ`
steps of `bundleRunSeq`. -/
noncomputable def bundleBatchList
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ) (C : Finset ℕ)
    (b : ℤ) : List (List Update) :=
  bundleBatchListWith (initLSFOnline oracle C_lsst) L sparsify k M N τ D ord j C b

theorem bundleBatchList_getElem?
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ) (C : Finset ℕ)
    (b : ℤ) {t : ℕ} (ht : t < τ) :
    (bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b)[t]? =
      some ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j t).U_B (C, b)) :=
  bundleBatchListWith_getElem? (initLSFOnline oracle C_lsst) L sparsify k M N τ D ord j C b ht

/-- The edges of the sparsified core that a component keeps outside its bundle graphs: its
non-forest edges that lie in no bundle graph of its active buckets. These are the edges that
`stepBundleTree` keeps in `extraComps'`. -/
noncomputable def BundleTreeState.extraEdges {L : ℕ} (st : BundleTreeState L) (C : Finset ℕ) :
    Finset ℕ :=
  ((st.cs.compSt C).G.E \ (st.cs.compSt C).RF.F.E) \
    (st.activeBuckets C).biUnion fun b => (st.bun (C, b)).edges

/-- The component-wise LSF of the run is the LSF run on the input batches. -/
theorem bundleRunSeq_cs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ) :
    ∀ t, (bundleRunSeq oracle C_lsst L sparsify k M N D ord j (t + 1)).1.cs =
      compLSFBatch (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.cs (D.U (t + 1)) :=
  fun _ => rfl

end MinCostFlow.SparseCore
