module

public import MinCostFlow.SparseCore.BundleCoreParams

/-!
# Generalized Per-Instance Hypotheses `BundleCoreHypsAtWith`

Parameterizes `BundleCoreHypsAt` over an arbitrary LSF initializer `lsfInit : LSFInit` via
`IsValidLSFInitFor`, with `BundleCoreHypsAt.toWith` recovering the `initLSFOnline` specialization
and `bundleCoreHypsAtWith_of_B_ge_m` providing the unconditional `B_fn M ≥ m` constructor.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow
open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

lemma initBundleTreeWith_activeBuckets_eq
    (lsfInit : LSFInit) (L₁ L₂ : ℕ)
    (sparsify₁ sparsify₂ : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M₁ M₂ N₁ N₂ : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord₁ ord₂ : ℕ → List End) (j : ℕ) :
    (initBundleTreeWith lsfInit L₁ sparsify₁ k M₁ N₁ G₀ ℓ₀ ord₁ j).activeBuckets =
      (initBundleTreeWith lsfInit L₂ sparsify₂ k M₂ N₂ G₀ ℓ₀ ord₂ j).activeBuckets :=
  rfl

lemma initBundleTreeWith_activeBuckets_apply
    (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) (C : Finset ℕ) :
    let cs₀ := initCompLSFWith lsfInit G₀ ℓ₀ k j
    let C₀ := coreGraph G₀ cs₀.lsf
    (initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j).activeBuckets C =
      (C₀.E.filter fun e => C₀.tail e ∈ C).image
        (fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e)) :=
  rfl

lemma initBundleTreeWith_activeBuckets_card_le_m
    (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) (C : Finset ℕ) :
    ((initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j).activeBuckets C).card ≤ G₀.m := by
  classical
  rw [initBundleTreeWith_activeBuckets_apply]
  exact le_trans Finset.card_image_le
    (le_trans (Finset.card_filter_le _ _) (Finset.card_le_card Finset.sdiff_subset))

/-- Generalized per-instance hypotheses of `sparseCoreBundleToolWith` at edge scale `M`,
parameterized by an arbitrary LSF initializer `lsfInit : LSFInit`. -/
structure BundleCoreHypsAtWith (E : SparseCoreEnv) (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M : ℕ) (D : DynamicInstance) : Prop where
  hInit : ∀ j < k, IsValidLSFInitFor lsfInit E.C_lsst k j
  hSp : SparsifySpec M (E.P_fn M) (sparsify M)
  hB_bound : ∀ j < k, ∀ C ∈ components (D.G 0),
    ((initBundleTreeWith lsfInit E.L sparsify k M 0 (D.G 0) (D.ℓ 0) (fun _ => []) j).activeBuckets
      C).card ≤ E.B_fn M

lemma BundleCoreHypsAtWith.activeBuckets_card_le {E : SparseCoreEnv} {lsfInit : LSFInit}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {k M : ℕ} {D : DynamicInstance}
    (h : BundleCoreHypsAtWith E lsfInit sparsify k M D)
    {N : ℕ} {ord : ℕ → ℕ → List End} {j : ℕ} (hj : j < k) :
    ∀ C ∈ components (D.G 0),
      ((bundleRunSeqWith lsfInit E.L sparsify k M N D ord j 0).1.activeBuckets C).card ≤
        E.B_fn M :=
  h.hB_bound j hj

theorem bundleCoreHypsAtWith_of_B_ge_m {E : SparseCoreEnv} {lsfInit : LSFInit}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {k M : ℕ} {D : DynamicInstance}
    (hInit : ∀ j < k, IsValidLSFInitFor lsfInit E.C_lsst k j)
    (hSp : SparsifySpec M (E.P_fn M) (sparsify M))
    (hBm : (D.G 0).m ≤ E.B_fn M) :
    BundleCoreHypsAtWith E lsfInit sparsify k M D where
  hInit := hInit
  hSp := hSp
  hB_bound := fun j _ C _ =>
    le_trans (initBundleTreeWith_activeBuckets_card_le_m lsfInit E.L sparsify k M 0
      (D.G 0) (D.ℓ 0) (fun _ => []) j C) hBm

lemma BundleCoreHypsAt.toWith {E : SparseCoreEnv}
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {k M : ℕ} {D : DynamicInstance}
    (h : BundleCoreHypsAt E oracle sparsify k M D) :
    BundleCoreHypsAtWith E (initLSFOnline oracle E.C_lsst) sparsify k M D where
  hInit := fun j _ => initLSFOnline_isValidLSFInitFor h.hLSST k j
  hSp := h.hSp
  hB_bound := h.hB_bound

end

end MinCostFlow.SparseCore
