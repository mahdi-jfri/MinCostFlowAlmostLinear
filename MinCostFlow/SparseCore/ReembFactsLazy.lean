module

public import MinCostFlow.SparseCore.Program.AssemblyInputRun

import MinCostFlow.Chain.BundleRestartBun
import MinCostFlow.Chain.BundleRestartMach

/-!
# Lazy-initialization coverage for reached states of the sparse core (`ReembFactsLazy`)

Proves that on every nonempty state `s` reached under `SparseCoreOrdInput` for
`sparseCoreBundleRestartToolMachWith`, every inactive component `C ∈ components tr.cs.G₀ \ tr.activeComps`
of branch `j` still holds its initial bundles and initial lazy cost (`runOrdAfterRestarts_bun_inv`),
so `tr.lazyInitCost C` covers the total number of edges in its buckets
(`initBundleTreeWith_edges_le_lazyInitCost`).

In particular, on any step `stepBundleTree sparsify tr U ord₁ ord'` from `tr`, every newly
activated component `C ∈ info.newlyActive` satisfies the lazy-coverage hypothesis of
`stepBundleTree_reembList_length_le_cost` (`BranchLazyCovers`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.LSF
open MinCostFlow.SparseCore.Program

/-- On every nonempty state reached under `SparseCoreOrdInput`, every inactive component `C` of
branch `j` keeps its initial bundles and lazy initialization cost, so `tr.lazyInitCost C` covers
the edges of all its buckets. -/
theorem sparseCoreOrdInput_inactive_edges_le_lazyInitCost
    {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {params : ℕ → SparsifyParams} {spanConst k M N : ℕ}
    {s : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).State}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hk : 0 < k)
    (hinp : SparseCoreOrdInput
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst)
      k M N s G ord n)
    (hne : SparseCoreBundleState.isNonempty (L := L) s = true)
    {j : ℕ} (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    let tr := SparseCoreBundleState.trees (L := L) s j
    ∀ C ∈ components tr.cs.G₀, C ∉ tr.activeComps →
      ((tr.activeBuckets C).sum fun b => (tr.bun (C, b)).edges.card) ≤ tr.lazyInitCost C := by
  classical
  intro tr C hC hna
  set Tm := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
  set Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
  obtain ⟨τ, D, ordSeq, restarts, hG₀, _, _, hℓ₀, hD, hOrd, _, _, _, _, hrun⟩ :=
    sparseCoreOrdInput_exists_run Tm hinp
  have hNM := (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L
    sparsify params spanConst k M N D ordSeq restarts τ).2.2
  rw [hrun] at hNM
  have hV₀ : (D.G 0).V.Nonempty := by
    have h1 := (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify
      k M N D ordSeq restarts τ).2.1
    rw [← hNM.isNonempty, hne] at h1
    exact of_decide_eq_true h1.symm
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ordSeq restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit τ le_rfl
  set st₀ := initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ordSeq 0) j
  set pre := (Tb.runOrdAfterUpdate k M N D ordSeq restarts τ).1.trees j
  set post := (Tb.runOrdAfterRestarts k M N D ordSeq restarts τ).trees j
  have hbf : BundleBaseFieldsEq post pre :=
    (foldl_bundleRestart_props lsfInit C_lsst L sparsify
      (Tb.runOrdAfterUpdate k M N D ordSeq restarts τ).1 (restarts τ)).2.2.2.2.1 j
  have hEq : BundleNonMachEq tr post := hNM.trees j
  have hG₀_eq : tr.cs.G₀ = D.G 0 := by
    rw [hEq.cs, hbf.cs, hBun.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
  have hC0 : C ∈ components (D.G 0) := hG₀_eq ▸ hC
  have hna_pre : C ∉ pre.activeComps := by
    rwa [← hbf.activeComps, ← hEq.activeComps]
  have hAB : tr.activeBuckets = st₀.activeBuckets :=
    hEq.activeBuckets.trans (hbf.activeBuckets.trans hBun.2.2.2.2.1)
  have hLC : tr.lazyInitCost = st₀.lazyInitCost :=
    hEq.lazyInitCost.trans (hbf.lazyInitCost.trans hBun.2.2.2.2.2.1)
  have hbun_eq : ∀ b : ℤ, tr.bun (C, b) = st₀.bun (C, b) := fun b => by
    rw [hEq.bun]
    exact ((hBun.2.2.2.2.2.2.2.2.2.2.1 C hC0 hna_pre).2 b).2.2.1
  rw [hAB, hLC]
  have hsum_eq : ((st₀.activeBuckets C).sum fun b => (tr.bun (C, b)).edges.card) =
      ((st₀.activeBuckets C).sum fun b => (st₀.bun (C, b)).edges.card) :=
    Finset.sum_congr rfl fun b _ => by rw [hbun_eq b]
  rw [hsum_eq]
  exact initBundleTreeWith_edges_le_lazyInitCost lsfInit L sparsify k M N (D.G 0) (D.ℓ 0)
    (ordSeq 0) j C

/-- On every step `stepBundleTree` from a nonempty state reached under `SparseCoreOrdInput`, every
newly activated component `C ∈ info.newlyActive` has its bucket edge count covered by
`tr.lazyInitCost C`. -/
theorem sparseCoreOrdInput_lazyCovers
    {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {params : ℕ → SparsifyParams} {spanConst k M N : ℕ}
    {s : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).State}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hk : 0 < k)
    (hinp : SparseCoreOrdInput
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst)
      k M N s G ord n)
    (hne : SparseCoreBundleState.isNonempty (L := L) s = true)
    {j : ℕ} (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    (U : List Update) (ord₁ ord' : ℕ → List End) :
    let tr := SparseCoreBundleState.trees (L := L) s j
    ∀ C ∈ (stepBundleTree sparsify tr U ord₁ ord').newlyActive,
      ((tr.activeBuckets C).sum fun b => (tr.bun (C, b)).edges.card) ≤ tr.lazyInitCost C := by
  intro tr C hC
  have hsd := Finset.mem_sdiff.mp hC
  have hC0 : C ∈ components tr.cs.G₀ := Finset.filter_subset _ _ hsd.1
  exact sparseCoreOrdInput_inactive_edges_le_lazyInitCost hk hinp hne hInit C hC0 hsd.2

end MinCostFlow.SparseCore
