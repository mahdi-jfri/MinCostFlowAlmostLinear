module

public import MinCostFlow.Chain.SparseCoreOrdSpec
public import MinCostFlow.SparseCore.BundleCoreParams
public import MinCostFlow.SparseCore.BundleCostEnv
public import MinCostFlow.SparseCore.BundleMetrics
public import MinCostFlow.SparseCore.BundleSpannerMetrics
public import MinCostFlow.SparseCore.BundleStability
public import MinCostFlow.SparseCore.BundleRunInv
public import MinCostFlow.SparseCore.BundleOutBatchSpec
public import MinCostFlow.SparseCore.BundleOutOrder
public import MinCostFlow.SparseCore.BundleStage
public import MinCostFlow.SparseCore.BundleInitCount
public import MinCostFlow.SparseCore.BundleRecourse
public import MinCostFlow.SparseCore.BundleCost
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemma 5.17 for the Tour-Bundle Sparse Core Tool (`jtree.tex`, pages 23–24)

This file proves the ordered specifications `SparseCoreTool.IsSpecOrdNoHiddenUpTo` and
`SparseCoreTool.IsSpecOrdUpTo` (together with `IsSpecOrdNoHidden`, `IsSpecOrd`, and the
`∀ m, m ≤ E.B_fn m` corollaries) for `sparseCoreBundleTool` with the degree-free parameter
envelope `bundleCoreParams E` under `BundleCoreHypsAt` (no input degree bound and no
`N ≤ c_n (M + 1)` hypothesis).

The stage invariants (`BundleStage.bundleRunSeq_stage_inv`, `BundleInitCount.initBundleTree_vertex_sum_le`),
output-batch specification (`BundleOutBatchSpec.buildUSOrd_spec`), run invariant
(`BundleRunInv.bundleRunSeq_inv`), output-order preservation
(`BundleOutOrder.sparseCoreBundleTool_orderedUpTo`), LSF guarantees (`BundleMetrics`),
sparsified-core metrics (`BundleSpannerMetrics`), `min N (M + 1)` recourse and active-cost bounds
(`BundleRecourse.bundleRunSeq_recourse_and_enc_min`, `BundleCost.bundleRunSeq_cost_le_active`),
hidden stability (`BundleStability`), and parameter-envelope bridges (`BundleParamBridges`,
`BundleCostEnv`) are all wired in unconditionally.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow
open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

/-! ## 1. Output-order wrapper from `BundleOutOrder` -/

/-- Unconditional output-order preservation for `sparseCoreBundleTool` on both nonempty and empty
initial graphs. -/
theorem bundleLemma_5_17_orderedUpTo
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord)
    (j : ℕ) (hj : j < k) :
    let T := sparseCoreBundleTool oracle C_lsst L sparsify
    let st := fun t => (T.runOrdAt k M N D ord t).1
    OrderedUpTo (T.coreInstanceOrdAt k M N D ord j) τ 2 (fun t => T.rot (st t) j) :=
  sparseCoreBundleTool_orderedUpTo oracle C_lsst L hL P_b sparsify hLSST k M N τ hk D hG₀ hℓ₀
    hD hM hN hThresh hSp ord hOrd j hj

/-! ## 2. Connected root bound and empty-graph helpers -/

/-- Lifts the connected-graph root count from `((D.G 0).m, (D.G 0).n)` to `(M, N)`. -/
lemma bundleTool_connected_root_bound
    (E : SparseCoreEnv) (k M N t : ℕ) (D : DynamicInstance)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    {Rcard : ℕ}
    (hR : (Rcard : ℝ) ≤ 112 * (((D.G 0).m : ℝ) / (k : ℝ) +
      (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
        (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 + 1)) :
    (Rcard : ℝ) ≤ (bundleCoreParams E).c_R * ((M : ℝ) / (k : ℝ) +
      (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
        (Real.log ((N : ℝ) + 2)) ^ 2 + 1) := by
  have hMR : ((D.G 0).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hNR : ((D.G 0).n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hdiv : ((D.G 0).m : ℝ) / (k : ℝ) ≤ (M : ℝ) / (k : ℝ) :=
    div_le_div_of_nonneg_right hMR (Nat.cast_nonneg k)
  have hlog_nn : 0 ≤ Real.log (((D.G 0).n : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (D.G 0).n])
  have hlog_le : Real.log (((D.G 0).n : ℝ) + 2) ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) (D.G 0).n]) (by linarith)
  have hsq : (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 ≤ (Real.log ((N : ℝ) + 2)) ^ 2 :=
    pow_le_pow_left₀ hlog_nn hlog_le 2
  have hq_nn : (0 : ℝ) ≤ (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hmul : (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
        (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 ≤
      (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
        (Real.log ((N : ℝ) + 2)) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hq_nn
  change (Rcard : ℝ) ≤ 112 * _
  linarith

/-- Empty-graph accessors for `sparseCoreBundleTool.runOrdAt`. -/
lemma bundleTool_empty_accessors
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hV₀ : ¬ (D.G 0).V.Nonempty) (t j : ℕ) :
    let T := sparseCoreBundleTool oracle C_lsst L sparsify
    let st := (T.runOrdAt k M N D ord t).1
    T.S st j = emptyGraph ∧
    T.lsfs st j = emptyLSF ∧
    T.emb st j = (fun _ => []) ∧
    T.rot st j = (fun _ => []) ∧
    (T.runOrdAt k M N D ord t).2 j = [] := by
  have hrunE := bundleTool_runOrdAt_empty oracle C_lsst L sparsify k M N D ord hV₀ t
  set r := (sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t
  have h1 : r.1.isNonempty = false := hrunE.1
  have h2 : r.2 j = [] := by rw [hrunE.2]
  refine ⟨?_, ?_, ?_, ?_, h2⟩
  · change (if r.1.isNonempty = true then (r.1.trees j).S_cur else emptyGraph) = emptyGraph
    simp only [h1, Bool.false_eq_true, ↓reduceIte]
  · change (if r.1.isNonempty = true then (r.1.trees j).cs.lsf else emptyLSF) = emptyLSF
    simp only [h1, Bool.false_eq_true, ↓reduceIte]
  · change (if r.1.isNonempty = true then (r.1.trees j).emb else fun _ => []) = fun _ => []
    simp only [h1, Bool.false_eq_true, ↓reduceIte]
  · change (if r.1.isNonempty = true then (r.1.trees j).outOrder r.1.ord else fun _ => []) =
      fun _ => []
    simp only [h1, Bool.false_eq_true, ↓reduceIte]

/-- Empty-graph clauses (1, 2, and 3) of `IsSpecOrdNoHiddenUpTo` for `sparseCoreBundleTool`. -/
lemma bundleTool_empty_clauses (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : ¬ (D.G 0).V.Nonempty) (hD : D.IsValid τ) :
    let T := sparseCoreBundleTool oracle E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    let st := fun t => (T.runOrdAt k M N D ord t).1
    let U_S := fun t => (T.runOrdAt k M N D ord t).2
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (st t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (st t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ M) (P.γ_c M) M
        (T.S (st t) j) (T.emb (st t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (st t) j).F.R.card : ℝ) ≤
          P.c_R * ((M : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((N : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (st t) j).F.F.E ⊆ (T.lsfs (st (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (st t) j).wstr e = (T.lsfs (st (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (st t) j).wstr e = 1) ∧
      (T.S (st (t - 1)) j).BatchIsValid (U_S t j) ∧
      T.S (st t) j = (T.S (st (t - 1)) j).applyBatch (U_S t j)) ∧
    (∀ t ≤ τ, ∀ j < k,
      (((Finset.Icc 1 t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc 1 t).sum fun s => (T.S (st (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        P.γ_r M * ((M : ℝ) / (k : ℝ) +
          (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ))) := by
  intro T P st U_S
  have hValP := bundleCoreParams_valid E
  obtain ⟨hG_empty, _⟩ := empty_dyn_eq hG₀ hV₀ hD
  have hAcc := fun t j => bundleTool_empty_accessors oracle E.C_lsst E.L sparsify k M N D ord hV₀ t j
  have hS_eq : ∀ t j, T.S (st t) j = emptyGraph := fun t j => (hAcc t j).1
  have hL_eq : ∀ t j, T.lsfs (st t) j = emptyLSF := fun t j => (hAcc t j).2.1
  have hEmb_eq : ∀ t j, T.emb (st t) j = fun _ => [] := fun t j => (hAcc t j).2.2.1
  have hUS_eq : ∀ t j, U_S t j = [] := fun t j => (hAcc t j).2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro t ht j _
    have hGt := hG_empty t ht
    rw [hL_eq t j, hS_eq t j, hEmb_eq t j]
    refine ⟨emptyLSF_holds hGt.left hGt.right.left (D.ℓ t) (P.σ k (D.G t).n), ?_, ?_⟩
    · have hCG_V : (coreGraph (D.G t) emptyLSF).V = ∅ := rfl
      have hCG_E : (coreGraph (D.G t) emptyLSF).E = ∅ := by
        simp [coreGraph, emptyLSF, hGt.2.2]
      refine ⟨⟨Finset.empty_subset _, Finset.empty_subset _, fun _ h => by simp [emptyGraph] at h⟩,
        ⟨by simp [hCG_V, emptyGraph], fun _ h => by simp [hCG_E] at h⟩,
        fun _ h => by simp [hCG_E] at h, ?_, ?_, ?_⟩
      · have hlen0 : Embedding.length (fun _ => []) (coreGraph (D.G t) emptyLSF) = 0 := by
          unfold Embedding.length; rw [hCG_E]; simp
        rw [hlen0, Nat.cast_zero]; linarith [hValP.2.2.1 M]
      · have hecong0 : Embedding.econg (fun _ => []) (coreGraph (D.G t) emptyLSF) emptyGraph
            (fun _ => 1) (fun _ => 1) = 0 := by
          unfold Embedding.econg; simp [emptyGraph]
        rw [hecong0]
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        have : 1 ≤ P.γ_c M := hValP.2.2.2.2.1 M
        nlinarith
      · simp [emptyGraph]
        have : 1 ≤ P.γ_ℓ M := hValP.2.2.1 M
        positivity
    · intro _
      simp only [emptyLSF, Finset.card_empty, Nat.cast_zero]
      have : 0 ≤ P.c_R := hValP.2.2.2.2.2.2.2.2.1
      have : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
      positivity
  · intro t ht1 htτ j _
    rw [hL_eq t j, hL_eq (t - 1) j, hS_eq t j, hS_eq (t - 1) j, hUS_eq t j]
    have hGtE := (hG_empty t htτ).2.2
    refine ⟨Finset.Subset.rfl, fun e he => by simp [hGtE] at he,
      fun e he => by simp [hGtE] at he, trivial, rfl⟩
  · intro t _ j _
    simp only [hUS_eq, List.length_nil, Finset.sum_const_zero, Nat.cast_zero, MGraph.batchEnc]
    have hγr : 0 ≤ P.γ_r M := by linarith [hValP.2.2.2.2.2.2.1 M]
    exact ⟨mul_nonneg hγr (Nat.cast_nonneg _), mul_nonneg hγr (by positivity)⟩

/-- Empty-graph `WeakHiddenStable` witness for `sparseCoreBundleTool.coreInstanceOrdAt`. -/
lemma bundleTool_empty_weakHidden
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ) (hV₀ : ¬ (D.G 0).V.Nonempty) (j : ℕ) :
    let T := sparseCoreBundleTool oracle C_lsst L sparsify
    WeakHiddenStable (T.coreInstanceOrdAt k M N D ord j) τ (max Ψ 0)
      (T.coreCOrdAt k M N D ord c j) (T.coreWOrdAt k M N D ord w j) := by
  intro T t _
  have hG_eq : (T.coreInstanceOrdAt k M N D ord j).G t = emptyGraph :=
    (bundleTool_empty_accessors oracle C_lsst L sparsify k M N D ord hV₀ t j).1
  have hSE : ((T.coreInstanceOrdAt k M N D ord j).G t).E = ∅ := by rw [hG_eq]; rfl
  have hSV : ((T.coreInstanceOrdAt k M N D ord j).G t).V = ∅ := by rw [hG_eq]; rfl
  exact ⟨fun v hv => by simp [hSV] at hv,
    ⟨fun v hv => by simp [hSV] at hv, fun e he => by simp [hSE] at he⟩,
    fun e he => by simp [hSE] at he,
    fun e he => by simp [hSE] at he⟩

/-! ## 3. Main Lemma 5.17 theorems for `sparseCoreBundleTool` -/

/-- **Lemma 5.17 without `WeakHiddenStable` on bundle graphs** (paper pages 23–24): proves all five
clauses of `IsSpecOrdNoHiddenUpTo` for `sparseCoreBundleTool` with `bundleCoreParams E` under
`BundleCoreHypsAt` (no degree bound and no `hComp_bound`). -/
theorem bundleLemma_5_17_noHidden_at
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAt E oracle sparsify k M D) :
    let T := sparseCoreBundleTool oracle E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    let st := fun t => (T.runOrdAt k M N D ord t).1
    let U_S := fun t => (T.runOrdAt k M N D ord t).2
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (st t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (st t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ M) (P.γ_c M) M
        (T.S (st t) j) (T.emb (st t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (st t) j).F.R.card : ℝ) ≤
          P.c_R * ((M : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((N : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (st t) j).F.F.E ⊆ (T.lsfs (st (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (st t) j).wstr e = (T.lsfs (st (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (st t) j).wstr e = 1) ∧
      (T.S (st (t - 1)) j).BatchIsValid (U_S t j) ∧
      T.S (st t) j = (T.S (st (t - 1)) j).applyBatch (U_S t j)) ∧
    (∀ t ≤ τ, ∀ j < k,
      (((Finset.Icc 1 t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc 1 t).sum fun s => (T.S (st (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        P.γ_r M * ((M : ℝ) / (k : ℝ) +
          (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
    (∀ j < k, OrderedUpTo (T.coreInstanceOrdAt k M N D ord j) τ 2 (fun t => T.rot (st t) j)) ∧
    ((T.cost (st τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) * (k : ℝ) * ((k : ℝ) + 1) * P.γ_r M *
        (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) := by
  intro T P st U_S
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  have hOrder : ∀ j < k,
      OrderedUpTo (T.coreInstanceOrdAt k M N D ord j) τ 2 (fun t => T.rot (st t) j) :=
    fun j hj => bundleLemma_5_17_orderedUpTo oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify
      hHyps.hLSST k M N τ hk D hG₀ hℓ₀ hD hM hN hThresh hHyps.hSp ord hOrd j hj
  have hCost : (T.cost (st τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) * (k : ℝ) * ((k : ℝ) + 1) * P.γ_r M *
        (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T :=
    sparseCoreBundleTool_cost_le_of_branch E oracle sparsify k M N τ D ord fun hV₀ j hj =>
      bundleRunSeq_cost_le_params_noComp_at
        E oracle sparsify k M N τ D ord hk hG₀ hV₀ hℓ₀ hD hM hN hThresh hOrd hHyps j hj
  by_cases hV₀ : (D.G 0).V.Nonempty
  · have hrun := sparseCoreBundleTool_runOrdAt oracle E.C_lsst E.L sparsify k M N D ord hV₀
    have hLSF := sparseCoreBundleTool_lsf_guarantees_at oracle E.C_lsst E.L sparsify hHyps.hLSST
      k M N τ hk D ord hG₀ hD hℓ hLen
    have hS_eq := bundleTool_S_eq_at oracle E.C_lsst E.L sparsify k M N D ord hV₀
    have hL_eq := bundleTool_lsfs_eq_at oracle E.C_lsst E.L sparsify k M N D ord hV₀
    have hEmb_eq := bundleTool_emb_eq_at oracle E.C_lsst E.L sparsify k M N D ord hV₀
    have hUS_eq : ∀ t, 1 ≤ t → ∀ j, U_S t j =
        (bundleRunSeq oracle E.C_lsst E.L sparsify k M N D ord j t).2 :=
      fun t ht j => (hrun t).2.2.2.2 ht j
    refine ⟨?_, ?_, ?_, hOrder, hCost⟩
    · intro t ht j hj
      have hlsf_tj := hLSF.1 t ht j hj
      have hisSp := bundleRunSeq_isSparsifiedCoreGraphAt_params E oracle sparsify
        k M N τ D ord hk hG₀ hV₀ hD hℓ hLen hM hN hThresh hOrd hHyps j hj t ht
      dsimp only at hisSp
      rw [← hL_eq j t, ← hS_eq j t, ← hEmb_eq j t] at hisSp
      exact ⟨holds_mono_sigma hlsf_tj.1 (le_max_right (1 : ℝ) _), hisSp, fun hConn =>
        bundleTool_connected_root_bound E k M N t D hM hN (hlsf_tj.2 hConn)⟩
    · intro t ht1 htτ j hj
      have h2_lsf := hLSF.2.1 t ht1 htτ j hj
      have hStep := (bundleRunSeq_inv oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify hHyps.hLSST
        k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hHyps.hSp ord hOrd j hj).2.1 t ht1 htτ
      have hUS_info : U_S t j =
          (bundleRunInfo oracle E.C_lsst E.L sparsify k M N D ord j (t - 1)).U_S := by
        obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
        rw [hUS_eq s.succ ht1 j]; rfl
      rw [hUS_info, hS_eq j (t - 1), hS_eq j t]
      exact ⟨h2_lsf.1, h2_lsf.2.1, h2_lsf.2.2, hStep.1, hStep.2.1⟩
    · intro t ht j hj
      have hUS_sum_eq :
          (Finset.Icc 1 t).sum (fun s => (U_S s j).length) =
            (Finset.Icc 1 t).sum (fun s =>
              (bundleRunSeq oracle E.C_lsst E.L sparsify k M N D ord j s).2.length) :=
        Finset.sum_congr rfl fun s hs => by rw [hUS_eq s (Finset.mem_Icc.mp hs).1 j]
      have hEnc_sum_eq :
          (Finset.Icc 1 t).sum (fun s => (T.S (st (s - 1)) j).batchEnc (U_S s j)) =
            (Finset.Icc 1 t).sum (fun s =>
              (bundleRunSeq oracle E.C_lsst E.L sparsify k M N D ord j (s - 1)).1.S_cur.batchEnc
                (bundleRunSeq oracle E.C_lsst E.L sparsify k M N D ord j s).2) :=
        Finset.sum_congr rfl fun s hs => by
          rw [hS_eq j (s - 1), hUS_eq s (Finset.mem_Icc.mp hs).1 j]
      rw [hUS_sum_eq, hEnc_sum_eq]
      exact bundleRunSeq_recourse_and_enc_params_noComp
        E oracle sparsify k M N τ D ord hk hG₀ hV₀ hD hℓ hLen hM hN hThresh hOrd hHyps j hj t ht
  · have hE := bundleTool_empty_clauses E oracle sparsify k τ M N D ord hk hG₀ hV₀ hD
    exact ⟨hE.1, hE.2.1, hE.2.2, hOrder, hCost⟩

/-- Uniform `IsSpecOrdNoHiddenUpTo` packaging of `bundleLemma_5_17_noHidden_at`. -/
theorem bundleLemma_5_17_isSpecOrdNoHiddenUpTo
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hHyps : ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) → OrderedUpTo D τ 2 ord →
      (D.G 0).m ≤ M → (D.G 0).n ≤ N →
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k M N →
      BundleCoreHypsAt E oracle sparsify k M D) :
    (sparseCoreBundleTool oracle E.C_lsst E.L sparsify).IsSpecOrdNoHiddenUpTo
      (bundleCoreParams E) :=
  fun k τ M N D ord hk hG₀ hD hLen hℓ hOrd hM hN hThresh =>
    bundleLemma_5_17_noHidden_at E oracle sparsify k τ M N D ord hk hG₀ hD
      hLen hℓ hOrd hM hN hThresh (hHyps k τ M N D ord hk hG₀ hD hLen hℓ hOrd hM hN hThresh)

/-- **Clauses 1, 2, and 4 of `WeakHiddenStable`** on `coreInstanceOrdAt` for
`sparseCoreBundleTool` (paper Lemma 5.17, item 2, pages 23–24). -/
theorem bundleLemma_5_17_weakHidden_items124_at
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAt E oracle sparsify k M D) :
    let T := sparseCoreBundleTool oracle E.C_lsst E.L sparsify
    ∀ j < k, ∃ Ψ_S : ℝ, ∀ t ≤ τ,
      ((T.coreInstanceOrdAt k M N D ord j).G t).IsCirculation (T.coreCOrdAt k M N D ord c j t) ∧
      IsValidPair ((T.coreInstanceOrdAt k M N D ord j).G t)
        ((T.coreInstanceOrdAt k M N D ord j).ℓ t)
        (T.coreCOrdAt k M N D ord c j t) (T.coreWOrdAt k M N D ord w j t) ∧
      ∀ e' ∈ ((T.coreInstanceOrdAt k M N D ord j).G t).E,
        0 < T.coreWOrdAt k M N D ord w j t e' ∧
        |Real.log (T.coreWOrdAt k M N D ord w j t e')| ≤ Ψ_S ∧
        0 < (T.coreInstanceOrdAt k M N D ord j).ℓ t e' ∧
        |Real.log ((T.coreInstanceOrdAt k M N D ord j).ℓ t e')| ≤ Ψ_S := by
  intro T j hj
  by_cases hV₀ : (D.G 0).V.Nonempty
  · exact ⟨_, bundleRunSeq_weakHidden_items124 oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify
      hHyps.hLSST k M N τ hk D hG₀ hV₀ hD hLen hM hN hThresh hHyps.hSp ord hOrd Ψ c w hWeak j hj⟩
  · have hW := bundleTool_empty_weakHidden oracle E.C_lsst E.L sparsify k M N τ D ord Ψ c w hV₀ j
    exact ⟨max Ψ 0, fun t ht => ⟨(hW t ht).1, (hW t ht).2.1, (hW t ht).2.2.2⟩⟩

/-- **Full Lemma 5.17 on bundle graphs** (paper Lemma 5.17, pages 23–24):
proves all six clauses of `IsSpecOrdUpTo` for `sparseCoreBundleTool` with `bundleCoreParams E`
under `BundleCoreHypsAt` (including `WeakHiddenStable` item 2 and output `OrderedUpTo`, with no
degree bound and no `hComp_bound`). -/
theorem bundleLemma_5_17_at
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAt E oracle sparsify k M D) :
    let T := sparseCoreBundleTool oracle E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    let st := fun t => (T.runOrdAt k M N D ord t).1
    let U_S := fun t => (T.runOrdAt k M N D ord t).2
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (st t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (st t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ M) (P.γ_c M) M
        (T.S (st t) j) (T.emb (st t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (st t) j).F.R.card : ℝ) ≤
          P.c_R * ((M : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((N : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (st t) j).F.F.E ⊆ (T.lsfs (st (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (st t) j).wstr e = (T.lsfs (st (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (st t) j).wstr e = 1) ∧
      (T.S (st (t - 1)) j).BatchIsValid (U_S t j) ∧
      T.S (st t) j = (T.S (st (t - 1)) j).applyBatch (U_S t j)) ∧
    (∀ t ≤ τ, ∀ j < k,
      (((Finset.Icc 1 t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc 1 t).sum fun s => (T.S (st (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        P.γ_r M * ((M : ℝ) / (k : ℝ) +
          (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
    (∀ j < k, ∃ Ψ' : ℝ, WeakHiddenStable (T.coreInstanceOrdAt k M N D ord j) τ Ψ'
      (T.coreCOrdAt k M N D ord c j) (T.coreWOrdAt k M N D ord w j)) ∧
    (∀ j < k, OrderedUpTo (T.coreInstanceOrdAt k M N D ord j) τ 2 (fun t => T.rot (st t) j)) ∧
    ((T.cost (st τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) * (k : ℝ) * ((k : ℝ) + 1) * P.γ_r M *
        (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) := by
  have hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e := fun t ht e he =>
    ((hWeak t ht).2.2.2 e he).2.2.1
  have hNH := bundleLemma_5_17_noHidden_at E oracle sparsify k τ M N D ord
    hk hG₀ hD hLen hℓ hOrd hM hN hThresh hHyps
  refine ⟨hNH.1, hNH.2.1, hNH.2.2.1, ?_, hNH.2.2.2.1, hNH.2.2.2.2⟩
  intro j hj
  by_cases hV₀ : (D.G 0).V.Nonempty
  · exact ⟨_, bundleRunSeq_weakHiddenStable oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify
      hHyps.hLSST k M N τ hk D hG₀ hV₀ hD hLen hM hN hThresh hHyps.hSp ord hOrd Ψ c w hWeak j hj⟩
  · exact ⟨max Ψ 0,
      bundleTool_empty_weakHidden oracle E.C_lsst E.L sparsify k M N τ D ord Ψ c w hV₀ j⟩

/-- Uniform `IsSpecOrdUpTo` packaging of `bundleLemma_5_17_at` (paper Lemma 5.17, pages 23–24). -/
theorem bundleLemma_5_17_isSpecOrdUpTo
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hHyps : ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) → OrderedUpTo D τ 2 ord →
      (D.G 0).m ≤ M → (D.G 0).n ≤ N →
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k M N →
      BundleCoreHypsAt E oracle sparsify k M D) :
    (sparseCoreBundleTool oracle E.C_lsst E.L sparsify).IsSpecOrdUpTo (bundleCoreParams E) :=
  fun k τ M N D ord Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hThresh =>
    bundleLemma_5_17_at E oracle sparsify k τ M N D ord Ψ c w hk hG₀ hD hLen
      hWeak hOrd hM hN hThresh
      (hHyps k τ M N D ord hk hG₀ hD hLen
        (fun t ht e he => ((hWeak t ht).2.2.2 e he).2.2.1) hOrd hM hN hThresh)

/-- Uniform `IsSpecOrdNoHidden` packaging at `((D.G 0).m, (D.G 0).n)`. -/
theorem bundleLemma_5_17_isSpecOrdNoHidden
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hHyps : ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) → OrderedUpTo D τ 2 ord →
      (D.G 0).m ≤ M → (D.G 0).n ≤ N →
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k M N →
      BundleCoreHypsAt E oracle sparsify k M D) :
    (sparseCoreBundleTool oracle E.C_lsst E.L sparsify).IsSpecOrdNoHidden (bundleCoreParams E) :=
  (bundleLemma_5_17_isSpecOrdNoHiddenUpTo E oracle sparsify
    hHyps).toIsSpecOrdNoHidden

/-- Uniform `IsSpecOrd` packaging at `((D.G 0).m, (D.G 0).n)`. -/
theorem bundleLemma_5_17_isSpecOrd
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hHyps : ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) → OrderedUpTo D τ 2 ord →
      (D.G 0).m ≤ M → (D.G 0).n ≤ N →
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k M N →
      BundleCoreHypsAt E oracle sparsify k M D) :
    (sparseCoreBundleTool oracle E.C_lsst E.L sparsify).IsSpecOrd (bundleCoreParams E) :=
  (bundleLemma_5_17_isSpecOrdUpTo E oracle sparsify hHyps).toIsSpecOrd

/-- When `∀ m, m ≤ E.B_fn m`, `BundleCoreHypsAt` holds for every instance directly from the
LSST and sparsifier specifications, giving `IsSpecOrdNoHiddenUpTo`. -/
theorem bundleLemma_5_17_isSpecOrdNoHiddenUpTo_of_B_ge_m
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle E.C_lsst)
    (hSp : ∀ m, SparsifySpec m (E.P_fn m) (sparsify m))
    (hBm : ∀ m, m ≤ E.B_fn m) :
    (sparseCoreBundleTool oracle E.C_lsst E.L sparsify).IsSpecOrdNoHiddenUpTo
      (bundleCoreParams E) :=
  bundleLemma_5_17_isSpecOrdNoHiddenUpTo E oracle sparsify
    (fun _ _ M _ _ _ _ _ _ _ _ _ hM _ _ =>
      bundleCoreHypsAt_of_B_ge_m hLSST (hSp M) (le_trans hM (hBm M)))

/-- When `∀ m, m ≤ E.B_fn m`, `BundleCoreHypsAt` holds for every instance directly from the
LSST and sparsifier specifications, giving `IsSpecOrdUpTo`. -/
theorem bundleLemma_5_17_isSpecOrdUpTo_of_B_ge_m
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle E.C_lsst)
    (hSp : ∀ m, SparsifySpec m (E.P_fn m) (sparsify m))
    (hBm : ∀ m, m ≤ E.B_fn m) :
    (sparseCoreBundleTool oracle E.C_lsst E.L sparsify).IsSpecOrdUpTo (bundleCoreParams E) :=
  bundleLemma_5_17_isSpecOrdUpTo E oracle sparsify
    (fun _ _ M _ _ _ _ _ _ _ _ _ hM _ _ =>
      bundleCoreHypsAt_of_B_ge_m hLSST (hSp M) (le_trans hM (hBm M)))

end

end MinCostFlow.SparseCore
