module

public import MinCostFlow.SparseCore.BundleLemma517
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ordered Side Predicates, `BundleCoreHyps` Corollaries, and Exponent Arithmetic

This file proves the companion results to `BundleLemma517.lean` (paper Lemma 5.17, pages 23–24):
* `bundleLemma_5_17_mwu_at` / `bundleLemma_5_17_mwu`: **unconditional** Lemma 5.5 MWU average
  stretch bound along `runOrdAt` / `runOrd` under `(D.G 0).m + 2 ≤ ((D.G 0).n + 2) ^ μ`.
* `bundleLemma_5_17_embedsSurviving_at` / `bundleLemma_5_17_embedsSurviving`
  (`ToolEmbedsSurvivingOrdUpTo`) and its `Ord` / `NoHidden` variants: **unconditional**.
* `bundleLemma_5_17_noReinsert_at` / `bundleLemma_5_17_toolNoReinsertOrdUpTo`
  (`ToolNoReinsertOrdUpTo`) and its `Ord` / `NoHidden` variants: **unconditional** surviving-edge
  insertion propagation (using `bundleRunInv_uncond`).
* `bundleLemma_5_17_switchedRecourse_mul_k`: switched-branch recourse with a factor of `k`.
* `bundleLemma_5_17_noHidden_inst` / `bundleLemma_5_17_inst`: specializations at
  `((D.G 0).m, (D.G 0).n)` under `BundleCoreHyps` / `BundleInstanceHyps`.
* `bundleLemma_5_17_exponent_arithmetic`: balancing `L` gives `8/9` for the paper's `log^{2/3}`
  sparsifier and `23/24` (`7/8 + 2/24 = 23/24`) for Theorem 8.6's `exp(O(log^{7/8} m))` bound.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow
open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

/-! ## 1. Unconditional ordered side predicates (`ToolMWUOrd`, `ToolEmbedsSurvivingOrd`, `ToolNoReinsertOrd`) -/

/-- **Lemma 5.5 MWU average stretch bound along `runOrdAt`** (paper page 18), using
`((D.G 0).m : ℝ) + 2 ≤ (((D.G 0).n : ℝ) + 2) ^ μ`. Unconditional beyond `HasLSSTSpec`. -/
theorem bundleLemma_5_17_mwu_at (C_lsst : ℝ) (L μ : ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    {k M N τ : ℕ} {D : DynamicInstance} (ord : ℕ → ℕ → List End)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) (hLen : LengthsStable D τ)
    (hM_poly : ((D.G 0).m : ℝ) + 2 ≤ (((D.G 0).n : ℝ) + 2) ^ μ) :
    let T := sparseCoreBundleTool oracle C_lsst L sparsify
    let σ_mwu := fun n => (μ : ℝ) * (26 * mwuK0 C_lsst + 128) * (Real.log ((n : ℝ) + 2)) ^ 7
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.runOrdAt k M N D ord t).1 j).wstr e) / (k : ℝ) ≤
        σ_mwu (D.G t).n := by
  intro T σ_mwu t ht e he
  have hLSF := sparseCoreBundleTool_lsf_guarantees_at oracle C_lsst L sparsify hLSST
    k M N τ hk D ord hG₀ hD hℓ hLen
  have hraw := hLSF.2.2 t ht e he
  have hV_sub : (D.G 0).V ⊆ (D.G t).V := dyn_G_V_sub hD (Nat.zero_le t) ht
  have hn_le : ((D.G 0).n : ℝ) ≤ ((D.G t).n : ℝ) := by exact_mod_cast Finset.card_le_card hV_sub
  have hlog_n0 : 0 ≤ Real.log (((D.G 0).n : ℝ) + 2) := by
    linarith [half_lt_log_add_two (D.G 0).n]
  have hlog_nt : Real.log (((D.G 0).n : ℝ) + 2) ≤ Real.log (((D.G t).n : ℝ) + 2) :=
    Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) (D.G 0).n]) (by linarith)
  have hlog_m : Real.log (((D.G 0).m : ℝ) + 2) ≤ (μ : ℝ) * Real.log (((D.G t).n : ℝ) + 2) := by
    have hm_pos : (0 : ℝ) < ((D.G 0).m : ℝ) + 2 := by
      linarith [Nat.cast_nonneg (α := ℝ) (D.G 0).m]
    calc Real.log (((D.G 0).m : ℝ) + 2)
        ≤ Real.log ((((D.G 0).n : ℝ) + 2) ^ μ) := Real.log_le_log hm_pos hM_poly
      _ = (μ : ℝ) * Real.log (((D.G 0).n : ℝ) + 2) := Real.log_pow _ _
      _ ≤ (μ : ℝ) * Real.log (((D.G t).n : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hlog_nt (Nat.cast_nonneg μ)
  have hK₀ : 0 ≤ 26 * mwuK0 C_lsst + 128 := by linarith [mwuK0_pos C_lsst]
  have hpow6 : (Real.log (((D.G 0).n : ℝ) + 2)) ^ 6 ≤ (Real.log (((D.G t).n : ℝ) + 2)) ^ 6 :=
    pow_le_pow_left₀ hlog_n0 hlog_nt 6
  have hmul : (26 * mwuK0 C_lsst + 128) * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 6 *
        Real.log (((D.G 0).m : ℝ) + 2) ≤
      (μ : ℝ) * (26 * mwuK0 C_lsst + 128) * (Real.log (((D.G t).n : ℝ) + 2)) ^ 7 := by
    have hlog_m_nn : 0 ≤ Real.log (((D.G 0).m : ℝ) + 2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (D.G 0).m])
    have hp := mul_le_mul (mul_le_mul_of_nonneg_left hpow6 hK₀) hlog_m hlog_m_nn (by positivity)
    have hEq : (26 * mwuK0 C_lsst + 128) * (Real.log (((D.G t).n : ℝ) + 2)) ^ 6 *
        ((μ : ℝ) * Real.log (((D.G t).n : ℝ) + 2)) =
        (μ : ℝ) * (26 * mwuK0 C_lsst + 128) * (Real.log (((D.G t).n : ℝ) + 2)) ^ 7 := by ring
    exact le_trans hp (le_of_eq hEq)
  exact le_trans hraw hmul

/-- Lemma 5.5 MWU average stretch bound along `runOrd` (at `((D.G 0).m, (D.G 0).n)`). -/
theorem bundleLemma_5_17_mwu (C_lsst : ℝ) (L μ : ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    {k τ : ℕ} {D : DynamicInstance} (ord : ℕ → ℕ → List End)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) (hLen : LengthsStable D τ)
    (hM_poly : ((D.G 0).m : ℝ) + 2 ≤ (((D.G 0).n : ℝ) + 2) ^ μ) :
    let T := sparseCoreBundleTool oracle C_lsst L sparsify
    let σ_mwu := fun n => (μ : ℝ) * (26 * mwuK0 C_lsst + 128) * (Real.log ((n : ℝ) + 2)) ^ 7
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.runOrd k D ord t).1 j).wstr e) / (k : ℝ) ≤
        σ_mwu (D.G t).n :=
  bundleLemma_5_17_mwu_at C_lsst L μ oracle sparsify hLSST ord hk hG₀ hD hℓ hLen hM_poly

/-- Unconditional pointwise surviving-edge self-embedding for `sparseCoreBundleTool`, handling both
nonempty and empty initial graphs. -/
theorem bundleLemma_5_17_embedsSurviving_at
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (t j : ℕ) (e : ℕ)
    (he : e ∈ ((sparseCoreBundleTool oracle C_lsst L sparsify).S
      ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1 j).E) :
    (sparseCoreBundleTool oracle C_lsst L sparsify).emb
      ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1 j e =
      [(e, true)] := by
  by_cases hV₀ : (D.G 0).V.Nonempty
  · exact bundleCore_embedsSurviving_at oracle C_lsst L sparsify k M N D ord hV₀ t j e he
  · have hS0 := (bundleTool_empty_accessors oracle C_lsst L sparsify k M N D ord hV₀ t j).1
    rw [hS0] at he
    simp [emptyGraph] at he

/-- Unconditional global `ToolEmbedsSurvivingOrdUpTo` for `sparseCoreBundleTool`. -/
theorem bundleLemma_5_17_embedsSurviving
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) :
    (sparseCoreBundleTool oracle C_lsst L sparsify).ToolEmbedsSurvivingOrdUpTo :=
  fun k _ M N D ord _ _ _ _ _ _ _ _ _ _ _ _ t _ j _ e he =>
    bundleLemma_5_17_embedsSurviving_at oracle C_lsst L sparsify k M N D ord t j e he

/-- Unconditional global `ToolEmbedsSurvivingOrd` for `sparseCoreBundleTool`. -/
theorem bundleLemma_5_17_embedsSurvivingOrd
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) :
    (sparseCoreBundleTool oracle C_lsst L sparsify).ToolEmbedsSurvivingOrd :=
  (bundleLemma_5_17_embedsSurviving oracle C_lsst L sparsify).toToolEmbedsSurvivingOrd

/-- Unconditional global `ToolEmbedsSurvivingOrdNoHiddenUpTo` for `sparseCoreBundleTool`. -/
theorem bundleLemma_5_17_embedsSurvivingNoHiddenUpTo
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) :
    (sparseCoreBundleTool oracle C_lsst L sparsify).ToolEmbedsSurvivingOrdNoHiddenUpTo :=
  (bundleLemma_5_17_embedsSurviving oracle C_lsst L sparsify).toNoHidden

/-- Unconditional global `ToolEmbedsSurvivingOrdNoHidden` for `sparseCoreBundleTool`. -/
theorem bundleLemma_5_17_embedsSurvivingNoHidden
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) :
    (sparseCoreBundleTool oracle C_lsst L sparsify).ToolEmbedsSurvivingOrdNoHidden :=
  (bundleLemma_5_17_embedsSurvivingNoHiddenUpTo oracle C_lsst L sparsify).toToolEmbedsSurvivingOrdNoHidden

/-- Unconditional pointwise surviving-edge non-insertion propagation for `sparseCoreBundleTool`,
handling both nonempty and empty initial graphs. -/
theorem bundleLemma_5_17_noReinsert_at
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord)
    (t : ℕ) (ht1 : 1 ≤ t) (htτ : t ≤ τ) (j : ℕ) (hj : j < k) :
    let T := sparseCoreBundleTool oracle C_lsst L sparsify
    ∀ e ∈ (T.S (T.runOrdAt k M N D ord (t - 1)).1 j).E,
      e ∈ (T.S (T.runOrdAt k M N D ord t).1 j).E →
      (∀ u ∈ (T.runOrdAt k M N D ord t).2 j, ¬ u.Inserts e) →
      ∀ u ∈ D.U t, ¬ u.Inserts e := by
  by_cases hV₀ : (D.G 0).V.Nonempty
  · exact bundleCore_noReinsert_step_at oracle C_lsst L hL P_b sparsify hLSST k M N τ hk D
      hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp ord hOrd t ht1 htτ j hj
  · intro T e he _ _
    have hS0 := (bundleTool_empty_accessors oracle C_lsst L sparsify k M N D ord hV₀ (t - 1) j).1
    rw [hS0] at he
    simp [emptyGraph] at he

/-- Unconditional global `ToolNoReinsertOrdUpTo` for `sparseCoreBundleTool` when `sparsify m`
satisfies `SparsifySpec m (P_fn m)` for every `m`. -/
theorem bundleLemma_5_17_toolNoReinsertOrdUpTo
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_fn : ℕ → SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (hSp : ∀ m, SparsifySpec m (P_fn m) (sparsify m)) :
    (sparseCoreBundleTool oracle C_lsst L sparsify).ToolNoReinsertOrdUpTo := by
  intro k τ M N D ord Ψ c w hk hG₀ hD _ hWeak hOrd hM hN hThresh t ht1 htτ j hj
  exact bundleLemma_5_17_noReinsert_at oracle C_lsst L hL (P_fn M) sparsify hLSST k M N τ hk D
    hG₀ (fun e he => ((hWeak 0 (Nat.zero_le τ)).2.2.2 e he).2.2.1) hD hM hN hThresh (hSp M)
    ord hOrd t ht1 htτ j hj

/-- Unconditional global `ToolNoReinsertOrd` for `sparseCoreBundleTool`. -/
theorem bundleLemma_5_17_toolNoReinsertOrd
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_fn : ℕ → SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (hSp : ∀ m, SparsifySpec m (P_fn m) (sparsify m)) :
    (sparseCoreBundleTool oracle C_lsst L sparsify).ToolNoReinsertOrd :=
  (bundleLemma_5_17_toolNoReinsertOrdUpTo oracle C_lsst L hL P_fn sparsify hLSST
    hSp).toToolNoReinsertOrd

/-- Unconditional global `ToolNoReinsertOrdNoHiddenUpTo` for `sparseCoreBundleTool`. -/
theorem bundleLemma_5_17_toolNoReinsertOrdNoHiddenUpTo
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_fn : ℕ → SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (hSp : ∀ m, SparsifySpec m (P_fn m) (sparsify m)) :
    (sparseCoreBundleTool oracle C_lsst L sparsify).ToolNoReinsertOrdNoHiddenUpTo :=
  (bundleLemma_5_17_toolNoReinsertOrdUpTo oracle C_lsst L hL P_fn sparsify hLSST hSp).toNoHidden

/-- Unconditional global `ToolNoReinsertOrdNoHidden` for `sparseCoreBundleTool`. -/
theorem bundleLemma_5_17_toolNoReinsertOrdNoHidden
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_fn : ℕ → SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (hSp : ∀ m, SparsifySpec m (P_fn m) (sparsify m)) :
    (sparseCoreBundleTool oracle C_lsst L sparsify).ToolNoReinsertOrdNoHidden :=
  (bundleLemma_5_17_toolNoReinsertOrdNoHiddenUpTo oracle C_lsst L hL P_fn sparsify hLSST
    hSp).toToolNoReinsertOrdNoHidden

/-! ## 2. Switched recourse, `BundleCoreHyps` specializations, and exponent arithmetic -/

/-- Switched-branch recourse bound with a factor of `k` for `sparseCoreBundleTool`. -/
theorem bundleLemma_5_17_switchedRecourse_mul_k
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k τ M N : ℕ} {D : DynamicInstance} {ord : ℕ → ℕ → List End} (b : ℕ → ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAt E oracle sparsify k M D)
    (hb : ∀ s, b s < k) :
    let T := sparseCoreBundleTool oracle E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    ∀ t ≤ τ,
      (((Finset.Icc 1 t).sum fun s => ((T.runOrdAt k M N D ord s).2 (b s)).length : ℕ) : ℝ) ≤
        (k : ℝ) * P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) := by
  intro T P
  have hNH := bundleLemma_5_17_noHidden_at E oracle sparsify k τ M N D ord
    hk hG₀ hD hLen hℓ hOrd hM hN hThresh hHyps
  exact SparseCoreTool.isSpecOrdUpTo_switched_recourse_mul_k (T := T) (P := P) b hb
    (fun j hj t ht => (hNH.2.2.1 t ht j hj).1)

/-- Specialization of `bundleLemma_5_17_noHidden_at` at `((D.G 0).m, (D.G 0).n)` under
`BundleCoreHyps`. -/
theorem bundleLemma_5_17_noHidden_inst
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n)
    (hHyps : BundleCoreHyps E oracle sparsify k τ D) :
    let T := sparseCoreBundleTool oracle E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    let st := fun t => (T.runOrd k D ord t).1
    let U_S := fun t => (T.runOrd k D ord t).2
    let m₀ := (D.G 0).m
    let n₀ := (D.G 0).n
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (st t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (st t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ m₀) (P.γ_c m₀) m₀
        (T.S (st t) j) (T.emb (st t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (st t) j).F.R.card : ℝ) ≤
          P.c_R * ((m₀ : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((n₀ : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (st t) j).F.F.E ⊆ (T.lsfs (st (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (st t) j).wstr e = (T.lsfs (st (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (st t) j).wstr e = 1) ∧
      (T.S (st (t - 1)) j).BatchIsValid (U_S t j) ∧
      T.S (st t) j = (T.S (st (t - 1)) j).applyBatch (U_S t j)) ∧
    (∀ t ≤ τ, ∀ j < k,
      (((Finset.Icc 1 t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r m₀ * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc 1 t).sum fun s => (T.S (st (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        P.γ_r m₀ * ((m₀ : ℝ) / (k : ℝ) +
          (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
    (∀ j < k, OrderedUpTo (T.coreInstanceOrd k D ord j) τ 2 (fun t => T.rot (st t) j)) ∧
    ((T.cost (st τ) : ℝ) ≤
      P.c_T * ((m₀ : ℝ) + 1) * (k : ℝ) * ((k : ℝ) + 1) * P.γ_r m₀ *
        (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ P.p_T) :=
  bundleLemma_5_17_noHidden_at E oracle sparsify k τ (D.G 0).m (D.G 0).n D
    ord hk hG₀ hD hLen hℓ hOrd le_rfl le_rfl hThresh hHyps

/-- Specialization of `bundleLemma_5_17_at` at `((D.G 0).m, (D.G 0).n)` under
`BundleCoreHyps`. -/
theorem bundleLemma_5_17_inst
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n)
    (hHyps : BundleCoreHyps E oracle sparsify k τ D) :
    let T := sparseCoreBundleTool oracle E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    let st := fun t => (T.runOrd k D ord t).1
    let U_S := fun t => (T.runOrd k D ord t).2
    let m₀ := (D.G 0).m
    let n₀ := (D.G 0).n
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (st t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (st t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ m₀) (P.γ_c m₀) m₀
        (T.S (st t) j) (T.emb (st t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (st t) j).F.R.card : ℝ) ≤
          P.c_R * ((m₀ : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((n₀ : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (st t) j).F.F.E ⊆ (T.lsfs (st (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (st t) j).wstr e = (T.lsfs (st (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (st t) j).wstr e = 1) ∧
      (T.S (st (t - 1)) j).BatchIsValid (U_S t j) ∧
      T.S (st t) j = (T.S (st (t - 1)) j).applyBatch (U_S t j)) ∧
    (∀ t ≤ τ, ∀ j < k,
      (((Finset.Icc 1 t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r m₀ * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc 1 t).sum fun s => (T.S (st (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        P.γ_r m₀ * ((m₀ : ℝ) / (k : ℝ) +
          (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
    (∀ j < k, ∃ Ψ' : ℝ, WeakHiddenStable (T.coreInstanceOrd k D ord j) τ Ψ'
      (T.coreCOrd k D ord c j) (T.coreWOrd k D ord w j)) ∧
    (∀ j < k, OrderedUpTo (T.coreInstanceOrd k D ord j) τ 2 (fun t => T.rot (st t) j)) ∧
    ((T.cost (st τ) : ℝ) ≤
      P.c_T * ((m₀ : ℝ) + 1) * (k : ℝ) * ((k : ℝ) + 1) * P.γ_r m₀ *
        (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ P.p_T) :=
  bundleLemma_5_17_at E oracle sparsify k τ (D.G 0).m (D.G 0).n D ord Ψ c w
    hk hG₀ hD hLen hWeak hOrd le_rfl le_rfl hThresh hHyps

/-- Balancing `m^{1/L}` against `γ^{L²}` in Theorem 8.2 / Lemma 5.17 (paper pages 23–24):
* With Theorem 8.1's paper bound `γ = exp(O(log^{2/3} m log log m))` and `L = Θ(log^{1/9} m)`,
  both `m^{1/L}` and `γ^{O(L²)}` have exponent `2/3 + 2/9 = 8/9 = 1 - 1/9`.
* With Theorem 8.6's formalized bound `γ = exp(O(log^{7/8} m))` and `L = Θ(log^{1/24} m)`,
  both `m^{1/L}` and `γ^{O(L²)}` have exponent `7/8 + 2/24 = 23/24 = 1 - 1/24`. -/
theorem bundleLemma_5_17_exponent_arithmetic :
    (1 : ℚ) - 1 / 9 = 8 / 9 ∧ (2 : ℚ) / 3 + 2 * (1 / 9) = 8 / 9 ∧
    (1 : ℚ) - 1 / 24 = 23 / 24 ∧ (7 : ℚ) / 8 + 2 * (1 / 24) = 23 / 24 := by
  norm_num

end

end MinCostFlow.SparseCore
