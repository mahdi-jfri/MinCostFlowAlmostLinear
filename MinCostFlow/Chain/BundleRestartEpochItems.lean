module

public import MinCostFlow.Chain.BundleRestartEpochMetrics
public import MinCostFlow.SparseCore.BundleCoreParamsWith
import MinCostFlow.SparseCore.BundleMetrics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Items 1–3 (Non-Cost) of `IsSpecOrdRestart` for `sparseCoreBundleRestartTool`

Proves `bundleRestart_spec_item1`, `bundleRestart_spec_item2`, and
`bundleRestart_spec_item3_nonCost` on nonempty initial graphs, using `bundleCoreParams E` under
`BundleCoreHypsAt` (no input degree bound and no `hComp_bound`).
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.LSF
open MinCostFlow.Bundle

/-- Item 1 of `IsSpecOrdRestart` for `sparseCoreBundleRestartTool` on a nonempty initial graph:
the LSF bounds, the sparsified core graph property (`IsSparsifiedCoreGraphAt`), and the connected
root count at every stage `t ≤ τ`. -/
theorem bundleRestart_spec_item1 (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (_hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D)
    (hV₀ : (D.G 0).V.Nonempty) :
    let T := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    let post := fun t => T.runOrdAfterRestarts k M N D ord restarts t
    ∀ t ≤ τ, ∀ j < k,
      (T.lsfs (post t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (post t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ M) (P.γ_c M) M
        (T.S (post t) j) (T.emb (post t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (post t) j).F.R.card : ℝ) ≤
          P.c_R * ((M : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((N : ℝ) + 2)) ^ 2 + 1)) := by
  intro T P post
  have hValP := bundleCoreParams_valid E
  have hk1 : 1 ≤ k := hk
  have hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e := fun t ht e he =>
    ((hWeak t ht).2.2.2 e he).2.2.1
  have hne : ∀ s, (post s).isNonempty = true := fun s =>
    (runOrdAfterRestarts_isNonempty lsfInit E.C_lsst E.L sparsify k M N D ord restarts s).2.1.trans
      (decide_eq_true hV₀)
  intro t ht j hj
  have hInit_j := hHyps.hInit j hj
  have hLSF := sparseCoreBundleRestartToolWith_lsf_guarantees_branch lsfInit E.C_lsst E.L sparsify
    k M N τ hk1 D ord restarts hG₀ hD hℓ hLen hInit_j
  have hlsf_tj := hLSF.1 t ht
  have hholds := holds_mono_sigma hlsf_tj.1 (le_max_right (1 : ℝ) _)
  set s₀ := bundleLastRestart restarts j t
  have hs₀ := bundleLastRestart_spec restarts j t
  have hNoR : ∀ r, s₀ < r → r < t → j ∉ restarts r := fun r h1 h2 => hs₀.2.2 r h1 h2.le
  have hSp_core := epochBundleSeq_isSparsifiedCoreGraph lsfInit E.C_lsst E.L E.hL (E.P_fn M)
    sparsify k M N τ hk1 D ord restarts hM hN hHyps.hSp hG₀ hV₀ hD hℓ hLen hOrd
    hThresh s₀ t j hInit_j hs₀.1 ht hs₀.2.1 hNoR (δ := t - s₀) le_rfl
  have hep_post : epochBundleSeq lsfInit E.C_lsst E.L sparsify k M N D ord restarts s₀ t j (t - s₀) =
      (post t).trees j := by
    refine (epochBundleSeq_eq_post lsfInit E.C_lsst E.L sparsify k M N D ord restarts s₀ t j hs₀.1).2.1 ?_
    by_cases hlt : s₀ < t
    · exact Or.inl (hs₀.2.2 t hlt le_rfl)
    · exact Or.inr (by omega)
  have hst_add : s₀ + (t - s₀) = t := by omega
  dsimp only at hSp_core
  rw [hep_post, hst_add] at hSp_core
  have hL_pt : T.lsfs (post t) j = ((post t).trees j).cs.lsf := by
    dsimp only [T]; exact sparseCoreBundleRestartTool_lsfs_of_nonempty (hne t) j
  have hS_pt : T.S (post t) j = ((post t).trees j).S_cur := by
    dsimp only [T]; rw [sparseCoreBundleRestartTool_S_eq, ite_eq_left (hne t)]
  have hEmb_pt : T.emb (post t) j = ((post t).trees j).emb := by
    dsimp only [T]; rw [sparseCoreBundleRestartTool_emb_eq, ite_eq_left (hne t)]
  rw [← hL_pt, ← hS_pt, ← hEmb_pt] at hSp_core
  have hlen : ((T.emb (post t) j).length (coreGraph (D.G t) (T.lsfs (post t) j)) : ℝ) ≤
      P.γ_ℓ M :=
    le_trans hSp_core.2.2.2.1 (le_max_left _ _)
  have hcong : (T.emb (post t) j).econg (coreGraph (D.G t) (T.lsfs (post t) j))
      (T.S (post t) j) (fun _ => 1) (fun _ => 1) ≤ (k : ℝ) * P.γ_c M := by
    have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have h1 : 1 + coreE82Cong E.L (E.P_fn M) * (k : ℝ) ≤
        (k : ℝ) * (1 + coreE82Cong E.L (E.P_fn M)) := by nlinarith
    exact le_trans hSp_core.2.2.2.2.1 h1
  have hcard : ((T.S (post t) j).E.card : ℝ) ≤ (M : ℝ) * P.γ_ℓ M / (k : ℝ) := by
    have hC := hSp_core.2.2.2.2.2 (E.B_fn M) (hHyps.activeBuckets_card_le (N := N) hj)
    have hsf_nn := bundleParams_sizeFactor_nonneg E.L (E.P_fn M) M (E.B_fn M)
    have hsf_le : bundleSizeFactor E.L (E.P_fn M) M (E.B_fn M) ≤ P.γ_ℓ M :=
      le_trans (by linarith) (le_max_right (coreE82Len E.L (E.P_fn M)) _)
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    have hm_nn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    exact le_trans hC (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsf_le hm_nn) (le_of_lt hk_pos) |>.trans_eq (by ring))
  have hR_le : (∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
      ((T.lsfs (post t) j).F.R.card : ℝ) ≤ P.c_R * ((M : ℝ) / (k : ℝ) +
        (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
          (Real.log ((N : ℝ) + 2)) ^ 2 + 1) := by
    intro hConn
    have hbase := hlsf_tj.2 hConn
    have hm₀M : ((D.G 0).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hn₀N : ((D.G 0).n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h1 : ((D.G 0).m : ℝ) / (k : ℝ) ≤ (M : ℝ) / (k : ℝ) :=
      div_le_div_of_nonneg_right hm₀M (by positivity)
    have hlogn : 0 ≤ Real.log (((D.G 0).n : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hlogn_le : Real.log (((D.G 0).n : ℝ) + 2) ≤ Real.log ((N : ℝ) + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have hsq_le : Real.log (((D.G 0).n : ℝ) + 2) ^ 2 ≤ Real.log ((N : ℝ) + 2) ^ 2 :=
      pow_le_pow_left₀ hlogn hlogn_le 2
    have h2 : (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
          Real.log (((D.G 0).n : ℝ) + 2) ^ 2 ≤
        (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
          Real.log ((N : ℝ) + 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq_le (Nat.cast_nonneg _)
    have hcR : (0 : ℝ) ≤ P.c_R := hValP.2.2.2.2.2.2.2.2.1
    refine le_trans hbase (mul_le_mul_of_nonneg_left ?_ hcR)
    linarith
  exact ⟨hholds, ⟨hSp_core.1, hSp_core.2.1, hSp_core.2.2.1, hlen, hcong, hcard⟩, hR_le⟩

/-- Item 2 of `IsSpecOrdRestart` for `sparseCoreBundleRestartTool` on a nonempty initial graph:
decremental forest, stretch immutability/reset, and `applyBatch` step from `post (t - 1)` to
`pre t`. -/
theorem bundleRestart_spec_item2 (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (_hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D)
    (hV₀ : (D.G 0).V.Nonempty) :
    let T := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    let pre := fun t => (T.runOrdAfterUpdate k M N D ord restarts t).1
    let U_S := fun t => (T.runOrdAfterUpdate k M N D ord restarts t).2
    let post := fun t => T.runOrdAfterRestarts k M N D ord restarts t
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (post t) j).F.F.E ⊆ (T.lsfs (post (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (post t) j).wstr e = (T.lsfs (post (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (post t) j).wstr e = 1) ∧
      (T.S (post (t - 1)) j).BatchIsValid (U_S t j) ∧
      T.S (pre t) j = (T.S (post (t - 1)) j).applyBatch (U_S t j) := by
  intro T pre U_S post
  have hk1 : 1 ≤ k := hk
  have hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e := fun t ht e he =>
    ((hWeak t ht).2.2.2 e he).2.2.1
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  have hne : ∀ s, (post s).isNonempty = true := fun s =>
    (runOrdAfterRestarts_isNonempty lsfInit E.C_lsst E.L sparsify k M N D ord restarts s).2.1.trans
      (decide_eq_true hV₀)
  intro t ht1 htτ j hj
  have hInit_j := hHyps.hInit j hj
  have hLSF := sparseCoreBundleRestartToolWith_lsf_guarantees_branch lsfInit E.C_lsst E.L sparsify
    k M N τ hk1 D ord restarts hG₀ hD hℓ hLen hInit_j
  have hlsf_step := hLSF.2 t ht1 htτ
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at hlsf_step ⊢
  set s₀ := bundleLastRestart restarts j s
  have hs₀ := bundleLastRestart_spec restarts j s
  have hNoR : ∀ r, s₀ < r → r < s + 1 → j ∉ restarts r := fun r h1 h2 => hs₀.2.2 r h1 (by omega)
  have hStp := epochBundleSeq_step_spec lsfInit E.C_lsst E.L E.hL (E.P_fn M) sparsify
    k M N τ hk1 D ord restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ (s + 1) j hInit_j
    (by omega) htτ hs₀.2.1 hNoR (s - s₀) (by omega)
  have hStep := (epochBundleSeq_steps lsfInit E.C_lsst E.L sparsify
    k M N D ord restarts hV₀ s₀ (s + 1) j (by omega) hNoR).2 (s - s₀) (by omega)
  have hprev : epochBundleSeq lsfInit E.C_lsst E.L sparsify k M N D ord restarts s₀ (s + 1) j (s - s₀) =
      (post s).trees j := by
    have h1 := (epochBundleSeq_eq_post lsfInit E.C_lsst E.L sparsify k M N D ord restarts s₀ (s + 1) j
      (by omega)).1 (s - s₀) (by omega)
    rw [show s₀ + (s - s₀) = s by omega] at h1
    exact h1
  have hcur : epochBundleSeq lsfInit E.C_lsst E.L sparsify k M N D ord restarts s₀ (s + 1) j (s - s₀ + 1) =
      (pre (s + 1)).trees j := by
    have h2 := (epochBundleSeq_eq_post lsfInit E.C_lsst E.L sparsify k M N D ord restarts s₀ (s + 1) j
      (by omega)).2.2 (by omega)
    rw [show s + 1 - s₀ = s - s₀ + 1 by omega] at h2
    exact h2
  have hUS : U_S (s + 1) j =
      (stepBundleTree sparsify ((post s).trees j) (D.U (s + 1)) (ord s) (ord (s + 1))).U_S := by
    have := hStep.2
    rw [show s₀ + (s - s₀) = s by omega, hprev] at this
    exact this
  have hBV : (T.S (post s) j).BatchIsValid (U_S (s + 1) j) := by
    dsimp only [T, post] at hne ⊢
    rw [sparseCoreBundleRestartTool_S_eq, ite_eq_left (hne s), hUS, ← hprev]
    rw [show s₀ + (s - s₀) = s by omega] at hStp
    exact hStp.1
  have hApp : T.S (pre (s + 1)) j = (T.S (post s) j).applyBatch (U_S (s + 1) j) := by
    have hne_pre : (pre (s + 1)).isNonempty = true :=
      (runOrdAfterRestarts_isNonempty lsfInit E.C_lsst E.L sparsify k M N D ord restarts (s + 1)).1.trans
        (decide_eq_true hV₀)
    dsimp only [T, pre, post] at hne hne_pre ⊢
    rw [sparseCoreBundleRestartTool_S_eq, ite_eq_left hne_pre,
      sparseCoreBundleRestartTool_S_eq, ite_eq_left (hne s), hUS, ← hcur, ← hprev]
    rw [show s₀ + (s - s₀) = s by omega] at hStp
    exact hStp.2.1
  exact ⟨hlsf_step.1, hlsf_step.2.1, hlsf_step.2.2, hBV, hApp⟩

/-- The non-cost part of item 3 of `IsSpecOrdRestart` for `sparseCoreBundleRestartToolWith`:
restarting branch `j'` preserves all `lsfs`, preserves `S`, `emb`, and `rot` on every other branch
`b ≠ j'`, and does not decrease `cost`. -/
theorem bundleRestart_spec_item3_nonCost (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ) :
    let T := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    let pre := fun t => (T.runOrdAfterUpdate k M N D ord restarts t).1
    ∀ r ≤ τ, ∀ (p : List ℕ) (j' : ℕ), p ++ [j'] <+: restarts r →
      let st' := p.foldl T.restart (pre r)
      (∀ b < k, T.lsfs (T.restart st' j') b = T.lsfs st' b) ∧
      (∀ b < k, b ≠ j' →
        T.S (T.restart st' j') b = T.S st' b ∧
        T.emb (T.restart st' j') b = T.emb st' b ∧
        T.rot (T.restart st' j') b = T.rot st' b) ∧
      T.cost st' ≤ T.cost (T.restart st' j') := by
  intro T pre r _ p j' _ st'
  exact ⟨fun b _ => sparseCoreBundleRestartTool_restart_lsfs lsfInit E.C_lsst E.L sparsify st' j' b,
    fun b _ hbj => (sparseCoreBundleRestartTool_restart_other lsfInit E.C_lsst E.L sparsify st' hbj).2,
    sparseCoreBundleRestartTool_cost_le_restart lsfInit E.C_lsst E.L sparsify st' j'⟩

end MinCostFlow.Chain

end
