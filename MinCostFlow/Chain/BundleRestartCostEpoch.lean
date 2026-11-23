module

public import MinCostFlow.Chain.BundleRestartCostTotal
import MinCostFlow.SparseCore.BundleEpochCost
import MinCostFlow.SparseCore.BundleEpochRecourse
import MinCostFlow.SparseCore.BundleConstantsLemmas
import MinCostFlow.SparseCore.CompLSFBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Per-Epoch and Baseline Cost Bounds for `sparseCoreBundleRestartTool`

Bounds the three dynamic pieces of `bundle_branch_cost_decomp` at `(M, N)` without any input degree
bound or `hComp_bound`:
- `bundleEpoch_dyn_cost_restart_le` and `bundleEpoch_dyn_cost_restart_le_Tk`: Theorem 8.2 update
  work over one non-restarted epoch `[s₀, t]`, using `bundle_epoch_dyn_cost_le` and
  `bundleCost_env_baseline_parts_noComp` with `n_eff = min N (M + 1)`.
- `bundleEpoch_US_restart_le`: output batch lengths `∑ |U_S|` over one epoch `[s₀, t]`, using
  `bundleEpoch_recourse_and_enc_min`.
- `bundleRestart_init_bun_le_active`: initial setup + lazy initializations (via
  `bundleInitBuckets_cost_sum_le`) and cumulative bundle-batch lengths `∑ bunCost_R` over `0 .. τ`
  (via `bundle_epoch_U_B_sum_le`).
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

/-! ## 1. Root-growth bounds over an arbitrary suffix `[s₀, t]` -/

private lemma bundleRunSeq_R_epoch_bounds
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (restarts : ℕ → List ℕ)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (s₀ t j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hst : s₀ ≤ t) (htτ : t ≤ τ) :
    let base := fun s => (bundleRunSeqWith lsfInit L sparsify k M N D ord j s).1
    let q_ep := ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + (t - s₀)), (D.U s).length
    (∀ r < t - s₀,
      ((components (D.G 0)).sum fun C =>
        (((base (s₀ + (r + 1))).cs.compSt C).R \ ((base (s₀ + r)).cs.compSt C).R).card) =
        ((base (s₀ + (r + 1))).cs.RF.R \ (base (s₀ + r)).cs.RF.R).card) ∧
    ((∑ r ∈ Finset.range (t - s₀),
        ((base (s₀ + (r + 1))).cs.RF.R \ (base (s₀ + r)).cs.RF.R).card : ℕ) : ℝ) ≤
      112 * (q_ep : ℝ) * (Real.log (((min N (M + 1) : ℕ) : ℝ) + 2)) ^ 2 := by
  intro base q_ep
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit
  have hI_at : ∀ s ≤ τ, CompLSFInv C_lsst (D.ℓ 0) (base s).cs ∧ (base s).cs.G = D.G s ∧
      (base s).cs.G₀ = D.G 0 := fun s hs => by
    have hbp := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts hV₀ j s).1
    have hb := hBun s hs
    exact ⟨hbp.cs ▸ hb.2.2.2.2.2.2.2.1, by rw [← hbp.cs]; exact hb.2.2.2.2.2.2.2.2.1,
      by rw [← hbp.cs, hb.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl⟩
  have hcomp_sum : ∀ r < t - s₀,
      ((components (D.G 0)).sum fun C =>
        (((base (s₀ + (r + 1))).cs.compSt C).R \ ((base (s₀ + r)).cs.compSt C).R).card) =
        ((base (s₀ + (r + 1))).cs.RF.R \ (base (s₀ + r)).cs.RF.R).card := by
    intro r hr
    obtain ⟨hI_r, hG_r, hG0_r⟩ := hI_at (s₀ + r) (by omega)
    obtain ⟨hI_r1, _, _⟩ := hI_at (s₀ + (r + 1)) (by omega)
    have hDt := hD (s₀ + r + 1) (Nat.succ_pos _) (by omega)
    simp only [Nat.add_sub_cancel] at hDt
    have hBU : (base (s₀ + r)).cs.G.BatchIsValid (D.U (s₀ + r + 1)) := hG_r.symm ▸ hDt.1
    have hcs1 : (base (s₀ + (r + 1))).cs = compLSFBatch (base (s₀ + r)).cs (D.U (s₀ + r + 1)) := by
      rw [show s₀ + (r + 1) = (s₀ + r) + 1 by omega]
      exact bundleRunSeqWith_cs lsfInit L sparsify k M N D ord j (s₀ + r)
    have hsp := compLSFBatch_step_props (D.U (s₀ + r + 1)) hI_r hBU
    have hR_mono : ∀ C ∈ components (base (s₀ + r)).cs.G₀,
        ((base (s₀ + r)).cs.compSt C).R ⊆ ((base (s₀ + (r + 1))).cs.compSt C).R :=
      fun C hC => by rw [hcs1]; exact (hsp.2.2.1 C hC).2.2.2.1
    have heq := compLSF_sum_R_sdiff_eq hI_r hI_r1 (by rw [hcs1, compLSFBatch_G₀]) hR_mono
    rwa [hG0_r] at heq
  have hstep_R : ∀ r < t - s₀,
      (((base (s₀ + (r + 1))).cs.RF.R \ (base (s₀ + r)).cs.RF.R).card : ℝ) ≤
        112 * ((D.U (s₀ + r + 1)).length : ℝ) *
          (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 := by
    intro r hr
    obtain ⟨hI_r, hG_r, hG0_r⟩ := hI_at (s₀ + r) (by omega)
    have hDt := hD (s₀ + r + 1) (Nat.succ_pos _) (by omega)
    simp only [Nat.add_sub_cancel] at hDt
    have hBU : (base (s₀ + r)).cs.G.BatchIsValid (D.U (s₀ + r + 1)) := hG_r.symm ▸ hDt.1
    have hcs1 : (base (s₀ + (r + 1))).cs = compLSFBatch (base (s₀ + r)).cs (D.U (s₀ + r + 1)) := by
      rw [show s₀ + (r + 1) = (s₀ + r) + 1 by omega]
      exact bundleRunSeqWith_cs lsfInit L sparsify k M N D ord j (s₀ + r)
    have hsub : (base (s₀ + r)).cs.RF.R ⊆ (base (s₀ + (r + 1))).cs.RF.R := by
      rw [hcs1]; exact (compLSFBatch_decremental hI_r hBU).2
    have hR := compLSF_R_sum_le_min hI_r hBU
    rw [← hcs1, hG0_r] at hR
    have hc : (((base (s₀ + (r + 1))).cs.RF.R \ (base (s₀ + r)).cs.RF.R).card : ℝ) =
        ((base (s₀ + (r + 1))).cs.RF.R.card : ℝ) - ((base (s₀ + r)).cs.RF.R.card : ℝ) := by
      rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
    have h2 : 56 * ((2 * (D.U (s₀ + r + 1)).length : ℕ) : ℝ) *
          (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 =
        112 * ((D.U (s₀ + r + 1)).length : ℝ) *
          (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 := by push_cast; ring
    linarith
  have hmin_le : min (D.G 0).n ((D.G 0).m + 1) ≤ min N (M + 1) :=
    min_le_min hN (Nat.add_le_add_right hM 1)
  have hlog_le : (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 ≤
      (Real.log (((min N (M + 1) : ℕ) : ℝ) + 2)) ^ 2 := by
    have hnn : 0 ≤ Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2) :=
      (half_lt_log_add_two (min (D.G 0).n ((D.G 0).m + 1))).le.trans' (by norm_num)
    refine pow_le_pow_left₀ hnn (Real.log_le_log (by positivity) ?_) 2
    have hR : ((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) ≤ ((min N (M + 1) : ℕ) : ℝ) := by
      exact_mod_cast hmin_le
    linarith
  have hq_eq : (q_ep : ℝ) = ∑ r ∈ Finset.range (t - s₀), ((D.U (s₀ + r + 1)).length : ℝ) := by
    dsimp only [q_ep]
    rw [Nat.cast_sum, bundle_sum_Icc_succ_eq_sum_range, show s₀ + (t - s₀) - s₀ = t - s₀ by omega]
  refine ⟨hcomp_sum, ?_⟩
  rw [Nat.cast_sum]
  calc (∑ r ∈ Finset.range (t - s₀),
          (((base (s₀ + (r + 1))).cs.RF.R \ (base (s₀ + r)).cs.RF.R).card : ℝ))
      ≤ ∑ r ∈ Finset.range (t - s₀),
          (112 * ((D.U (s₀ + r + 1)).length : ℝ) *
            (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2) :=
        Finset.sum_le_sum fun r hr => hstep_R r (Finset.mem_range.mp hr)
    _ = 112 * (∑ r ∈ Finset.range (t - s₀), ((D.U (s₀ + r + 1)).length : ℝ)) *
          (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = 112 * (q_ep : ℝ) * (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 := by
        rw [hq_eq]
    _ ≤ 112 * (q_ep : ℝ) * (Real.log (((min N (M + 1) : ℕ) : ℝ) + 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hlog_le (by positivity)

/-! ## 2. Per-epoch dynamic-spanner cost and output recourse -/

/-- `bundle_epoch_dyn_cost_le` instantiated on one epoch `[s₀, t]` of branch `j` with
`n_eff = min N (M + 1)` (no degree bound and no `hComp_bound`). -/
lemma bundleEpoch_dyn_cost_restart_le (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D)
    (s₀ t j : ℕ) (hj : j < k) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀ : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r) :
    let ep := epochBundleSeq lsfInit E.C_lsst E.L sparsify k M N D ord restarts s₀ t j
    let actB := (initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets
    let n_eff := min N (M + 1)
    let q_ep := ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + (t - s₀)), (D.U s).length
    let q_τ := ∑ s ∈ Finset.Icc 1 τ, (D.U s).length
    let Λ := bundleLambda (E.P_fn M) M
    let uc_ep := 2 * bundleUCRatio n_eff * (q_ep : ℝ)
    let ucBound := 2 * bundleUCRatio n_eff * (q_τ : ℝ)
    (∑ r ∈ Finset.range (t - s₀), ((ep (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
      (((stepBundleTree sparsify (ep r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1))).stepOut (C, b)).cost : ℝ))) ≤
      90 * (E.L : ℝ) * bundleNRoot E.L M * ((E.P_fn M).K_t + (E.P_fn M).K_s + 1) *
        coreE_L E.L (E.P_fn M) * ((k : ℝ) + 1) * Λ *
        (20 * ((M : ℝ) + (E.B_fn M : ℝ) * uc_ep) * Real.log ((M : ℝ) + ucBound + 2)) := by
  intro ep actB n_eff q_ep q_τ Λ uc_ep ucBound
  have hk1 : 1 ≤ k := hk
  have hInit_j := hHyps.hInit j hj
  have hInv := epochBundleSeq_inv lsfInit E.C_lsst E.L E.hL (E.P_fn M) sparsify
    k M N τ hk1 D ord restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hOrd hThresh s₀ t j hInit_j hst htτ hs₀ hNoRest
  have hDyn := epochBundleSeq_dyn_spec lsfInit E.C_lsst E.L E.hL (E.P_fn M) sparsify
    k M N τ hk1 D ord restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit_j hst htτ hs₀ hNoRest
  obtain ⟨hSt_base, _⟩ := epochBundleSeq_steps lsfInit E.C_lsst E.L sparsify
    k M N D ord restarts hV₀ s₀ t j hst hNoRest
  obtain ⟨hR_comp_sum, hR_sum⟩ := bundleRunSeq_R_epoch_bounds lsfInit E.C_lsst E.L sparsify
    k M N τ hk1 D ord restarts hG₀ hV₀ hℓ₀ hD hOrd hM hN s₀ t j hInit_j hst htτ
  set Hb := fun C b => normGraph ((ep 0).bun (C, b)).graph
  set Us_ep := fun C b => (List.range (t - s₀)).map fun r =>
    (stepBundleTree sparsify (ep r) (D.U (s₀ + r + 1)) (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)
  obtain ⟨hUB_single_ep, hUB_sum⟩ := bundle_epoch_U_B_sum_le
    (G₀ := D.G 0) (N := n_eff) (B_bound := E.B_fn M) (s₀ := s₀) (Δ := t - s₀) (D := D)
    actB (hHyps.activeBuckets_card_le (N := N) hj)
    (fun r => (ep r).cs)
    (fun r p => (stepBundleTree sparsify (ep r) (D.U (s₀ + r + 1)) (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B p)
    (fun r hr C hC b _ => ((hDyn C hC b).2.2.2.2.2.2.2.2.2.2 r hr).2.2.1)
    (fun r hr => epochBundleSeq_deletes_sum_le lsfInit E.C_lsst E.L E.hL (E.P_fn M) sparsify
      k M N τ hk1 D ord restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit_j hst htτ hs₀ hNoRest hr)
    (fun r hr C hC b _ => ((hDyn C hC b).2.2.2.2.2.2.2.2.2.2 r hr).2.2.2.1)
    (fun r hr => by
      have h1 := (hSt_base r hr.le).cs
      have h2 := (hSt_base (r + 1) hr).cs
      rw [h1, h2]; exact hR_comp_sum r hr)
    (by
      have heq : ∀ r ∈ Finset.range (t - s₀),
          ((ep (r + 1)).cs.RF.R \ (ep r).cs.RF.R).card =
          (((bundleRunSeqWith lsfInit E.L sparsify k M N D ord j (s₀ + (r + 1))).1.cs.RF.R \
            (bundleRunSeqWith lsfInit E.L sparsify k M N D ord j (s₀ + r)).1.cs.RF.R).card) := by
        intro r hr
        have hr' := Finset.mem_range.mp hr
        rw [(hSt_base (r + 1) hr').cs, (hSt_base r hr'.le).cs]
      dsimp only
      rw [Finset.sum_congr rfl heq]
      exact hR_sum)
  have hq_le : q_ep ≤ q_τ := Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc (by omega) (by omega))
  have huc_le : uc_ep ≤ ucBound :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hq_le)
      (mul_nonneg zero_le_two (bundleUCRatio_pos n_eff).le)
  have huc_nn : 0 ≤ ucBound :=
    mul_nonneg (mul_nonneg zero_le_two (bundleUCRatio_pos n_eff).le) (Nat.cast_nonneg _)
  exact bundle_epoch_dyn_cost_le E.hL sparsify hk1 actB (fun r => (ep (r + 1)).activeComps) Hb
    Us_ep
    (fun r p => (stepBundleTree sparsify (ep r) (D.U (s₀ + r + 1)) (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B p)
    (fun r p => (stepBundleTree sparsify (ep r) (D.U (s₀ + r + 1)) (ord (s₀ + r)) (ord (s₀ + r + 1))).stepOut p)
    uc_ep ucBound huc_nn
    (le_trans hInv.2.1 hM)
    (fun C hC b _ => (hInv.1 C hC b).2.2.1)
    (fun C hC b _ => by dsimp only [Hb]; rw [normGraph_maxDeg]; exact (hInv.1 C hC b).2.2.2.1)
    (fun C hC b hb => le_trans (hUB_single_ep C hC b hb) huc_le)
    hUB_sum
    (fun r hr => (hInv.2.2.1 (r + 1) hr).2.1)
    (fun C hC b _ => by
      have h0 := (hDyn C hC b).2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
      dsimp only [Hb]; rw [normGraph_n, ← h0.1]; exact h0.2.2.1)
    (fun C hC b _ => by
      have h0 := (hDyn C hC b).2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
      dsimp only [Hb]; rw [normGraph_n, ← h0.1, graphEq_m h0.2.1]; rfl)
    (fun r hr C hC b _ => by
      have hr0 := (hDyn C hC b).2.2.2.2.2.2.2.2.2.1 r hr.le
      have hr1 := (hDyn C hC b).2.2.2.2.2.2.2.2.2.1 (r + 1) hr
      have hs := (hDyn C hC b).2.2.2.2.2.2.2.2.2.2 r hr
      have hsp := (hInv.2.2.2.1 r hr).2.2.2.1 C hC b
      dsimp only [Hb]; rw [normGraph_n, ← hr0.1, ← hr1.1]
      exact ⟨hs.2.1, by rw [← hsp.2.1, hsp.1, update_G_eq]⟩)
    (fun C hC b _ r hr => by
      dsimp only [Hb]; rw [normGraph_n]
      exact ((hDyn C hC b).2.2.2.2.2.2.2.2.2.2 r hr).1)
    (fun C hC b _ => by
      simpa only [Hb, normGraph_n, normGraph_m, normGraph_maxDeg] using (hInv.2.2.2.2 C hC b).2.2)

/-- Output batch lengths `∑ |U_S|` over one epoch `[s₀, t]`, in terms of `bundleRecoursePerQ` at
`min N (M + 1)`. -/
lemma bundleEpoch_US_restart_le (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D)
    (s₀ t j : ℕ) (hj : j < k) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀ : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r) :
    let T := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    ∑ s ∈ Finset.Icc (s₀ + 1) t, (((T.runOrdAfterUpdate k M N D ord restarts s).2 j).length : ℝ) ≤
      bundleRecoursePerQ E.L (E.P_fn M) M (min N (M + 1)) (E.B_fn M) *
        ∑ s ∈ Finset.Icc (s₀ + 1) t, ((D.U s).length : ℝ) := by
  intro T
  have hk1 : 1 ≤ k := hk
  have hInit_j := hHyps.hInit j hj
  have hInv := epochBundleSeq_inv lsfInit E.C_lsst E.L E.hL (E.P_fn M) sparsify
    k M N τ hk1 D ord restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hOrd hThresh s₀ t j hInit_j hst htτ hs₀ hNoRest
  have hBun := runOrdAfterRestarts_bun_inv lsfInit E.C_lsst E.L sparsify
    k M N τ hk1 D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit_j
  obtain ⟨hSt_base, hSt_step⟩ := epochBundleSeq_steps lsfInit E.C_lsst E.L sparsify
    k M N D ord restarts hV₀ s₀ t j hst hNoRest
  set st₀ := initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
  set ep := epochBundleSeq lsfInit E.C_lsst E.L sparsify k M N D ord restarts s₀ t j
  set Hb := fun C b => ((ep 0).bun (C, b)).graph
  have hRec := bundleEpoch_recourse_and_enc_min (C_lsst := E.C_lsst) (L := E.L) (τ := τ) E.hL
    (E.P_fn M) sparsify hk1 D ord st₀.activeBuckets (E.B_fn M) (hHyps.activeBuckets_card_le (N := N) hj)
    (fun C _ ⟨b, hb⟩ => by
      rcases Finset.mem_image.mp hb with ⟨e, he, _⟩
      exact le_trans (Finset.card_pos.mpr ⟨e, (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).1⟩) hM)
    s₀ (t - s₀) (by omega) ep
    (fun r => (T.runOrdAfterUpdate k M N D ord restarts (s₀ + r)).2 j) Hb
    (fun C hC b => ⟨le_trans (hInv.1 C hC b).2.1 hM, (hInv.1 C hC b).2.2.1⟩)
    (fun r hr => (hSt_step r hr).1)
    (fun r hr => by rw [show s₀ + (r + 1) = s₀ + r + 1 by omega]; exact (hSt_step r hr).2)
    (fun r hr => by
      have hbp := (runOrdAfterRestarts_base_proj lsfInit E.C_lsst E.L sparsify k M N D ord restarts
        hV₀ j (s₀ + r)).1
      have hb := hBun (s₀ + r) (by omega)
      refine ⟨by rw [(hSt_base r hr).cs, ← hbp.cs]; exact hb.2.2.2.2.2.2.2.1, ?_⟩
      rw [(hSt_base r hr).cs, ← hbp.cs, hb.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl)
    (fun r hr => by
      have hbp := (runOrdAfterRestarts_base_proj lsfInit E.C_lsst E.L sparsify k M N D ord restarts
        hV₀ j (s₀ + r)).1
      have hb := hBun (s₀ + r) (by omega)
      have hDt := hD (s₀ + r + 1) (Nat.succ_pos _) (by omega)
      simp only [Nat.add_sub_cancel] at hDt
      rw [(hSt_base r hr.le).cs, ← hbp.cs, hb.2.2.2.2.2.2.2.2.1]; exact hDt.1)
    (fun r hr => by
      have hbp := (runOrdAfterRestarts_base_proj lsfInit E.C_lsst E.L sparsify k M N D ord restarts
        hV₀ j (s₀ + r)).1
      rw [(hSt_base r hr).activeBuckets, ← hbp.activeBuckets]
      exact (hBun (s₀ + r) (by omega)).2.2.2.2.1)
    (fun r hr => epochBundleSeq_UB_sum_le lsfInit E.C_lsst E.L E.hL (E.P_fn M) sparsify
      k M N τ hk1 D ord restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t j (E.B_fn M) hInit_j
      hst htτ hs₀ hNoRest (hHyps.activeBuckets_card_le (N := N) hj) hr)
    (fun r hr => by
      have hs := hInv.2.2.1 r hr
      refine ⟨hs.1, hs.2.1, fun C hC b => ?_⟩
      have hcb := hs.2.2 C hC b
      exact ⟨hcb.2.2.2.1, hcb.2.2.2.2.1, hcb.2.2.2.2.2.2.2.1⟩)
    (fun r hr => by
      have hst' := hInv.2.2.2.1 r hr
      exact ⟨hst'.1, hst'.2.1, hst'.2.2.1,
        fun C hC b => ⟨(hst'.2.2.2.1 C hC b).2.1, (hst'.2.2.2.1 C hC b).2.2.1⟩,
        hst'.2.2.2.2.1, hst'.2.2.2.2.2.1, hst'.2.2.2.2.2.2.1, hst'.2.2.2.2.2.2.2⟩)
    (fun C hC b => ⟨(hInv.2.2.2.2 C hC b).1, (hInv.2.2.2.2 C hC b).2.1⟩)
  have hUS_sum_eq :
      (Finset.Icc (s₀ + 1) t).sum (fun s => ((T.runOrdAfterUpdate k M N D ord restarts s).2 j).length) =
        (Finset.Icc 1 (t - s₀)).sum
          (fun r => ((T.runOrdAfterUpdate k M N D ord restarts (s₀ + r)).2 j).length) := by
    refine Finset.sum_bij (fun s _ => s - s₀)
      (fun s hs => by simp only [Finset.mem_Icc] at hs ⊢; omega)
      (fun a ha b hb h => by simp only [Finset.mem_Icc] at ha hb; omega)
      (fun r hr => ⟨s₀ + r, by simp only [Finset.mem_Icc] at hr ⊢; omega, by omega⟩)
      (fun s hs => by simp only [Finset.mem_Icc] at hs; rw [Nat.add_sub_cancel' (by omega)])
  have hq_ep_rw : (Finset.Icc (s₀ + 1) (s₀ + (t - s₀))).sum (fun s => (D.U s).length) =
      (Finset.Icc (s₀ + 1) t).sum (fun s => (D.U s).length) := by
    rw [show s₀ + (t - s₀) = t by omega]
  have h1 := hRec.1
  rw [hq_ep_rw, ← hUS_sum_eq] at h1
  push_cast at h1
  have hmono := bundleParams_recoursePerQ_mono_n E.L (E.P_fn M) M
    (min_le_min hN (Nat.add_le_add_right hM 1)) (E.B_fn M)
  exact le_trans h1 (mul_le_mul_of_nonneg_right hmono (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _))

/-- Theorem 8.2 work over one epoch `[s₀, t]`, wrapped into the `Tk` envelope of
`bundleCost_env_baseline_parts_noComp`. -/
lemma bundleEpoch_dyn_cost_restart_le_Tk (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D)
    (s₀ t j : ℕ) (hj : j < k) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀ : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r) :
    let T := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    let st₀ := initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
    let post := fun s => T.runOrdAfterRestarts k M N D ord restarts s
    let infoR := fun s => stepBundleTree sparsify ((post s).trees j) (D.U (s + 1)) (ord s) (ord (s + 1))
    let p_max := max E.p_s_hi E.p_t_hi
    let logMN := Real.log ((M : ℝ) + (N : ℝ) + 2)
    let Tk := ((M : ℝ) + 1) * ((k : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) *
      logMN ^ (p_max + 1)
    ∑ s ∈ Finset.Icc (s₀ + 1) t,
        ((((infoR (s - 1)).state.activeComps.sum fun C =>
          (st₀.activeBuckets C).sum fun b => ((infoR (s - 1)).stepOut (C, b)).cost : ℕ) : ℝ)) ≤
      12600 * (7 : ℝ) ^ p_max * Tk +
        (25200 * (7 : ℝ) ^ p_max *
          (((k : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) * logMN ^ (p_max + 1))) *
          ∑ s ∈ Finset.Icc (s₀ + 1) t, ((D.U s).length : ℝ) := by
  intro T st₀ post infoR p_max logMN Tk
  obtain ⟨_, hSt_step⟩ := epochBundleSeq_steps lsfInit E.C_lsst E.L sparsify
    k M N D ord restarts hV₀ s₀ t j hst hNoRest
  set ep := epochBundleSeq lsfInit E.C_lsst E.L sparsify k M N D ord restarts s₀ t j
  have hDyn := bundleEpoch_dyn_cost_restart_le E lsfInit sparsify k M N τ D ord restarts
    hk hG₀ hV₀ hℓ₀ hD hOrd hM hN hThresh hHyps s₀ t j hj hst htτ hs₀ hNoRest
  dsimp only at hDyn
  have hterm : ∀ r < t - s₀,
      (((infoR (s₀ + r)).state.activeComps.sum fun C =>
          (st₀.activeBuckets C).sum fun b => ((infoR (s₀ + r)).stepOut (C, b)).cost : ℕ) : ℝ) =
        ((ep (r + 1)).activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
          (((stepBundleTree sparsify (ep r) (D.U (s₀ + r + 1))
            (ord (s₀ + r)) (ord (s₀ + r + 1))).stepOut (C, b)).cost : ℝ)) := by
    intro r hr
    have hep : ep r = (post (s₀ + r)).trees j :=
      (epochBundleSeq_eq_post lsfInit E.C_lsst E.L sparsify k M N D ord restarts s₀ t j hst).1 r hr
    have hstep : ep (r + 1) = (stepBundleTree sparsify (ep r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1))).state := (hSt_step r hr).1
    have hinfo : infoR (s₀ + r) = stepBundleTree sparsify (ep r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1)) := by dsimp only [infoR]; rw [hep]
    rw [hinfo, ← hstep]
    push_cast
    rfl
  rw [bundle_sum_Icc_succ_eq_sum_range]
  have hsum_eq2 : ∑ r ∈ Finset.range (t - s₀),
      ((((infoR (s₀ + r + 1 - 1)).state.activeComps.sum fun C =>
          (st₀.activeBuckets C).sum fun b =>
            ((infoR (s₀ + r + 1 - 1)).stepOut (C, b)).cost : ℕ) : ℝ)) =
      ∑ r ∈ Finset.range (t - s₀), ((ep (r + 1)).activeComps.sum fun C =>
        (st₀.activeBuckets C).sum fun b =>
          (((stepBundleTree sparsify (ep r) (D.U (s₀ + r + 1))
            (ord (s₀ + r)) (ord (s₀ + r + 1))).stepOut (C, b)).cost : ℝ)) :=
    Finset.sum_congr rfl fun r hr => by
      rw [show s₀ + r + 1 - 1 = s₀ + r by omega]
      exact hterm r (Finset.mem_range.mp hr)
  rw [hsum_eq2]
  refine le_trans hDyn ?_
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hqτ_le_M : (Finset.Icc 1 τ).sum (fun s => (D.U s).length) ≤ M :=
    (updateThreshold_le_div_k_at hk hN_pos hThresh τ le_rfl).2
  obtain ⟨_, hd5, _⟩ := bundleCost_env_baseline_parts_noComp E k M N (activeSubgraph (D.G 0)).n
    ((Finset.Icc 1 τ).sum fun s => (D.U s).length) hN_pos
    (le_trans (activeSubgraph_n_le_two_m hG₀) (Nat.mul_le_mul_left 2 hM)) hqτ_le_M
  have h5 := hd5 ((Finset.Icc (s₀ + 1) (s₀ + (t - s₀))).sum fun s => (D.U s).length)
  have hq_eq : (((Finset.Icc (s₀ + 1) (s₀ + (t - s₀))).sum fun s => (D.U s).length : ℕ) : ℝ) =
      ∑ s ∈ Finset.Icc (s₀ + 1) t, ((D.U s).length : ℝ) := by
    rw [show s₀ + (t - s₀) = t by omega, Nat.cast_sum]
  refine le_trans h5 (le_of_eq ?_)
  rw [hq_eq]
  ring

/-! ## 3. Baseline initialization and cumulative bundle-batch length bounds -/

/-- Bounds the initial + lazy initialization cost and the cumulative bundle-batch length
`∑_{s < τ} bunCost_R s` of branch `j` across the entire run `0 .. τ` with restarts. -/
lemma bundleRestart_init_bun_le_active
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (B_bound : ℕ)
    (hB_bound : ∀ C ∈ components (D.G 0),
      ((initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).card ≤
        B_bound) :
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
    let post := fun s => T.runOrdAfterRestarts k M N D ord restarts s
    let base := fun s => (bundleRunSeqWith lsfInit L sparsify k M N D ord j s).1
    let infoR := fun s => stepBundleTree sparsify ((post s).trees j) (D.U (s + 1)) (ord s) (ord (s + 1))
    let n_eff := min N (M + 1)
    let q_τ := ∑ s ∈ Finset.Icc 1 τ, (D.U s).length
    let Λ := bundleLambda P_b M
    (((D.G 0).m : ℝ) + ((activeSubgraph (D.G 0)).n : ℝ) + 1) +
        (((base τ).activeComps.sum st₀.lazyInitCost : ℕ) : ℝ) ≤
        ((M : ℝ) + ((activeSubgraph (D.G 0)).n : ℝ) + 1) +
          ((L : ℝ) + 1 + P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ +
            2 * P_b.K_s * P_b.γ_ℓ * Λ) * (M : ℝ) ∧
    (∑ s ∈ Finset.range τ, (((infoR s).state.activeComps.sum fun C =>
        (st₀.activeBuckets C).sum fun b => ((infoR s).U_B (C, b)).length : ℕ) : ℝ)) ≤
      (B_bound : ℝ) * (2 * bundleUCRatio n_eff * (q_τ : ℝ)) := by
  classical
  intro T st₀ post base infoR n_eff q_τ Λ
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit
  obtain ⟨hAct_card, hm_sum, hn_2m, _⟩ := initBundleTreeWith_buckets_sum_le lsfInit L sparsify
    (M := M) (N := N) hk (G₀ := D.G 0) (D.ℓ 0) (ord 0) j
  have hact_sub : ∀ s ≤ τ, (base s).activeComps ⊆ components (D.G 0) := fun s hs => by
    have hbp := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts hV₀ j s).1
    rw [← hbp.activeComps]
    exact (hBun s hs).2.2.2.2.2.2.2.2.2.1.2
  -- Part 1: Initial setup + lazy initializations
  have hInit_sum :
      (((D.G 0).m : ℝ) + ((activeSubgraph (D.G 0)).n : ℝ) + 1) +
        (((base τ).activeComps.sum st₀.lazyInitCost : ℕ) : ℝ) ≤
        ((M : ℝ) + ((activeSubgraph (D.G 0)).n : ℝ) + 1) +
          ((L : ℝ) + 1 + P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ +
            2 * P_b.K_s * P_b.γ_ℓ * Λ) * (M : ℝ) := by
    have hI₀ : CompLSFInv C_lsst (D.ℓ 0) st₀.cs := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
    obtain ⟨ρ₀, hρ₀⟩ := orderedUpTo_rot_at hOrd (Nat.zero_le τ) (G := st₀.cs.G) rfl
    have h82_0 : ∀ C ∈ components (D.G 0), ∀ b ∈ st₀.activeBuckets C,
        let Hb := normGraph (st₀.bun (C, b)).graph
        let initB := DynSpanner.init Hb L (phaseBase (Hb.n + bundleSplitBudget k M) L) (sparsify M)
        (initB.state.H.m : ℝ) ≤
          P_b.K_s * (Hb.n : ℝ) * P_b.γ_ℓ *
            (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s ∧
        (initB.cost : ℝ) ≤
          P_b.K_t * (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
              (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_t +
            (Hb.n : ℝ) + (Hb.m : ℝ) + (initB.state.H.m : ℝ) +
            (Hb.m : ℝ) * P_b.γ_ℓ + (L : ℝ) + 1 := by
      intro C hC b hb Hb initB
      have hR0 := ((hBun 0 (Nat.zero_le τ)).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b |>.1
      have hpart := hR0.1 ρ₀ hI₀.hG_val (compLSF_RF_isRSF hI₀) hρ₀
      have hval : Hb.IsValid := normGraph_isValid (BundleState.graph_isValid hpart)
      have hm_b : Hb.m ≤ M := le_trans
        (le_trans (Finset.single_le_sum (f := fun b' => (st₀.bun (C, b')).graph.m) (fun _ _ => Nat.zero_le _) hb)
          (Finset.single_le_sum (f := fun C' => (st₀.activeBuckets C').sum fun b' => (st₀.bun (C', b')).graph.m)
            (fun _ _ => Nat.zero_le _) hC)) (le_trans hm_sum hM)
      have hthm := DynSpanner.theorem_8_2 (Us := []) (splitBound := bundleSplitBudget k M)
        hval hL hm_b hSp trivial (by simp) (by simp [batchSplitCount])
      exact ⟨hthm.1, hthm.2.1⟩
    have hlazy_eq : st₀.lazyInitCost = fun C => (st₀.activeBuckets C).sum fun b =>
        (DynSpanner.init (normGraph (st₀.bun (C, b)).graph) L
          (phaseBase ((normGraph (st₀.bun (C, b)).graph).n + bundleSplitBudget k M) L) (sparsify M)).cost := rfl
    rw [hlazy_eq]
    push_cast
    have hsum := bundleInitBuckets_cost_sum_le (L := L) (P_b := P_b) (m₀ := M) (G₀ := D.G 0)
      (base τ).activeComps (hact_sub τ le_rfl) st₀.activeBuckets
      (fun C b => normGraph (st₀.bun (C, b)).graph)
      (fun C b => DynSpanner.init (normGraph (st₀.bun (C, b)).graph) L
        (phaseBase ((normGraph (st₀.bun (C, b)).graph).n + bundleSplitBudget k M) L) (sparsify M))
      (le_trans hAct_card hM) (le_trans hm_sum hM) (fun C _ b _ => hn_2m C b) h82_0
    have hMR : ((D.G 0).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith [hsum, hMR]
  -- Part 2: Cumulative bundle-batch lengths `∑ bunCost_R` over `0 .. τ`
  have hPerStep : ∀ r < τ,
      (∀ C ∈ components (D.G 0), ∀ b ∈ st₀.activeBuckets C,
        ∀ op ∈ (infoR r).U_B (C, b), isDelOrSplit op) ∧
      (((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
        ((infoR r).U_B (C, b)).countP deleteTag) ≤ (D.U (r + 1)).length) ∧
      (∀ C ∈ components (D.G 0), ∀ b ∈ st₀.activeBuckets C,
        batchSplitCount ((infoR r).U_B (C, b)) ≤
          2 * (((base (r + 1)).cs.compSt C).R \ ((base r).cs.compSt C).R).card) := by
    intro r hr
    set s₀ := bundleLastRestart restarts j r
    have hs₀ := bundleLastRestart_spec restarts j r
    have hNoR : ∀ x, s₀ < x → x < r + 1 → j ∉ restarts x := fun x h1 h2 => hs₀.2.2 x h1 (by omega)
    have hDyn := epochBundleSeq_dyn_spec lsfInit C_lsst L hL P_b sparsify
      k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ (r + 1) j hInit (by omega) hr hs₀.2.1 hNoR
    have hDel := epochBundleSeq_deletes_sum_le lsfInit C_lsst L hL P_b sparsify
      k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ (r + 1) j hInit (by omega) hr hs₀.2.1 hNoR
      (δ := r - s₀) (by omega)
    have hSt_base := (epochBundleSeq_steps lsfInit C_lsst L sparsify
      k M N D ord restarts hV₀ s₀ (r + 1) j (by omega) hNoR).1
    have hep_r : epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ (r + 1) j (r - s₀) =
        (post r).trees j := by
      have h1 := (epochBundleSeq_eq_post lsfInit C_lsst L sparsify k M N D ord restarts s₀ (r + 1) j
        (by omega)).1 (r - s₀) (by omega)
      rw [show s₀ + (r - s₀) = r by omega] at h1; exact h1
    have hinfo_eq : stepBundleTree sparsify
          (epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ (r + 1) j (r - s₀))
          (D.U (s₀ + (r - s₀) + 1)) (ord (s₀ + (r - s₀))) (ord (s₀ + (r - s₀) + 1)) =
        infoR r := by
      dsimp only [infoR]
      rw [hep_r, show s₀ + (r - s₀) = r by omega]
    dsimp only at hDel
    rw [hinfo_eq, show s₀ + (r - s₀) = r by omega] at hDel
    refine ⟨fun C hC b _ => ?_, hDel, fun C hC b _ => ?_⟩
    · have hstep := ((hDyn C hC b).2.2.2.2.2.2.2.2.2.2 (r - s₀) (by omega)).2.2.1
      rwa [hinfo_eq] at hstep
    · have hstep := ((hDyn C hC b).2.2.2.2.2.2.2.2.2.2 (r - s₀) (by omega)).2.2.2.1
      rw [hinfo_eq, (hSt_base (r - s₀ + 1) (by omega)).cs, (hSt_base (r - s₀) (by omega)).cs,
        show s₀ + (r - s₀ + 1) = r + 1 by omega, show s₀ + (r - s₀) = r by omega] at hstep
      exact hstep
  obtain ⟨hR_comp_sum, hR_sum⟩ := bundleRunSeq_R_epoch_bounds lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd hM hN 0 τ j hInit (Nat.zero_le τ) le_rfl
  obtain ⟨_, hUB_total⟩ := bundle_epoch_U_B_sum_le
    (G₀ := D.G 0) (N := n_eff) (B_bound := B_bound) (s₀ := 0) (Δ := τ) (D := D)
    st₀.activeBuckets hB_bound (fun r => (base r).cs) (fun r p => (infoR r).U_B p)
    (fun r hr => (hPerStep r hr).1)
    (fun r hr => by rw [Nat.zero_add]; exact (hPerStep r hr).2.1)
    (fun r hr => (hPerStep r hr).2.2)
    (fun r hr => by simpa only [Nat.zero_add] using hR_comp_sum r hr)
    (by
      dsimp only
      simpa only [Nat.zero_add, Nat.sub_zero] using hR_sum)
  have hIcc0 : Finset.Icc (0 + 1) (0 + τ) = Finset.Icc 1 τ := by simp
  rw [hIcc0] at hUB_total
  have hBun_sum :
      (∑ s ∈ Finset.range τ, (((infoR s).state.activeComps.sum fun C =>
        (st₀.activeBuckets C).sum fun b => ((infoR s).U_B (C, b)).length : ℕ) : ℝ)) ≤
        (B_bound : ℝ) * (2 * bundleUCRatio n_eff * (q_τ : ℝ)) := by
    have hact_info : ∀ s < τ, (infoR s).state.activeComps ⊆ components (D.G 0) := fun s hs => by
      have hne_post : (post s).isNonempty = true :=
        (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.1.trans
          (decide_eq_true hV₀)
      have hord_post : (post s).ord = ord s :=
        ((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.2.2.2 hV₀).2
      have hpre_eq : (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j = (infoR s).state := by
        dsimp only [T, post, infoR]
        rw [SparseCoreRestartTool.runOrdAfterUpdate_succ,
          sparseCoreBundleRestartTool_updateOrd_of_nonempty hne_post, hord_post]
      rw [← hpre_eq]
      exact (hBun (s + 1) hs).2.2.2.2.2.2.2.2.2.1.2
    have h1 :
        (∑ s ∈ Finset.range τ, (((infoR s).state.activeComps.sum fun C =>
          (st₀.activeBuckets C).sum fun b => ((infoR s).U_B (C, b)).length : ℕ) : ℝ)) ≤
        ∑ s ∈ Finset.range τ, (components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
          (((infoR s).U_B (C, b)).length : ℝ) := by
      refine Finset.sum_le_sum fun s hs => ?_
      push_cast
      exact Finset.sum_le_sum_of_subset_of_nonneg (hact_info s (Finset.mem_range.mp hs))
        (fun _ _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    have hcomm :
        (∑ s ∈ Finset.range τ, (components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
          (((infoR s).U_B (C, b)).length : ℝ)) =
        (components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
          ∑ s ∈ Finset.range τ, (((infoR s).U_B (C, b)).length : ℝ) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun C _ => Finset.sum_comm
    exact le_trans (le_trans h1 (le_of_eq hcomm)) hUB_total
  exact ⟨hInit_sum, hBun_sum⟩

end MinCostFlow.Chain

end
