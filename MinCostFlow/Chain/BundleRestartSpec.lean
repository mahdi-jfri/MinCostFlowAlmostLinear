module

public import MinCostFlow.Chain.BundleRestartEpochItems
import MinCostFlow.SparseCore.BundleEpochRecourse
import MinCostFlow.SparseCore.BundleEpochCost
import MinCostFlow.SparseCore.BundleCostPieces
import MinCostFlow.SparseCore.BundleStability
import MinCostFlow.SparseCore.BundleStabilityStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Items 1–6 (Non-Cost) of `IsSpecOrdRestart` for `sparseCoreBundleRestartTool`

Proves:
- `bundleRestart_spec_item4`: windowed recourse and encoding size over any non-restarted epoch
  `[s₀, t]`, using `bundleEpoch_recourse_and_enc_min` (with `min N (M + 1)`),
  `epochBundleSeq_isSparsifiedCoreGraph` at `δ = 0`, and `four_mul_bundleEncEnv_le_gamma_r`;
- `bundleRestart_spec_item5`: post-restart `WeakHiddenStable` on `coreInstanceOrdFrom` via
  `bundleTreeState_seq_weakHiddenStable`;
- `bundleRestart_spec_noCost`: items 1, 2, non-cost item 3, item 4, item 5, and item 6
  (`OrderedUpTo` via `epochBundleSeq_orderedUpTo`) for both nonempty and empty initial graphs.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.LSF
open MinCostFlow.Bundle

/-! ## 1. Helper: per-step bundle-batch length bound in an epoch -/

/-- At each step `δ < t - s₀` of an epoch `[s₀, t]`, the total length of all component-bucket
bundle batches is bounded by `B_bound * (|D.U (s₀ + δ + 1)| + 2 * |R(s₀+δ+1) \ R(s₀+δ)|)`. -/
lemma epochBundleSeq_UB_sum_le
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N) (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (s₀ t j B_bound : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀ : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r)
    (hB_bound : ∀ C ∈ components (D.G 0),
      ((initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).card ≤
        B_bound)
    {δ : ℕ} (hδ : δ < t - s₀) :
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
    let st := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j
    let info := stepBundleTree sparsify (st δ) (D.U (s₀ + δ + 1)) (ord (s₀ + δ)) (ord (s₀ + δ + 1))
    ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
      (info.U_B (C, b)).length) ≤
      B_bound * ((D.U (s₀ + δ + 1)).length + 2 * ((st (δ + 1)).cs.RF.R \ (st δ).cs.RF.R).card) := by
  intro st₀ st info
  by_cases hB0 : B_bound = 0
  · subst hB0
    have hzero : ∀ C ∈ components (D.G 0), st₀.activeBuckets C = ∅ := fun C hC =>
      Finset.card_eq_zero.mp (Nat.le_zero.mp (hB_bound C hC))
    have hlhs : ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
        (info.U_B (C, b)).length) = 0 :=
      Finset.sum_eq_zero fun C hC => by rw [hzero C hC, Finset.sum_empty]
    rw [hlhs]; exact Nat.zero_le _
  · have hB1 : 1 ≤ B_bound := Nat.pos_of_ne_zero hB0
    have hDyn := epochBundleSeq_dyn_spec lsfInit C_lsst L hL P_b sparsify
      k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit hst htτ hs₀ hNoRest
    have hDel := epochBundleSeq_deletes_sum_le lsfInit C_lsst L hL P_b sparsify
      k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit hst htτ hs₀ hNoRest hδ
    have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
      k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit
    have hSt_base := (epochBundleSeq_steps lsfInit C_lsst L sparsify
      k M N D ord restarts hV₀ s₀ t j hst hNoRest).1
    have hSt_step := (epochBundleSeq_steps lsfInit C_lsst L sparsify
      k M N D ord restarts hV₀ s₀ t j hst hNoRest).2 δ hδ
    have hbp_δ := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts
      hV₀ j (s₀ + δ)).1
    have hbp_δ1 := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts
      hV₀ j (s₀ + (δ + 1))).1
    have hI_δ : CompLSFInv C_lsst (D.ℓ 0) (st δ).cs := by
      rw [(hSt_base δ hδ.le).cs, ← hbp_δ.cs]; exact (hBun (s₀ + δ) (by omega)).2.2.2.2.2.2.2.1
    have hI_δ1 : CompLSFInv C_lsst (D.ℓ 0) (st (δ + 1)).cs := by
      rw [(hSt_base (δ + 1) hδ).cs, ← hbp_δ1.cs]
      exact (hBun (s₀ + (δ + 1)) (by omega)).2.2.2.2.2.2.2.1
    have hG0_δ : (st δ).cs.G₀ = D.G 0 := by
      rw [(hSt_base δ hδ.le).cs, ← hbp_δ.cs, (hBun (s₀ + δ) (by omega)).2.2.2.2.2.2.1,
        compLSFBatch_G₀]; rfl
    have hG_δ : (st δ).cs.G = D.G (s₀ + δ) := by
      rw [(hSt_base δ hδ.le).cs, ← hbp_δ.cs]; exact (hBun (s₀ + δ) (by omega)).2.2.2.2.2.2.2.2.1
    have hcs1 : (st (δ + 1)).cs = compLSFBatch (st δ).cs (D.U (s₀ + δ + 1)) := by
      dsimp only [st]; rw [hSt_step.1]; rfl
    have hDt := hD (s₀ + δ + 1) (Nat.succ_pos _) (by omega)
    simp only [Nat.add_sub_cancel] at hDt
    have hBU : (st δ).cs.G.BatchIsValid (D.U (s₀ + δ + 1)) := hG_δ.symm ▸ hDt.1
    have hR_sum : ((components (D.G 0)).sum fun C =>
        (((st (δ + 1)).cs.compSt C).R \ ((st δ).cs.compSt C).R).card) =
        ((st (δ + 1)).cs.RF.R \ (st δ).cs.RF.R).card := by
      have hsp := compLSFBatch_step_props (D.U (s₀ + δ + 1)) hI_δ hBU
      have hR_m : ∀ C ∈ components (st δ).cs.G₀, ((st δ).cs.compSt C).R ⊆ ((st (δ + 1)).cs.compSt C).R :=
        fun C hC => by rw [hcs1]; exact (hsp.2.2.1 C hC).2.2.2.1
      have heq := compLSF_sum_R_sdiff_eq hI_δ hI_δ1 (by rw [hcs1, compLSFBatch_G₀]) hR_m
      rwa [hG0_δ] at heq
    have hdecomp : ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
          (info.U_B (C, b)).length) =
        ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
          (info.U_B (C, b)).countP deleteTag) +
        ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
          batchSplitCount (info.U_B (C, b))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun C hC => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      exact length_eq_delete_add_split_of_delOrSplit
        (((hDyn C hC b).2.2.2.2.2.2.2.2.2.2 δ hδ).2.2.1)
    have hsp_le : ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
          batchSplitCount (info.U_B (C, b))) ≤
        2 * B_bound * ((st (δ + 1)).cs.RF.R \ (st δ).cs.RF.R).card := by
      calc ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
              batchSplitCount (info.U_B (C, b)))
          ≤ (components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun _ =>
              2 * (((st (δ + 1)).cs.compSt C).R \ ((st δ).cs.compSt C).R).card :=
            Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b _ =>
              ((hDyn C hC b).2.2.2.2.2.2.2.2.2.2 δ hδ).2.2.2.1
        _ = (components (D.G 0)).sum fun C =>
              (st₀.activeBuckets C).card *
                (2 * (((st (δ + 1)).cs.compSt C).R \ ((st δ).cs.compSt C).R).card) :=
            Finset.sum_congr rfl fun C _ => by simp [Finset.sum_const]
        _ ≤ (components (D.G 0)).sum fun C =>
              B_bound * (2 * (((st (δ + 1)).cs.compSt C).R \ ((st δ).cs.compSt C).R).card) :=
            Finset.sum_le_sum fun C hC => Nat.mul_le_mul_right _ (hB_bound C hC)
        _ = (2 * B_bound) * ((components (D.G 0)).sum fun C =>
              (((st (δ + 1)).cs.compSt C).R \ ((st δ).cs.compSt C).R).card) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun C _ => by ring
        _ = 2 * B_bound * ((st (δ + 1)).cs.RF.R \ (st δ).cs.RF.R).card := by rw [hR_sum]
    have hdel_B : (D.U (s₀ + δ + 1)).length ≤ B_bound * (D.U (s₀ + δ + 1)).length :=
      Nat.le_mul_of_pos_left _ hB1
    rw [hdecomp, Nat.mul_add]
    calc _ ≤ (D.U (s₀ + δ + 1)).length + 2 * B_bound * ((st (δ + 1)).cs.RF.R \ (st δ).cs.RF.R).card :=
          Nat.add_le_add hDel hsp_le
      _ ≤ B_bound * (D.U (s₀ + δ + 1)).length +
            B_bound * (2 * ((st (δ + 1)).cs.RF.R \ (st δ).cs.RF.R).card) := by
          have : 2 * B_bound * ((st (δ + 1)).cs.RF.R \ (st δ).cs.RF.R).card =
              B_bound * (2 * ((st (δ + 1)).cs.RF.R \ (st δ).cs.RF.R).card) := by ring
          omega

/-! ## 2. Item 4 (windowed recourse and encoding) and Item 5 (`WeakHiddenStable`) -/

/-- Item 4 of `IsSpecOrdRestart` for `sparseCoreBundleRestartTool` on a nonempty initial graph:
windowed recourse and encoding size over any non-restarted epoch `[s₀, t]`. -/
theorem bundleRestart_spec_item4 (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (_hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (_hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D)
    (hV₀ : (D.G 0).V.Nonempty) :
    let T := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    let U_S := fun t => (T.runOrdAfterUpdate k M N D ord restarts t).2
    let post := fun t => T.runOrdAfterRestarts k M N D ord restarts t
    ∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r < t → j ∉ restarts r) →
      (((Finset.Icc (s₀ + 1) t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc (s₀ + 1) t).sum fun s => (T.S (post (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        P.γ_r M * ((M : ℝ) / (k : ℝ) +
          (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ)) := by
  intro T P U_S post
  have hValP := bundleCoreParams_valid E
  have hk1 : 1 ≤ k := hk
  have hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e := fun t ht e he =>
    ((hWeak t ht).2.2.2 e he).2.2.1
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  have hγr_nn : 0 ≤ P.γ_r M := by linarith [hValP.2.2.2.2.2.2.1 M]
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hne : ∀ s, (post s).isNonempty = true := fun s =>
    (runOrdAfterRestarts_isNonempty lsfInit E.C_lsst E.L sparsify k M N D ord restarts s).2.1.trans
      (decide_eq_true hV₀)
  intro s₀ t hst htτ j hj hs₀ hNoRest
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
    s₀ (t - s₀) (by omega) ep (fun r => U_S (s₀ + r) j) Hb
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
      (Finset.Icc (s₀ + 1) t).sum (fun s => (U_S s j).length) =
        (Finset.Icc 1 (t - s₀)).sum (fun r => (U_S (s₀ + r) j).length) := by
    refine Finset.sum_bij (fun s _ => s - s₀)
      (fun s hs => by simp only [Finset.mem_Icc] at hs ⊢; omega)
      (fun a ha b hb h => by simp only [Finset.mem_Icc] at ha hb; omega)
      (fun r hr => ⟨s₀ + r, by simp only [Finset.mem_Icc] at hr ⊢; omega, by omega⟩)
      (fun s hs => by simp only [Finset.mem_Icc] at hs; rw [Nat.add_sub_cancel' (by omega)])
  have hEnc_sum_eq :
      (Finset.Icc (s₀ + 1) t).sum (fun s => (T.S (post (s - 1)) j).batchEnc (U_S s j)) =
        (Finset.Icc 1 (t - s₀)).sum (fun r => (ep (r - 1)).S_cur.batchEnc (U_S (s₀ + r) j)) := by
    refine Finset.sum_bij (fun s _ => s - s₀)
      (fun s hs => by simp only [Finset.mem_Icc] at hs ⊢; omega)
      (fun a ha b hb h => by simp only [Finset.mem_Icc] at ha hb; omega)
      (fun r hr => ⟨s₀ + r, by simp only [Finset.mem_Icc] at hr ⊢; omega, by omega⟩)
      (fun s hs => ?_)
    have hs' := Finset.mem_Icc.mp hs
    have hlt : s - s₀ - 1 < t - s₀ := by omega
    have hep : ep (s - s₀ - 1) = (post (s - 1)).trees j := by
      have h1 := (epochBundleSeq_eq_post lsfInit E.C_lsst E.L sparsify k M N D ord restarts s₀ t j hst).1
        (s - s₀ - 1) hlt
      rw [show s₀ + (s - s₀ - 1) = s - 1 by omega] at h1
      exact h1
    rw [hep, show s₀ + (s - s₀) = s by omega]
    dsimp only [T, post]
    rw [sparseCoreBundleRestartTool_S_eq, ite_eq_left (hne (s - 1))]
  set q_ep := (Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length
  have hq_ep_rw : (Finset.Icc (s₀ + 1) (s₀ + (t - s₀))).sum (fun s => (D.U s).length) = q_ep := by
    rw [show s₀ + (t - s₀) = t by omega]
  rw [hq_ep_rw] at hRec
  -- Step 1: Recourse bound (`min (D.G 0).n ((D.G 0).m + 1) ≤ min N (M + 1)`)
  have hn_eff_le : min (D.G 0).n ((D.G 0).m + 1) ≤ min N (M + 1) :=
    min_le_min hN (Nat.add_le_add_right hM 1)
  have hRec_le : bundleRecoursePerQ E.L (E.P_fn M) M (min (D.G 0).n ((D.G 0).m + 1)) (E.B_fn M) ≤
      bundleRecEnv E M := by
    refine le_trans (bundleParams_recoursePerQ_mono_n E.L (E.P_fn M) M hn_eff_le (E.B_fn M)) ?_
    exact (bundleEnv_core_bounds E M (min N (M + 1)) (E.B_fn M) le_rfl
      (min_le_cn_mul_m_add_one E M N)).2.2.2.1
  have hlen_rec :
      (((Finset.Icc 1 (t - s₀)).sum fun r => (U_S (s₀ + r) j).length : ℕ) : ℝ) ≤
        bundleRecEnv E M * (q_ep : ℝ) :=
    le_trans hRec.1 (mul_le_mul_of_nonneg_right hRec_le (Nat.cast_nonneg _))
  have hrec_le_γr : bundleRecEnv E M ≤ P.γ_r M := by
    dsimp only [P, bundleCoreParams]
    have hcm := bundleCostMult_ge_one E M
    have hrb : bundleRecEnv E M ≤ bundleRecBase E M := le_max_left _ _
    have hr_nn : 0 ≤ bundleRecEnv E M := by linarith [bundleRecEnv_ge_four E M]
    nlinarith
  have hC4a :
      (((Finset.Icc (s₀ + 1) t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r M * (q_ep : ℝ) := by
    rw [hUS_sum_eq]
    exact le_trans hlen_rec (mul_le_mul_of_nonneg_right hrec_le_γr (Nat.cast_nonneg _))
  -- Step 2: Encoding bound
  refine ⟨hC4a, ?_⟩
  rw [hEnc_sum_eq]
  by_cases hq0 : q_ep = 0
  · obtain ⟨_, hEnc0⟩ := hRec.2.2 hq0
    rw [hEnc0, Nat.cast_zero]
    exact mul_nonneg hγr_nn (by positivity)
  · have hqτ_le_M : (Finset.Icc 1 τ).sum (fun s => (D.U s).length) ≤ M :=
      (updateThreshold_le_div_k_at hk hN_pos hThresh τ le_rfl).2
    have hq_le_τ : q_ep ≤ (Finset.Icc 1 τ).sum fun s => (D.U s).length :=
      Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc (by omega) htτ)
    have hq_le_M : q_ep ≤ M := le_trans hq_le_τ hqτ_le_M
    have hM_pos : 1 ≤ M := by omega
    have hB_0 : ((ep 0).S_cur.E.card : ℝ) ≤
        bundleSizeFactor E.L (E.P_fn M) M (E.B_fn M) * (M : ℝ) / (k : ℝ) :=
      epochBundleSeq_S_cur_card_le lsfInit E.C_lsst E.L E.hL (E.P_fn M) sparsify
        k M N τ hk1 D ord restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hOrd hThresh s₀ t j hInit_j hst htτ
        hs₀ hNoRest (δ := 0) (Nat.zero_le _) (hHyps.activeBuckets_card_le (N := N) hj)
    have hsf_nn := bundleParams_sizeFactor_nonneg E.L (E.P_fn M) M (E.B_fn M)
    have hγ_sub : bundleSizeFactor E.L (E.P_fn M) M (E.B_fn M) ≤ bundleGammaLEnv E M :=
      le_trans (by linarith) (le_max_right (coreE82Len E.L (E.P_fn M)) _)
    have hm₀_le_S₀ : ((ep 0).S_cur.m : ℝ) ≤ 2 * bundleGammaLEnv E M * ((M : ℝ) / (k : ℝ)) := by
      change ((ep 0).S_cur.E.card : ℝ) ≤ _
      have hS1 : ((ep 0).S_cur.E.card : ℝ) ≤ bundleGammaLEnv E M * (M : ℝ) / (k : ℝ) :=
        le_trans hB_0 (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hγ_sub (Nat.cast_nonneg _)) (by positivity))
      have hγ_nn : 0 ≤ bundleGammaLEnv E M := by linarith [bundleGammaLEnv_ge_three E M]
      have hMk_nn : 0 ≤ (M : ℝ) / (k : ℝ) := by positivity
      linarith [hS1, mul_nonneg hγ_nn hMk_nn,
        show bundleGammaLEnv E M * (M : ℝ) / (k : ℝ) = bundleGammaLEnv E M * ((M : ℝ) / (k : ℝ)) by ring]
    have hkR1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hγ_le_rec : bundleGammaLEnv E M ≤ bundleRecEnv E M := bundleGammaLEnv_le_bundleRecEnv E M
    have hm₀_le_raw : ((ep 0).S_cur.m : ℝ) ≤ 2 * bundleRecEnv E M * (M : ℝ) := by
      have h1 : ((M : ℝ) / (k : ℝ)) ≤ (M : ℝ) := div_le_self (Nat.cast_nonneg _) hkR1
      have hγ_nn : 0 ≤ bundleGammaLEnv E M := by linarith [bundleGammaLEnv_ge_three E M]
      have ha : ((ep 0).S_cur.m : ℝ) ≤ 2 * bundleGammaLEnv E M * (M : ℝ) :=
        le_trans hm₀_le_S₀ (mul_le_mul_of_nonneg_left h1 (by positivity))
      have hb : 2 * bundleGammaLEnv E M * (M : ℝ) ≤ 2 * bundleRecEnv E M * (M : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      exact le_trans ha hb
    have hqR_le : (q_ep : ℝ) ≤ (M : ℝ) := by exact_mod_cast hq_le_M
    have hrec_ge4 : 4 ≤ bundleRecEnv E M := bundleRecEnv_ge_four E M
    have hlog_arg :
        ((ep 0).S_cur.m : ℝ) +
          (((Finset.Icc 1 (t - s₀)).sum fun r => (U_S (s₀ + r) j).length : ℕ) : ℝ) + 2 ≤
          3 * ((M : ℝ) + bundleRecEnv E M * (M : ℝ) + 2) := by
      have hrq : bundleRecEnv E M * (q_ep : ℝ) ≤ bundleRecEnv E M * (M : ℝ) :=
        mul_le_mul_of_nonneg_left hqR_le (by linarith)
      have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
      linarith only [hm₀_le_raw, hlen_rec, hrq, hMnn]
    have harg_pos :
        0 < ((ep 0).S_cur.m : ℝ) +
          (((Finset.Icc 1 (t - s₀)).sum fun r => (U_S (s₀ + r) j).length : ℕ) : ℝ) + 2 := by
      have h1 := Nat.cast_nonneg (α := ℝ) (ep 0).S_cur.m
      have h2 := Nat.cast_nonneg (α := ℝ)
        ((Finset.Icc 1 (t - s₀)).sum fun r => (U_S (s₀ + r) j).length)
      linarith only [h1, h2]
    have hlog1 :
        0 ≤ Real.log (((ep 0).S_cur.m : ℝ) +
          (((Finset.Icc 1 (t - s₀)).sum fun r => (U_S (s₀ + r) j).length : ℕ) : ℝ) + 2) :=
      Real.log_nonneg (by
        have h1 := Nat.cast_nonneg (α := ℝ) (ep 0).S_cur.m
        have h2 := Nat.cast_nonneg (α := ℝ)
          ((Finset.Icc 1 (t - s₀)).sum fun r => (U_S (s₀ + r) j).length)
        linarith only [h1, h2])
    have hlog_big_ge3 : 3 ≤ (M : ℝ) + bundleRecEnv E M * (M : ℝ) + 2 := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_pos
      nlinarith
    have hlog_le :
        Real.log (((ep 0).S_cur.m : ℝ) +
          (((Finset.Icc 1 (t - s₀)).sum fun r => (U_S (s₀ + r) j).length : ℕ) : ℝ) + 2) ≤
          2 * Real.log ((M : ℝ) + bundleRecEnv E M * (M : ℝ) + 2) := by
      have hl1 := Real.log_le_log harg_pos hlog_arg
      have hl_mul : Real.log (3 * ((M : ℝ) + bundleRecEnv E M * (M : ℝ) + 2)) =
          Real.log 3 + Real.log ((M : ℝ) + bundleRecEnv E M * (M : ℝ) + 2) :=
        Real.log_mul (by norm_num) (by linarith)
      have hl3 : Real.log 3 ≤ Real.log ((M : ℝ) + bundleRecEnv E M * (M : ℝ) + 2) :=
        Real.log_le_log (by norm_num) hlog_big_ge3
      linarith
    have hm1 :
        20 * (((ep 0).S_cur.m : ℝ) +
          (((Finset.Icc 1 (t - s₀)).sum fun r => (U_S (s₀ + r) j).length : ℕ) : ℝ)) ≤
          40 * max (bundleGammaLEnv E M) (bundleRecEnv E M) * ((M : ℝ) / (k : ℝ) + (q_ep : ℝ)) := by
      have hm_nn : 0 ≤ (M : ℝ) / (k : ℝ) := by positivity
      have hq_nn : 0 ≤ (q_ep : ℝ) := Nat.cast_nonneg _
      have hM1 := mul_le_mul_of_nonneg_right
        (le_max_left (bundleGammaLEnv E M) (bundleRecEnv E M)) hm_nn
      have hM2 := mul_le_mul_of_nonneg_right
        (le_max_right (bundleGammaLEnv E M) (bundleRecEnv E M)) hq_nn
      have hr_nn : 0 ≤ bundleRecEnv E M := by linarith
      linarith only [hm₀_le_S₀, hlen_rec, hM1, hM2, mul_nonneg hr_nn hq_nn]
    have hm2 := mul_le_mul hm1 hlog_le hlog1 (by
      have : 0 ≤ bundleRecEnv E M := by linarith
      have : 0 ≤ max (bundleGammaLEnv E M) (bundleRecEnv E M) := le_trans this (le_max_right _ _)
      positivity)
    have heq : 40 * max (bundleGammaLEnv E M) (bundleRecEnv E M) * ((M : ℝ) / (k : ℝ) + (q_ep : ℝ)) *
          (2 * Real.log ((M : ℝ) + bundleRecEnv E M * (M : ℝ) + 2)) =
        4 * bundleEncEnv E M * ((M : ℝ) / (k : ℝ) + (q_ep : ℝ)) := by
      unfold bundleEncEnv; ring
    have h1 := le_trans hRec.2.1 (hm2.trans_eq heq)
    exact le_trans h1 (mul_le_mul_of_nonneg_right (four_mul_bundleEncEnv_le_gamma_r E M) (by positivity))

/-- Item 5 of `IsSpecOrdRestart` for `sparseCoreBundleRestartTool` on a nonempty initial graph:
hidden stability on branch `j`'s `coreInstanceOrdFrom` from `s₀` through `t`. -/
theorem bundleRestart_spec_item5 (E : SparseCoreEnv)
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
    ∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r ≤ t → j ∉ restarts r) →
      ∃ Ψ' : ℝ,
        WeakHiddenStable (T.coreInstanceOrdFrom k M N D ord restarts s₀ j) (t - s₀) Ψ'
          (T.coreCOrdFrom k M N D ord restarts c s₀ j)
          (T.coreWOrdFrom k M N D ord restarts w s₀ j) := by
  intro T
  have hk1 : 1 ≤ k := hk
  have hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e := fun t ht e he =>
    ((hWeak t ht).2.2.2 e he).2.2.1
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  let post := fun t => T.runOrdAfterRestarts k M N D ord restarts t
  have hne : ∀ s, (post s).isNonempty = true := fun s =>
    (runOrdAfterRestarts_isNonempty lsfInit E.C_lsst E.L sparsify k M N D ord restarts s).2.1.trans
      (decide_eq_true hV₀)
  intro s₀ t hst htτ j hj hs₀ hNoRest
  have hInit_j := hHyps.hInit j hj
  have hNoRest_lt : ∀ r, s₀ < r → r < t → j ∉ restarts r := fun r h1 h2 => hNoRest r h1 h2.le
  have hInv := epochBundleSeq_inv lsfInit E.C_lsst E.L E.hL (E.P_fn M) sparsify
    k M N τ hk1 D ord restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hOrd hThresh s₀ t j hInit_j hst htτ hs₀
    hNoRest_lt
  have hDyn := epochBundleSeq_dyn_spec lsfInit E.C_lsst E.L E.hL (E.P_fn M) sparsify
    k M N τ hk1 D ord restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit_j hst htτ hs₀ hNoRest_lt
  have hBun := runOrdAfterRestarts_bun_inv lsfInit E.C_lsst E.L sparsify
    k M N τ hk1 D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit_j
  have hSc := runOrdAfterRestarts_S_cur_inv lsfInit E.C_lsst E.L E.hL (E.P_fn M) sparsify
    k M N τ hk1 D ord restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hOrd j hInit_j
  obtain ⟨hSt_base, hSt_step⟩ := epochBundleSeq_steps lsfInit E.C_lsst E.L sparsify
    k M N D ord restarts hV₀ s₀ t j hst hNoRest_lt
  set ep := epochBundleSeq lsfInit E.C_lsst E.L sparsify k M N D ord restarts s₀ t j
  set st₀ := initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
  have hep_post_all : ∀ r ≤ t - s₀, ep r = (post (s₀ + r)).trees j := by
    intro r hr
    by_cases hlt : r < t - s₀
    · exact (epochBundleSeq_eq_post lsfInit E.C_lsst E.L sparsify k M N D ord restarts s₀ t j hst).1 r hlt
    · have hr_eq : r = t - s₀ := by omega
      subst hr_eq
      rw [show s₀ + (t - s₀) = t by omega]
      refine (epochBundleSeq_eq_post lsfInit E.C_lsst E.L sparsify k M N D ord restarts s₀ t j hst).2.1 ?_
      by_cases hlt2 : s₀ < t
      · exact Or.inl (hNoRest t hlt2 le_rfl)
      · exact Or.inr (by omega)
  have hS_eq : ∀ r ≤ t - s₀, (T.coreInstanceOrdFrom k M N D ord restarts s₀ j).G r = (ep r).S_cur := by
    intro r hr
    dsimp only [SparseCoreRestartTool.coreInstanceOrdFrom, T, post]
    rw [sparseCoreBundleRestartTool_S_eq, ite_eq_left (hne (s₀ + r)), hep_post_all r hr]
  have hL_eq : ∀ r ≤ t - s₀, T.lsfs (post (s₀ + r)) j = (ep r).cs.lsf := by
    intro r hr
    dsimp only [T, post]
    rw [sparseCoreBundleRestartTool_lsfs_of_nonempty (hne (s₀ + r)), hep_post_all r hr]
  have hEmb_eq : ∀ r ≤ t - s₀, T.emb (post (s₀ + r)) j = (ep r).emb := by
    intro r hr
    dsimp only [T, post]
    rw [sparseCoreBundleRestartTool_emb_eq, ite_eq_left (hne (s₀ + r)), hep_post_all r hr]
  have hI_ep : ∀ r ≤ t - s₀, CompLSFInv E.C_lsst (D.ℓ 0) (ep r).cs := fun r hr => by
    have hbp := (runOrdAfterRestarts_base_proj lsfInit E.C_lsst E.L sparsify k M N D ord restarts
      hV₀ j (s₀ + r)).1
    rw [(hSt_base r hr).cs, ← hbp.cs]; exact (hBun (s₀ + r) (by omega)).2.2.2.2.2.2.2.1
  have hG0_ep : ∀ r ≤ t - s₀, (ep r).cs.G₀ = D.G 0 := fun r hr => by
    have hbp := (runOrdAfterRestarts_base_proj lsfInit E.C_lsst E.L sparsify k M N D ord restarts
      hV₀ j (s₀ + r)).1
    rw [(hSt_base r hr).cs, ← hbp.cs, (hBun (s₀ + r) (by omega)).2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
  have hG_ep : ∀ r ≤ t - s₀, (ep r).cs.G = D.G (s₀ + r) := fun r hr => by
    have hbp := (runOrdAfterRestarts_base_proj lsfInit E.C_lsst E.L sparsify k M N D ord restarts
      hV₀ j (s₀ + r)).1
    rw [(hSt_base r hr).cs, ← hbp.cs]; exact (hBun (s₀ + r) (by omega)).2.2.2.2.2.2.2.2.1
  have hDisj0 := (initBundleTreeWith_buckets_sum_le lsfInit E.L sparsify (M := M) (N := N) hk1
    (G₀ := D.G 0) (D.ℓ 0) (ord 0) j).2.2.2
  refine ⟨_, bundleTreeState_seq_weakHiddenStable_with lsfInit E.C_lsst E.L E.hL (E.P_fn M) sparsify
    k M N τ hk1 D hG₀ hV₀ hD hLen ord hOrd Ψ c w hWeak j hInit_j s₀ (t - s₀) (by omega) ep
    (T.coreInstanceOrdFrom k M N D ord restarts s₀ j)
    (T.coreCOrdFrom k M N D ord restarts c s₀ j) (T.coreWOrdFrom k M N D ord restarts w s₀ j)
    hS_eq
    (fun r hr => by
      dsimp only [SparseCoreRestartTool.coreInstanceOrdFrom, T]
      rw [show s₀ + (r + 1) = s₀ + r + 1 by omega]; exact (hSt_step r hr).2)
    (fun r hr => by dsimp only [SparseCoreRestartTool.coreInstanceOrdFrom]; rw [hL_eq r hr])
    (fun r hr => by dsimp only [SparseCoreRestartTool.coreCOrdFrom]; rw [hL_eq r hr, hEmb_eq r hr])
    (fun r hr => by dsimp only [SparseCoreRestartTool.coreWOrdFrom]; rw [hL_eq r hr, hEmb_eq r hr])
    (fun r hr => (hSt_step r hr).1)
    (fun r hr => (hSt_base r hr).cs)
    hI_ep hG0_ep hG_ep
    (fun r hr => (hInv.2.2.1 r hr).2.1)
    (fun r hr => by
      have hSc_r := (hSc (s₀ + r) (by omega)).2.2.2.1
      rw [← hep_post_all r hr] at hSc_r
      have hbp := (runOrdAfterRestarts_base_proj lsfInit E.C_lsst E.L sparsify k M N D ord restarts
        hV₀ j (s₀ + r)).1
      have hAB : (ep r).activeBuckets = st₀.activeBuckets := by
        rw [(hSt_base r hr).activeBuckets, ← hbp.activeBuckets]
        exact (hBun (s₀ + r) (by omega)).2.2.2.2.1
      rwa [hAB])
    (fun r hr => by
      have hSp := epochBundleSeq_isSparsifiedCoreGraph lsfInit E.C_lsst E.L E.hL (E.P_fn M) sparsify
        k M N τ hk1 D ord restarts hM hN hHyps.hSp hG₀ hV₀ hD hℓ hLen hOrd hThresh
        s₀ t j hInit_j hst htτ hs₀ hNoRest_lt hr
      exact ⟨hSp.1, hSp.2.1, hSp.2.2.1, hSp.2.2.2.1, hSp.2.2.2.2.1⟩)
    (fun r hr C hC b => by
      have hb := hBun (s₀ + r) (by omega)
      have hbp := (runOrdAfterRestarts_base_proj lsfInit E.C_lsst E.L sparsify k M N D ord restarts
        hV₀ j (s₀ + r)).1
      have hbf := (foldl_bundleRestart_props lsfInit E.C_lsst E.L sparsify
        (T.runOrdAfterUpdate k M N D ord restarts (s₀ + r)).1 (restarts (s₀ + r))).2.2.2.2.1 j
      have hkr : (ep r).k = k := by rw [(hSt_base r hr).k, ← hbp.k]; exact hb.1
      have hc := (hb.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b
      have hst := (hInv.2.2.1 r hr).2.2 C hC b
      refine ⟨fun ρ hρ => ?_, ?_, ?_, hst.1, hst.2.2.2.1, hst.2.2.2.2.2.2.1⟩
      · have hR : BundleCompReady (ep r).cs C ((ep r).bun (C, b)) k (ord (s₀ + r)) := by
          rw [hep_post_all r hr]; exact hc.2.1
        rw [hkr]
        exact hR.1 ρ (hI_ep r hr).hG_val (compLSF_RF_isRSF (hI_ep r hr)) hρ
      · have hR : BundleCompReady (ep r).cs C ((ep r).bun (C, b)) k (ord (s₀ + r)) := by
          rw [hep_post_all r hr]; exact hc.2.1
        exact hR.2.1
      · refine Finset.disjoint_left.mpr fun e he hX => ?_
        have hcs_eq : ((post (s₀ + r)).trees j).cs =
            ((T.runOrdAfterUpdate k M N D ord restarts (s₀ + r)).1.trees j).cs := hbf.cs
        have hdisj : Disjoint ((ep r).bun (C, b)).edges (ep r).cs.insertedGlobal := by
          rw [hep_post_all r hr, hc.2.2.2.1, hcs_eq]; exact hc.2.2.2.2.1
        exact Finset.disjoint_left.mp hdisj he ((hI_ep r hr).hCross_sub hX))
    (fun r hr C₁ hC₁ C₂ hC₂ b₁ b₂ x hx₁ hx₂ => by
      have hb := hBun (s₀ + r) (by omega)
      have hc₁ := (hb.2.2.2.2.2.2.2.2.2.2.2 C₁ hC₁).2 b₁
      have hc₂ := (hb.2.2.2.2.2.2.2.2.2.2.2 C₂ hC₂).2 b₂
      rw [hep_post_all r hr, hc₁.2.2.2.1, hc₁.2.2.1] at hx₁
      rw [hep_post_all r hr, hc₂.2.2.2.1, hc₂.2.2.1] at hx₂
      by_contra hne
      have hne' : (C₁, b₁) ≠ (C₂, b₂) := fun h => hne ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
      exact Finset.disjoint_left.mp (hDisj0 C₁ hC₁ C₂ hC₂ b₁ b₂ hne')
        (Finset.mem_sdiff.mp hx₁).1 (Finset.mem_sdiff.mp hx₂).1)
    (fun r hr C hC b => by
      have hst := (hDyn C hC b).2.2.2.2.2.2.2.2.2.2 r hr
      have hsub : ((ep (r + 1)).bun (C, b)).edges ⊆ ((ep r).bun (C, b)).edges := by
        have hE1 : ((ep r).bun (C, b)).edges =
            (st₀.bun (C, b)).edges \ (Finset.Icc 1 (s₀ + r)).biUnion (fun s => batchDeletes (D.U s)) := by
          rw [hep_post_all r hr.le]
          have hc := ((hBun (s₀ + r) (by omega)).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b
          rw [hc.2.2.2.1, hc.2.2.1]
        have hE2 : ((ep (r + 1)).bun (C, b)).edges =
            (st₀.bun (C, b)).edges \
              (Finset.Icc 1 (s₀ + (r + 1))).biUnion (fun s => batchDeletes (D.U s)) := by
          rw [hep_post_all (r + 1) hr]
          have hc := ((hBun (s₀ + (r + 1)) (by omega)).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b
          rw [hc.2.2.2.1, hc.2.2.1]
        rw [hE1, hE2]
        exact Finset.sdiff_subset_sdiff Finset.Subset.rfl
          (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.Icc_subset_Icc_right (by omega)))
      exact ⟨hsub, hst.2.2.2.2.2.2⟩)
    (fun r hr C hC b =>
      let hs := (hInv.2.2.2.1 r hr).2.2.2.1 C hC b
      ⟨hs.1, hs.2.1, hs.2.2.2.1, hs.2.2.2.2⟩)⟩

/-! ## 3. Combined non-cost specification (items 1–6, nonempty and empty graphs) -/

/-- Items 1, 2, non-cost item 3, and items 4, 5, 6 of `SparseCoreRestartTool.IsSpecOrdRestart`
for `sparseCoreBundleRestartTool` on one instance under `BundleCoreHypsAt` (handling both
nonempty and empty initial graphs). -/
theorem bundleRestart_spec_noCost (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D) :
    let T := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    let pre := fun t => (T.runOrdAfterUpdate k M N D ord restarts t).1
    let U_S := fun t => (T.runOrdAfterUpdate k M N D ord restarts t).2
    let post := fun t => T.runOrdAfterRestarts k M N D ord restarts t
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (post t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (post t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ M) (P.γ_c M) M
        (T.S (post t) j) (T.emb (post t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (post t) j).F.R.card : ℝ) ≤
          P.c_R * ((M : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((N : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (post t) j).F.F.E ⊆ (T.lsfs (post (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (post t) j).wstr e = (T.lsfs (post (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (post t) j).wstr e = 1) ∧
      (T.S (post (t - 1)) j).BatchIsValid (U_S t j) ∧
      T.S (pre t) j = (T.S (post (t - 1)) j).applyBatch (U_S t j)) ∧
    (∀ r ≤ τ, ∀ (p : List ℕ) (j' : ℕ), p ++ [j'] <+: restarts r →
      let st' := p.foldl T.restart (pre r)
      (∀ b < k, T.lsfs (T.restart st' j') b = T.lsfs st' b) ∧
      (∀ b < k, b ≠ j' →
        T.S (T.restart st' j') b = T.S st' b ∧
        T.emb (T.restart st' j') b = T.emb st' b ∧
        T.rot (T.restart st' j') b = T.rot st' b) ∧
      T.cost st' ≤ T.cost (T.restart st' j')) ∧
    (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r < t → j ∉ restarts r) →
      (((Finset.Icc (s₀ + 1) t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc (s₀ + 1) t).sum fun s => (T.S (post (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        P.γ_r M * ((M : ℝ) / (k : ℝ) +
          (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
    (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r ≤ t → j ∉ restarts r) →
      ∃ Ψ' : ℝ,
        WeakHiddenStable (T.coreInstanceOrdFrom k M N D ord restarts s₀ j) (t - s₀) Ψ'
          (T.coreCOrdFrom k M N D ord restarts c s₀ j)
          (T.coreWOrdFrom k M N D ord restarts w s₀ j)) ∧
    (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r ≤ t → j ∉ restarts r) →
      OrderedUpTo (T.coreInstanceOrdFrom k M N D ord restarts s₀ j) (t - s₀) 2
        (fun δ => T.rot (post (s₀ + δ)) j)) := by
  intro T P pre U_S post
  have hValP := bundleCoreParams_valid E
  have hk1 : 1 ≤ k := hk
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := fun e he =>
    ((hWeak 0 (Nat.zero_le τ)).2.2.2 e he).2.2.1
  have hItem6 : ∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r ≤ t → j ∉ restarts r) →
      OrderedUpTo (T.coreInstanceOrdFrom k M N D ord restarts s₀ j) (t - s₀) 2
        (fun δ => T.rot (post (s₀ + δ)) j) := fun s₀ t hst htτ j hj _ hNoR =>
    epochBundleSeq_orderedUpTo lsfInit E.C_lsst E.L E.hL (E.P_fn M) sparsify
      k M N τ hk1 D ord restarts hM hN hHyps.hSp hG₀ hℓ₀ hD hOrd s₀ t j (hHyps.hInit j hj) hst htτ hNoR
  by_cases hV₀ : (D.G 0).V.Nonempty
  · exact ⟨bundleRestart_spec_item1 E lsfInit sparsify k τ M N D ord restarts Ψ c w hk hG₀ hD hLen
        hWeak hOrd hM hN hrest hThresh hHyps hV₀,
      bundleRestart_spec_item2 E lsfInit sparsify k τ M N D ord restarts Ψ c w hk hG₀ hD hLen
        hWeak hOrd hM hN hrest hHyps hV₀,
      bundleRestart_spec_item3_nonCost E lsfInit sparsify k τ M N D ord restarts,
      bundleRestart_spec_item4 E lsfInit sparsify k τ M N D ord restarts Ψ c w hk hG₀ hD hLen
        hWeak hOrd hM hN hrest hThresh hHyps hV₀,
      bundleRestart_spec_item5 E lsfInit sparsify k τ M N D ord restarts Ψ c w hk hG₀ hD hLen
        hWeak hOrd hM hN hrest hThresh hHyps hV₀,
      hItem6⟩
  · have hγr_nn : 0 ≤ P.γ_r M := by linarith [hValP.2.2.2.2.2.2.1 M]
    obtain ⟨hG_empty, _⟩ := empty_dyn_eq hG₀ hV₀ hD
    have hrunE := runOrdAfterRestarts_empty_case lsfInit E.C_lsst E.L sparsify k M N D ord restarts hV₀
    have hL_eq : ∀ t j, T.lsfs (post t) j = emptyLSF := fun t j => by
      dsimp only [T, post]; exact sparseCoreBundleRestartTool_lsfs_of_empty (hrunE t).2.1 j
    have hS_eq : ∀ t j, T.S (post t) j = emptyGraph := fun t j => by
      dsimp only [T, post]
      rw [sparseCoreBundleRestartTool_S_eq, (hrunE t).2.1]; rfl
    have hEmb_eq : ∀ t j, T.emb (post t) j = fun _ => [] := fun t j => by
      dsimp only [T, post]
      rw [sparseCoreBundleRestartTool_emb_eq, (hrunE t).2.1]; rfl
    have hUS_eq : ∀ t j, U_S t j = [] := fun t j => by
      dsimp only [U_S, T]; rw [(hrunE t).2.2]
    refine ⟨?_, ?_, bundleRestart_spec_item3_nonCost E lsfInit sparsify k τ M N D ord restarts,
      ?_, ?_, hItem6⟩
    · intro t ht j _
      have hGt := hG_empty t ht
      rw [hL_eq t j, hS_eq t j, hEmb_eq t j]
      refine ⟨emptyLSF_holds hGt.1 hGt.2.1 (D.ℓ t) (P.σ k (D.G t).n), ?_, ?_⟩
      · have hCG_V : (coreGraph (D.G t) emptyLSF).V = ∅ := rfl
        have hCG_E : (coreGraph (D.G t) emptyLSF).E = ∅ := by simp [coreGraph, emptyLSF, hGt.2.2]
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
          have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
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
      have hS_pre : T.S (pre t) j = emptyGraph := by
        dsimp only [T, pre]; rw [sparseCoreBundleRestartTool_S_eq, (hrunE t).1]; rfl
      rw [hL_eq t j, hL_eq (t - 1) j, hS_eq (t - 1) j, hS_pre, hUS_eq t j]
      have hGtE := (hG_empty t htτ).2.2
      refine ⟨Finset.Subset.rfl, fun e he => by simp [hGtE] at he,
        fun e he => by simp [hGtE] at he, trivial, rfl⟩
    · intro s₀ t _ _ j _ _ _
      simp only [hUS_eq, List.length_nil, Finset.sum_const_zero, Nat.cast_zero, MGraph.batchEnc]
      exact ⟨mul_nonneg hγr_nn (Nat.cast_nonneg _), mul_nonneg hγr_nn (by positivity)⟩
    · intro s₀ t _ _ j _ _ _
      refine ⟨max Ψ 0, fun r _ => ?_⟩
      have hSE : ((T.coreInstanceOrdFrom k M N D ord restarts s₀ j).G r).E = ∅ := by
        dsimp only [SparseCoreRestartTool.coreInstanceOrdFrom]
        rw [hS_eq (s₀ + r) j]; rfl
      have hSV : ((T.coreInstanceOrdFrom k M N D ord restarts s₀ j).G r).V = ∅ := by
        dsimp only [SparseCoreRestartTool.coreInstanceOrdFrom]
        rw [hS_eq (s₀ + r) j]; rfl
      exact ⟨fun v hv => by simp [hSV] at hv,
        ⟨fun v hv => by simp [hSV] at hv, fun e he => by simp [hSE] at he⟩,
        fun e he => by simp [hSE] at he,
        fun e he => by simp [hSE] at he⟩

end MinCostFlow.Chain

end
