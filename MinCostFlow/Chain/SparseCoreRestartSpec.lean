module

public import MinCostFlow.Chain.SparseCoreRestartItems123
import MinCostFlow.Chain.SparseCoreRestartEpoch
import MinCostFlow.SparseCore.Lemma517
import MinCostFlow.SparseCore.SparseCoreBounds
import MinCostFlow.SparseCore.SparseCoreCost
import MinCostFlow.SparseCore.SparseCoreRecourse
import MinCostFlow.SparseCore.SparseCoreMetrics
import MinCostFlow.SparseCore.SparseCoreRunBounds
import MinCostFlow.SparseCore.SparseCoreSpannerMetrics
import MinCostFlow.SparseCore.SparseCoreStability
import MinCostFlow.DynSpanner.Complexity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The restart specification of `sparseCoreRestartTool`, except its cost bounds

`SparseCoreRestartTool.IsSpecRestart` (Lemma 5.17 with restarts) has six items. Together with
`SparseCoreRestartItems123.lean` (items 1, 2, and non-cost item 3), this file proves items 4 and 5
and packages items 1–5 (without cost bounds) as `sparseCoreRestart_spec_noCost_noComp`, using the
update budget at `(M, N)` directly (no `hThresh₀`).
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner

/-- Item 4 of `IsSpecRestart` for `sparseCoreRestartTool` on a nonempty initial graph: recourse and
encoding size of the spanner batches over one epoch. -/
theorem sparseCoreRestart_spec_item4_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (_hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : SparseCoreCoreHypsAt E oracle sparsify k M D)
    (hV₀ : (D.G 0).V.Nonempty) :
    let T := sparseCoreRestartTool oracle E.C_lsst E.L sparsify
    let P := sparseCoreParams E
    let U_S := fun t => (T.runAfterUpdate k M N D restarts t).2
    let post := fun t => T.runAfterRestarts k M N D restarts t
    ∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
        (s₀ = 0 ∨ j ∈ restarts s₀) →
        (∀ r, s₀ < r → r < t → j ∉ restarts r) →
        (((Finset.Icc (s₀ + 1) t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
          P.γ_r M * (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
        (((Finset.Icc (s₀ + 1) t).sum fun s => (T.S (post (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
          P.γ_r M * ((M : ℝ) / (k : ℝ) +
            (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ)) := by
  intro T P U_S post
  have hValP := sparseCoreParams_valid E
  have hk1 : 1 ≤ k := hk
  have hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e := fun t ht e he =>
    ((hWeak t ht).2.2.2 e he).2.2.1
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  have hγr_nn : 0 ≤ P.γ_r M := by linarith [hValP.2.2.2.2.2.2.1 M]
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hne : ∀ s, (post s).isNonempty = true := fun s =>
    (runAfterRestarts_isNonempty oracle E.C_lsst E.L sparsify k M N D restarts s).2.1.trans
      (decide_eq_true hV₀)
  have hSc := runAfterRestarts_S_cur_inv oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify hHyps.hLSST
    k M N τ hk1 D restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD
  intro s₀ t hst htτ j hj hs₀ hNoRest
  have hInv := epochTreeSeq_inv oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify hHyps.hLSST
    k M N τ hk1 D restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hThresh s₀ t j hj hst htτ hs₀ hNoRest
  obtain ⟨hSt_base, hSt_step⟩ := epochTreeSeq_steps oracle E.C_lsst E.L sparsify
    k M N D restarts hV₀ s₀ t j hst hNoRest
  set ep := epochTreeSeq oracle E.C_lsst E.L sparsify k M N D restarts s₀ t j
  set Hb := fun C b => restartBucketGraph (ep 0) C b
  have hRec := epoch_recourse_and_enc_min oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify hHyps.hLSST
    k M N τ hk1 D hG₀ hV₀ hℓ₀ hD hM hN hThresh j (E.B_fn M) (hHyps.hB_bound j hj)
    s₀ (t - s₀) (by omega) ep (fun r => (T.runAfterUpdate k M N D restarts (s₀ + r)).2 j) Hb
    (fun C hC b => ⟨le_trans (hInv.1 C hC b).2.1 hM, (hInv.1 C hC b).2.2.1⟩)
    (fun r hr => (hSt_step r hr).1)
    (fun r hr => by rw [show s₀ + (r + 1) = s₀ + r + 1 by omega]; exact (hSt_step r hr).2)
    (fun r hr => (hSt_base r hr).cs)
    (fun r hr => (hSt_base r hr).ts)
    (fun r hr => (hSt_base r hr).activeBuckets)
    (fun r hr => by
      have hs := hInv.2.2.1 r hr
      refine ⟨hs.1, hs.2.1, fun C hC b => ?_⟩
      have hcb := hs.2.2 C hC b
      exact ⟨hcb.2.2.2.2.1, hcb.2.2.2.2.2.1, hcb.2.2.2.2.2.2.2.2.1⟩)
    (fun r hr => by
      have hst' := hInv.2.2.2.1 r hr
      exact ⟨hst'.1, hst'.2.1, hst'.2.2.1,
        fun C hC b => ⟨(hst'.2.2.2.1 C hC b).2.1, (hst'.2.2.2.1 C hC b).2.2.1,
          (hst'.2.2.2.1 C hC b).2.2.2.1⟩,
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
        (Finset.Icc 1 (t - s₀)).sum (fun r =>
          (ep (r - 1)).S_cur.batchEnc (U_S (s₀ + r) j)) := by
    refine Finset.sum_bij (fun s _ => s - s₀)
      (fun s hs => by simp only [Finset.mem_Icc] at hs ⊢; omega)
      (fun a ha b hb h => by simp only [Finset.mem_Icc] at ha hb; omega)
      (fun r hr => ⟨s₀ + r, by simp only [Finset.mem_Icc] at hr ⊢; omega, by omega⟩)
      (fun s hs => ?_)
    have hs' := Finset.mem_Icc.mp hs
    have hlt : s - s₀ - 1 < t - s₀ := by omega
    have hep : ep (s - s₀ - 1) = (post (s - 1)).trees j := by
      have h1 := (epochTreeSeq_eq_post oracle E.C_lsst E.L sparsify k M N D restarts s₀ t j hst).1
        (s - s₀ - 1) hlt
      rw [show s₀ + (s - s₀ - 1) = s - 1 by omega] at h1
      exact h1
    rw [hep, show s₀ + (s - s₀) = s by omega]
    dsimp only [T, post]
    rw [sRT_S_of_nonempty (hne (s - 1)) j]
  set q_ep := (Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length
  have hq_ep_rw : (Finset.Icc (s₀ + 1) (s₀ + (t - s₀))).sum (fun s => (D.U s).length) = q_ep := by
    rw [show s₀ + (t - s₀) = t by omega]
  rw [hq_ep_rw] at hRec
  -- Step 1: Recourse bound
  have hn_eff_le : min (D.G 0).n ((D.G 0).m + 1) ≤ min N (M + 1) :=
    min_le_min hN (Nat.add_le_add_right hM 1)
  have hRec_le : coreRecoursePerQ E.L (E.P_fn M) M (min (D.G 0).n ((D.G 0).m + 1)) (D.G 0).maxDeg (E.B_fn M) ≤
      recEnv E M := by
    refine le_trans (coreRecoursePerQ_mono_n E.L (E.P_fn M) M hn_eff_le (D.G 0).maxDeg (E.B_fn M)) ?_
    exact (env_core_bounds E M (min N (M + 1)) (D.G 0).maxDeg 0 (E.B_fn M)
      le_rfl (by exact_mod_cast hHyps.hDeg_bound.1)
      (by exact_mod_cast Nat.zero_le (E.d_fn M)) (min_le_cn_mul_m_add_one E M N)).2.2.2.1
  have hlen_rec :
      (((Finset.Icc 1 (t - s₀)).sum fun r => (U_S (s₀ + r) j).length : ℕ) : ℝ) ≤
        recEnv E M * (q_ep : ℝ) :=
    le_trans hRec.1 (mul_le_mul_of_nonneg_right hRec_le (Nat.cast_nonneg _))
  have hrec_le_γr : recEnv E M ≤ P.γ_r M := by
    dsimp only [P, sparseCoreParams]
    have hcm := costMult_ge_one E M
    have hrb : recEnv E M ≤ recBase E M := le_max_left _ _
    have hr_nn : 0 ≤ recEnv E M := by linarith [recEnv_ge_four E M]
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
    have hSt_0 := (epochTreeSeq_steps oracle E.C_lsst E.L sparsify
      k M N D restarts hV₀ s₀ t j hst hNoRest).1 0 (Nat.zero_le _)
    have hep0 : ep 0 = (post s₀).trees j := by
      have := (epochTreeSeq_eq_post oracle E.C_lsst E.L sparsify k M N D restarts s₀ t j hst).1
      by_cases hlt : 0 < t - s₀
      · simpa using this 0 hlt
      · have heq : s₀ = t := by omega
        have h2 := (epochTreeSeq_eq_post oracle E.C_lsst E.L sparsify k M N D restarts s₀ t j hst).2.1
          (Or.inr heq)
        rw [show t - s₀ = 0 by omega] at h2
        rw [heq]
        exact h2
    have hSc_0 := (hSc j s₀ (le_trans hst htτ)).2
    have hStg_0 := hInv.2.2.1 0 (Nat.zero_le _)
    rw [← hep0] at hSc_0
    rw [Nat.add_zero] at hSt_0
    obtain ⟨hBaseT, _, _⟩ := treeRunSeq_tilde_core_inv oracle E.C_lsst E.L sparsify
      hHyps.hLSST k M N τ hk1 D hG₀ hV₀ hℓ₀ hD j
    have hOB0 : (ep 0).origBucket =
        fun e => bucketOf (coreLen (initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j).lsf
          (safeLen (D.G 0) (D.ℓ 0)) e) :=
      hSt_0.origBucket.trans (hBaseT s₀ (le_trans hst htτ)).2.2.2.2.1
    have hSp_0 := treeCoreState_isSparsifiedCoreGraph oracle E.C_lsst E.L E.hL (E.P_fn M)
      sparsify hHyps.hLSST k M N τ hk1 D hG₀ hV₀ hD hℓ hLen hM hN hThresh hHyps.hSp j hj s₀
      (le_trans hst htτ) (ep 0) hOB0 hSt_0.cs hSt_0.ts hSt_0.activeComps
      hSc_0.2.1 hSc_0.2.2.1 hSc_0.2.2.2
      (fun C hC b =>
        let cb := hStg_0.2.2 C hC b
        ⟨cb.1, cb.2.1,
          cb.2.2.1.trans (origBucket_filter_safe_eq oracle E.C_lsst hk1 hG₀ hV₀ hℓ₀ hC hHyps.hLSST
            (hSt_0.ts.symm ▸ ((hBaseT s₀ (le_trans hst htτ)).2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.1)
            hOB0 b),
          cb.2.2.2.1⟩)
      (fun C hC b =>
        let cb := hStg_0.2.2 C hC b
        ⟨cb.2.2.2.2.1, cb.2.2.2.2.2.2.1, cb.2.2.2.2.2.2.2.1,
          cb.2.2.2.2.2.2.2.2.1, cb.2.2.2.2.2.2.2.2.2.1, cb.2.2.2.2.2.2.2.2.2.2⟩)
    dsimp only at hSp_0
    have hB_0 := hSp_0.2.2.2.2.2.2 (E.B_fn M) (hHyps.hB_bound j hj)
    have hγ_sub : ((E.L + 1 : ℝ) * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
          coreLambdaS (E.P_fn M) M * (E.B_fn M : ℝ) * (2 * ((D.G 0).maxDeg : ℝ) + 190) + 115) ≤
        gammaLEnv E M := by
      have h11 : ((E.L + 1 : ℝ) * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
            coreLambdaS (E.P_fn M) M * (E.B_fn M : ℝ) * (2 * ((D.G 0).maxDeg : ℝ) + 190) + 115) ≤
          11 * ((E.L + 1 : ℝ) * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
            coreLambdaS (E.P_fn M) M * (E.B_fn M : ℝ) * (2 * ((D.G 0).maxDeg : ℝ) + 190) + 115) := by
        have hKs := (E.P_fn M).hK_s
        have hγ : 0 ≤ (E.P_fn M).γ_ℓ := by linarith [(E.P_fn M).hγ_ℓ]
        have hlam := coreLambdaS_pos (E.P_fn M) M
        have : 0 ≤ (E.L + 1 : ℝ) * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
            coreLambdaS (E.P_fn M) M * (E.B_fn M : ℝ) * (2 * ((D.G 0).maxDeg : ℝ) + 190) + 115 := by
          positivity
        linarith
      refine le_trans h11 (le_trans ?_ (le_max_right _ _))
      have hdk : (0 : ℝ) ≤ ((E.L : ℝ) + 1) * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
          coreLambdaS (E.P_fn M) M * (E.B_fn M : ℝ) := by
        have := (E.P_fn M).hK_s; have := (E.P_fn M).hγ_ℓ
        have := coreLambdaS_pos (E.P_fn M) M; positivity
      have hd_le : ((D.G 0).maxDeg : ℝ) ≤ (E.d_fn M : ℝ) := by exact_mod_cast hHyps.hDeg_bound.1
      gcongr
    have hm₀_le_S₀ : ((ep 0).S_cur.m : ℝ) ≤ 2 * gammaLEnv E M * ((M : ℝ) / (k : ℝ)) := by
      change ((ep 0).S_cur.E.card : ℝ) ≤ _
      have hS1 : ((ep 0).S_cur.E.card : ℝ) ≤ gammaLEnv E M * (M : ℝ) / (k : ℝ) :=
        le_trans hB_0 (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hγ_sub (Nat.cast_nonneg _)) (by positivity))
      have hγ_nn : 0 ≤ gammaLEnv E M := by linarith [gammaLEnv_ge_three E M]
      have hMk_nn : 0 ≤ (M : ℝ) / (k : ℝ) := by positivity
      linarith [hS1, mul_nonneg hγ_nn hMk_nn,
        show gammaLEnv E M * (M : ℝ) / (k : ℝ) = gammaLEnv E M * ((M : ℝ) / (k : ℝ)) by ring]
    have hkR1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hγ_le_rec : gammaLEnv E M ≤ recEnv E M := gammaLEnv_le_recEnv E M
    have hm₀_le_raw : ((ep 0).S_cur.m : ℝ) ≤ 2 * recEnv E M * (M : ℝ) := by
      have h1 : ((M : ℝ) / (k : ℝ)) ≤ (M : ℝ) := div_le_self (Nat.cast_nonneg _) hkR1
      have hγ_nn : 0 ≤ gammaLEnv E M := by linarith [gammaLEnv_ge_three E M]
      have ha : ((ep 0).S_cur.m : ℝ) ≤ 2 * gammaLEnv E M * (M : ℝ) :=
        le_trans hm₀_le_S₀ (mul_le_mul_of_nonneg_left h1 (by positivity))
      have hb : 2 * gammaLEnv E M * (M : ℝ) ≤ 2 * recEnv E M * (M : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      exact le_trans ha hb
    have hqR_le : (q_ep : ℝ) ≤ (M : ℝ) := by exact_mod_cast hq_le_M
    have hrec_ge4 : 4 ≤ recEnv E M := recEnv_ge_four E M
    have hlog_arg :
        ((ep 0).S_cur.m : ℝ) +
          (((Finset.Icc 1 (t - s₀)).sum fun r => (U_S (s₀ + r) j).length : ℕ) : ℝ) + 2 ≤
          3 * ((M : ℝ) + recEnv E M * (M : ℝ) + 2) := by
      have hrq : recEnv E M * (q_ep : ℝ) ≤ recEnv E M * (M : ℝ) :=
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
    have hlog_big_ge3 : 3 ≤ (M : ℝ) + recEnv E M * (M : ℝ) + 2 := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_pos
      nlinarith
    have hlog_le :
        Real.log (((ep 0).S_cur.m : ℝ) +
          (((Finset.Icc 1 (t - s₀)).sum fun r => (U_S (s₀ + r) j).length : ℕ) : ℝ) + 2) ≤
          2 * Real.log ((M : ℝ) + recEnv E M * (M : ℝ) + 2) := by
      have hl1 := Real.log_le_log harg_pos hlog_arg
      have hl_mul : Real.log (3 * ((M : ℝ) + recEnv E M * (M : ℝ) + 2)) =
          Real.log 3 + Real.log ((M : ℝ) + recEnv E M * (M : ℝ) + 2) :=
        Real.log_mul (by norm_num) (by linarith)
      have hl3 : Real.log 3 ≤ Real.log ((M : ℝ) + recEnv E M * (M : ℝ) + 2) :=
        Real.log_le_log (by norm_num) hlog_big_ge3
      linarith
    have hlog_outer : 0 ≤ Real.log ((M : ℝ) + recEnv E M * (M : ℝ) + 2) :=
      Real.log_nonneg (by linarith)
    have hm1 :
        20 * (((ep 0).S_cur.m : ℝ) +
          (((Finset.Icc 1 (t - s₀)).sum fun r => (U_S (s₀ + r) j).length : ℕ) : ℝ)) ≤
          40 * max (gammaLEnv E M) (recEnv E M) * ((M : ℝ) / (k : ℝ) + (q_ep : ℝ)) := by
      have hm_nn : 0 ≤ (M : ℝ) / (k : ℝ) := by positivity
      have hq_nn : 0 ≤ (q_ep : ℝ) := Nat.cast_nonneg _
      have hM1 := mul_le_mul_of_nonneg_right (le_max_left (gammaLEnv E M) (recEnv E M)) hm_nn
      have hM2 := mul_le_mul_of_nonneg_right (le_max_right (gammaLEnv E M) (recEnv E M)) hq_nn
      have hr_nn : 0 ≤ recEnv E M := by linarith
      linarith only [hm₀_le_S₀, hlen_rec, hM1, hM2, mul_nonneg hr_nn hq_nn]
    have hm2 := mul_le_mul hm1 hlog_le hlog1 (by
      have : 0 ≤ recEnv E M := by linarith
      have : 0 ≤ max (gammaLEnv E M) (recEnv E M) := le_trans this (le_max_right _ _)
      positivity)
    have heq : 40 * max (gammaLEnv E M) (recEnv E M) * ((M : ℝ) / (k : ℝ) + (q_ep : ℝ)) *
          (2 * Real.log ((M : ℝ) + recEnv E M * (M : ℝ) + 2)) =
        4 * encEnv E M * ((M : ℝ) / (k : ℝ) + (q_ep : ℝ)) := by
      unfold encEnv; ring
    have h4enc_le_γr : 4 * encEnv E M ≤ P.γ_r M := by
      dsimp only [P, sparseCoreParams]
      have h1 : encEnv E M ≤ recBase E M := le_max_right _ _
      have hcm4 : 4 ≤ costMult E M := costMult_ge_four E M
      have h3 : 0 ≤ encEnv E M := by
        have : 0 ≤ recEnv E M := by linarith
        have : 0 ≤ max (gammaLEnv E M) (recEnv E M) := le_trans this (le_max_right _ _)
        unfold encEnv; positivity
      have hrb_nn : 0 ≤ recBase E M := le_trans h3 h1
      have h4 := mul_le_mul_of_nonneg_left hcm4 hrb_nn
      linarith only [h1, h4]
    have h1 := le_trans hRec.2.1 (hm2.trans_eq heq)
    exact le_trans h1 (mul_le_mul_of_nonneg_right h4enc_le_γr (by positivity))

/-- Item 5 of `IsSpecRestart` for `sparseCoreRestartTool` on a nonempty initial graph: hidden
stability of the core instance over one epoch. -/
theorem sparseCoreRestart_spec_item5_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (_hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : SparseCoreCoreHypsAt E oracle sparsify k M D)
    (hV₀ : (D.G 0).V.Nonempty) :
    let T := sparseCoreRestartTool oracle E.C_lsst E.L sparsify
    ∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
        (s₀ = 0 ∨ j ∈ restarts s₀) →
        (∀ r, s₀ < r → r ≤ t → j ∉ restarts r) →
        ∃ Ψ' : ℝ,
          WeakHiddenStable (T.coreInstanceFrom k M N D restarts s₀ j) (t - s₀) Ψ'
            (T.coreCFrom k M N D restarts c s₀ j) (T.coreWFrom k M N D restarts w s₀ j) := by
  intro T
  have hk1 : 1 ≤ k := hk
  have hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e := fun t ht e he =>
    ((hWeak t ht).2.2.2 e he).2.2.1
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  let post := fun t => T.runAfterRestarts k M N D restarts t
  have hne : ∀ s, (post s).isNonempty = true := fun s =>
    (runAfterRestarts_isNonempty oracle E.C_lsst E.L sparsify k M N D restarts s).2.1.trans
      (decide_eq_true hV₀)
  have hSc := runAfterRestarts_S_cur_inv oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify hHyps.hLSST
    k M N τ hk1 D restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD
  intro s₀ t hst htτ j hj hs₀ hNoRest
  have hNoRest_lt : ∀ r, s₀ < r → r < t → j ∉ restarts r := fun r hr1 hr2 =>
    hNoRest r hr1 hr2.le
  have hInv := epochTreeSeq_inv oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify hHyps.hLSST
    k M N τ hk1 D restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hThresh s₀ t j hj hst htτ hs₀ hNoRest_lt
  obtain ⟨hSt_base, hSt_step⟩ := epochTreeSeq_steps oracle E.C_lsst E.L sparsify
    k M N D restarts hV₀ s₀ t j hst hNoRest_lt
  set ep := epochTreeSeq oracle E.C_lsst E.L sparsify k M N D restarts s₀ t j
  have hep_post_all : ∀ r ≤ t - s₀, ep r = (post (s₀ + r)).trees j := by
    intro r hr
    by_cases hlt : r < t - s₀
    · exact (epochTreeSeq_eq_post oracle E.C_lsst E.L sparsify k M N D restarts s₀ t j hst).1 r hlt
    · have hr_eq : r = t - s₀ := by omega
      subst hr_eq
      rw [show s₀ + (t - s₀) = t by omega]
      refine (epochTreeSeq_eq_post oracle E.C_lsst E.L sparsify k M N D restarts s₀ t j hst).2.1 ?_
      by_cases hlt2 : s₀ < t
      · exact Or.inl (hNoRest t hlt2 le_rfl)
      · exact Or.inr (by omega)
  obtain ⟨hBaseT, _, _⟩ := treeRunSeq_tilde_core_inv oracle E.C_lsst E.L sparsify hHyps.hLSST
    k M N τ hk1 D hG₀ hV₀ hℓ₀ hD j
  have hSpM : ∀ r ≤ t - s₀,
      (coreGraph (D.G (s₀ + r)) (ep r).cs.lsf).IsSubgraph (ep r).S_cur ∧
      (ep r).emb.IsEmbedding (coreGraph (D.G (s₀ + r)) (ep r).cs.lsf) (ep r).S_cur ∧
      (∀ e ∈ (coreGraph (D.G (s₀ + r)) (ep r).cs.lsf).E, ∀ e' ∈ walkEdges ((ep r).emb e),
        approx2 (coreLen (ep r).cs.lsf (D.ℓ (s₀ + r)) e)
          (coreLen (ep r).cs.lsf (D.ℓ (s₀ + r)) e')) ∧
      ((ep r).emb.length (coreGraph (D.G (s₀ + r)) (ep r).cs.lsf) : ℝ) ≤
        coreE82Len E.L (E.P_fn M) ∧
      (ep r).emb.econg (coreGraph (D.G (s₀ + r)) (ep r).cs.lsf) (ep r).S_cur
          (fun _ => 1) (fun _ => 1) ≤
        1 + coreE82Cong E.L (E.P_fn M) * (2 * (M : ℝ)) := by
    intro r hr
    have hsr : s₀ + r ≤ τ := by omega
    have hSt_r := hSt_base r hr
    have hStg_r := hInv.2.2.1 r hr
    have hSc_r := (hSc j (s₀ + r) hsr).2
    rw [← hep_post_all r hr] at hSc_r
    have hOBr : (ep r).origBucket =
        fun e => bucketOf (coreLen (initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j).lsf
          (safeLen (D.G 0) (D.ℓ 0)) e) :=
      hSt_r.origBucket.trans (hBaseT (s₀ + r) hsr).2.2.2.2.1
    have hSp_r := treeCoreState_isSparsifiedCoreGraph oracle E.C_lsst E.L E.hL (E.P_fn M)
      sparsify hHyps.hLSST k M N τ hk1 D hG₀ hV₀ hD hℓ hLen hM hN hThresh hHyps.hSp j hj
      (s₀ + r) hsr (ep r) hOBr hSt_r.cs hSt_r.ts hSt_r.activeComps
      hSc_r.2.1 hSc_r.2.2.1 hSc_r.2.2.2
      (fun C hC b =>
        let cb := hStg_r.2.2 C hC b
        ⟨cb.1, cb.2.1,
          cb.2.2.1.trans (origBucket_filter_safe_eq oracle E.C_lsst hk1 hG₀ hV₀ hℓ₀ hC hHyps.hLSST
            (hSt_r.ts.symm ▸ ((hBaseT (s₀ + r) hsr).2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.1)
            hOBr b),
          cb.2.2.2.1⟩)
      (fun C hC b =>
        let cb := hStg_r.2.2 C hC b
        ⟨cb.2.2.2.2.1, cb.2.2.2.2.2.2.1, cb.2.2.2.2.2.2.2.1,
          cb.2.2.2.2.2.2.2.2.1, cb.2.2.2.2.2.2.2.2.2.1, cb.2.2.2.2.2.2.2.2.2.2⟩)
    dsimp only at hSp_r
    exact ⟨hSp_r.1, hSp_r.2.1, hSp_r.2.2.1, hSp_r.2.2.2.1, hSp_r.2.2.2.2.2.1⟩
  have hS_eq : ∀ r ≤ t - s₀, (T.coreInstanceFrom k M N D restarts s₀ j).G r = (ep r).S_cur := by
    intro r hr
    dsimp only [SparseCoreRestartTool.coreInstanceFrom, T, post]
    rw [hep_post_all r hr]
    exact sRT_S_of_nonempty (hne (s₀ + r)) j
  have hL_eq : ∀ r ≤ t - s₀, T.lsfs (post (s₀ + r)) j = (ep r).cs.lsf := by
    intro r hr
    dsimp only [T, post]; rw [hep_post_all r hr]
    exact sRT_lsfs_of_nonempty (hne (s₀ + r)) j
  have hEmb_eq : ∀ r ≤ t - s₀, T.emb (post (s₀ + r)) j = (ep r).emb := by
    intro r hr
    dsimp only [T, post]; rw [hep_post_all r hr]
    exact sRT_emb_of_nonempty (hne (s₀ + r)) j
  refine ⟨_, treeCoreState_seq_weakHiddenStable oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify
    hHyps.hLSST k M N τ hk1 D hG₀ hV₀ hD hLen hN hThresh Ψ c w hWeak j hj s₀ (t - s₀) (by omega) ep
    (T.coreInstanceFrom k M N D restarts s₀ j)
    (T.coreCFrom k M N D restarts c s₀ j) (T.coreWFrom k M N D restarts w s₀ j)
    hS_eq
    (fun r hr => by
      dsimp only [SparseCoreRestartTool.coreInstanceFrom, T]
      rw [show s₀ + (r + 1) = s₀ + r + 1 by omega]
      exact (hSt_step r hr).2)
    (fun r hr => by
      dsimp only [SparseCoreRestartTool.coreInstanceFrom]
      rw [hL_eq r hr])
    (fun r hr => by
      dsimp only [SparseCoreRestartTool.coreCFrom]
      rw [hL_eq r hr, hEmb_eq r hr])
    (fun r hr => by
      dsimp only [SparseCoreRestartTool.coreWFrom]
      rw [hL_eq r hr, hEmb_eq r hr])
    (fun r hr => (hSt_step r hr).1)
    (fun r hr => (hSt_base r hr).m₀.trans (hBaseT (s₀ + r) (by omega)).1)
    (fun r hr => (hSt_base r hr).cs)
    (fun r hr => (hSt_base r hr).ts)
    (fun r hr => (hSt_base r hr).activeComps)
    (fun r hr => (hSt_base r hr).origBucket)
    (fun r hr => (hSt_base r hr).activeBuckets)
    (fun r hr => by
      have hSc_r := (hSc j (s₀ + r) (by omega)).2
      rw [← hep_post_all r hr] at hSc_r
      rw [(hSt_base r hr).activeBuckets, (hBaseT (s₀ + r) (by omega)).2.2.2.2.2.1]
      exact hSc_r.2.2.1)
    hSpM
    (fun r hr C hC b =>
      let cb := (hInv.2.2.1 r hr).2.2 C hC b
      ⟨cb.2.1, cb.2.2.1, cb.2.2.2.2.1, cb.2.2.2.2.2.2.2.1⟩)
    (fun r hr C hC b =>
      let hs := (hInv.2.2.2.1 r hr).2.2.2.1 C hC b
      ⟨hs.1, hs.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩)⟩

/-- Items 1, 2, 4 and 5 of `SparseCoreRestartTool.IsSpecRestart` and the non-cost part of item 3,
for `sparseCoreRestartTool` (Lemma 5.17, pages 23–24, with restarts as used by Algorithm 1),
using the update budget at `(M, N)` directly (no `hThresh₀`). -/
theorem sparseCoreRestart_spec_noCost_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : SparseCoreCoreHypsAt E oracle sparsify k M D) :
    let T := sparseCoreRestartTool oracle E.C_lsst E.L sparsify
    let P := sparseCoreParams E
    let pre := fun t => (T.runAfterUpdate k M N D restarts t).1
    let U_S := fun t => (T.runAfterUpdate k M N D restarts t).2
    let post := fun t => T.runAfterRestarts k M N D restarts t
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
      (∀ b < k, b ≠ j' → T.S (T.restart st' j') b = T.S st' b ∧ T.emb (T.restart st' j') b = T.emb st' b) ∧
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
        WeakHiddenStable (T.coreInstanceFrom k M N D restarts s₀ j) (t - s₀) Ψ'
          (T.coreCFrom k M N D restarts c s₀ j) (T.coreWFrom k M N D restarts w s₀ j)) := by
  intro T P pre U_S post
  have hValP := sparseCoreParams_valid E
  have hk1 : 1 ≤ k := hk
  have hγr_nn : 0 ≤ P.γ_r M := by linarith [hValP.2.2.2.2.2.2.1 M]
  by_cases hV₀ : (D.G 0).V.Nonempty
  · exact ⟨sparseCoreRestart_spec_item1_noComp E oracle sparsify k τ M N D restarts Ψ c w hk hG₀ hD hLen hWeak hM hN hrest hThresh hHyps hV₀,
      sparseCoreRestart_spec_item2_noComp E oracle sparsify k τ M N D restarts Ψ c w hk hG₀ hD hLen hWeak hM hN hrest hThresh hHyps hV₀,
      sparseCoreRestart_spec_item3_noComp E oracle sparsify k τ M N D restarts,
      sparseCoreRestart_spec_item4_noComp E oracle sparsify k τ M N D restarts Ψ c w hk hG₀ hD hLen hWeak hM hN hrest hThresh hHyps hV₀,
      sparseCoreRestart_spec_item5_noComp E oracle sparsify k τ M N D restarts Ψ c w hk hG₀ hD hLen hWeak hM hN hrest hThresh hHyps hV₀⟩
  · -- Empty vertex set case: `(D.G 0).V = ∅`, all updates and restarts act trivially
    obtain ⟨hG_empty, _⟩ := empty_dyn_eq hG₀ hV₀ hD
    have hrunE := runAfterRestarts_empty_case oracle E.C_lsst E.L sparsify k M N D restarts hV₀
    have hL_eq : ∀ t j, T.lsfs (post t) j = emptyLSF := fun t j => by
      dsimp only [T, post]; exact sRT_lsfs_of_empty (hrunE t).2.1 j
    have hS_eq : ∀ t j, T.S (post t) j = emptyGraph := fun t j => by
      dsimp only [T, post]; exact sRT_S_of_empty (hrunE t).2.1 j
    have hEmb_eq : ∀ t j, T.emb (post t) j = fun _ => [] := fun t j => by
      dsimp only [T, post]; exact sRT_emb_of_empty (hrunE t).2.1 j
    have hUS_eq : ∀ t j, U_S t j = [] := fun t j => by
      dsimp only [U_S, T]; rw [(hrunE t).2.2]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
          rw [hlen0, Nat.cast_zero]
          linarith [hValP.2.2.1 M]
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
        positivity
    · intro t ht1 htτ j _
      have hS_pre : T.S (pre t) j = emptyGraph := by
        dsimp only [T, pre]; exact sRT_S_of_empty (hrunE t).1 j
      rw [hL_eq t j, hL_eq (t - 1) j, hS_eq (t - 1) j, hS_pre, hUS_eq t j]
      have hGtE := (hG_empty t htτ).2.2
      refine ⟨Finset.Subset.rfl, fun e he => by simp [hGtE] at he,
        fun e he => by simp [hGtE] at he, trivial, rfl⟩
    · intro r _ p j' _ st'
      have hst'_hem : st'.isNonempty = false := by
        dsimp only [st']
        rw [sRT_foldl_restart_empty oracle E.C_lsst E.L sparsify (pre r) (hrunE r).1 p]
        exact (hrunE r).1
      have hres_eq : T.restart st' j' = st' := by
        dsimp only [T]
        change (if st'.isNonempty then _ else st') = st'
        simp only [hst'_hem, Bool.false_eq_true, ↓reduceIte]
      exact ⟨fun _ _ => by rw [hres_eq], fun _ _ _ => by rw [hres_eq]; exact ⟨rfl, rfl⟩,
        by rw [hres_eq]⟩
    · intro s₀ t _ _ j _ _ _
      simp only [hUS_eq, List.length_nil, Finset.sum_const_zero, Nat.cast_zero, MGraph.batchEnc]
      exact ⟨mul_nonneg hγr_nn (Nat.cast_nonneg _), mul_nonneg hγr_nn (by positivity)⟩
    · intro s₀ t _ _ j _ _ _
      refine ⟨max Ψ 0, fun r _ => ?_⟩
      have hSE : ((T.coreInstanceFrom k M N D restarts s₀ j).G r).E = ∅ := by
        dsimp only [SparseCoreRestartTool.coreInstanceFrom]
        rw [hS_eq (s₀ + r) j]; rfl
      have hSV : ((T.coreInstanceFrom k M N D restarts s₀ j).G r).V = ∅ := by
        dsimp only [SparseCoreRestartTool.coreInstanceFrom]
        rw [hS_eq (s₀ + r) j]; rfl
      exact ⟨fun v hv => by simp [hSV] at hv,
        ⟨fun v hv => by simp [hSV] at hv, fun e he => by simp [hSE] at he⟩,
        fun e he => by simp [hSE] at he,
        fun e he => by simp [hSE] at he⟩

end MinCostFlow.Chain

end
