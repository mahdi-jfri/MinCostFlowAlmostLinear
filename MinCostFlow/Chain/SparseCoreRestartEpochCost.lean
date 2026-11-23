module

public import MinCostFlow.Chain.SparseCoreRestartTotal
import MinCostFlow.Chain.SparseCoreRestartEpoch
import MinCostFlow.SparseCore.SparseCoreCost
import MinCostFlow.SparseCore.SparseCoreEpochCost
import MinCostFlow.SparseCore.SparseCoreCostEnvNoComp
import MinCostFlow.SparseCore.SparseCoreRecourse
import MinCostFlow.SparseCore.SplitSpannerBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The work of the Theorem 8.2 structures in one epoch of a run with restarts

Bounds the dynamic-spanner work and batch sizes over one epoch `[s₀, t]` of branch `j` in a run
with restarts at `(M, N)` without `hThresh₀`.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner

lemma sum_Icc_succ_eq_sum_range (f : ℕ → ℝ) (a b : ℕ) :
    ∑ s ∈ Finset.Icc (a + 1) b, f s = ∑ r ∈ Finset.range (b - a), f (a + r + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by congr 1; omega) fun r _ => by congr 1; omega

/-- `epoch_dyn_cost_le_min` on one epoch `[s₀, t]` of branch `j` in the run with restarts at
`(M, N)` (without `hComp_bound` or `hThresh₀`). -/
lemma epoch_dyn_cost_restart_le_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : SparseCoreCoreHypsAt E oracle sparsify k M D)
    (s₀ t j : ℕ) (hj : j < k) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀ : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r) :
    let ep := epochTreeSeq oracle E.C_lsst E.L sparsify k M N D restarts s₀ t j
    let cs₀ := initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j
    let ts₀ := fun C => initTildeState (cs₀.compSt C)
    let actB := fun C => (ts₀ C).C.E.image (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))
    let n_eff := min N (M + 1)
    let Δ₀ := (D.G 0).maxDeg
    let dC := (components (D.G 0)).sup fun C => (ts₀ C).C.maxDeg
    let q_ep := ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + (t - s₀)), (D.U s).length
    let q_τ := ∑ s ∈ Finset.Icc 1 τ, (D.U s).length
    let Λ := coreLambda (E.P_fn M) M
    let uc_ep := 2 * coreUCRatio n_eff Δ₀ * (q_ep : ℝ)
    let ucBound := 2 * coreUCRatio n_eff Δ₀ * (q_τ : ℝ)
    (∑ r ∈ Finset.range (t - s₀), ((ep (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
      (((stepTreeCoreAux sparsify (ep r) (D.U (s₀ + r + 1))).stepOut (C, b)).cost : ℝ))) ≤
      90 * (E.L : ℝ) * coreNRoot E.L M * ((E.P_fn M).K_t + (E.P_fn M).K_s + 1) *
        coreE_L E.L (E.P_fn M) * ((dC : ℝ) + 1) * Λ *
        (20 * ((M : ℝ) + (E.B_fn M : ℝ) * uc_ep) * Real.log ((M : ℝ) + ucBound + 2)) := by
  intro ep cs₀ ts₀ actB n_eff Δ₀ dC q_ep q_τ Λ uc_ep ucBound
  have hk1 : 1 ≤ k := hk
  have hInv := epochTreeSeq_inv oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify hHyps.hLSST
    k M N τ hk1 D restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hThresh s₀ t j hj hst htτ hs₀ hNoRest
  have hDyn := epochTreeSeq_dyn_spec oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify hHyps.hLSST
    k M N τ hk1 D restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD s₀ t j hst htτ hs₀ hNoRest
  obtain ⟨hSt_base, _⟩ := epochTreeSeq_steps oracle E.C_lsst E.L sparsify
    k M N D restarts hV₀ s₀ t j hst hNoRest
  obtain ⟨hBase, _, _⟩ := treeRunSeq_tilde_core_inv oracle E.C_lsst E.L sparsify hHyps.hLSST
    k M N τ hk1 D hG₀ hV₀ hℓ₀ hD j
  dsimp only at hInv hDyn
  have hsΔ : s₀ + (t - s₀) ≤ τ := by omega
  have hm0 : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      ((ep 0).dyn (C, b)).G.m = (restartBucketGraph (ep 0) C b).m := by
    intro C hC b
    have hT_0 : TildeInv (cs₀.compSt C) ((ep 0).cs.compSt C) ((ep 0).ts C) := by
      rw [(hSt_base 0 (Nat.zero_le _)).cs, (hSt_base 0 (Nat.zero_le _)).ts, Nat.add_zero]
      exact (hBase s₀ (by omega)).2.2.2.2.2.2.2.2.2.2.2.2 C hC |>.2.1
    have he_Hb := (activeSubgraph_rawBucket_spec hT_0.hC_val (ep 0).origBucket b).2.2.1
    have he_dyn := ((hDyn C hC b).2.2.2.2.2.2.2.1 0 (Nat.zero_le _)).2.2.2.1
    change ((ep 0).dyn (C, b)).G.E.card = (restartBucketGraph (ep 0) C b).E.card
    rw [he_dyn]
    exact congrArg Finset.card he_Hb.symm
  exact epoch_dyn_cost_le_min oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify hHyps.hLSST
    k M N τ hk1 D hG₀ hV₀ hℓ₀ hD hM hN hThresh j (E.B_fn M) (hHyps.hB_bound j hj)
    s₀ (t - s₀) hsΔ ep (fun C b => restartBucketGraph (ep 0) C b)
    (fun C b => (List.range (t - s₀)).map fun r =>
      (stepTreeCoreAux sparsify (ep r) (D.U (s₀ + r + 1))).U_b (C, b))
    (le_trans hInv.2.1 hM)
    (fun C hC b => (hInv.1 C hC b).2.2.1)
    (fun C hC b => (hInv.1 C hC b).2.2.2.1)
    (fun r hr => (hInv.2.2.1 r hr).2.1)
    (fun r hr => (hSt_base r hr).cs)
    (fun r hr => (hSt_base r hr).ts)
    (fun C hC b => ((hInv.2.2.1 0 (Nat.zero_le _)).2.2 C hC b).1)
    hm0
    (fun r hr C hC b => by
      have hs := (hInv.2.2.2.1 r hr).2.2.2.1 C hC b
      have hd := (hDyn C hC b).2.2.2.2.2.2.2.2 r hr
      refine ⟨hd.2.1, ?_, hd.2.2⟩
      rw [← hs.2.1, hs.1, update_G_eq])
    (fun C hC b r hr => congrArg DynSpannerState.G
      ((hDyn C hC b).2.2.2.2.2.2.2.1 r hr).1)
    (fun C hC b r hr => ((hDyn C hC b).2.2.2.2.2.2.2.2 r hr).1)
    (fun C hC b => (hInv.2.2.2.2 C hC b).2.2)

/-- The batch sizes of branch `j` in one epoch, by `epoch_recourse_and_enc_min` (without
`hComp_bound` or `hThresh₀`). -/
lemma epoch_US_restart_le_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : SparseCoreCoreHypsAt E oracle sparsify k M D)
    (s₀ t j : ℕ) (hj : j < k) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀ : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r) :
    let T := sparseCoreRestartTool oracle E.C_lsst E.L sparsify
    ∑ s ∈ Finset.Icc (s₀ + 1) t, (((T.runAfterUpdate k M N D restarts s).2 j).length : ℝ) ≤
      coreRecoursePerQ E.L (E.P_fn M) M (min N (M + 1))
        (D.G 0).maxDeg (E.B_fn M) * ∑ s ∈ Finset.Icc (s₀ + 1) t, ((D.U s).length : ℝ) := by
  intro T
  have hk1 : 1 ≤ k := hk
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
      (Finset.Icc (s₀ + 1) t).sum (fun s => ((T.runAfterUpdate k M N D restarts s).2 j).length) =
        (Finset.Icc 1 (t - s₀)).sum
          (fun r => ((T.runAfterUpdate k M N D restarts (s₀ + r)).2 j).length) := by
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
  have hmono := coreRecoursePerQ_mono_n E.L (E.P_fn M) M
    (min_le_min hN (Nat.add_le_add_right hM 1)) (D.G 0).maxDeg (E.B_fn M)
  exact le_trans h1 (mul_le_mul_of_nonneg_right hmono (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _))

/-- The Theorem 8.2 work of branch `j` in one epoch, in the form used for the total cost at
`(M, N)` (without `hComp_bound` or `hThresh₀`). -/
lemma epoch_dyn_cost_restart_le_T_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : SparseCoreCoreHypsAt E oracle sparsify k M D)
    (s₀ t j : ℕ) (hj : j < k) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀ : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r) :
    let T := sparseCoreRestartTool oracle E.C_lsst E.L sparsify
    let post := fun s => T.runAfterRestarts k M N D restarts s
    let infoR := fun s => stepTreeCoreAux sparsify ((post s).trees j) (D.U (s + 1))
    let p_max := max E.p_s_hi E.p_t_hi
    let logMN := Real.log ((M : ℝ) + (N : ℝ) + 2)
    let T_b := ((M : ℝ) + 1) * (recBase E M * costMult E M) * logMN ^ (p_max + 1)
    ∑ s ∈ Finset.Icc (s₀ + 1) t,
        ((((infoR (s - 1)).state.activeComps.sum fun C =>
          (((post (s - 1)).trees j).activeBuckets C).sum fun b =>
            ((infoR (s - 1)).stepOut (C, b)).cost : ℕ) : ℝ)) ≤
      12600 * (7 : ℝ) ^ p_max * T_b +
        (25200 * (7 : ℝ) ^ p_max * ((recBase E M * costMult E M) * logMN ^ (p_max + 1))) *
          ∑ s ∈ Finset.Icc (s₀ + 1) t, ((D.U s).length : ℝ) := by
  intro T post infoR p_max logMN T_b
  have hk1 : 1 ≤ k := hk
  obtain ⟨hSt_base, hSt_step⟩ := epochTreeSeq_steps oracle E.C_lsst E.L sparsify
    k M N D restarts hV₀ s₀ t j hst hNoRest
  obtain ⟨hBase, _, _⟩ := treeRunSeq_tilde_core_inv oracle E.C_lsst E.L sparsify hHyps.hLSST
    k M N τ hk1 D hG₀ hV₀ hℓ₀ hD j
  set ep := epochTreeSeq oracle E.C_lsst E.L sparsify k M N D restarts s₀ t j
  have hDyn := epoch_dyn_cost_restart_le_noComp E oracle sparsify k M N τ D restarts hk hG₀ hV₀ hℓ₀
    hD hM hN hThresh hHyps s₀ t j hj hst htτ hs₀ hNoRest
  dsimp only at hDyn
  have hterm : ∀ r < t - s₀,
      (((infoR (s₀ + r)).state.activeComps.sum fun C =>
          (((post (s₀ + r)).trees j).activeBuckets C).sum fun b =>
            ((infoR (s₀ + r)).stepOut (C, b)).cost : ℕ) : ℝ) =
        ((ep (r + 1)).activeComps.sum fun C =>
          ((initTildeState ((initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j).compSt C)).C.E.image
            (fun e => bucketOf (coreLen (initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j).lsf
              (D.ℓ 0) e))).sum fun b =>
          (((stepTreeCoreAux sparsify (ep r) (D.U (s₀ + r + 1))).stepOut (C, b)).cost : ℝ)) := by
    intro r hr
    have hep : ep r = (post (s₀ + r)).trees j :=
      ((epochTreeSeq_eq_post oracle E.C_lsst E.L sparsify k M N D restarts s₀ t j hst).1 r hr)
    have hAB : (ep r).activeBuckets = _ :=
      (hSt_base r hr.le).activeBuckets.trans (hBase (s₀ + r) (by omega)).2.2.2.2.2.1
    have hstep : ep (r + 1) = (stepTreeCoreAux sparsify (ep r) (D.U (s₀ + r + 1))).state :=
      (hSt_step r hr).1
    have hinfo : infoR (s₀ + r) = stepTreeCoreAux sparsify (ep r) (D.U (s₀ + r + 1)) := by
      dsimp only [infoR]; rw [hep]
    rw [hinfo, ← hstep, ← hep, hAB]
    push_cast
    rfl
  have hsum_eq := sum_Icc_succ_eq_sum_range (fun s =>
    ((((infoR (s - 1)).state.activeComps.sum fun C =>
          (((post (s - 1)).trees j).activeBuckets C).sum fun b =>
            ((infoR (s - 1)).stepOut (C, b)).cost : ℕ) : ℝ))) s₀ t
  rw [hsum_eq]
  have hsum_eq2 : ∑ r ∈ Finset.range (t - s₀),
      ((((infoR (s₀ + r + 1 - 1)).state.activeComps.sum fun C =>
          (((post (s₀ + r + 1 - 1)).trees j).activeBuckets C).sum fun b =>
            ((infoR (s₀ + r + 1 - 1)).stepOut (C, b)).cost : ℕ) : ℝ)) =
      ∑ r ∈ Finset.range (t - s₀), ((ep (r + 1)).activeComps.sum fun C =>
          ((initTildeState ((initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j).compSt C)).C.E.image
            (fun e => bucketOf (coreLen (initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j).lsf
              (D.ℓ 0) e))).sum fun b =>
          (((stepTreeCoreAux sparsify (ep r) (D.U (s₀ + r + 1))).stepOut (C, b)).cost : ℝ)) :=
    Finset.sum_congr rfl fun r hr => by
      rw [show s₀ + r + 1 - 1 = s₀ + r by omega]
      exact hterm r (Finset.mem_range.mp hr)
  rw [hsum_eq2]
  refine le_trans hDyn ?_
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hqτ_le_M : (Finset.Icc 1 τ).sum (fun s => (D.U s).length) ≤ M :=
    (updateThreshold_le_div_k_at hk hN_pos hThresh τ le_rfl).2
  obtain ⟨_, hd5, _⟩ := cost_env_baseline_parts_noComp E M N (activeSubgraph (D.G 0)).n
    (D.G 0).maxDeg
    ((components (D.G 0)).sup fun C =>
      (initTildeState ((initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j).compSt C)).C.maxDeg)
    ((Finset.Icc 1 τ).sum fun s => (D.U s).length) hN_pos
    (le_trans (activeSubgraph_n_le_two_m hG₀) (Nat.mul_le_mul_left 2 hM))
    hqτ_le_M (le_trans (maxDeg_le_two_m (D.G 0)) (Nat.mul_le_mul_left 2 hM))
    (by exact_mod_cast hHyps.hDeg_bound.1)
    (by exact_mod_cast hHyps.hDeg_bound.2 j hj)
  have h5 := hd5 ((Finset.Icc (s₀ + 1) (s₀ + (t - s₀))).sum fun s => (D.U s).length)
  have hq_eq : (((Finset.Icc (s₀ + 1) (s₀ + (t - s₀))).sum fun s => (D.U s).length : ℕ) : ℝ) =
      ∑ s ∈ Finset.Icc (s₀ + 1) t, ((D.U s).length : ℝ) := by
    rw [show s₀ + (t - s₀) = t by omega, Nat.cast_sum]
  refine le_trans h5 (le_of_eq ?_)
  rw [hq_eq]
  ring

end MinCostFlow.Chain

end
