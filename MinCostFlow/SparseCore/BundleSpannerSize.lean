module

public import MinCostFlow.SparseCore.BundleSpannerMetricsAux
import MinCostFlow.SparseCore.SplitSpannerBase
import MinCostFlow.SparseCore.SparseCoreRunBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sparsity bound for the sparsified core on bundle graphs

Proves `bundleRunSeq_S_cur_card_le`, bounding `st.S_cur.E.card` at every stage `t ≤ τ` by
`bundleSizeFactor L P_b M B_bound * M / k` (paper Definition 5.7, item 3, page 19). The proof sums
initial bundle vertices over large components (`≤ 10 B M / k`) and activated small components
(`≤ 2 B M / k`), adds bundle-split growth (`≤ 224 B M / k`), and adds the `extraEdges`
(`≤ 114 M / k`) and `crossEdges` (`≤ M / k`) contributions.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

/-- Sparsity bound (clause 6 of `bundleRunSeq_isSparsifiedCoreGraph`): at every stage `t ≤ τ`,
`st.S_cur.E.card ≤ bundleSizeFactor L P_b M B_bound * M / k`. -/
lemma bundleRunSeq_S_cur_card_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    {k M N τ : ℕ} (hk : 1 ≤ k) {D : DynamicInstance}
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    {ord : ℕ → ℕ → List End} (hOrd : OrderedUpTo D τ 2 ord)
    (j : ℕ) {t : ℕ} (ht : t ≤ τ)
    (hActB_t : (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.activeBuckets =
      (bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1.activeBuckets)
    (hI_t : CompLSFInv C_lsst (D.ℓ 0) (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.cs)
    (hAct_sub : (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.activeComps ⊆
      components (D.G 0))
    (hS_E : (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.S_cur.E =
      ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.activeComps.biUnion fun C =>
        ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1.activeBuckets C).biUnion fun b =>
          ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.dyn (C, b)).H.E) ∪
        ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.activeComps.biUnion fun C =>
          (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.extraEdges C) ∪
        (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.cs.crossEdges)
    (hSmallAct : ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.activeComps \
      largeComps k (D.G 0)).card ≤ 2 * (Finset.Icc 1 t).sum (fun s => (D.U s).length))
    (hBun_eq : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.bun (C, b)).edges =
        ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1.bun (C, b)).edges \
          (Finset.Icc 1 t).biUnion (fun s => batchDeletes (D.U s)))
    (hGn_bnds : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.dyn (C, b)).G.n ≤ bundleNMax M ∧
      ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.dyn (C, b)).G.n ≤
        ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1.bun (C, b)).vertices.card +
          2 * (((bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.cs.compSt C).R \
            ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1.cs.compSt C).R).card)
    (hDynHm : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (((bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.dyn (C, b)).H.m : ℝ) ≤
        ((L : ℝ) + 1) * P_b.K_s *
          (((bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.dyn (C, b)).G.n : ℝ) *
          P_b.γ_ℓ *
          (1 + Real.log
            ((((bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.dyn (C, b)).G.n : ℝ) +
              (((bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1.bun (C, b)).graph.m : ℝ) +
              2)) ^ P_b.p_s)
    {B_bound : ℕ}
    (hB_bound : ∀ C ∈ components (D.G 0),
      ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1.activeBuckets C).card ≤ B_bound) :
    ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.S_cur.E.card : ℝ) ≤
      bundleSizeFactor L P_b M B_bound * (M : ℝ) / (k : ℝ) := by
  let G₀ := D.G 0
  let run := bundleRunSeq oracle C_lsst L sparsify k M N D ord j
  let st₀ := (run 0).1
  let cs₀ := st₀.cs
  let actB := st₀.activeBuckets
  let st := (run t).1
  have hI₀ : CompLSFInv C_lsst (D.ℓ 0) cs₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hcs_t : st.cs = compLSFBatch cs₀ (dynBatches D t).flatten :=
    bundleRunSeq_cs_eq oracle C_lsst L sparsify k M N D ord j t
  have hcs_G₀ : st.cs.G₀ = G₀ := by rw [hcs_t, compLSFBatch_G₀]; rfl
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hq_sub : Finset.Icc 1 t ⊆ Finset.Icc 1 τ := fun s hs => by
    simp only [Finset.mem_Icc] at hs ⊢; exact ⟨hs.1, le_trans hs.2 ht⟩
  have hq_t_le_div : (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      (M : ℝ) / (k : ℝ) :=
    le_trans (by exact_mod_cast Finset.sum_le_sum_of_subset hq_sub)
      (q_sum_le_M_div_k hk hN_pos hThresh)
  have hR_diff := compLSF_R_diff_le oracle hLSST hk hG₀ hV₀ hℓ₀ hD hN hThresh j t ht
  have hR_le : ((st.cs.RF.R \ cs₀.RF.R).card : ℝ) ≤ 112 * (M : ℝ) / (k : ℝ) := by
    rw [hcs_t]; exact hR_diff.2.2
  have hCross_le : (st.cs.crossEdges.card : ℝ) ≤ (M : ℝ) / (k : ℝ) :=
    le_trans (by exact_mod_cast bundleRunSeq_crossEdges_le oracle C_lsst L sparsify k M N D ord j t)
      hq_t_le_div
  have hba := applyBatch_dynBatches hD t ht
  have hBV_flat : cs₀.G.BatchIsValid (dynBatches D t).flatten :=
    (batchIsValid_flatten (D.G 0) (dynBatches D t)).mpr hba.2
  have hsp_flat := compLSFBatch_step_props (dynBatches D t).flatten hI₀ hBV_flat
  have hsum_R_eq : ((components G₀).sum fun C => ((st.cs.compSt C).R \ (cs₀.compSt C).R).card) =
      (st.cs.RF.R \ cs₀.RF.R).card := by
    have hR_m : ∀ C ∈ components cs₀.G₀, (cs₀.compSt C).R ⊆ (st.cs.compSt C).R :=
      fun C hC => by rw [hcs_t]; exact (hsp_flat.2.2.1 C hC).2.2.2.1
    exact compLSF_sum_R_sdiff_eq hI₀ hI_t hcs_G₀ hR_m
  have hEx_card : ((st.activeComps.biUnion fun C => st.extraEdges C).card : ℝ) ≤
      114 * (M : ℝ) / (k : ℝ) := by
    have hEx_sub : st.activeComps.biUnion (fun C => st.extraEdges C) ⊆
        st.cs.insertedGlobal ∪
          (components G₀).biUnion (fun C => (cs₀.compSt C).RF.F.E \ (st.cs.compSt C).RF.F.E) := by
      refine Finset.biUnion_subset.mpr fun C hCA e he => ?_
      have hC := hAct_sub hCA
      have hsubC := bundleRunSeq_extraEdges_sub oracle C_lsst L sparsify hLSST hk hG₀ hV₀ hℓ₀
        hOrd j hActB_t hI_t hBun_eq hC he
      rcases Finset.mem_union.mp hsubC with h1 | h2
      · exact Finset.mem_union_left _ h1
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨C, hC, h2⟩)
    have hIns_card : st.cs.insertedGlobal.card ≤ ∑ s ∈ Finset.Icc 1 t, (D.U s).length := by
      rw [hcs_t]
      have h1 := compLSFBatch_insertedGlobal_card_le cs₀ rfl (dynBatches D t).flatten
      have hfl : (dynBatches D t).flatten.length = ∑ s ∈ Finset.Icc 1 t, (D.U s).length := by
        rw [← totalUpdates_dynBatches D t, MinCostFlow.LSF.totalUpdates, List.length_flatten]
      rwa [hfl] at h1
    have hF_sum : ((components G₀).biUnion fun C =>
          (cs₀.compSt C).RF.F.E \ (st.cs.compSt C).RF.F.E).card ≤
        (st.cs.RF.R \ cs₀.RF.R).card := by
      calc ((components G₀).biUnion fun C => (cs₀.compSt C).RF.F.E \ (st.cs.compSt C).RF.F.E).card
          ≤ (components G₀).sum fun C => ((cs₀.compSt C).RF.F.E \ (st.cs.compSt C).RF.F.E).card :=
              Finset.card_biUnion_le
        _ ≤ (components G₀).sum fun C => ((st.cs.compSt C).R \ (cs₀.compSt C).R).card := by
            refine Finset.sum_le_sum fun C hC => ?_
            have hCsp := hsp_flat.2.2.1 C hC
            rw [hcs_t, hCsp.1]
            exact lsf_forest_diff_batch_le_R_diff _ (hI₀.hCompLSF C hC).1 hCsp.2.2.1
        _ = (st.cs.RF.R \ cs₀.RF.R).card := hsum_R_eq
    have hnat_ex : (st.activeComps.biUnion fun C => st.extraEdges C).card ≤
        (∑ s ∈ Finset.Icc 1 t, (D.U s).length) + (st.cs.RF.R \ cs₀.RF.R).card :=
      le_trans (Finset.card_le_card hEx_sub)
        (le_trans (Finset.card_union_le _ _) (Nat.add_le_add hIns_card hF_sum))
    have hR_ex : ((st.activeComps.biUnion fun C => st.extraEdges C).card : ℝ) ≤
        (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) +
          ((st.cs.RF.R \ cs₀.RF.R).card : ℝ) := by exact_mod_cast hnat_ex
    have hM_nn : (0 : ℝ) ≤ (M : ℝ) / (k : ℝ) := by positivity
    have h112 : 112 * (M : ℝ) / (k : ℝ) = 112 * ((M : ℝ) / (k : ℝ)) := by ring
    have h114 : 114 * (M : ℝ) / (k : ℝ) = 114 * ((M : ℝ) / (k : ℝ)) := by ring
    linarith
  set C0 := ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M
  have hC0_nn : 0 ≤ C0 := by
    have := P_b.hK_s; have := P_b.hγ_ℓ; have := (bundleLambdaS_pos P_b M).le; positivity
  have hDyn_Hm : ∀ C ∈ components G₀, ∀ b : ℤ,
      ((st.dyn (C, b)).H.m : ℝ) ≤ C0 * ((st.dyn (C, b)).G.n : ℝ) := by
    intro C hC b
    have hHb_m : (st₀.bun (C, b)).graph.m ≤ M :=
      initBundleTree_bun_m_le (k := k) (N := N) oracle C_lsst L sparsify hM (D.ℓ 0) (ord 0) j C b
    have hlam_le := bundleLambdaS_of_le P_b (hGn_bnds C hC b).1 hHb_m
    have hpre_nn : 0 ≤ ((L : ℝ) + 1) * P_b.K_s * ((st.dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ := by
      have := P_b.hK_s; have := P_b.hγ_ℓ; positivity
    calc ((st.dyn (C, b)).H.m : ℝ)
        ≤ ((L : ℝ) + 1) * P_b.K_s * ((st.dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ *
            (1 + Real.log (((st.dyn (C, b)).G.n : ℝ) + ((st₀.bun (C, b)).graph.m : ℝ) + 2)) ^ P_b.p_s :=
            hDynHm C hC b
      _ ≤ ((L : ℝ) + 1) * P_b.K_s * ((st.dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ * bundleLambdaS P_b M :=
            mul_le_mul_of_nonneg_left hlam_le hpre_nn
      _ = C0 * ((st.dyn (C, b)).G.n : ℝ) := by dsimp only [C0]; ring
  have hGn_sum : (st.activeComps.sum fun C => (actB C).sum fun b => ((st.dyn (C, b)).G.n : ℝ)) ≤
      1000 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by
    have hsplit_act : st.activeComps ⊆ largeComps k G₀ ∪ (st.activeComps \ largeComps k G₀) := by
      intro C hC
      by_cases hLc : C ∈ largeComps k G₀
      · exact Finset.mem_union_left _ hLc
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hC, hLc⟩)
    have hInit_L : ((largeComps k G₀).sum fun C =>
          (actB C).sum fun b => ((st₀.bun (C, b)).vertices.card : ℝ)) ≤
        10 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by
      calc (largeComps k G₀).sum (fun C => (actB C).sum fun b => ((st₀.bun (C, b)).vertices.card : ℝ))
          ≤ (largeComps k G₀).sum (fun C => 10 * (B_bound : ℝ) * ((compGraph G₀ C).m : ℝ) / (k : ℝ)) :=
            Finset.sum_le_sum fun C hC =>
              initBundleTree_large_bun_sum_le oracle L sparsify hLSST k M N hk hG₀ hV₀ hℓ₀ (ord 0) j hC
                (hB_bound C (largeComps_sub hC))
        _ = 10 * (B_bound : ℝ) *
              (((largeComps k G₀).sum fun C => (compGraph G₀ C).m : ℕ) : ℝ) / (k : ℝ) := by
            rw [← Finset.sum_div, ← Finset.mul_sum]; push_cast; ring
        _ ≤ 10 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by
            have hm_sub : (largeComps k G₀).sum (fun C => (compGraph G₀ C).m) ≤ M :=
              le_trans (le_trans (Finset.sum_le_sum_of_subset largeComps_sub)
                (components_sum_m G₀ hG₀).le) hM
            have hm_r : (((largeComps k G₀).sum fun C => (compGraph G₀ C).m : ℕ) : ℝ) ≤ (M : ℝ) := by
              exact_mod_cast hm_sub
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hm_r (by positivity)) hk_pos.le
    have hInit_S : ((st.activeComps \ largeComps k G₀).sum fun C =>
          (actB C).sum fun b => ((st₀.bun (C, b)).vertices.card : ℝ)) ≤
        2 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by
      calc (st.activeComps \ largeComps k G₀).sum
            (fun C => (actB C).sum fun b => ((st₀.bun (C, b)).vertices.card : ℝ))
          ≤ (st.activeComps \ largeComps k G₀).sum (fun _ => (B_bound : ℝ)) := by
            refine Finset.sum_le_sum fun C hC => ?_
            rcases Finset.mem_sdiff.mp hC with ⟨hCA, hNL⟩
            have hC_mem := hAct_sub hCA
            calc (actB C).sum (fun b => ((st₀.bun (C, b)).vertices.card : ℝ))
                ≤ (actB C).sum (fun _ => (1 : ℝ)) :=
                  Finset.sum_le_sum fun b _ => by
                    exact_mod_cast initBundleTree_small_bun_card_le_one oracle L sparsify hLSST k M N hk
                      hG₀ hV₀ hℓ₀ (ord 0) j hC_mem hNL b
              _ = ((actB C).card : ℝ) := by simp
              _ ≤ (B_bound : ℝ) := by exact_mod_cast hB_bound C hC_mem
        _ = ((st.activeComps \ largeComps k G₀).card : ℝ) * (B_bound : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ)) * (B_bound : ℝ) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hSmallAct) (Nat.cast_nonneg _)
        _ ≤ (2 * ((M : ℝ) / (k : ℝ))) * (B_bound : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        _ = 2 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by ring
    have hGrowth_sum : (st.activeComps.sum fun C =>
          (actB C).sum fun _ => 2 * (((st.cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ)) ≤
        224 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by
      calc (st.activeComps.sum fun C =>
            (actB C).sum fun _ => 2 * (((st.cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ))
          = st.activeComps.sum fun C =>
              ((actB C).card : ℝ) * (2 * (((st.cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ)) := by
            refine Finset.sum_congr rfl fun C _ => by simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ st.activeComps.sum fun C =>
              (B_bound : ℝ) * (2 * (((st.cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ)) :=
            Finset.sum_le_sum fun C hCA =>
              mul_le_mul_of_nonneg_right (by exact_mod_cast hB_bound C (hAct_sub hCA)) (by positivity)
        _ ≤ (components G₀).sum fun C =>
              (B_bound : ℝ) * (2 * (((st.cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hAct_sub (fun _ _ _ => by positivity)
        _ = (2 * (B_bound : ℝ)) * (((components G₀).sum fun C =>
              ((st.cs.compSt C).R \ (cs₀.compSt C).R).card : ℕ) : ℝ) := by
            rw [Nat.cast_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun _ _ => by ring
        _ = (2 * (B_bound : ℝ)) * ((st.cs.RF.R \ cs₀.RF.R).card : ℝ) := by rw [hsum_R_eq]
        _ ≤ (2 * (B_bound : ℝ)) * (112 * (M : ℝ) / (k : ℝ)) :=
            mul_le_mul_of_nonneg_left hR_le (by positivity)
        _ = 224 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by ring
    have hEach : (st.activeComps.sum fun C => (actB C).sum fun b => ((st.dyn (C, b)).G.n : ℝ)) ≤
        (st.activeComps.sum fun C => (actB C).sum fun b => ((st₀.bun (C, b)).vertices.card : ℝ)) +
        (st.activeComps.sum fun C => (actB C).sum fun _ =>
          2 * (((st.cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun C hCA => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun b _ => ?_
      have hg : ((st.dyn (C, b)).G.n : ℝ) ≤
          (((st₀.bun (C, b)).vertices.card + 2 * ((st.cs.compSt C).R \ (cs₀.compSt C).R).card : ℕ) : ℝ) := by
        exact_mod_cast (hGn_bnds C (hAct_sub hCA) b).2
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hg
    have hInit_tot : (st.activeComps.sum fun C =>
          (actB C).sum fun b => ((st₀.bun (C, b)).vertices.card : ℝ)) ≤
        12 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by
      calc (st.activeComps.sum fun C => (actB C).sum fun b => ((st₀.bun (C, b)).vertices.card : ℝ))
          ≤ (largeComps k G₀ ∪ (st.activeComps \ largeComps k G₀)).sum
              (fun C => (actB C).sum fun b => ((st₀.bun (C, b)).vertices.card : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsplit_act (fun _ _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
        _ = ((largeComps k G₀).sum fun C => (actB C).sum fun b => ((st₀.bun (C, b)).vertices.card : ℝ)) +
            ((st.activeComps \ largeComps k G₀).sum fun C => (actB C).sum fun b => ((st₀.bun (C, b)).vertices.card : ℝ)) :=
            Finset.sum_union (Finset.disjoint_left.mpr fun _ h1 h2 => (Finset.mem_sdiff.mp h2).2 h1)
        _ ≤ 10 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) + 2 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) :=
            add_le_add hInit_L hInit_S
        _ = 12 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by ring
    have hBM_nn : 0 ≤ (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by positivity
    calc (st.activeComps.sum fun C => (actB C).sum fun b => ((st.dyn (C, b)).G.n : ℝ))
        ≤ 12 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) + 224 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by
          linarith
      _ = 236 * ((B_bound : ℝ) * (M : ℝ) / (k : ℝ)) := by ring
      _ ≤ 1000 * ((B_bound : ℝ) * (M : ℝ) / (k : ℝ)) := by linarith
      _ = 1000 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by ring
  have hDyn_sum : ((st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E).card : ℝ) ≤
      (C0 * (B_bound : ℝ) * 1000) * (M : ℝ) / (k : ℝ) := by
    have hcard_le : (st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E).card ≤
        st.activeComps.sum fun C => (actB C).sum fun b => (st.dyn (C, b)).H.m :=
      le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
    have hR1 : ((st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E).card : ℝ) ≤
        st.activeComps.sum fun C => (actB C).sum fun b => ((st.dyn (C, b)).H.m : ℝ) := by
      exact_mod_cast hcard_le
    have hR2 : (st.activeComps.sum fun C => (actB C).sum fun b => ((st.dyn (C, b)).H.m : ℝ)) ≤
        C0 * (st.activeComps.sum fun C => (actB C).sum fun b => ((st.dyn (C, b)).G.n : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun C hCA => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun b _ => hDyn_Hm C (hAct_sub hCA) b
    calc ((st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E).card : ℝ)
        ≤ C0 * (st.activeComps.sum fun C => (actB C).sum fun b => ((st.dyn (C, b)).G.n : ℝ)) :=
          le_trans hR1 hR2
      _ ≤ C0 * (1000 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hGn_sum hC0_nn
      _ = (C0 * (B_bound : ℝ) * 1000) * (M : ℝ) / (k : ℝ) := by ring
  have hS_union : st.S_cur.E.card ≤
      (st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E).card +
      (st.activeComps.biUnion fun C => st.extraEdges C).card +
      st.cs.crossEdges.card := by
    rw [hS_E]
    exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have h1 : (st.S_cur.E.card : ℝ) ≤
      ((st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E).card : ℝ) +
      ((st.activeComps.biUnion fun C => st.extraEdges C).card : ℝ) +
      (st.cs.crossEdges.card : ℝ) := by exact_mod_cast hS_union
  unfold bundleSizeFactor
  have heq : (C0 * (B_bound : ℝ) * 1000) * (M : ℝ) / (k : ℝ) +
        114 * (M : ℝ) / (k : ℝ) + (M : ℝ) / (k : ℝ) =
      (((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M * (B_bound : ℝ) * 1000 + 115) *
        (M : ℝ) / (k : ℝ) := by dsimp only [C0]; ring
  linarith

end

end MinCostFlow.SparseCore
