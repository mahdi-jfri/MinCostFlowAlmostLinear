module

public import MinCostFlow.Chain.BundleRestartEpoch
import MinCostFlow.SparseCore.BundleSpannerMetricsAux
import MinCostFlow.SparseCore.BundleConstantsLemmas
import MinCostFlow.SparseCore.SplitSpannerBase
import MinCostFlow.SparseCore.SparseCoreRunBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Post-Restart Sparsity Bound for `sparseCoreBundleRestartTool`

Proves `epochBundleSeq_S_cur_card_le`: at every stage `δ ≤ t - s₀` of a non-restarted epoch
`[s₀, t]` of `sparseCoreBundleRestartTool`, `(st δ).S_cur.E.card ≤ bundleSizeFactor L P_b M B_bound * M / k`.

At a restart `s₀`, `restartBundleTree` re-bundles only the surviving initially-admitted edges of
each bucket on the current tours, giving `k * |V(bun_{s₀})| ≤ k * |R_C(s₀)| + 2 * |E(bun_{s₀})|`
and `|V(bun_{s₀ + δ})| ≤ |V(bun_{s₀})| + 2 * |R_C(s₀ + δ) \ R_C(s₀)|`. Combining
`|R_C(s₀) \ R_C(0)| + 2 * |R_C(s₀ + δ) \ R_C(s₀)| ≤ 2 * |R_C(s₀ + δ) \ R_C(0)|` keeps the total
bundle vertex count within `236 * B_bound * M / k ≤ 1000 * B_bound * M / k`, matching the exact
`bundleSizeFactor` of the unrestarted run.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.LSF
open MinCostFlow.Bundle

/-! ## 1. Helper bounds along an epoch -/

private lemma bundleRunSeq_smallAct_le
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord) (j : ℕ)
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    ∀ s ≤ τ,
      ((bundleRunSeqWith lsfInit L sparsify k M N D ord j s).1.activeComps \
        largeComps k (D.G 0)).card ≤ 2 * (Finset.Icc 1 s).sum (fun i => (D.U i).length) := by
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit
  intro s
  induction s with
  | zero =>
    intro _
    change (largeComps k (D.G 0) \ largeComps k (D.G 0)).card ≤ 0
    simp
  | succ m ih =>
    intro hm_le
    have hBm := hBun m (Nat.le_of_succ_le hm_le)
    have hbp_m := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts
      hV₀ j m).1
    have hI_m : CompLSFInv C_lsst (D.ℓ 0)
        (bundleRunSeqWith lsfInit L sparsify k M N D ord j m).1.cs :=
      hbp_m.cs ▸ hBm.2.2.2.2.2.2.2.1
    have hG_m : (bundleRunSeqWith lsfInit L sparsify k M N D ord j m).1.cs.G = D.G m := by
      rw [← hbp_m.cs, hBm.2.2.2.2.2.2.2.2.1]
    have hDt := hD (m + 1) (Nat.succ_pos m) hm_le
    simp only [Nat.add_sub_cancel] at hDt
    have htc : (touchedCompsBatch
        (bundleRunSeqWith lsfInit L sparsify k M N D ord j m).1.cs (D.U (m + 1))).card ≤
        2 * (D.U (m + 1)).length :=
      touchedCompsBatch_card_le hI_m (hG_m.symm ▸ hDt.1)
    have hsub : (bundleRunSeqWith lsfInit L sparsify k M N D ord j (m + 1)).1.activeComps \
          largeComps k (D.G 0) ⊆
        ((bundleRunSeqWith lsfInit L sparsify k M N D ord j m).1.activeComps \
          largeComps k (D.G 0)) ∪
          touchedCompsBatch (bundleRunSeqWith lsfInit L sparsify k M N D ord j m).1.cs
            (D.U (m + 1)) := by
      intro C hC
      rcases Finset.mem_sdiff.mp hC with ⟨hCA, hNL⟩
      change C ∈ (bundleRunSeqWith lsfInit L sparsify k M N D ord j m).1.activeComps ∪
        (touchedCompsBatch _ _ \ _) at hCA
      rcases Finset.mem_union.mp hCA with h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h1, hNL⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp h2).1
    have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext x; simp [Finset.mem_Icc]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    have hc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have ih' := ih (Nat.le_of_succ_le hm_le)
    omega

private lemma epochBundleSeq_R_sub_δ
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (s₀ t j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r)
    {δ : ℕ} (hδ : δ ≤ t - s₀) {C : Finset ℕ} (hC : C ∈ components (D.G 0)) :
    let st := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j
    ((st 0).cs.compSt C).R ⊆ ((st δ).cs.compSt C).R := by
  intro st
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit
  have hSt_base := (epochBundleSeq_steps lsfInit C_lsst L sparsify
    k M N D ord restarts hV₀ s₀ t j hst hNoRest).1
  have hbp_0 := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts
    hV₀ j s₀).1
  have hBs0 := hBun s₀ (le_trans hst htτ)
  have h0_cs : (st 0).cs =
      (((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterUpdate k M N D ord
        restarts s₀).1.trees j).cs := by
    have h0 := (hSt_base 0 (Nat.zero_le _)).cs
    rw [Nat.add_zero] at h0
    exact h0.trans hbp_0.cs.symm
  have hI_0 : CompLSFInv C_lsst (D.ℓ 0) (st 0).cs := h0_cs ▸ hBs0.2.2.2.2.2.2.2.1
  have hG_0 : (st 0).cs.G = D.G s₀ := h0_cs ▸ hBs0.2.2.2.2.2.2.2.2.1
  have hG0_0 : (st 0).cs.G₀ = D.G 0 := by
    rw [h0_cs, hBs0.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
  have hcs_δ : (st δ).cs = compLSFBatch (st 0).cs
      ((List.range δ).map fun i => D.U (s₀ + i + 1)).flatten := by
    have hgen : ∀ d ≤ t - s₀,
        (st d).cs = compLSFBatch (st 0).cs
          ((List.range d).map fun i => D.U (s₀ + i + 1)).flatten := by
      intro d
      induction d with
      | zero => intro _; simp [compLSFBatch]
      | succ m ih =>
        intro hm
        have h1 : (st (m + 1)).cs =
            (bundleRunSeqWith lsfInit L sparsify k M N D ord j (s₀ + m + 1)).1.cs := by
          have := (hSt_base (m + 1) hm).cs
          simpa [Nat.add_assoc] using this
        have h2 : (st m).cs =
            (bundleRunSeqWith lsfInit L sparsify k M N D ord j (s₀ + m)).1.cs :=
          (hSt_base m (Nat.le_of_succ_le hm)).cs
        have hcs_m1 : (st (m + 1)).cs = compLSFBatch (st m).cs (D.U (s₀ + m + 1)) := by
          rw [h1, h2]
          exact bundleRunSeqWith_cs lsfInit L sparsify k M N D ord j (s₀ + m)
        rw [hcs_m1, ih (Nat.le_of_succ_le hm), List.range_succ, List.map_append,
          List.flatten_append, compLSFBatch_append, List.map_singleton, List.flatten_singleton]
    exact hgen δ hδ
  have hBV_ep : (st 0).cs.G.BatchIsValid ((List.range δ).map fun i => D.U (s₀ + i + 1)).flatten := by
    rw [hG_0]
    have hgen : ∀ d, s₀ + d ≤ τ →
        (D.G s₀).BatchIsValid ((List.range d).map fun i => D.U (s₀ + i + 1)).flatten ∧
        (D.G s₀).applyBatch ((List.range d).map fun i => D.U (s₀ + i + 1)).flatten =
          D.G (s₀ + d) := by
      intro d
      induction d with
      | zero => intro _; simp [MGraph.BatchIsValid, MGraph.applyBatch]
      | succ m ih =>
        intro hm
        obtain ⟨hbv, happ⟩ := ih (by omega)
        have hDt := hD (s₀ + m + 1) (Nat.succ_pos _) hm
        simp only [Nat.add_sub_cancel] at hDt
        rw [List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
          List.flatten_singleton, DynSpanner.batchIsValid_append, DynSpanner.applyBatch_append, happ]
        exact ⟨⟨hbv, hDt.1⟩, by simpa [Nat.add_assoc] using hDt.2.symm⟩
    exact (hgen δ (by omega)).1
  rw [hcs_δ]
  exact ((compLSFBatch_step_props _ hI_0 hBV_ep).2.2.1 C (hG0_0 ▸ hC)).2.2.2.1

private lemma epochBundleSeq_extra_le
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (s₀ t j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀ : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r)
    {δ : ℕ} (hδ : δ ≤ t - s₀) :
    let st := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j
    (((st δ).activeComps.biUnion fun C => (st δ).extraEdges C).card : ℝ) ≤
      114 * (M : ℝ) / (k : ℝ) := by
  classical
  intro st
  let G₀ := D.G 0
  let st₀ := initBundleTreeWith lsfInit L sparsify k M N G₀ (D.ℓ 0) (ord 0) j
  let cs₀ := st₀.cs
  let r := s₀ + δ
  have hr_le : r ≤ τ := by omega
  have hI₀ : CompLSFInv C_lsst (D.ℓ 0) cs₀ := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
  have hInv := epochBundleSeq_inv lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd hThresh s₀ t j hInit hst htτ hs₀ hNoRest
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit
  have hSt_base := (epochBundleSeq_steps lsfInit C_lsst L sparsify
    k M N D ord restarts hV₀ s₀ t j hst hNoRest).1
  have hbp_r := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts
    hV₀ j r).1
  have hBr := hBun r hr_le
  have hcs_r : (st δ).cs = compLSFBatch cs₀ (dynBatches D r).flatten := by
    rw [(hSt_base δ hδ).cs, ← hbp_r.cs]; exact hBr.2.2.2.2.2.2.1
  have hI_r : CompLSFInv C_lsst (D.ℓ 0) (st δ).cs := by
    rw [(hSt_base δ hδ).cs, ← hbp_r.cs]; exact hBr.2.2.2.2.2.2.2.1
  have hcs_G₀ : (st δ).cs.G₀ = G₀ := by rw [hcs_r, compLSFBatch_G₀]; rfl
  have hAct_sub : (st δ).activeComps ⊆ components G₀ := (hInv.2.2.1 δ hδ).2.1
  have hActB_r : (st δ).activeBuckets = st₀.activeBuckets := by
    rw [(hSt_base δ hδ).activeBuckets, ← hbp_r.activeBuckets]; exact hBr.2.2.2.2.1
  have hBun_eq : ∀ C ∈ components G₀, ∀ b : ℤ,
      ((st δ).bun (C, b)).edges =
        (st₀.bun (C, b)).edges \ (Finset.Icc 1 r).biUnion (fun s => batchDeletes (D.U s)) := by
    intro C hC b
    dsimp only [st, epochBundleSeq]
    split_ifs with hcond
    · have hBt := hBun t htτ
      have hrt : r = t := hcond.1
      rw [hrt]
      exact ((hBt.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.1
    · rw [((hBr.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.1]
      exact ((hBr.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.1
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hq_sub : Finset.Icc 1 r ⊆ Finset.Icc 1 τ := fun s hs => by
    simp only [Finset.mem_Icc] at hs ⊢; exact ⟨hs.1, le_trans hs.2 hr_le⟩
  have hq_r_le_div : (((Finset.Icc 1 r).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      (M : ℝ) / (k : ℝ) :=
    le_trans (by exact_mod_cast Finset.sum_le_sum_of_subset hq_sub)
      (q_sum_le_M_div_k hk hN_pos hThresh)
  have hR_le : (((st δ).cs.RF.R \ cs₀.RF.R).card : ℝ) ≤ 112 * (M : ℝ) / (k : ℝ) := by
    rw [hcs_r]
    exact (compLSF_R_diff_le_with lsfInit hk hG₀ hV₀ hℓ₀ hD hN hThresh hInit r hr_le).2.2
  have hba := applyBatch_dynBatches hD r hr_le
  have hBV_flat : cs₀.G.BatchIsValid (dynBatches D r).flatten :=
    (batchIsValid_flatten (D.G 0) (dynBatches D r)).mpr hba.2
  have hsp_flat := compLSFBatch_step_props (dynBatches D r).flatten hI₀ hBV_flat
  have hsum_R_eq : ((components G₀).sum fun C => (((st δ).cs.compSt C).R \ (cs₀.compSt C).R).card) =
      ((st δ).cs.RF.R \ cs₀.RF.R).card := by
    have hR_m : ∀ C ∈ components cs₀.G₀, (cs₀.compSt C).R ⊆ ((st δ).cs.compSt C).R :=
      fun C hC => by rw [hcs_r]; exact (hsp_flat.2.2.1 C hC).2.2.2.1
    exact compLSF_sum_R_sdiff_eq hI₀ hI_r hcs_G₀ hR_m
  have hEx_sub : (st δ).activeComps.biUnion (fun C => (st δ).extraEdges C) ⊆
      (st δ).cs.insertedGlobal ∪
        (components G₀).biUnion (fun C => (cs₀.compSt C).RF.F.E \ ((st δ).cs.compSt C).RF.F.E) := by
    refine Finset.biUnion_subset.mpr fun C hCA e he => ?_
    have hC := hAct_sub hCA
    have hCompG : ∀ C' ∈ components G₀, (cs₀.compSt C').G = compGraph G₀ C' :=
      fun C' hC' => (initCompLSFWith_compSt_basic hInit hG₀ hℓ₀ hk hC').2.1
    by_cases hins : e ∈ (st δ).cs.insertedGlobal
    · exact Finset.mem_union_left _ hins
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨C, hC, ?_⟩)
      have he1 := Finset.mem_sdiff.mp he
      have he2 := Finset.mem_sdiff.mp he1.1
      have heC : e ∈ ((st δ).cs.compSt C).G.E := he2.1
      have hnF : e ∉ ((st δ).cs.compSt C).RF.F.E := he2.2
      have hniC : e ∉ ((st δ).cs.compSt C).insertedEdges := fun hm =>
        hins (hI_r.hCompIns_sub C (hcs_G₀ ▸ hC) hm)
      have heC₀ : e ∈ (cs₀.compSt C).G.E := by
        have hs := ((hI_r.hCompLSF C (hcs_G₀ ▸ hC)).1.hsurv_edge e heC hniC).1
        have hG₀C : ((st δ).cs.compSt C).G₀ = (cs₀.compSt C).G := by
          rw [(hI_r.hCompLSF C (hcs_G₀ ▸ hC)).2.1, hcs_G₀, hCompG C hC]
        rwa [hG₀C] at hs
      by_cases hF₀ : e ∈ (cs₀.compSt C).RF.F.E
      · exact Finset.mem_sdiff.mpr ⟨hF₀, hnF⟩
      · exfalso
        have hmem := comp_sdiff_mem_bucketCoreEdges hI₀ rfl hCompG st₀.origBucket hC
          (Finset.mem_sdiff.mpr ⟨heC₀, hF₀⟩)
        set b := st₀.origBucket e
        have hb_act : b ∈ (st δ).activeBuckets C := by rw [hActB_r]; exact hmem.1
        obtain ⟨ρ_all, hρ_ord, _⟩ := hOrd
        have he_bun0 : e ∈ (st₀.bun (C, b)).edges := by
          have hed : (st₀.bun (C, b)).edges =
              bucketCoreEdges (coreGraph (D.G 0) cs₀.lsf) st₀.origBucket C b :=
            initBundleFor_edges hI₀ (hρ_ord 0 (Nat.zero_le τ)) _ k
          rw [hed]; exact hmem.2
        have he_Dr : e ∈ ((D.G 0).applyBatch (dynBatches D r).flatten).E := by
          have h1 : e ∈ (st δ).cs.G.E := hI_r.hCE_sub C (hcs_G₀ ▸ hC) heC
          rw [hcs_r, compLSFBatch_G] at h1; exact h1
        have hni_flat : ∀ u ∈ (dynBatches D r).flatten, ¬ u.Inserts e := by
          rw [hcs_r, compLSFBatch_insertedGlobal] at hins
          exact (applyBatch_not_inserted_of_not_foldl (dynBatches D r).flatten (D.G 0) ∅ e he_Dr hins).2.2
        have hnd_flat : ∀ u ∈ (dynBatches D r).flatten, u ≠ .delete e :=
          not_delete_of_mem_applyBatch_of_not_inserts he_Dr hni_flat
        have hnd_union : e ∉ (Finset.Icc 1 r).biUnion (fun s => batchDeletes (D.U s)) := by
          intro hm
          rw [Finset.mem_biUnion] at hm
          rcases hm with ⟨s, hs, hdel⟩
          rw [mem_batchDeletes_iff] at hdel
          rcases hdel with ⟨u, hu, rfl⟩
          have hs' := Finset.mem_Icc.mp hs
          exact hnd_flat (.delete e) (mem_dynBatches_flatten_of_Icc D hs'.1 hs'.2 hu) rfl
        have he_bun : e ∈ ((st δ).bun (C, b)).edges := by
          rw [hBun_eq C hC b]; exact Finset.mem_sdiff.mpr ⟨he_bun0, hnd_union⟩
        exact he1.2 (Finset.mem_biUnion.mpr ⟨b, hb_act, he_bun⟩)
  have hIns_card : (st δ).cs.insertedGlobal.card ≤ ∑ s ∈ Finset.Icc 1 r, (D.U s).length := by
    rw [hcs_r]
    have h1 := compLSFBatch_insertedGlobal_card_le cs₀ rfl (dynBatches D r).flatten
    have hfl : (dynBatches D r).flatten.length = ∑ s ∈ Finset.Icc 1 r, (D.U s).length := by
      rw [← totalUpdates_dynBatches D r, MinCostFlow.LSF.totalUpdates, List.length_flatten]
    rwa [hfl] at h1
  have hF_sum : ((components G₀).biUnion fun C =>
        (cs₀.compSt C).RF.F.E \ ((st δ).cs.compSt C).RF.F.E).card ≤
      ((st δ).cs.RF.R \ cs₀.RF.R).card := by
    calc ((components G₀).biUnion fun C =>
            (cs₀.compSt C).RF.F.E \ ((st δ).cs.compSt C).RF.F.E).card
        ≤ (components G₀).sum fun C =>
            ((cs₀.compSt C).RF.F.E \ ((st δ).cs.compSt C).RF.F.E).card := Finset.card_biUnion_le
      _ ≤ (components G₀).sum fun C =>
            (((st δ).cs.compSt C).R \ (cs₀.compSt C).R).card := by
          refine Finset.sum_le_sum fun C hC => ?_
          have hCsp := hsp_flat.2.2.1 C hC
          rw [hcs_r, hCsp.1]
          exact lsf_forest_diff_batch_le_R_diff _ (hI₀.hCompLSF C hC).1 hCsp.2.2.1
      _ = ((st δ).cs.RF.R \ cs₀.RF.R).card := hsum_R_eq
  have hnat_ex : ((st δ).activeComps.biUnion fun C => (st δ).extraEdges C).card ≤
      (∑ s ∈ Finset.Icc 1 r, (D.U s).length) + ((st δ).cs.RF.R \ cs₀.RF.R).card :=
    le_trans (Finset.card_le_card hEx_sub)
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add hIns_card hF_sum))
  have hR_ex : (((st δ).activeComps.biUnion fun C => (st δ).extraEdges C).card : ℝ) ≤
      (((Finset.Icc 1 r).sum fun s => (D.U s).length : ℕ) : ℝ) +
        (((st δ).cs.RF.R \ cs₀.RF.R).card : ℝ) := by exact_mod_cast hnat_ex
  have hM_nn : (0 : ℝ) ≤ (M : ℝ) / (k : ℝ) := by positivity
  have h112 : 112 * (M : ℝ) / (k : ℝ) = 112 * ((M : ℝ) / (k : ℝ)) := by ring
  have h114 : 114 * (M : ℝ) / (k : ℝ) = 114 * ((M : ℝ) / (k : ℝ)) := by ring
  linarith

private lemma epochBundleSeq_Gn_sum_le
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (s₀ t j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀ : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r)
    {δ : ℕ} (hδ : δ ≤ t - s₀) {B_bound : ℕ}
    (hB_bound : ∀ C ∈ components (D.G 0),
      ((initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).card ≤
        B_bound) :
    let st := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j
    let actB := (initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets
    ((st δ).activeComps.sum fun C => (actB C).sum fun b => (((st δ).dyn (C, b)).G.n : ℝ)) ≤
      1000 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by
  classical
  intro st actB
  let G₀ := D.G 0
  let st₀ := initBundleTreeWith lsfInit L sparsify k M N G₀ (D.ℓ 0) (ord 0) j
  let cs₀ := st₀.cs
  let r := s₀ + δ
  have hr_le : r ≤ τ := by omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hI₀ : CompLSFInv C_lsst (D.ℓ 0) cs₀ := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
  have hInv := epochBundleSeq_inv lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd hThresh s₀ t j hInit hst htτ hs₀ hNoRest
  have hDyn := epochBundleSeq_dyn_spec lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit hst htτ hs₀ hNoRest
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit
  have hSt_base := (epochBundleSeq_steps lsfInit C_lsst L sparsify
    k M N D ord restarts hV₀ s₀ t j hst hNoRest).1
  have hbp_r := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts
    hV₀ j r).1
  have hbp_0 := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts
    hV₀ j s₀).1
  have hBr := hBun r hr_le
  have hBs0 := hBun s₀ (le_trans hst htτ)
  have hcs_r : (st δ).cs = compLSFBatch cs₀ (dynBatches D r).flatten := by
    rw [(hSt_base δ hδ).cs, ← hbp_r.cs]; exact hBr.2.2.2.2.2.2.1
  have hI_r : CompLSFInv C_lsst (D.ℓ 0) (st δ).cs := by
    rw [(hSt_base δ hδ).cs, ← hbp_r.cs]; exact hBr.2.2.2.2.2.2.2.1
  have hcs_G₀ : (st δ).cs.G₀ = G₀ := by rw [hcs_r, compLSFBatch_G₀]; rfl
  have hAct_sub : (st δ).activeComps ⊆ components G₀ := (hInv.2.2.1 δ hδ).2.1
  by_cases hB0 : B_bound = 0
  · subst hB0
    have hzero : ∀ C ∈ (st δ).activeComps, actB C = ∅ := fun C hCA =>
      Finset.card_eq_zero.mp (Nat.le_zero.mp (hB_bound C (hAct_sub hCA)))
    have hlhs : ((st δ).activeComps.sum fun C => (actB C).sum fun b =>
        (((st δ).dyn (C, b)).G.n : ℝ)) = 0 :=
      Finset.sum_eq_zero fun C hCA => by rw [hzero C hCA, Finset.sum_empty]
    rw [hlhs]; simp
  · have hB1 : (1 : ℝ) ≤ (B_bound : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hB0
    have hGn_cb : ∀ C ∈ components G₀, ∀ b : ℤ,
        (((st δ).dyn (C, b)).G.n : ℝ) ≤
          ((cs₀.compSt C).R.card : ℝ) +
            2 * ((((st δ).cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ) +
            2 * (((st 0).bun (C, b)).graph.m : ℝ) / (k : ℝ) := by
      intro C hC b
      have hdC := hDyn C hC b
      have hstep := hdC.2.2.2.2.2.2.2.2.2.1 δ hδ
      have hgn_eq : ((st δ).dyn (C, b)).G.n = ((st δ).bun (C, b)).vertices.card := by
        rw [graphEq_n hstep.2.1]; rfl
      have hv0 : ((st 0).bun (C, b)).vertices.card * k ≤
          ((st 0).cs.compSt C).R.card * k + 2 * ((st 0).bun (C, b)).edges.card := by
        have := hdC.2.2.2.2.1; linarith
      have hv0R : (((st 0).bun (C, b)).vertices.card : ℝ) ≤
          (((st 0).cs.compSt C).R.card : ℝ) +
            2 * (((st 0).bun (C, b)).graph.m : ℝ) / (k : ℝ) := by
        have h1 : (((st 0).bun (C, b)).vertices.card : ℝ) * (k : ℝ) ≤
            (((st 0).cs.compSt C).R.card : ℝ) * (k : ℝ) +
              2 * (((st 0).bun (C, b)).edges.card : ℝ) := by exact_mod_cast hv0
        have hdiv := div_le_div_of_nonneg_right h1 hk_pos.le
        have hL : (((st 0).bun (C, b)).vertices.card : ℝ) * (k : ℝ) / (k : ℝ) =
            (((st 0).bun (C, b)).vertices.card : ℝ) := mul_div_cancel_right₀ _ hk_pos.ne'
        have hR : ((((st 0).cs.compSt C).R.card : ℝ) * (k : ℝ) +
              2 * (((st 0).bun (C, b)).edges.card : ℝ)) / (k : ℝ) =
            (((st 0).cs.compSt C).R.card : ℝ) +
              2 * (((st 0).bun (C, b)).edges.card : ℝ) / (k : ℝ) := by
          rw [add_div, mul_div_cancel_right₀ _ hk_pos.ne']
        rw [hL, hR] at hdiv
        exact hdiv
      have hR0_sub : (cs₀.compSt C).R ⊆ ((st 0).cs.compSt C).R := by
        have h0 := (hSt_base 0 (Nat.zero_le _)).cs
        rw [Nat.add_zero] at h0
        rw [h0, ← hbp_0.cs]
        exact (hBs0.2.2.2.2.2.2.2.2.2.2.2 C hC).1.hR_sub
      have hR_sub_δ : ((st 0).cs.compSt C).R ⊆ ((st δ).cs.compSt C).R :=
        epochBundleSeq_R_sub_δ lsfInit C_lsst L sparsify k M N τ hk D ord restarts
          hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit hst htτ hNoRest hδ hC
      have hR_comb : ((st 0).cs.compSt C).R.card +
            2 * (((st δ).cs.compSt C).R \ ((st 0).cs.compSt C).R).card ≤
          (cs₀.compSt C).R.card + 2 * (((st δ).cs.compSt C).R \ (cs₀.compSt C).R).card := by
        have c1 := Finset.card_le_card hR0_sub
        have c2 := Finset.card_le_card hR_sub_δ
        rw [Finset.card_sdiff_of_subset hR_sub_δ, Finset.card_sdiff_of_subset (hR0_sub.trans hR_sub_δ)]
        omega
      have hvδ : (((st δ).dyn (C, b)).G.n : ℝ) ≤
          (((st 0).bun (C, b)).vertices.card : ℝ) +
            2 * ((((st δ).cs.compSt C).R \ ((st 0).cs.compSt C).R).card : ℝ) := by
        rw [hgn_eq]; exact_mod_cast hstep.2.2.2.2
      have hR_combR : (((st 0).cs.compSt C).R.card : ℝ) +
            2 * ((((st δ).cs.compSt C).R \ ((st 0).cs.compSt C).R).card : ℝ) ≤
          ((cs₀.compSt C).R.card : ℝ) +
            2 * ((((st δ).cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ) := by
        exact_mod_cast hR_comb
      linarith
    have hq_sub : Finset.Icc 1 r ⊆ Finset.Icc 1 τ := fun s hs => by
      simp only [Finset.mem_Icc] at hs ⊢; exact ⟨hs.1, le_trans hs.2 hr_le⟩
    have hq_r_le_div : (((Finset.Icc 1 r).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        (M : ℝ) / (k : ℝ) :=
      le_trans (by exact_mod_cast Finset.sum_le_sum_of_subset hq_sub)
        (q_sum_le_M_div_k hk hN_pos hThresh)
    have hSmallAct : ((st δ).activeComps \ largeComps k G₀).card ≤
        2 * (Finset.Icc 1 r).sum (fun s => (D.U s).length) := by
      rw [(hSt_base δ hδ).activeComps]
      exact bundleRunSeq_smallAct_le lsfInit C_lsst L sparsify k M N τ hk D ord restarts
        hG₀ hV₀ hℓ₀ hD hOrd j hInit r hr_le
    have hR_le : (((st δ).cs.RF.R \ cs₀.RF.R).card : ℝ) ≤ 112 * (M : ℝ) / (k : ℝ) := by
      rw [hcs_r]
      exact (compLSF_R_diff_le_with lsfInit hk hG₀ hV₀ hℓ₀ hD hN hThresh hInit r hr_le).2.2
    have hsum_R_eq : ((components G₀).sum fun C => (((st δ).cs.compSt C).R \ (cs₀.compSt C).R).card) =
        ((st δ).cs.RF.R \ cs₀.RF.R).card := by
      have hba := applyBatch_dynBatches hD r hr_le
      have hBV_flat : cs₀.G.BatchIsValid (dynBatches D r).flatten :=
        (batchIsValid_flatten (D.G 0) (dynBatches D r)).mpr hba.2
      have hsp_flat := compLSFBatch_step_props (dynBatches D r).flatten hI₀ hBV_flat
      have hR_m : ∀ C ∈ components cs₀.G₀, (cs₀.compSt C).R ⊆ ((st δ).cs.compSt C).R :=
        fun C hC => by rw [hcs_r]; exact (hsp_flat.2.2.1 C hC).2.2.2.1
      exact compLSF_sum_R_sdiff_eq hI₀ hI_r hcs_G₀ hR_m
    have hsplit_act : (st δ).activeComps ⊆ largeComps k G₀ ∪ ((st δ).activeComps \ largeComps k G₀) := by
      intro C hC
      by_cases hLc : C ∈ largeComps k G₀
      · exact Finset.mem_union_left _ hLc
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hC, hLc⟩)
    have hℓs : ∀ e ∈ G₀.E, 0 < safeLen G₀ (D.ℓ 0) e := fun e he => by
      rw [safeLen_eq_of_mem (D.ℓ 0) he]; exact hℓ₀ e he
    have hR0_L : ((largeComps k G₀).sum fun C => (actB C).sum fun _ => ((cs₀.compSt C).R.card : ℝ)) ≤
        8 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by
      calc ((largeComps k G₀).sum fun C => (actB C).sum fun _ => ((cs₀.compSt C).R.card : ℝ))
          = (largeComps k G₀).sum fun C => ((actB C).card : ℝ) * ((cs₀.compSt C).R.card : ℝ) :=
            Finset.sum_congr rfl fun C _ => by simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (largeComps k G₀).sum fun C =>
              (B_bound : ℝ) * (8 * ((compGraph G₀ C).m : ℝ) / (k : ℝ)) := by
            refine Finset.sum_le_sum fun C hC => ?_
            have hR_C : ((cs₀.compSt C).R.card : ℝ) ≤ 8 * ((compGraph G₀ C).m : ℝ) / (k : ℝ) :=
              initLSF_large_R_card_le_with hInit hG₀ hℓs hk hC
            exact mul_le_mul (by exact_mod_cast hB_bound C (largeComps_sub hC)) hR_C
              (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        _ = 8 * (B_bound : ℝ) *
              (((largeComps k G₀).sum fun C => (compGraph G₀ C).m : ℕ) : ℝ) / (k : ℝ) := by
            rw [Nat.cast_sum, Finset.mul_sum, Finset.sum_div]
            refine Finset.sum_congr rfl fun C _ => by ring
        _ ≤ 8 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by
            have hm_sub : (largeComps k G₀).sum (fun C => (compGraph G₀ C).m) ≤ M :=
              le_trans (le_trans (Finset.sum_le_sum_of_subset largeComps_sub)
                (components_sum_m G₀ hG₀).le) hM
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by exact_mod_cast hm_sub) (by positivity)) hk_pos.le
    have hR0_S : (((st δ).activeComps \ largeComps k G₀).sum fun C =>
          (actB C).sum fun _ => ((cs₀.compSt C).R.card : ℝ)) ≤
        2 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by
      calc (((st δ).activeComps \ largeComps k G₀).sum fun C =>
            (actB C).sum fun _ => ((cs₀.compSt C).R.card : ℝ))
          ≤ ((st δ).activeComps \ largeComps k G₀).sum fun _ => (B_bound : ℝ) := by
            refine Finset.sum_le_sum fun C hC => ?_
            rcases Finset.mem_sdiff.mp hC with ⟨hCA, hNL⟩
            have hC_mem := hAct_sub hCA
            have hlt : 4 * (compGraph G₀ C).m < k := by
              by_contra hge
              push Not at hge
              have hm1 : 1 ≤ (compGraph G₀ C).m := by
                have : 0 < 4 * (compGraph G₀ C).m := lt_of_lt_of_le hk hge; omega
              exact hNL (Finset.mem_filter.mpr ⟨hC_mem, hm1, hge⟩)
            have hR1 : (cs₀.compSt C).R.card = 1 :=
              (initLSF_small_props_with hInit hG₀ hℓs hk hC_mem hlt).1
            simp only [hR1, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one]
            exact_mod_cast hB_bound C hC_mem
        _ = (((st δ).activeComps \ largeComps k G₀).card : ℝ) * (B_bound : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * (((Finset.Icc 1 r).sum fun s => (D.U s).length : ℕ) : ℝ)) * (B_bound : ℝ) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hSmallAct) (Nat.cast_nonneg _)
        _ ≤ (2 * ((M : ℝ) / (k : ℝ))) * (B_bound : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        _ = 2 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by ring
    have hR0_tot : ((st δ).activeComps.sum fun C => (actB C).sum fun _ => ((cs₀.compSt C).R.card : ℝ)) ≤
        10 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by
      calc ((st δ).activeComps.sum fun C => (actB C).sum fun _ => ((cs₀.compSt C).R.card : ℝ))
          ≤ (largeComps k G₀ ∪ ((st δ).activeComps \ largeComps k G₀)).sum
              (fun C => (actB C).sum fun _ => ((cs₀.compSt C).R.card : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsplit_act
              (fun _ _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
        _ = ((largeComps k G₀).sum fun C => (actB C).sum fun _ => ((cs₀.compSt C).R.card : ℝ)) +
            (((st δ).activeComps \ largeComps k G₀).sum fun C =>
              (actB C).sum fun _ => ((cs₀.compSt C).R.card : ℝ)) :=
            Finset.sum_union (Finset.disjoint_left.mpr fun _ h1 h2 => (Finset.mem_sdiff.mp h2).2 h1)
        _ ≤ 8 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) + 2 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) :=
            add_le_add hR0_L hR0_S
        _ = 10 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by ring
    have hGrowth_sum : ((st δ).activeComps.sum fun C => (actB C).sum fun _ =>
          2 * ((((st δ).cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ)) ≤
        224 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by
      have hterm_nn : ∀ C ∈ components G₀, C ∉ (st δ).activeComps →
          0 ≤ (B_bound : ℝ) * (2 * ((((st δ).cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ)) :=
        fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      calc ((st δ).activeComps.sum fun C => (actB C).sum fun _ =>
            2 * ((((st δ).cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ))
          = (st δ).activeComps.sum fun C =>
              ((actB C).card : ℝ) * (2 * ((((st δ).cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ)) :=
            Finset.sum_congr rfl fun C _ => by simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (st δ).activeComps.sum fun C =>
              (B_bound : ℝ) * (2 * ((((st δ).cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ)) :=
            Finset.sum_le_sum fun C hCA =>
              mul_le_mul_of_nonneg_right (by exact_mod_cast hB_bound C (hAct_sub hCA))
                (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        _ ≤ (components G₀).sum fun C =>
              (B_bound : ℝ) * (2 * ((((st δ).cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hAct_sub hterm_nn
        _ = (2 * (B_bound : ℝ)) * (((components G₀).sum fun C =>
              (((st δ).cs.compSt C).R \ (cs₀.compSt C).R).card : ℕ) : ℝ) := by
            rw [Nat.cast_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun _ _ => by ring
        _ = (2 * (B_bound : ℝ)) * (((st δ).cs.RF.R \ cs₀.RF.R).card : ℝ) := by rw [hsum_R_eq]
        _ ≤ (2 * (B_bound : ℝ)) * (112 * (M : ℝ) / (k : ℝ)) :=
            mul_le_mul_of_nonneg_left hR_le (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        _ = 224 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by ring
    have hEdge_sum : ((st δ).activeComps.sum fun C => (actB C).sum fun b =>
          2 * (((st 0).bun (C, b)).graph.m : ℝ) / (k : ℝ)) ≤
        2 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by
      have hm_le : ((components G₀).sum fun C => (actB C).sum fun b =>
          ((st 0).bun (C, b)).graph.m) ≤ M := le_trans hInv.2.1 hM
      calc ((st δ).activeComps.sum fun C => (actB C).sum fun b =>
            2 * (((st 0).bun (C, b)).graph.m : ℝ) / (k : ℝ))
          ≤ (components G₀).sum fun C => (actB C).sum fun b =>
              2 * (((st 0).bun (C, b)).graph.m : ℝ) / (k : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hAct_sub fun _ _ _ =>
              Finset.sum_nonneg fun _ _ => div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hk_pos.le
        _ = 2 * ((((components G₀).sum fun C => (actB C).sum fun b =>
              ((st 0).bun (C, b)).graph.m : ℕ) : ℝ)) / (k : ℝ) := by
            simp only [Nat.cast_sum, Finset.mul_sum, Finset.sum_div]
        _ ≤ 2 * (M : ℝ) / (k : ℝ) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by exact_mod_cast hm_le) (by norm_num)) hk_pos.le
        _ ≤ 2 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by
            have hM_nn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
            exact div_le_div_of_nonneg_right (by nlinarith) hk_pos.le
    have hEach : ((st δ).activeComps.sum fun C => (actB C).sum fun b =>
          (((st δ).dyn (C, b)).G.n : ℝ)) ≤
        ((st δ).activeComps.sum fun C => (actB C).sum fun _ => ((cs₀.compSt C).R.card : ℝ)) +
        ((st δ).activeComps.sum fun C => (actB C).sum fun _ =>
          2 * ((((st δ).cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ)) +
        ((st δ).activeComps.sum fun C => (actB C).sum fun b =>
          2 * (((st 0).bun (C, b)).graph.m : ℝ) / (k : ℝ)) := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun C hCA => Finset.sum_le_sum fun b _ => hGn_cb C (hAct_sub hCA) b
    have hBM_nn : 0 ≤ (B_bound : ℝ) * (M : ℝ) / (k : ℝ) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hk_pos.le
    calc ((st δ).activeComps.sum fun C => (actB C).sum fun b => (((st δ).dyn (C, b)).G.n : ℝ))
        ≤ 10 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) + 224 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) +
            2 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by linarith
      _ = 236 * ((B_bound : ℝ) * (M : ℝ) / (k : ℝ)) := by ring
      _ ≤ 1000 * ((B_bound : ℝ) * (M : ℝ) / (k : ℝ)) := by linarith
      _ = 1000 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ) := by ring

/-! ## 2. Post-restart sparsity bound -/

/-- Sparsity bound at any stage `δ ≤ t - s₀` of an epoch `[s₀, t]` of `sparseCoreBundleRestartTool`:
`(st δ).S_cur.E.card ≤ bundleSizeFactor L P_b M B_bound * M / k`. -/
lemma epochBundleSeq_S_cur_card_le
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (s₀ t j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀ : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r)
    {δ : ℕ} (hδ : δ ≤ t - s₀) {B_bound : ℕ}
    (hB_bound : ∀ C ∈ components (D.G 0),
      ((initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).card ≤
        B_bound) :
    let st := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j
    ((st δ).S_cur.E.card : ℝ) ≤ bundleSizeFactor L P_b M B_bound * (M : ℝ) / (k : ℝ) := by
  classical
  intro st
  let G₀ := D.G 0
  let actB := (initBundleTreeWith lsfInit L sparsify k M N G₀ (D.ℓ 0) (ord 0) j).activeBuckets
  let r := s₀ + δ
  have hr_le : r ≤ τ := by omega
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hInv := epochBundleSeq_inv lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd hThresh s₀ t j hInit hst htτ hs₀ hNoRest
  have hSc := runOrdAfterRestarts_S_cur_inv lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd j hInit
  have hSt_base := (epochBundleSeq_steps lsfInit C_lsst L sparsify
    k M N D ord restarts hV₀ s₀ t j hst hNoRest).1
  have hAct_sub : (st δ).activeComps ⊆ components G₀ := (hInv.2.2.1 δ hδ).2.1
  have hS_E : (st δ).S_cur.E =
      ((st δ).activeComps.biUnion fun C => (actB C).biUnion fun b => ((st δ).dyn (C, b)).H.E) ∪
        ((st δ).activeComps.biUnion fun C => (st δ).extraEdges C) ∪
        (st δ).cs.crossEdges := by
    dsimp only [st, epochBundleSeq]
    split_ifs with hcond
    · exact (hSc t htτ).1.2.2.1
    · exact (hSc r hr_le).2.2.2.1
  have hCross_le : ((st δ).cs.crossEdges.card : ℝ) ≤ (M : ℝ) / (k : ℝ) := by
    have hq_sub : Finset.Icc 1 r ⊆ Finset.Icc 1 τ := fun s hs => by
      simp only [Finset.mem_Icc] at hs ⊢; exact ⟨hs.1, le_trans hs.2 hr_le⟩
    have hce : (st δ).cs.crossEdges.card ≤ ∑ s ∈ Finset.Icc 1 r, (D.U s).length := by
      rw [(hSt_base δ hδ).cs]
      exact bundleRunSeqWith_crossEdges_le lsfInit L sparsify k M N D ord j r
    exact le_trans (by exact_mod_cast le_trans hce (Finset.sum_le_sum_of_subset hq_sub))
      (q_sum_le_M_div_k hk hN_pos hThresh)
  have hEx_card := epochBundleSeq_extra_le lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd hThresh s₀ t j hInit hst htτ hs₀ hNoRest hδ
  have hGn_sum := epochBundleSeq_Gn_sum_le lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd hThresh s₀ t j hInit hst htτ hs₀ hNoRest
    hδ hB_bound
  set C0 := ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M
  have hC0_nn : 0 ≤ C0 := by
    have := P_b.hK_s; have := P_b.hγ_ℓ; have := (bundleLambdaS_pos P_b M).le; positivity
  have hDyn_sum : (((st δ).activeComps.biUnion fun C => (actB C).biUnion fun b =>
        ((st δ).dyn (C, b)).H.E).card : ℝ) ≤
      (C0 * (B_bound : ℝ) * 1000) * (M : ℝ) / (k : ℝ) := by
    have hcard_le : ((st δ).activeComps.biUnion fun C => (actB C).biUnion fun b =>
          ((st δ).dyn (C, b)).H.E).card ≤
        (st δ).activeComps.sum fun C => (actB C).sum fun b => ((st δ).dyn (C, b)).H.m :=
      le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
    have hR1 : (((st δ).activeComps.biUnion fun C => (actB C).biUnion fun b =>
          ((st δ).dyn (C, b)).H.E).card : ℝ) ≤
        (st δ).activeComps.sum fun C => (actB C).sum fun b => (((st δ).dyn (C, b)).H.m : ℝ) := by
      exact_mod_cast hcard_le
    have hR2 : ((st δ).activeComps.sum fun C => (actB C).sum fun b => (((st δ).dyn (C, b)).H.m : ℝ)) ≤
        C0 * ((st δ).activeComps.sum fun C => (actB C).sum fun b => (((st δ).dyn (C, b)).G.n : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun C hCA => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b _ => ?_
      have hHm := ((hInv.2.2.1 δ hδ).2.2 C (hAct_sub hCA) b).2.2.2.2.2.1
      exact hHm.trans_eq (by dsimp only [C0]; ring)
    calc (((st δ).activeComps.biUnion fun C => (actB C).biUnion fun b =>
            ((st δ).dyn (C, b)).H.E).card : ℝ)
        ≤ C0 * ((st δ).activeComps.sum fun C => (actB C).sum fun b => (((st δ).dyn (C, b)).G.n : ℝ)) :=
          le_trans hR1 hR2
      _ ≤ C0 * (1000 * (B_bound : ℝ) * (M : ℝ) / (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hGn_sum hC0_nn
      _ = (C0 * (B_bound : ℝ) * 1000) * (M : ℝ) / (k : ℝ) := by ring
  have hS_union : (st δ).S_cur.E.card ≤
      ((st δ).activeComps.biUnion fun C => (actB C).biUnion fun b => ((st δ).dyn (C, b)).H.E).card +
      ((st δ).activeComps.biUnion fun C => (st δ).extraEdges C).card +
      (st δ).cs.crossEdges.card := by
    rw [hS_E]
    exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have h1 : ((st δ).S_cur.E.card : ℝ) ≤
      (((st δ).activeComps.biUnion fun C => (actB C).biUnion fun b =>
          ((st δ).dyn (C, b)).H.E).card : ℝ) +
      (((st δ).activeComps.biUnion fun C => (st δ).extraEdges C).card : ℝ) +
      ((st δ).cs.crossEdges.card : ℝ) := by exact_mod_cast hS_union
  unfold bundleSizeFactor
  have heq : (C0 * (B_bound : ℝ) * 1000) * (M : ℝ) / (k : ℝ) +
        114 * (M : ℝ) / (k : ℝ) + (M : ℝ) / (k : ℝ) =
      (((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M * (B_bound : ℝ) * 1000 + 115) *
        (M : ℝ) / (k : ℝ) := by dsimp only [C0]; ring
  linarith

end MinCostFlow.Chain

end
