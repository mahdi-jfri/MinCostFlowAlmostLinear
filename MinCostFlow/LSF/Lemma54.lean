module

public import MinCostFlow.LSF.Lemma54Base
public import MinCostFlow.LSF.Lemma54Split
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dynamic Low-Stretch Forest (Lemma 5.4, Appendix A.1)

This file proves **Lemma 5.4** (`lemma_5_4`) and its snapshot corollary **`lemma_5_4_holds`**,
establishing the dynamic low-stretch forest guarantees (items 1–4, page 17 of the paper) over
arbitrary valid update batches (`BatchesIsValid`), including vertex splits via Appendix A.1 (page 48).
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Lifting to batches and sequences of batches -/

lemma applyLSFBatch_inv_with {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ (U : List Update) {S : LSFState}, LSFInvWith thresh K_σ ℓ₀ S → S.G.BatchIsValid U →
      let S' := applyLSFBatch S U
      LSFInvWith thresh K_σ ℓ₀ S' ∧
      S'.G = S.G.applyBatch U ∧
      S'.G₀ = S.G₀ ∧ S'.T₀ = S.T₀ ∧ S'.r₀ = S.r₀ ∧ S'.π = S.π ∧ S'.k = S.k ∧
      S'.W_init = S.W_init ∧
      S.R ⊆ S'.R ∧
      S'.RF.F.E ⊆ S.RF.F.E ∧
      (S'.R.card : ℝ) ≤ (S.R.card : ℝ) +
        56 * (U.length : ℝ) * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 2
  | [], S, I, _ => by
    refine ⟨I, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Finset.Subset.refl _, Finset.Subset.refl _, ?_⟩
    dsimp only [applyLSFBatch]
    simp
  | u :: U, S, I, ⟨hu, hU⟩ => by
    have h1 := applyLSFUpdate_inv_with I hu
    rcases h1 with ⟨I₁, hG₁, hG₀₁, hT₀₁, hr₀₁, hπ₁, hk₁, hW₁, hR₁, hF₁E, hRcard₁⟩
    have h2 := applyLSFBatch_inv_with U I₁ (hG₁ ▸ hU)
    rcases h2 with ⟨I₂, hG₂, hG₀₂, hT₀₂, hr₀₂, hπ₂, hk₂, hW₂, hR₂, hF₂E, hRcard₂⟩
    have hU_eq : applyLSFBatch S (u :: U) = applyLSFBatch (applyLSFUpdate S u) U := rfl
    have hGU_eq : S.G.applyBatch (u :: U) = (S.G.applyUpdate u).applyBatch U := rfl
    rw [hU_eq, hGU_eq]
    refine ⟨I₂, hG₂.trans (by rw [hG₁]), hG₀₂.trans hG₀₁, hT₀₂.trans hT₀₁, hr₀₂.trans hr₀₁,
      hπ₂.trans hπ₁, hk₂.trans hk₁, hW₂.trans hW₁, hR₁.trans hR₂, hF₂E.trans hF₁E, ?_⟩
    rw [hG₀₁] at hRcard₂
    have hlen : ((u :: U).length : ℝ) = (U.length : ℝ) + 1 := by simp
    rw [hlen]
    linarith [show 56 * ((U.length : ℝ) + 1) * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 2 =
      56 * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 2 +
        56 * (U.length : ℝ) * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 2 by ring]

lemma applyLSFBatch_inv {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ (U : List Update) {S : LSFState}, LSFInv C_lsst ℓ₀ S → S.G.BatchIsValid U →
      let S' := applyLSFBatch S U
      LSFInv C_lsst ℓ₀ S' ∧
      S'.G = S.G.applyBatch U ∧
      S'.G₀ = S.G₀ ∧ S'.T₀ = S.T₀ ∧ S'.r₀ = S.r₀ ∧ S'.π = S.π ∧ S'.k = S.k ∧
      S'.W_init = S.W_init ∧
      S.R ⊆ S'.R ∧
      S'.RF.F.E ⊆ S.RF.F.E ∧
      (S'.R.card : ℝ) ≤ (S.R.card : ℝ) +
        56 * (U.length : ℝ) * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 2 := by
  intro U S I hU
  have hres := applyLSFBatch_inv_with U I hU
  refine ⟨?_, hres.2⟩
  change LSFInvWith (wstrThresh C_lsst (applyLSFBatch S U).G₀.n (applyLSFBatch S U).k)
    (6272 * max 1 C_lsst) ℓ₀ (applyLSFBatch S U)
  rw [hres.2.2.1, hres.2.2.2.2.2.2.1]
  exact hres.1

lemma applyLSFBatches_inv_with {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ (Us : List (List Update)) {S : LSFState}, LSFInvWith thresh K_σ ℓ₀ S → BatchesIsValid S.G Us →
      let S' := applyLSFBatches S Us
      LSFInvWith thresh K_σ ℓ₀ S' ∧
      S'.G = Us.foldl MGraph.applyBatch S.G ∧
      S'.G₀ = S.G₀ ∧ S'.T₀ = S.T₀ ∧ S'.r₀ = S.r₀ ∧ S'.π = S.π ∧ S'.k = S.k ∧
      S'.W_init = S.W_init ∧
      S.R ⊆ S'.R ∧
      S'.RF.F.E ⊆ S.RF.F.E ∧
      (S'.R.card : ℝ) ≤ (S.R.card : ℝ) +
        56 * (totalUpdates Us : ℝ) * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 2
  | [], S, I, _ => by
    refine ⟨I, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Finset.Subset.refl _, Finset.Subset.refl _, ?_⟩
    dsimp only [applyLSFBatches]
    simp [totalUpdates]
  | U :: Us, S, I, ⟨hU, hUs⟩ => by
    have h1 := applyLSFBatch_inv_with U I hU
    rcases h1 with ⟨I₁, hG₁, hG₀₁, hT₀₁, hr₀₁, hπ₁, hk₁, hW₁, hR₁, hF₁E, hRcard₁⟩
    have h2 := applyLSFBatches_inv_with Us I₁ (hG₁ ▸ hUs)
    rcases h2 with ⟨I₂, hG₂, hG₀₂, hT₀₂, hr₀₂, hπ₂, hk₂, hW₂, hR₂, hF₂E, hRcard₂⟩
    have hUs_eq : applyLSFBatches S (U :: Us) = applyLSFBatches (applyLSFBatch S U) Us := rfl
    have hGUs_eq : (U :: Us).foldl MGraph.applyBatch S.G =
        Us.foldl MGraph.applyBatch (S.G.applyBatch U) := rfl
    rw [hUs_eq, hGUs_eq]
    refine ⟨I₂, hG₂.trans (by rw [hG₁]), hG₀₂.trans hG₀₁, hT₀₂.trans hT₀₁, hr₀₂.trans hr₀₁,
      hπ₂.trans hπ₁, hk₂.trans hk₁, hW₂.trans hW₁, hR₁.trans hR₂, hF₂E.trans hF₁E, ?_⟩
    rw [hG₀₁] at hRcard₂
    have htot : (totalUpdates (U :: Us) : ℝ) = (U.length : ℝ) + (totalUpdates Us : ℝ) := by
      unfold totalUpdates; simp
    rw [htot]
    linarith [show 56 * ((U.length : ℝ) + (totalUpdates Us : ℝ)) * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 2 =
      56 * (U.length : ℝ) * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 2 +
        56 * (totalUpdates Us : ℝ) * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 2 by ring]

lemma applyLSFBatches_inv {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ (Us : List (List Update)) {S : LSFState}, LSFInv C_lsst ℓ₀ S → BatchesIsValid S.G Us →
      let S' := applyLSFBatches S Us
      LSFInv C_lsst ℓ₀ S' ∧
      S'.G = Us.foldl MGraph.applyBatch S.G ∧
      S'.G₀ = S.G₀ ∧ S'.T₀ = S.T₀ ∧ S'.r₀ = S.r₀ ∧ S'.π = S.π ∧ S'.k = S.k ∧
      S'.W_init = S.W_init ∧
      S.R ⊆ S'.R ∧
      S'.RF.F.E ⊆ S.RF.F.E ∧
      (S'.R.card : ℝ) ≤ (S.R.card : ℝ) +
        56 * (totalUpdates Us : ℝ) * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 2 := by
  intro Us S I hUs
  have hres := applyLSFBatches_inv_with Us I hUs
  refine ⟨?_, hres.2⟩
  change LSFInvWith (wstrThresh C_lsst (applyLSFBatches S Us).G₀.n (applyLSFBatches S Us).k)
    (6272 * max 1 C_lsst) ℓ₀ (applyLSFBatches S Us)
  rw [hres.2.2.1, hres.2.2.2.2.2.2.1]
  exact hres.1

lemma LSFInvWith.vol_bound {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInvWith thresh K_σ ℓ₀ S) {W : Finset ℕ} (hW : W ∈ S.W_init) :
    (S.G.vol (W \ S.R) : ℝ) ≤ 2240 * S.k * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 2 := by
  have hw := I.hW_props W hW
  have hsub : W \ S.R ⊆ W \ S.R_orig := fun x hx =>
    Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
      fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ h)⟩
  have hdeg : ∀ x ∈ W \ S.R, S.G.deg x ≤ S.G₀.deg x := fun x hx =>
    I.hdeg_le x (hw.2.1 (Finset.mem_sdiff.mp hx).1) (Finset.mem_sdiff.mp hx).2
  have hvol_le : S.G.vol (W \ S.R) ≤ S.G₀.vol (W \ S.R_orig) := by
    unfold MGraph.vol
    exact (Finset.sum_le_sum hdeg).trans (Finset.sum_le_sum_of_subset hsub)
  exact (Nat.cast_le.mpr hvol_le).trans hw.2.2.2

/-! ## Lemma 5.4 and Corollary `lemma_5_4_holds` -/

open Classical in
/-- **Lemma 5.4** (Dynamic Low Stretch Forest, page 17, Appendix A.1 page 48):
Given a static LSST oracle with parameter `C_lsst`, there is a constant `K > 0` (`6272 * max 1 C_lsst`)
such that for every valid nonempty graph `G₀`, positive lengths `ℓ₀` and weights `v`, parameter
`k ≥ 1`, valid sequence of update batches `Us`, and positive edge lengths `ℓ` agreeing with `ℓ₀`
on surviving un-inserted edges, `initLSF` and `applyLSFBatches` satisfy all guarantees 1–4 of
Lemma 5.4, including `G.IsSubgraph S.RF.F` and `S.T.IsSubgraph S.RF.F` (with additive `+ 1` /
`(components G₀).card * K * log²` on initial component count and `+ 6 + ...` on `W.card` when `G₀`
is disconnected or `k > m`). -/
theorem lemma_5_4 (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hLSST : HasLSSTSpec oracle C_lsst) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (G₀ : MGraph) (_hG₀ : G₀.IsValid) (_hV₀ : G₀.V.Nonempty)
        (ℓ₀ v : ℕ → ℝ) (_hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (_hv : ∀ e ∈ G₀.E, 0 < v e)
        (k : ℝ) (_hk : 1 ≤ k)
        (Us : List (List Update)) (_hUs : BatchesIsValid G₀ Us)
        (ℓ : ℕ → ℝ)
        (_hℓ : ∀ e ∈ (Us.foldl MGraph.applyBatch G₀).E, 0 < ℓ e)
        (_hℓ_orig : ∀ e ∈ G₀.E, e ∈ (Us.foldl MGraph.applyBatch G₀).E →
          e ∉ (applyLSFBatches (initLSF oracle C_lsst G₀ ℓ₀ v k) Us).insertedEdges →
          ℓ e = ℓ₀ e),
        let S₀ := initLSF oracle C_lsst G₀ ℓ₀ v k
        let S := applyLSFBatches S₀ Us
        let G := Us.foldl MGraph.applyBatch G₀
        let q := totalUpdates Us
        S.G = G ∧
        S.RF.F.E ⊆ S₀.RF.F.E ∧
        G.IsSubgraph S.RF.F ∧
        S.T.IsSubgraph S.RF.F ∧
        (∀ e ∈ S.insertedEdges, S.wstr e = 1) ∧
        (∀ e ∈ G.E, e ∉ S.insertedEdges → S.wstr e = S₀.wstr e) ∧
        ((components S₀.RF.F).card : ℝ) ≤
          (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
            else ((components G₀).card : ℝ) * K * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
            K * ((G₀.E.card : ℝ) / k) ∧
        ((components S.RF.F).card : ℝ) ≤ ((components S₀.RF.F).card : ℝ) +
          K * (q : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ∧
        S.lsf.Holds G ℓ (K * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 6) ∧
        ∑ e ∈ G₀.E, v e * S₀.wstr e ≤ K * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 4 ∧
        (S.W_init.card : ℝ) ≤
          6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
            else ((components G₀).card : ℝ) * K * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
            K * ((G₀.E.card : ℝ) / k) ∧
        S.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E ∧
        (∀ W₁ ∈ S.W_init, ∀ W₂ ∈ S.W_init, W₁ ≠ W₂ →
          Disjoint (inducedEdges S₀.RF.F W₁) (inducedEdges S₀.RF.F W₂)) ∧
        boundary S.W_init ⊆ S.R ∧
        ∀ W ∈ S.W_init, PathConvex S.T₀ W ∧ W ⊆ G.V ∧
          (pieceBoundary S.W_init W).card ≤ 1 ∧
          (G.vol (W \ S.R) : ℝ) ≤ K * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
  refine ⟨6272 * max 1 C_lsst, by positivity, ?_⟩
  intro G₀ hG₀ hV₀ ℓ₀ v hℓ₀ hv k hk Us hUs ℓ hℓ hℓ_orig S₀ S G q
  have hC1 : 1 ≤ max 1 C_lsst := le_max_left _ _
  have hk_pos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hL := half_lt_log_add_two G₀.n
  have hL_nn : 0 ≤ Real.log ((G₀.n : ℝ) + 2) := by linarith
  have hsp₀ := initLSF_spec hLSST hG₀ hV₀ hℓ₀ hv hk
  rcases hsp₀ with ⟨hG₀₀, hG₀_eq, _, hk₀, hiso₀, hins₀, _, hT_cur₀, horig₀, hT₀₀, hTV₀, _, _,
    _, _, _, _, _, hR₀_card, _, hwstr₀_cs, hwstr₀_sum, hW₀_card, hb_W₀, hcov₀, hdisj₀, _⟩
  have hI₀ := initLSF_inv hLSST hG₀ hV₀ hℓ₀ hv hk
  have hbatches := applyLSFBatches_inv Us hI₀ (hG₀_eq.symm ▸ hUs)
  rcases hbatches with ⟨hI, hSG, hG₀_eq', hT₀_eq', hr₀_eq', hπ_eq', hk_eq', hW_eq, hR_sub,
    hFE_sub, hR_growth⟩
  have hS₀_comp : (components S₀.RF.F).card = S₀.R.card :=
    rootedForest_components_card hI₀.to_RF_spanning
  have hS_comp : (components S.RF.F).card = S.R.card :=
    rootedForest_components_card hI.to_RF_spanning
  have hSG' : S.G = G := hSG.trans (by rw [hG₀_eq])
  have hTF' : S.T.IsSubgraph S.RF.F :=
    ⟨Finset.Subset.refl _, hI.hT_cur_E ▸ Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
  refine ⟨hSG', hFE_sub, hSG' ▸ hI.hF_sub_G, hTF',
    fun e he => (hI.hins_wstr e he).1, ?_, ?_, ?_, ?_, ?_, ?_, hW_eq ▸ hcov₀,
    fun W₁ h1 W₂ h2 hne => hdisj₀ W₁ (hW_eq ▸ h1) W₂ (hW_eq ▸ h2) hne, ?_, ?_⟩
  · intro e heG he_nins
    have heS : e ∈ S.G.E := by rw [hSG']; exact heG
    have hse := hI.hsurv_edge e heS he_nins
    have hG₀e : e ∈ G₀.E := by rw [← hG₀₀, ← hG₀_eq']; exact hse.1
    rw [hse.2.1, hG₀_eq', hG₀₀, hT₀_eq', hr₀_eq', hπ_eq', hk_eq', hk₀]
    split_ifs with hth
    · exact ((hwstr₀_cs e hG₀e).2 hth).1.symm
    · exact ((hwstr₀_cs e hG₀e).1 (not_le.mp hth)).symm
  · rw [hS₀_comp]
    have h28_le : (28 : ℝ) ≤ 6272 * max 1 C_lsst := by linarith
    have h4_le : 4 * ((G₀.E.card : ℝ) / k) ≤ 6272 * max 1 C_lsst * ((G₀.E.card : ℝ) / k) :=
      mul_le_mul_of_nonneg_right (by linarith) (div_nonneg (Nat.cast_nonneg _) hk_pos.le)
    have hcomp_le : (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then (1 : ℝ)
        else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) ≤
        (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
        else ((components G₀).card : ℝ) * (6272 * max 1 C_lsst) *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 2) := by
      split_ifs
      · exact le_rfl
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h28_le (Nat.cast_nonneg _)) (sq_nonneg _)
    calc (S₀.R.card : ℝ)
        ≤ (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
            else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
            4 * (G₀.E.card : ℝ) / k := hR₀_card
      _ = (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
            else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
            4 * ((G₀.E.card : ℝ) / k) := by ring
      _ ≤ (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
            else ((components G₀).card : ℝ) * (6272 * max 1 C_lsst) *
              (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
            6272 * max 1 C_lsst * ((G₀.E.card : ℝ) / k) := add_le_add hcomp_le h4_le
  · rw [hS_comp, hS₀_comp]
    rw [hG₀₀] at hR_growth
    have h56_le : 56 ≤ 6272 * max 1 C_lsst := by linarith
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h56_le (Nat.cast_nonneg q)) (sq_nonneg (Real.log ((G₀.n : ℝ) + 2)))
    linarith [hR_growth]
  · have hℓ_S : ∀ e ∈ S.G.E, 0 < ℓ e :=
      fun e he => hℓ e (by show e ∈ G.E; rw [← hSG']; exact he)
    have hℓ_orig_S : ∀ e ∈ S.G₀.E, e ∈ S.G.E → e ∉ S.insertedEdges → ℓ e = ℓ₀ e := by
      intro e he₀ heS he_nins
      exact hℓ_orig e (by rw [← hG₀₀, ← hG₀_eq']; exact he₀)
        (by show e ∈ G.E; rw [← hSG']; exact heS) he_nins
    have hholds := hI.to_Holds hℓ_S hℓ_orig_S
    rw [hSG', hG₀_eq', hG₀₀, hk_eq', hk₀] at hholds
    exact hholds
  · have h224_le : 224 * max 1 C_lsst ≤ 6272 * max 1 C_lsst := by linarith
    have hnorm0 : 0 ≤ G₀.norm1 v := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h224_le hnorm0) (pow_nonneg hL_nn 4)
    exact hwstr₀_sum.trans hmul
  · rw [hW_eq]
    have h28_le : (28 : ℝ) ≤ 6272 * max 1 C_lsst := by linarith
    have h10_le : 10 * ((G₀.E.card : ℝ) / k) ≤ 6272 * max 1 C_lsst * ((G₀.E.card : ℝ) / k) :=
      mul_le_mul_of_nonneg_right (by linarith) (div_nonneg (Nat.cast_nonneg G₀.E.card) hk_pos.le)
    have hcomp_le : (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then (1 : ℝ)
        else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) ≤
        (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
        else ((components G₀).card : ℝ) * (6272 * max 1 C_lsst) *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 2) := by
      split_ifs
      · exact le_rfl
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h28_le (Nat.cast_nonneg _)) (sq_nonneg _)
    calc (S₀.W_init.card : ℝ)
        ≤ 6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
            else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
            10 * (G₀.E.card : ℝ) / k := hW₀_card
      _ = 6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
            else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
            10 * ((G₀.E.card : ℝ) / k) := by ring
      _ ≤ 6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
            else ((components G₀).card : ℝ) * (6272 * max 1 C_lsst) *
              (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
            6272 * max 1 C_lsst * ((G₀.E.card : ℝ) / k) :=
          add_le_add (add_le_add le_rfl hcomp_le) h10_le
  · rw [hW_eq]
    exact hb_W₀.trans (fun x hx => hR_sub (Finset.mem_union_left _ hx))
  · intro W hW
    have hwp := hI.hW_props W hW
    have hv := hI.vol_bound hW
    rw [hSG', hG₀_eq', hk_eq'] at hv
    have hW_sub_GV : W ⊆ G.V := by
      rw [← hSG', hI.hGV_eq]
      exact Finset.Subset.trans hwp.2.1 Finset.subset_union_left
    have h2240_le : 2240 ≤ 6272 * max 1 C_lsst := by linarith
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2240_le hk_pos.le) (sq_nonneg (Real.log ((G₀.n : ℝ) + 2)))
    exact ⟨hwp.1, hW_sub_GV, hwp.2.2.1, hv.trans hmul⟩

/-- Snapshot corollary of Lemma 5.4: at any stage after valid batches `Us`, the maintained
triple `(T, F, wstr)` satisfies `LSF.Holds G ℓ (K * k * log^6(G₀.n + 2))`. -/
lemma lemma_5_4_holds (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hLSST : HasLSSTSpec oracle C_lsst) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (G₀ : MGraph), G₀.IsValid → G₀.V.Nonempty →
        ∀ (ℓ₀ v : ℕ → ℝ), (∀ e ∈ G₀.E, 0 < ℓ₀ e) → (∀ e ∈ G₀.E, 0 < v e) →
        ∀ (k : ℝ), 1 ≤ k →
        ∀ (Us : List (List Update)), BatchesIsValid G₀ Us →
        ∀ (ℓ : ℕ → ℝ), (∀ e ∈ (Us.foldl MGraph.applyBatch G₀).E, 0 < ℓ e) →
        (∀ e ∈ G₀.E, e ∈ (Us.foldl MGraph.applyBatch G₀).E →
          e ∉ (applyLSFBatches (initLSF oracle C_lsst G₀ ℓ₀ v k) Us).insertedEdges →
          ℓ e = ℓ₀ e) →
        (applyLSFBatches (initLSF oracle C_lsst G₀ ℓ₀ v k) Us).lsf.Holds
          (Us.foldl MGraph.applyBatch G₀) ℓ (K * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 6) := by
  obtain ⟨K, hK, hmain⟩ := lemma_5_4 oracle C_lsst hLSST
  exact ⟨K, hK, fun G₀ hG₀ hV₀ ℓ₀ v hℓ₀ hv k hk Us hUs ℓ hℓ hℓ_orig =>
    (hmain G₀ hG₀ hV₀ ℓ₀ v hℓ₀ hv k hk Us hUs ℓ hℓ hℓ_orig).2.2.2.2.2.2.2.2.1⟩

end MinCostFlow.LSF
