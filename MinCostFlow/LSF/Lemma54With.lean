module

public import MinCostFlow.LSF.Lemma54InitWith
public import MinCostFlow.LSF.Lemma54
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Dynamic Invariants and Lemma 5.4 for Parameterized `initLSFWith`

This file lifts `initLSFWith_spec` to `LSFInvWith` (`initLSFWith_inv`), then delegates all update
and batch preservation proofs directly to `applyLSFBatches_inv_with`, `LSFInvWith.to_Holds`, and
`LSFInvWith.vol_bound` from `MinCostFlow.LSF.Lemma54`.

It provides:
* `lemma_5_4_with_explicit`: explicit constant `K = max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240)`.
* `lemma_5_4_with`, `lemma_5_4_with_holds`: uniform existential form over all valid parameters.
* `lemma_5_4_withCore`: three-parameter corollary for `initLSFWithCore`.
* `lemma_5_4_of_with`: derivation of `lemma_5_4` as the `(α = 1, K_σ = 6272 * max 1 C_lsst)` case.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Initialization satisfies `LSFInvWith` -/

/-- `initLSFWith` satisfies `LSFInvWith thresh K_σ ℓ₀` under `ValidLSFParams`. -/
lemma initLSFWith_inv {C_lsst α thresh K_σ : ℝ} {G₀ : MGraph}
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ v : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hv : ∀ e ∈ G₀.E, 0 < v e)
    {k : ℝ} (hk : 1 ≤ k)
    {T_raw : MGraph} {r₀ : ℕ} {C_reps : Finset ℕ} {π : ℕ → ℕ} {W_T : Finset (Finset ℕ)}
    (hp : ValidLSFParams C_lsst α thresh K_σ G₀ ℓ₀ v k T_raw r₀ C_reps π W_T) :
    LSFInvWith thresh K_σ ℓ₀ (initLSFWith G₀ ℓ₀ v k T_raw r₀ C_reps π W_T thresh) := by
  have hsp := initLSFWith_spec hG₀ hV₀ hℓ₀ hv hk hp
  rcases hsp with ⟨hG₀_eq, hG_eq, _, hk_eq, hiso, hins, _, hT_cur_eq, horig_eq,
    hT₀, hTV, hr₀_b, hR₀_sub, hord, hTG₀, hTp₀, hpi_br, hsub₀, _,
    hwstr_bd, hwstr_cs, _, _, hb_W, _, _, hW_pr⟩
  set S₀ := initLSFWith G₀ ℓ₀ v k T_raw r₀ C_reps π W_T thresh
  have hsurv : ∀ e ∈ S₀.G.E, e ∉ S₀.insertedEdges →
      e ∈ S₀.G₀.E ∧
      S₀.wstr e = (if thresh ≤
          levelStretchBound S₀.T₀ S₀.r₀ S₀.π S₀.G₀ (safeLen S₀.G₀ ℓ₀) e
        then 1 else levelStretchBound S₀.T₀ S₀.r₀ S₀.π S₀.G₀ (safeLen S₀.G₀ ℓ₀) e) ∧
      (S₀.G.tail e ≠ S₀.G₀.tail e → S₀.G₀.tail e ∈ S₀.R_orig ∧ S₀.G.tail e ∈ S₀.isolatedVerts) ∧
      (S₀.G.head e ≠ S₀.G₀.head e → S₀.G₀.head e ∈ S₀.R_orig ∧ S₀.G.head e ∈ S₀.isolatedVerts) ∧
      (thresh ≤ levelStretchBound S₀.T₀ S₀.r₀ S₀.π S₀.G₀ (safeLen S₀.G₀ ℓ₀) e →
        S₀.G₀.tail e ∈ S₀.R_orig ∧ S₀.G₀.head e ∈ S₀.R_orig) := by
    intro e he _
    have heG₀ : e ∈ G₀.E := hG_eq ▸ he
    refine ⟨hG₀_eq ▸ heG₀, ?_,
      fun h => absurd (congrArg (fun M => M.tail e) (hG_eq.trans hG₀_eq.symm)) h,
      fun h => absurd (congrArg (fun M => M.head e) (hG_eq.trans hG₀_eq.symm)) h, fun hge => ?_⟩
    · by_cases hth : thresh ≤
          levelStretchBound S₀.T₀ S₀.r₀ S₀.π S₀.G₀ (safeLen S₀.G₀ ℓ₀) e
      · rw [ite_eq_left_iff.mpr (fun h => absurd hth h)]
        exact (hwstr_cs e heG₀).2 (by simpa only [hG₀_eq] using hth) |>.1
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hth)]
        exact (hwstr_cs e heG₀).1 (not_le.mp (by simpa only [hG₀_eq] using hth))
    · have h2 := (hwstr_cs e heG₀).2 (by simpa only [hG₀_eq] using hge)
      simpa only [hG₀_eq] using ⟨h2.2.1, h2.2.2⟩
  refine
    { hG₀_val := hG₀_eq ▸ hG₀
      hG_val := hG_eq ▸ hG₀
      hV₀ := hG₀_eq ▸ hV₀
      hk := hk_eq ▸ hk
      hℓ₀ := fun e he => hℓ₀ e (hG₀_eq ▸ he)
      hT₀ := hT₀
      hTV := hG₀_eq ▸ hTV
      hr₀_base := hr₀_b
      hR₀_sub := hR₀_sub
      hord := hord
      hTG₀ := fun f hf hfG => by
        simpa only [hG₀_eq] using hTG₀ f hf (hG₀_eq ▸ hfG)
      hTp₀ := fun e he => by
        simpa only [hG₀_eq] using hTp₀ e (hG₀_eq ▸ he)
      hpi_br := fun b hb hbG g hg hgG =>
        hpi_br b hb (hG₀_eq ▸ hbG) g hg (hG₀_eq ▸ hgG)
      hT_cur_forest := hT_cur_eq ▸ hT₀.isForest
      hT_cur_V := by rw [hT_cur_eq, hTV, hG_eq]
      hT_cur_E := by rw [hT_cur_eq]
      hF_sub_G := hG_eq.symm ▸ hsub₀
      horig_id := fun x _ => congrFun horig_eq x
      horig_split := fun x hx => by rw [hiso] at hx; exact absurd hx (Finset.notMem_empty _)
      horig_T := fun e _ => by rw [hT_cur_eq, horig_eq]; exact ⟨rfl, rfl⟩
      horig_G_nins := fun e _ _ => by rw [hG_eq, hG₀_eq, horig_eq]; exact ⟨rfl, rfl⟩
      hunsplit_F := fun x _ _ f _ => by rw [hT_cur_eq, horig_eq]; exact ⟨fun h => h, fun h => h⟩
      hdisj_iso := hiso ▸ Finset.disjoint_empty_right _
      hGV_eq := by rw [hG_eq, hTV, hiso, Finset.union_empty]
      hins_sub := hins ▸ Finset.empty_subset _
      hins_wstr := fun e he => by rw [hins] at he; exact absurd he (Finset.notMem_empty _)
      horig_del := fun e he => Or.inl ⟨hG_eq ▸ (hG₀_eq ▸ he), hins ▸ Finset.notMem_empty _⟩
      hsurv_edge := hsurv
      hwstr_bound := fun e he => by
        simpa only [hG₀_eq, hk_eq] using hwstr_bd e (hG_eq ▸ he)
      hthresh_bd := by
        simpa only [hG₀_eq, hk_eq] using ⟨hp.hthresh.1, hp.hthresh.2.2⟩
      hdeg_le := fun x _ _ => by rw [hG_eq, hG₀_eq]
      hb_W := hb_W
      hW_props := fun W hW => by
        have hw := hW_pr W hW
        exact ⟨hw.1, hTV ▸ hw.2.1, hw.2.2.1, by simpa only [hG₀_eq, hk_eq] using hw.2.2.2⟩ }

/-! ## Parameterized Lemma 5.4 -/

open Classical in
/-- Explicit-constant Lemma 5.4 for `initLSFWith`. -/
theorem lemma_5_4_with_explicit (C_lsst α K_σ : ℝ)
    (G₀ : MGraph) (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (ℓ₀ v : ℕ → ℝ) (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hv : ∀ e ∈ G₀.E, 0 < v e)
    (k : ℝ) (hk : 1 ≤ k)
    (T_raw : MGraph) (r₀ : ℕ) (C_reps : Finset ℕ) (π : ℕ → ℕ)
    (W_T : Finset (Finset ℕ)) (thresh : ℝ)
    (hp : ValidLSFParams C_lsst α thresh K_σ G₀ ℓ₀ v k T_raw r₀ C_reps π W_T)
    (Us : List (List Update)) (hUs : BatchesIsValid G₀ Us)
    (ℓ : ℕ → ℝ)
    (hℓ : ∀ e ∈ (Us.foldl MGraph.applyBatch G₀).E, 0 < ℓ e)
    (hℓ_orig : ∀ e ∈ G₀.E, e ∈ (Us.foldl MGraph.applyBatch G₀).E →
      e ∉ (applyLSFBatches (initLSFWith G₀ ℓ₀ v k T_raw r₀ C_reps π W_T thresh) Us).insertedEdges →
      ℓ e = ℓ₀ e) :
    let K := max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240)
    let S₀ := initLSFWith G₀ ℓ₀ v k T_raw r₀ C_reps π W_T thresh
    let S := applyLSFBatches S₀ Us
    let G := Us.foldl MGraph.applyBatch G₀
    let q := totalUpdates Us
    0 < K ∧
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
  intro K S₀ S G q
  have hKσ_le : K_σ ≤ K := le_max_left _ _
  have hw_le : 112 * (1 + α) * max 1 C_lsst ≤ K :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h2240_le : 2240 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hK_pos : 0 < K := by linarith
  have hk_pos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hL := half_lt_log_add_two G₀.n
  have hL_nn : 0 ≤ Real.log ((G₀.n : ℝ) + 2) := by linarith
  have hsp₀ := initLSFWith_spec hG₀ hV₀ hℓ₀ hv hk hp
  rcases hsp₀ with ⟨hG₀₀, hG₀_eq, _, hk₀, hiso₀, hins₀, _, hT_cur₀, horig₀, hT₀₀, hTV₀, _, _,
    _, _, _, _, _, hR₀_card, _, hwstr₀_cs, hwstr₀_sum, hW₀_card, hb_W₀, hcov₀, hdisj₀, _⟩
  have hI₀ := initLSFWith_inv hG₀ hV₀ hℓ₀ hv hk hp
  have hbatches := applyLSFBatches_inv_with Us hI₀ (hG₀_eq.symm ▸ hUs)
  rcases hbatches with ⟨hI, hSG, hG₀_eq', hT₀_eq', hr₀_eq', hπ_eq', hk_eq', hW_eq, hR_sub,
    hFE_sub, hR_growth⟩
  have hS₀_comp : (components S₀.RF.F).card = S₀.R.card :=
    rootedForest_components_card hI₀.to_RF_spanning
  have hS_comp : (components S.RF.F).card = S.R.card :=
    rootedForest_components_card hI.to_RF_spanning
  have hSG' : S.G = G := hSG.trans (by rw [hG₀_eq])
  have hTF' : S.T.IsSubgraph S.RF.F :=
    ⟨Finset.Subset.refl _, hI.hT_cur_E ▸ Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
  refine ⟨hK_pos, hSG', hFE_sub, hSG' ▸ hI.hF_sub_G, hTF',
    fun e he => (hI.hins_wstr e he).1, ?_, ?_, ?_, ?_, ?_, ?_, hW_eq ▸ hcov₀,
    fun W₁ h1 W₂ h2 hne => hdisj₀ W₁ (hW_eq ▸ h1) W₂ (hW_eq ▸ h2) hne, ?_, ?_⟩
  · intro e heG he_nins
    have heS : e ∈ S.G.E := by rw [hSG']; exact heG
    have hse := hI.hsurv_edge e heS he_nins
    have hG₀e : e ∈ G₀.E := by rw [← hG₀₀, ← hG₀_eq']; exact hse.1
    rw [hse.2.1, hG₀_eq', hG₀₀, hT₀_eq', hr₀_eq', hπ_eq']
    split_ifs with hth
    · exact ((hwstr₀_cs e hG₀e).2 hth).1.symm
    · exact ((hwstr₀_cs e hG₀e).1 (not_le.mp hth)).symm
  · rw [hS₀_comp]
    have h28_le : (28 : ℝ) ≤ K := by linarith
    have h4_le : 4 * ((G₀.E.card : ℝ) / k) ≤ K * ((G₀.E.card : ℝ) / k) :=
      mul_le_mul_of_nonneg_right (by linarith) (div_nonneg (Nat.cast_nonneg _) hk_pos.le)
    have hcomp_le : (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then (1 : ℝ)
        else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) ≤
        (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
        else ((components G₀).card : ℝ) * K * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) := by
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
            else ((components G₀).card : ℝ) * K * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
            K * ((G₀.E.card : ℝ) / k) := add_le_add hcomp_le h4_le
  · rw [hS_comp, hS₀_comp]
    rw [hG₀₀] at hR_growth
    have h56_le : 56 ≤ K := by linarith
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
    refine ⟨hholds.1, hholds.2.1, hholds.2.2.1, fun e he => ⟨(hholds.2.2.2 e he).1, ?_⟩⟩
    have hmul : K_σ * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 ≤
        K * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKσ_le hk_pos.le) (pow_nonneg hL_nn 6)
    exact (hholds.2.2.2 e he).2.trans hmul
  · have hnorm0 : 0 ≤ G₀.norm1 v := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hw_le hnorm0) (pow_nonneg hL_nn 4)
    exact hwstr₀_sum.trans hmul
  · rw [hW_eq]
    have h28_le : (28 : ℝ) ≤ K := by linarith
    have h10_le : 10 * ((G₀.E.card : ℝ) / k) ≤ K * ((G₀.E.card : ℝ) / k) :=
      mul_le_mul_of_nonneg_right (by linarith) (div_nonneg (Nat.cast_nonneg G₀.E.card) hk_pos.le)
    have hcomp_le : (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then (1 : ℝ)
        else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) ≤
        (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
        else ((components G₀).card : ℝ) * K * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) := by
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
            else ((components G₀).card : ℝ) * K * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
            K * ((G₀.E.card : ℝ) / k) := add_le_add (add_le_add le_rfl hcomp_le) h10_le
  · rw [hW_eq]
    exact hb_W₀.trans (fun x hx => hR_sub (Finset.mem_union_left _ hx))
  · intro W hW
    have hwp := hI.hW_props W hW
    have hv := hI.vol_bound hW
    rw [hSG', hG₀_eq', hk_eq'] at hv
    have hW_sub_GV : W ⊆ G.V := by
      rw [← hSG', hI.hGV_eq]
      exact Finset.Subset.trans hwp.2.1 Finset.subset_union_left
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2240_le hk_pos.le) (sq_nonneg (Real.log ((G₀.n : ℝ) + 2)))
    exact ⟨hwp.1, hW_sub_GV, hwp.2.2.1, hv.trans hmul⟩

open Classical in
/-- Existential Lemma 5.4 for `initLSFWith` over all valid parameter tuples `(T_raw, r₀, C_reps,
π, W_T, thresh)` satisfying `ValidLSFParams C_lsst α thresh K_σ`. -/
theorem lemma_5_4_with (C_lsst α K_σ : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (G₀ : MGraph) (_hG₀ : G₀.IsValid) (_hV₀ : G₀.V.Nonempty)
        (ℓ₀ v : ℕ → ℝ) (_hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (_hv : ∀ e ∈ G₀.E, 0 < v e)
        (k : ℝ) (_hk : 1 ≤ k)
        (T_raw : MGraph) (r₀ : ℕ) (C_reps : Finset ℕ) (π : ℕ → ℕ)
        (W_T : Finset (Finset ℕ)) (thresh : ℝ)
        (_hp : ValidLSFParams C_lsst α thresh K_σ G₀ ℓ₀ v k T_raw r₀ C_reps π W_T)
        (Us : List (List Update)) (_hUs : BatchesIsValid G₀ Us)
        (ℓ : ℕ → ℝ)
        (_hℓ : ∀ e ∈ (Us.foldl MGraph.applyBatch G₀).E, 0 < ℓ e)
        (_hℓ_orig : ∀ e ∈ G₀.E, e ∈ (Us.foldl MGraph.applyBatch G₀).E →
          e ∉ (applyLSFBatches (initLSFWith G₀ ℓ₀ v k T_raw r₀ C_reps π W_T thresh) Us).insertedEdges →
          ℓ e = ℓ₀ e),
        let S₀ := initLSFWith G₀ ℓ₀ v k T_raw r₀ C_reps π W_T thresh
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
  refine ⟨max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240), by
    have : 2240 ≤ max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240) :=
      (le_max_right _ _).trans (le_max_right _ _)
    linarith, ?_⟩
  intro G₀ hG₀ hV₀ ℓ₀ v hℓ₀ hv k hk T_raw r₀ C_reps π W_T thresh hp Us hUs ℓ hℓ hℓ_orig
  exact (lemma_5_4_with_explicit C_lsst α K_σ G₀ hG₀ hV₀ ℓ₀ v hℓ₀ hv k hk
    T_raw r₀ C_reps π W_T thresh hp Us hUs ℓ hℓ hℓ_orig).2

/-- Snapshot corollary of `lemma_5_4_with`. -/
lemma lemma_5_4_with_holds (C_lsst α K_σ : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (G₀ : MGraph) (_hG₀ : G₀.IsValid) (_hV₀ : G₀.V.Nonempty)
        (ℓ₀ v : ℕ → ℝ) (_hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (_hv : ∀ e ∈ G₀.E, 0 < v e)
        (k : ℝ) (_hk : 1 ≤ k)
        (T_raw : MGraph) (r₀ : ℕ) (C_reps : Finset ℕ) (π : ℕ → ℕ)
        (W_T : Finset (Finset ℕ)) (thresh : ℝ)
        (_hp : ValidLSFParams C_lsst α thresh K_σ G₀ ℓ₀ v k T_raw r₀ C_reps π W_T)
        (Us : List (List Update)) (_hUs : BatchesIsValid G₀ Us)
        (ℓ : ℕ → ℝ)
        (_hℓ : ∀ e ∈ (Us.foldl MGraph.applyBatch G₀).E, 0 < ℓ e)
        (_hℓ_orig : ∀ e ∈ G₀.E, e ∈ (Us.foldl MGraph.applyBatch G₀).E →
          e ∉ (applyLSFBatches (initLSFWith G₀ ℓ₀ v k T_raw r₀ C_reps π W_T thresh) Us).insertedEdges →
          ℓ e = ℓ₀ e),
        let S := applyLSFBatches (initLSFWith G₀ ℓ₀ v k T_raw r₀ C_reps π W_T thresh) Us
        let G := Us.foldl MGraph.applyBatch G₀
        S.lsf.Holds G ℓ (K * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 6) := by
  obtain ⟨K, hK_pos, h54⟩ := lemma_5_4_with C_lsst α K_σ
  exact ⟨K, hK_pos, fun G₀ hG₀ hV₀ ℓ₀ v hℓ₀ hv k hk T_raw r₀ C_reps π W_T thresh hp Us hUs ℓ hℓ hℓ_orig =>
    (h54 G₀ hG₀ hV₀ ℓ₀ v hℓ₀ hv k hk T_raw r₀ C_reps π W_T thresh hp Us hUs ℓ hℓ hℓ_orig).2.2.2.2.2.2.2.2.1⟩

open Classical in
/-- `lemma_5_4_withCore` for the three-parameter wrapper `initLSFWithCore`. -/
theorem lemma_5_4_withCore (C_lsst : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (G₀ : MGraph) (_hG₀ : G₀.IsValid) (_hV₀ : G₀.V.Nonempty)
        (ℓ₀ v : ℕ → ℝ) (_hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (_hv : ∀ e ∈ G₀.E, 0 < v e)
        (k : ℝ) (_hk : 1 ≤ k)
        (T_raw : MGraph) (r₀ : ℕ) (W_T : Finset (Finset ℕ))
        (_hT_raw : IsLSST (if G₀.E.Nonempty then weightedCopyGraph G₀ v else G₀)
          (if G₀.E.Nonempty then weightedCopyLen G₀ ℓ₀ else fun _ => 1)
          (fun _ => 1) (C_lsst * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) T_raw)
        (_hr₀ : r₀ ∈ G₀.V)
        (_hW_T : IsTreeDecompSpec G₀ (projectTree G₀ v T_raw) k W_T)
        (Us : List (List Update)) (_hUs : BatchesIsValid G₀ Us)
        (ℓ : ℕ → ℝ)
        (_hℓ : ∀ e ∈ (Us.foldl MGraph.applyBatch G₀).E, 0 < ℓ e)
        (_hℓ_orig : ∀ e ∈ G₀.E, e ∈ (Us.foldl MGraph.applyBatch G₀).E →
          e ∉ (applyLSFBatches (initLSFWithCore C_lsst G₀ ℓ₀ v k T_raw r₀ W_T) Us).insertedEdges →
          ℓ e = ℓ₀ e),
        let S₀ := initLSFWithCore C_lsst G₀ ℓ₀ v k T_raw r₀ W_T
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
  obtain ⟨K, hK_pos, h54⟩ := lemma_5_4_with C_lsst 1 (6272 * max 1 C_lsst)
  refine ⟨K, hK_pos, ?_⟩
  intro G₀ hG₀ hV₀ ℓ₀ v hℓ₀ hv k hk T_raw r₀ W_T hT_raw hr₀ hW_T Us hUs ℓ hℓ hℓ_orig
  let G_v := weightedCopyGraph G₀ v
  let ℓ_v := weightedCopyLen G₀ ℓ₀
  let T₀ := projectTree G₀ v T_raw
  let π :=
    if G₀.E.Nonempty then congOrder T₀ (congestion G_v T₀ ℓ_v)
    else congOrder T₀ (congestion G₀ T₀ (fun _ => 1))
  have hp : ValidLSFParams C_lsst 1 (wstrThresh C_lsst G₀.n k) (6272 * max 1 C_lsst) G₀ ℓ₀ v k
      T_raw r₀ (compReps G₀ r₀) π W_T := by
    refine ⟨hT_raw, hr₀, ⟨compReps_mem hr₀, compReps_subset hG₀ hr₀,
      compReps_card_le G₀ r₀, fun _ hw => compReps_connected hw⟩, ?_, hW_T, isWstrThresh_wstrThresh hk⟩
    by_cases hE : G₀.E.Nonempty <;> simp only [hE, ↓reduceIte, π] <;>
      exact isApproxCongOrder_congOrder _ _ _
  have hS_eq : initLSFWithCore C_lsst G₀ ℓ₀ v k T_raw r₀ W_T =
      initLSFWith G₀ ℓ₀ v k T_raw r₀ (compReps G₀ r₀) π W_T (wstrThresh C_lsst G₀.n k) :=
    initLSFWithCore_eq_initLSFWith C_lsst G₀ ℓ₀ v k T_raw r₀ W_T
  simpa only [hS_eq] using
    h54 G₀ hG₀ hV₀ ℓ₀ v hℓ₀ hv k hk T_raw r₀ (compReps G₀ r₀) π W_T (wstrThresh C_lsst G₀.n k)
      hp Us hUs ℓ hℓ (by simpa only [hS_eq] using hℓ_orig)

open Classical in
/-- Derivation of `lemma_5_4` as a special case of `lemma_5_4_with_explicit` and
`initLSF_eq_initLSFWith`. -/
theorem lemma_5_4_of_with (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
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
  intro G₀ hG₀ hV₀ ℓ₀ v hℓ₀ hv k hk Us hUs ℓ hℓ hℓ_orig
  let G_v := weightedCopyGraph G₀ v
  let ℓ_v := weightedCopyLen G₀ ℓ₀
  let T_raw := if G₀.E.Nonempty then oracle G_v ℓ_v (fun _ => 1) else oracle G₀ (fun _ => 1) (fun _ => 1)
  let T₀ := projectTree G₀ v T_raw
  let r₀ := pickRoot G₀
  let π :=
    if G₀.E.Nonempty then congOrder T₀ (congestion G_v T₀ ℓ_v)
    else congOrder T₀ (congestion G₀ T₀ (fun _ => 1))
  have hp := validLSFParams_initLSF hLSST hG₀ hV₀ hℓ₀ hv hk
  have hS_eq : initLSF oracle C_lsst G₀ ℓ₀ v k =
      initLSFWith G₀ ℓ₀ v k T_raw r₀ (compReps G₀ r₀) π (pickDecomp G₀ T₀ r₀ k)
        (wstrThresh C_lsst G₀.n k) :=
    initLSF_eq_initLSFWith oracle C_lsst G₀ ℓ₀ v k
  have hK_eq : max (6272 * max 1 C_lsst) (max (112 * (1 + 1) * max 1 C_lsst) 2240) =
      6272 * max 1 C_lsst := by
    have h1 : 1 ≤ max 1 C_lsst := le_max_left _ _
    have h2 : 112 * (1 + 1) * max 1 C_lsst ≤ 6272 * max 1 C_lsst := by linarith
    have h3 : (2240 : ℝ) ≤ 6272 * max 1 C_lsst := by linarith
    exact max_eq_left (max_le h2 h3)
  have hres := lemma_5_4_with_explicit C_lsst 1 (6272 * max 1 C_lsst)
    G₀ hG₀ hV₀ ℓ₀ v hℓ₀ hv k hk
    T_raw r₀ (compReps G₀ r₀) π (pickDecomp G₀ T₀ r₀ k) (wstrThresh C_lsst G₀.n k)
    hp Us hUs ℓ hℓ (by simpa only [← hS_eq] using hℓ_orig)
  simpa only [← hS_eq, hK_eq] using hres.2

end MinCostFlow.LSF
