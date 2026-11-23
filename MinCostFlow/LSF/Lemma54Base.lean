module

public import MinCostFlow.LSF.Lemma54Split
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemma54, first part

The first part of `Lemma54.lean`, split off to keep files short. It contains:
- Dynamic invariant `LSFInvWith` and `LSFInv`
- `RootedForest` properties of `S.RF` and stretch preservation
- Snapshots satisfy `LSF.Holds`
- Initialization preserves invariant and single-update transition
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Dynamic invariant `LSFInvWith` and `LSFInv` -/

/-- Parameterized dynamic invariant maintained by `applyLSFUpdate` for threshold `thresh` and
worst-case stretch bound `K_σ * S.k * log^6(S.G₀.n + 2)`. -/
structure LSFInvWith (thresh K_σ : ℝ) (ℓ₀ : ℕ → ℝ) (S : LSFState) : Prop where
  hG₀_val : S.G₀.IsValid
  hG_val : S.G.IsValid
  hV₀ : S.G₀.V.Nonempty
  hk : 1 ≤ S.k
  hℓ₀ : ∀ e ∈ S.G₀.E, 0 < ℓ₀ e
  hT₀ : IsRootedTree S.T₀ S.r₀
  hTV : S.T₀.V = S.G₀.V
  hr₀_base : S.r₀ ∈ S.R₀_base
  hR₀_sub : S.R₀_base ⊆ S.T₀.V
  hord : IsEdgeOrder S.T₀ S.π
  hTG₀ : ∀ f ∈ S.T₀.E, f ∈ S.G₀.E → S.T₀.tail f = S.G₀.tail f ∧ S.T₀.head f = S.G₀.head f
  hTp₀ : ∀ e ∈ S.G₀.E, walkEdges (S.T₀.forestPath (S.G₀.tail e) (S.G₀.head e)) ⊆ S.G₀.E
  hpi_br : ∀ b ∈ S.T₀.E, b ∉ S.G₀.E → ∀ g ∈ S.T₀.E, g ∈ S.G₀.E → S.π b < S.π g
  hT_cur_forest : S.T_cur.IsForest
  hT_cur_V : S.T_cur.V = S.G.V
  hT_cur_E : S.T_cur.E = S.T₀.E
  hF_sub_G : S.G.IsSubgraph S.RF.F
  horig_id : ∀ x ∈ S.T₀.V, S.origVert x = x
  horig_split : ∀ x ∈ S.isolatedVerts, S.origVert x ∈ S.R_orig
  horig_T : ∀ e ∈ S.T₀.E, S.origVert (S.T_cur.tail e) = S.T₀.tail e ∧ S.origVert (S.T_cur.head e) = S.T₀.head e
  horig_G_nins : ∀ e ∈ S.G.E, e ∉ S.insertedEdges →
    S.origVert (S.G.tail e) = S.G₀.tail e ∧ S.origVert (S.G.head e) = S.G₀.head e
  hunsplit_F : ∀ x ∈ S.G.V, S.origVert x ∉ S.R_orig → ∀ f ∈ S.T₀.E,
    (S.T₀.tail f = S.origVert x → S.T_cur.tail f = x) ∧
    (S.T₀.head f = S.origVert x → S.T_cur.head f = x)
  hdisj_iso : Disjoint S.T₀.V S.isolatedVerts
  hGV_eq : S.G.V = S.T₀.V ∪ S.isolatedVerts
  hins_sub : S.insertedEdges ⊆ S.G.E
  hins_wstr : ∀ e ∈ S.insertedEdges, S.wstr e = 1 ∧ S.G.tail e ∈ S.R ∧ S.G.head e ∈ S.R
  horig_del : ∀ e ∈ S.G₀.E,
    (e ∈ S.G.E ∧ e ∉ S.insertedEdges) ∨ (S.G₀.tail e ∈ S.R_orig ∧ S.G₀.head e ∈ S.R_orig)
  hsurv_edge : ∀ e ∈ S.G.E, e ∉ S.insertedEdges →
    e ∈ S.G₀.E ∧
    S.wstr e = (if thresh ≤
        levelStretchBound S.T₀ S.r₀ S.π S.G₀ (safeLen S.G₀ ℓ₀) e
      then 1 else levelStretchBound S.T₀ S.r₀ S.π S.G₀ (safeLen S.G₀ ℓ₀) e) ∧
    (S.G.tail e ≠ S.G₀.tail e → S.G₀.tail e ∈ S.R_orig ∧ S.G.tail e ∈ S.isolatedVerts) ∧
    (S.G.head e ≠ S.G₀.head e → S.G₀.head e ∈ S.R_orig ∧ S.G.head e ∈ S.isolatedVerts) ∧
    (thresh ≤
        levelStretchBound S.T₀ S.r₀ S.π S.G₀ (safeLen S.G₀ ℓ₀) e →
      S.G₀.tail e ∈ S.R_orig ∧ S.G₀.head e ∈ S.R_orig)
  hwstr_bound : ∀ e ∈ S.G.E,
    S.wstr e ≤ K_σ * S.k * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 6
  hthresh_bd : 1 ≤ thresh ∧ thresh ≤ K_σ * S.k * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 6
  hdeg_le : ∀ x ∈ S.T₀.V, x ∉ S.R → S.G.deg x ≤ S.G₀.deg x
  hb_W : boundary S.W_init ⊆ S.R_orig
  hW_props : ∀ W ∈ S.W_init,
    PathConvex S.T₀ W ∧ W ⊆ S.T₀.V ∧ (pieceBoundary S.W_init W).card ≤ 1 ∧
      (S.G₀.vol (W \ S.R_orig) : ℝ) ≤ 2240 * S.k * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 2

/-- Dynamic invariant maintained by `applyLSFUpdate` from `initLSF oracle C_lsst G₀ ℓ₀ v k`. -/
abbrev LSFInv (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (S : LSFState) : Prop :=
  LSFInvWith (wstrThresh C_lsst S.G₀.n S.k) (6272 * max 1 C_lsst) ℓ₀ S

private lemma R_orig_sub_TV {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInvWith thresh K_σ ℓ₀ S) : S.R_orig ⊆ S.T₀.V :=
  upClosure_subset (hldAuxTree_isRootedTree I.hT₀) I.hR₀_sub

private lemma R_orig_bf {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInvWith thresh K_σ ℓ₀ S) : IsBranchFree S.T₀ S.r₀ S.R_orig :=
  upClosure_isBranchFree I.hT₀ I.hR₀_sub

private lemma r₀_mem_R_orig {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInvWith thresh K_σ ℓ₀ S) : S.r₀ ∈ S.R_orig :=
  subset_upClosure I.hr₀_base

private lemma R_card_eq {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInvWith thresh K_σ ℓ₀ S) :
    S.R.card = S.R_orig.card + S.isolatedVerts.card := by
  have hdisj : Disjoint S.R_orig S.isolatedVerts :=
    Finset.disjoint_left.mpr (fun x hx1 hx2 =>
      Finset.disjoint_left.mp I.hdisj_iso (R_orig_sub_TV I hx1) hx2)
  exact Finset.card_union_of_disjoint hdisj

/-! ## `RootedForest` properties of `S.RF` and stretch preservation -/

lemma LSFInvWith.to_RF_spanning {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInvWith thresh K_σ ℓ₀ S) :
    S.RF.IsRootedSpanningForestOf S.G := by
  let F_orig := forestGivenRoots S.T₀ S.r₀ S.R_orig S.π
  have hRS := forestGivenRoots_isRootedSpanningForest I.hT₀ (R_orig_bf I)
    ⟨S.r₀, r₀_mem_R_orig I⟩ S.π
  have hRF_V : S.RF.F.V = S.G.V := I.hT_cur_V
  have hRF_E : S.RF.F.E = F_orig.E := rfl
  have hRF_val : S.RF.F.IsValid := fun e he =>
    I.hT_cur_forest.1 e (I.hT_cur_E ▸ (Finset.sdiff_subset he))
  have hRF_forest : S.RF.F.IsForest :=
    proj_isForest_of_isForest hRS.1 hRF_val fun e he =>
      ⟨he, I.horig_T e (Finset.sdiff_subset he)⟩
  exact RF_isRootedSpanningForestOf hRS hRF_forest hRF_V hRF_E I.hGV_eq I.hdisj_iso
    (R_orig_sub_TV I) I.horig_id I.horig_split
    (fun e he => I.horig_T e (Finset.sdiff_subset he))
    (fun x hx hxR f hf => I.hunsplit_F x hx hxR f (Finset.sdiff_subset hf))
    I.hF_sub_G

/-! ## Snapshots satisfy `LSF.Holds` -/

private lemma stretch_RF_lt_rawWstr {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInvWith thresh K_σ ℓ₀ S)
    {ℓ : ℕ → ℝ} (_hℓ : ∀ e ∈ S.G.E, 0 < ℓ e)
    (hℓ_orig : ∀ e ∈ S.G₀.E, e ∈ S.G.E → e ∉ S.insertedEdges → ℓ e = ℓ₀ e)
    {e : ℕ} (he : e ∈ S.G.E) (he_ins : e ∉ S.insertedEdges) :
    S.RF.stretch S.G ℓ e ≤ S.wstr e := by
  let F_orig := forestGivenRoots S.T₀ S.r₀ S.R_orig S.π
  have hRS_full := I.to_RF_spanning
  have hse := I.hsurv_edge e he he_ins
  rcases hse with ⟨heG₀, hwstr_e, _, _, hhi_ch⟩
  let raw := levelStretchBound S.T₀ S.r₀ S.π S.G₀ (safeLen S.G₀ ℓ₀) e
  by_cases hth : thresh ≤ raw
  · rw [hwstr_e, ite_eq_left_iff.mpr (fun h => absurd hth h)]
    have hends := hhi_ch hth
    have hgn := I.horig_G_nins e he he_ins
    have htail_R : S.G.tail e ∈ S.R :=
      (origVert_mem_R_iff I.hGV_eq I.hdisj_iso (R_orig_sub_TV I) I.horig_id I.horig_split
        (I.hG_val e he).1).mpr (hgn.1 ▸ hends.1)
    have hhead_R : S.G.head e ∈ S.R :=
      (origVert_mem_R_iff I.hGV_eq I.hdisj_iso (R_orig_sub_TV I) I.horig_id I.horig_split
        (I.hG_val e he).2).mpr (hgn.2 ▸ hends.2)
    rw [rootedForest_stretch_eq_one_of_roots hRS_full ℓ htail_R hhead_R]
  · rw [hwstr_e, ite_eq_right_iff.mpr (fun h => absurd h hth)]
    have hgn := I.horig_G_nins e he he_ins
    have hRF_V : S.RF.F.V = S.G.V := I.hT_cur_V
    have hRF_E : S.RF.F.E = F_orig.E := rfl
    have hst_eq := RF_stretch_eq_orig I.hG₀_val I.hG_val I.hT₀ I.hTV I.hord I.hTG₀ I.hTp₀
      I.hpi_br (R_orig_bf I) (r₀_mem_R_orig I) I.hGV_eq I.hdisj_iso I.horig_id I.horig_split
      hRF_V hRF_E (fun f hf => I.horig_T f (Finset.sdiff_subset hf))
      (fun x hx hxR f hf => I.hunsplit_F x hx hxR f (Finset.sdiff_subset hf))
      I.hF_sub_G hRS_full.1 I.horig_del hℓ_orig he heG₀ he_ins hgn.1 hgn.2
    have hRF_eq : S.RF = { F := S.RF.F, R := S.R_orig ∪ S.isolatedVerts } := rfl
    rw [hRF_eq, hst_eq]
    have hu₀V : S.G₀.tail e ∈ S.T₀.V := I.hTV ▸ (I.hG₀_val e heG₀).1
    have hv₀V : S.G₀.head e ∈ S.T₀.V := I.hTV ▸ (I.hG₀_val e heG₀).2
    exact stretch_le_levelStretchBound I.hT₀ I.hord I.hR₀_sub ⟨S.r₀, I.hr₀_base⟩ hu₀V hv₀V
      (fun f _ => safeLen_nonneg I.hℓ₀ f) (by rw [safeLen_eq_of_mem ℓ₀ heG₀]; exact I.hℓ₀ e heG₀)

lemma LSFInvWith.to_Holds {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInvWith thresh K_σ ℓ₀ S)
    {ℓ : ℕ → ℝ} (hℓ : ∀ e ∈ S.G.E, 0 < ℓ e)
    (hℓ_orig : ∀ e ∈ S.G₀.E, e ∈ S.G.E → e ∉ S.insertedEdges → ℓ e = ℓ₀ e) :
    S.lsf.Holds S.G ℓ (K_σ * S.k * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 6) := by
  have hT_forest : S.T.IsForest := I.hT_cur_forest
  have hRS_full := I.to_RF_spanning
  have hsub_TF : S.T.IsSubgraph S.RF.F :=
    ⟨Finset.Subset.refl _, I.hT_cur_E ▸ Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
  refine ⟨hT_forest, hRS_full, hsub_TF, fun e he => ⟨?_, I.hwstr_bound e he⟩⟩
  by_cases hins : e ∈ S.insertedEdges
  · obtain ⟨hw, ht, hh⟩ := I.hins_wstr e hins
    dsimp only [LSFState.lsf]
    rw [hw, rootedForest_stretch_eq_one_of_roots hRS_full ℓ ht hh]
  · exact stretch_RF_lt_rawWstr I hℓ hℓ_orig he hins

lemma LSFInv.to_Holds {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInv C_lsst ℓ₀ S)
    {ℓ : ℕ → ℝ} (hℓ : ∀ e ∈ S.G.E, 0 < ℓ e)
    (hℓ_orig : ∀ e ∈ S.G₀.E, e ∈ S.G.E → e ∉ S.insertedEdges → ℓ e = ℓ₀ e) :
    S.lsf.Holds S.G ℓ (6272 * max 1 C_lsst * S.k * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 6) :=
  LSFInvWith.to_Holds I hℓ hℓ_orig

/-! ## Initialization preserves invariant and single-update transition -/

lemma initLSF_inv {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ v : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hv : ∀ e ∈ G₀.E, 0 < v e)
    {k : ℝ} (hk : 1 ≤ k) :
    LSFInv C_lsst ℓ₀ (initLSF oracle C_lsst G₀ ℓ₀ v k) := by
  have hsp := initLSF_spec hLSST hG₀ hV₀ hℓ₀ hv hk
  rcases hsp with ⟨hG₀_eq, hG_eq, _, hk_eq, hiso, hins, _, hT_cur_eq, horig_eq,
    hT₀, hTV, hr₀_b, hR₀_sub, hord, hTG₀, hTp₀, hpi_br, hsub₀, _,
    hwstr_bd, hwstr_cs, _, _, hb_W, _, _, hW_pr⟩
  set S₀ := initLSF oracle C_lsst G₀ ℓ₀ v k
  have hsurv : ∀ e ∈ S₀.G.E, e ∉ S₀.insertedEdges →
      e ∈ S₀.G₀.E ∧
      S₀.wstr e = (if wstrThresh C_lsst S₀.G₀.n S₀.k ≤
          levelStretchBound S₀.T₀ S₀.r₀ S₀.π S₀.G₀ (safeLen S₀.G₀ ℓ₀) e
        then 1 else levelStretchBound S₀.T₀ S₀.r₀ S₀.π S₀.G₀ (safeLen S₀.G₀ ℓ₀) e) ∧
      (S₀.G.tail e ≠ S₀.G₀.tail e → S₀.G₀.tail e ∈ S₀.R_orig ∧ S₀.G.tail e ∈ S₀.isolatedVerts) ∧
      (S₀.G.head e ≠ S₀.G₀.head e → S₀.G₀.head e ∈ S₀.R_orig ∧ S₀.G.head e ∈ S₀.isolatedVerts) ∧
      (wstrThresh C_lsst S₀.G₀.n S₀.k ≤
          levelStretchBound S₀.T₀ S₀.r₀ S₀.π S₀.G₀ (safeLen S₀.G₀ ℓ₀) e →
        S₀.G₀.tail e ∈ S₀.R_orig ∧ S₀.G₀.head e ∈ S₀.R_orig) := by
    intro e he _
    have heG₀ : e ∈ G₀.E := hG_eq ▸ he
    refine ⟨hG₀_eq ▸ heG₀, ?_, fun h => absurd (congrArg (fun M => M.tail e) (hG_eq.trans hG₀_eq.symm)) h,
      fun h => absurd (congrArg (fun M => M.head e) (hG_eq.trans hG₀_eq.symm)) h, fun hge => ?_⟩
    · by_cases hth : wstrThresh C_lsst S₀.G₀.n S₀.k ≤
          levelStretchBound S₀.T₀ S₀.r₀ S₀.π S₀.G₀ (safeLen S₀.G₀ ℓ₀) e
      · rw [ite_eq_left_iff.mpr (fun h => absurd hth h)]
        exact (hwstr_cs e heG₀).2 (by simpa only [hG₀_eq, hk_eq] using hth) |>.1
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hth)]
        exact (hwstr_cs e heG₀).1 (not_le.mp (by simpa only [hG₀_eq, hk_eq] using hth))
    · have h2 := (hwstr_cs e heG₀).2 (by simpa only [hG₀_eq, hk_eq] using hge)
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
      hthresh_bd := ⟨wstrThresh_ge_one C_lsst S₀.G₀.n S₀.k,
        wstrThresh_le (hk_eq ▸ hk)⟩
      hdeg_le := fun x _ _ => by rw [hG_eq, hG₀_eq]
      hb_W := hb_W
      hW_props := fun W hW => by
        have hw := hW_pr W hW
        exact ⟨hw.1, hTV ▸ hw.2.1, hw.2.2.1, by simpa only [hG₀_eq, hk_eq] using hw.2.2.2⟩ }

private lemma RF_E_eq (S : LSFState) :
    S.RF.F.E = S.T₀.E \ deletedEdges S.T₀ S.r₀ S.R_orig S.π := rfl

private lemma applyLSFUpdate_fields (S : LSFState) (u : Update) :
    (applyLSFUpdate S u).G = S.G.applyUpdate u ∧
    (applyLSFUpdate S u).G₀ = S.G₀ ∧
    (applyLSFUpdate S u).T₀ = S.T₀ ∧
    (applyLSFUpdate S u).r₀ = S.r₀ ∧
    (applyLSFUpdate S u).TH = S.TH ∧
    (applyLSFUpdate S u).π = S.π ∧
    (applyLSFUpdate S u).k = S.k ∧
    (applyLSFUpdate S u).W_init = S.W_init := by
  cases u <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma upClosure_union_two_card_le {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInvWith thresh K_σ ℓ₀ S) (a b : ℕ) :
    (upClosure (hldAuxTree S.T₀ S.r₀) S.r₀
      (S.R₀_base ∪ ({a, b} : Finset ℕ).filter (fun x => x ∈ S.T₀.V))).card ≤
      S.R_orig.card + 2 * (hldDepthBound S.G₀.n + 1) := by
  let addR := ({a, b} : Finset ℕ).filter (fun x => x ∈ S.T₀.V)
  have hadd_sub : addR ⊆ S.T₀.V := fun _ hx => (Finset.mem_filter.mp hx).2
  have hadd_card : addR.card ≤ 2 :=
    (Finset.card_filter_le _ _).trans ((Finset.card_insert_le _ _).trans (by simp))
  have hun : upClosure (hldAuxTree S.T₀ S.r₀) S.r₀ (S.R₀_base ∪ addR) =
      upClosure (hldAuxTree S.T₀ S.r₀) S.r₀ S.R₀_base ∪
        upClosure (hldAuxTree S.T₀ S.r₀) S.r₀ addR := by
    ext x
    simp only [upClosure, Finset.mem_biUnion, Finset.mem_union]
    exact ⟨fun ⟨y, hy, hx⟩ => hy.elim (fun h => Or.inl ⟨y, h, hx⟩) (fun h => Or.inr ⟨y, h, hx⟩),
      fun h => h.elim (fun ⟨y, hy, hx⟩ => ⟨y, Or.inl hy, hx⟩) (fun ⟨y, hy, hx⟩ => ⟨y, Or.inr hy, hx⟩)⟩
  have h1 := Finset.card_union_le
    (upClosure (hldAuxTree S.T₀ S.r₀) S.r₀ S.R₀_base)
    (upClosure (hldAuxTree S.T₀ S.r₀) S.r₀ addR)
  have h2 := upClosure_union_ancestors_card_le I.hT₀ hadd_sub
  have hT_D_eq : hldDepthBound S.T₀.V.card = hldDepthBound S.G₀.n := by rw [I.hTV]; rfl
  rw [hT_D_eq] at h2
  have hmul : addR.card * (hldDepthBound S.G₀.n + 1) ≤ 2 * (hldDepthBound S.G₀.n + 1) :=
    Nat.mul_le_mul_right _ hadd_card
  have hup : (upClosure (hldAuxTree S.T₀ S.r₀) S.r₀ (S.R₀_base ∪ addR)).card ≤
      S.R_orig.card + addR.card * (hldDepthBound S.G₀.n + 1) := by
    rw [hun]; exact h1.trans (Nat.add_le_add_left h2 _)
  exact hup.trans (Nat.add_le_add_left hmul _)

private lemma applyLSFUpdate_R_orig_sub {S : LSFState} (u : Update) :
    S.R_orig ⊆ (applyLSFUpdate S u).R_orig := by
  have ⟨_, _, _, hr₀', hTH', _, _, _⟩ := applyLSFUpdate_fields S u
  have hR₀_base_sub : S.R₀_base ⊆ (applyLSFUpdate S u).R₀_base := by
    cases u with
    | insert e a b => exact Finset.subset_union_left
    | delete e => exact Finset.subset_union_left
    | split v v' St Sh =>
      dsimp only [applyLSFUpdate]
      split_ifs
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _
  intro x hx
  rw [LSFState.R_orig, hTH', hr₀', mem_upClosure_iff]
  rw [LSFState.R_orig, mem_upClosure_iff] at hx
  obtain ⟨w, hw, haw⟩ := hx
  exact ⟨w, hR₀_base_sub hw, haw⟩

private lemma applyLSFUpdate_R₀_sub {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInvWith thresh K_σ ℓ₀ S) (u : Update) :
    (applyLSFUpdate S u).R₀_base ⊆ S.T₀.V := by
  cases u with
  | insert e a b =>
    dsimp only [applyLSFUpdate]
    exact Finset.union_subset I.hR₀_sub (fun _ hx => (Finset.mem_filter.mp hx).2)
  | delete e =>
    dsimp only [applyLSFUpdate]
    exact Finset.union_subset I.hR₀_sub (fun _ hx => (Finset.mem_filter.mp hx).2)
  | split v v' St Sh =>
    dsimp only [applyLSFUpdate]
    split_ifs with hv
    · exact Finset.insert_subset_iff.mpr ⟨hv, I.hR₀_sub⟩
    · exact I.hR₀_sub

private lemma applyLSFUpdate_RF_E {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInvWith thresh K_σ ℓ₀ S) (u : Update) :
    (applyLSFUpdate S u).RF.F.E ⊆ S.RF.F.E := by
  have ⟨_, _, hT₀', hr₀', hTH', hπ', _, _⟩ := applyLSFUpdate_fields S u
  have hS_TH : S.TH = hldAuxTree S.T₀ S.r₀ := rfl
  have hR₀'_T : (applyLSFUpdate S u).R₀_base ⊆ S.T₀.V := applyLSFUpdate_R₀_sub I u
  have hbf1 := R_orig_bf I
  have hR_orig'_eq : (applyLSFUpdate S u).R_orig =
      upClosure (hldAuxTree S.T₀ S.r₀) S.r₀ (applyLSFUpdate S u).R₀_base := by
    rw [LSFState.R_orig, hTH', hr₀', hS_TH]
  have hbf2 : IsBranchFree S.T₀ S.r₀ (applyLSFUpdate S u).R_orig := by
    rw [hR_orig'_eq]; exact upClosure_isBranchFree I.hT₀ hR₀'_T
  have hdel := deletedEdges_mono I.hT₀ hbf1 hbf2 ⟨S.r₀, r₀_mem_R_orig I⟩
    (applyLSFUpdate_R_orig_sub u) S.π I.hord
  rw [RF_E_eq, RF_E_eq, hT₀', hr₀', hπ']
  exact Finset.sdiff_subset_sdiff Finset.Subset.rfl hdel

private lemma applyLSFUpdate_hins_wstr {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInvWith thresh K_σ ℓ₀ S) {u : Update} (hu : S.G.UpdateIsValid u)
    (hR_sub : S.R ⊆ (applyLSFUpdate S u).R) :
    ∀ e ∈ (applyLSFUpdate S u).insertedEdges,
      (applyLSFUpdate S u).wstr e = 1 ∧
      (applyLSFUpdate S u).G.tail e ∈ (applyLSFUpdate S u).R ∧
      (applyLSFUpdate S u).G.head e ∈ (applyLSFUpdate S u).R := by
  cases u with
  | insert e_new a b =>
    intro f hf
    dsimp only [applyLSFUpdate] at hf
    rw [Finset.mem_insert] at hf
    rcases hf with rfl | hf_old
    · refine ⟨Function.update_self _ _ S.wstr, ?_, ?_⟩
      · dsimp only [applyLSFUpdate, MGraph.applyUpdate]
        rw [Function.update_self]
        have haV : a ∈ S.T₀.V ∪ S.isolatedVerts := I.hGV_eq ▸ hu.2.1
        rw [Finset.mem_union] at haV
        rcases haV with haT | haI
        · exact Finset.mem_union_left _ (subset_upClosure (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, haT⟩)))
        · exact Finset.mem_union_right _ haI
      · dsimp only [applyLSFUpdate, MGraph.applyUpdate]
        rw [Function.update_self]
        have hbV : b ∈ S.T₀.V ∪ S.isolatedVerts := I.hGV_eq ▸ hu.2.2
        rw [Finset.mem_union] at hbV
        rcases hbV with hbT | hbI
        · exact Finset.mem_union_left _ (subset_upClosure (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hbT⟩)))
        · exact Finset.mem_union_right _ hbI
    · have hne : f ≠ e_new := fun h => hu.1 (h ▸ I.hins_sub hf_old)
      have hold := I.hins_wstr f hf_old
      dsimp only [applyLSFUpdate, MGraph.applyUpdate]
      rw [Function.update_of_ne hne, Function.update_of_ne hne, Function.update_of_ne hne]
      exact ⟨hold.1, hR_sub hold.2.1, hR_sub hold.2.2⟩
  | delete e_del =>
    intro f hf
    dsimp only [applyLSFUpdate] at hf
    have hold := I.hins_wstr f (Finset.mem_erase.mp hf).2
    exact ⟨hold.1, hR_sub hold.2.1, hR_sub hold.2.2⟩
  | split v v' St Sh =>
    intro f hf
    have hold := I.hins_wstr f hf
    refine ⟨hold.1, ?_, ?_⟩
    · by_cases hc : f ∈ St ∧ S.G.tail f = v
      · have htl : (applyLSFUpdate S (.split v v' St Sh)).G.tail f = v' := by
          dsimp only [applyLSFUpdate, MGraph.applyUpdate]; exact ite_eq_left hc
        rw [htl]
        exact Finset.mem_union_right _ (by dsimp only [applyLSFUpdate]; exact Finset.mem_insert_self _ _)
      · have htl : (applyLSFUpdate S (.split v v' St Sh)).G.tail f = S.G.tail f := by
          dsimp only [applyLSFUpdate, MGraph.applyUpdate]; exact ite_eq_right hc
        rw [htl]; exact hR_sub hold.2.1
    · by_cases hc : f ∈ Sh ∧ S.G.head f = v
      · have hhd : (applyLSFUpdate S (.split v v' St Sh)).G.head f = v' := by
          dsimp only [applyLSFUpdate, MGraph.applyUpdate]; exact ite_eq_left hc
        rw [hhd]
        exact Finset.mem_union_right _ (by dsimp only [applyLSFUpdate]; exact Finset.mem_insert_self _ _)
      · have hhd : (applyLSFUpdate S (.split v v' St Sh)).G.head f = S.G.head f := by
          dsimp only [applyLSFUpdate, MGraph.applyUpdate]; exact ite_eq_right hc
        rw [hhd]; exact hR_sub hold.2.2

private lemma applyLSFUpdate_horig_del {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInvWith thresh K_σ ℓ₀ S) {u : Update} (hu : S.G.UpdateIsValid u) :
    ∀ e ∈ (applyLSFUpdate S u).G₀.E,
      (e ∈ (applyLSFUpdate S u).G.E ∧ e ∉ (applyLSFUpdate S u).insertedEdges) ∨
      ((applyLSFUpdate S u).G₀.tail e ∈ (applyLSFUpdate S u).R_orig ∧
        (applyLSFUpdate S u).G₀.head e ∈ (applyLSFUpdate S u).R_orig) := by
  have ⟨_, hG₀', _, _, _, _, _, _⟩ := applyLSFUpdate_fields S u
  have hR_orig_sub := applyLSFUpdate_R_orig_sub (S := S) u
  rw [hG₀']
  intro e he
  rcases I.horig_del e he with ⟨heG, he_nins⟩ | ⟨ht, hh⟩
  · cases u with
    | insert e_new a b =>
      have hne : e ≠ e_new := fun h => hu.1 (h ▸ heG)
      left
      dsimp only [applyLSFUpdate, MGraph.applyUpdate]
      exact ⟨Finset.mem_insert_of_mem heG, fun h => by
        rw [Finset.mem_insert] at h; exact he_nins (h.resolve_left hne)⟩
    | delete e_del =>
      by_cases hed : e = e_del
      · subst hed
        right
        have hgn := I.horig_G_nins e heG he_nins
        have htV : S.G₀.tail e ∈ S.T₀.V := I.hTV ▸ (I.hG₀_val e he).1
        have hhV : S.G₀.head e ∈ S.T₀.V := I.hTV ▸ (I.hG₀_val e he).2
        refine ⟨subset_upClosure (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_, htV⟩)),
          subset_upClosure (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_, hhV⟩))⟩
        · rw [← hgn.1]; exact Finset.mem_insert_self _ _
        · rw [← hgn.2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · left
        dsimp only [applyLSFUpdate, MGraph.applyUpdate]
        exact ⟨Finset.mem_erase.mpr ⟨hed, heG⟩, fun h => he_nins (Finset.mem_erase.mp h).2⟩
    | split _ _ _ _ => exact Or.inl ⟨heG, he_nins⟩
  · exact Or.inr ⟨hR_orig_sub ht, hR_orig_sub hh⟩

private lemma applyLSFUpdate_hsurv {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInvWith thresh K_σ ℓ₀ S) (u : Update) :
    ∀ e ∈ (applyLSFUpdate S u).G.E, e ∉ (applyLSFUpdate S u).insertedEdges →
      e ∈ (applyLSFUpdate S u).G₀.E ∧
      (applyLSFUpdate S u).wstr e =
        (if thresh ≤
            levelStretchBound (applyLSFUpdate S u).T₀ (applyLSFUpdate S u).r₀
              (applyLSFUpdate S u).π (applyLSFUpdate S u).G₀
              (safeLen (applyLSFUpdate S u).G₀ ℓ₀) e
          then 1
          else levelStretchBound (applyLSFUpdate S u).T₀ (applyLSFUpdate S u).r₀
            (applyLSFUpdate S u).π (applyLSFUpdate S u).G₀
            (safeLen (applyLSFUpdate S u).G₀ ℓ₀) e) ∧
      ((applyLSFUpdate S u).G.tail e ≠ (applyLSFUpdate S u).G₀.tail e →
        (applyLSFUpdate S u).G₀.tail e ∈ (applyLSFUpdate S u).R_orig ∧
        (applyLSFUpdate S u).G.tail e ∈ (applyLSFUpdate S u).isolatedVerts) ∧
      ((applyLSFUpdate S u).G.head e ≠ (applyLSFUpdate S u).G₀.head e →
        (applyLSFUpdate S u).G₀.head e ∈ (applyLSFUpdate S u).R_orig ∧
        (applyLSFUpdate S u).G.head e ∈ (applyLSFUpdate S u).isolatedVerts) ∧
      (thresh ≤
          levelStretchBound (applyLSFUpdate S u).T₀ (applyLSFUpdate S u).r₀
            (applyLSFUpdate S u).π (applyLSFUpdate S u).G₀
            (safeLen (applyLSFUpdate S u).G₀ ℓ₀) e →
        (applyLSFUpdate S u).G₀.tail e ∈ (applyLSFUpdate S u).R_orig ∧
        (applyLSFUpdate S u).G₀.head e ∈ (applyLSFUpdate S u).R_orig) := by
  have ⟨_, hG₀', hT₀', hr₀', _, hπ', _, _⟩ := applyLSFUpdate_fields S u
  have hR_orig_sub := applyLSFUpdate_R_orig_sub (S := S) u
  rw [hG₀', hT₀', hr₀', hπ']
  intro e he he_nins
  cases u with
  | insert e_new a b =>
    dsimp only [applyLSFUpdate, MGraph.applyUpdate] at he he_nins ⊢
    have hne : e ≠ e_new := fun h => he_nins (h ▸ Finset.mem_insert_self _ _)
    have he_old : e ∈ S.G.E := (Finset.mem_insert.mp he).resolve_left hne
    have he_old_ni : e ∉ S.insertedEdges := fun h => he_nins (Finset.mem_insert_of_mem h)
    have hold := I.hsurv_edge e he_old he_old_ni
    rw [Function.update_of_ne hne, Function.update_of_ne hne, Function.update_of_ne hne]
    exact ⟨hold.1, hold.2.1,
      fun h => ⟨hR_orig_sub (hold.2.2.1 h).1, (hold.2.2.1 h).2⟩,
      fun h => ⟨hR_orig_sub (hold.2.2.2.1 h).1, (hold.2.2.2.1 h).2⟩,
      fun h => ⟨hR_orig_sub (hold.2.2.2.2 h).1, hR_orig_sub (hold.2.2.2.2 h).2⟩⟩
  | delete e_del =>
    dsimp only [applyLSFUpdate, MGraph.applyUpdate] at he he_nins ⊢
    have hne : e ≠ e_del := (Finset.mem_erase.mp he).1
    have he_old : e ∈ S.G.E := (Finset.mem_erase.mp he).2
    have he_old_ni : e ∉ S.insertedEdges := fun h => he_nins (Finset.mem_erase.mpr ⟨hne, h⟩)
    have hold := I.hsurv_edge e he_old he_old_ni
    exact ⟨hold.1, hold.2.1,
      fun h => ⟨hR_orig_sub (hold.2.2.1 h).1, (hold.2.2.1 h).2⟩,
      fun h => ⟨hR_orig_sub (hold.2.2.2.1 h).1, (hold.2.2.2.1 h).2⟩,
      fun h => ⟨hR_orig_sub (hold.2.2.2.2 h).1, hR_orig_sub (hold.2.2.2.2 h).2⟩⟩
  | split v v' St Sh =>
    have hold := I.hsurv_edge e he he_nins
    have hgn := I.horig_G_nins e he he_nins
    refine ⟨hold.1, hold.2.1, ?_, ?_, fun h => ⟨hR_orig_sub (hold.2.2.2.2 h).1,
      hR_orig_sub (hold.2.2.2.2 h).2⟩⟩
    · intro hne
      by_cases hcond : e ∈ St ∧ S.G.tail e = v
      · have htl : (applyLSFUpdate S (.split v v' St Sh)).G.tail e = v' := by
          dsimp only [applyLSFUpdate, MGraph.applyUpdate]; exact ite_eq_left hcond
        rw [htl]
        refine ⟨?_, by dsimp only [applyLSFUpdate]; exact Finset.mem_insert_self _ _⟩
        have hv₀ : S.origVert v = S.G₀.tail e := hcond.2.symm ▸ hgn.1
        have hvT : S.origVert v ∈ S.T₀.V := hv₀ ▸ I.hTV ▸ (I.hG₀_val e hold.1).1
        refine subset_upClosure ?_
        dsimp only [applyLSFUpdate]
        rw [ite_eq_left hvT, ← hv₀]
        exact Finset.mem_insert_self _ _
      · have htl : (applyLSFUpdate S (.split v v' St Sh)).G.tail e = S.G.tail e := by
          dsimp only [applyLSFUpdate, MGraph.applyUpdate]; exact ite_eq_right hcond
        rw [htl] at hne ⊢
        refine ⟨hR_orig_sub (hold.2.2.1 hne).1, ?_⟩
        dsimp only [applyLSFUpdate]
        exact Finset.mem_insert_of_mem (hold.2.2.1 hne).2
    · intro hne
      by_cases hcond : e ∈ Sh ∧ S.G.head e = v
      · have hhd : (applyLSFUpdate S (.split v v' St Sh)).G.head e = v' := by
          dsimp only [applyLSFUpdate, MGraph.applyUpdate]; exact ite_eq_left hcond
        rw [hhd]
        refine ⟨?_, by dsimp only [applyLSFUpdate]; exact Finset.mem_insert_self _ _⟩
        have hv₀ : S.origVert v = S.G₀.head e := hcond.2.symm ▸ hgn.2
        have hvT : S.origVert v ∈ S.T₀.V := hv₀ ▸ I.hTV ▸ (I.hG₀_val e hold.1).2
        refine subset_upClosure ?_
        dsimp only [applyLSFUpdate]
        rw [ite_eq_left hvT, ← hv₀]
        exact Finset.mem_insert_self _ _
      · have hhd : (applyLSFUpdate S (.split v v' St Sh)).G.head e = S.G.head e := by
          dsimp only [applyLSFUpdate, MGraph.applyUpdate]; exact ite_eq_right hcond
        rw [hhd] at hne ⊢
        refine ⟨hR_orig_sub (hold.2.2.2.1 hne).1, ?_⟩
        dsimp only [applyLSFUpdate]
        exact Finset.mem_insert_of_mem (hold.2.2.2.1 hne).2

lemma applyLSFUpdate_inv_with {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInvWith thresh K_σ ℓ₀ S) {u : Update} (hu : S.G.UpdateIsValid u) :
    let S' := applyLSFUpdate S u
    LSFInvWith thresh K_σ ℓ₀ S' ∧
    S'.G = S.G.applyUpdate u ∧
    S'.G₀ = S.G₀ ∧ S'.T₀ = S.T₀ ∧ S'.r₀ = S.r₀ ∧ S'.π = S.π ∧ S'.k = S.k ∧
    S'.W_init = S.W_init ∧
    S.R ⊆ S'.R ∧
    S'.RF.F.E ⊆ S.RF.F.E ∧
    (S'.R.card : ℝ) ≤ (S.R.card : ℝ) + 56 * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 2 := by
  classical
  intro S'
  have ⟨hG', hG₀', hT₀', hr₀', hTH', hπ', hk', hW'⟩ := applyLSFUpdate_fields S u
  have horig_mem_TV : ∀ x ∈ S.G.V, S.origVert x ∈ S.T₀.V := by
    intro x hx
    rw [I.hGV_eq, Finset.mem_union] at hx
    rcases hx with h | h
    · rw [I.horig_id x h]; exact h
    · exact R_orig_sub_TV I (I.horig_split x h)
  have hD_le : ((hldDepthBound S.G₀.n + 1 : ℕ) : ℝ) ≤ 28 * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 2 :=
    hldDepthBound_add_one_le S.G₀.n
  have hT_D_eq : hldDepthBound S.T₀.V.card = hldDepthBound S.G₀.n := by
    rw [I.hTV]; rfl
  have hR₀_base_sub : S.R₀_base ⊆ S'.R₀_base := by
    cases u with
    | insert e a b => exact Finset.subset_union_left
    | delete e => exact Finset.subset_union_left
    | split v v' St Sh =>
      dsimp only [S', applyLSFUpdate]
      split_ifs
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _
  have hR_orig_sub : S.R_orig ⊆ S'.R_orig := applyLSFUpdate_R_orig_sub u
  have hiso_sub : S.isolatedVerts ⊆ S'.isolatedVerts := by
    cases u with
    | insert _ _ _ => exact Finset.Subset.refl _
    | delete _ => exact Finset.Subset.refl _
    | split _ v' _ _ => exact Finset.subset_insert _ _
  have hR_sub : S.R ⊆ S'.R := Finset.union_subset_union hR_orig_sub hiso_sub
  have hR₀'_sub : S'.R₀_base ⊆ S'.T₀.V := by
    rw [hT₀']; exact applyLSFUpdate_R₀_sub I u
  have hdisj' : Disjoint S'.T₀.V S'.isolatedVerts := by
    rw [hT₀']
    cases u with
    | insert _ _ _ => exact I.hdisj_iso
    | delete _ => exact I.hdisj_iso
    | split v v' St Sh =>
      rw [Finset.disjoint_left]
      intro x hxT hxI
      dsimp only [S', applyLSFUpdate] at hxI
      rw [Finset.mem_insert] at hxI
      rcases hxI with rfl | hx_old
      · exact hu.2.1 (I.hGV_eq ▸ Finset.mem_union_left _ hxT)
      · exact Finset.disjoint_left.mp I.hdisj_iso hxT hx_old
  have hGV' : S'.G.V = S'.T₀.V ∪ S'.isolatedVerts := by
    rw [hT₀']
    cases u with
    | insert _ _ _ => exact I.hGV_eq
    | delete _ => exact I.hGV_eq
    | split v v' St Sh =>
      dsimp only [S', applyLSFUpdate, MGraph.applyUpdate]
      rw [I.hGV_eq]
      ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
  have hdeg' : ∀ x ∈ S'.T₀.V, x ∉ S'.R → S'.G.deg x ≤ S'.G₀.deg x := by
    intro x hxT hxR
    rw [hT₀'] at hxT
    rw [hG', hG₀']
    have hx_old : x ∉ S.R := fun h => hxR (hR_sub h)
    refine (deg_le_of_update S.G u ?_).trans (I.hdeg_le x hxT hx_old)
    cases u with
    | insert e a b =>
      constructor
      · intro hEq; apply hxR; subst hEq
        exact Finset.mem_union_left _ (subset_upClosure (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hxT⟩)))
      · intro hEq; apply hxR; subst hEq
        exact Finset.mem_union_left _ (subset_upClosure (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hxT⟩)))
    | delete e => exact trivial
    | split v v' St Sh =>
      constructor
      · intro hEq; apply hxR; rw [hEq]
        change v ∈ S'.R_orig ∪ S'.isolatedVerts
        refine Finset.mem_union_left _ (subset_upClosure ?_)
        change v ∈ (applyLSFUpdate S (.split v v' St Sh)).R₀_base
        dsimp only [applyLSFUpdate]
        rw [ite_eq_left (by rw [← hEq, I.horig_id x hxT]; exact hxT), ← hEq, I.horig_id x hxT]
        exact Finset.mem_insert_self _ _
      · intro hEq; apply hxR; rw [hEq]
        exact Finset.mem_union_right _ (by dsimp only [S', applyLSFUpdate]; exact Finset.mem_insert_self _ _)
  have hF_sub : S'.RF.F.E ⊆ S.RF.F.E := applyLSFUpdate_RF_E I u
  have hcard_R' : (S'.R.card : ℝ) ≤ (S.R.card : ℝ) + 56 * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 2 := by
    have hdisj_S' : Disjoint S'.R_orig S'.isolatedVerts := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have hS_TH : S.TH = hldAuxTree S.T₀ S.r₀ := rfl
      have hx1T : x ∈ S'.T₀.V := by
        rw [hT₀']
        rw [LSFState.R_orig, hTH', hr₀', hS_TH] at hx1
        exact upClosure_subset (hldAuxTree_isRootedTree I.hT₀) (applyLSFUpdate_R₀_sub I u) hx1
      exact Finset.disjoint_left.mp hdisj' hx1T hx2
    have hR'_eq : S'.R.card = S'.R_orig.card + S'.isolatedVerts.card :=
      Finset.card_union_of_disjoint hdisj_S'
    have hR_eq : S.R.card = S.R_orig.card + S.isolatedVerts.card := R_card_eq I
    have h_nat : S'.R.card ≤ S.R.card + 2 * (hldDepthBound S.G₀.n + 1) := by
      rw [hR'_eq, hR_eq]
      cases u with
      | insert e a b =>
        have hup : S'.R_orig.card ≤ S.R_orig.card + 2 * (hldDepthBound S.G₀.n + 1) :=
          upClosure_union_two_card_le I a b
        change S'.R_orig.card + S.isolatedVerts.card ≤ _
        omega
      | delete e =>
        have hup : S'.R_orig.card ≤ S.R_orig.card + 2 * (hldDepthBound S.G₀.n + 1) :=
          upClosure_union_two_card_le I (S.origVert (S.G.tail e)) (S.origVert (S.G.head e))
        change S'.R_orig.card + S.isolatedVerts.card ≤ _
        omega
      | split v v' St Sh =>
        have hup : S'.R_orig.card ≤ S.R_orig.card + (hldDepthBound S.G₀.n + 1) := by
          change (upClosure (hldAuxTree S.T₀ S.r₀) S.r₀
            (if S.origVert v ∈ S.T₀.V then insert (S.origVert v) S.R₀_base else S.R₀_base)).card ≤ _
          split_ifs with hv
          · have h2 := upClosure_insert_card_le I.hT₀ hv S.R₀_base
            rwa [hT_D_eq] at h2
          · exact Nat.le_add_right _ _
        have hiso_c : (insert v' S.isolatedVerts).card ≤ S.isolatedVerts.card + 1 :=
          Finset.card_insert_le _ _
        have h1le : 1 ≤ hldDepthBound S.G₀.n + 1 := Nat.succ_pos _
        change S'.R_orig.card + (insert v' S.isolatedVerts).card ≤ _
        omega
    have h_real : (S'.R.card : ℝ) ≤ (S.R.card : ℝ) + 2 * ((hldDepthBound S.G₀.n + 1 : ℕ) : ℝ) := by
      exact_mod_cast h_nat
    have h2D := mul_le_mul_of_nonneg_left hD_le zero_le_two
    linarith
  have hins_sub' : S'.insertedEdges ⊆ S'.G.E := by
    cases u with
    | insert e a b =>
      intro f hf
      dsimp only [S', applyLSFUpdate, MGraph.applyUpdate] at hf ⊢
      rw [Finset.mem_insert] at hf ⊢
      exact hf.imp id (fun h => I.hins_sub h)
    | delete e =>
      intro f hf
      dsimp only [S', applyLSFUpdate, MGraph.applyUpdate] at hf ⊢
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hf).1, I.hins_sub (Finset.mem_erase.mp hf).2⟩
    | split _ _ _ _ => exact I.hins_sub
  have hins_wstr' : ∀ e ∈ S'.insertedEdges,
      S'.wstr e = 1 ∧ S'.G.tail e ∈ S'.R ∧ S'.G.head e ∈ S'.R :=
    applyLSFUpdate_hins_wstr I hu hR_sub
  have horig_del' : ∀ e ∈ S'.G₀.E,
      (e ∈ S'.G.E ∧ e ∉ S'.insertedEdges) ∨ (S'.G₀.tail e ∈ S'.R_orig ∧ S'.G₀.head e ∈ S'.R_orig) :=
    applyLSFUpdate_horig_del I hu
  have hsurv' := applyLSFUpdate_hsurv I u
  have hwstr_bound' : ∀ e ∈ S'.G.E,
      S'.wstr e ≤ K_σ * S'.k * (Real.log ((S'.G₀.n : ℝ) + 2)) ^ 6 := by
    rw [hk', hG₀']
    intro e he
    cases u with
    | insert e_new a b =>
      by_cases heq : e = e_new
      · subst heq
        have h1 : S'.wstr e = 1 := Function.update_self _ _ S.wstr
        rw [h1]
        exact I.hthresh_bd.1.trans I.hthresh_bd.2
      · dsimp only [S', applyLSFUpdate, MGraph.applyUpdate] at he ⊢
        rw [Function.update_of_ne heq]
        exact I.hwstr_bound e ((Finset.mem_insert.mp he).resolve_left heq)
    | delete e_del =>
      exact I.hwstr_bound e (Finset.erase_subset _ _ he)
    | split _ _ _ _ => exact I.hwstr_bound e he
  have hT_cur_forest' : S'.T_cur.IsForest := by
    cases u with
    | insert _ _ _ => exact I.hT_cur_forest
    | delete _ => exact I.hT_cur_forest
    | split v v' St Sh =>
      exact applyUpdate_split_isForest I.hT_cur_forest (I.hT_cur_V ▸ hu.1) (I.hT_cur_V ▸ hu.2.1) St Sh
  have hT_cur_V' : S'.T_cur.V = S'.G.V := by
    cases u with
    | insert _ _ _ => exact I.hT_cur_V
    | delete _ => exact I.hT_cur_V
    | split v v' St Sh => dsimp only [S', applyLSFUpdate, MGraph.applyUpdate]; rw [I.hT_cur_V]
  have hT_cur_E' : S'.T_cur.E = S'.T₀.E := by cases u <;> exact I.hT_cur_E
  have horig_id' : ∀ x ∈ S'.T₀.V, S'.origVert x = x := by
    rw [hT₀']
    intro x hx
    cases u with
    | insert _ _ _ => exact I.horig_id x hx
    | delete _ => exact I.horig_id x hx
    | split v v' St Sh =>
      have hne : x ≠ v' := fun h => hu.2.1 (I.hGV_eq ▸ Finset.mem_union_left _ (h ▸ hx))
      dsimp only [S', applyLSFUpdate]
      rw [Function.update_of_ne hne]
      exact I.horig_id x hx
  have horig_split' : ∀ x ∈ S'.isolatedVerts, S'.origVert x ∈ S'.R_orig := by
    intro x hx
    cases u with
    | insert _ _ _ => exact hR_orig_sub (I.horig_split x hx)
    | delete _ => exact hR_orig_sub (I.horig_split x hx)
    | split v v' St Sh =>
      dsimp only [S', applyLSFUpdate] at hx ⊢
      have hv_origT : S.origVert v ∈ S.T₀.V := horig_mem_TV v hu.1
      have hv_origR' : S.origVert v ∈ S'.R_orig := by
        refine subset_upClosure ?_
        dsimp only [S', applyLSFUpdate]
        rw [ite_eq_left hv_origT]
        exact Finset.mem_insert_self _ _
      rw [Finset.mem_insert] at hx
      rcases hx with hxv | hx_old
      · rw [hxv, Function.update_self]
        exact hv_origR'
      · have hne : x ≠ v' := fun h => hu.2.1 (I.hGV_eq ▸ Finset.mem_union_right _ (h ▸ hx_old))
        rw [Function.update_of_ne hne]
        exact hR_orig_sub (I.horig_split x hx_old)
  have horig_T' : ∀ e ∈ S'.T₀.E,
      S'.origVert (S'.T_cur.tail e) = S'.T₀.tail e ∧
      S'.origVert (S'.T_cur.head e) = S'.T₀.head e := by
    rw [hT₀']
    intro e he
    have hec := I.hT_cur_forest.1 e (I.hT_cur_E ▸ he)
    have horig_old := I.horig_T e he
    cases u with
    | insert _ _ _ => exact horig_old
    | delete _ => exact horig_old
    | split v v' St Sh =>
      dsimp only [S', applyLSFUpdate, MGraph.applyUpdate]
      refine ⟨?_, ?_⟩
      · by_cases ht : e ∈ St ∧ S.T_cur.tail e = v
        · rw [ite_eq_left ht, Function.update_self, ← ht.2]; exact horig_old.1
        · have hne : S.T_cur.tail e ≠ v' := fun h => hu.2.1 (I.hT_cur_V ▸ (h ▸ hec.1))
          rw [ite_eq_right ht, Function.update_of_ne hne]; exact horig_old.1
      · by_cases hh : e ∈ Sh ∧ S.T_cur.head e = v
        · rw [ite_eq_left hh, Function.update_self, ← hh.2]; exact horig_old.2
        · have hne : S.T_cur.head e ≠ v' := fun h => hu.2.1 (I.hT_cur_V ▸ (h ▸ hec.2))
          rw [ite_eq_right hh, Function.update_of_ne hne]; exact horig_old.2
  have horig_G_nins' : ∀ e ∈ S'.G.E, e ∉ S'.insertedEdges →
      S'.origVert (S'.G.tail e) = S'.G₀.tail e ∧
      S'.origVert (S'.G.head e) = S'.G₀.head e := by
    rw [hG₀']
    intro e he he_nins
    cases u with
    | insert e_new a b =>
      dsimp only [S', applyLSFUpdate, MGraph.applyUpdate] at he he_nins ⊢
      have hne : e ≠ e_new := fun h => he_nins (h ▸ Finset.mem_insert_self _ _)
      have he_old : e ∈ S.G.E := (Finset.mem_insert.mp he).resolve_left hne
      have he_old_ni : e ∉ S.insertedEdges := fun h => he_nins (Finset.mem_insert_of_mem h)
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
      exact I.horig_G_nins e he_old he_old_ni
    | delete e_del =>
      dsimp only [S', applyLSFUpdate, MGraph.applyUpdate] at he he_nins ⊢
      have hne : e ≠ e_del := (Finset.mem_erase.mp he).1
      have he_old : e ∈ S.G.E := (Finset.mem_erase.mp he).2
      have he_old_ni : e ∉ S.insertedEdges := fun h => he_nins (Finset.mem_erase.mpr ⟨hne, h⟩)
      exact I.horig_G_nins e he_old he_old_ni
    | split v v' St Sh =>
      have hec := I.hG_val e he
      have horig_old := I.horig_G_nins e he he_nins
      dsimp only [S', applyLSFUpdate, MGraph.applyUpdate]
      refine ⟨?_, ?_⟩
      · by_cases ht : e ∈ St ∧ S.G.tail e = v
        · rw [ite_eq_left ht, Function.update_self, ← ht.2]; exact horig_old.1
        · have hne : S.G.tail e ≠ v' := fun h => hu.2.1 (h ▸ hec.1)
          rw [ite_eq_right ht, Function.update_of_ne hne]; exact horig_old.1
      · by_cases hh : e ∈ Sh ∧ S.G.head e = v
        · rw [ite_eq_left hh, Function.update_self, ← hh.2]; exact horig_old.2
        · have hne : S.G.head e ≠ v' := fun h => hu.2.1 (h ▸ hec.2)
          rw [ite_eq_right hh, Function.update_of_ne hne]; exact horig_old.2
  have hunsplit_F' : ∀ x ∈ S'.G.V, S'.origVert x ∉ S'.R_orig → ∀ f ∈ S'.T₀.E,
      (S'.T₀.tail f = S'.origVert x → S'.T_cur.tail f = x) ∧
      (S'.T₀.head f = S'.origVert x → S'.T_cur.head f = x) := by
    rw [hT₀']
    intro x hx hxR f hf
    cases u with
    | insert _ _ _ =>
      exact I.hunsplit_F x hx (fun h => hxR (hR_orig_sub h)) f hf
    | delete _ =>
      exact I.hunsplit_F x hx (fun h => hxR (hR_orig_sub h)) f hf
    | split v v' St Sh =>
      have hv_origT : S.origVert v ∈ S.T₀.V := horig_mem_TV v hu.1
      have hv_origR' : S.origVert v ∈ S'.R_orig := by
        refine subset_upClosure ?_
        dsimp only [S', applyLSFUpdate]
        rw [ite_eq_left hv_origT]
        exact Finset.mem_insert_self _ _
      have hx_ne_v' : x ≠ v' := fun h => by
        subst h
        dsimp only [S', applyLSFUpdate] at hxR
        rw [Function.update_self] at hxR
        exact hxR hv_origR'
      have hx_oldG : x ∈ S.G.V := by
        dsimp only [S', applyLSFUpdate, MGraph.applyUpdate] at hx
        exact (Finset.mem_insert.mp hx).resolve_left hx_ne_v'
      have hx_orig_eq : S'.origVert x = S.origVert x := by
        dsimp only [S', applyLSFUpdate]
        exact Function.update_of_ne hx_ne_v' (S.origVert v) S.origVert
      rw [hx_orig_eq] at hxR ⊢
      have hx_old := I.hunsplit_F x hx_oldG (fun h => hxR (hR_orig_sub h)) f hf
      have hx_ne_v : x ≠ v := fun h => by
        subst h; exact hxR hv_origR'
      dsimp only [S', applyLSFUpdate, MGraph.applyUpdate]
      refine ⟨fun ht => ?_, fun hh => ?_⟩
      · have hcur := hx_old.1 ht
        rw [ite_eq_right (fun hc => hx_ne_v (hcur ▸ hc.2))]
        exact hcur
      · have hcur := hx_old.2 hh
        rw [ite_eq_right (fun hc => hx_ne_v (hcur ▸ hc.2))]
        exact hcur
  have hF_sub_G' : S'.G.IsSubgraph S'.RF.F := by
    refine ⟨(hT_cur_V').subset, fun f hf => ?_, fun f hf => ?_⟩
    · have hf_old := hF_sub hf
      have hfG_old := I.hF_sub_G.2.1 hf_old
      cases u with
      | insert e_new a b =>
        dsimp only [S', applyLSFUpdate, MGraph.applyUpdate]
        exact Finset.mem_insert_of_mem hfG_old
      | delete e_del =>
        dsimp only [S', applyLSFUpdate, MGraph.applyUpdate]
        refine Finset.mem_erase.mpr ⟨fun hfe => ?_, hfG_old⟩
        subst hfe
        have hfT : f ∈ S.T₀.E := Finset.sdiff_subset hf
        have horig_f := I.horig_T f hfT
        have hfg : S.T_cur.tail f = S.G.tail f ∧ S.T_cur.head f = S.G.head f :=
          I.hF_sub_G.2.2 f hf_old
        have hu₀V : S.T₀.tail f ∈ S.T₀.V := (I.hT₀.isForest.1 f hfT).1
        have hv₀V : S.T₀.head f ∈ S.T₀.V := (I.hT₀.isForest.1 f hfT).2
        have hS_TH : S.TH = hldAuxTree S.T₀ S.r₀ := rfl
        have hbf' : IsBranchFree S.T₀ S.r₀ S'.R_orig := by
          rw [LSFState.R_orig, hTH', hr₀', hS_TH]
          exact upClosure_isBranchFree I.hT₀ (hT₀' ▸ hR₀'_sub)
        have hr₀_mem' : S.r₀ ∈ S'.R_orig :=
          hR_orig_sub (r₀_mem_R_orig I)
        have hRS' := forestGivenRoots_isRootedSpanningForest I.hT₀ hbf' ⟨S.r₀, hr₀_mem'⟩ S.π
        have hu₀R : S.T₀.tail f ∈ S'.R_orig := by
          rw [← horig_f.1, hfg.1]
          refine subset_upClosure (Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Finset.mem_insert_self _ _, ?_⟩))
          rw [← hfg.1, horig_f.1]; exact hu₀V
        have hv₀R : S.T₀.head f ∈ S'.R_orig := by
          rw [← horig_f.2, hfg.2]
          refine subset_upClosure (Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩))
          rw [← hfg.2, horig_f.2]; exact hv₀V
        have hf_orig : f ∈ (forestGivenRoots S.T₀ S.r₀ S'.R_orig S.π).E := by
          have hf' : f ∈ (forestGivenRoots S'.T₀ S'.r₀ S'.R_orig S'.π).E := hf
          rwa [hT₀', hr₀', hπ'] at hf'
        exact rf_edge_not_both_roots_orig hRS' hf_orig ⟨hu₀R, hv₀R⟩
      | split _ _ _ _ =>
        exact hfG_old
    · have hf_old := hF_sub hf
      have hfG_old := I.hF_sub_G.2.1 hf_old
      have hfg := I.hF_sub_G.2.2 f hf_old
      cases u with
      | insert e_new a b =>
        have hne : f ≠ e_new := fun h => hu.1 (h ▸ hfG_old)
        dsimp only [LSFState.RF, S', applyLSFUpdate, MGraph.applyUpdate]
        rw [Function.update_of_ne hne, Function.update_of_ne hne]
        exact hfg
      | delete _ =>
        exact hfg
      | split v v' St Sh =>
        dsimp only [LSFState.RF, S', applyLSFUpdate, MGraph.applyUpdate]
        have ht_eq : S.T_cur.tail f = S.G.tail f := hfg.1
        have hh_eq : S.T_cur.head f = S.G.head f := hfg.2
        rw [ht_eq, hh_eq]
        exact ⟨rfl, rfl⟩
  have hI' : LSFInvWith thresh K_σ ℓ₀ S' :=
    { hG₀_val := hG₀'.symm ▸ I.hG₀_val
      hG_val := hG'.symm ▸ applyUpdate_isValid I.hG_val hu
      hV₀ := hG₀'.symm ▸ I.hV₀
      hk := hk'.symm ▸ I.hk
      hℓ₀ := hG₀'.symm ▸ I.hℓ₀
      hT₀ := hT₀'.symm ▸ hr₀'.symm ▸ I.hT₀
      hTV := hT₀'.symm ▸ hG₀'.symm ▸ I.hTV
      hr₀_base := hr₀'.symm ▸ hR₀_base_sub I.hr₀_base
      hR₀_sub := hR₀'_sub
      hord := hT₀'.symm ▸ hπ'.symm ▸ I.hord
      hTG₀ := hT₀'.symm ▸ hG₀'.symm ▸ I.hTG₀
      hTp₀ := hT₀'.symm ▸ hG₀'.symm ▸ I.hTp₀
      hpi_br := hT₀'.symm ▸ hG₀'.symm ▸ hπ'.symm ▸ I.hpi_br
      hT_cur_forest := hT_cur_forest'
      hT_cur_V := hT_cur_V'
      hT_cur_E := hT_cur_E'
      hF_sub_G := hF_sub_G'
      horig_id := horig_id'
      horig_split := horig_split'
      horig_T := horig_T'
      horig_G_nins := horig_G_nins'
      hunsplit_F := hunsplit_F'
      hdisj_iso := hdisj'
      hGV_eq := hGV'
      hins_sub := hins_sub'
      hins_wstr := hins_wstr'
      horig_del := horig_del'
      hsurv_edge := hsurv'
      hwstr_bound := hwstr_bound'
      hthresh_bd := ⟨I.hthresh_bd.1, by rw [hk', hG₀']; exact I.hthresh_bd.2⟩
      hdeg_le := hdeg'
      hb_W := hW'.symm ▸ I.hb_W.trans hR_orig_sub
      hW_props := fun W hW => by
        rw [hW'] at hW
        have hw := I.hW_props W hW
        refine ⟨hT₀'.symm ▸ hw.1, hT₀'.symm ▸ hw.2.1, hW'.symm ▸ hw.2.2.1, ?_⟩
        rw [hk', hG₀']
        have hsub_diff : W \ S'.R_orig ⊆ W \ S.R_orig := fun x hx =>
          Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1, fun h => (Finset.mem_sdiff.mp hx).2 (hR_orig_sub h)⟩
        exact (Nat.cast_le.mpr (Finset.sum_le_sum_of_subset hsub_diff)).trans hw.2.2.2 }
  exact ⟨hI', hG', hG₀', hT₀', hr₀', hπ', hk', hW', hR_sub, hF_sub, hcard_R'⟩

lemma applyLSFUpdate_inv {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (I : LSFInv C_lsst ℓ₀ S) {u : Update} (hu : S.G.UpdateIsValid u) :
    let S' := applyLSFUpdate S u
    LSFInv C_lsst ℓ₀ S' ∧
    S'.G = S.G.applyUpdate u ∧
    S'.G₀ = S.G₀ ∧ S'.T₀ = S.T₀ ∧ S'.r₀ = S.r₀ ∧ S'.π = S.π ∧ S'.k = S.k ∧
    S'.W_init = S.W_init ∧
    S.R ⊆ S'.R ∧
    S'.RF.F.E ⊆ S.RF.F.E ∧
    (S'.R.card : ℝ) ≤ (S.R.card : ℝ) + 56 * (Real.log ((S.G₀.n : ℝ) + 2)) ^ 2 := by
  have hres := applyLSFUpdate_inv_with I hu
  have ⟨_, hG₀', _, _, _, _, hk', _⟩ := applyLSFUpdate_fields S u
  refine ⟨?_, hres.2⟩
  change LSFInvWith (wstrThresh C_lsst (applyLSFUpdate S u).G₀.n (applyLSFUpdate S u).k)
    (6272 * max 1 C_lsst) ℓ₀ (applyLSFUpdate S u)
  rw [hG₀', hk']
  exact hres.1


end MinCostFlow.LSF
