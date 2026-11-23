module

public import MinCostFlow.SparseCore.BundleEpochRecourse

import MinCostFlow.SparseCore.BundleStage
import MinCostFlow.SparseCore.BundleRunInv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Recourse, batch encoding size, and bucket-size bounds for `bundleRunSeq`

Specializes `bundleEpoch_recourse_and_enc` to `bundleRunSeq` (`bundleRunSeq_recourse_and_enc`),
proving the degree-free cumulative recourse bound with factor `bundleRecoursePerQ`, the Lemma 2.1
encoded recourse bound, and exact vanishing on zero input updates. Deletions and splits of all
`(component, bucket)` pairs are bounded using the local counting of `bundleCompStep_local` and
`bundleRunSeq_stage_inv`.

Also provides the unconditional initial bucket-size sums (`bundleRec_all_buckets_sum_le`) and
step-cost decomposition (`bundleRec_runSeq_cost_eq`).
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

private lemma cast_rotation_order {G H : MGraph} (h : G = H) (ρ : Rotation G) :
    (h ▸ ρ : Rotation H).order = ρ.order := by
  cases h; rfl

private lemma cast_rotationBatch {G₁ G₂ : MGraph} (hG : G₁ = G₂) {β : ℕ} {U : List Update}
    {ρ : Rotation G₁} {σ : Rotation (G₁.applyBatch U)} (hrot : RotationBatch β U ρ σ) :
    RotationBatch β U (hG ▸ ρ) ((congrArg (fun G => G.applyBatch U) hG) ▸ σ) := by
  cases hG; exact hrot

private lemma bundleRunSeq_UB_sum_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M N τ : ℕ} (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hOrd : OrderedUpTo D τ 2 ord) (j B_bound : ℕ)
    (hB_bound : ∀ C ∈ components (D.G 0),
      ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1.activeBuckets C).card ≤ B_bound)
    {r : ℕ} (hr : r < τ)
    (hBase_r :
      let G₀ := D.G 0
      let run := bundleRunSeq oracle C_lsst L sparsify k M N D ord j
      let st₀ := (run 0).1
      let st := (run r).1
      st.k = k ∧
      st.cs = compLSFBatch st₀.cs (dynBatches D r).flatten ∧
      CompLSFInv C_lsst (D.ℓ 0) st.cs ∧
      st.cs.G = D.G r ∧
      ∀ C ∈ components G₀, ∀ b : ℤ,
        (∀ (ρ : Rotation st.cs.G) (hG : st.cs.G.IsValid)
            (hF : st.cs.RF.IsRootedSpanningForestOf st.cs.G), ρ.order = ord r →
          (st.bun (C, b)).IsPartition (coreRotation (L := st.cs.lsf) ρ hG hF) k) ∧
        (st.bun (C, b)).edges ⊆ (st₀.bun (C, b)).edges ∧
        (∀ x ∈ (st.bun (C, b)).vertices, (st.bun (C, b)).parent x ∈ (st.cs.compSt C).R))
    (hStep_r :
      let G₀ := D.G 0
      let run := bundleRunSeq oracle C_lsst L sparsify k M N D ord j
      let st := (run r).1
      let st' := (run (r + 1)).1
      let info := bundleRunInfo oracle C_lsst L sparsify k M N D ord j r
      st.cs.G.BatchIsValid (D.U (r + 1)) ∧
      ∀ C ∈ components G₀, ∀ b : ℤ,
        (st.dyn (C, b)).G.BatchIsValid (info.U_B (C, b)) ∧
        (∀ op ∈ info.U_B (C, b), isDelOrSplit op) ∧
        batchSplitCount (info.U_B (C, b)) ≤
          2 * ((st'.cs.compSt C).R \ (st.cs.compSt C).R).card) :
    let G₀ := D.G 0
    let run := bundleRunSeq oracle C_lsst L sparsify k M N D ord j
    let actB := (run 0).1.activeBuckets
    let st := (run r).1
    let st' := (run (r + 1)).1
    let info := bundleRunInfo oracle C_lsst L sparsify k M N D ord j r
    ((components G₀).sum fun C => (actB C).sum fun b => (info.U_B (C, b)).length) ≤
      B_bound * ((D.U (r + 1)).length + 2 * (st'.cs.RF.R \ st.cs.RF.R).card) := by
  classical
  intro G₀ run actB st st' info
  by_cases hB0 : B_bound = 0
  · subst hB0
    have hzero : ∀ C ∈ components G₀, actB C = ∅ := fun C hC =>
      Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hB_bound C hC))
    have hsum0 : ((components G₀).sum fun C => (actB C).sum fun b => (info.U_B (C, b)).length) = 0 :=
      Finset.sum_eq_zero fun C hC => by rw [hzero C hC]; simp
    omega
  have hB1 : 1 ≤ B_bound := Nat.pos_of_ne_zero hB0
  obtain ⟨hst_k, hst_cs_eq, hI_r, hG_eq, hComp_r⟩ := hBase_r
  obtain ⟨hBV_r, hStep_cb⟩ := hStep_r
  obtain ⟨ρ_all, hρ_ord, hρ_batch⟩ := hOrd
  obtain ⟨hG_step, hrot_r⟩ := hρ_batch r hr
  have hlen_split :
      ((components G₀).sum fun C => (actB C).sum fun b => (info.U_B (C, b)).length) =
      ((components G₀).sum fun C => (actB C).sum fun b => (info.U_B (C, b)).countP deleteTag) +
      ((components G₀).sum fun C => (actB C).sum fun b => batchSplitCount (info.U_B (C, b))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun C hC => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact bundleRec_isDelOrSplit_length (hStep_cb C hC b).2.1
  have hDel_le :
      ((components G₀).sum fun C => (actB C).sum fun b => (info.U_B (C, b)).countP deleteTag) ≤
        (D.U (r + 1)).length := by
    let cs₀ := initCompLSF oracle C_lsst G₀ (D.ℓ 0) k j
    let C₀ := coreGraph G₀ cs₀.lsf
    let origB : ℕ → ℤ := fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ (D.ℓ 0)) e)
    have hsub_cb : ∀ C ∈ components G₀, ∀ b : ℤ,
        (info.U_B (C, b)).countP deleteTag = (batchDeletes (info.U_B (C, b))).card ∧
        batchDeletes (info.U_B (C, b)) ⊆ bucketCoreEdges C₀ origB C b ∩ batchDeletes (D.U (r + 1)) := by
      intro C hC b
      have hscb := hStep_cb C hC b
      have hcnt := bundleRec_countP_deleteTag_eq_card_batchDeletes hscb.1 hscb.2.1
      have hready : BundleStepReady st.cs (st.bun (C, b)) k (ord r) (ord (r + 1)) (D.U (r + 1)) := by
        let ρr : Rotation st.cs.G := hG_eq.symm ▸ ρ_all r
        let σr : Rotation (st.cs.G.applyBatch (D.U (r + 1))) :=
          (congrArg (fun G => G.applyBatch (D.U (r + 1))) hG_eq.symm) ▸ (hG_step ▸ ρ_all (r + 1))
        have hρr_ord : ρr.order = ord r := by
          rw [cast_rotation_order]; exact hρ_ord r (Nat.le_of_lt hr)
        have hσr_ord : σr.order = ord (r + 1) := by
          rw [cast_rotation_order, cast_rotation_order]; exact hρ_ord (r + 1) hr
        have hrot' : RotationBatch 2 (D.U (r + 1)) ρr σr := cast_rotationBatch hG_eq.symm hrot_r
        unfold BundleStepReady
        exact ⟨C_lsst, D.ℓ 0, hI_r, ρr, σr, hρr_ord, hσr_ord, hrot', hBV_r,
          (hComp_r C hC b).1 ρr hI_r.hG_val (compLSF_RF_isRSF hI_r) hρr_ord⟩
      have hG0_eq : st.cs.G₀ = G₀ := by
        rw [hst_cs_eq, compLSFBatch_G₀]; rfl
      have hloc := (bundleCompStep_local hready C (hG0_eq.symm ▸ hC) (hComp_r C hC b).2.2).2
      have hUB_eq : info.U_B (C, b) =
          (bundleCompStep st.cs (st.bun (C, b)) k (ord r) (ord (r + 1)) (D.U (r + 1))).1 := by
        change (bundleCompStep st.cs (st.bun (C, b)) st.k (ord r) (ord (r + 1)) (D.U (r + 1))).1 = _
        rw [hst_k]
      rw [← hUB_eq] at hloc
      have hbd_sub := bundleRec_batchDeletes_sub_of_local hloc
      have he_sub : (st.bun (C, b)).edges ⊆ bucketCoreEdges C₀ origB C b := by
        refine Finset.Subset.trans (hComp_r C hC b).2.1 ?_
        change (initBundleFor cs₀ (ord 0) (bucketCoreEdges C₀ origB C b) k).edges ⊆ _
        unfold initBundleFor
        split_ifs
        · exact Finset.Subset.refl _
        · exact Finset.empty_subset _
      exact ⟨hcnt, Finset.Subset.trans hbd_sub (Finset.inter_subset_inter_right he_sub)⟩
    let S := (components G₀).sigma actB
    have hdisj : Set.PairwiseDisjoint (↑S : Set (Σ _ : Finset ℕ, ℤ))
        (fun p => batchDeletes (info.U_B (p.1, p.2))) := by
      intro p₁ hp₁ p₂ hp₂ hne
      rw [Finset.mem_coe, Finset.mem_sigma] at hp₁ hp₂
      have hne' : (p₁.1, p₁.2) ≠ (p₂.1, p₂.2) := by
        intro hEq
        apply hne
        cases p₁; cases p₂
        simp only [Prod.mk.injEq] at hEq
        cases hEq.1; cases hEq.2; rfl
      have hd := bundleRec_bucketCoreEdges_disjoint G₀ C₀ origB hp₁.1 hp₂.1 hne'
      exact hd.mono
        (Finset.Subset.trans (hsub_cb p₁.1 hp₁.1 p₁.2).2 Finset.inter_subset_left)
        (Finset.Subset.trans (hsub_cb p₂.1 hp₂.1 p₂.2).2 Finset.inter_subset_left)
    have hsum_eq :
        ((components G₀).sum fun C => (actB C).sum fun b => (info.U_B (C, b)).countP deleteTag) =
        (S.biUnion fun p => batchDeletes (info.U_B (p.1, p.2))).card := by
      rw [Finset.card_biUnion hdisj, Finset.sum_sigma]
      exact Finset.sum_congr rfl fun C hC =>
        Finset.sum_congr rfl fun b _ => (hsub_cb C hC b).1
    have hbi_sub : (S.biUnion fun p => batchDeletes (info.U_B (p.1, p.2))) ⊆
        batchDeletes (D.U (r + 1)) := by
      refine Finset.biUnion_subset.mpr fun p hp => ?_
      rw [Finset.mem_sigma] at hp
      exact Finset.Subset.trans (hsub_cb p.1 hp.1 p.2).2 Finset.inter_subset_right
    rw [hsum_eq]
    exact le_trans (Finset.card_le_card hbi_sub) (batchDeletes_card_le _)
  have hSplit_le :
      ((components G₀).sum fun C => (actB C).sum fun b => batchSplitCount (info.U_B (C, b))) ≤
        2 * B_bound * (st'.cs.RF.R \ st.cs.RF.R).card := by
    have hG0_eq : st.cs.G₀ = G₀ := by
      rw [hst_cs_eq, compLSFBatch_G₀]; rfl
    have hcs'_eq : st'.cs = compLSFBatch st.cs (D.U (r + 1)) := rfl
    have hsum_R :
        ((components G₀).sum fun C => ((st'.cs.compSt C).R \ (st.cs.compSt C).R).card) =
          (st'.cs.RF.R \ st.cs.RF.R).card := by
      rw [hcs'_eq, ← hG0_eq]
      exact bundleRec_sum_comp_R_sdiff_eq hI_r hBV_r
    calc ((components G₀).sum fun C => (actB C).sum fun b => batchSplitCount (info.U_B (C, b)))
        ≤ (components G₀).sum fun C => (actB C).sum fun _ =>
            2 * ((st'.cs.compSt C).R \ (st.cs.compSt C).R).card :=
          Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b _ => (hStep_cb C hC b).2.2
      _ = (components G₀).sum fun C =>
            (actB C).card * (2 * ((st'.cs.compSt C).R \ (st.cs.compSt C).R).card) := by
          refine Finset.sum_congr rfl fun C _ => ?_
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (components G₀).sum fun C =>
            B_bound * (2 * ((st'.cs.compSt C).R \ (st.cs.compSt C).R).card) :=
          Finset.sum_le_sum fun C hC => Nat.mul_le_mul_right _ (hB_bound C hC)
      _ = 2 * B_bound * ((components G₀).sum fun C =>
            ((st'.cs.compSt C).R \ (st.cs.compSt C).R).card) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun C _ => by ring
      _ = 2 * B_bound * (st'.cs.RF.R \ st.cs.RF.R).card := by rw [hsum_R]
  have hDel_B : (D.U (r + 1)).length ≤ B_bound * (D.U (r + 1)).length :=
    Nat.le_mul_of_pos_left _ hB1
  rw [hlen_split]
  calc ((components G₀).sum fun C => (actB C).sum fun b => (info.U_B (C, b)).countP deleteTag) +
        ((components G₀).sum fun C => (actB C).sum fun b => batchSplitCount (info.U_B (C, b)))
      ≤ B_bound * (D.U (r + 1)).length + 2 * B_bound * (st'.cs.RF.R \ st.cs.RF.R).card :=
        Nat.add_le_add (le_trans hDel_le hDel_B) hSplit_le
    _ = B_bound * ((D.U (r + 1)).length + 2 * (st'.cs.RF.R \ st.cs.RF.R).card) := by ring

/-- Cumulative recourse `∑ |U_S|` (with degree-free factor `bundleRecoursePerQ` at vertex scale
`min N (M + 1)`), Lemma 2.1 encoded recourse `∑ S.batchEnc U_S`, and exact vanishing on zero
input updates for one branch `bundleRunSeq` (paper Lemma 5.17, item 1, page 23). -/
theorem bundleRunSeq_recourse_and_enc_min
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord)
    (j : ℕ) (hj : j < k) (B_bound : ℕ)
    (hB_bound : ∀ C ∈ components (D.G 0),
      ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1.activeBuckets C).card ≤ B_bound) :
    ∀ t ≤ τ,
      let st := fun s => (bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).1
      let U_S := fun s => (bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).2
      let q_t := ∑ s ∈ Finset.Icc 1 t, (D.U s).length
      ((∑ s ∈ Finset.Icc 1 t, (U_S s).length : ℕ) : ℝ) ≤
        bundleRecoursePerQ L P_b M (min N (M + 1)) B_bound * (q_t : ℝ) ∧
      ((∑ s ∈ Finset.Icc 1 t, (st (s - 1)).S_cur.batchEnc (U_S s) : ℕ) : ℝ) ≤
        20 * (((st 0).S_cur.m : ℝ) + ((∑ s ∈ Finset.Icc 1 t, (U_S s).length : ℕ) : ℝ)) *
          Real.log (((st 0).S_cur.m : ℝ) + ((∑ s ∈ Finset.Icc 1 t, (U_S s).length : ℕ) : ℝ) + 2) ∧
      (q_t = 0 →
        ∑ s ∈ Finset.Icc 1 t, (U_S s).length = 0 ∧
        ∑ s ∈ Finset.Icc 1 t, (st (s - 1)).S_cur.batchEnc (U_S s) = 0) := by
  classical
  intro t ht st U_S q_t
  set G₀ := D.G 0
  set actB := (st 0).activeBuckets
  obtain ⟨hBase, hStep, _⟩ := bundleRunSeq_stage_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh ord hOrd j
  obtain ⟨hStage_all, hStep_full, hT82_cum⟩ := bundleRunSeq_inv oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp ord hOrd j hj
  have hM_of_actB : ∀ C ∈ components G₀, (actB C).Nonempty → 1 ≤ M := fun C _ hne =>
    bundleRec_initBundleTree_M_of_actB oracle C_lsst L sparsify (N := N) hM (ord 0) j hne
  have hHb_bounds : ∀ C ∈ components G₀, ∀ b : ℤ,
      ((st 0).bun (C, b)).graph.m ≤ M ∧
      ((st 0).bun (C, b)).graph.n ≤ 2 * ((st 0).bun (C, b)).graph.m := fun C _ b =>
    bundleRec_initBundleTree_bun_bounds oracle C_lsst L sparsify (N := N) hk hM (ord 0) j C b
  have hcs_inv_ep : ∀ r ≤ t, CompLSFInv C_lsst (D.ℓ 0) (st r).cs ∧ (st r).cs.G₀ = D.G 0 := by
    intro r hr
    have hbr := hBase r (le_trans hr ht)
    exact ⟨hbr.2.2.2.2.2.2.2.1, by rw [hbr.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl⟩
  have hBV_ep : ∀ r < t, (st r).cs.G.BatchIsValid (D.U (0 + r + 1)) := fun r hr => by
    rw [Nat.zero_add]; exact (hStep r (lt_of_lt_of_le hr ht)).1
  have hactB_ep : ∀ r ≤ t, (st r).activeBuckets = actB := fun r hr =>
    (hBase r (le_trans hr ht)).2.2.2.2.1
  have hUB_sum_ep : ∀ r < t,
      ((components G₀).sum fun C => (actB C).sum fun b =>
        ((stepBundleTree sparsify (st r) (D.U (0 + r + 1))
          (ord (0 + r)) (ord (0 + r + 1))).U_B (C, b)).length) ≤
        B_bound * ((D.U (0 + r + 1)).length + 2 * ((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card) := by
    intro r hr
    have hr_lt : r < τ := lt_of_lt_of_le hr ht
    have hbr := hBase r (Nat.le_of_lt hr_lt)
    have hsr := hStep r hr_lt
    rw [Nat.zero_add]
    exact bundleRunSeq_UB_sum_le oracle C_lsst L sparsify D ord hOrd j B_bound hB_bound
      hr_lt
      ⟨hbr.1, hbr.2.2.2.2.2.2.1, hbr.2.2.2.2.2.2.2.1, hbr.2.2.2.2.2.2.2.2.1,
        fun C hC b => ⟨((hbr.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).1,
          ((hbr.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.1,
          ((hbr.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.1⟩⟩
      ⟨hsr.1, fun C hC b => ⟨(hsr.2.2.2.2 C hC b).1, (hsr.2.2.2.2 C hC b).2.2.1,
        (hsr.2.2.2.2 C hC b).2.2.2.1⟩⟩
  have hStage_ep : ∀ r ≤ t,
      (st r).S_cur.IsValid ∧
      (st r).activeComps ⊆ components G₀ ∧
      ∀ C ∈ components G₀, ∀ b : ℤ,
        ((st r).dyn (C, b)).G.IsSubgraph ((st r).dyn (C, b)).H ∧
        (((st r).dyn (C, b)).H.m : ℝ) ≤
          ((L : ℝ) + 1) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ *
            (1 + Real.log ((((st r).dyn (C, b)).G.n : ℝ) + (((st 0).bun (C, b)).graph.m : ℝ) + 2)) ^ P_b.p_s ∧
        ((piTotal ((st r).dyn (C, b))).length ((st r).dyn (C, b)).G : ℝ) ≤ coreE82Len L P_b := by
    intro r hr
    have hS := hStage_all r (le_trans hr ht)
    exact ⟨hS.1, hS.2.2.2.2.1, fun C hC b =>
      ⟨(hS.2.2.2.2.2.2.2 C hC b).1, (hS.2.2.2.2.2.2.2 C hC b).2.1,
        (hS.2.2.2.2.2.2.2 C hC b).2.2.2.2.1⟩⟩
  have hStep_ep : ∀ r < t,
      let info := stepBundleTree sparsify (st r) (D.U (0 + r + 1))
        (ord (0 + r)) (ord (0 + r + 1))
      (st r).S_cur.BatchIsValid info.U_S ∧
      (st (r + 1)).S_cur = (st r).S_cur.applyBatch info.U_S ∧
      (D.U (0 + r + 1) = [] → info.U_S = []) ∧
      (∀ C ∈ components G₀, ∀ b : ℤ,
        (info.stepOut (C, b)).state = (st (r + 1)).dyn (C, b) ∧
        ((st r).dyn (C, b)).H.applyBatch (info.stepOut (C, b)).UH = ((st (r + 1)).dyn (C, b)).H) ∧
      info.newlyActive ⊆ components G₀ \ largeComps k G₀ ∧
      info.newlyActive.card ≤ 2 * (D.U (0 + r + 1)).length ∧
      (∀ C ∈ info.newlyActive, ∀ b : ℤ, ((st r).dyn (C, b)).G.n ≤ 11) ∧
      info.U_S.length ≤
        (st (r + 1)).activeComps.sum (fun C => (actB C).sum fun b =>
          (info.stepOut (C, b)).UH.length) +
        info.newlyActive.sum (fun C => (actB C).sum fun b =>
          ((st r).dyn (C, b)).H.E.card) +
        7 * (D.U (0 + r + 1)).length +
        2 * ((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card +
        2 * info.D_total.card := by
    intro r hr
    have hSt := hStep_full (r + 1) (Nat.succ_pos r) (le_trans (Nat.succ_le_of_lt hr) ht)
    simp only [Nat.add_sub_cancel] at hSt
    rw [Nat.zero_add]
    exact ⟨hSt.1, hSt.2.1, fun hn => (hSt.2.2.1 hn).1,
      fun C hC b => ⟨(hSt.2.2.2.1 C hC b).2.1, (hSt.2.2.2.1 C hC b).2.2.2.1⟩,
      hSt.2.2.2.2.2.1, hSt.2.2.2.2.2.2.1, hSt.2.2.2.2.2.2.2.1, hSt.2.2.2.2.2.2.2.2⟩
  have hT82_ep : ∀ C ∈ components G₀, ∀ b : ℤ,
      let Hb₀ := ((st 0).bun (C, b)).graph
      let splitB := bundleSplitBudget k M
      let nMax_b := Hb₀.n + splitB
      let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s
      let nRoot_b := ((max nMax_b 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
      let batchTot_b := ∑ r ∈ Finset.range t,
        (((stepBundleTree sparsify (st r) (D.U (0 + r + 1))
          (ord (0 + r)) (ord (0 + r + 1))).U_B (C, b)).length : ℝ)
      (∑ r ∈ Finset.range t,
        (((stepBundleTree sparsify (st r) (D.U (0 + r + 1))
          (ord (0 + r)) (ord (0 + r + 1))).stepOut (C, b)).UH.length : ℝ)) ≤
        (2 + 12 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * Λ_s_b) * batchTot_b ∧
      (∑ r ∈ Finset.range t,
        (((stepBundleTree sparsify (st r) (D.U (0 + r + 1))
          (ord (0 + r)) (ord (0 + r + 1))).stepOut (C, b)).D.card : ℝ)) ≤
        6 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) * Λ_s_b *
          batchTot_b := by
    intro C hC b
    have hT := hT82_cum C hC b t ht
    have hlen : ((bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b).take t).flatten.length =
        ∑ r ∈ Finset.range t,
          ((stepBundleTree sparsify (st r) (D.U (0 + r + 1))
            (ord (0 + r)) (ord (0 + r + 1))).U_B (C, b)).length := by
      rw [bundleBatchList_take_flatten_length oracle C_lsst L sparsify k M N τ D ord j C b ht]
      exact Finset.sum_congr rfl fun r _ => by rw [Nat.zero_add]; rfl
    have hstep : ∀ r ∈ Finset.range t,
        DynSpanner.runBatchStepOut (L := L) (normGraph ((st 0).bun (C, b)).graph)
          (phaseBase ((normGraph ((st 0).bun (C, b)).graph).n + bundleSplitBudget k M) L) (sparsify M)
          (bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b) r =
        (stepBundleTree sparsify (st r) (D.U (0 + r + 1))
          (ord (0 + r)) (ord (0 + r + 1))).stepOut (C, b) := by
      intro r hr
      have hr_lt : r < τ := lt_of_lt_of_le (Finset.mem_range.mp hr) ht
      have hDyn := ((hBase r (Nat.le_of_lt hr_lt)).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b |>.2.2.2.2.2
      have hSt := hStep_full (r + 1) (Nat.succ_pos r) hr_lt
      simp only [Nat.add_sub_cancel] at hSt
      have hEq := bundleRunBatchStepOut_eq_stepOut oracle C_lsst L sparsify k M N τ D ord j
        C b hr_lt hDyn (hSt.2.2.2.1 C hC b).1
      rw [Nat.zero_add]; exact hEq
    have h1 := hT.2.2.1
    have h2 := hT.2.2.2.1
    dsimp only at h1 h2
    rw [hlen, Nat.cast_sum] at h1 h2
    conv_lhs at h1 =>
      rw [Finset.sum_congr rfl fun r hr =>
        congrArg (fun x : StepOut L => (x.UH.length : ℝ)) (hstep r hr)]
    conv_lhs at h2 =>
      rw [Finset.sum_congr rfl fun r hr =>
        congrArg (fun x : StepOut L => (x.D.card : ℝ)) (hstep r hr)]
    exact ⟨h1, h2⟩
  have hep := bundleEpoch_recourse_and_enc_min (τ := τ) hL P_b sparsify hk D ord actB B_bound hB_bound
    hM_of_actB 0 t (by simpa using ht) st U_S (fun C b => ((st 0).bun (C, b)).graph) hHb_bounds
    (fun r _ => by rw [Nat.zero_add]; rfl) (fun r _ => by rw [Nat.zero_add]; rfl)
    hcs_inv_ep hBV_ep hactB_ep hUB_sum_ep hStage_ep hStep_ep hT82_ep
  have hIcc : Finset.Icc (0 + 1) (0 + t) = Finset.Icc 1 t := by simp
  have h1 := hep.1
  have h2 := hep.2.1
  have h3 := hep.2.2
  rw [hIcc] at h1 h3
  have hmin_le : min (D.G 0).n ((D.G 0).m + 1) ≤ min N (M + 1) :=
    le_min (le_trans (min_le_left _ _) hN) (le_trans (min_le_right _ _) (Nat.succ_le_succ hM))
  exact ⟨le_trans h1 (mul_le_mul_of_nonneg_right
    (bundleRec_PerQ_mono_n L P_b M hmin_le B_bound) (Nat.cast_nonneg _)), h2, h3⟩

/-- Cumulative recourse `∑ |U_S|` (with degree-free factor `bundleRecoursePerQ`), Lemma 2.1
encoded recourse `∑ S.batchEnc U_S`, and exact vanishing on zero input updates for one branch
`bundleRunSeq` (paper Lemma 5.17, item 1, page 23). -/
theorem bundleRunSeq_recourse_and_enc
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord)
    (j : ℕ) (hj : j < k) (B_bound : ℕ)
    (hB_bound : ∀ C ∈ components (D.G 0),
      ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1.activeBuckets C).card ≤ B_bound) :
    ∀ t ≤ τ,
      let st := fun s => (bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).1
      let U_S := fun s => (bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).2
      let q_t := ∑ s ∈ Finset.Icc 1 t, (D.U s).length
      ((∑ s ∈ Finset.Icc 1 t, (U_S s).length : ℕ) : ℝ) ≤
        bundleRecoursePerQ L P_b M N B_bound * (q_t : ℝ) ∧
      ((∑ s ∈ Finset.Icc 1 t, (st (s - 1)).S_cur.batchEnc (U_S s) : ℕ) : ℝ) ≤
        20 * (((st 0).S_cur.m : ℝ) + ((∑ s ∈ Finset.Icc 1 t, (U_S s).length : ℕ) : ℝ)) *
          Real.log (((st 0).S_cur.m : ℝ) + ((∑ s ∈ Finset.Icc 1 t, (U_S s).length : ℕ) : ℝ) + 2) ∧
      (q_t = 0 →
        ∑ s ∈ Finset.Icc 1 t, (U_S s).length = 0 ∧
        ∑ s ∈ Finset.Icc 1 t, (st (s - 1)).S_cur.batchEnc (U_S s) = 0) := by
  intro t ht st U_S q_t
  have h := bundleRunSeq_recourse_and_enc_min oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp ord hOrd j hj B_bound hB_bound t ht
  exact ⟨le_trans h.1 (mul_le_mul_of_nonneg_right
    (bundleRec_PerQ_mono_n L P_b M (min_le_left N (M + 1)) B_bound)
    (Nat.cast_nonneg _)), h.2.1, h.2.2⟩

/-! ## Global initial bucket-size sums and step-cost decomposition -/

/-- Unconditional global bucket-count, edge-count, and vertex-count bounds for `initBundleTree`. -/
lemma bundleRec_all_buckets_sum_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M N : ℕ} (hk : 1 ≤ k) {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} (ord : ℕ → List End) (j : ℕ) :
    let st₀ := initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j
    let actB := st₀.activeBuckets
    ((components G₀).sum fun C => (actB C).card) ≤ G₀.m ∧
    ((components G₀).sum fun C => (actB C).sum fun b => (st₀.bun (C, b)).graph.m) ≤ G₀.m ∧
    ((components G₀).sum fun C => (actB C).sum fun b => (st₀.bun (C, b)).graph.n) ≤ 2 * G₀.m := by
  classical
  intro st₀ actB
  let cs₀ := initCompLSF oracle C_lsst G₀ ℓ₀ k j
  let C₀ := coreGraph G₀ cs₀.lsf
  let origB : ℕ → ℤ := fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e)
  have hcard_disj : Set.PairwiseDisjoint (↑(components G₀) : Set (Finset ℕ))
      (fun C => C₀.E.filter fun e => C₀.tail e ∈ C) := by
    intro C₁ hC₁ C₂ hC₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he₁ he₂
    exact Finset.disjoint_left.mp (components_V_pairwiseDisjoint G₀ hC₁ hC₂ hne)
      (Finset.mem_filter.mp he₁).2 (Finset.mem_filter.mp he₂).2
  have hact_sum : ((components G₀).sum fun C => (actB C).card) ≤ G₀.m := by
    calc ((components G₀).sum fun C => (actB C).card)
        ≤ (components G₀).sum fun C => (C₀.E.filter fun e => C₀.tail e ∈ C).card :=
          Finset.sum_le_sum fun C _ => Finset.card_image_le
      _ = ((components G₀).biUnion fun C => C₀.E.filter fun e => C₀.tail e ∈ C).card :=
          (Finset.card_biUnion hcard_disj).symm
      _ ≤ G₀.m := Finset.card_le_card (Finset.biUnion_subset.mpr fun _ _ =>
          Finset.Subset.trans (Finset.filter_subset _ _) Finset.sdiff_subset)
  let S := (components G₀).sigma actB
  have hpair_disj : Set.PairwiseDisjoint (↑S : Set (Σ _ : Finset ℕ, ℤ))
      (fun p => bucketCoreEdges C₀ origB p.1 p.2) := by
    intro p₁ hp₁ p₂ hp₂ hne
    rw [Finset.mem_coe, Finset.mem_sigma] at hp₁ hp₂
    have hne' : (p₁.1, p₁.2) ≠ (p₂.1, p₂.2) := by
      intro hEq; apply hne; cases p₁; cases p₂
      simp only [Prod.mk.injEq] at hEq; cases hEq.1; cases hEq.2; rfl
    exact bundleRec_bucketCoreEdges_disjoint G₀ C₀ origB hp₁.1 hp₂.1 hne'
  have hbf_all : ∀ C ∈ components G₀, ∀ b : ℤ,
      (st₀.bun (C, b)).graph.m ≤ (bucketCoreEdges C₀ origB C b).card ∧
      (st₀.bun (C, b)).graph.n ≤ 2 * (st₀.bun (C, b)).graph.m := by
    intro C _ b
    have hcs0_G : cs₀.G = G₀ := rfl
    have hsub := bundleRec_bucketCoreEdges_sub G₀ cs₀.lsf origB C b
    have hbf := bundleRec_initBundleFor_bounds cs₀ ord (bucketCoreEdges C₀ origB C b) hk
      (by rw [hcs0_G]; exact hsub.1)
    exact ⟨hbf.2.1, hbf.2.2⟩
  have hm_sum : ((components G₀).sum fun C => (actB C).sum fun b => (st₀.bun (C, b)).graph.m) ≤ G₀.m := by
    calc ((components G₀).sum fun C => (actB C).sum fun b => (st₀.bun (C, b)).graph.m)
        ≤ (components G₀).sum fun C => (actB C).sum fun b => (bucketCoreEdges C₀ origB C b).card :=
          Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b _ => (hbf_all C hC b).1
      _ = S.sum fun p => (bucketCoreEdges C₀ origB p.1 p.2).card :=
          (Finset.sum_sigma (components G₀) actB
            (fun p => (bucketCoreEdges C₀ origB p.1 p.2).card)).symm
      _ = (S.biUnion fun p => bucketCoreEdges C₀ origB p.1 p.2).card :=
          (Finset.card_biUnion hpair_disj).symm
      _ ≤ G₀.m := Finset.card_le_card (Finset.biUnion_subset.mpr fun _ _ =>
          Finset.Subset.trans (Finset.filter_subset _ _) Finset.sdiff_subset)
  have hn_sum : ((components G₀).sum fun C => (actB C).sum fun b => (st₀.bun (C, b)).graph.n) ≤ 2 * G₀.m := by
    calc ((components G₀).sum fun C => (actB C).sum fun b => (st₀.bun (C, b)).graph.n)
        ≤ (components G₀).sum fun C => (actB C).sum fun b => 2 * (st₀.bun (C, b)).graph.m :=
          Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b _ => (hbf_all C hC b).2
      _ = 2 * ((components G₀).sum fun C => (actB C).sum fun b => (st₀.bun (C, b)).graph.m) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun C _ => (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * G₀.m := Nat.mul_le_mul_left 2 hm_sum
  exact ⟨hact_sum, hm_sum, hn_sum⟩

/-- Unconditional step-cost decomposition of `bundleRunSeq`. -/
lemma bundleRec_runSeq_cost_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ) :
    let run := bundleRunSeq oracle C_lsst L sparsify k M N D ord j
    let st₀ := (run 0).1
    let actB := st₀.activeBuckets
    ∀ t,
      (run t).1.cost =
        (D.G 0).m + (activeSubgraph (D.G 0)).n + 1 +
          ((run t).1.activeComps.sum st₀.lazyInitCost) +
          ∑ s ∈ Finset.range t,
            ((D.U (s + 1)).length +
              ((run (s + 1)).1.activeComps.sum fun C => (actB C).sum fun b =>
                ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)).length) +
              (run (s + 1)).2.length +
              ((run (s + 1)).1.activeComps.sum fun C => (actB C).sum fun b =>
                ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).stepOut (C, b)).cost)) := by
  intro run st₀ actB t
  have hinv : ∀ s, (run s).1.activeBuckets = actB ∧ (run s).1.lazyInitCost = st₀.lazyInitCost := by
    intro s
    induction s with
    | zero => exact ⟨rfl, rfl⟩
    | succ s ih => exact ih
  induction t with
  | zero => rfl
  | succ s ih =>
    have hact_b := (hinv s).1
    have hlazy := (hinv s).2
    have hdisj : Disjoint (run s).1.activeComps
        (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).newlyActive :=
      disjoint_sdiff_self_right
    have hact_eq : (run (s + 1)).1.activeComps =
        (run s).1.activeComps ∪
          (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).newlyActive := rfl
    have hsum_act :
        (run (s + 1)).1.activeComps.sum st₀.lazyInitCost =
        (run s).1.activeComps.sum st₀.lazyInitCost +
        (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).newlyActive.sum st₀.lazyInitCost := by
      rw [hact_eq, Finset.sum_union hdisj]
    have hstep := stepBundleTree_cost sparsify (run s).1 (D.U (s + 1)) (ord s) (ord (s + 1))
    dsimp only at hstep
    rw [hact_b, hlazy] at hstep
    change (run (s + 1)).1.cost = (run s).1.cost +
      ((D.U (s + 1)).length +
        ((run (s + 1)).1.activeComps.sum fun C => (actB C).sum fun b =>
          ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)).length) +
        (run (s + 1)).2.length +
        ((run (s + 1)).1.activeComps.sum fun C => (actB C).sum fun b =>
          ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).stepOut (C, b)).cost) +
        (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).newlyActive.sum st₀.lazyInitCost) at hstep
    rw [hstep, ih, hsum_act, Finset.sum_range_succ]
    ac_rfl

end

end MinCostFlow.SparseCore
