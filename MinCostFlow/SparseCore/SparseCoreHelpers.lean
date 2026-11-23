module

public import MinCostFlow.SparseCore.SplitSpannerBounds

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Graph-size and component-LSF helpers for `sparseCoreTool`

General degree/component/threshold helpers (`m0_le_eleven_m`) and `CompLSF` edge/root/bucket
helpers used by `SparseCoreBounds` (`treeRunSeq_inv`).
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## 1. General graph degree/component bounds and `m₀ ≤ 11 * m_t` -/

lemma maxDeg_le_two_m (G : MGraph) : G.maxDeg ≤ 2 * G.m := by
  unfold MGraph.maxDeg
  rw [Finset.sup_le_iff]
  intro v _
  unfold MGraph.deg MGraph.m
  have h1 : (G.E.filter fun e => G.tail e = v).card ≤ G.E.card := Finset.card_filter_le _ _
  have h2 : (G.E.filter fun e => G.head e = v).card ≤ G.E.card := Finset.card_filter_le _ _
  omega

lemma connected_eq_of_deg_zero {G : MGraph} {v : ℕ} (hdeg : G.deg v = 0)
    {w : ℕ} (hconn : G.Connected v w) : w = v := by
  obtain ⟨P, hW⟩ := hconn
  cases hW with
  | nil _ => rfl
  | @cons a b x P' hx hsrc _ =>
    exfalso
    unfold MGraph.deg at hdeg
    rcases x with ⟨e, dir⟩
    cases dir
    · simp only [MGraph.src] at hsrc
      have hpos : 0 < (G.E.filter fun e' => G.head e' = v).card :=
        Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨hx, hsrc⟩⟩
      omega
    · simp only [MGraph.src] at hsrc
      have hpos : 0 < (G.E.filter fun e' => G.tail e' = v).card :=
        Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨hx, hsrc⟩⟩
      omega

lemma n_le_components_add_two_m {G : MGraph} (hG : G.IsValid) :
    G.n ≤ (components G).card + 2 * G.m := by
  set V_iso := G.V.filter fun v => G.deg v = 0
  set V_act := G.V.filter fun v => 0 < G.deg v
  have hpart : G.V = V_iso ∪ V_act := by
    ext v
    simp only [V_iso, V_act, Finset.mem_union, Finset.mem_filter]
    by_cases h0 : G.deg v = 0
    · simp [h0]
    · simp [h0, Nat.pos_of_ne_zero h0]
  have hiso_le : V_iso.card ≤ (components G).card := by
    refine Finset.card_le_card_of_injOn (compOf G)
      (fun v hv => Finset.mem_image_of_mem _ (Finset.mem_filter.mp hv).1) ?_
    intro u hu v hv heq
    have hu_f := Finset.mem_filter.mp hu
    have hv_f := Finset.mem_filter.mp hv
    have huv_mem : v ∈ compOf G u := heq ▸ self_mem_compOf hv_f.1
    exact (connected_eq_of_deg_zero hu_f.2 (mem_compOf_iff.mp huv_mem).2).symm
  have hact_sub : V_act ⊆ G.E.biUnion fun e => {G.tail e, G.head e} := by
    intro v hv
    have hpos : 0 < G.deg v := (Finset.mem_filter.mp hv).2
    unfold MGraph.deg at hpos
    rw [Finset.mem_biUnion]
    by_cases h1 : (G.E.filter fun e => G.tail e = v).Nonempty
    · obtain ⟨e, he⟩ := h1
      rw [Finset.mem_filter] at he
      exact ⟨e, he.1, by simp [he.2]⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      rw [h1, Finset.card_empty, zero_add, Finset.card_pos] at hpos
      obtain ⟨e, he⟩ := hpos
      rw [Finset.mem_filter] at he
      exact ⟨e, he.1, by simp [he.2]⟩
  have hact_le : V_act.card ≤ 2 * G.m := by
    calc V_act.card
        ≤ (G.E.biUnion fun e => {G.tail e, G.head e}).card := Finset.card_le_card hact_sub
      _ ≤ ∑ _e ∈ G.E, 2 := by
          refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun _ _ => ?_)
          exact le_trans (Finset.card_insert_le _ _) (by simp)
      _ = 2 * G.m := by simp [MGraph.m, mul_comm]
  have hV_le : G.n ≤ V_iso.card + V_act.card := by
    unfold MGraph.n
    rw [hpart]
    exact Finset.card_union_le _ _
  have _ := hG
  omega

lemma m_applyBatch_add_length (G : MGraph) (U : List Update) :
    G.m ≤ (G.applyBatch U).m + U.length := by
  have h := symmDiff_applyBatch_card_le G U
  have hsub : G.E ⊆ (G.E \ (G.applyBatch U).E) ∪ (G.applyBatch U).E := by
    intro e he
    by_cases h' : e ∈ (G.applyBatch U).E <;> simp [he, h']
  have hc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  unfold MGraph.m at *
  omega

lemma real_log_three_gt : (21 / 20 : ℝ) < Real.log 3 := by
  have hneg : (19 / 20 : ℝ) ≤ Real.exp (-1 / 20 : ℝ) := by
    linarith [Real.add_one_le_exp (-1 / 20 : ℝ)]
  have hexp_inv : Real.exp (1 / 20 : ℝ) ≤ 20 / 19 := by
    have h1 : (Real.exp (-1 / 20 : ℝ))⁻¹ ≤ (19 / 20 : ℝ)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr hneg
    rw [← Real.exp_neg] at h1
    norm_num at h1
    exact h1
  have hexp_sum : Real.exp (21 / 20 : ℝ) < 3 := by
    have hsum : (21 / 20 : ℝ) = 1 + 1 / 20 := by norm_num
    rw [hsum, Real.exp_add]
    have he1 := Real.exp_one_lt_d9
    nlinarith [Real.exp_pos (1 / 20 : ℝ)]
  calc (21 / 20 : ℝ)
      = Real.log (Real.exp (21 / 20 : ℝ)) := (Real.log_exp _).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos _) hexp_sum

lemma m0_le_eleven_m {k τ : ℕ} (hk : 1 ≤ k) {D : DynamicInstance}
    (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n) :
    ∀ t ≤ τ, ((D.G 0).m : ℝ) ≤ 11 * ((D.G t).m : ℝ) := by
  intro t ht
  by_cases hm₀ : (D.G 0).m = 0
  · rw [hm₀, Nat.cast_zero]
    positivity
  · have hne₀ : (D.G 0).E.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hm₀)
    obtain ⟨e₀, he₀⟩ := hne₀
    have hn₀ : 1 ≤ (D.G 0).n := Finset.card_pos.mpr ⟨(D.G 0).tail e₀, (hG₀ e₀ he₀).1⟩
    have hlog3 : (21 / 20 : ℝ) < Real.log ((D.G 0).n + 2 : ℝ) := by
      refine lt_of_lt_of_le real_log_three_gt (Real.log_le_log (by norm_num) ?_)
      have : (1 : ℝ) ≤ (D.G 0).n := by exact_mod_cast hn₀
      linarith
    have hlog2 : (441 / 400 : ℝ) < (Real.log ((D.G 0).n + 2 : ℝ)) ^ 2 := by nlinarith
    have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hq_t_le : ∑ s ∈ Finset.Icc 1 t, (D.U s).length ≤ ∑ s ∈ Finset.Icc 1 τ, (D.U s).length := by
      refine Finset.sum_le_sum_of_subset fun s hs => ?_
      simp only [Finset.mem_Icc] at hs ⊢
      exact ⟨hs.1, le_trans hs.2 ht⟩
    have hm_t : ∀ s ≤ τ, (D.G 0).m ≤ (D.G s).m + ∑ i ∈ Finset.Icc 1 s, (D.U i).length := by
      intro s
      induction s with
      | zero => intro _; simp
      | succ s ih =>
        intro hs
        have ih' := ih (Nat.le_of_succ_le hs)
        have hstep := hD (s + 1) (Nat.succ_pos s) hs
        simp only [Nat.add_sub_cancel] at hstep
        have hm1 := m_applyBatch_add_length (D.G s) (D.U (s + 1))
        rw [← hstep.2] at hm1
        have hIcc : Finset.Icc 1 (s + 1) = insert (s + 1) (Finset.Icc 1 s) := by
          ext x; simp [Finset.mem_Icc]; omega
        rw [hIcc, Finset.sum_insert (by simp)]
        omega
    have hm_rel : ((D.G 0).m : ℝ) ≤ ((D.G t).m : ℝ) +
        ((∑ s ∈ Finset.Icc 1 τ, (D.U s).length : ℕ) : ℝ) := by
      exact_mod_cast le_trans (hm_t t ht) (Nat.add_le_add_left hq_t_le _)
    have hq_up : ((∑ s ∈ Finset.Icc 1 τ, (D.U s).length : ℕ) : ℝ) ≤
        ((D.G 0).m : ℝ) / (441 / 400 : ℝ) := by
      refine le_trans hThresh ?_
      rw [SparseCoreTool.updateThreshold]
      refine div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) ?_
      nlinarith
    linarith

/-! ## 2. Component-LSF edge, bucket, and Stage 2+3 trajectory helpers (`treeRunSeq_inv`) -/

lemma symmDiff_applyBatch_UH {H H' : MGraph} {UH : List Update} (h : H.applyBatch UH = H') :
    (H.E \ H'.E).card + (H'.E \ H.E).card ≤ UH.length := by
  subst h
  exact symmDiff_applyBatch_card_le H UH

lemma lsfInv_RF_edge_not_inserted {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (hI : LSFInvWith thresh K_σ ℓ₀ S) {e : ℕ} (heF : e ∈ S.RF.F.E) :
    e ∉ S.insertedEdges := by
  intro heI
  have hRS := lsfInv_to_RS hI
  have hw := hI.hins_wstr e heI
  have hFG := hRS.2.2.2.2.2.2 e heF
  have htV : S.RF.F.tail e ∈ S.G.V := hRS.2.1 ▸ (hRS.1.1 e heF).1
  have hu : S.RF.F.tail e ∈ S.RF.R ∧ S.RF.F.Connected (S.RF.F.tail e) (S.RF.F.tail e) :=
    ⟨hFG.1 ▸ hw.2.1, ⟨[], MGraph.IsWalk.nil _⟩⟩
  have hv : S.RF.F.head e ∈ S.RF.R ∧ S.RF.F.Connected (S.RF.F.tail e) (S.RF.F.head e) :=
    ⟨hFG.2 ▸ hw.2.2, ⟨[(e, true)], .cons heF rfl (.nil _)⟩⟩
  obtain ⟨r, _, huniq⟩ := hRS.2.2.2.1 _ htV
  have hth : S.RF.F.tail e = S.RF.F.head e := (huniq _ hu).trans (huniq _ hv).symm
  exact hRS.1.2 [(e, true)] ⟨by simp, by simp, S.RF.F.tail e,
    .cons heF rfl (by simpa [MGraph.dst, hth] using MGraph.IsWalk.nil (S.RF.F.tail e))⟩

lemma compLSF_comp_sdiff_sub {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C : Finset ℕ} (hC : C ∈ components cs.G₀) :
    (cs.compSt C).G.E \ (cs.compSt C).RF.F.E ⊆ cs.G.E \ cs.RF.F.E := by
  intro e he
  rcases Finset.mem_sdiff.mp he with ⟨heG, hnF⟩
  refine Finset.mem_sdiff.mpr ⟨hI.hCE_sub C hC heG, fun heRF => ?_⟩
  change e ∈ (components cs.G₀).biUnion (fun C' => (cs.compSt C').RF.F.E) at heRF
  rw [Finset.mem_biUnion] at heRF
  rcases heRF with ⟨C', hC', heC'⟩
  by_cases hEq : C' = C
  · exact hnF (hEq ▸ heC')
  · have hCI := (hI.hCompLSF C hC).1
    have hCI' := (hI.hCompLSF C' hC').1
    have heG' : e ∈ (cs.compSt C').G.E := (lsfInv_to_RS hCI').2.2.2.2.2.1 heC'
    have hni' : e ∉ (cs.compSt C').insertedEdges := lsfInv_RF_edge_not_inserted hCI' heC'
    by_cases hins : e ∈ (cs.compSt C).insertedEdges
    · exact hni' (hI.hCE_ins C' hC' e heG' (hI.hCompIns_sub C hC hins))
    · have he₀ : e ∈ (cs.compSt C).G₀.E := (hCI.hsurv_edge e heG hins).1
      rw [(hI.hCompLSF C hC).2.1] at he₀
      exact Finset.disjoint_left.mp (compEdgeSet_pairwiseDisjoint cs.G₀ hC hC' fun h => hEq h.symm)
        he₀ (hI.hF_sub_compE C' hC' heC')

lemma compLSF_crossEdges_sub {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) : cs.crossEdges ⊆ cs.G.E \ cs.RF.F.E := by
  intro e he
  have hIns := hI.hCross_sub he
  refine Finset.mem_sdiff.mpr ⟨hI.hIns_sub hIns, fun heRF => ?_⟩
  change e ∈ (components cs.G₀).biUnion (fun C' => (cs.compSt C').RF.F.E) at heRF
  rw [Finset.mem_biUnion] at heRF
  rcases heRF with ⟨C', hC', heC'⟩
  have hCI' := (hI.hCompLSF C' hC').1
  have heG' : e ∈ (cs.compSt C').G.E := (lsfInv_to_RS hCI').2.2.2.2.2.1 heC'
  exact lsfInv_RF_edge_not_inserted hCI' heC' (hI.hCE_ins C' hC' e heG' hIns)

lemma compLSF_crossEdges_sdiff_prev (cs : CompLSFState) (U : List Update) :
    cs.crossEdges \ (compLSFBatch cs U).crossEdges ⊆ batchDeletes U := by
  intro e he
  rw [mem_batchDeletes_iff]
  induction U generalizing cs with
  | nil =>
    rw [Finset.mem_sdiff] at he
    exact absurd he.1 he.2
  | cons u rest ih =>
    rw [Finset.mem_sdiff] at he
    by_cases h1 : e ∈ (compLSFStepSingle cs u).crossEdges
    · rcases ih (compLSFStepSingle cs u) (Finset.mem_sdiff.mpr ⟨h1, he.2⟩) with ⟨w, hw, hwEq⟩
      exact ⟨w, List.mem_cons_of_mem u hw, hwEq⟩
    · cases u with
      | delete e' =>
        dsimp only [compLSFStepSingle] at h1
        by_cases heq : e = e'
        · subst heq; exact ⟨.delete e, List.mem_cons_self, rfl⟩
        · exact absurd (Finset.mem_erase.mpr ⟨heq, he.1⟩) h1
      | insert _ _ _ =>
        exfalso
        dsimp only [compLSFStepSingle] at h1
        split_ifs at h1
        · exact h1 he.1
        · exact h1 (Finset.mem_insert_of_mem he.1)
      | split _ _ _ _ => exact absurd he.1 h1

lemma compLSF_crossEdges_sdiff_cur (U : List Update) (cs : CompLSFState) :
    ((compLSFBatch cs U).crossEdges \ cs.crossEdges).card ≤ U.length := by
  induction U generalizing cs with
  | nil => simp [compLSFBatch]
  | cons u rest ih =>
    set cs1 := compLSFStepSingle cs u
    have hsub : (compLSFBatch cs1 rest).crossEdges \ cs.crossEdges ⊆
        ((compLSFBatch cs1 rest).crossEdges \ cs1.crossEdges) ∪ (cs1.crossEdges \ cs.crossEdges) := by
      intro e he
      rw [Finset.mem_sdiff] at he
      by_cases h1 : e ∈ cs1.crossEdges
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h1, he.2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he.1, h1⟩)
    have h1_card : (cs1.crossEdges \ cs.crossEdges).card ≤ 1 := by
      cases u with
      | delete _ =>
        have : cs1.crossEdges \ cs.crossEdges = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr (Finset.erase_subset _ _)
        rw [this]; simp
      | insert e _ _ =>
        dsimp only [cs1, compLSFStepSingle]
        split_ifs
        · simp
        · exact le_trans (Finset.card_le_card fun x hx => by
            rw [Finset.mem_sdiff, Finset.mem_insert] at hx
            rcases hx with ⟨rfl | hx1, hx2⟩
            · exact Finset.mem_singleton_self _
            · exact absurd hx1 hx2) (by simp)
      | split _ _ _ _ => simp [cs1, compLSFStepSingle]
    have h2 := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have h3 := ih cs1
    change ((compLSFBatch cs1 rest).crossEdges \ cs.crossEdges).card ≤ rest.length + 1
    omega

lemma compLSF_sum_R_sdiff_eq {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs cs' : CompLSFState}
    (_hI : CompLSFInv C_lsst ℓ₀ cs) (hI' : CompLSFInv C_lsst ℓ₀ cs')
    (hG₀ : cs'.G₀ = cs.G₀) (hR_mono : ∀ C ∈ components cs.G₀, (cs.compSt C).R ⊆ (cs'.compSt C).R) :
    ((components cs.G₀).sum fun C => ((cs'.compSt C).R \ (cs.compSt C).R).card) =
      (cs'.RF.R \ cs.RF.R).card := by
  have hdisj : Set.PairwiseDisjoint (↑(components cs.G₀) : Set (Finset ℕ))
      (fun C => (cs'.compSt C).R \ (cs.compSt C).R) := by
    intro C₁ hC₁ C₂ hC₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx₁ hx₂
    have hR₁ := lsfInv_R_sub_V (hI'.hCompLSF C₁ (hG₀ ▸ hC₁)).1 (Finset.mem_sdiff.mp hx₁).1
    have hR₂ := lsfInv_R_sub_V (hI'.hCompLSF C₂ (hG₀ ▸ hC₂)).1 (Finset.mem_sdiff.mp hx₂).1
    exact Finset.disjoint_left.mp (hI'.hV_disj C₁ (hG₀ ▸ hC₁) C₂ (hG₀ ▸ hC₂) hne) hR₁ hR₂
  have hbi : (components cs.G₀).biUnion (fun C => (cs'.compSt C).R \ (cs.compSt C).R) =
      cs'.RF.R \ cs.RF.R := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_sdiff]
    constructor
    · rintro ⟨C, hC, hx', hnx⟩
      refine ⟨Finset.mem_biUnion.mpr ⟨C, hG₀ ▸ hC, hx'⟩, fun hxR => ?_⟩
      change x ∈ (components cs.G₀).biUnion (fun C' => (cs.compSt C').R) at hxR
      rw [Finset.mem_biUnion] at hxR
      rcases hxR with ⟨C', hC', hxC'⟩
      have hxC'' : x ∈ (cs'.compSt C').R := hR_mono C' hC' hxC'
      by_cases hEq : C' = C
      · exact hnx (hEq ▸ hxC')
      · have hR₁ := lsfInv_R_sub_V (hI'.hCompLSF C (hG₀ ▸ hC)).1 hx'
        have hR₂ := lsfInv_R_sub_V (hI'.hCompLSF C' (hG₀ ▸ hC')).1 hxC''
        exact Finset.disjoint_left.mp (hI'.hV_disj C (hG₀ ▸ hC) C' (hG₀ ▸ hC') fun h => hEq h.symm)
          hR₁ hR₂
    · rintro ⟨hx', hnx⟩
      change x ∈ (components cs'.G₀).biUnion (fun C => (cs'.compSt C).R) at hx'
      rw [Finset.mem_biUnion] at hx'
      rcases hx' with ⟨C, hC, hxC⟩
      rw [hG₀] at hC
      exact ⟨C, hC, hxC, fun hxold => hnx (Finset.mem_biUnion.mpr ⟨C, hC, hxold⟩)⟩
  rw [← Finset.card_biUnion hdisj, hbi]

lemma smallComp_tildeV_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {C : Finset ℕ} (hC : C ∈ components G₀)
    (hNL : C ∉ largeComps k G₀) :
    let cs₀ := initCompLSF oracle C_lsst G₀ ℓ₀ k j
    (initTildeState (cs₀.compSt C)).C.V.card ≤ 11 := by
  intro cs₀
  have hlt : 4 * (compGraph G₀ C).m < k := by
    by_contra hge
    push Not at hge
    have hm1 : 1 ≤ (compGraph G₀ C).m := by
      have : 0 < 4 * (compGraph G₀ C).m := lt_of_lt_of_le hk hge
      omega
    exact hNL (Finset.mem_filter.mpr ⟨hC, hm1, hge⟩)
  have hℓs : ∀ e ∈ G₀.E, 0 < safeLen G₀ ℓ₀ e := fun e he => by
    rw [safeLen_eq_of_mem ℓ₀ he]; exact hℓ₀ e he
  exact (initLSF_small_props hLSST hG₀ hℓs hk hC hlt j).2.2.1

lemma largeComps_card_le {k : ℕ} (hk : 1 ≤ k) {G₀ : MGraph} (hG₀ : G₀.IsValid) :
    ((largeComps k G₀).card : ℝ) ≤ 4 * (G₀.m : ℝ) / (k : ℝ) ∧
      (largeComps k G₀).card ≤ G₀.m := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsum_m : (largeComps k G₀).sum (fun C => (compGraph G₀ C).m) ≤ G₀.m :=
    le_trans (Finset.sum_le_sum_of_subset largeComps_sub) (components_sum_m G₀ hG₀).le
  have hnat1 : (largeComps k G₀).card ≤ (largeComps k G₀).sum (fun C => (compGraph G₀ C).m) := by
    calc (largeComps k G₀).card
        = (largeComps k G₀).sum (fun _ => 1) := Finset.card_eq_sum_ones _
      _ ≤ (largeComps k G₀).sum (fun C => (compGraph G₀ C).m) :=
          Finset.sum_le_sum fun C hC => (Finset.mem_filter.mp hC).2.1
  have hnat2 : (largeComps k G₀).card * k ≤ 4 * G₀.m := by
    calc (largeComps k G₀).card * k
        = (largeComps k G₀).sum (fun _ => k) := by simp [Finset.sum_const, smul_eq_mul]
      _ ≤ (largeComps k G₀).sum (fun C => 4 * (compGraph G₀ C).m) :=
          Finset.sum_le_sum fun C hC => (Finset.mem_filter.mp hC).2.2
      _ = 4 * (largeComps k G₀).sum (fun C => (compGraph G₀ C).m) := by rw [← Finset.mul_sum]
      _ ≤ 4 * G₀.m := Nat.mul_le_mul_left 4 hsum_m
  have hr : ((largeComps k G₀).card : ℝ) * (k : ℝ) ≤ 4 * (G₀.m : ℝ) := by exact_mod_cast hnat2
  exact ⟨(le_div_iff₀ hk_pos).mpr hr, le_trans hnat1 hsum_m⟩


end

end MinCostFlow.SparseCore
