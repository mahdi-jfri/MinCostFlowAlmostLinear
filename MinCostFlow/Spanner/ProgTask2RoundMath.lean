module

public import MinCostFlow.Spanner.ProgTask2InitMath

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Claim 8.7 round shrinkage and round-count bound -/

private lemma sum_biUnion_le_of_nonneg {ι : Type*} (s : Finset ι) (t : ι → Finset ℕ)
    (f : ℕ → ℝ) (hf : ∀ i ∈ s, ∀ x ∈ t i, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hf_s : ∀ i ∈ s, ∀ x ∈ t i, 0 ≤ f x := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hunion : ∑ x ∈ t a ∪ s.biUnion t, f x ≤
        ∑ x ∈ t a, f x + ∑ x ∈ s.biUnion t, f x := by
      have hsplit : t a ∪ s.biUnion t = t a ∪ (s.biUnion t \ t a) := (Finset.union_sdiff_self_eq_union).symm
      rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
      refine add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun x hx _ => ?_)
      rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxt⟩
      exact hf_s i hi x hxt
    exact le_trans hunion (add_le_add le_rfl (ih hf_s))

lemma t2Round_math_spec {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    (hembJH : IsEmbedding inp.prep.J inp.H' inp.embJH)
    {η_prev : ℕ} {emb₀ emb₁ : ℕ → Option Walk}
    {procVerts : Finset ℕ} {delJ vhatJ : ℕ → Finset ℕ}
    (hmono : ∀ eW < (inp.mkWitnessData ce pds WSubs).W.m, emb₀ eW = none ∨ emb₁ eW = emb₀ eW)
    (hpart : IsPartialEmbedding (inp.mkWitnessData ce pds WSubs).W inp.prep.J emb₁)
    (hj0 : ∀ eW < (inp.mkWitnessData ce pds WSubs).j0Edges.length, (emb₁ eW).isSome = true)
    (helen : ∀ eW < (inp.mkWitnessData ce pds WSubs).W.m,
      ((partialToWalk emb₁ eW).edges.length : ℝ) ≤ (inp.mkWitnessData ce pds WSubs).γ_ExpPath)
    (hvcong_prev : ∀ x < inp.H'.n,
      vcongAt (inp.mkWitnessData ce pds WSubs).W (inp.mkWitnessData ce pds WSubs).wW
        (compose inp.prep.J inp.embJH (partialToWalk emb₀)) x ≤
        ((η_prev : ℝ) + 1 / 2) * (inp.mkWitnessData ce pds WSubs).τ₁)
    (hproc_sub : ∀ x ∈ procVerts,
      x < inp.H'.n ∧
      ((η_prev + 1 : ℕ) : ℝ) * (inp.mkWitnessData ce pds WSubs).τ₁ ≤
        vcongAt (inp.mkWitnessData ce pds WSubs).W (inp.mkWitnessData ce pds WSubs).wW
          (compose inp.prep.J inp.embJH (partialToWalk emb₁)) x)
    (hvhat_sub : ∀ (ci : ℕ) (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length),
      vhatJ ci ⊆ (inp.mkWitnessData ce pds WSubs).comps[ci].J_sub.verts)
    (hvhat_vol : ∀ (ci : ℕ) (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length),
      ((inp.mkWitnessData ce pds WSubs).comps[ci].J_sub.vol (vhatJ ci) : ℝ) ≤
        (inp.mkWitnessData ce pds WSubs).γ_del * ((delJ ci).card : ℝ) /
          (inp.mkWitnessData ce pds WSubs).φ_ds)
    (hdel_sub_proc : ∀ (ci : ℕ) (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length) (b : ℕ),
      b ∈ delJ ci → b < (inp.mkWitnessData ce pds WSubs).comps[ci].J_sub.m ∧
        ∃ x ∈ procVerts, x ∈ (inp.embJH ((inp.mkWitnessData ce pds WSubs).comps[ci].jSubOrigEdges.getD b 0)).verts)
    (hmid_done : ∀ (ci : ℕ) (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length) (eL : ℕ),
      eL < (inp.mkWitnessData ce pds WSubs).comps[ci].W_sub.m →
      emb₁ ((inp.mkWitnessData ce pds WSubs).comps[ci].wStart + eL) = none →
      ((inp.mkWitnessData ce pds WSubs).comps[ci].W_sub.edges.getD eL (0, 0)).1 ∈ vhatJ ci ∨
        ((inp.mkWitnessData ce pds WSubs).comps[ci].W_sub.edges.getD eL (0, 0)).2 ∈ vhatJ ci)
    (hzero_proc : (inp.mkWitnessData ce pds WSubs).W.m = 0 → procVerts = ∅ ∧
      ∀ ci < (inp.mkWitnessData ce pds WSubs).comps.length, delJ ci = ∅) :
    let wd := inp.mkWitnessData ce pds WSubs
    let E_embed := (Finset.range wd.W.m).filter fun eW => (emb₀ eW).isNone = true ∧ (emb₁ eW).isSome = true
    volWRemPure wd emb₁ ≤ (2 * wd.c_deg) * (∑ eW ∈ E_embed, wd.wW eW) ∧
    volWRemPure wd emb₁ ≤ ((2 * wd.c_deg) / (2 * wd.c_deg + 1)) * volWRemPure wd emb₀ ∧
    ∑ ci ∈ Finset.range wd.comps.length, (delJ ci).card ≤ inp.prep.J.m ∧
    procVerts.card ≤ inp.H'.n ∧
    ((procVerts.card : ℕ) : ℝ) ≤ (E_embed.card : ℝ) * (wd.γ_ExpPath * ((length inp.prep.J inp.embJH : ℝ) + 1)) := by
  intro wd E_embed
  have hcdeg_nn : 0 ≤ wd.c_deg := le_trans (by norm_num) hok.c_deg_ge
  have hφds_pos : 0 < wd.φ_ds := hok.φ_ds_pos
  have hγD_pos : 0 < wd.γ_del := by linarith [hok.γ_del_ge]
  have hγE_pos : 0 < wd.γ_ExpPath := by
    have : 0 < 1 / wd.φ_ds := by positivity
    linarith [hok.γ_ExpPath_ge]
  have hpart_set : unembeddedSetPure wd emb₀ = E_embed ∪ unembeddedSetPure wd emb₁ := by
    ext eW
    simp only [unembeddedSetPure, E_embed, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro ⟨hm, h0⟩
      cases h1 : emb₁ eW with
      | none => exact Or.inr ⟨hm, by simp⟩
      | some P => exact Or.inl ⟨hm, h0, by simp⟩
    · intro h
      rcases h with ⟨hm, h0, _⟩ | ⟨hm, h1⟩
      · exact ⟨hm, h0⟩
      · refine ⟨hm, ?_⟩
        rcases hmono eW hm with h0 | h10
        · simp [h0]
        · rw [h10] at h1; exact h1
  have hdisj : Disjoint E_embed (unembeddedSetPure wd emb₁) := by
    rw [Finset.disjoint_left]
    intro eW hE hU
    have hE1 := (Finset.mem_filter.mp hE).2.2
    have hU1 := (Finset.mem_filter.mp hU).2
    rw [Option.isSome_iff_ne_none] at hE1
    rw [Option.isNone_iff_eq_none] at hU1
    exact hE1 hU1
  have hvol_part : volWRemPure wd emb₀ = (∑ eW ∈ E_embed, wd.wW eW) + volWRemPure wd emb₁ := by
    unfold volWRemPure
    rw [hpart_set, Finset.sum_union hdisj]
  let delImg : ℕ → Finset ℕ := fun ci =>
    (delJ ci).image (fun b => (wd.comps.getD ci defaultCompInfo).jSubOrigEdges.getD b 0)
  let deletedEdges := (Finset.range wd.comps.length).biUnion delImg
  have hdel_card_eq : ∑ ci ∈ Finset.range wd.comps.length, (delJ ci).card = deletedEdges.card := by
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun ci hci_r => ?_
      have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
      dsimp only [delImg]; rw [Finset.card_image_of_injOn]
      intro a ha b hb hab
      dsimp only at hab
      rw [List.getD_eq_getElem _ _ hci] at hab
      have ha_m := (hdel_sub_proc ci hci a ha).1
      have hb_m := (hdel_sub_proc ci hci b hb).1
      have hjLen := (hok.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hjNd := (hok.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have ha_l : a < wd.comps[ci].jSubOrigEdges.length := by rw [hjLen]; exact ha_m
      have hb_l : b < wd.comps[ci].jSubOrigEdges.length := by rw [hjLen]; exact hb_m
      rw [List.getD_eq_getElem _ _ ha_l, List.getD_eq_getElem _ _ hb_l] at hab
      exact congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hjNd) (a₁ := ⟨a, ha_l⟩) (a₂ := ⟨b, hb_l⟩) hab)
    · intro c1 h1 c2 h2 hne
      have h1' := Finset.mem_range.mp h1
      have h2' := Finset.mem_range.mp h2
      change Disjoint (delImg c1) (delImg c2)
      dsimp only [delImg]; rw [Finset.disjoint_left]
      intro j hj1 hj2
      rcases Finset.mem_image.mp hj1 with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hj2 with ⟨b, hb, hab⟩
      rw [List.getD_eq_getElem _ _ h1', List.getD_eq_getElem _ _ h2'] at hab
      have ha_l : a < wd.comps[c1].jSubOrigEdges.length := by
        rw [(hok.comp_props c1 h1').2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
        exact (hdel_sub_proc c1 h1' a ha).1
      have hb_l : b < wd.comps[c2].jSubOrigEdges.length := by
        rw [(hok.comp_props c2 h2').2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
        exact (hdel_sub_proc c2 h2' b hb).1
      have hm1 : wd.comps[c1].jSubOrigEdges.getD a 0 ∈ wd.comps[c1].jSubOrigEdges.toFinset := by
        rw [List.mem_toFinset, List.getD_eq_getElem _ _ ha_l]; exact List.getElem_mem ha_l
      have hm2 : wd.comps[c2].jSubOrigEdges.getD b 0 ∈ wd.comps[c2].jSubOrigEdges.toFinset := by
        rw [List.mem_toFinset, List.getD_eq_getElem _ _ hb_l]; exact List.getElem_mem hb_l
      rw [← hab] at hm1
      exact Finset.disjoint_left.mp (hok.comp_disjoint c1 c2 h1' h2' hne) hm1 hm2
  have hdel_sub_J : deletedEdges ⊆ Finset.range inp.prep.J.m := by
    intro j hj
    rcases Finset.mem_biUnion.mp hj with ⟨ci, hci_r, hjci⟩
    have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
    dsimp only [delImg] at hjci
    rcases Finset.mem_image.mp hjci with ⟨b, hb, rfl⟩
    rw [List.getD_eq_getElem _ _ hci]
    have hb_l : b < wd.comps[ci].jSubOrigEdges.length := by
      rw [(hok.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
      exact (hdel_sub_proc ci hci b hb).1
    rw [Finset.mem_range, List.getD_eq_getElem _ _ hb_l]
    exact (hok.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (List.getElem_mem hb_l)
  have hdel_le_J : ∑ ci ∈ Finset.range wd.comps.length, (delJ ci).card ≤ inp.prep.J.m := by
    rw [hdel_card_eq]; exact (Finset.card_le_card hdel_sub_J).trans_eq (Finset.card_range inp.prep.J.m)
  have hproc_H : procVerts.card ≤ inp.H'.n := by
    have hsub : procVerts ⊆ Finset.range inp.H'.n := fun x hx => Finset.mem_range.mpr (hproc_sub x hx).1
    exact (Finset.card_le_card hsub).trans_eq (Finset.card_range inp.H'.n)
  by_cases hW0 : wd.W.m = 0
  · obtain ⟨hp0, _⟩ := hzero_proc hW0
    have hu1 : volWRemPure wd emb₁ = 0 := by simp [volWRemPure, unembeddedSetPure, hW0]
    have hu0 : volWRemPure wd emb₀ = 0 := by simp [volWRemPure, unembeddedSetPure, hW0]
    have hE0 : (∑ eW ∈ E_embed, wd.wW eW) = 0 := by
      have : E_embed = ∅ := by simp [E_embed, hW0]
      rw [this, Finset.sum_empty]
    rw [hu1, hu0, hE0]
    refine ⟨by norm_num, by norm_num, hdel_le_J, by simp [hp0], by simp [hp0]; positivity⟩
  have hWpos : 0 < wd.W.m := Nat.pos_of_ne_zero hW0
  obtain ⟨hmaxD, hlenJ⟩ := mkW_maxDeg_pos_of_W_pos hs hok hws hembJH hWpos
  have hsc := inp.mkWitnessData_scalars ce pds WSubs hs
  have hvcong_inc : ∀ x ∈ procVerts,
      wd.τ₁ / 2 ≤ ∑ eW ∈ E_embed,
        if x ∈ (compose inp.prep.J inp.embJH (partialToWalk emb₁) eW).verts then wd.wW eW else 0 := by
    intro x hx
    have hx_sub := hproc_sub x hx
    have hdiff : wd.τ₁ / 2 ≤
        vcongAt wd.W wd.wW (compose inp.prep.J inp.embJH (partialToWalk emb₁)) x -
          vcongAt wd.W wd.wW (compose inp.prep.J inp.embJH (partialToWalk emb₀)) x := by
      have h1 := hx_sub.2
      have h0 := hvcong_prev x hx_sub.1
      push_cast at h1
      linarith only [h1, h0]
    have hmono_diff := vcongAt_mono_diff wd.W inp.prep.J wd.wW inp.embJH emb₀ emb₁ hmono x
    have hsum_eq : (∑ eW ∈ (Finset.range wd.W.m).filter (fun eW =>
          (emb₀ eW).isNone = true ∧ (emb₁ eW).isSome = true ∧
            x ∈ (compose inp.prep.J inp.embJH (partialToWalk emb₁) eW).verts), wd.wW eW) =
        ∑ eW ∈ E_embed,
          if x ∈ (compose inp.prep.J inp.embJH (partialToWalk emb₁) eW).verts then wd.wW eW else 0 := by
      rw [Finset.sum_filter]; dsimp only [E_embed]; rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun eW _ => ?_
      by_cases h1 : (emb₀ eW).isNone = true <;>
        by_cases h2 : (emb₁ eW).isSome = true <;>
        by_cases h3 : x ∈ (compose inp.prep.J inp.embJH (partialToWalk emb₁) eW).verts <;>
        simp [h1, h2, h3]
    rw [hsum_eq] at hmono_diff
    linarith only [hdiff, hmono_diff]
  have hverts_le : ∀ eW ∈ E_embed,
      ((compose inp.prep.J inp.embJH (partialToWalk emb₁) eW).verts.toFinset.card : ℝ) ≤
        wd.γ_ExpPath * ((length inp.prep.J inp.embJH : ℝ) + 1) := by
    intro eW heW
    have hm := Finset.mem_range.mp (Finset.mem_filter.mp heW).1
    have hs := (Finset.mem_filter.mp heW).2.2
    rcases Option.isSome_iff_exists.mp hs with ⟨P, hP⟩
    have hwalk := hpart.2 eW hm P hP
    have hpw : partialToWalk emb₁ eW = P := by simp [partialToWalk, hP]
    have hPedges : ∀ j ∈ P.edges, j < inp.prep.J.m :=
      hwalk.2.2.elim (fun h => by simp [h.2.1]) (fun h => h.2.2.2.2.1)
    have hcard := verts_toFinset_compose_card_le hembJH hPedges
    have hlen := helen eW hm
    change ((composeAux inp.prep.J inp.embJH (partialToWalk emb₁ eW).verts
      (partialToWalk emb₁ eW).edges).verts.toFinset.card : ℝ) ≤ _
    rw [hpw]
    exact le_trans hcard (mul_le_mul_of_nonneg_right (hpw ▸ hlen) (by positivity))
  have hsum_proc : (procVerts.card : ℝ) * (wd.τ₁ / 2) ≤
      (∑ eW ∈ E_embed, wd.wW eW) * (wd.γ_ExpPath * ((length inp.prep.J inp.embJH : ℝ) + 1)) := by
    calc (procVerts.card : ℝ) * (wd.τ₁ / 2)
        = ∑ _x ∈ procVerts, (wd.τ₁ / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ procVerts, ∑ eW ∈ E_embed,
            if x ∈ (compose inp.prep.J inp.embJH (partialToWalk emb₁) eW).verts then wd.wW eW else 0 :=
          Finset.sum_le_sum hvcong_inc
      _ = ∑ eW ∈ E_embed, ∑ x ∈ procVerts,
            if x ∈ (compose inp.prep.J inp.embJH (partialToWalk emb₁) eW).verts then wd.wW eW else 0 :=
          Finset.sum_comm
      _ ≤ ∑ eW ∈ E_embed, wd.wW eW * (wd.γ_ExpPath * ((length inp.prep.J inp.embJH : ℝ) + 1)) := by
          refine Finset.sum_le_sum fun eW heW => ?_
          have hsub_card : (procVerts.filter fun x =>
              x ∈ (compose inp.prep.J inp.embJH (partialToWalk emb₁) eW).verts).card ≤
              (compose inp.prep.J inp.embJH (partialToWalk emb₁) eW).verts.toFinset.card := by
            refine Finset.card_le_card fun x hx => ?_
            exact List.mem_toFinset.mpr (Finset.mem_filter.mp hx).2
          have hinner : ∑ x ∈ procVerts,
              (if x ∈ (compose inp.prep.J inp.embJH (partialToWalk emb₁) eW).verts then wd.wW eW else 0) =
              ((procVerts.filter fun x =>
                x ∈ (compose inp.prep.J inp.embJH (partialToWalk emb₁) eW).verts).card : ℝ) * wd.wW eW := by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          rw [hinner]
          have hww_nn := (mkW_wW_pos hok hws (Finset.mem_range.mp (Finset.mem_filter.mp heW).1)).le
          calc ((procVerts.filter _).card : ℝ) * wd.wW eW
              ≤ ((compose inp.prep.J inp.embJH (partialToWalk emb₁) eW).verts.toFinset.card : ℝ) * wd.wW eW :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hsub_card) hww_nn
            _ ≤ (wd.γ_ExpPath * ((length inp.prep.J inp.embJH : ℝ) + 1)) * wd.wW eW :=
                mul_le_mul_of_nonneg_right (hverts_le eW heW) hww_nn
            _ = wd.wW eW * (wd.γ_ExpPath * ((length inp.prep.J inp.embJH : ℝ) + 1)) := mul_comm _ _
      _ = (∑ eW ∈ E_embed, wd.wW eW) * (wd.γ_ExpPath * ((length inp.prep.J inp.embJH : ℝ) + 1)) := by
          rw [← Finset.sum_mul]
  have hinner_le : ((procVerts.card : ℕ) : ℝ) ≤
      (E_embed.card : ℝ) * (wd.γ_ExpPath * ((length inp.prep.J inp.embJH : ℝ) + 1)) := by
    have hmax_half : (maxDeg inp.prep.J : ℝ) ≤ wd.τ₁ / 2 := mkW_maxDeg_le_tau_half hs hok hlenJ
    have hmax_pos : (0 : ℝ) < (maxDeg inp.prep.J : ℝ) := by exact_mod_cast hmaxD
    have hτh_pos : 0 < wd.τ₁ / 2 := lt_of_lt_of_le hmax_pos hmax_half
    have hsum_w_le : ∑ eW ∈ E_embed, wd.wW eW ≤ (E_embed.card : ℝ) * (wd.τ₁ / 2) := by
      calc ∑ eW ∈ E_embed, wd.wW eW
          ≤ ∑ _eW ∈ E_embed, (wd.τ₁ / 2) :=
            Finset.sum_le_sum fun eW heW =>
              le_trans (mkW_wW_le_maxDeg hs hok hws (Finset.mem_range.mp (Finset.mem_filter.mp heW).1)) hmax_half
        _ = (E_embed.card : ℝ) * (wd.τ₁ / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hmul : (procVerts.card : ℝ) * (wd.τ₁ / 2) ≤
        ((E_embed.card : ℝ) * (wd.γ_ExpPath * ((length inp.prep.J inp.embJH : ℝ) + 1))) * (wd.τ₁ / 2) := by
      calc (procVerts.card : ℝ) * (wd.τ₁ / 2)
          ≤ (∑ eW ∈ E_embed, wd.wW eW) * (wd.γ_ExpPath * ((length inp.prep.J inp.embJH : ℝ) + 1)) := hsum_proc
        _ ≤ ((E_embed.card : ℝ) * (wd.τ₁ / 2)) * (wd.γ_ExpPath * ((length inp.prep.J inp.embJH : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hsum_w_le (by positivity)
        _ = _ := by ring
    exact le_of_mul_le_mul_right hmul hτh_pos
  have hdel_le_vcong : ∑ ci ∈ Finset.range wd.comps.length, (delJ ci).card ≤
      procVerts.card * vcongNat inp.prep.J inp.H' inp.embJH := by
    have hsub_proc : deletedEdges ⊆
        procVerts.biUnion fun x => (Finset.range inp.prep.J.m).filter fun j => x ∈ (inp.embJH j).verts := by
      intro j hj
      rcases Finset.mem_biUnion.mp hj with ⟨ci, hci_r, hjci⟩
      have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
      dsimp only [delImg] at hjci
      rcases Finset.mem_image.mp hjci with ⟨b, hb, rfl⟩
      rw [List.getD_eq_getElem _ _ hci]
      obtain ⟨hb_m, x, hx_p, hx_e⟩ := hdel_sub_proc ci hci b hb
      refine Finset.mem_biUnion.mpr ⟨x, hx_p, Finset.mem_filter.mpr ⟨?_, hx_e⟩⟩
      have hb_l : b < wd.comps[ci].jSubOrigEdges.length := by
        rw [(hok.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hb_m
      rw [Finset.mem_range, List.getD_eq_getElem _ _ hb_l]
      exact (hok.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (List.getElem_mem hb_l)
    calc ∑ ci ∈ Finset.range wd.comps.length, (delJ ci).card
        = deletedEdges.card := hdel_card_eq
      _ ≤ (procVerts.biUnion fun x => (Finset.range inp.prep.J.m).filter fun j => x ∈ (inp.embJH j).verts).card :=
          Finset.card_le_card hsub_proc
      _ ≤ ∑ x ∈ procVerts, ((Finset.range inp.prep.J.m).filter fun j => x ∈ (inp.embJH j).verts).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ procVerts, vcongNat inp.prep.J inp.H' inp.embJH := by
          refine Finset.sum_le_sum fun x hx => ?_
          rw [Finset.card_filter]
          unfold vcongNat
          simp_rw [← Finset.card_filter]
          exact Finset.le_sup (f := fun v =>
            ((Finset.range inp.prep.J.m).filter fun e => v ∈ (inp.embJH e).verts).card)
            (Finset.mem_range.mpr (hproc_sub x hx).1)
      _ = procVerts.card * vcongNat inp.prep.J inp.H' inp.embJH := by rw [Finset.sum_const, smul_eq_mul]
  have hvol_mid : volWRemPure wd emb₁ ≤
      wd.c_deg * wd.γ_del * (vcongNat inp.prep.J inp.H' inp.embJH : ℝ) / wd.φ_ds * (procVerts.card : ℝ) := by
    let unembComp : ℕ → Finset ℕ := fun ci =>
      ((Finset.range (wd.comps.getD ci defaultCompInfo).W_sub.m).filter fun eL =>
        (emb₁ ((wd.comps.getD ci defaultCompInfo).wStart + eL)).isNone)
    let unembImg : ℕ → Finset ℕ := fun ci =>
      (unembComp ci).image (fun eL => (wd.comps.getD ci defaultCompInfo).wStart + eL)
    have hcov : unembeddedSetPure wd emb₁ ⊆ (Finset.range wd.comps.length).biUnion unembImg := by
      intro eW heW
      rcases Finset.mem_filter.mp heW with ⟨hm, hnone⟩
      have heWm := Finset.mem_range.mp hm
      rcases mkW_W_edge_cases hws heWm with hj0_lt | ⟨ci, hci, eL, heL, rfl⟩
      · have hs := hj0 eW hj0_lt
        rw [Option.isSome_iff_ne_none] at hs
        rw [Option.isNone_iff_eq_none] at hnone
        exact absurd hnone hs
      · refine Finset.mem_biUnion.mpr ⟨ci, Finset.mem_range.mpr hci, ?_⟩
        dsimp only [unembImg, unembComp]
        rw [Finset.mem_image]
        exact ⟨eL, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by rw [List.getD_eq_getElem _ _ hci]; exact heL),
          by rw [List.getD_eq_getElem _ _ hci]; exact hnone⟩, by rw [List.getD_eq_getElem _ _ hci]⟩
    have hsum1 : volWRemPure wd emb₁ ≤ ∑ ci ∈ Finset.range wd.comps.length, ∑ eW ∈ unembImg ci, wd.wW eW := by
      have hunemb_nn : ∀ ci ∈ Finset.range wd.comps.length, ∀ eW ∈ unembImg ci, 0 ≤ wd.wW eW := by
        intro ci hci_r eW heWci
        have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
        dsimp only [unembImg, unembComp] at heWci
        rw [Finset.mem_image] at heWci
        rcases heWci with ⟨eL, heL, rfl⟩
        rw [List.getD_eq_getElem _ _ hci] at heL ⊢
        have heLm := Finset.mem_range.mp (Finset.mem_filter.mp heL).1
        exact (mkW_wW_pos hok hws (mkW_W_edges_comp hws hci heLm).1).le
      unfold volWRemPure
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hcov fun eW heW _ => ?_)
        (sum_biUnion_le_of_nonneg (Finset.range wd.comps.length) unembImg wd.wW hunemb_nn)
      rcases Finset.mem_biUnion.mp heW with ⟨ci, hci_r, heWci⟩
      exact hunemb_nn ci hci_r eW heWci
    have hsum2 : ∑ ci ∈ Finset.range wd.comps.length, ∑ eW ∈ unembImg ci, wd.wW eW ≤
        ∑ ci ∈ Finset.range wd.comps.length,
          wd.c_deg * wd.γ_del * ((delJ ci).card : ℝ) / wd.φ_ds := by
      refine Finset.sum_le_sum fun ci hci_r => ?_
      have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
      dsimp only [unembImg, unembComp]
      rw [List.getD_eq_getElem _ _ hci, Finset.sum_image (fun a _ b _ hab => by omega)]
      set c := wd.comps[ci]
      have hcongr : ∑ eL ∈ (Finset.range c.W_sub.m).filter (fun eL => (emb₁ (c.wStart + eL)).isNone),
            wd.wW (c.wStart + eL) =
          (((Finset.range c.W_sub.m).filter (fun eL => (emb₁ (c.wStart + eL)).isNone)).card : ℝ) *
            (wd.φ_dec * (2 ^ c.level : ℝ)) := by
        have hpt : ∑ eL ∈ (Finset.range c.W_sub.m).filter (fun eL => (emb₁ (c.wStart + eL)).isNone),
              wd.wW (c.wStart + eL) =
            ∑ _eL ∈ (Finset.range c.W_sub.m).filter (fun eL => (emb₁ (c.wStart + eL)).isNone),
              (wd.φ_dec * (2 ^ c.level : ℝ)) := by
          refine Finset.sum_congr rfl fun eL heL => ?_
          have heLm := Finset.mem_range.mp (Finset.mem_filter.mp heL).1
          exact (mkW_W_edges_comp hws hci heLm).2.2.2
        rw [hpt, Finset.sum_const, nsmul_eq_mul]
      rw [hcongr]
      have hcprops := hok.comp_props ci hci
      have hc_Wvalid : c.W_sub.IsValid := hcprops.2.2.2.2.2.2.2.2.2.2.2.2.1
      have htouch : ((Finset.range c.W_sub.m).filter (fun eL => (emb₁ (c.wStart + eL)).isNone)).card ≤
          c.W_sub.vol (vhatJ ci) := by
        refine card_edges_touching_le_vol c.W_sub (vhatJ ci) _ hc_Wvalid ?_ ?_
        · intro eL heL; exact (Finset.mem_filter.mp heL).1
        · intro eL heL
          have heLf := Finset.mem_filter.mp heL
          exact hmid_done ci hci eL (Finset.mem_range.mp heLf.1) (Option.isNone_iff_eq_none.mp heLf.2)
      have hφ := hok.φ_dec_pos
      have hvol_W_J : (c.W_sub.vol (vhatJ ci) : ℝ) * (wd.φ_dec * (2 ^ c.level : ℝ)) ≤
          wd.c_deg * (c.J_sub.vol (vhatJ ci) : ℝ) := by
        have hv_sub_r : vhatJ ci ⊆ Finset.range c.X.card := by
          simpa [Graph.verts, hcprops.2.2.2.2.2.1] using hvhat_sub ci hci
        have hWvol : (c.W_sub.vol (vhatJ ci) : ℝ) = ∑ k ∈ vhatJ ci, (c.W_sub.deg k : ℝ) := by
          unfold Graph.vol Graph.volIn Graph.deg
          rw [Nat.cast_sum]
        have hJvol : (c.J_sub.vol (vhatJ ci) : ℝ) = ∑ k ∈ vhatJ ci, (c.J_sub.deg k : ℝ) := by
          unfold Graph.vol Graph.volIn Graph.deg
          rw [Nat.cast_sum]
        rw [hWvol, hJvol, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_le_sum fun k hk => ?_
        have hkx := Finset.mem_range.mp (hv_sub_r hk)
        have hsand : (c.W_sub.deg k : ℝ) ≤ wd.c_deg * (c.J_sub.deg k : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ)) := by
          simpa only [mul_div_assoc'] using (hcprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k hkx).2
        have hdenom : 0 < wd.φ_dec * (2 ^ c.level : ℝ) := by positivity
        exact (le_div_iff₀ hdenom).mp hsand
      calc (((Finset.range c.W_sub.m).filter _).card : ℝ) * (wd.φ_dec * (2 ^ c.level : ℝ))
          ≤ (c.W_sub.vol (vhatJ ci) : ℝ) * (wd.φ_dec * (2 ^ c.level : ℝ)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast htouch) (by positivity)
        _ ≤ wd.c_deg * (c.J_sub.vol (vhatJ ci) : ℝ) := hvol_W_J
        _ ≤ wd.c_deg * (wd.γ_del * ((delJ ci).card : ℝ) / wd.φ_ds) :=
            mul_le_mul_of_nonneg_left (hvhat_vol ci hci) hcdeg_nn
        _ = wd.c_deg * wd.γ_del * ((delJ ci).card : ℝ) / wd.φ_ds := by ring
    have hsum3 : (∑ ci ∈ Finset.range wd.comps.length,
          wd.c_deg * wd.γ_del * ((delJ ci).card : ℝ) / wd.φ_ds) =
        wd.c_deg * wd.γ_del * ((∑ ci ∈ Finset.range wd.comps.length, (delJ ci).card : ℕ) : ℝ) / wd.φ_ds := by
      simp_rw [div_eq_mul_inv, mul_assoc, ← Finset.mul_sum, Nat.cast_sum]
      rw [← Finset.sum_mul]
    have hsum4 : wd.c_deg * wd.γ_del * ((∑ ci ∈ Finset.range wd.comps.length, (delJ ci).card : ℕ) : ℝ) / wd.φ_ds ≤
        wd.c_deg * wd.γ_del * (vcongNat inp.prep.J inp.H' inp.embJH : ℝ) / wd.φ_ds * (procVerts.card : ℝ) := by
      have hcast : ((∑ ci ∈ Finset.range wd.comps.length, (delJ ci).card : ℕ) : ℝ) ≤
          (procVerts.card : ℝ) * (vcongNat inp.prep.J inp.H' inp.embJH : ℝ) := by exact_mod_cast hdel_le_vcong
      have h1 : 0 ≤ wd.c_deg * wd.γ_del / wd.φ_ds := by positivity
      calc wd.c_deg * wd.γ_del * ((∑ ci ∈ Finset.range wd.comps.length, (delJ ci).card : ℕ) : ℝ) / wd.φ_ds
          = (wd.c_deg * wd.γ_del / wd.φ_ds) * ((∑ ci ∈ Finset.range wd.comps.length, (delJ ci).card : ℕ) : ℝ) := by ring
        _ ≤ (wd.c_deg * wd.γ_del / wd.φ_ds) * ((procVerts.card : ℝ) * (vcongNat inp.prep.J inp.H' inp.embJH : ℝ)) :=
            mul_le_mul_of_nonneg_left hcast h1
        _ = _ := by ring
    exact le_trans hsum1 (le_trans hsum2 (le_trans (le_of_eq hsum3) hsum4))
  have h1_le_L : (1 : ℝ) ≤ (length inp.prep.J inp.embJH : ℝ) := by exact_mod_cast hlenJ
  have hse_nn : 0 ≤ ∑ eW ∈ E_embed, wd.wW eW := Finset.sum_nonneg fun eW heW =>
    (mkW_wW_pos hok hws (Finset.mem_range.mp (Finset.mem_filter.mp heW).1)).le
  have htauh_eq : wd.τ₁ / 2 = wd.γ_ExpPath * (length inp.prep.J inp.embJH : ℝ) * wd.γ_del *
      ((vcongNat inp.prep.J inp.H' inp.embJH : ℝ) + (maxDeg inp.prep.J : ℝ)) / wd.φ_ds := by
    rw [hsc.2.2.2.2.2]
    unfold WitnessCoreInput.tau1Int WitnessCoreInput.tau2Int
    rw [hsc.2.1, hsc.2.2.1, hsc.2.2.2.1]
    have hden_ne : (inp.phiDsDenInt ce pds : ℝ) ≠ 0 := by
      have hp := hok.φ_ds_pos; rw [hsc.2.1] at hp
      exact ne_of_gt (by exact_mod_cast Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hp))
    push_cast; field_simp
  have hsP_alg : (procVerts.card : ℝ) * (wd.τ₁ / 2) ≤
      2 * wd.γ_ExpPath * (length inp.prep.J inp.embJH : ℝ) * (∑ eW ∈ E_embed, wd.wW eW) := by
    have hL2 : (length inp.prep.J inp.embJH : ℝ) + 1 ≤ 2 * (length inp.prep.J inp.embJH : ℝ) := by linarith
    have hγ_nn : 0 ≤ wd.γ_ExpPath := hγE_pos.le
    calc (procVerts.card : ℝ) * (wd.τ₁ / 2)
        ≤ (∑ eW ∈ E_embed, wd.wW eW) * (wd.γ_ExpPath * ((length inp.prep.J inp.embJH : ℝ) + 1)) := hsum_proc
      _ ≤ (∑ eW ∈ E_embed, wd.wW eW) * (wd.γ_ExpPath * (2 * (length inp.prep.J inp.embJH : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL2 hγ_nn) hse_nn
      _ = 2 * wd.γ_ExpPath * (length inp.prep.J inp.embJH : ℝ) * (∑ eW ∈ E_embed, wd.wW eW) := by ring
  have hV_le : volWRemPure wd emb₁ ≤ (2 * wd.c_deg) * (∑ eW ∈ E_embed, wd.wW eW) :=
    @claim_8_7_algebra (volWRemPure wd emb₁) (procVerts.card : ℝ) (wd.τ₁ / 2) wd.c_deg wd.γ_del wd.φ_ds
      (length inp.prep.J inp.embJH : ℝ) wd.γ_ExpPath (vcongNat inp.prep.J inp.H' inp.embJH : ℝ)
      (maxDeg inp.prep.J : ℝ) (∑ eW ∈ E_embed, wd.wW eW)
      hcdeg_nn hγD_pos hφds_pos (lt_of_lt_of_le (by norm_num) h1_le_L) hγE_pos
      (Nat.cast_nonneg _) (by exact_mod_cast hmaxD) hse_nn htauh_eq hvol_mid hsP_alg
  have hshrink : volWRemPure wd emb₁ ≤ ((2 * wd.c_deg) / (2 * wd.c_deg + 1)) * volWRemPure wd emb₀ := by
    have hsub_se : ∑ eW ∈ E_embed, wd.wW eW = volWRemPure wd emb₀ - volWRemPure wd emb₁ := by
      linarith only [hvol_part]
    rw [hsub_se] at hV_le
    have h2c_pos : 0 < 2 * wd.c_deg + 1 := by linarith only [hcdeg_nn]
    have hmul : (2 * wd.c_deg + 1) * volWRemPure wd emb₁ ≤ (2 * wd.c_deg) * volWRemPure wd emb₀ := by
      linarith only [hV_le]
    rw [div_mul_eq_mul_div, le_div_iff₀ h2c_pos]
    linarith only [hmul]
  exact ⟨hV_le, hshrink, hdel_le_J, hproc_H, hinner_le⟩

lemma t2Round_bound_of_unembedded {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph}
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    {η_prev : ℕ} {emb₀ : ℕ → Option Walk}
    (hj0 : ∀ eW < (inp.mkWitnessData ce pds WSubs).j0Edges.length, (emb₀ eW).isSome = true)
    (hunemb : (unembeddedSetPure (inp.mkWitnessData ce pds WSubs) emb₀).Nonempty)
    (hgeom : volWRemPure (inp.mkWitnessData ce pds WSubs) emb₀ ≤
      ((2 * (inp.mkWitnessData ce pds WSubs).c_deg) /
        (2 * (inp.mkWitnessData ce pds WSubs).c_deg + 1)) ^ η_prev *
        ((inp.mkWitnessData ce pds WSubs).c_deg * (inp.prep.J.m : ℝ))) :
    η_prev + 1 < eta1Bound (inp.mkWitnessData ce pds WSubs) inp.prep.J := by
  set wd := inp.mkWitnessData ce pds WSubs
  have hc2_pos : 0 < 2 * wd.c_deg := by linarith only [hok.c_deg_ge]
  have hφ2_pos : 0 < 2 * wd.φ_dec := by linarith only [hok.φ_dec_pos]
  have hVm_nn : 0 ≤ wd.c_deg * (inp.prep.J.m : ℝ) := by
    have : 0 ≤ wd.c_deg := by linarith only [hok.c_deg_ge]
    positivity
  have hber := bernoulli_round_lt hc2_pos hVm_nn hφ2_pos
  set K := Nat.ceil (2 * wd.c_deg)
  set B := Nat.log 2 (Nat.ceil (wd.c_deg * (inp.prep.J.m : ℝ) / (2 * wd.φ_dec)) + 1) + 1
  rcases hunemb with ⟨eW, heW⟩
  rcases Finset.mem_filter.mp heW with ⟨heWm_r, hnone⟩
  have heWm := Finset.mem_range.mp heWm_r
  have heW_ge : wd.j0Edges.length ≤ eW := by
    by_contra hlt
    have hs := hj0 eW (lt_of_not_ge hlt)
    rw [Option.isSome_iff_ne_none] at hs
    rw [Option.isNone_iff_eq_none] at hnone
    exact hs hnone
  have hlow : 2 * wd.φ_dec ≤ volWRemPure wd emb₀ := by
    have hw_ge := mkW_wW_ge_two_phi_comp hok hws heW_ge heWm
    have hpt := Finset.single_le_sum (fun j hj =>
      (mkW_wW_pos hok hws (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)).le) heW
    exact le_trans hw_ge hpt
  by_contra hge
  have hKB : K * B ≤ η_prev := by
    have h1 : eta1Bound wd inp.prep.J = 1 + K * B := rfl
    omega
  set r : ℝ := (2 * wd.c_deg) / (2 * wd.c_deg + 1)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := div_le_one_of_le₀ (by linarith only [hc2_pos]) (by positivity)
  have hpow : r ^ η_prev ≤ r ^ (K * B) := pow_le_pow_of_le_one hr0 hr1 hKB
  have hup : volWRemPure wd emb₀ < 2 * wd.φ_dec := by
    calc volWRemPure wd emb₀
        ≤ r ^ η_prev * (wd.c_deg * (inp.prep.J.m : ℝ)) := hgeom
      _ ≤ r ^ (K * B) * (wd.c_deg * (inp.prep.J.m : ℝ)) := mul_le_mul_of_nonneg_right hpow hVm_nn
      _ < 2 * wd.φ_dec := hber
  linarith only [hlow, hup]

end MinCostFlow.Spanner
