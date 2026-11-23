module

public import MinCostFlow.Spanner.ProgTask3Math

@[expose] public section

namespace MinCostFlow.Spanner

open Cited

/-- Pure per-round progress theorem for Task 3 (mirroring `Analysis2.claim_8_9` on `mkWitnessData`). -/
lemma t3Round_math_spec {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph}
    (hok : ∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
      WitnessOK (N_max := N_max) (W_max := W_max) tools inp.H' inp.prep.J inp.embJH
        (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    {η_prev : ℕ} {emb₀ emb₁ : ℕ → Option Walk} {delW vhatW : ℕ → Finset ℕ}
    (hmono : ∀ eJ < inp.prep.J.m, emb₀ eJ = none ∨ emb₁ eJ = emb₀ eJ)
    (helen : ∀ eJ < inp.prep.J.m, ↑(partialToWalk emb₁ eJ).edges.length ≤ (inp.mkWitnessData ce pds WSubs).γ_ExpPath)
    (hecong_prev : ∀ eW < (inp.mkWitnessData ce pds WSubs).W.m,
      econgAt inp.prep.J (fun _ => 1) (inp.mkWitnessData ce pds WSubs).wW (partialToWalk emb₀) eW ≤
        (↑η_prev + 1 / 2) * (inp.mkWitnessData ce pds WSubs).τ₂)
    (hdel_spec : ∀ (ci : ℕ) (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length), ∀ eL ∈ delW ci,
      eL < (inp.mkWitnessData ce pds WSubs).comps[ci].W_sub.m ∧
        ↑(η_prev + 1) * (inp.mkWitnessData ce pds WSubs).τ₂ ≤
          econgAt inp.prep.J (fun _ => 1) (inp.mkWitnessData ce pds WSubs).wW (partialToWalk emb₁)
            ((inp.mkWitnessData ce pds WSubs).comps[ci].wStart + eL))
    (hvhat_sub : ∀ (ci : ℕ) (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length),
      vhatW ci ⊆ (inp.mkWitnessData ce pds WSubs).comps[ci].W_sub.verts)
    (hvhat_vol : ∀ (ci : ℕ) (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length),
      ↑((inp.mkWitnessData ce pds WSubs).comps[ci].W_sub.vol (vhatW ci)) ≤
        (inp.mkWitnessData ce pds WSubs).γ_del * ↑(delW ci).card / (inp.mkWitnessData ce pds WSubs).φ_ds)
    (hunemb_vhat : ∀ eJ < inp.prep.J.m, (emb₁ eJ).isNone = true →
      ∃ (ci : ℕ) (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length) (jL : ℕ),
        jL < (inp.mkWitnessData ce pds WSubs).comps[ci].J_sub.m ∧
        (inp.mkWitnessData ce pds WSubs).jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inComp ci jL ∧
        (((inp.mkWitnessData ce pds WSubs).comps[ci].J_sub.edges.getD jL (0, 0)).1 ∈ vhatW ci ∨
         ((inp.mkWitnessData ce pds WSubs).comps[ci].J_sub.edges.getD jL (0, 0)).2 ∈ vhatW ci))
    (hjOrig_eq_of_inComp : ∀ eJ < inp.prep.J.m, ∀ ci jL,
      (inp.mkWitnessData ce pds WSubs).jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inComp ci jL →
      ∃ hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length,
        (inp.mkWitnessData ce pds WSubs).comps[ci].jSubOrigEdges.getD jL 0 = eJ) :
    let wd := inp.mkWitnessData ce pds WSubs
    let U₀ := unembeddedSet2Pure inp.prep.J emb₀
    let U₁ := unembeddedSet2Pure inp.prep.J emb₁
    let E_embed := {eJ ∈ Finset.range inp.prep.J.m | (emb₀ eJ).isNone = true ∧ (emb₁ eJ).isSome = true}
    U₁.card ≤ 2 * E_embed.card ∧
      3 * U₁.card ≤ 2 * U₀.card ∧
      (∑ ci ∈ Finset.range wd.comps.length, (delW ci).card) ≤ wd.W.m ∧
      ((∑ ci ∈ Finset.range wd.comps.length, (delW ci).card : ℕ) : ℝ) ≤ ↑E_embed.card * wd.γ_ExpPath := by
  intro wd U₀ U₁ E_embed
  let t0 := (exists_localSpannerTools 0 (0 : ℝ)).some
  have hw := hok t0
  have hτ₂_pos : 0 < wd.τ₂ := hw.τ₂_pos
  have hγ_pos : 0 < wd.γ_ExpPath := by
    have h1 : (2 : ℝ) ≤ 1 / wd.φ_ds := by rw [le_div_iff₀ hw.φ_ds_pos]; linarith [hw.φ_ds_half]
    linarith [hw.γ_ExpPath_ge, h1]
  have hφ_dec_pos : 0 < wd.φ_dec := hw.φ_dec_pos
  have hτ₂_half : 1 / wd.φ_dec ≤ wd.τ₂ / 2 := mkW_one_div_phi_dec_le_tau2_half hok
  let delImg : ℕ → Finset ℕ := fun ci =>
    (delW ci).image (fun eL => (wd.comps.getD ci defaultCompInfo).wStart + eL)
  let E_del_W : Finset ℕ := (Finset.range wd.comps.length).biUnion delImg
  have hdisj_del : Set.PairwiseDisjoint ↑(Finset.range wd.comps.length) delImg := by
    intro ci1 hci1 ci2 hci2 hne
    rw [Finset.mem_coe, Finset.mem_range] at hci1 hci2
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro eW he1 he2
    simp only [delImg, Finset.mem_image] at he1 he2
    rcases he1 with ⟨eL1, heL1, rfl⟩
    rcases he2 with ⟨eL2, heL2, heq⟩
    have hm1 : eL1 < wd.comps[ci1].W_sub.m := (hdel_spec ci1 hci1 eL1 heL1).1
    have hm2 : eL2 < wd.comps[ci2].W_sub.m := (hdel_spec ci2 hci2 eL2 heL2).1
    simp only [List.getD_eq_getElem _ _ hci1, List.getD_eq_getElem _ _ hci2] at heq
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hadj : wd.comps[ci1].wStart + wd.comps[ci1].W_sub.m ≤ wd.comps[ci2].wStart :=
        compsAligned_adjacent hw.aligned ci1 ci2 hci1 hci2 hlt
      omega
    · have hadj : wd.comps[ci2].wStart + wd.comps[ci2].W_sub.m ≤ wd.comps[ci1].wStart :=
        compsAligned_adjacent hw.aligned ci2 ci1 hci2 hci1 hlt
      omega
  have hdel_card_eq : E_del_W.card = ∑ ci ∈ Finset.range wd.comps.length, (delW ci).card := by
    rw [Finset.card_biUnion hdisj_del]
    refine Finset.sum_congr rfl fun ci _ => ?_
    exact Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)
  have hdel_mem : ∀ eW ∈ E_del_W,
      ∃ (ci : ℕ) (hci : ci < wd.comps.length) (eL : ℕ),
        eL ∈ delW ci ∧ eL < wd.comps[ci].W_sub.m ∧ eW = wd.comps[ci].wStart + eL ∧
        wd.j0Edges.length ≤ eW ∧ eW < wd.W.m ∧
        ↑(η_prev + 1) * wd.τ₂ ≤ econgAt inp.prep.J (fun _ => 1) wd.wW (partialToWalk emb₁) eW := by
    intro eW heW
    simp only [E_del_W, Finset.mem_biUnion, Finset.mem_range, delImg, Finset.mem_image] at heW
    rcases heW with ⟨ci, hci, eL, heL, rfl⟩
    rcases hdel_spec ci hci eL heL with ⟨hm, hec⟩
    have hprops := hw.comp_props ci hci
    have hs_ge : wd.j0Edges.length ≤ wd.comps[ci].wStart :=
      hprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hs_end : wd.comps[ci].wStart + wd.comps[ci].W_sub.m ≤ wd.W.m :=
      hprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hm' : eL < wd.comps[ci].W_sub.m := hm
    rw [List.getD_eq_getElem _ _ hci]
    exact ⟨ci, hci, eL, heL, hm', rfl, by omega, by omega, hec⟩
  have hE_del_sub : E_del_W ⊆ Finset.range wd.W.m := fun eW heW =>
    Finset.mem_range.mpr (hdel_mem eW heW).choose_spec.choose_spec.choose_spec.2.2.2.2.1
  have hdel_le_Wm : (∑ ci ∈ Finset.range wd.comps.length, (delW ci).card) ≤ wd.W.m := by
    rw [← hdel_card_eq]
    calc E_del_W.card ≤ (Finset.range wd.W.m).card := Finset.card_le_card hE_del_sub
      _ = wd.W.m := Finset.card_range _
  have hW_gap_sum : wd.τ₂ / 2 * ∑ eW ∈ E_del_W, wd.wW eW ≤ ↑E_embed.card * wd.γ_ExpPath := by
    rw [Finset.mul_sum]
    have hle_per : ∀ eW ∈ E_del_W,
        wd.τ₂ / 2 * wd.wW eW ≤
          ∑ eJ ∈ E_embed, (if eW ∈ (partialToWalk emb₁ eJ).edges then (1 : ℝ) else 0) := by
      intro eW heW
      have hinfo := hdel_mem eW heW
      have heWm : eW < wd.W.m := hinfo.choose_spec.choose_spec.choose_spec.2.2.2.2.1
      have hec1 : ↑(η_prev + 1) * wd.τ₂ ≤ econgAt inp.prep.J (fun _ => 1) wd.wW (partialToWalk emb₁) eW :=
        hinfo.choose_spec.choose_spec.choose_spec.2.2.2.2.2
      have hec0 : econgAt inp.prep.J (fun _ => 1) wd.wW (partialToWalk emb₀) eW ≤ (↑η_prev + 1 / 2) * wd.τ₂ :=
        hecong_prev eW heWm
      have hgap : wd.τ₂ / 2 ≤ econgAt inp.prep.J (fun _ => 1) wd.wW (partialToWalk emb₁) eW -
          econgAt inp.prep.J (fun _ => 1) wd.wW (partialToWalk emb₀) eW := by
        have hcast : (↑(η_prev + 1) : ℝ) = ↑η_prev + 1 := by push_cast; ring
        have h2 : ((η_prev : ℝ) + 1) * wd.τ₂ = (η_prev : ℝ) * wd.τ₂ + wd.τ₂ := by ring
        have h3 : ((η_prev : ℝ) + 1 / 2) * wd.τ₂ = (η_prev : ℝ) * wd.τ₂ + wd.τ₂ / 2 := by ring
        rw [hcast, h2] at hec1
        rw [h3] at hec0
        linarith
      rw [econgAt_mono_diff inp.prep.J wd.wW emb₀ emb₁ hmono eW] at hgap
      have hwW_pos : 0 < wd.wW eW := mkW_wW_pos hw hws heWm
      have hmul := (le_div_iff₀ hwW_pos).mp hgap
      have hcard_eq : ({eJ ∈ Finset.range inp.prep.J.m |
          (emb₀ eJ).isNone = true ∧ (emb₁ eJ).isSome = true ∧ eW ∈ (partialToWalk emb₁ eJ).edges}.card : ℝ) =
          ∑ eJ ∈ E_embed, (if eW ∈ (partialToWalk emb₁ eJ).edges then (1 : ℝ) else 0) := by
        have hflt : {eJ ∈ Finset.range inp.prep.J.m |
            (emb₀ eJ).isNone = true ∧ (emb₁ eJ).isSome = true ∧ eW ∈ (partialToWalk emb₁ eJ).edges} =
            E_embed.filter (fun eJ => eW ∈ (partialToWalk emb₁ eJ).edges) := by
          ext eJ; simp [E_embed, Finset.mem_filter, and_assoc]
        rw [hflt, ← Finset.sum_boole]
      linarith [hmul, hcard_eq]
    calc ∑ eW ∈ E_del_W, wd.τ₂ / 2 * wd.wW eW
        ≤ ∑ eW ∈ E_del_W, ∑ eJ ∈ E_embed, (if eW ∈ (partialToWalk emb₁ eJ).edges then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun eW heW => hle_per eW heW
      _ = ∑ eJ ∈ E_embed, ∑ eW ∈ E_del_W, (if eW ∈ (partialToWalk emb₁ eJ).edges then (1 : ℝ) else 0) :=
          Finset.sum_comm
      _ ≤ ∑ eJ ∈ E_embed, wd.γ_ExpPath := by
          refine Finset.sum_le_sum fun eJ heJ => ?_
          have heJm : eJ < inp.prep.J.m := (Finset.mem_filter.mp heJ).1 |> Finset.mem_range.mp
          have hsub : E_del_W.filter (fun eW => eW ∈ (partialToWalk emb₁ eJ).edges) ⊆
              (partialToWalk emb₁ eJ).edges.toFinset := fun eW heW =>
            List.mem_toFinset.mpr (Finset.mem_filter.mp heW).2
          have hsum_le : (∑ eW ∈ E_del_W, (if eW ∈ (partialToWalk emb₁ eJ).edges then (1 : ℝ) else 0)) ≤
              ((partialToWalk emb₁ eJ).edges.length : ℝ) := by
            rw [← Finset.sum_filter (p := fun eW => eW ∈ (partialToWalk emb₁ eJ).edges)]
            simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
            exact_mod_cast (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
          exact le_trans hsum_le (helen eJ heJm)
      _ = ↑E_embed.card * wd.γ_ExpPath := by simp
  have hdel_le_γ : ((∑ ci ∈ Finset.range wd.comps.length, (delW ci).card : ℕ) : ℝ) ≤ ↑E_embed.card * wd.γ_ExpPath := by
    rw [← hdel_card_eq]
    have h1 : (E_del_W.card : ℝ) ≤ wd.τ₂ / 2 * ∑ eW ∈ E_del_W, wd.wW eW := by
      rw [Finset.mul_sum]
      calc (E_del_W.card : ℝ) = ∑ _ ∈ E_del_W, (1 : ℝ) := by simp
        _ ≤ ∑ eW ∈ E_del_W, wd.τ₂ / 2 * wd.wW eW := by
          refine Finset.sum_le_sum fun eW heW => ?_
          have heWm := Finset.mem_range.mp (hE_del_sub heW)
          have hphi : wd.φ_dec ≤ wd.wW eW := mkW_wW_ge_phi hw hws heWm
          have hmul1 : (1 : ℝ) ≤ wd.τ₂ / 2 * wd.φ_dec := (div_le_iff₀ hφ_dec_pos).mp hτ₂_half
          have hτ₂_nn : 0 ≤ wd.τ₂ / 2 := by positivity
          exact le_trans hmul1 (mul_le_mul_of_nonneg_left hphi hτ₂_nn)
    exact le_trans h1 hW_gap_sum
  have hU_card_real : (U₁.card : ℝ) ≤ wd.γ_del / wd.φ_ds * ∑ eW ∈ E_del_W, wd.wW eW := by
    let unembComp : ℕ → Finset ℕ := fun ci =>
      U₁.filter fun eJ => ∃ jL < (wd.comps.getD ci defaultCompInfo).J_sub.m,
        wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inComp ci jL ∧
        (((wd.comps.getD ci defaultCompInfo).J_sub.edges.getD jL (0, 0)).1 ∈ vhatW ci ∨
         ((wd.comps.getD ci defaultCompInfo).J_sub.edges.getD jL (0, 0)).2 ∈ vhatW ci)
    have hU_sub : U₁ ⊆ (Finset.range wd.comps.length).biUnion unembComp := by
      intro eJ heJ
      rw [Finset.mem_biUnion]
      have heJ' := Finset.mem_filter.mp heJ
      rcases hunemb_vhat eJ (Finset.mem_range.mp heJ'.1) heJ'.2 with ⟨ci, hci, jL, hjL, hsrc, hmem⟩
      refine ⟨ci, Finset.mem_range.mpr hci, Finset.mem_filter.mpr ⟨heJ, jL, ?_, hsrc, ?_⟩⟩
      · rw [List.getD_eq_getElem _ _ hci]; exact hjL
      · rw [List.getD_eq_getElem _ _ hci]; exact hmem
    have hU_le_sum : U₁.card ≤ ∑ ci ∈ Finset.range wd.comps.length, (unembComp ci).card :=
      (Finset.card_le_card hU_sub).trans Finset.card_biUnion_le
    have hcomp_bound : ∀ ci ∈ Finset.range wd.comps.length,
        ((unembComp ci).card : ℝ) ≤
          wd.γ_del / wd.φ_ds * ∑ eW ∈ delImg ci, wd.wW eW := by
      intro ci hci_mem
      have hci : ci < wd.comps.length := Finset.mem_range.mp hci_mem
      set c := wd.comps[ci]
      have hcprops := hw.comp_props ci hci
      have hJn := hcprops.2.2.2.2.2.1
      have hJvalid := hcprops.2.2.2.2.2.2.1
      have hWn := hcprops.2.2.2.2.2.2.2.2.2.2.2.1
      have hdegSand := hcprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      let touchEdges : Finset ℕ := (Finset.range c.J_sub.m).filter fun b =>
        (c.J_sub.edges.getD b (0, 0)).1 ∈ vhatW ci ∨ (c.J_sub.edges.getD b (0, 0)).2 ∈ vhatW ci
      have hcomp_sub : unembComp ci ⊆ touchEdges.image (fun b => c.jSubOrigEdges.getD b 0) := by
        intro eJ heJ_c
        rw [Finset.mem_filter] at heJ_c
        rcases heJ_c with ⟨heJ_u, jL, hjL, hsrc, hend⟩
        have heJm : eJ < inp.prep.J.m := Finset.mem_range.mp (Finset.mem_filter.mp heJ_u).1
        have horig := (hjOrig_eq_of_inComp eJ heJm ci jL hsrc).2
        rw [Finset.mem_image]
        have hjL' : jL < c.J_sub.m := by
          change jL < wd.comps[ci].J_sub.m
          rwa [← List.getD_eq_getElem wd.comps defaultCompInfo hci]
        have hend' : (c.J_sub.edges.getD jL (0, 0)).1 ∈ vhatW ci ∨
            (c.J_sub.edges.getD jL (0, 0)).2 ∈ vhatW ci := by
          change (wd.comps[ci].J_sub.edges.getD jL (0, 0)).1 ∈ vhatW ci ∨
            (wd.comps[ci].J_sub.edges.getD jL (0, 0)).2 ∈ vhatW ci
          rwa [← List.getD_eq_getElem wd.comps defaultCompInfo hci]
        have horig' : c.jSubOrigEdges.getD jL 0 = eJ := horig
        exact ⟨jL, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjL', hend'⟩, horig'⟩
      have htouch_le : touchEdges.card ≤ c.J_sub.vol (vhatW ci) :=
        card_edges_touching_le_vol c.J_sub (vhatW ci) touchEdges hJvalid
          (Finset.filter_subset _ _) (fun _ hb => (Finset.mem_filter.mp hb).2)
      have hc_card_le : (unembComp ci).card ≤ c.J_sub.vol (vhatW ci) :=
        ((Finset.card_le_card hcomp_sub).trans Finset.card_image_le).trans htouch_le
      have hvhat_J : vhatW ci ⊆ Finset.range c.X.card := by
        have hsubW := hvhat_sub ci hci
        simpa [Graph.verts, hWn] using hsubW
      have hvol_J_W : (c.J_sub.vol (vhatW ci) : ℝ) ≤
          (wd.φ_dec * (2 : ℝ) ^ c.level) * (c.W_sub.vol (vhatW ci) : ℝ) := by
        have hJvol : (c.J_sub.vol (vhatW ci) : ℝ) = ∑ k ∈ vhatW ci, (c.J_sub.deg k : ℝ) := by
          unfold Graph.vol Graph.volIn Graph.deg
          rw [Nat.cast_sum]
        have hWvol : (c.W_sub.vol (vhatW ci) : ℝ) = ∑ k ∈ vhatW ci, (c.W_sub.deg k : ℝ) := by
          unfold Graph.vol Graph.volIn Graph.deg
          rw [Nat.cast_sum]
        rw [hJvol, hWvol, Finset.mul_sum]
        refine Finset.sum_le_sum fun k hk => ?_
        have hkX : k < c.X.card := Finset.mem_range.mp (hvhat_J hk)
        have hlow := (hdegSand k hkX).1
        have hpow_pos : (0 : ℝ) < wd.φ_dec * (2 : ℝ) ^ c.level := by positivity
        exact (div_le_iff₀ hpow_pos).mp hlow |>.trans_eq (by ring)
      have hW_vol_del := hvhat_vol ci hci
      have hdel_sum_eq : ∑ eW ∈ delImg ci, wd.wW eW =
          (wd.φ_dec * (2 : ℝ) ^ c.level) * ((delW ci).card : ℝ) := by
        dsimp only [delImg]
        rw [Finset.sum_image (fun a _ b _ h => Nat.add_left_cancel h)]
        have hconst : ∀ eL ∈ delW ci, wd.wW ((wd.comps.getD ci defaultCompInfo).wStart + eL) =
            wd.φ_dec * (2 : ℝ) ^ c.level := by
          intro eL heL
          have heL_lt : eL < c.W_sub.m := (hdel_spec ci hci eL heL).1
          have hw_eq := (mkW_W_edges_comp hws hci heL_lt).2.2.2
          rw [List.getD_eq_getElem _ _ hci]
          exact hw_eq
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_comm]
      have hpow_nn : (0 : ℝ) ≤ wd.φ_dec * (2 : ℝ) ^ c.level := by positivity
      have hγdel_nn : 0 ≤ wd.γ_del / wd.φ_ds := div_nonneg (by positivity [hw.γ_del_ge]) (le_of_lt hw.φ_ds_pos)
      calc ((unembComp ci).card : ℝ)
          ≤ (c.J_sub.vol (vhatW ci) : ℝ) := by exact_mod_cast hc_card_le
        _ ≤ (wd.φ_dec * (2 : ℝ) ^ c.level) * (c.W_sub.vol (vhatW ci) : ℝ) := hvol_J_W
        _ ≤ (wd.φ_dec * (2 : ℝ) ^ c.level) * (wd.γ_del * ((delW ci).card : ℝ) / wd.φ_ds) :=
            mul_le_mul_of_nonneg_left hW_vol_del hpow_nn
        _ = (wd.γ_del / wd.φ_ds) * ((wd.φ_dec * (2 : ℝ) ^ c.level) * ((delW ci).card : ℝ)) := by ring
        _ = wd.γ_del / wd.φ_ds * ∑ eW ∈ delImg ci, wd.wW eW := by rw [← hdel_sum_eq]
    calc (U₁.card : ℝ)
        ≤ ∑ ci ∈ Finset.range wd.comps.length, ((unembComp ci).card : ℝ) := by exact_mod_cast hU_le_sum
      _ ≤ ∑ ci ∈ Finset.range wd.comps.length, (wd.γ_del / wd.φ_ds * ∑ eW ∈ delImg ci, wd.wW eW) :=
          Finset.sum_le_sum fun ci hci => hcomp_bound ci hci
      _ = wd.γ_del / wd.φ_ds * ∑ ci ∈ Finset.range wd.comps.length, ∑ eW ∈ delImg ci, wd.wW eW := by
          rw [← Finset.mul_sum]
      _ = wd.γ_del / wd.φ_ds * ∑ eW ∈ E_del_W, wd.wW eW := by
          rw [← Finset.sum_biUnion hdisj_del]
  have hU_le_2E_real : (U₁.card : ℝ) ≤ 2 * (E_embed.card : ℝ) := by
    have hτ₂_eq : wd.τ₂ = wd.γ_ExpPath * wd.γ_del / wd.φ_ds := rfl
    have hγdel_eq : wd.γ_del / wd.φ_ds = wd.τ₂ / wd.γ_ExpPath := by
      rw [hτ₂_eq]; field_simp
    calc (U₁.card : ℝ)
        ≤ wd.γ_del / wd.φ_ds * ∑ eW ∈ E_del_W, wd.wW eW := hU_card_real
      _ = (2 / wd.γ_ExpPath) * (wd.τ₂ / 2 * ∑ eW ∈ E_del_W, wd.wW eW) := by
          rw [hγdel_eq]; ring
      _ ≤ (2 / wd.γ_ExpPath) * ((E_embed.card : ℝ) * wd.γ_ExpPath) :=
          mul_le_mul_of_nonneg_left hW_gap_sum (by positivity)
      _ = 2 * (E_embed.card : ℝ) := by field_simp
  have hU_le_2E : U₁.card ≤ 2 * E_embed.card := by
    exact_mod_cast hU_le_2E_real
  have hdisj_u : Disjoint U₁ E_embed := by
    rw [Finset.disjoint_left]
    intro eJ he1 he2
    have h1 := (Finset.mem_filter.mp he1).2
    have h2 := (Finset.mem_filter.mp he2).2.2
    cases h : emb₁ eJ <;> simp [h] at h1 h2
  have hunion : U₁ ∪ E_embed = U₀ := by
    ext eJ
    simp only [U₁, U₀, E_embed, unembeddedSet2Pure, Finset.mem_union, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · rintro (⟨hm, h1⟩ | ⟨hm, h0, _⟩)
      · refine ⟨hm, ?_⟩
        rcases hmono eJ hm with h0 | h01
        · exact Option.isNone_iff_eq_none.mpr h0
        · rw [h01] at h1; exact h1
      · exact ⟨hm, h0⟩
    · rintro ⟨hm, h0⟩
      by_cases h1 : (emb₁ eJ).isNone = true
      · exact Or.inl ⟨hm, h1⟩
      · right; refine ⟨hm, h0, ?_⟩
        cases h : emb₁ eJ with
        | none => simp [h] at h1
        | some _ => rfl
  have hU0_eq : U₀.card = U₁.card + E_embed.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj_u]
  refine ⟨hU_le_2E, ?_, hdel_le_Wm, hdel_le_γ⟩
  omega

/-- Pure `ℕ` logarithmic bound: geometric `2/3` shrinkage prevents exceeding `eta2Bound J`. -/
lemma t3Round_bound_of_unembedded {J : Graph} {η_prev : ℕ} {U₀ : Finset ℕ}
    (hunemb : U₀.Nonempty)
    (hgeom : 3 ^ η_prev * U₀.card ≤ 2 ^ η_prev * J.m) :
    η_prev + 1 < eta2Bound J := by
  by_contra hge
  have hk_pos : 1 ≤ Nat.log 2 (J.m + 1) + 1 := Nat.succ_pos _
  set k := Nat.log 2 (J.m + 1) + 1
  have h2k_le : 2 * k ≤ η_prev := by
    have : eta2Bound J = 1 + 2 * k := rfl
    omega
  have hm_lt : J.m + 1 < 2 ^ k := Nat.lt_pow_succ_log_self (by omega) (J.m + 1)
  have h42 : 4 ^ k * J.m < 4 ^ k * 2 ^ k :=
    Nat.mul_lt_mul_of_pos_left (by omega) (Nat.pow_pos (by omega))
  have h42_eq : 4 ^ k * 2 ^ k = 8 ^ k := by
    rw [← Nat.mul_pow]
  have h89 : 8 ^ k < 9 ^ k := Nat.pow_lt_pow_left (by omega) (by omega)
  have h2k_gap : 2 ^ (2 * k) * J.m < 3 ^ (2 * k) := by
    have h4eq : 4 ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
    have h9eq : 9 ^ k = 3 ^ (2 * k) := by rw [pow_mul]; norm_num
    rw [← h4eq, ← h9eq]
    exact lt_of_lt_of_le (lt_of_lt_of_eq h42 h42_eq) (le_of_lt h89)
  set d := η_prev - 2 * k
  have hη_eq : η_prev = d + 2 * k := by omega
  have h2le3 : 2 ^ d ≤ 3 ^ d := Nat.pow_le_pow_left (by omega) d
  have hpos_d : 0 < 2 ^ d := Nat.pow_pos (by omega)
  have h1 : 2 ^ d * (2 ^ (2 * k) * J.m) < 2 ^ d * 3 ^ (2 * k) :=
    Nat.mul_lt_mul_of_pos_left h2k_gap hpos_d
  have h2 : 2 ^ d * 3 ^ (2 * k) ≤ 3 ^ d * 3 ^ (2 * k) :=
    Nat.mul_le_mul_right _ h2le3
  have hstrict : 2 ^ η_prev * J.m < 3 ^ η_prev := by
    rw [hη_eq, pow_add, pow_add]
    calc 2 ^ d * 2 ^ (2 * k) * J.m = 2 ^ d * (2 ^ (2 * k) * J.m) := by ring
      _ < 2 ^ d * 3 ^ (2 * k) := h1
      _ ≤ 3 ^ d * 3 ^ (2 * k) := h2
  have hcard_pos : 1 ≤ U₀.card := Finset.Nonempty.card_pos hunemb
  have hmul : 3 ^ η_prev ≤ 3 ^ η_prev * U₀.card := Nat.le_mul_of_pos_right _ hcard_pos
  omega

end MinCostFlow.Spanner
