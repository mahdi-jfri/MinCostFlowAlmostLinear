module

public import MinCostFlow.Spanner.ProgTask2WeightMath

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Integer numerator congestion and `t2InitJ0` pure-math invariants -/

private lemma static_phiDen_pos {inp : WitnessCoreInput} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w) : 0 < inp.prep.phiDen_dec := by
  have h1 := hs.2.2.2.2.2.2.2.2.1
  have h2 := hs.2.2.2.2.2.2.2.2.2.1
  omega

def vcongNumPure (wd : WitnessData) (J : Graph) (embJH : ℕ → Walk)
    (wWNum : ℕ → ℕ) (embWJ : ℕ → Option Walk) (x : ℕ) : ℕ :=
  ∑ eW ∈ Finset.range wd.W.m,
    if x ∈ (compose J embJH (partialToWalk embWJ) eW).verts then wWNum eW else 0

lemma vcongNumPure_eq_phiDen_mul {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    {wWNum : ℕ → ℕ}
    (hwN : ∀ eW < (inp.mkWitnessData ce pds WSubs).W.m,
      (wWNum eW : ℝ) / (inp.prep.phiDen_dec : ℝ) = (inp.mkWitnessData ce pds WSubs).wW eW)
    (embWJ : ℕ → Option Walk) (x : ℕ) :
    ((vcongNumPure (inp.mkWitnessData ce pds WSubs) inp.prep.J inp.embJH wWNum embWJ x : ℕ) : ℝ) =
      (inp.prep.phiDen_dec : ℝ) *
        vcongAt (inp.mkWitnessData ce pds WSubs).W
          (inp.mkWitnessData ce pds WSubs).wW (compose inp.prep.J inp.embJH (partialToWalk embWJ)) x := by
  have hden_pos : (0 : ℝ) < inp.prep.phiDen_dec := by
    exact_mod_cast static_phiDen_pos hs
  unfold vcongNumPure vcongAt
  rw [Finset.sum_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun eW heW => ?_
  have heWm := Finset.mem_range.mp heW
  split_ifs with hx
  · rw [← hwN eW heWm]
    field_simp
  · simp

lemma vcongNumPure_le_iff {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    {wWNum : ℕ → ℕ}
    (hwN : ∀ eW < (inp.mkWitnessData ce pds WSubs).W.m,
      (wWNum eW : ℝ) / (inp.prep.phiDen_dec : ℝ) = (inp.mkWitnessData ce pds WSubs).wW eW)
    (embWJ : ℕ → Option Walk) (x k : ℕ) :
    vcongAt (inp.mkWitnessData ce pds WSubs).W
        (inp.mkWitnessData ce pds WSubs).wW (compose inp.prep.J inp.embJH (partialToWalk embWJ)) x ≤
      (k : ℝ) * (inp.mkWitnessData ce pds WSubs).τ₁ ↔
      vcongNumPure (inp.mkWitnessData ce pds WSubs) inp.prep.J inp.embJH wWNum embWJ x ≤
        k * inp.tau1Int ce pds * inp.prep.phiDen_dec := by
  have hden_pos : (0 : ℝ) < inp.prep.phiDen_dec := by
    exact_mod_cast static_phiDen_pos hs
  have hsc := inp.mkWitnessData_scalars ce pds WSubs hs
  have hmul := vcongNumPure_eq_phiDen_mul hs hwN embWJ x
  rw [hsc.2.2.2.2.2]
  constructor
  · intro h
    have hr : ((vcongNumPure (inp.mkWitnessData ce pds WSubs) inp.prep.J inp.embJH wWNum embWJ x : ℕ) : ℝ) ≤
        ((k * inp.tau1Int ce pds * inp.prep.phiDen_dec : ℕ) : ℝ) := by
      rw [hmul]; push_cast; nlinarith
    exact_mod_cast hr
  · intro h
    have hr : ((vcongNumPure (inp.mkWitnessData ce pds WSubs) inp.prep.J inp.embJH wWNum embWJ x : ℕ) : ℝ) ≤
        ((k * inp.tau1Int ce pds * inp.prep.phiDen_dec : ℕ) : ℝ) := by exact_mod_cast h
    rw [hmul] at hr; push_cast at hr
    nlinarith

lemma vcongNumPure_ge_iff {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    {wWNum : ℕ → ℕ}
    (hwN : ∀ eW < (inp.mkWitnessData ce pds WSubs).W.m,
      (wWNum eW : ℝ) / (inp.prep.phiDen_dec : ℝ) = (inp.mkWitnessData ce pds WSubs).wW eW)
    (embWJ : ℕ → Option Walk) (x k : ℕ) :
    (k : ℝ) * (inp.mkWitnessData ce pds WSubs).τ₁ ≤
      vcongAt (inp.mkWitnessData ce pds WSubs).W
        (inp.mkWitnessData ce pds WSubs).wW (compose inp.prep.J inp.embJH (partialToWalk embWJ)) x ↔
      k * inp.tau1Int ce pds * inp.prep.phiDen_dec ≤
        vcongNumPure (inp.mkWitnessData ce pds WSubs) inp.prep.J inp.embJH wWNum embWJ x := by
  have hden_pos : (0 : ℝ) < inp.prep.phiDen_dec := by
    exact_mod_cast static_phiDen_pos hs
  have hsc := inp.mkWitnessData_scalars ce pds WSubs hs
  have hmul := vcongNumPure_eq_phiDen_mul hs hwN embWJ x
  rw [hsc.2.2.2.2.2]
  constructor
  · intro h
    have hr : ((k * inp.tau1Int ce pds * inp.prep.phiDen_dec : ℕ) : ℝ) ≤
        ((vcongNumPure (inp.mkWitnessData ce pds WSubs) inp.prep.J inp.embJH wWNum embWJ x : ℕ) : ℝ) := by
      rw [hmul]; push_cast; nlinarith
    exact_mod_cast hr
  · intro h
    have hr : ((k * inp.tau1Int ce pds * inp.prep.phiDen_dec : ℕ) : ℝ) ≤
        ((vcongNumPure (inp.mkWitnessData ce pds WSubs) inp.prep.J inp.embJH wWNum embWJ x : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [hmul] at hr; push_cast at hr
    nlinarith

def initEmb0 (inp : WitnessCoreInput) : ℕ → Option Walk := fun eW =>
  if eW < inp.prep.j0Edges.length then
    let eJ := inp.prep.j0Edges.getD eW 0
    let e := inp.prep.J.edges.getD eJ (0, 0)
    some { verts := [e.1, e.2], edges := [eJ] }
  else none

lemma t2Init_pure_inv {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    (hembJH : IsEmbedding inp.prep.J inp.H' inp.embJH) :
    let wd := inp.mkWitnessData ce pds WSubs
    IsPartialEmbedding wd.W inp.prep.J (initEmb0 inp) ∧
      (∀ eW < wd.j0Edges.length, (initEmb0 inp eW).isSome = true) ∧
      (∀ eW < wd.W.m, ((partialToWalk (initEmb0 inp) eW).edges.length : ℝ) ≤ wd.γ_ExpPath) ∧
      (∀ x < inp.H'.n,
        vcongAt wd.W wd.wW (compose inp.prep.J inp.embJH (partialToWalk (initEmb0 inp))) x ≤
          ((0 : ℝ) + 1 / 2) * wd.τ₁) := by
  intro wd
  have hJ : inp.prep.J.IsValid := hs.1
  have hpart : IsPartialEmbedding wd.W inp.prep.J (initEmb0 inp) := by
    refine ⟨le_refl _, fun eW heW P hP => ?_⟩
    dsimp only [initEmb0] at hP
    split_ifs at hP with hj0
    injection hP with hP_eq
    subst hP_eq
    have hj0_wd : eW < wd.j0Edges.length := hj0
    have hwe := (mkW_W_edges_j0 (inp := inp) (ce := ce) (pds := pds) (WSubs := WSubs) hj0)
    have heJ_m : wd.j0Edges.getD eW 0 < inp.prep.J.m := by
      rw [List.getD_eq_getElem _ _ hj0_wd]
      exact hok.j0_lt _ (List.getElem_mem hj0_wd)
    have he_mem : inp.prep.J.edges.getD (wd.j0Edges.getD eW 0) (0, 0) ∈ inp.prep.J.edges := by
      rw [List.getD_eq_getElem _ _ heJ_m]; exact List.getElem_mem heJ_m
    have hv := hJ _ he_mem
    have hWe_eq : wd.W.edges.getD eW (0, 0) = inp.prep.J.edges.getD (inp.prep.j0Edges.getD eW 0) (0, 0) :=
      hwe.2.1
    rw [List.getD_eq_getElem wd.W.edges (0, 0) heW] at hWe_eq
    rw [hWe_eq]
    exact ⟨hv.1, hv.2, Or.inr ⟨by simp, by simp, rfl, rfl,
      fun j hj => by simp at hj; rwa [hj],
      fun i hi => by
        have hi0 : i = 0 := by simp at hi; omega
        subst hi0; left; simp⟩⟩
  have hj0_emb : ∀ eW < wd.j0Edges.length, (initEmb0 inp eW).isSome = true := by
    intro eW heW
    have heW' : eW < inp.prep.j0Edges.length := heW
    simp [initEmb0, heW']
  have helen : ∀ eW < wd.W.m, ((partialToWalk (initEmb0 inp) eW).edges.length : ℝ) ≤ wd.γ_ExpPath := by
    intro eW _
    have h1_le_γ : (1 : ℝ) ≤ wd.γ_ExpPath := by
      have := hok.γ_ExpPath_ge
      have hhalf := hok.φ_ds_half
      have hpos := hok.φ_ds_pos
      have h2 : (2 : ℝ) ≤ 1 / wd.φ_ds := by rw [le_div_iff₀ hpos]; linarith
      linarith
    dsimp only [partialToWalk, initEmb0]
    split_ifs <;> simp [Walk.empty] <;> linarith
  have hvcong : ∀ x < inp.H'.n,
      vcongAt wd.W wd.wW (compose inp.prep.J inp.embJH (partialToWalk (initEmb0 inp))) x ≤
        ((0 : ℝ) + 1 / 2) * wd.τ₁ := by
    intro x hxH
    by_cases hW0 : wd.W.m = 0
    · unfold vcongAt; rw [hW0]; simp; linarith [hok.τ₁_nonneg]
    have hWpos : 0 < wd.W.m := Nat.pos_of_ne_zero hW0
    have ⟨hmaxD, hlenJ⟩ := mkW_maxDeg_pos_of_W_pos hs hok hws hembJH hWpos
    have hsc := inp.mkWitnessData_scalars ce pds WSubs hs
    have hsum_le : vcongAt wd.W wd.wW (compose inp.prep.J inp.embJH (partialToWalk (initEmb0 inp))) x ≤
        (vcongNat inp.prep.J inp.H' inp.embJH : ℝ) := by
      have hj0_le_W : wd.j0Edges.length ≤ wd.W.m := by rw [hok.W_m_eq]; exact Nat.le_add_right _ _
      unfold vcongAt
      rw [Finset.sum_filter, ← Finset.sum_range_add_sum_Ico _ hj0_le_W]
      have htail : ∑ eW ∈ Finset.Ico wd.j0Edges.length wd.W.m,
          (if x ∈ (compose inp.prep.J inp.embJH (partialToWalk (initEmb0 inp)) eW).verts then wd.wW eW else 0) = 0 := by
        refine Finset.sum_eq_zero fun eW heW => ?_
        have hge : inp.prep.j0Edges.length ≤ eW := (Finset.mem_Ico.mp heW).1
        have hnone : initEmb0 inp eW = none := by simp [initEmb0, not_lt.mpr hge]
        have heq_e : partialToWalk (initEmb0 inp) eW = Walk.empty := by simp [partialToWalk, hnone]
        simp [compose, heq_e, composeAux, Walk.empty]
      rw [htail, add_zero]
      have hpt : ∀ eW ∈ Finset.range wd.j0Edges.length,
          (if x ∈ (compose inp.prep.J inp.embJH (partialToWalk (initEmb0 inp)) eW).verts then wd.wW eW else 0) ≤
            if x ∈ (inp.embJH (wd.j0Edges.getD eW 0)).verts then 1 else 0 := by
        intro eW heW
        have hj0 : eW < inp.prep.j0Edges.length := Finset.mem_range.mp heW
        have he_nl := mkW_j0_nonloop hs hj0
        have he_eq : partialToWalk (initEmb0 inp) eW =
            { verts := [(inp.prep.J.edges.getD (inp.prep.j0Edges.getD eW 0) (0, 0)).1,
                        (inp.prep.J.edges.getD (inp.prep.j0Edges.getD eW 0) (0, 0)).2],
              edges := [inp.prep.j0Edges.getD eW 0] } := by
          simp [partialToWalk, initEmb0, hj0]
        have he_lt' : (inp.prep.J.edges.getD (inp.prep.j0Edges.getD eW 0) (0, 0)).2 < inp.prep.J.n := by
          have hm : inp.prep.j0Edges.getD eW 0 < inp.prep.J.edges.length := he_nl.1
          rw [List.getD_eq_getElem _ _ hm]
          exact (hJ _ (List.getElem_mem hm)).2
        have hmem_iff := compose_nonloop_mem_verts_iff hembJH
          [(inp.prep.J.edges.getD (inp.prep.j0Edges.getD eW 0) (0, 0)).1,
           (inp.prep.J.edges.getD (inp.prep.j0Edges.getD eW 0) (0, 0)).2]
          [inp.prep.j0Edges.getD eW 0] (by simp) (fun _ h => by simp at h; rw [h]; exact he_nl)
          (fun i hi => by
            have hi0 : i = 0 := by simp at hi; omega
            subst hi0; left; simp)
          rfl rfl he_lt' x
        have he_verts : (compose inp.prep.J inp.embJH (partialToWalk (initEmb0 inp)) eW).verts.Mem x ↔
            x ∈ (inp.embJH (wd.j0Edges.getD eW 0)).verts := by
          change x ∈ (composeAux inp.prep.J inp.embJH (partialToWalk (initEmb0 inp) eW).verts
            (partialToWalk (initEmb0 inp) eW).edges).verts ↔
            x ∈ (inp.embJH (inp.prep.j0Edges.getD eW 0)).verts
          rw [he_eq]
          simpa using hmem_iff
        have hww_le1 : wd.wW eW ≤ 1 := by
          rw [(mkW_W_edges_j0 (inp := inp) (ce := ce) (pds := pds) (WSubs := WSubs) hj0).2.2]
          exact hok.φ_dec_le
        split_ifs with h1 h2
        · exact hww_le1
        · exact absurd (he_verts.mp h1) h2
        · norm_num
        · norm_num
      have hcard_le : (∑ eW ∈ Finset.range wd.j0Edges.length,
          if x ∈ (inp.embJH (wd.j0Edges.getD eW 0)).verts then (1 : ℝ) else 0) ≤
          (vcongNat inp.prep.J inp.H' inp.embJH : ℝ) := by
        have hinj : Set.InjOn (fun eW => wd.j0Edges.getD eW 0) (Finset.range wd.j0Edges.length) := by
          intro a ha b hb hab
          dsimp only at hab
          have ha' := Finset.mem_range.mp ha
          have hb' := Finset.mem_range.mp hb
          rw [List.getD_eq_getElem _ _ ha', List.getD_eq_getElem _ _ hb'] at hab
          exact congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hok.j0_nodup) (a₁ := ⟨a, ha'⟩) (a₂ := ⟨b, hb'⟩) hab)
        have hsub : ((Finset.range wd.j0Edges.length).filter
            fun eW => x ∈ (inp.embJH (wd.j0Edges.getD eW 0)).verts).image (fun eW => wd.j0Edges.getD eW 0) ⊆
            (Finset.range inp.prep.J.m).filter fun e => x ∈ (inp.embJH e).verts := by
          intro j hj
          rcases Finset.mem_image.mp hj with ⟨eW, heW, rfl⟩
          have heW_f := Finset.mem_filter.mp heW
          have heW_r := Finset.mem_range.mp heW_f.1
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨?_, heW_f.2⟩
          rw [List.getD_eq_getElem _ _ heW_r]; exact hok.j0_lt _ (List.getElem_mem heW_r)
        have hnat_le : ((Finset.range wd.j0Edges.length).filter
            fun eW => x ∈ (inp.embJH (wd.j0Edges.getD eW 0)).verts).card ≤
            ((Finset.range inp.prep.J.m).filter fun e => x ∈ (inp.embJH e).verts).card := by
          rw [← Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]
          exact Finset.card_le_card hsub
        have hvc : ((Finset.range inp.prep.J.m).filter fun e => x ∈ (inp.embJH e).verts).card ≤
            vcongNat inp.prep.J inp.H' inp.embJH := by
          unfold vcongNat
          refine Finset.le_sup (f := fun v =>
            ((Finset.range inp.prep.J.m).filter fun e => v ∈ (inp.embJH e).verts).card)
            (Finset.mem_range.mpr hxH)
        have hsum_nat : (∑ eW ∈ Finset.range wd.j0Edges.length,
            if x ∈ (inp.embJH (wd.j0Edges.getD eW 0)).verts then (1 : ℝ) else 0) =
            (((Finset.range wd.j0Edges.length).filter
              fun eW => x ∈ (inp.embJH (wd.j0Edges.getD eW 0)).verts).card : ℝ) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [hsum_nat]
        exact_mod_cast le_trans hnat_le hvc
      exact le_trans (Finset.sum_le_sum hpt) hcard_le
    have hv_le_tau : (vcongNat inp.prep.J inp.H' inp.embJH : ℝ) ≤ wd.τ₁ / 2 := by
      have hpos : (0 : ℝ) < inp.phiDsDenInt ce pds := by
        have := hok.φ_ds_pos; rw [hsc.2.1] at this
        exact_mod_cast Nat.pos_of_ne_zero (fun h0 => by simp [h0] at this)
      have hhalf : (1 : ℝ) / (inp.phiDsDenInt ce pds : ℝ) ≤ 1 / 2 := hsc.2.1 ▸ hok.φ_ds_half
      have h2r : (2 : ℝ) ≤ (inp.phiDsDenInt ce pds : ℝ) := by
        have := (div_le_div_iff₀ hpos (by norm_num)).mp hhalf; linarith
      have hds_ge2 : 2 ≤ inp.phiDsDenInt ce pds := by exact_mod_cast h2r
      have hγE_ge1 : 1 ≤ inp.γExpInt ce pds := by
        have hle := hok.γ_ExpPath_ge; rw [hsc.2.1, hsc.2.2.1] at hle
        have hdiv_eq : 1 / (1 / (inp.phiDsDenInt ce pds : ℝ)) = inp.phiDsDenInt ce pds := by field_simp
        have h2γ : (2 : ℝ) ≤ inp.γExpInt ce pds := by linarith
        exact_mod_cast (le_trans (by norm_num : (1 : ℝ) ≤ 2) h2γ)
      have hγD_ge1 : 1 ≤ inp.γDelInt ce pds := by
        have h1 := hok.γ_del_ge; rw [hsc.2.2.2.1] at h1; exact_mod_cast h1
      have htau2_ge1 : 1 ≤ inp.tau2Int ce pds := by
        unfold WitnessCoreInput.tau2Int
        exact Nat.le_trans (by omega) (Nat.mul_le_mul (Nat.mul_le_mul hγE_ge1 hγD_ge1) hds_ge2)
      have h2v : 2 * vcongNat inp.prep.J inp.H' inp.embJH ≤ inp.tau1Int ce pds := by
        unfold WitnessCoreInput.tau1Int
        have hprod : 1 ≤ inp.tau2Int ce pds * length inp.prep.J inp.embJH :=
          Nat.le_trans (by decide) (Nat.mul_le_mul htau2_ge1 hlenJ)
        nlinarith
      have hr : (2 : ℝ) * (vcongNat inp.prep.J inp.H' inp.embJH : ℝ) ≤ wd.τ₁ := by
        rw [hsc.2.2.2.2.2]; exact_mod_cast h2v
      linarith
    linarith [hsum_le, hv_le_tau]
  exact ⟨hpart, hj0_emb, helen, hvcong⟩

lemma vcongAt_step_unchanged_of_deleted {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    (hembJH : IsEmbedding inp.prep.J inp.H' inp.embJH)
    {ci : ℕ} (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length)
    {delSet : Finset ℕ} {x : ℕ}
    (hproc : ∀ b < (inp.mkWitnessData ce pds WSubs).comps[ci].J_sub.m,
      x ∈ (inp.embJH ((inp.mkWitnessData ce pds WSubs).comps[ci].jSubOrigEdges.getD b 0)).verts →
      b ∈ delSet)
    {u' v' : ℕ} {P_sub : Walk}
    (hP_walk : P_sub.IsWalk (inp.mkWitnessData ce pds WSubs).comps[ci].J_sub u' v')
    (hP_undel : ∀ b ∈ P_sub.edges, b ∉ delSet) :
    x ∉ (composeAux inp.prep.J inp.embJH (liftJSubWalk (inp.mkWitnessData ce pds WSubs).comps[ci] P_sub).verts
      (liftJSubWalk (inp.mkWitnessData ce pds WSubs).comps[ci] P_sub).edges).verts := by
  set c := (inp.mkWitnessData ce pds WSubs).comps[ci]
  have hPL := mkW_isWalk_liftJSubWalk hs hok hws hci hP_walk
  have hjOrig_nl : ∀ b ∈ P_sub.edges,
      c.jSubOrigEdges.getD b 0 < inp.prep.J.m ∧
      (inp.prep.J.edges.getD (c.jSubOrigEdges.getD b 0) (0, 0)).1 ≠
        (inp.prep.J.edges.getD (c.jSubOrigEdges.getD b 0) (0, 0)).2 := by
    intro b hb
    have hb_m : b < c.J_sub.m :=
      hP_walk.2.2.elim (fun h => by simp [h.2.1] at hb) (fun h => h.2.2.2.2.1 b hb)
    have hb_orig : b < c.jSubOrigEdges.length := by
      rw [(hok.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hb_m
    exact mkW_comp_jOrig_nonloop hs hws hci hb_orig
  intro hmem
  rcases hPL with ⟨_, hvL, ⟨hPv, hPe, _⟩ | ⟨_, hlenL, hheadL, hlastL, _, hstepL⟩⟩
  · rw [hPv, hPe] at hmem
    simp [composeAux, Walk.empty] at hmem
  · have hedges_nl : ∀ e' ∈ (liftJSubWalk c P_sub).edges,
        e' < inp.prep.J.m ∧ (inp.prep.J.edges.getD e' (0, 0)).1 ≠ (inp.prep.J.edges.getD e' (0, 0)).2 := by
      intro e' he'
      simp only [liftJSubWalk, List.mem_map] at he'
      rcases he' with ⟨b, hb, rfl⟩
      exact hjOrig_nl b hb
    have heq_m := compose_nonloop_mem_verts_iff hembJH
      (liftJSubWalk c P_sub).verts (liftJSubWalk c P_sub).edges hlenL hedges_nl hstepL hheadL hlastL hvL x
    rw [heq_m] at hmem
    rcases hmem with ⟨e', he', hx_e'⟩
    simp only [liftJSubWalk, List.mem_map] at he'
    rcases he' with ⟨b, hb, rfl⟩
    have hb_m : b < c.J_sub.m :=
      hP_walk.2.2.elim (fun h => by simp [h.2.1] at hb) (fun h => h.2.2.2.2.1 b hb)
    exact absurd (hproc b hb_m hx_e') (hP_undel b hb)

def unembeddedSetPure (wd : WitnessData) (embWJ : ℕ → Option Walk) : Finset ℕ :=
  (Finset.range wd.W.m).filter fun eW => (embWJ eW).isNone

noncomputable def volWRemPure (wd : WitnessData) (embWJ : ℕ → Option Walk) : ℝ :=
  ∑ eW ∈ unembeddedSetPure wd embWJ, wd.wW eW

lemma volWRemPure_nonneg {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph}
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    (embWJ : ℕ → Option Walk) :
    0 ≤ volWRemPure (inp.mkWitnessData ce pds WSubs) embWJ := by
  refine Finset.sum_nonneg fun eW heW => ?_
  exact (mkW_wW_pos hok hws (Finset.mem_range.mp (Finset.mem_filter.mp heW).1)).le

lemma volWRemPure_init_le {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    (embWJ : ℕ → Option Walk)
    (hj0 : ∀ eW < (inp.mkWitnessData ce pds WSubs).j0Edges.length, (embWJ eW).isSome = true) :
    let wd := inp.mkWitnessData ce pds WSubs
    volWRemPure wd embWJ ≤ wd.c_deg * (inp.prep.J.m : ℝ) := by
  intro wd
  have hsub : unembeddedSetPure wd embWJ ⊆ Finset.Ico wd.j0Edges.length wd.W.m := by
    intro eW heW
    rcases Finset.mem_filter.mp heW with ⟨hm, hnone⟩
    have heWm := Finset.mem_range.mp hm
    rw [Finset.mem_Ico]
    refine ⟨?_, heWm⟩
    by_contra hlt
    have hs := hj0 eW (lt_of_not_ge hlt)
    rw [Option.isSome_iff_ne_none] at hs
    rw [Option.isNone_iff_eq_none] at hnone
    exact hs hnone
  have hle : volWRemPure wd embWJ ≤ ∑ eW ∈ Finset.Ico wd.j0Edges.length wd.W.m, wd.wW eW :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun eW heW _ =>
      (mkW_wW_pos hok hws (Finset.mem_Ico.mp heW).2).le
  exact le_trans hle (mkW_sum_wW_comp_le hs hok hws)

end MinCostFlow.Spanner
