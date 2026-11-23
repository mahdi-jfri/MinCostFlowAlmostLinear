module

public import MinCostFlow.Spanner.ProgTask2DSOps

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Task 2 unpacked context, static preservation, and capacity bounds -/

lemma task2_wd_W_m_le_mwCap {impl : SpannerToolImpl} {wInp : WitnessCoreInput}
    {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : wInp.prep.StaticValid mem w)
    (hok : WitnessOK (exists_localSpannerTools 0 0).some wInp.H' wInp.prep.J wInp.embJH
      (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs))
    (hws : wInp.ValidWSubs impl.constructExpander WSubs)
    (hφ_lb : impl.decompose.φ_lb wInp.prep.J0_strip.m ≤
      (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec) :
    (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs).W.m ≤
      Task1Input.mwCap impl wInp.prep.J := by
  set wd := wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs
  have hJ0 : wInp.prep.J0_strip = stripLoops wInp.prep.J := hs.2.2.1
  have hJ0_wd : wd.J0_strip = stripLoops wInp.prep.J := hJ0
  have hm0_le : wd.j0Edges.length ≤ (stripLoops wInp.prep.J).m := by
    have h1 : wd.j0Edges.length + (wd.comps.map fun c => c.J_sub.m).sum ≤ wd.J0_strip.m :=
      mkW_sum_comp_j_m_le hs hok hws
    rw [hJ0_wd] at h1
    omega
  have hsum_w : (Nat.cast (wd.comps.map fun c => c.W_sub.m).sum : ℝ) * (2 * wd.φ_dec) ≤
      wd.c_deg * ((stripLoops wInp.prep.J).m : ℝ) := by
    have h1 : ∀ ci (hci : ci < wd.comps.length),
        (wd.comps[ci].W_sub.m : ℝ) * (2 * wd.φ_dec) ≤
          wd.c_deg * (wd.comps[ci].J_sub.m : ℝ) := by
      intro ci hci
      have hmul := mkW_comp_W_m_mul_weight_le hok hci
      have hlev := (hok.comp_props ci hci).1
      have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ wd.comps[ci].level := by
        exact_mod_cast Nat.le_self_pow hlev.ne' 2
      have hφnn : 0 ≤ (wd.comps[ci].W_sub.m : ℝ) * wd.φ_dec :=
        mul_nonneg (Nat.cast_nonneg _) hok.φ_dec_pos.le
      have hle_lhs : (wd.comps[ci].W_sub.m : ℝ) * (2 * wd.φ_dec) ≤
          (wd.comps[ci].W_sub.m : ℝ) * (wd.φ_dec * (2 : ℝ) ^ wd.comps[ci].level) := by
        calc (wd.comps[ci].W_sub.m : ℝ) * (2 * wd.φ_dec)
            = ((wd.comps[ci].W_sub.m : ℝ) * wd.φ_dec) * 2 := by ring
          _ ≤ ((wd.comps[ci].W_sub.m : ℝ) * wd.φ_dec) * (2 : ℝ) ^ wd.comps[ci].level :=
              mul_le_mul_of_nonneg_left h2 hφnn
          _ = (wd.comps[ci].W_sub.m : ℝ) * (wd.φ_dec * (2 : ℝ) ^ wd.comps[ci].level) := by ring
      exact le_trans hle_lhs hmul
    have hsum1 : ∑ ci ∈ Finset.range wd.comps.length,
          ((wd.comps.getD ci defaultCompInfo).W_sub.m : ℝ) * (2 * wd.φ_dec) ≤
        ∑ ci ∈ Finset.range wd.comps.length,
          wd.c_deg * ((wd.comps.getD ci defaultCompInfo).J_sub.m : ℝ) := by
      refine Finset.sum_le_sum fun ci hci_r => ?_
      have hci := Finset.mem_range.mp hci_r
      rw [List.getD_eq_getElem _ _ hci]
      exact h1 ci hci
    rw [← Finset.sum_mul, ← Finset.mul_sum] at hsum1
    rw [← Nat.cast_sum, sum_range_getD_nat wd.comps defaultCompInfo (fun c => c.W_sub.m)] at hsum1
    rw [← Nat.cast_sum, sum_range_getD_nat wd.comps defaultCompInfo (fun c => c.J_sub.m)] at hsum1
    have hjm_le : (wd.comps.map fun c => c.J_sub.m).sum ≤ (stripLoops wInp.prep.J).m := by
      have h : wd.j0Edges.length + (wd.comps.map fun c => c.J_sub.m).sum ≤ wd.J0_strip.m :=
        mkW_sum_comp_j_m_le hs hok hws
      rw [hJ0_wd] at h
      omega
    have hcd_nn : 0 ≤ wd.c_deg := le_trans (by norm_num) hok.c_deg_ge
    exact le_trans hsum1 (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hjm_le) hcd_nn)
  have hφ_pos : 0 < wd.φ_dec := hok.φ_dec_pos
  have hφ_le : wd.φ_dec ≤ 1 := hok.φ_dec_le
  have hcd_eq : wd.c_deg = 2 * (impl.constructExpander.c_deg_int : ℝ) := rfl
  have hcdeg_int_ge1 : (1 : ℝ) ≤ (impl.constructExpander.c_deg_int : ℝ) := by
    have h := hok.c_deg_ge; rw [hcd_eq] at h
    have hnat : 1 ≤ 2 * impl.constructExpander.c_deg_int := by exact_mod_cast h
    exact_mod_cast (by omega : 1 ≤ impl.constructExpander.c_deg_int)
  have hm0_cast : (wd.j0Edges.length : ℝ) ≤
      (impl.constructExpander.c_deg_int : ℝ) * ((stripLoops wInp.prep.J).m : ℝ) / wd.φ_dec := by
    have h1 : (wd.j0Edges.length : ℝ) ≤ ((stripLoops wInp.prep.J).m : ℝ) := by exact_mod_cast hm0_le
    have h2 : wd.φ_dec ≤ (impl.constructExpander.c_deg_int : ℝ) := le_trans hφ_le hcdeg_int_ge1
    have h3 : (1 : ℝ) ≤ (impl.constructExpander.c_deg_int : ℝ) / wd.φ_dec :=
      (one_le_div hφ_pos).mpr h2
    calc (wd.j0Edges.length : ℝ) ≤ ((stripLoops wInp.prep.J).m : ℝ) := h1
      _ = 1 * ((stripLoops wInp.prep.J).m : ℝ) := (one_mul _).symm
      _ ≤ ((impl.constructExpander.c_deg_int : ℝ) / wd.φ_dec) * ((stripLoops wInp.prep.J).m : ℝ) :=
          mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
      _ = (impl.constructExpander.c_deg_int : ℝ) * ((stripLoops wInp.prep.J).m : ℝ) / wd.φ_dec := by ring
  have hcomp_cast : (Nat.cast (wd.comps.map fun c => c.W_sub.m).sum : ℝ) ≤
      (impl.constructExpander.c_deg_int : ℝ) * ((stripLoops wInp.prep.J).m : ℝ) / wd.φ_dec := by
    rw [le_div_iff₀ hφ_pos]
    have h2 : wd.c_deg * ((stripLoops wInp.prep.J).m : ℝ) =
        2 * ((impl.constructExpander.c_deg_int : ℝ) * ((stripLoops wInp.prep.J).m : ℝ)) := by
      rw [hcd_eq]; ring
    linarith [hsum_w]
  have hφ_eq : wd.φ_dec = (wInp.prep.phiNum_dec : ℝ) / (wInp.prep.phiDen_dec : ℝ) := rfl
  have hW_real : (wd.W.m : ℝ) ≤
      2 * (impl.constructExpander.c_deg_int : ℝ) * ((stripLoops wInp.prep.J).m : ℝ) /
        impl.decompose.φ_lb (stripLoops wInp.prep.J).m := by
    rw [hok.W_m_eq, Nat.cast_add]
    have hadd : (wd.j0Edges.length : ℝ) + (Nat.cast (wd.comps.map fun c => c.W_sub.m).sum : ℝ) ≤
        2 * (impl.constructExpander.c_deg_int : ℝ) * ((stripLoops wInp.prep.J).m : ℝ) / wd.φ_dec := by
      calc (wd.j0Edges.length : ℝ) + (Nat.cast (wd.comps.map fun c => c.W_sub.m).sum : ℝ)
          ≤ (impl.constructExpander.c_deg_int : ℝ) * ((stripLoops wInp.prep.J).m : ℝ) / wd.φ_dec +
            (impl.constructExpander.c_deg_int : ℝ) * ((stripLoops wInp.prep.J).m : ℝ) / wd.φ_dec :=
              add_le_add hm0_cast hcomp_cast
        _ = 2 * (impl.constructExpander.c_deg_int : ℝ) * ((stripLoops wInp.prep.J).m : ℝ) / wd.φ_dec := by ring
    have hφ_lb' : impl.decompose.φ_lb (stripLoops wInp.prep.J).m ≤ wd.φ_dec := by
      rw [hφ_eq, ← hJ0]; exact hφ_lb
    have hlb_pos : 0 < impl.decompose.φ_lb (stripLoops wInp.prep.J).m := impl.decompose.hφ_lb_pos _
    have hdiv := div_le_div_of_nonneg_left (by positivity :
        0 ≤ 2 * (impl.constructExpander.c_deg_int : ℝ) * ((stripLoops wInp.prep.J).m : ℝ))
      hlb_pos hφ_lb'
    exact le_trans hadd hdiv
  have hceil : (wd.W.m : ℝ) ≤
      ((Nat.ceil (2 * (impl.constructExpander.c_deg_int : ℝ) * ((stripLoops wInp.prep.J).m : ℝ) /
        impl.decompose.φ_lb (stripLoops wInp.prep.J).m) : ℕ) : ℝ) :=
    le_trans hW_real (Nat.le_ceil _)
  have hnat : wd.W.m ≤ Nat.ceil (2 * (impl.constructExpander.c_deg_int : ℝ) *
      ((stripLoops wInp.prep.J).m : ℝ) / impl.decompose.φ_lb (stripLoops wInp.prep.J).m) := by
    exact_mod_cast hceil
  dsimp only [Task1Input.mwCap]
  exact le_trans hnat (Nat.le_add_right _ _)

lemma t2_inc_vertSum_le {J H' : Graph} {embJH : ℕ → Walk} {wd : WitnessData}
    (hok : WitnessOK (exists_localSpannerTools 0 0).some H' J embJH wd) :
    ∑ ci ∈ Finset.range wd.comps.length,
      ∑ b ∈ Finset.range ((wd.comps.getD ci defaultCompInfo).J_sub.m),
        (embJH ((wd.comps.getD ci defaultCompInfo).jSubOrigEdges.getD b 0)).verts.length ≤
      ∑ eJ ∈ Finset.range J.m, (embJH eJ).verts.length := by
  let S : Finset (Σ ci : Fin wd.comps.length, ℕ) :=
    (Finset.univ : Finset (Fin wd.comps.length)).sigma fun ci =>
      Finset.range wd.comps[ci.1].J_sub.m
  let f : (Σ ci : Fin wd.comps.length, ℕ) → ℕ := fun p =>
    wd.comps[p.1.1].jSubOrigEdges.getD p.2 0
  have hinj : Set.InjOn f S := by
    intro p1 hp1 p2 hp2 heq
    rw [Finset.mem_coe, Finset.mem_sigma] at hp1 hp2
    have hb1 : p1.2 < wd.comps[p1.1.1].J_sub.m := Finset.mem_range.mp hp1.2
    have hb2 : p2.2 < wd.comps[p2.1.1].J_sub.m := Finset.mem_range.mp hp2.2
    have hp1_props := hok.comp_props p1.1.1 p1.1.2
    have hp2_props := hok.comp_props p2.1.1 p2.1.2
    have ho1 : p1.2 < wd.comps[p1.1.1].jSubOrigEdges.length := by
      rw [hp1_props.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hb1
    have ho2 : p2.2 < wd.comps[p2.1.1].jSubOrigEdges.length := by
      rw [hp2_props.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hb2
    have hci_eq : p1.1 = p2.1 := by
      by_contra hne
      have hdisj := hok.comp_disjoint p1.1.1 p2.1.1 p1.1.2 p2.1.2 (fun h => hne (Fin.ext h))
      have hm1 : f p1 ∈ wd.comps[p1.1.1].jSubOrigEdges.toFinset := by
        dsimp only [f]; rw [List.mem_toFinset, List.getD_eq_getElem _ _ ho1]; exact List.getElem_mem ho1
      have hm2 : f p2 ∈ wd.comps[p2.1.1].jSubOrigEdges.toFinset := by
        dsimp only [f]; rw [List.mem_toFinset, List.getD_eq_getElem _ _ ho2]; exact List.getElem_mem ho2
      exact Finset.disjoint_left.mp hdisj hm1 (heq ▸ hm2)
    rcases p1 with ⟨⟨c1, hc1⟩, b1⟩
    rcases p2 with ⟨⟨c2, hc2⟩, b2⟩
    have hc_eq : c1 = c2 := congrArg Fin.val hci_eq
    subst hc_eq
    congr 1
    dsimp only [f] at heq
    rw [List.getD_eq_getElem _ _ ho1, List.getD_eq_getElem _ _ ho2] at heq
    exact (hp1_props.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.getElem_inj (hi := ho1) (hj := ho2)).mp heq
  have himg : S.image f ⊆ Finset.range J.m := by
    intro eJ heJ
    rcases Finset.mem_image.mp heJ with ⟨p, hp, rfl⟩
    rw [Finset.mem_sigma] at hp
    have hb : p.2 < wd.comps[p.1.1].J_sub.m := Finset.mem_range.mp hp.2
    have hprops := hok.comp_props p.1.1 p.1.2
    have ho : p.2 < wd.comps[p.1.1].jSubOrigEdges.length := by
      rw [hprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hb
    rw [Finset.mem_range]
    dsimp only [f]; rw [List.getD_eq_getElem _ _ ho]
    exact hprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (List.getElem_mem ho)
  have hsum_eq : ∑ ci ∈ Finset.range wd.comps.length,
        ∑ b ∈ Finset.range ((wd.comps.getD ci defaultCompInfo).J_sub.m),
          (embJH ((wd.comps.getD ci defaultCompInfo).jSubOrigEdges.getD b 0)).verts.length =
      ∑ p ∈ S, (embJH (f p)).verts.length := by
    rw [Finset.sum_sigma, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun ci _ => ?_
    simp [f]
  rw [hsum_eq, ← Finset.sum_image (f := fun eJ => (embJH eJ).verts.length) hinj]
  exact Finset.sum_le_sum_of_subset himg

/-- Unpacked Task 2 static context + verified memory layout & bounds from `Task2Input.Valid`. -/
structure T2Ctx (impl : SpannerToolImpl) (inp : Task2Input) (mem₀ : ℕ → ℕ) (w : ℕ) where
  wInp : WitnessCoreInput
  WSubs : List Graph
  hWInpH' : wInp.H' = inp.H'
  hWInpEmb : ∀ e < inp.J.m, wInp.embJH e = inp.embJH e
  hWInpJ : wInp.prep.J = inp.J
  hWInpJAddr : wInp.prep.jAddr = inp.jAddr
  hH' : inp.H'.IsValid
  hgH' : GraphAt mem₀ inp.hAddr inp.H'
  hJ : inp.J.IsValid
  hgJ : GraphAt mem₀ inp.jAddr inp.J
  hembJH : IsEmbedding inp.J inp.H' inp.embJH
  hEmbAt : EmbAt mem₀ inp.embJHAddr inp.J.m inp.embJH
  hEmbBd : EmbBounded mem₀ inp.embJHAddr inp.J.m inp.embJH inp.t1OutAddr
  hH'_le : inp.hAddr + inp.H'.encode.length ≤ inp.t1OutAddr
  hJ_le : inp.jAddr + inp.J.encode.length ≤ inp.t1OutAddr
  ht1_0 : mem₀ inp.t1OutAddr = wInp.statsAddr
  ht1_1 : mem₀ (inp.t1OutAddr + 1) = wInp.prep.j0Addr
  ht1_2 : mem₀ (inp.t1OutAddr + 2) = wInp.prep.nlAddr
  ht1_3 : mem₀ (inp.t1OutAddr + 3) = wInp.prep.decAddr
  ht1_4 : mem₀ (inp.t1OutAddr + 4) = wInp.prep.h
  ht1_5 : mem₀ (inp.t1OutAddr + 5) = wInp.h
  hw_j0Addr : wInp.prep.j0Addr = inp.t1OutAddr + 6 + 3 + inp.J.n + 2 * inp.H'.n
  hw_nlAddr : wInp.prep.nlAddr = wInp.prep.j0Addr + 2 + 2 * inp.J.m
  hw_decAddr : wInp.prep.decAddr = wInp.prep.nlAddr + wInp.prep.J0_strip.m
  hpst : PrepStaticState wInp.prep mem₀ mem₀
  hcdt : CompsDoneUpTo wInp.prep mem₀ wInp.prep.rawComps.length
  hstat : wInp.prep.StaticValid mem₀ w
  hws : wInp.ValidWSubs impl.constructExpander WSubs
  hφ_lb : impl.decompose.φ_lb wInp.prep.J0_strip.m ≤
    (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec
  hφ_cap : wInp.prep.phiDen_dec ≤ impl.decompose.maxPhiDen wInp.prep.J0_strip.m
  hout : wInp.OutputAt impl.constructExpander impl.pathDS.params
    (fun x => if x < wInp.h then mem₀ x else 0) mem₀ inp.v1
    (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs)
  hw_ok : ∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
    WitnessOK tools inp.H' inp.J inp.embJH
      (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs)
  hhend : wInp.prep.hEnd ≤ wInp.h
  hz0 : WordRAM.ZeroFrom mem₀ inp.v1
  hv20 : wInp.h + 20 ≤ inp.v1
  hww : inp.WordWidthOK impl w

namespace T2Ctx

noncomputable abbrev wd {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) : WitnessData :=
  ctx.wInp.mkWitnessData impl.constructExpander impl.pathDS.params ctx.WSubs

lemma hw_okW {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) :
    WitnessOK (exists_localSpannerTools 0 0).some ctx.wInp.H' ctx.wInp.prep.J ctx.wInp.embJH ctx.wd := by
  have h := ctx.hw_ok (exists_localSpannerTools 0 0).some
  rw [ctx.hWInpH', ctx.hWInpJ]
  rcases h with ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17,
    f18, f19, f20, f21, f22⟩
  exact ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17,
    f18, f19, f20, f21, f22⟩

lemma hembJHW {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) :
    IsEmbedding ctx.wInp.prep.J ctx.wInp.H' ctx.wInp.embJH := by
  refine ⟨by rw [ctx.hWInpJ, ctx.hWInpH']; exact ctx.hembJH.1, fun j hj => ?_⟩
  have hj' : j < inp.J.m := by rwa [← ctx.hWInpJ]
  have he := ctx.hembJH.2 j hj'
  rw [ctx.hWInpEmb j hj', ctx.hWInpH']
  simp only [ctx.hWInpJ] at hj ⊢
  exact he

lemma hmW_le {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) :
    ctx.wd.W.m ≤ Task1Input.mwCap impl inp.J :=
  ctx.hWInpJ ▸ task2_wd_W_m_le_mwCap ctx.hstat ctx.hw_okW ctx.hws ctx.hφ_lb

lemma hK_le {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) :
    ctx.wd.comps.length ≤ inp.J.m :=
  ctx.hWInpJ ▸ t2_comps_len_le_J ctx.hstat ctx.hw_okW ctx.hws

lemma hvhatSum_le {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) :
    (ctx.wd.comps.map fun c => c.J_sub.n).sum ≤ 2 * inp.J.m :=
  ctx.hWInpJ ▸ t2_vhatSum_le ctx.hstat ctx.hw_okW ctx.hws

lemma ds_bounds {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) :
    let wd := ctx.wd
    let p := impl.pathDS.params
    let dsOne := t2DsOne impl inp.J
    let dJ := Task1Input.dJCap impl inp.J
    let m0 := (stripLoops inp.J).m
    let γJ := p.gExp dJ m0
    let γJq := p.gQuery dJ m0
    (∀ ci (hci : ci < wd.comps.length),
      let c := wd.comps[ci]
      p.initSpace ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec c.J_sub.n c.J_sub.m wd.J0_strip.m ≤ dsOne ∧
      p.delSpace ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec c.J_sub.n c.J_sub.m wd.J0_strip.m ≤ dsOne ∧
      p.querySpace ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec c.J_sub.n c.J_sub.m wd.J0_strip.m ≤ dsOne ∧
      p.cw * (Nat.log 2 (c.J_sub.n + c.J_sub.m + ctx.wInp.prep.phiDen_dec + wd.J0_strip.m +
        ⌈p.γ_ExpPath wd.φ_dec wd.J0_strip.m⌉₊ + 2) + 1) ≤ w ∧
      ⌈p.K_init * ↑c.J_sub.m * p.γ_ExpPath wd.φ_dec wd.J0_strip.m⌉₊ ≤ c.J_sub.m * ⌈p.K_init * ↑γJ⌉₊) ∧
    ⌈p.K_del * p.γ_query wd.φ_dec wd.J0_strip.m⌉₊ ≤ ⌈p.K_del * ↑γJq⌉₊ ∧
    ⌈p.K_query * p.γ_query wd.φ_dec wd.J0_strip.m⌉₊ ≤ ⌈p.K_query * ↑γJq⌉₊ ∧
    wd.J0_strip.m = m0 ∧
    1 ≤ ctx.wInp.prep.phiNum_dec ∧ ctx.wInp.prep.phiNum_dec ≤ ctx.wInp.prep.phiDen_dec ∧
    p.γ_del wd.φ_dec wd.J0_strip.m ≤ wd.γ_del ∧
    wd.φ_ds ≤ p.φ_out wd.φ_dec wd.J0_strip.m ∧
    ⌈p.γ_ExpPath wd.φ_dec wd.J0_strip.m⌉₊ ≤ γJ ∧
    p.γ_ExpPath wd.φ_dec wd.J0_strip.m ≤ ↑(ctx.wInp.γExpInt impl.constructExpander p) :=
  t2_ds_bounds ctx.hWInpJ ctx.hstat ctx.hw_okW ctx.hφ_cap ctx.hφ_lb ctx.hww

lemma tau1Int_le_cap {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) :
    ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params ≤
      2 * Task2Input.gammaExpCap impl inp.J *
        max (impl.pathDS.params.gDel (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m)
          (impl.pathDS.params.gDel (WitnessCoreInput.dWInt impl.constructExpander)
            (Task1Input.mwCap impl inp.J)) *
        max (impl.pathDS.params.phiOutDen (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m)
          (impl.pathDS.params.phiOutDen (WitnessCoreInput.dWInt impl.constructExpander)
            (Task1Input.mwCap impl inp.J)) *
        (length inp.J inp.embJH + 1) *
        (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1) := by
  have hcaps := ctx.hWInpJ ▸ task2_scalars_le_caps ctx.hstat ctx.hφ_lb
  have hlen : length ctx.wInp.prep.J ctx.wInp.embJH = length inp.J inp.embJH := by
    rw [ctx.hWInpJ]; exact length_congr_emb (fun e he => ctx.hWInpEmb e he)
  have hvc : vcongNat ctx.wInp.prep.J ctx.wInp.H' ctx.wInp.embJH =
      vcongNat inp.J inp.H' inp.embJH := by
    rw [ctx.hWInpJ, ctx.hWInpH']; exact vcongNat_congr_emb (fun e he => ctx.hWInpEmb e he)
  have hmd : maxDeg ctx.wInp.prep.J = maxDeg inp.J := by rw [ctx.hWInpJ]
  unfold WitnessCoreInput.tau1Int WitnessCoreInput.tau2Int
  rw [hlen, hvc, hmd]
  have h1 := hcaps.1; have h2 := hcaps.2.1; have h3 := hcaps.2.2
  have ht2 : ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params *
        ctx.wInp.γDelInt impl.constructExpander impl.pathDS.params *
        ctx.wInp.phiDsDenInt impl.constructExpander impl.pathDS.params ≤
      Task2Input.gammaExpCap impl inp.J *
        max (impl.pathDS.params.gDel (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m)
          (impl.pathDS.params.gDel (WitnessCoreInput.dWInt impl.constructExpander)
            (Task1Input.mwCap impl inp.J)) *
        max (impl.pathDS.params.phiOutDen (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m)
          (impl.pathDS.params.phiOutDen (WitnessCoreInput.dWInt impl.constructExpander)
            (Task1Input.mwCap impl inp.J)) :=
    Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have ha : 2 * (ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params *
        ctx.wInp.γDelInt impl.constructExpander impl.pathDS.params *
        ctx.wInp.phiDsDenInt impl.constructExpander impl.pathDS.params) *
        length inp.J inp.embJH ≤
      2 * (Task2Input.gammaExpCap impl inp.J *
        max (impl.pathDS.params.gDel (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m)
          (impl.pathDS.params.gDel (WitnessCoreInput.dWInt impl.constructExpander)
            (Task1Input.mwCap impl inp.J)) *
        max (impl.pathDS.params.phiOutDen (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m)
          (impl.pathDS.params.phiOutDen (WitnessCoreInput.dWInt impl.constructExpander)
            (Task1Input.mwCap impl inp.J))) *
        (length inp.J inp.embJH + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 ht2) (Nat.le_succ _)
  have hb := Nat.mul_le_mul ha (Nat.le_succ (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J))
  simpa only [mul_assoc] using hb

/-- Static component/weight/header facts extracted from `OutputAt` inside `[0, inp.v1)`. -/
def StaticOutAt {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (mem : ℕ → ℕ) : Prop :=
  let prepH := ctx.wInp.prep.h
  let wH := ctx.wInp.h
  let aCompExt := mem (wH + 12)
  let wAddr := mem (wH + 13)
  let wWNumAddr := mem (wH + 14)
  mem inp.t1OutAddr = ctx.wInp.statsAddr ∧
  mem (inp.t1OutAddr + 1) = ctx.wInp.prep.j0Addr ∧
  mem (inp.t1OutAddr + 2) = ctx.wInp.prep.nlAddr ∧
  mem (inp.t1OutAddr + 3) = ctx.wInp.prep.decAddr ∧
  mem (inp.t1OutAddr + 4) = prepH ∧
  mem (inp.t1OutAddr + 5) = wH ∧
  mem (wH + 8) = ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params ∧
  mem (wH + 10) = ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params ∧
  mem (wH + 17) = ctx.wInp.prep.phiNum_dec ∧
  mem (wH + 18) = ctx.wInp.prep.phiDen_dec ∧
  mem (wH + 19) = ctx.wInp.prep.J0_strip.m ∧
  wH + 20 ≤ aCompExt ∧
  aCompExt + 6 * ctx.wd.comps.length ≤ wAddr ∧
  wWNumAddr = wAddr + (2 + 2 * ctx.wd.W.m) ∧
  wWNumAddr + ctx.wd.W.m ≤ inp.v1 ∧
  CompExtAt mem aCompExt ctx.wInp.prep.phiNum_dec wAddr ctx.wd.comps ∧
  GraphAt mem wAddr ctx.wd.W ∧
  ∀ eW < ctx.wd.W.m,
    (mem (wWNumAddr + eW) : ℝ) / (ctx.wInp.prep.phiDen_dec : ℝ) = ctx.wd.wW eW ∧
    1 ≤ mem (wWNumAddr + eW)

lemma staticOutAt_init {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) : StaticOutAt ctx mem₀ := by
  have ho := ctx.hout
  rcases ho with ⟨_, _, _, _, _, _, _, _, _, _, _, _, h8, _, h10, _, h17, h18, h19, rest⟩
  dsimp only at rest
  rcases rest with ⟨ha1, ha2, ha3, ha4, ha5, ha6, hce, hgw, hwwn, _, _⟩
  have hv1_bound : mem₀ (ctx.wInp.h + 14) + ctx.wd.W.m ≤ inp.v1 := by
    dsimp only [T2Ctx.wd]
    omega
  exact ⟨ctx.ht1_0, ctx.ht1_1, ctx.ht1_2, ctx.ht1_3, ctx.ht1_4, ctx.ht1_5,
    h8, h10, h17, h18, h19, ha1, ha2, ha3, hv1_bound, hce, hgw, hwwn⟩

lemma agrees_preserves_static {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ mem' : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (hagree : ∀ x < inp.v1, mem' x = mem₀ x) :
    GraphAt mem' inp.hAddr inp.H' ∧
    GraphAt mem' inp.jAddr inp.J ∧
    EmbAt mem' inp.embJHAddr inp.J.m inp.embJH ∧
    EmbBounded mem' inp.embJHAddr inp.J.m inp.embJH inp.t1OutAddr ∧
    PrepStaticState ctx.wInp.prep mem' mem' ∧
    CompsDoneUpTo ctx.wInp.prep mem' ctx.wInp.prep.rawComps.length ∧
    ctx.wInp.prep.StaticValid mem' w ∧
    StaticOutAt ctx mem' := by
  have ht1_lt : inp.t1OutAddr + 6 ≤ ctx.wInp.prep.h := by
    have hdec := ctx.hstat.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have := ctx.hw_j0Addr; have := ctx.hw_nlAddr; have := ctx.hw_decAddr
    omega
  have hprep_le_hEnd : ctx.wInp.prep.h ≤ ctx.wInp.prep.hEnd := by
    have h0 := ctx.wInp.prep.hBlocksStart_eq
    have h1 := ctx.wInp.prep.cJSubPtr_le_hEnd (Nat.zero_le _)
    have h2 : ctx.wInp.prep.hBlocksStart = ctx.wInp.prep.cJSubPtr 0 :=
      ctx.wInp.prep.cJSubPtr_zero.symm
    unfold PrepInput.aVLoc PrepInput.aVComp PrepInput.aComps PrepInput.aJ0Out
      PrepInput.aEdgeNext PrepInput.aLvlHead at h0
    omega
  have hhend_lt : ctx.wInp.prep.hEnd ≤ inp.v1 := le_trans ctx.hhend (by have := ctx.hv20; omega)
  have ht1_v1 : inp.t1OutAddr ≤ inp.v1 := by omega
  have hH_at := GraphAt.of_agree_below ctx.hgH' (le_trans ctx.hH'_le ht1_v1) hagree
  have hJ_at := GraphAt.of_agree_below ctx.hgJ (le_trans ctx.hJ_le ht1_v1) hagree
  have ⟨hEmb, hEB⟩ := embAt_preserve ctx.hEmbAt ctx.hEmbBd fun k hk =>
    hagree k (lt_of_lt_of_le hk ht1_v1)
  have hpr : ∀ x < ctx.wInp.prep.hEnd, mem' x = mem₀ x := fun x hx =>
    hagree x (lt_of_lt_of_le hx hhend_lt)
  have hss_cd := prepStatic_and_comps_of_agree_range ctx.hstat ctx.hpst ctx.hcdt
    (fun x _ hx => hpr x hx)
  have hsv := PrepInput.StaticValid.of_agree_below ctx.hstat
    (fun x hx => hpr x (lt_of_lt_of_le hx hprep_le_hEnd))
  have hs0 := ctx.staticOutAt_init
  rcases hs0 with ⟨s0, s1, s2, s3, s4, s5, s8, s10, s17, s18, s19, ha1, ha2, ha3, ha_le,
    hce, hgw, hwwn⟩
  have hwH20 : ctx.wInp.h + 20 ≤ inp.v1 := ctx.hv20
  have ha_hdr : ∀ k < 20, mem' (ctx.wInp.h + k) = mem₀ (ctx.wInp.h + k) := fun k hk =>
    hagree _ (by omega)
  refine ⟨hH_at, hJ_at, hEmb, hEB, hss_cd.1, hss_cd.2, hsv, ?_⟩
  refine ⟨by rw [hagree _ (by omega)]; exact s0, by rw [hagree _ (by omega)]; exact s1,
    by rw [hagree _ (by omega)]; exact s2, by rw [hagree _ (by omega)]; exact s3,
    by rw [hagree _ (by omega)]; exact s4, by rw [hagree _ (by omega)]; exact s5,
    by rw [ha_hdr 8 (by omega)]; exact s8, by rw [ha_hdr 10 (by omega)]; exact s10,
    by rw [ha_hdr 17 (by omega)]; exact s17, by rw [ha_hdr 18 (by omega)]; exact s18,
    by rw [ha_hdr 19 (by omega)]; exact s19, ?_⟩
  rw [ha_hdr 12 (by omega), ha_hdr 13 (by omega), ha_hdr 14 (by omega)]
  refine ⟨ha1, ha2, ha3, ha_le, ?_, ?_, ?_⟩
  · intro ci hci
    rcases hce ci hci with ⟨c0, c2, c3, c4, c5, cg, cg_ge, cg_le⟩
    dsimp only
    have hptr : mem' (mem₀ (ctx.wInp.h + 12) + 6 * ci + 1) =
        mem₀ (mem₀ (ctx.wInp.h + 12) + 6 * ci + 1) := hagree _ (by omega)
    rw [hptr]
    refine ⟨by rw [hagree _ (by omega)]; exact c0,
      by rw [hagree _ (by omega)]; exact c2,
      by rw [hagree _ (by omega)]; exact c3,
      by rw [hagree _ (by omega)]; exact c4,
      by rw [hagree _ (by omega)]; exact c5,
      GraphAt.of_agree_below cg (by rw [graph_encode_length]; exact le_trans cg_le (by omega)) hagree,
      cg_ge, cg_le⟩
  · exact GraphAt.of_agree_below hgw (by rw [graph_encode_length]; omega) hagree
  · intro eW heW
    rw [hagree _ (by omega)]
    exact hwwn eW heW

end T2Ctx

/-- Unpack `Task2Input.Valid` into a usable `T2Ctx`. -/
lemma t2_unpack_valid {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (hv : inp.Valid impl mem₀ w) : Nonempty (T2Ctx impl inp mem₀ w) := by
  rcases hv with ⟨hH', hgH', hJ, hgJ, hembJH, hEmbAt, hEmbBd, hH'_le, hJ_le,
    ⟨memPre, wInp, WSubs, hwH', hwEmb, hwJ, hwJAddr, _, hw_j0Addr, hw_nlAddr, hw_decAddr, _, _,
      hzf, hv20, _, ht0, ht1, ht2, ht3, ht4, ht5, _, _, _, hpst, hcdt, hstat, hws, hφ_lb, hφ_cap,
      hout, hw_ok, hhend⟩, hww⟩
  exact ⟨⟨wInp, WSubs, hwH', hwEmb, hwJ, hwJAddr, hH', hgH', hJ, hgJ, hembJH, hEmbAt, hEmbBd,
    hH'_le, hJ_le, ht0, ht1, ht2, ht3, ht4, ht5, hw_j0Addr, hw_nlAddr, hw_decAddr,
    hpst, hcdt, hstat, hws, hφ_lb, hφ_cap,
    hout (fun _ => 0), hw_ok, hhend, hzf, hv20, hww⟩⟩

end MinCostFlow.Spanner
