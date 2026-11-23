module

public import MinCostFlow.Spanner.ProgTask2StepsDrainBase

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Pure math, weight bounds, walk bounds, and congestion helpers for `t2MiddleEdge` -/

/-- Round-local vertex congestion invariant across `t2MiddleEdge` / `t2DrainQueue` calls:
all vertices stay `≤ (η₁ + 1/2) · τ₁`, and vertices outside `procVerts` stay `≤ η₁ · τ₁`. -/
def T2VcongRoundInv {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (g : T2Ghost impl.pathDS) : Prop :=
  (∀ x < inp.H'.n,
    vcongAt ctx.wd.W ctx.wd.wW (compose inp.J inp.embJH (partialToWalk g.emb)) x ≤
      ((g.η₁ : ℝ) + 1 / 2) * ctx.wd.τ₁) ∧
  (∀ x < inp.H'.n, x ∉ g.procVerts →
    vcongAt ctx.wd.W ctx.wd.wW (compose inp.J inp.embJH (partialToWalk g.emb)) x ≤
      (g.η₁ : ℝ) * ctx.wd.τ₁)

lemma t2VcongRoundInv_of_initJ0 {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) {stc : T2StaticData ctx} {g : T2Ghost impl.pathDS} {mem : ℕ → ℕ}
    (hS : T2StepInv ctx stc g mem) (hη : g.η₁ = 1) (hemb : g.emb = g.emb_prev) :
    T2VcongRoundInv ctx g := by
  have hτ : 0 ≤ ctx.wd.τ₁ := ctx.hw_okW.τ₁_nonneg
  refine ⟨fun x hx => ?_, fun x hx _ => ?_⟩
  · have hv := hS.hVc_prev x hx
    rw [← hemb] at hv
    rw [hη] at hv ⊢
    simp only [Nat.sub_self, Nat.cast_zero, zero_add] at hv
    push_cast; linarith
  · have hv := hS.hVc_prev x hx
    rw [← hemb] at hv
    rw [hη] at hv ⊢
    simp only [Nat.sub_self, Nat.cast_zero, zero_add] at hv
    push_cast; linarith

lemma t2VcongRoundInv_next_round {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) {g g' : T2Ghost impl.pathDS}
    (hV : T2VcongRoundInv ctx g) (hη : g'.η₁ = g.η₁ + 1) (hemb : g'.emb = g.emb) :
    (∀ x < inp.H'.n,
      vcongAt ctx.wd.W ctx.wd.wW (compose inp.J inp.embJH (partialToWalk g.emb)) x ≤
        ((g.η₁ : ℝ) + 1 / 2) * ctx.wd.τ₁) ∧
    (∀ x < inp.H'.n,
      vcongAt ctx.wd.W ctx.wd.wW (compose inp.J inp.embJH (partialToWalk g'.emb)) x ≤
        ((g'.η₁ : ℝ) + 1 / 2) * ctx.wd.τ₁) ∧
    (∀ x < inp.H'.n, x ∉ g'.procVerts →
      vcongAt ctx.wd.W ctx.wd.wW (compose inp.J inp.embJH (partialToWalk g'.emb)) x ≤
        (g'.η₁ : ℝ) * ctx.wd.τ₁) := by
  have hτ : 0 ≤ ctx.wd.τ₁ := ctx.hw_okW.τ₁_nonneg
  refine ⟨hV.1, fun x hx => ?_, fun x hx _ => ?_⟩
  · rw [hemb, hη]; push_cast; linarith [hV.1 x hx]
  · rw [hemb, hη]; push_cast; linarith [hV.1 x hx]

lemma t2VcongRoundInv_drain {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) {g g' : T2Ghost impl.pathDS}
    (hV : T2VcongRoundInv ctx g) (hη : g'.η₁ = g.η₁) (hemb : g'.emb = g.emb)
    (hp : g'.procVerts = g.procVerts) :
    T2VcongRoundInv ctx g' := by
  simpa [T2VcongRoundInv, hη, hemb, hp] using hV

private lemma graph_deg_eq_range_sum {G : Graph} (hG : G.IsValid) (v : ℕ) :
    G.deg v = ∑ b ∈ Finset.range G.m,
      ((if (G.edges.getD b (0, 0)).1 = v then 1 else 0) +
       (if (G.edges.getD b (0, 0)).2 = v then 1 else 0)) := by
  have hins : G.inside G.verts = G.edges := by
    unfold Graph.inside
    exact List.filter_eq_self.mpr fun e he => by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Graph.verts, Finset.mem_range]
      exact hG e he
  have hfilt : ∀ p : ℕ × ℕ → Prop, [DecidablePred p] →
      (G.edges.filter (fun e => decide (p e))).length =
        ∑ b ∈ Finset.range G.m, if p (G.edges.getD b (0, 0)) then 1 else 0 := fun p _ => by
    have hs1 : (∑ b ∈ Finset.range G.m, if p (G.edges.getD b (0, 0)) then 1 else 0) =
        ∑ idx : Fin G.edges.length, if p (G.edges[idx.1]'idx.2) then 1 else 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun idx _ => ?_
      rw [List.getD_eq_getElem _ _ idx.2]
      exact if_congr Iff.rfl rfl rfl
    rw [hs1]
    clear hs1
    induction G.edges with
    | nil => simp
    | cons e es ih =>
      simp only [List.length_cons, Fin.sum_univ_succ, Fin.val_zero, List.getElem_cons_zero,
        Fin.val_succ, List.getElem_cons_succ, List.filter_cons]
      by_cases hp : p e
      · simp [hp, ih]; omega
      · simp [hp, ih]
  unfold Graph.deg Graph.degIn
  rw [hins, hfilt (fun e => e.1 = v), hfilt (fun e => e.2 = v), ← Finset.sum_add_distrib]

private lemma buildCompsFrom_edge_find (inp : WitnessCoreInput) :
    ∀ offset raw ws, ws.length = raw.length →
      ∀ k < (ws.map Graph.m).sum,
        let cs := inp.buildCompsFrom offset raw ws
        ∃ ci, ∃ (hci : ci < cs.length), ∃ eL, eL < cs[ci].W_sub.m ∧
          offset + k = cs[ci].wStart + eL
  | _, [], [], _, k, hk => by simp at hk
  | offset, _ :: rest, W :: ws, hlen, k, hk => by
    simp only [List.length_cons] at hlen
    simp only [List.map_cons, List.sum_cons] at hk
    by_cases hkW : k < W.m
    · exact ⟨0, by simp [WitnessCoreInput.buildCompsFrom], k, by simpa [WitnessCoreInput.buildCompsFrom], rfl⟩
    · have hk' : k - W.m < (ws.map Graph.m).sum := by omega
      obtain ⟨ci, hci, eL, heL, heq⟩ := buildCompsFrom_edge_find inp (offset + W.m) rest ws (by omega) (k - W.m) hk'
      refine ⟨ci + 1, by simpa [WitnessCoreInput.buildCompsFrom] using hci, eL, heL, ?_⟩
      change offset + k = (inp.buildCompsFrom (offset + W.m) rest ws)[ci].wStart + eL
      omega

lemma t2_wW_le_maxDeg {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) {eW : ℕ} (heW : eW < ctx.wd.W.m) :
    ctx.wd.wW eW ≤ (maxDeg inp.J : ℝ) := by
  by_cases hj0 : eW < ctx.wd.j0Edges.length
  · have hm := mkW_W_edges_j0 (WSubs := ctx.WSubs) (ce := impl.constructExpander) (pds := impl.pathDS.params) hj0
    rw [hm.2.2]
    have hj_lt : ctx.wd.j0Edges.getD eW 0 < inp.J.m := by
      rw [List.getD_eq_getElem _ _ hj0, ← ctx.hWInpJ]
      exact ctx.hw_okW.j0_lt _ (List.getElem_mem hj0)
    set e := inp.J.edges[ctx.wd.j0Edges.getD eW 0]'hj_lt
    have hv1 : e.1 < inp.J.n := (ctx.hJ e (List.getElem_mem hj_lt)).1
    have hdeg1 : 1 ≤ inp.J.deg e.1 := by
      rw [graph_deg_eq_range_sum ctx.hJ]
      have hterm := Finset.single_le_sum (fun b _ => Nat.zero_le
        ((if (inp.J.edges.getD b (0, 0)).1 = e.1 then 1 else 0) +
         (if (inp.J.edges.getD b (0, 0)).2 = e.1 then 1 else 0))) (Finset.mem_range.mpr hj_lt)
      have h1 : (inp.J.edges.getD (ctx.wd.j0Edges.getD eW 0) (0, 0)).1 = e.1 := by
        rw [List.getD_eq_getElem _ _ hj_lt]
      rw [h1] at hterm; simp only [↓reduceIte] at hterm; omega
    have hle : (1 : ℝ) ≤ (maxDeg inp.J : ℝ) := by
      exact_mod_cast le_trans hdeg1 (deg_le_maxDeg hv1)
    exact le_trans ctx.hw_okW.φ_dec_le hle
  · have heW_ge : ctx.wd.j0Edges.length ≤ eW := Nat.le_of_not_lt hj0
    have hWm_eq : ctx.wd.W.m = ctx.wd.j0Edges.length + (ctx.WSubs.map Graph.m).sum :=
      mkWitnessData_W_m_eq_sum ctx.wInp impl.constructExpander impl.pathDS.params ctx.hws.1
    have hk_lt : eW - ctx.wd.j0Edges.length < (ctx.WSubs.map Graph.m).sum := by omega
    obtain ⟨ci, hci0, eL, heL, heq⟩ := buildCompsFrom_edge_find ctx.wInp ctx.wd.j0Edges.length
      ctx.wInp.prep.rawComps ctx.WSubs ctx.hws.1 (eW - ctx.wd.j0Edges.length) hk_lt
    have hci : ci < ctx.wd.comps.length := hci0
    have heW_eq : eW = ctx.wd.comps[ci].wStart + eL := by
      change ctx.wd.j0Edges.length + (eW - ctx.wd.j0Edges.length) = ctx.wd.comps[ci].wStart + eL at heq
      omega
    rw [heW_eq]
    have hm := mkW_W_edges_comp (pds := impl.pathDS.params) ctx.hws hci heL
    rw [hm.2.2.2]
    rcases ctx.hw_okW.comp_props ci hci with
      ⟨_, _, hXJ_c, _, hverts_c, hc_Jn, hc_Jvalid, hc_Jm_pos, _, _, _, _, _, _, _, _, _, _,
       hdeg_ge_phi_c, hjOrig_c⟩
    set c := ctx.wd.comps[ci]'hci
    have h0lt_n : 0 < c.J_sub.n := by omega
    have hφ_le_Jsub : ctx.wd.φ_dec * 2 ^ c.level ≤ (c.J_sub.deg 0 : ℝ) :=
      hdeg_ge_phi_c 0 (hc_Jn ▸ h0lt_n)
    have hv0_lt : 0 < c.verts.length := by rw [hverts_c, vertsOf, Finset.length_sort, ← hc_Jn]; exact h0lt_n
    set v0 := c.verts.getD 0 0
    have hv0_mem : v0 ∈ c.X := by dsimp only [v0]; rw [hverts_c]; exact getD_vertsOf_mem (by omega)
    have hv0_J : v0 < inp.J.n := Finset.mem_range.mp (ctx.hWInpJ ▸ hXJ_c hv0_mem)
    have hinj : Set.InjOn (fun b => c.jSubOrigEdges.getD b 0) (Finset.range c.J_sub.m) := by
      intro a ha b hb hab
      have ha' := Finset.mem_range.mp ha; have hb' := Finset.mem_range.mp hb
      have hja : a < c.jSubOrigEdges.length := by rw [hjOrig_c.1]; exact ha'
      have hjb : b < c.jSubOrigEdges.length := by rw [hjOrig_c.1]; exact hb'
      dsimp only at hab
      rw [List.getD_eq_getElem _ _ hja, List.getD_eq_getElem _ _ hjb] at hab
      exact congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hjOrig_c.2.1)
        (a₁ := ⟨a, hja⟩) (a₂ := ⟨b, hjb⟩) hab)
    have himg : (Finset.range c.J_sub.m).image (fun b => c.jSubOrigEdges.getD b 0) ⊆ Finset.range inp.J.m := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨b, hb, rfl⟩
      have hb' := Finset.mem_range.mp hb
      have hjb : b < c.jSubOrigEdges.length := by rw [hjOrig_c.1]; exact hb'
      rw [Finset.mem_range, ← ctx.hWInpJ, List.getD_eq_getElem _ _ hjb]
      exact hjOrig_c.2.2.1 _ (List.getElem_mem hjb)
    have hnd_v : c.verts.Nodup := by
      rw [hverts_c]; exact vertsOf_nodup c.X
    have hJedge := mkW_comp_jOrig_edge ctx.hstat ctx.hw_okW ctx.hws hci
    have hdeg_le : c.J_sub.deg 0 ≤ inp.J.deg v0 := by
      rw [graph_deg_eq_range_sum hc_Jvalid, graph_deg_eq_range_sum ctx.hJ]
      have hpt : ∀ b ∈ Finset.range c.J_sub.m,
          ((if (c.J_sub.edges.getD b (0, 0)).1 = 0 then 1 else 0) +
           (if (c.J_sub.edges.getD b (0, 0)).2 = 0 then 1 else 0)) ≤
          ((if (inp.J.edges.getD (c.jSubOrigEdges.getD b 0) (0, 0)).1 = v0 then 1 else 0) +
           (if (inp.J.edges.getD (c.jSubOrigEdges.getD b 0) (0, 0)).2 = v0 then 1 else 0)) := fun b hb => by
        have hb' := Finset.mem_range.mp hb
        have heq := ctx.hWInpJ ▸ (hJedge b hb').2
        change _ = (c.verts.getD (c.J_sub.edges.getD b (0, 0)).1 0,
          c.verts.getD (c.J_sub.edges.getD b (0, 0)).2 0) at heq
        rw [heq]; dsimp only
        have hc_edge := hc_Jvalid (c.J_sub.edges[b]'(by simpa [Graph.m] using hb')) (List.getElem_mem _)
        have hd1 : (c.J_sub.edges.getD b (0, 0)).1 < c.verts.length := by
          rw [List.getD_eq_getElem _ _ (by simpa [Graph.m] using hb')]
          rw [hverts_c, vertsOf, Finset.length_sort, ← hc_Jn]; exact hc_edge.1
        have hd2 : (c.J_sub.edges.getD b (0, 0)).2 < c.verts.length := by
          rw [List.getD_eq_getElem _ _ (by simpa [Graph.m] using hb')]
          rw [hverts_c, vertsOf, Finset.length_sort, ← hc_Jn]; exact hc_edge.2
        have hiff : ∀ k < c.verts.length, (c.verts.getD k 0 = v0 ↔ k = 0) := fun k hk => by
          rw [List.getD_eq_getElem _ _ hk]; dsimp only [v0]; rw [List.getD_eq_getElem _ _ hv0_lt]
          constructor
          · intro h
            exact congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hnd_v)
              (a₁ := ⟨k, hk⟩) (a₂ := ⟨0, hv0_lt⟩) h)
          · rintro rfl; rfl
        have h1 := hiff _ hd1
        have h2 := hiff _ hd2
        simp only [h1, h2, le_refl]
      refine le_trans (Finset.sum_le_sum hpt) ?_
      have himg_sum : ∑ b ∈ Finset.range c.J_sub.m,
          ((if (inp.J.edges.getD (c.jSubOrigEdges.getD b 0) (0, 0)).1 = v0 then 1 else 0) +
           (if (inp.J.edges.getD (c.jSubOrigEdges.getD b 0) (0, 0)).2 = v0 then 1 else 0)) =
          ∑ eJ ∈ (Finset.range c.J_sub.m).image (fun b => c.jSubOrigEdges.getD b 0),
          ((if (inp.J.edges.getD eJ (0, 0)).1 = v0 then 1 else 0) +
           (if (inp.J.edges.getD eJ (0, 0)).2 = v0 then 1 else 0)) :=
        (Finset.sum_image (f := fun eJ =>
          (if (inp.J.edges.getD eJ (0, 0)).1 = v0 then 1 else 0) +
          (if (inp.J.edges.getD eJ (0, 0)).2 = v0 then 1 else 0))
          (fun a ha b hb hab => hinj ha hb hab)).symm
      rw [himg_sum]
      exact Finset.sum_le_sum_of_subset himg
    have hmax : c.J_sub.deg 0 ≤ maxDeg inp.J := le_trans hdeg_le (deg_le_maxDeg hv0_J)
    exact le_trans hφ_le_Jsub (by exact_mod_cast hmax)

lemma t2_wW_le_tau1_half {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) {eW : ℕ} (heW : eW < ctx.wd.W.m) :
    ctx.wd.wW eW ≤ ctx.wd.τ₁ / 2 := by
  have h1 := t2_wW_le_maxDeg ctx heW
  have hsc := ctx.wInp.mkWitnessData_scalars impl.constructExpander impl.pathDS.params ctx.WSubs ctx.hstat
  have hds_ge2 : 2 ≤ ctx.wInp.phiDsDenInt impl.constructExpander impl.pathDS.params := by
    have hpos : (0 : ℝ) < ctx.wInp.phiDsDenInt impl.constructExpander impl.pathDS.params := by
      have := ctx.hw_okW.φ_ds_pos; rw [hsc.2.1] at this
      exact_mod_cast Nat.pos_of_ne_zero (fun h0 => by simp [h0] at this)
    have hhalf : (1 : ℝ) / (ctx.wInp.phiDsDenInt impl.constructExpander impl.pathDS.params : ℝ) ≤ 1 / 2 :=
      hsc.2.1 ▸ ctx.hw_okW.φ_ds_half
    have h2r : (2 : ℝ) ≤ (ctx.wInp.phiDsDenInt impl.constructExpander impl.pathDS.params : ℝ) := by
      have := (div_le_div_iff₀ hpos (by norm_num)).mp hhalf; linarith
    exact_mod_cast h2r
  have hγE_ge1 : 1 ≤ ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params := by
    have hle := ctx.hw_okW.γ_ExpPath_ge; rw [hsc.2.1, hsc.2.2.1] at hle
    have hpos : (0 : ℝ) < ctx.wInp.phiDsDenInt impl.constructExpander impl.pathDS.params := by
      exact_mod_cast (by omega : 0 < ctx.wInp.phiDsDenInt impl.constructExpander impl.pathDS.params)
    have h2γ : (2 : ℝ) ≤ ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params := by
      calc (2 : ℝ) ≤ ctx.wInp.phiDsDenInt impl.constructExpander impl.pathDS.params := by exact_mod_cast hds_ge2
        _ = 1 / (1 / (ctx.wInp.phiDsDenInt impl.constructExpander impl.pathDS.params : ℝ)) := by field_simp
        _ ≤ ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params := hle
    exact_mod_cast le_trans (by norm_num : (1 : ℝ) ≤ 2) h2γ
  have hγD_ge1 : 1 ≤ ctx.wInp.γDelInt impl.constructExpander impl.pathDS.params := by
    have := ctx.hw_okW.γ_del_ge; rw [hsc.2.2.2.1] at this; exact_mod_cast this
  have htau2_ge1 : 1 ≤ ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params := by
    unfold WitnessCoreInput.tau2Int
    exact Nat.le_trans (by omega) (Nat.mul_le_mul (Nat.mul_le_mul hγE_ge1 hγD_ge1) hds_ge2)
  have hlenJ : 1 ≤ length inp.J inp.embJH := by
    rw [← ctx.hWInpJ]
    have hl : 1 ≤ length ctx.wInp.prep.J ctx.wInp.embJH := by
      have hw_len := ctx.hw_okW.W_m_eq
      have hnonloop_len : ∀ e < ctx.wInp.prep.J.m,
          (ctx.wInp.prep.J.edges.getD e (0, 0)).1 ≠ (ctx.wInp.prep.J.edges.getD e (0, 0)).2 →
          1 ≤ length ctx.wInp.prep.J ctx.wInp.embJH := fun e he_m hne => by
        have hwk := ctx.hembJHW.2 e he_m
        have he_pos : 1 ≤ (ctx.wInp.embJH e).edges.length := by
          rcases hwk.2.2 with ⟨_, _, heq⟩ | ⟨hnn, _⟩
          · rw [← List.getD_eq_getElem _ (0, 0) he_m] at heq; exact absurd heq hne
          · exact Nat.pos_of_ne_zero (by simpa [List.length_eq_zero_iff] using hnn)
        exact le_trans he_pos (Finset.le_sup (f := fun j => (ctx.wInp.embJH j).edges.length)
          (Finset.mem_range.mpr he_m))
      by_cases hj0_pos : 0 < ctx.wd.j0Edges.length
      · have he_nl := mkW_j0_nonloop ctx.hstat hj0_pos
        exact hnonloop_len _ he_nl.1 he_nl.2
      · have hcomp_pos : 0 < ctx.wd.comps.length := by
          by_contra h0
          have h0' : ctx.wd.comps = [] := List.eq_nil_iff_length_eq_zero.mpr (by omega)
          have hj0' : ctx.wd.j0Edges.length = 0 := by omega
          rw [hj0', h0'] at hw_len; simp at hw_len; omega
        rcases ctx.hw_okW.comp_props 0 hcomp_pos with
          ⟨_, _, _, _, _, _, _, hc_Jm, _, _, _, _, _, _, _, _, _, _, _, hjOrig⟩
        have he_nl := mkW_comp_jOrig_nonloop ctx.hstat ctx.hws hcomp_pos (by rw [hjOrig.1]; exact hc_Jm)
        exact hnonloop_len _ he_nl.1 he_nl.2
    rw [length_congr_emb (fun e he => ctx.hWInpEmb e (ctx.hWInpJ ▸ he))] at hl; exact hl
  have h2m : 2 * maxDeg inp.J ≤ ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params := by
    unfold WitnessCoreInput.tau1Int
    have hlen_w : length ctx.wInp.prep.J ctx.wInp.embJH = length inp.J inp.embJH := by
      rw [ctx.hWInpJ]; exact length_congr_emb (fun e he => ctx.hWInpEmb e he)
    rw [hlen_w, ctx.hWInpJ]
    have hprod : 1 ≤ ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params * length inp.J inp.embJH :=
      Nat.le_trans (by decide) (Nat.mul_le_mul htau2_ge1 hlenJ)
    nlinarith
  have hr : (maxDeg inp.J : ℝ) ≤ ctx.wd.τ₁ / 2 := by
    have := hsc.2.2.2.2.2
    have hr2 : (2 : ℝ) * (maxDeg inp.J : ℝ) ≤ ctx.wd.τ₁ := by
      rw [this]; exact_mod_cast h2m
    linarith
  exact le_trans h1 hr

lemma t2_wWNum_le_maxDeg {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) {wWNum : ℕ → ℕ}
    (hwN : ∀ eW < ctx.wd.W.m,
      (wWNum eW : ℝ) / (ctx.wInp.prep.phiDen_dec : ℝ) = ctx.wd.wW eW)
    {eW : ℕ} (heW : eW < ctx.wd.W.m) :
    wWNum eW ≤ maxDeg inp.J * ctx.wInp.prep.phiDen_dec := by
  have hden_pos : (0 : ℝ) < ctx.wInp.prep.phiDen_dec := by
    have := ctx.hstat.2.2.2.2.2.2.2.2.1; have := ctx.hstat.2.2.2.2.2.2.2.2.2.1
    exact_mod_cast (by omega : 0 < ctx.wInp.prep.phiDen_dec)
  have hle : (wWNum eW : ℝ) / (ctx.wInp.prep.phiDen_dec : ℝ) ≤ (maxDeg inp.J : ℝ) := by
    rw [hwN eW heW]; exact t2_wW_le_maxDeg ctx heW
  have hr : (wWNum eW : ℝ) ≤ ((maxDeg inp.J * ctx.wInp.prep.phiDen_dec : ℕ) : ℝ) := by
    rw [div_le_iff₀ hden_pos] at hle; push_cast; exact hle
  exact_mod_cast hr

lemma t2_vcongNumPure_le {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) {wWNum : ℕ → ℕ}
    (hwN : ∀ eW < ctx.wd.W.m,
      (wWNum eW : ℝ) / (ctx.wInp.prep.phiDen_dec : ℝ) = ctx.wd.wW eW)
    (emb : ℕ → Option Walk) (x : ℕ) :
    vcongNumPure ctx.wd inp.J inp.embJH wWNum emb x ≤
      ctx.wd.W.m * (maxDeg inp.J * ctx.wInp.prep.phiDen_dec) := by
  unfold vcongNumPure
  have hsum : ∑ eW ∈ Finset.range ctx.wd.W.m,
        (if x ∈ (compose inp.J inp.embJH (partialToWalk emb) eW).verts then wWNum eW else 0) ≤
      ∑ _eW ∈ Finset.range ctx.wd.W.m, (maxDeg inp.J * ctx.wInp.prep.phiDen_dec) := by
    refine Finset.sum_le_sum fun eW heW => ?_
    split_ifs
    · exact t2_wWNum_le_maxDeg ctx hwN (Finset.mem_range.mp heW)
    · exact Nat.zero_le _
  exact le_trans hsum (by rw [Finset.sum_const, Finset.card_range, smul_eq_mul])

private lemma walk_edge_ne_of_lt {G : Graph} {P : Walk}
    (hnd : P.verts.Nodup) (hlen : P.verts.length = P.edges.length + 1)
    (hstep : ∀ idx < P.edges.length,
      Walk.EdgeMatches (G.edges.getD (P.edges.getD idx 0) (0, 0))
        (P.verts.getD idx 0) (P.verts.getD (idx + 1) 0))
    {i j : ℕ} (hi : i < P.edges.length) (hj : j < P.edges.length) (hlt : i < j) :
    P.edges[i] ≠ P.edges[j] := by
  intro heq
  have h1 := hstep i hi
  have h2 := hstep j hj
  rw [List.getD_eq_getElem _ _ hi, heq, ← List.getD_eq_getElem _ _ hj] at h1
  have hvi_eq : P.verts.getD i 0 = P.verts[i]'(by omega) := List.getD_eq_getElem _ _ (by omega)
  have hvi1_eq : P.verts.getD (i + 1) 0 = P.verts[i + 1]'(by omega) := List.getD_eq_getElem _ _ (by omega)
  have hvj_eq : P.verts.getD j 0 = P.verts[j]'(by omega) := List.getD_eq_getElem _ _ (by omega)
  have hvj1_eq : P.verts.getD (j + 1) 0 = P.verts[j + 1]'(by omega) := List.getD_eq_getElem _ _ (by omega)
  rw [hvi_eq, hvi1_eq] at h1; rw [hvj_eq, hvj1_eq] at h2
  have hne : ∀ a b (ha : a < P.verts.length) (hb : b < P.verts.length), a ≠ b →
      P.verts[a]'ha ≠ P.verts[b]'hb := fun a b ha hb hab h => by
    have := (List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) h
    simp only [Fin.mk.injEq] at this; exact hab this
  rcases h1 with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩ <;> rcases h2 with ⟨ha2, hb2⟩ | ⟨ha2, hb2⟩
  · exact hne i j (by omega) (by omega) (by omega) (ha1.symm.trans ha2)
  · exact hne i (j + 1) (by omega) (by omega) (by omega) (ha1.symm.trans hb2)
  · exact hne i (j + 1) (by omega) (by omega) (by omega) (ha1.symm.trans hb2)
  · exact hne i j (by omega) (by omega) (by omega) (ha1.symm.trans ha2)

lemma t2_walk_edges_nodup_of_verts_nodup {G : Graph} {u v : ℕ} {P : Walk}
    (hW : P.IsWalk G u v) (hnd : P.verts.Nodup) :
    P.edges.Nodup := by
  rcases hW.2.2 with ⟨_, hPe, _⟩ | ⟨_, hlen, _, _, _, hstep⟩
  · rw [hPe]; exact List.nodup_nil
  · rw [List.nodup_iff_injective_getElem]
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact absurd heq (walk_edge_ne_of_lt hnd hlen hstep hi hj hlt)
    · rfl
    · exact absurd heq.symm (walk_edge_ne_of_lt hnd hlen hstep hj hi hgt)

lemma t2_walkAt_add_le {mem : ℕ → ℕ} {h0 h1 : ℕ} {G : Graph} {u v : ℕ} {P : Walk}
    (hW : P.IsWalk G u v) (hnd : P.verts.Nodup) (hwk : WalkAt mem h0 P) (hz : ZeroFrom mem h1)
    (hle : h0 ≤ h1) :
    P.verts.length ≤ P.edges.length + 1 ∧
    h0 + 1 + P.verts.length ≤ h1 + 1 ∧
    (P.verts.length ≥ 1 → h0 + 1 + P.verts.length < h1 ∧
      (∀ j < P.verts.length, h0 + 1 + j < h1)) ∧
    (P.edges.length ≥ 1 → h0 + 1 + P.verts.length < h1 ∧
      ∀ j < P.edges.length, h0 + 2 + P.verts.length + j ≤ h1) := by
  rcases hW.2.2 with ⟨hv0, he0, _⟩ | ⟨hne, hlen, _, _, _, _⟩
  · have hvl : P.verts.length = 0 := by rw [hv0]; rfl
    have hel : P.edges.length = 0 := by rw [he0]; rfl
    exact ⟨by omega, by omega, fun h => by omega, fun h => by omega⟩
  · have he_pos : 1 ≤ P.edges.length := Nat.pos_of_ne_zero (by simpa [List.length_eq_zero_iff] using hne)
    have hlen_lt : h0 + 1 + P.verts.length < h1 := by
      have hm : mem (h0 + 1 + P.verts.length) ≠ 0 := by rw [hwk.edges_len]; omega
      by_contra hge; exact hm (hz _ (by omega))
    have hv_lt : ∀ j < P.verts.length, h0 + 1 + j < h1 := fun j hj => by omega
    have he_nd := t2_walk_edges_nodup_of_verts_nodup hW hnd
    have he_seq : SeqAt mem (h0 + 1 + P.verts.length) P.edges :=
      ⟨hwk.edges_len, fun j hj => by
        simpa only [Nat.add_assoc, show 1 + (P.verts.length + (1 + j)) = 2 + P.verts.length + j by omega]
          using hwk.edges_listAt j hj⟩
    have he_le : ∀ j < P.edges.length, h0 + 2 + P.verts.length + j ≤ h1 := fun j hj => by
      have ha := drain_seqAt_nodup_add_le he_nd he_seq hz (by omega) hj
      omega
    exact ⟨by omega, by omega, fun _ => ⟨hlen_lt, hv_lt⟩, fun _ => ⟨hlen_lt, he_le⟩⟩

/-! ## Lifting, `EmbInv`, congestion update, and word-width bounds for `t2MiddleEdge` -/

lemma t2_unembedded_erase_card {wd : WitnessData} {emb : ℕ → Option Walk} {eW : ℕ}
    {P : Walk} (heW : eW < wd.W.m) (hnone : emb eW = none) :
    unembeddedSetPure wd (Function.update emb eW (some P)) =
      (unembeddedSetPure wd emb).erase eW ∧
    eW ∈ unembeddedSetPure wd emb ∧
    (unembeddedSetPure wd (Function.update emb eW (some P))).card + 1 =
      (unembeddedSetPure wd emb).card := by
  have hmem : eW ∈ unembeddedSetPure wd emb := by
    simp [unembeddedSetPure, heW, hnone]
  have heq : unembeddedSetPure wd (Function.update emb eW (some P)) =
      (unembeddedSetPure wd emb).erase eW := by
    ext j
    simp only [unembeddedSetPure, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    by_cases hj : j = eW
    · subst hj; simp
    · simp [hj]
  refine ⟨heq, hmem, ?_⟩
  rw [heq, Finset.card_erase_add_one hmem]

lemma t2_liftJSubWalk_spec {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) {stc : T2StaticData ctx} {g₀ : T2Ghost impl.pathDS} {mem : ℕ → ℕ}
    (hS : T2StepInv ctx stc g₀ mem)
    {ci eL eW u_loc v_loc : ℕ} {P_sub : Walk}
    (hci : ci < ctx.wd.comps.length) (heL : eL < ctx.wd.comps[ci].W_sub.m)
    (heW_eq : eW = ctx.wd.comps[ci].wStart + eL) (hnone : g₀.emb eW = none)
    (hWe_edge : ctx.wd.W.edges.getD eW (0, 0) =
      (ctx.wd.comps[ci].verts.getD u_loc 0, ctx.wd.comps[ci].verts.getD v_loc 0))
    (hPsub : P_sub.IsWalk ctx.wd.comps[ci].J_sub u_loc v_loc)
    (hPsub_len : (P_sub.edges.length : ℝ) ≤
      impl.pathDS.params.γ_ExpPath ((ctx.wInp.prep.phiNum_dec : ℝ) / ctx.wInp.prep.phiDen_dec)
        ctx.wd.J0_strip.m)
    (hPsub_undel : ∀ b ∈ P_sub.edges, b ∉ (g₀.states ci).deleted) :
    let c := ctx.wd.comps[ci]
    let P_J := liftJSubWalk c P_sub
    let emb' := Function.update g₀.emb eW (some P_J)
    eW < ctx.wd.W.m ∧
    P_J.verts.length = P_sub.verts.length ∧
    P_J.edges.length = P_sub.edges.length ∧
    P_J.encode.length ≤ 2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5 ∧
    (P_J.edges.length : ℝ) ≤ ctx.wd.γ_ExpPath ∧
    P_J.IsWalk inp.J (ctx.wd.W.edges.getD eW (0, 0)).1 (ctx.wd.W.edges.getD eW (0, 0)).2 ∧
    (∀ y ∈ P_sub.verts, y < c.J_sub.n ∧ c.verts.getD y 0 < inp.J.n) ∧
    (∀ b ∈ P_sub.edges, b < c.J_sub.m ∧ c.jSubOrigEdges.getD b 0 < inp.J.m) ∧
    (∀ eJ ∈ P_J.edges, eJ < inp.J.m ∧
      (∀ x ∈ (inp.embJH eJ).verts, x < inp.H'.n) ∧
      (inp.embJH eJ).verts.length ≤ length inp.J inp.embJH + 1) ∧
    (∀ x, x ∈ (compose inp.J inp.embJH (partialToWalk emb') eW).verts ↔
      ∃ eJ ∈ P_J.edges, x ∈ (inp.embJH eJ).verts) ∧
    (∀ x ∈ g₀.procVerts, g₀.drained = g₀.procVerts →
      x ∉ (compose inp.J inp.embJH (partialToWalk emb') eW).verts ∧
      ∀ eJ ∈ P_J.edges, x ∉ (inp.embJH eJ).verts) ∧
    IsPartialEmbedding ctx.wd.W inp.J emb' ∧
    (∀ e' < ctx.wd.W.m, ((partialToWalk emb' e').edges.length : ℝ) ≤ ctx.wd.γ_ExpPath) := by
  intro c P_J emb'
  have hm := mkW_W_edges_comp ctx.hws hci heL
  have heW_m : eW < ctx.wd.W.m := heW_eq ▸ hm.1
  have hds := ctx.ds_bounds.2.2.2.2.2.2.2.2.2
  have hlen_e : P_sub.edges.length ≤ ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params := by
    exact_mod_cast le_trans hPsub_len hds
  have hP_verts_le : P_sub.verts.length ≤ P_sub.edges.length + 1 := by
    rcases hPsub.2.2 with ⟨hv0, he0, _⟩ | ⟨_, hlen, _⟩
    · rw [hv0, he0]; simp
    · omega
  have henc : P_J.encode.length ≤ 2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5 := by
    rw [walk_encode_length]
    simp only [P_J, liftJSubWalk, List.length_map]
    omega
  have hγ_le : (P_J.edges.length : ℝ) ≤ ctx.wd.γ_ExpPath := by
    simp only [P_J, liftJSubWalk, List.length_map]
    have hds_le : impl.pathDS.params.γ_ExpPath ctx.wd.φ_dec ctx.wd.J0_strip.m ≤ ctx.wd.γ_ExpPath := by
      refine le_trans (impl.pathDS.params.hγ_ExpPath_mono (roundPhi_pos ctx.hw_okW.φ_dec_pos)
        (roundPhi_le ctx.hw_okW.φ_dec_pos) ctx.hw_okW.φ_dec_le le_rfl) ?_
      dsimp only [T2Ctx.wd, WitnessCoreInput.mkWitnessData]
      exact le_max_left _ _
    exact le_trans hPsub_len hds_le
  have hwalk_J : P_J.IsWalk inp.J (ctx.wd.W.edges.getD eW (0, 0)).1 (ctx.wd.W.edges.getD eW (0, 0)).2 := by
    rw [hWe_edge, ← ctx.hWInpJ]
    exact mkW_isWalk_liftJSubWalk ctx.hstat ctx.hw_okW ctx.hws hci hPsub
  have hprops := ctx.hw_okW.comp_props ci hci
  rcases hprops with ⟨_, _, hXJ_c, _, hverts_c, hc_Jn, hc_Jvalid, _, _, _, _, _, _, _, _, _, _, _, _, hjOrig_c⟩
  have hc_vlen : c.verts.length = c.J_sub.n := by rw [hverts_c, vertsOf, Finset.length_sort, ← hc_Jn]
  have hy_sub : ∀ y ∈ P_sub.verts, y < c.J_sub.n ∧ c.verts.getD y 0 < inp.J.n := fun y hy => by
    have hy_lt : y < c.J_sub.n := by
      rcases hPsub.2.2 with ⟨hv0, _, _⟩ | ⟨hne, hlen, _, _, hedges_m, hstep⟩
      · rw [hv0] at hy; simp at hy
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
        have he_pos : 0 < P_sub.edges.length := Nat.pos_of_ne_zero (by simpa [List.length_eq_zero_iff] using hne)
        have hstep_pt : ∀ idx (hidx : idx < P_sub.edges.length),
            (P_sub.verts.getD idx 0 < c.J_sub.n ∧ P_sub.verts.getD (idx + 1) 0 < c.J_sub.n) := fun idx hidx => by
          have hb_m : P_sub.edges.getD idx 0 < c.J_sub.m := by
            rw [List.getD_eq_getElem _ _ hidx]; exact hedges_m _ (List.getElem_mem hidx)
          have hcedge := hc_Jvalid (c.J_sub.edges.getD (P_sub.edges.getD idx 0) (0, 0))
            (by rw [List.getD_eq_getElem _ _ (by simpa [Graph.m] using hb_m)]; exact List.getElem_mem _)
          rcases hstep idx hidx with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [← h1, ← h2]; exact hcedge
          · rw [← h1, ← h2]; exact ⟨hcedge.2, hcedge.1⟩
        by_cases hk_e : k < P_sub.edges.length
        · have hp := (hstep_pt k hk_e).1
          rwa [List.getD_eq_getElem _ _ hk] at hp
        · have hk_eq : k = P_sub.edges.length := by omega
          have hp := (hstep_pt (P_sub.edges.length - 1) (by omega)).2
          rw [show (P_sub.edges.length - 1) + 1 = k by omega, List.getD_eq_getElem _ _ hk] at hp
          exact hp
    have hy_mem : c.verts.getD y 0 ∈ c.X := by
      have hy_card : y < c.X.card := hc_Jn ▸ hy_lt
      rw [hverts_c]; exact getD_vertsOf_mem hy_card
    exact ⟨hy_lt, Finset.mem_range.mp (ctx.hWInpJ ▸ hXJ_c hy_mem)⟩
  have hb_sub : ∀ b ∈ P_sub.edges, b < c.J_sub.m ∧ c.jSubOrigEdges.getD b 0 < inp.J.m := fun b hb => by
    have hb_m : b < c.J_sub.m := by
      rcases hPsub.2.2 with ⟨_, he0, _⟩ | ⟨_, _, _, _, hedges_m, _⟩
      · rw [he0] at hb; simp at hb
      · exact hedges_m b hb
    exact ⟨hb_m, ctx.hWInpJ ▸ (mkW_comp_jOrig_edge ctx.hstat ctx.hw_okW ctx.hws hci b hb_m).1⟩
  have heJ_sub : ∀ eJ ∈ P_J.edges, eJ < inp.J.m ∧
      (∀ x ∈ (inp.embJH eJ).verts, x < inp.H'.n) ∧
      (inp.embJH eJ).verts.length ≤ length inp.J inp.embJH + 1 := fun eJ heJ => by
    simp only [P_J, liftJSubWalk, List.mem_map] at heJ
    rcases heJ with ⟨b, hb, rfl⟩
    have he_m := (hb_sub b hb).2
    have hwk := ctx.hembJH.2 (c.jSubOrigEdges.getD b 0) he_m
    have hv_lt : ∀ x ∈ (inp.embJH (c.jSubOrigEdges.getD b 0)).verts, x < inp.H'.n := fun x hx => by
      rcases hwk.2.2 with ⟨hv0, _, _⟩ | ⟨hne, hlen, _, _, hedges_m, hstep⟩
      · rw [hv0] at hx; simp at hx
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
        have he_pos : 0 < (inp.embJH (c.jSubOrigEdges.getD b 0)).edges.length :=
          Nat.pos_of_ne_zero (by simpa [List.length_eq_zero_iff] using hne)
        have hstep_pt : ∀ idx (hidx : idx < (inp.embJH (c.jSubOrigEdges.getD b 0)).edges.length),
            ((inp.embJH (c.jSubOrigEdges.getD b 0)).verts.getD idx 0 < inp.H'.n ∧
             (inp.embJH (c.jSubOrigEdges.getD b 0)).verts.getD (idx + 1) 0 < inp.H'.n) := fun idx hidx => by
          have hb_h : (inp.embJH (c.jSubOrigEdges.getD b 0)).edges.getD idx 0 < inp.H'.m := by
            rw [List.getD_eq_getElem _ _ hidx]; exact hedges_m _ (List.getElem_mem hidx)
          have hcedge := ctx.hH' (inp.H'.edges[(inp.embJH (c.jSubOrigEdges.getD b 0)).edges.getD idx 0]'(by
            simpa [Graph.m] using hb_h)) (List.getElem_mem _)
          rw [← List.getD_eq_getElem _ (0, 0) (by simpa [Graph.m] using hb_h)] at hcedge
          rcases hstep idx hidx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨by omega, by omega⟩
        by_cases hk_e : k < (inp.embJH (c.jSubOrigEdges.getD b 0)).edges.length
        · have hp := (hstep_pt k hk_e).1
          rwa [List.getD_eq_getElem _ _ hk] at hp
        · have hp := (hstep_pt ((inp.embJH (c.jSubOrigEdges.getD b 0)).edges.length - 1) (by omega)).2
          rw [show ((inp.embJH (c.jSubOrigEdges.getD b 0)).edges.length - 1) + 1 = k by omega,
            List.getD_eq_getElem _ _ hk] at hp
          exact hp
    have hlen_le : (inp.embJH (c.jSubOrigEdges.getD b 0)).verts.length ≤ length inp.J inp.embJH + 1 := by
      have hl : (inp.embJH (c.jSubOrigEdges.getD b 0)).edges.length ≤ length inp.J inp.embJH := by
        have hpos : 0 < inp.J.m := Nat.pos_of_ne_zero (by omega)
        unfold length
        refine Finset.le_sup (f := fun e => (inp.embJH e).edges.length) (Finset.mem_range.mpr he_m)
      rcases hwk.2.2 with ⟨hv0, _, _⟩ | ⟨_, hlen, _⟩
      · rw [hv0]; simp
      · omega
    exact ⟨he_m, hv_lt, hlen_le⟩
  have hcomp_iff : ∀ x, x ∈ (compose inp.J inp.embJH (partialToWalk emb') eW).verts ↔
      ∃ eJ ∈ P_J.edges, x ∈ (inp.embJH eJ).verts := fun x => by
    have hemb_ew : partialToWalk emb' eW = P_J := by simp [partialToWalk, emb']
    change x ∈ (composeAux inp.J inp.embJH (partialToWalk emb' eW).verts
      (partialToWalk emb' eW).edges).verts ↔ _
    rw [hemb_ew]
    rcases hwalk_J with ⟨_, hvJ, ⟨hPv, hPe, _⟩ | ⟨_, hlenL, hheadL, hlastL, _, hstepL⟩⟩
    · rw [hPv, hPe]; simp [composeAux, Walk.empty]
    · have hedges_nl : ∀ e' ∈ P_J.edges,
          e' < inp.J.m ∧ (inp.J.edges.getD e' (0, 0)).1 ≠ (inp.J.edges.getD e' (0, 0)).2 := fun e' he' => by
        simp only [P_J, liftJSubWalk, List.mem_map] at he'
        rcases he' with ⟨b, hb, rfl⟩
        have hb_m := (hb_sub b hb).1
        have hb_orig : b < c.jSubOrigEdges.length := by rw [hjOrig_c.1]; exact hb_m
        exact ctx.hWInpJ ▸ mkW_comp_jOrig_nonloop ctx.hstat ctx.hws hci hb_orig
      exact compose_nonloop_mem_verts_iff ctx.hembJH P_J.verts P_J.edges hlenL hedges_nl hstepL
        hheadL hlastL hvJ x
  have hproc_nmem : ∀ x ∈ g₀.procVerts, g₀.drained = g₀.procVerts →
      x ∉ (compose inp.J inp.embJH (partialToWalk emb') eW).verts ∧
      ∀ eJ ∈ P_J.edges, x ∉ (inp.embJH eJ).verts := fun x hx hDr => by
    have hx_H : x < inp.H'.n := (hS.hProcSub x hx).1
    have h2 : ∀ eJ ∈ P_J.edges, x ∉ (inp.embJH eJ).verts := fun eJ heJ hx_in => by
      simp only [P_J, liftJSubWalk, List.mem_map] at heJ
      rcases heJ with ⟨b, hb, rfl⟩
      have hb_m := (hb_sub b hb).1
      exact absurd (hS.hDr_del x (hDr ▸ hx) hx_H ci hci b hb_m hx_in) (hPsub_undel b hb)
    exact ⟨fun hm => let ⟨eJ, heJ, hx_in⟩ := (hcomp_iff x).mp hm; h2 eJ heJ hx_in, h2⟩
  have hpart : IsPartialEmbedding ctx.wd.W inp.J emb' :=
    ⟨hS.hPart.1, fun e' he' P hP => by
      by_cases heq : e' = eW
      · subst heq
        simp only [emb', Function.update_self, Option.some.injEq] at hP
        subst hP
        rw [← List.getD_eq_getElem ctx.wd.W.edges (0, 0) he']; exact hwalk_J
      · simp only [emb', Function.update_of_ne heq] at hP
        exact hS.hPart.2 e' he' P hP⟩
  have helen : ∀ e' < ctx.wd.W.m, ((partialToWalk emb' e').edges.length : ℝ) ≤ ctx.wd.γ_ExpPath := fun e' he' => by
    by_cases heq : e' = eW
    · subst heq; simpa [partialToWalk, emb'] using hγ_le
    · simp only [partialToWalk, emb', Function.update_of_ne heq]; exact hS.hELen e' he'
  refine ⟨heW_m, by simp [P_J, liftJSubWalk], by simp [P_J, liftJSubWalk], henc, hγ_le, hwalk_J,
    hy_sub, hb_sub, heJ_sub, hcomp_iff, hproc_nmem, hpart, helen⟩

lemma t2_vcongAt_update_none {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) {emb : ℕ → Option Walk} {eW : ℕ} {P_J : Walk}
    (heW : eW < ctx.wd.W.m) (hnone : emb eW = none) (x : ℕ) :
    let emb' := Function.update emb eW (some P_J)
    vcongAt ctx.wd.W ctx.wd.wW (compose inp.J inp.embJH (partialToWalk emb')) x =
      vcongAt ctx.wd.W ctx.wd.wW (compose inp.J inp.embJH (partialToWalk emb)) x +
        if x ∈ (compose inp.J inp.embJH (partialToWalk emb') eW).verts then
          ctx.wd.wW eW
        else 0 := by
  intro emb'
  have hmem : eW ∈ Finset.range ctx.wd.W.m := Finset.mem_range.mpr heW
  unfold vcongAt
  rw [Finset.sum_filter, Finset.sum_filter,
      ← Finset.add_sum_erase (Finset.range ctx.wd.W.m) _ hmem,
      ← Finset.add_sum_erase (Finset.range ctx.wd.W.m) _ hmem]
  have hrest : ∑ e ∈ (Finset.range ctx.wd.W.m).erase eW,
        (if x ∈ (compose inp.J inp.embJH (partialToWalk emb') e).verts then ctx.wd.wW e else 0) =
      ∑ e ∈ (Finset.range ctx.wd.W.m).erase eW,
        (if x ∈ (compose inp.J inp.embJH (partialToWalk emb) e).verts then ctx.wd.wW e else 0) :=
    Finset.sum_congr rfl fun e he => by
      have hne : e ≠ eW := Finset.ne_of_mem_erase he
      have hpe : partialToWalk emb' e = partialToWalk emb e := by
        simp [partialToWalk, emb', Function.update_of_ne hne]
      rw [compose, hpe]; rfl
  have hold : (if x ∈ (compose inp.J inp.embJH (partialToWalk emb) eW).verts then ctx.wd.wW eW else 0) = 0 := by
    have hcomp : compose inp.J inp.embJH (partialToWalk emb) eW = Walk.empty := by
      simp [compose, partialToWalk, hnone, composeAux, Walk.empty]
    simp [hcomp, Walk.empty]
  rw [hrest, hold, zero_add, add_comm]

lemma t2_vcongNumPure_update_none {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) {wWNum : ℕ → ℕ} {emb : ℕ → Option Walk} {eW : ℕ} {P_J : Walk}
    (heW : eW < ctx.wd.W.m) (hnone : emb eW = none) (x : ℕ) :
    let emb' := Function.update emb eW (some P_J)
    vcongNumPure ctx.wd inp.J inp.embJH wWNum emb' x =
      vcongNumPure ctx.wd inp.J inp.embJH wWNum emb x +
        if x ∈ (compose inp.J inp.embJH (partialToWalk emb') eW).verts then
          wWNum eW
        else 0 := by
  intro emb'
  have hmem : eW ∈ Finset.range ctx.wd.W.m := Finset.mem_range.mpr heW
  unfold vcongNumPure
  rw [← Finset.add_sum_erase (Finset.range ctx.wd.W.m) _ hmem,
      ← Finset.add_sum_erase (Finset.range ctx.wd.W.m) _ hmem]
  have hrest : ∑ e ∈ (Finset.range ctx.wd.W.m).erase eW,
        (if x ∈ (compose inp.J inp.embJH (partialToWalk emb') e).verts then wWNum e else 0) =
      ∑ e ∈ (Finset.range ctx.wd.W.m).erase eW,
        (if x ∈ (compose inp.J inp.embJH (partialToWalk emb) e).verts then wWNum e else 0) :=
    Finset.sum_congr rfl fun e he => by
      have hne : e ≠ eW := Finset.ne_of_mem_erase he
      have hpe : partialToWalk emb' e = partialToWalk emb e := by
        simp [partialToWalk, emb', Function.update_of_ne hne]
      rw [compose, hpe]; rfl
  have hold : (if x ∈ (compose inp.J inp.embJH (partialToWalk emb) eW).verts then wWNum eW else 0) = 0 := by
    have hcomp : compose inp.J inp.embJH (partialToWalk emb) eW = Walk.empty := by
      simp [compose, partialToWalk, hnone, composeAux, Walk.empty]
    simp [hcomp, Walk.empty]
  rw [hrest, hold, zero_add, add_comm]

end MinCostFlow.Spanner
