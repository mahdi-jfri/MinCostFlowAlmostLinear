module

public import MinCostFlow.Spanner.ProgTask2InitJ0Bridge
public import MinCostFlow.Spanner.ProgTask2DSOps

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Helpers and loop invariant for `t2DrainQueue` -/

lemma drain_seqAt_nodup_add_le {mem : ℕ → ℕ} {h0 h1 : ℕ} {L : List ℕ}
    (hnd : L.Nodup) (hseq : WordRAM.SeqAt mem h0 L) (hz : WordRAM.ZeroFrom mem h1)
    (hle : h0 ≤ h1) {j : ℕ} (hj : j < L.length) :
    h0 + 1 + j ≤ h1 := by
  by_cases hnz : L[j] ≠ 0
  · have hm : mem (h0 + 1 + j) ≠ 0 := by rw [hseq.2 j hj]; exact hnz
    by_contra hgt; exact hm (hz _ (by omega))
  · push Not at hnz
    by_cases hj1 : j + 1 < L.length
    · have hneq : L[j + 1] ≠ L[j] := fun heq => by
        have hinj := List.nodup_iff_injective_getElem.mp hnd
          (a₁ := ⟨j + 1, hj1⟩) (a₂ := ⟨j, hj⟩) heq
        simp only [Fin.mk.injEq] at hinj; omega
      have hm : mem (h0 + 1 + (j + 1)) ≠ 0 := by rw [hseq.2 (j + 1) hj1, ← hnz] at *; exact hneq
      by_contra hgt; exact hm (hz _ (by omega))
    · by_cases hj0 : j = 0
      · subst hj0
        have hm : mem h0 ≠ 0 := by rw [hseq.1]; omega
        by_contra hgt; exact hm (hz h0 (by omega))
      · have hj_prev : j - 1 < L.length := by omega
        have hneq : L[j - 1] ≠ L[j] := fun heq => by
          have hinj := List.nodup_iff_injective_getElem.mp hnd
            (a₁ := ⟨j - 1, hj_prev⟩) (a₂ := ⟨j, hj⟩) heq
          simp only [Fin.mk.injEq] at hinj; omega
        have hm : mem (h0 + 1 + (j - 1)) ≠ 0 := by rw [hseq.2 (j - 1) hj_prev]; omega
        by_contra hgt; exact hm (hz _ (by omega))

lemma drain_del_family_card_le_J {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) (D : ℕ → Finset ℕ)
    (hD : ∀ ci (hci : ci < ctx.wd.comps.length) b, b ∈ D ci →
      b < (ctx.wd.comps[ci]'hci).J_sub.m) :
    ∑ ci ∈ Finset.range ctx.wd.comps.length, (D ci).card ≤ inp.J.m := by
  let delImg : ℕ → Finset ℕ := fun ci =>
    ((Finset.range (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m).filter (· ∈ D ci)).image
      (fun b => (ctx.wd.comps.getD ci defaultCompInfo).jSubOrigEdges.getD b 0)
  have hcard_eq : ∀ ci (hci : ci < ctx.wd.comps.length), (D ci).card = (delImg ci).card := fun ci hci => by
    have hget : ctx.wd.comps.getD ci defaultCompInfo = ctx.wd.comps[ci]'hci :=
      List.getD_eq_getElem _ _ hci
    have hf : D ci = (Finset.range (ctx.wd.comps[ci]'hci).J_sub.m).filter (· ∈ D ci) := by
      ext b; simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun hb => ⟨hD ci hci b hb, hb⟩, fun hb => hb.2⟩
    rw [hf]; dsimp only [delImg]; rw [hget]; symm
    refine Finset.card_image_of_injOn fun a ha b hb hab => ?_
    have ha_m := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hb_m := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have hpr := (ctx.hw_okW.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rw [List.getD_eq_getElem _ _ (by rw [hpr.1]; exact ha_m),
        List.getD_eq_getElem _ _ (by rw [hpr.1]; exact hb_m)] at hab
    exact congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hpr.2.1)
      (a₁ := ⟨a, by rw [hpr.1]; exact ha_m⟩) (a₂ := ⟨b, by rw [hpr.1]; exact hb_m⟩) hab)
  have hsum_eq : ∑ ci ∈ Finset.range ctx.wd.comps.length, (D ci).card =
      ((Finset.range ctx.wd.comps.length).biUnion fun ci =>
        if ci < ctx.wd.comps.length then delImg ci else ∅).card := by
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun ci hci => ?_
      have hci' := Finset.mem_range.mp hci
      simp only [hci', ↓reduceIte, hcard_eq ci hci']
    · intro c1 h1 c2 h2 hne
      change Disjoint _ _
      have h1' := Finset.mem_range.mp h1; have h2' := Finset.mem_range.mp h2
      simp only [h1', h2', ↓reduceIte, Finset.disjoint_left]
      intro j hj1 hj2
      rcases Finset.mem_image.mp hj1 with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hj2 with ⟨b, hb, hab⟩
      rw [List.getD_eq_getElem _ _ h1'] at ha hab
      rw [List.getD_eq_getElem _ _ h2'] at hb hab
      have ha_m := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
      have hb_m := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      have h1m : ctx.wd.comps[c1].jSubOrigEdges.getD a 0 ∈ ctx.wd.comps[c1].jSubOrigEdges.toFinset := by
        rw [List.mem_toFinset, List.getD_eq_getElem _ _ (by
          rw [(ctx.hw_okW.comp_props c1 h1').2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact ha_m)]
        exact List.getElem_mem _
      have h2m : ctx.wd.comps[c2].jSubOrigEdges.getD b 0 ∈ ctx.wd.comps[c2].jSubOrigEdges.toFinset := by
        rw [List.mem_toFinset, List.getD_eq_getElem _ _ (by
          rw [(ctx.hw_okW.comp_props c2 h2').2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hb_m)]
        exact List.getElem_mem _
      rw [← hab] at h1m
      exact Finset.disjoint_left.mp (ctx.hw_okW.comp_disjoint c1 c2 h1' h2' hne) h1m h2m
  have hsub_J : ((Finset.range ctx.wd.comps.length).biUnion fun ci =>
      if ci < ctx.wd.comps.length then delImg ci else ∅) ⊆ Finset.range inp.J.m := by
    intro j hj
    rcases Finset.mem_biUnion.mp hj with ⟨ci, hci_r, hjci⟩
    have hci := Finset.mem_range.mp hci_r
    simp only [hci, ↓reduceIte] at hjci
    rcases Finset.mem_image.mp hjci with ⟨b, hb, rfl⟩
    dsimp only [delImg] at *; rw [List.getD_eq_getElem _ _ hci] at hb ⊢
    have hb_m := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have hp := (ctx.hw_okW.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rw [Finset.mem_range, ← ctx.hWInpJ, List.getD_eq_getElem _ _ (by omega)]
    exact hp.2.2.1 _ (List.getElem_mem _)
  rw [hsum_eq]
  exact (Finset.card_le_card hsub_J).trans_eq (Finset.card_range inp.J.m)

lemma drain_undelRem_step {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) (states : ℕ → PathDSAbsState)
    {ci b : ℕ} (hci : ci < ctx.wd.comps.length) (hb_m : b < ctx.wd.comps[ci].J_sub.m)
    (hb_ndel : b ∉ (states ci).deleted) (s' : PathDSAbsState)
    (hs'_del : s'.deleted = insert b (states ci).deleted)
    (hsub : ∀ k (hk : k < ctx.wd.comps.length),
      (states k).deleted ⊆ Finset.range (ctx.wd.comps[k]'hk).J_sub.m) :
    let undel := fun stFn : ℕ → PathDSAbsState => ∑ k ∈ Finset.range ctx.wd.comps.length,
      ((ctx.wd.comps.getD k defaultCompInfo).J_sub.m -
        ((Finset.range (ctx.wd.comps.getD k defaultCompInfo).J_sub.m).filter
          (· ∈ (stFn k).deleted)).card)
    undel states = undel (Function.update states ci s') + 1 := by
  intro undel
  have hmem : ci ∈ Finset.range ctx.wd.comps.length := Finset.mem_range.mpr hci
  dsimp only [undel]
  rw [← Finset.add_sum_erase (Finset.range ctx.wd.comps.length) _ hmem,
      ← Finset.add_sum_erase (Finset.range ctx.wd.comps.length) _ hmem]
  have hrest : ∑ k ∈ (Finset.range ctx.wd.comps.length).erase ci,
      ((ctx.wd.comps.getD k defaultCompInfo).J_sub.m -
        ((Finset.range (ctx.wd.comps.getD k defaultCompInfo).J_sub.m).filter
          (· ∈ (Function.update states ci s' k).deleted)).card) =
      ∑ k ∈ (Finset.range ctx.wd.comps.length).erase ci,
      ((ctx.wd.comps.getD k defaultCompInfo).J_sub.m -
        ((Finset.range (ctx.wd.comps.getD k defaultCompInfo).J_sub.m).filter
          (· ∈ (states k).deleted)).card) :=
    Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [hrest, Function.update_self, List.getD_eq_getElem _ _ hci, hs'_del]
  have hflt1 : (Finset.range ctx.wd.comps[ci].J_sub.m).filter (· ∈ (states ci).deleted) =
      (states ci).deleted := by
    ext z; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun hz => hz.2, fun hz => ⟨Finset.mem_range.mp (hsub ci hci hz), hz⟩⟩
  have hflt2 : (Finset.range ctx.wd.comps[ci].J_sub.m).filter (· ∈ insert b (states ci).deleted) =
      insert b (states ci).deleted := by
    ext z; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    exact ⟨fun hz => hz.2, fun hz => ⟨hz.elim (fun h => h ▸ hb_m) (fun h => Finset.mem_range.mp (hsub ci hci h)), hz⟩⟩
  have hcard_le : (states ci).deleted.card + 1 ≤ ctx.wd.comps[ci].J_sub.m := by
    have hcard_ins : (insert b (states ci).deleted).card ≤ (Finset.range ctx.wd.comps[ci].J_sub.m).card :=
      Finset.card_le_card fun z hz => (Finset.mem_insert.mp hz).elim
        (fun h => Finset.mem_range.mpr (h ▸ hb_m)) (fun h => hsub ci hci h)
    rw [Finset.card_insert_of_notMem hb_ndel, Finset.card_range] at hcard_ins
    exact hcard_ins
  rw [hflt1, hflt2, Finset.card_insert_of_notMem hb_ndel]; omega

lemma drain_vhatRem_step {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) (states : ℕ → PathDSAbsState)
    {ci : ℕ} (hci : ci < ctx.wd.comps.length) (s' : PathDSAbsState) {L : List ℕ}
    (hsub0 : (states ci).Vhat ⊆ Finset.range (ctx.wd.comps[ci]'hci).J_sub.n)
    (hsub1 : s'.Vhat ⊆ Finset.range (ctx.wd.comps[ci]'hci).J_sub.n)
    (hmono : (states ci).Vhat ⊆ s'.Vhat)
    (hnd : L.Nodup) (hL : L.toFinset = s'.Vhat \ (states ci).Vhat) :
    let vh := fun stFn : ℕ → PathDSAbsState => ∑ k ∈ Finset.range ctx.wd.comps.length,
      ((ctx.wd.comps.getD k defaultCompInfo).J_sub.n -
        ((Finset.range (ctx.wd.comps.getD k defaultCompInfo).J_sub.n).filter
          (· ∈ (stFn k).Vhat)).card)
    vh states = vh (Function.update states ci s') + L.length := by
  intro vh
  have hmem : ci ∈ Finset.range ctx.wd.comps.length := Finset.mem_range.mpr hci
  dsimp only [vh]
  rw [← Finset.add_sum_erase (Finset.range ctx.wd.comps.length) _ hmem,
      ← Finset.add_sum_erase (Finset.range ctx.wd.comps.length) _ hmem]
  have hrest : ∑ k ∈ (Finset.range ctx.wd.comps.length).erase ci,
      ((ctx.wd.comps.getD k defaultCompInfo).J_sub.n -
        ((Finset.range (ctx.wd.comps.getD k defaultCompInfo).J_sub.n).filter
          (· ∈ (Function.update states ci s' k).Vhat)).card) =
      ∑ k ∈ (Finset.range ctx.wd.comps.length).erase ci,
      ((ctx.wd.comps.getD k defaultCompInfo).J_sub.n -
        ((Finset.range (ctx.wd.comps.getD k defaultCompInfo).J_sub.n).filter
          (· ∈ (states k).Vhat)).card) :=
    Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [hrest, Function.update_self, List.getD_eq_getElem _ _ hci]
  have hf0 : (Finset.range ctx.wd.comps[ci].J_sub.n).filter (· ∈ (states ci).Vhat) = (states ci).Vhat := by
    ext z; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun hz => hz.2, fun hz => ⟨Finset.mem_range.mp (hsub0 hz), hz⟩⟩
  have hf1 : (Finset.range ctx.wd.comps[ci].J_sub.n).filter (· ∈ s'.Vhat) = s'.Vhat := by
    ext z; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun hz => hz.2, fun hz => ⟨Finset.mem_range.mp (hsub1 hz), hz⟩⟩
  have hcard1 : s'.Vhat.card ≤ ctx.wd.comps[ci].J_sub.n := by
    simpa [Finset.card_range] using Finset.card_le_card hsub1
  have hsdiff := Finset.card_sdiff_add_card_eq_card hmono
  have hLlen : L.length = (s'.Vhat \ (states ci).Vhat).card := by
    rw [← hL, List.toFinset_card_of_nodup hnd]
  rw [hf0, hf1, hLlen]; omega

lemma drain_nodeRem_split {nH : ℕ} (L_inc : ℕ → List (ℕ × ℕ)) (drained0 : Finset ℕ)
    (queue : List ℕ) (hnd : queue.Nodup)
    (hsub : ∀ x ∈ queue, x < nH ∧ x ∉ drained0)
    {i : ℕ} (hi : i < queue.length) :
    let drainedAt := fun k => drained0 ∪ (queue.take k).toFinset
    let nodeRem := fun dr => ∑ y ∈ (Finset.range nH).filter (· ∉ dr), (L_inc y).length
    nodeRem (drainedAt i) = (L_inc (queue[i]'hi)).length + nodeRem (drainedAt (i + 1)) := by
  intro drainedAt nodeRem
  set x := queue[i]'hi
  have hx_mem : x ∈ queue := List.getElem_mem hi
  have hx_lt : x < nH := (hsub x hx_mem).1
  have hx_ndr0 : x ∉ drained0 := (hsub x hx_mem).2
  have hx_ntake : x ∉ queue.take i := by
    intro hmem
    obtain ⟨j, hj_len, hj_eq⟩ := List.getElem_of_mem hmem
    have hj_lt : j < i := by have := hj_len; simp at this; omega
    have hget : (queue.take i)[j]'hj_len = queue[j]'(by omega) := List.getElem_take
    rw [hget] at hj_eq
    have hinj := List.nodup_iff_injective_getElem.mp hnd (a₁ := ⟨j, by omega⟩) (a₂ := ⟨i, hi⟩) hj_eq
    simp only [Fin.mk.injEq] at hinj; omega
  have htake_succ : queue.take (i + 1) = queue.take i ++ [x] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
  have hS1 : (Finset.range nH).filter (· ∉ drainedAt i) =
      insert x ((Finset.range nH).filter (· ∉ drainedAt (i + 1))) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, drainedAt, htake_succ,
      List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_union, Finset.mem_singleton, List.mem_toFinset]
    constructor
    · rintro ⟨hy, hny⟩
      by_cases hyx : y = x
      · exact Or.inl hyx
      · refine Or.inr ⟨hy, ?_⟩
        rintro (h1 | h2 | h3)
        · exact hny (Or.inl h1)
        · exact hny (Or.inr h2)
        · exact hyx h3
    · rintro (rfl | ⟨hy, hny⟩)
      · exact ⟨hx_lt, fun h => h.elim hx_ndr0 hx_ntake⟩
      · exact ⟨hy, fun h => hny (h.elim Or.inl (fun h2 => Or.inr (Or.inl h2)))⟩
  have hnot : x ∉ (Finset.range nH).filter (· ∉ drainedAt (i + 1)) := by
    simp only [Finset.mem_filter, Finset.mem_range, drainedAt, htake_succ,
      List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_union, Finset.mem_singleton, not_and, not_not]
    intro _; simp
  dsimp only [nodeRem]
  rw [hS1, Finset.sum_insert hnot]

/-- Flat record of linear address and capacity inequalities for `t2DrainQueue`. -/
structure DrainBounds {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) : Prop where
  e_v1 : inp.v1 + 32 = inp.embWJAddr
  e_emb : inp.embWJAddr + ctx.wd.W.m = inp.dsHandlesAddr ctx.wd.W.m
  e_hdl : inp.dsHandlesAddr ctx.wd.W.m + ctx.wd.comps.length =
    inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length
  e_ceb : inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length + ctx.wd.comps.length =
    inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length
  e_vho : inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length + ctx.wd.comps.length =
    inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length
  e_del : inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + inp.J.m =
    inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length
  e_vh : inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + 2 * inp.J.m =
    inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length
  e_vhd : inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n =
    inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length
  e_vc : inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n =
    inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length
  e_ps : inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n =
    inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length
  e_ew : inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n =
    inp.queueAddr ctx.wd.W.m ctx.wd.comps.length
  e_q : inp.queueAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n =
    inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length
  h_nlo : inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length ≤ stc.nodesEnd
  h_nds : stc.nodesEnd ≤ stc.dsBaseAddr
  h_dsc : stc.dsBaseAddr ≤ Task2Input.staticEndCap impl inp
  h_stc : Task2Input.staticEndCap impl inp ≤ Task2Input.maxHeapEnd impl inp
  h_mhe : Task2Input.maxHeapEnd impl inp ≤ Task2Input.maxWordBound impl inp
  h_mwb : Task2Input.maxWordBound impl inp < 2 ^ w
  h_w1 : 1 < 2 ^ w
  h_jm : (ctx.wd.comps.map fun c => c.J_sub.m).sum ≤ inp.J.m
  h_jn : (ctx.wd.comps.map fun c => c.J_sub.n).sum ≤ 2 * inp.J.m

lemma drain_bounds {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) :
    DrainBounds ctx stc := by
  have h1 : (ctx.wd.comps.map fun c => c.J_sub.m).sum ≤ inp.J.m :=
    le_trans (Nat.le_add_left _ _) (ctx.hWInpJ ▸ mkW_sum_comp_j_m_le_J ctx.hstat ctx.hw_okW ctx.hws)
  have h6 : Task2Input.staticEndCap impl inp ≤ Task2Input.maxHeapEnd impl inp := by
    unfold Task2Input.maxHeapEnd; dsimp only; omega
  have h7 : Task2Input.maxHeapEnd impl inp ≤ Task2Input.maxWordBound impl inp := by
    unfold Task2Input.maxWordBound; exact le_trans (Nat.le_add_right _ 3) (le_max_left _ _)
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    stc.hNodes_lo, Nat.le_add_right _ _, stc.dsBaseAddr_le_cap, h6, h7,
    ctx.hww.2.2, ctx.hww.1, h1, ctx.hvhatSum_le⟩

/-- Machine invariant active during `t2DrainQueue` loops between `mem[v1+7]` update and `mem[v1+27] := 0`. -/
structure T2DrainInv {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) (g₀ : T2Ghost impl.pathDS)
    (memStart : ℕ → ℕ) (drained : Finset ℕ) (states : ℕ → PathDSAbsState)
    (reps : ℕ → impl.pathDS.R.τ) (hCur deleteCountJ : ℕ) (mem : ℕ → ℕ) : Prop where
  hAgr : ∀ a, a ≠ inp.v1 + 7 → a ≠ inp.v1 + 5 →
    ¬(inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length ≤ a ∧
      a < inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length) →
    ¬(inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length ≤ a ∧
      a < inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length) →
    a < stc.dsBaseAddr → mem a = memStart a
  h5 : mem (inp.v1 + 5) = deleteCountJ
  h7 : mem (inp.v1 + 7) = g₀.innerIters1 + g₀.queue.length
  hDelEq : deleteCountJ = g₀.prevDelCountJ +
    ∑ ci ∈ Finset.range ctx.wd.comps.length, (states ci).deleted.card
  hDS : DSArrayAt impl.pathDS ctx.wd.comps ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
    ctx.wd.J0_strip.m w stc.dsBaseAddr (inp.dsHandlesAddr ctx.wd.W.m) hCur mem
    ctx.wd.comps.length states reps
  hDelR : ∀ ci (hci : ci < ctx.wd.comps.length) b, b < (ctx.wd.comps[ci]'hci).J_sub.m →
    mem (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + compEdgeBase ctx.wd ci + b) ≤ g₀.η₁ ∧
    (mem (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + compEdgeBase ctx.wd ci + b) = g₀.η₁ ↔
      b ∈ (states ci).deleted)
  hVhatS : ∀ ci (hci : ci < ctx.wd.comps.length) y, y < (ctx.wd.comps[ci]'hci).J_sub.n →
    mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + y) ≤ g₀.η₁ ∧
    (mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + y) = g₀.η₁ ↔
      y ∈ (states ci).Vhat)
  hDelSub : ∀ ci (hci : ci < ctx.wd.comps.length) b, b ∈ (states ci).deleted →
    b < (ctx.wd.comps[ci]'hci).J_sub.m ∧
    ∃ x ∈ g₀.procVerts, x ∈ (inp.embJH ((ctx.wd.comps[ci]'hci).jSubOrigEdges.getD b 0)).verts
  hDelMono : ∀ ci, (g₀.states ci).deleted ⊆ (states ci).deleted
  hVhMono : ∀ ci, (g₀.states ci).Vhat ⊆ (states ci).Vhat
  hDr_sub : drained ⊆ g₀.procVerts
  hDr_del : ∀ x ∈ drained, x < inp.H'.n →
    ∀ ci (hci : ci < ctx.wd.comps.length) b, b < (ctx.wd.comps[ci]'hci).J_sub.m →
      x ∈ (inp.embJH ((ctx.wd.comps[ci]'hci).jSubOrigEdges.getD b 0)).verts →
      b ∈ (states ci).deleted
  hHCur_le : hCur ≤ stc.dsBaseAddr +
    (g₀.initCountJ + deleteCountJ + g₀.getPathCountJ) * t2DsOne impl inp.J
  hCur_ge : g₀.hCur ≤ hCur

lemma t2DrainInv_init {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) (g₀ : T2Ghost impl.pathDS)
    (hLoc : impl.pathDS.R.Local) {memStart : ℕ → ℕ} (hS : T2StepInv ctx stc g₀ memStart) :
    let mem1 := Function.update memStart (inp.v1 + 7) (g₀.innerIters1 + g₀.queue.length)
    T2DrainInv ctx stc g₀ memStart g₀.drained g₀.states g₀.reps g₀.hCur g₀.deleteCountJ mem1 := by
  intro mem1
  rcases drain_bounds ctx stc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hds := (hS.hDS.frame_below (mem' := mem1) hLoc
    (fun ci hci => by dsimp only [mem1]; exact Function.update_of_ne (by omega) _ _)
    (fun a ha => by dsimp only [mem1]; exact Function.update_of_ne (by omega) _ _)).1
  refine ⟨fun a ha7 _ _ _ _ => by dsimp only [mem1]; exact Function.update_of_ne ha7 _ _,
    by dsimp only [mem1]; rw [Function.update_of_ne (by omega), hS.h5],
    Function.update_self _ _ _, hS.hDelEq, hds,
    fun ci hci b hb => by dsimp only [mem1]; rw [Function.update_of_ne (by omega)]; exact hS.hDelR ci hci b hb,
    fun ci hci y hy => by dsimp only [mem1]; rw [Function.update_of_ne (by omega)]; exact hS.hVhatS ci hci y hy,
    hS.hDelSub, fun _ => Finset.Subset.refl _, fun _ => Finset.Subset.refl _,
    hS.hDr_sub, hS.hDr_del, hS.hHCur_le, le_refl _⟩

lemma T2StepInv.arenaPtr_le_dsBase {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} {ctx : T2Ctx impl inp mem₀ w} {stc : T2StaticData ctx} {g : T2Ghost impl.pathDS}
    {mem : ℕ → ℕ} (h : T2StepInv ctx stc g mem) :
    g.arenaPtr ≤ stc.dsBaseAddr := by
  have h1 := h.hAr_le
  have h2 : ctx.wd.j0Edges.length + g.getPathCountJ ≤ ctx.wd.W.m := by
    have := h.hGetC
    have hj0_le : ctx.wd.j0Edges.length ≤ ctx.wd.W.m := by
      rw [ctx.hw_okW.W_m_eq]; exact Nat.le_add_right _ _
    omega
  have h3 := Nat.mul_le_mul_right (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5) h2
  dsimp only [T2StaticData.dsBaseAddr]; omega

lemma t2DrainInv_finish {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) (g₀ : T2Ghost impl.pathDS)
    (hLoc : impl.pathDS.R.Local) {memStart mem : ℕ → ℕ} (hS : T2StepInv ctx stc g₀ memStart)
    {states : ℕ → PathDSAbsState} {reps : ℕ → impl.pathDS.R.τ} {hCur deleteCountJ : ℕ}
    (hD : T2DrainInv ctx stc g₀ memStart g₀.procVerts states reps hCur deleteCountJ mem) :
    let g' : T2Ghost impl.pathDS :=
      { g₀ with
        states := states, reps := reps, drained := g₀.procVerts, queue := []
        deleteCountJ := deleteCountJ, innerIters1 := g₀.innerIters1 + g₀.queue.length, hCur := hCur }
    let mem' := Function.update mem (inp.v1 + 27) 0
    T2StepInv ctx stc g' mem' := by
  intro g' mem'
  rcases drain_bounds ctx stc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hm_eq : ∀ a, a ≠ inp.v1 + 27 → a ≠ inp.v1 + 7 → a ≠ inp.v1 + 5 →
      ¬(inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length ≤ a ∧
        a < inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length) →
      ¬(inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length ≤ a ∧
        a < inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length) →
      a < stc.dsBaseAddr → mem' a = memStart a := fun a h27 h7 h5 hc hv hds => by
    dsimp only [mem']; rw [Function.update_of_ne h27]; exact hD.hAgr a h7 h5 hc hv hds
  have hslot : ∀ k ≤ 31, k ≠ 5 → k ≠ 7 → k ≠ 27 → mem' (inp.v1 + k) = memStart (inp.v1 + k) :=
    fun k hk h5 h7 h27 => hm_eq (inp.v1 + k) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have har := hS.arenaPtr_le_dsBase
  have hInc' : ∀ x < inp.H'.n,
      IncChainBound mem' (inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length) stc.nodesEnd
        (mem' (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x)) (stc.L_inc x) ∧
      (∀ p ∈ stc.L_inc x, ∃ (hp : p.1 < ctx.wd.comps.length),
        p.2 < (ctx.wd.comps[p.1]'hp).J_sub.m ∧
        x ∈ (inp.embJH ((ctx.wd.comps[p.1]'hp).jSubOrigEdges.getD p.2 0)).verts) ∧
      (∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (b : ℕ), b < (ctx.wd.comps[ci]'hci).J_sub.m →
        x ∈ (inp.embJH ((ctx.wd.comps[ci]'hci).jSubOrigEdges.getD b 0)).verts → (ci, b) ∈ stc.L_inc x) := by
    intro x hx; obtain ⟨hc, hsub, hmem⟩ := hS.hInc x hx
    refine ⟨?_, hsub, hmem⟩
    rw [hm_eq _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hc.mono fun a ha1 ha2 => hm_eq a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hEmb' : EmbInv mem' inp.embWJAddr ctx.wd.W.m stc.nodesEnd g₀.arenaPtr g₀.emb := by
    intro eW heW; have hm1 := hS.hEmb eW heW
    have hptr : mem' (inp.embWJAddr + eW) = memStart (inp.embWJAddr + eW) :=
      hm_eq _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    cases hemb : g₀.emb eW with
    | none => simp only [hemb] at hm1 ⊢; rw [hptr]; exact hm1
    | some P =>
      simp only [hemb] at hm1 ⊢; rw [hptr]
      refine ⟨hm1.1, hm1.2.1, listAt_of_congr hm1.2.2 fun j hj => ?_⟩
      exact hm_eq _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hDS' := (hD.hDS.frame_below (mem' := mem') hLoc
    (fun ci hci => by dsimp only [mem']; exact Function.update_of_ne (by omega) _ _)
    (fun a ha => by dsimp only [mem']; exact Function.update_of_ne (by omega) _ _)).1
  refine
    { agr_pre := fun a ha => (hm_eq a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (hS.agr_pre a ha)
      h0 := by simpa using (hslot 0 (by omega) (by omega) (by omega) (by omega)).trans hS.h0
      h1 := (hslot 1 (by omega) (by omega) (by omega) (by omega)).trans hS.h1
      hη_pos := hS.hη_pos, hη_bd := hS.hη_bd
      h2 := (hslot 2 (by omega) (by omega) (by omega) (by omega)).trans hS.h2, hInitC := hS.hInitC
      h3 := (hslot 3 (by omega) (by omega) (by omega) (by omega)).trans hS.h3, hInitE := hS.hInitE
      h4 := (hslot 4 (by omega) (by omega) (by omega) (by omega)).trans hS.h4, hGetC := hS.hGetC
      h5 := by dsimp only [mem']; rw [Function.update_of_ne (by omega), hD.h5]
      hDelEq := hD.hDelEq, hPrevDel := hS.hPrevDel
      h6 := (hslot 6 (by omega) (by omega) (by omega) (by omega)).trans hS.h6, hVcUpd := hS.hVcUpd
      h7 := by dsimp only [mem']; rw [Function.update_of_ne (by omega), hD.h7]
      hInner := by dsimp only [g']; simpa using hS.hInner
      h8 := (hslot 8 (by omega) (by omega) (by omega) (by omega)).trans hS.h8
      h9 := (hslot 9 (by omega) (by omega) (by omega) (by omega)).trans hS.h9
      h10 := (hslot 10 (by omega) (by omega) (by omega) (by omega)).trans hS.h10
      h12 := (hslot 12 (by omega) (by omega) (by omega) (by omega)).trans hS.h12
      h13 := (hslot 13 (by omega) (by omega) (by omega) (by omega)).trans hS.h13
      h14 := (hslot 14 (by omega) (by omega) (by omega) (by omega)).trans hS.h14
      h15 := (hslot 15 (by omega) (by omega) (by omega) (by omega)).trans hS.h15
      h16 := (hslot 16 (by omega) (by omega) (by omega) (by omega)).trans hS.h16
      h17 := (hslot 17 (by omega) (by omega) (by omega) (by omega)).trans hS.h17
      h18 := (hslot 18 (by omega) (by omega) (by omega) (by omega)).trans hS.h18
      h19 := (hslot 19 (by omega) (by omega) (by omega) (by omega)).trans hS.h19
      h20 := (hslot 20 (by omega) (by omega) (by omega) (by omega)).trans hS.h20
      h21 := (hslot 21 (by omega) (by omega) (by omega) (by omega)).trans hS.h21
      h22 := (hslot 22 (by omega) (by omega) (by omega) (by omega)).trans hS.h22
      h23 := (hslot 23 (by omega) (by omega) (by omega) (by omega)).trans hS.h23
      h24 := (hslot 24 (by omega) (by omega) (by omega) (by omega)).trans hS.h24
      h25 := (hslot 25 (by omega) (by omega) (by omega) (by omega)).trans hS.h25
      h26 := (hslot 26 (by omega) (by omega) (by omega) (by omega)).trans hS.h26, hQid := hS.hQid
      h27 := Function.update_self _ _ _
      h28 := (hslot 28 (by omega) (by omega) (by omega) (by omega)).trans hS.h28
      h29 := (hslot 29 (by omega) (by omega) (by omega) (by omega)).trans hS.h29
      h30 := (hslot 30 (by omega) (by omega) (by omega) (by omega)).trans hS.h30
      h31 := (hslot 31 (by omega) (by omega) (by omega) (by omega)).trans hS.h31
      hCeb := fun ci hci => (hm_eq _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (hS.hCeb ci hci)
      hVho := fun ci hci => (hm_eq _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (hS.hVho ci hci)
      hInc := hInc', hEmb := hEmb', hAr_le := hS.hAr_le, hDS := hDS'
      hDelR := fun ci hci b hb => by dsimp only [mem']; rw [Function.update_of_ne (by omega)]; exact hD.hDelR ci hci b hb
      hVhatS := fun ci hci y hy => by dsimp only [mem']; rw [Function.update_of_ne (by omega)]; exact hD.hVhatS ci hci y hy
      hDelSub := hD.hDelSub
      hVc := fun x hx => (hm_eq _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (hS.hVc x hx)
      hEwSt := fun x hx => by rw [hm_eq _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hS.hEwSt x hx
      hProcS := fun x hx => by rw [hm_eq _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hS.hProcS x hx
      hProcSub := fun x hx => hS.hProcSub x hx, hQ_nd := List.nodup_nil,
      hQ_sub := fun x hx => by simp [g'] at hx,
      hDr_sub := by dsimp only [g']; exact Finset.Subset.refl _,
      hQ_mem := fun x hx => by dsimp only [g'] at hx ⊢; simp [hx],
      hQ_at := fun i hi => by simp [g'] at hi,
      hDr_del := hD.hDr_del, hPart := hS.hPart, hMono := hS.hMono, hj0 := hS.hj0
      hELen := hS.hELen, hVc_prev := hS.hVc_prev, hVol_prev := hS.hVol_prev, hHCur_le := hD.hHCur_le }

end MinCostFlow.Spanner
