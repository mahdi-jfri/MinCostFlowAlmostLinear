module

public import MinCostFlow.Spanner.ProgWitnessPrepHelpers

/-!
# Pure Component-Block Helpers and Invariant Predicates for `witnessPrep`

Provides `compBlocksAux` splitting properties, disjointness and uniqueness of component endpoints
within a level block, subgraph edge/origin specifications, and block-loop predicates (`CompsDoneUpTo`,
`CompsParsedFrom`, `VertMarksZero`, `VertMarksPartial`, `VertMarksBlock`).
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## 4. Block Loop Sub-Lemmas & Full Proof -/

theorem dropWhile_length_le {α : Type*} (p : α → Bool) :
    ∀ l : List α, (l.dropWhile p).length ≤ l.length
  | [] => le_rfl
  | a :: l => by
    simp only [List.dropWhile_cons]
    split
    · exact le_trans (dropWhile_length_le p l) (Nat.le_succ _)
    · exact le_rfl

theorem compBlocksAux_fst_eq :
    ∀ (idx : ℕ) (xs : List (ℕ × List ℕ))
      (done : List (ℕ × ℕ × List (ℕ × List ℕ))) (b : ℕ × ℕ × List (ℕ × List ℕ))
      (rest : List (ℕ × ℕ × List (ℕ × List ℕ))),
      compBlocksAux idx xs = done ++ b :: rest →
        b.1 = idx + (done.flatMap (·.2.2)).length
  | idx, [], done, b, rest, h => by cases done <;> simp [compBlocksAux] at h
  | idx, c :: cs, done, b, rest, h => by
    have hlt_cs : (cs.dropWhile fun q => decide (q.1 = c.1)).length < (c :: cs).length :=
      Nat.lt_succ_of_le (dropWhile_length_le _ cs)
    cases done with
    | nil =>
      simp only [compBlocksAux, List.nil_append, List.cons.injEq] at h
      rw [← h.1]; simp
    | cons d ds =>
      simp only [compBlocksAux, List.cons_append, List.cons.injEq] at h
      rcases h with ⟨rfl, htail⟩
      have ih := compBlocksAux_fst_eq (idx + (c :: cs.takeWhile fun q => decide (q.1 = c.1)).length)
        (cs.dropWhile fun q => decide (q.1 = c.1)) ds b rest htail
      simp only [List.flatMap_cons, List.length_append, ih]
      omega
termination_by _ xs _ _ _ _ => xs.length
decreasing_by exact Nat.lt_succ_of_le (dropWhile_length_le _ cs)

theorem compBlocksAux_split_spec {xs : List (ℕ × List ℕ)}
    (hpw : List.Pairwise (fun a b => a.1 ≤ b.1) xs)
    {done : List (ℕ × ℕ × List (ℕ × List ℕ))} {i₀ lvl : ℕ} {block : List (ℕ × List ℕ)}
    {rest : List (ℕ × ℕ × List (ℕ × List ℕ))}
    (hcb : compBlocksAux 0 xs = done ++ (i₀, lvl, block) :: rest) :
    i₀ = (done.flatMap (·.2.2)).length ∧
    0 < block.length ∧
    i₀ + block.length ≤ xs.length ∧
    (∀ c ∈ block, c.1 = lvl) ∧
    (∀ k (hk : k < block.length), xs[i₀ + k]? = some (block[k]'hk)) ∧
    (i₀ + block.length < xs.length →
      ∃ q, xs[i₀ + block.length]? = some q ∧ lvl < q.1) ∧
    xs.filter (fun c => decide (c.1 = lvl)) = block := by
  have h1 := compBlocksAux_fst_eq 0 xs done (i₀, lvl, block) rest hcb
  simp only [Nat.zero_add] at h1
  have hmem : (i₀, lvl, block) ∈ compBlocksAux 0 xs := by rw [hcb]; simp
  obtain ⟨hpw_lvl, _, hfm, hprops⟩ := compBlocksAux_props 0 xs hpw
  obtain ⟨_, hlen_le, hget, hnext⟩ := compBlocksAux_getElem 0 xs hpw (i₀, lvl, block) hmem
  have hb_props := hprops (i₀, lvl, block) hmem
  rw [hcb] at hpw_lvl hfm
  simp only [List.flatMap_append, List.flatMap_cons, List.pairwise_append] at hpw_lvl hfm
  have hdone_lt : ∀ c ∈ done.flatMap (·.2.2), c.1 < lvl := by
    intro c hc
    rcases List.mem_flatMap.mp hc with ⟨d, hd, hcd⟩
    have hd_mem : d ∈ compBlocksAux 0 xs := by rw [hcb]; exact List.mem_append_left _ hd
    rw [(hprops d hd_mem).2 c hcd]
    exact hpw_lvl.2.2 d hd (i₀, lvl, block) List.mem_cons_self
  have hrest_gt : ∀ c ∈ rest.flatMap (·.2.2), lvl < c.1 := by
    intro c hc
    rcases List.mem_flatMap.mp hc with ⟨r, hr, hcr⟩
    have hr_mem : r ∈ compBlocksAux 0 xs := by
      rw [hcb]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
    rw [(hprops r hr_mem).2 c hcr]
    exact (List.pairwise_cons.mp hpw_lvl.2.1).1 r hr
  have hfilt : xs.filter (fun c => decide (c.1 = lvl)) = block := by
    rw [← hfm]
    simp only [List.filter_append]
    have hf1 : (done.flatMap (·.2.2)).filter (fun c => decide (c.1 = lvl)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc hdec
      have := hdone_lt c hc
      simp only [decide_eq_true_eq] at hdec
      omega
    have hf2 : block.filter (fun c => decide (c.1 = lvl)) = block :=
      List.filter_eq_self.mpr fun c hc => by simp [hb_props.2 c hc]
    have hf3 : (rest.flatMap (·.2.2)).filter (fun c => decide (c.1 = lvl)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc hdec
      have := hrest_gt c hc
      simp only [decide_eq_true_eq] at hdec
      omega
    rw [hf1, hf2, hf3, List.nil_append, List.append_nil]
  refine ⟨h1, hb_props.1, by simpa using hlen_le, hb_props.2, ?_, ?_, hfilt⟩
  · intro k hk
    have hgk := hget k hk
    simp only [Nat.sub_zero, List.getElem?_eq_getElem hk] at hgk
    exact hgk
  · intro hlt
    simpa [Nat.zero_add] using hnext (by simpa [Nat.zero_add] using hlt)

theorem comp_verts_disjoint_block {inp : PrepInput} {mem₀ : ℕ → ℕ} {w : ℕ}
    (hv : inp.Valid mem₀ w) {done : List (ℕ × ℕ × List (ℕ × List ℕ))} {i₀ lvl : ℕ}
    {block : List (ℕ × List ℕ)} {rest : List (ℕ × ℕ × List (ℕ × List ℕ))}
    (hcb : compBlocksAux 0 inp.rawComps = done ++ (i₀, lvl, block) :: rest)
    {k₁ k₂ : ℕ} (hk₁ : i₀ ≤ k₁) (hk₁' : k₁ < i₀ + block.length)
    (hk₂ : i₀ ≤ k₂) (hk₂' : k₂ < i₀ + block.length) (hne : k₁ ≠ k₂) :
    Disjoint (inp.rawComps[k₁]'(by
        have := (compBlocksAux_split_spec hv.2.2.2.2.2.2.2.2.2.2.1 hcb).2.2.1; omega)).2.toFinset
      (inp.rawComps[k₂]'(by
        have := (compBlocksAux_split_spec hv.2.2.2.2.2.2.2.2.2.2.1 hcb).2.2.1; omega)).2.toFinset := by
  have hsp := compBlocksAux_split_spec hv.2.2.2.2.2.2.2.2.2.2.1 hcb
  rcases hsp with ⟨_, hpos, hle, hlvl_b, hget, _, hfilt⟩
  have h1_lvl : 1 ≤ lvl ∧ lvl ≤ inp.d_ℓ := by
    have hc₀ := hget 0 hpos
    rw [List.getElem?_eq_getElem (by omega)] at hc₀
    have hc_eq : inp.rawComps[i₀ + 0] = block[0] := Option.some.inj hc₀
    have hcm := hv.2.2.2.2.2.2.2.2.2.2.2.1 inp.rawComps[i₀] (List.getElem_mem (by omega))
    have hbl := hlvl_b block[0] (List.getElem_mem hpos)
    simp only [Nat.add_zero] at hc_eq
    rw [hc_eq, hbl] at hcm
    exact ⟨hcm.1, hcm.2.1⟩
  have hdisj : (inp.decomp.comps lvl).Pairwise Disjoint :=
    (hv.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2 lvl h1_lvl.1 h1_lvl.2).1
  simp only [PrepInput.decomp, mkDecomposeOutput, hfilt] at hdisj
  have hp := List.pairwise_iff_getElem.mp hdisj
  have hget₁ : inp.rawComps[k₁]'(by omega) = block[k₁ - i₀] := by
    have h := hget (k₁ - i₀) (by omega)
    rw [show i₀ + (k₁ - i₀) = k₁ by omega, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  have hget₂ : inp.rawComps[k₂]'(by omega) = block[k₂ - i₀] := by
    have h := hget (k₂ - i₀) (by omega)
    rw [show i₀ + (k₂ - i₀) = k₂ by omega, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  simp only [hget₁, hget₂]
  by_cases hlt : k₁ - i₀ < k₂ - i₀
  · have hp' := hp (k₁ - i₀) (k₂ - i₀) (by simp; omega) (by simp; omega) hlt
    simp only [List.getElem_map] at hp'
    exact hp'
  · have hp' := hp (k₂ - i₀) (k₁ - i₀) (by simp; omega) (by simp; omega) (by omega)
    simp only [List.getElem_map] at hp'
    exact hp'.symm

theorem edge_unique_comp_at_lvl {inp : PrepInput} {mem₀ : ℕ → ℕ} {w : ℕ}
    (hv : inp.Valid mem₀ w) {done : List (ℕ × ℕ × List (ℕ × List ℕ))} {i₀ lvl : ℕ}
    {block : List (ℕ × List ℕ)} {rest : List (ℕ × ℕ × List (ℕ × List ℕ))}
    (hcb : compBlocksAux 0 inp.rawComps = done ++ (i₀, lvl, block) :: rest)
    {b : ℕ} (hb : b ∈ DecomposeOutput.edgesAt inp.J0_strip inp.decomp lvl) :
    ∃ (ci : ℕ) (hci : ci < inp.rawComps.length), i₀ ≤ ci ∧ ci < i₀ + block.length ∧
      (inp.J0_strip.edges.getD b (0, 0)).1 ∈ inp.rawComps[ci].2 ∧
      (inp.J0_strip.edges.getD b (0, 0)).2 ∈ inp.rawComps[ci].2 ∧
      (∀ (cj : ℕ) (hcj : cj < inp.rawComps.length), i₀ ≤ cj → cj < i₀ + block.length →
        (inp.J0_strip.edges.getD b (0, 0)).1 ∈ inp.rawComps[cj].2 → cj = ci) ∧
      (inp.J0_strip.edges.getD b (0, 0)).1 < inp.J.n ∧
      (inp.J0_strip.edges.getD b (0, 0)).2 < inp.J.n := by
  have hsp := compBlocksAux_split_spec hv.2.2.2.2.2.2.2.2.2.2.1 hcb
  rcases hsp with ⟨_, hpos, hle, hlvl_b, hget, _, hfilt⟩
  have hc0 : block[0] ∈ inp.rawComps := by
    have h0 := hget 0 hpos
    rw [List.getElem?_eq_getElem (by omega)] at h0
    have : inp.rawComps[i₀] = block[0] := Option.some.inj h0
    rw [← this]
    exact List.getElem_mem (by omega)
  have hlvl_bd := hv.2.2.2.2.2.2.2.2.2.2.2.1 block[0] hc0
  rw [hlvl_b block[0] (List.getElem_mem hpos)] at hlvl_bd
  have he_mem : inp.J0_strip.edges.getD b (0, 0) ∈ (inp.decomp.graphAt inp.J0_strip lvl).edges := by
    simp only [DecomposeOutput.graphAt]
    exact List.mem_map_of_mem hb
  have hex := (hv.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2 lvl hlvl_bd.1 hlvl_bd.2.1).2.2 _ he_mem
  rcases hex with ⟨X, hX, he1, he2⟩
  simp only [PrepInput.decomp, mkDecomposeOutput, hfilt, List.mem_map] at hX
  rcases hX with ⟨c, hc_blk, rfl⟩
  rcases List.mem_iff_getElem.mp hc_blk with ⟨k, hk, hck⟩
  set ci := i₀ + k
  have hci : ci < inp.rawComps.length := by omega
  have hget_ci : inp.rawComps[ci] = c := by
    have h := hget k hk
    rw [List.getElem?_eq_getElem (by omega)] at h
    rw [← hck]; exact Option.some.inj h
  have hb_m : b < inp.J0_strip.m := by
    simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hb
    exact hb.1
  have hJ0_val : inp.J0_strip.IsValid := hv.2.2.1 ▸ stripLoops_isValid hv.1
  have he_bd : (inp.J0_strip.edges.getD b (0, 0)).1 < inp.J0_strip.n ∧
      (inp.J0_strip.edges.getD b (0, 0)).2 < inp.J0_strip.n := by
    rw [List.getD_eq_getElem _ _ (by simpa [Graph.m] using hb_m)]
    exact hJ0_val _ (List.getElem_mem (by simpa [Graph.m] using hb_m))
  have hn_eq : inp.J0_strip.n = inp.J.n := by rw [hv.2.2.1]; rfl
  refine ⟨ci, hci, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hget_ci, List.mem_toFinset] using he1
  · simpa [hget_ci, List.mem_toFinset] using he2
  · intro cj hcj hcj1 hcj2 hmem_cj
    by_contra hne
    have hdisj := comp_verts_disjoint_block hv hcb (by omega) (by omega) hcj1 hcj2 (Ne.symm hne)
    exact Finset.disjoint_left.mp hdisj
      (by simpa [hget_ci, List.mem_toFinset] using he1)
      (by simpa [List.mem_toFinset] using hmem_cj)
  · omega
  · omega

theorem rawComps_getD_eq_getBang (xs : List (ℕ × List ℕ)) {k : ℕ} (hk : k < xs.length) :
    xs.getD k (0, []) = xs[k]! := by
  rw [List.getD_eq_getElem _ _ hk, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

theorem block_lvl_bounds {inp : PrepInput} {mem₀ : ℕ → ℕ} {w : ℕ}
    (hv : inp.Valid mem₀ w)
    {done rest : List (ℕ × ℕ × List (ℕ × List ℕ))} {i₀ lvl : ℕ} {block : List (ℕ × List ℕ)}
    (hcb : compBlocksAux 0 inp.rawComps = done ++ (i₀, lvl, block) :: rest) :
    1 ≤ lvl ∧ lvl ≤ inp.d_ℓ := by
  obtain ⟨_, hpos, hle, hlvl, hget, _, _⟩ :=
    compBlocksAux_split_spec hv.2.2.2.2.2.2.2.2.2.2.1 hcb
  have h0 := hget 0 hpos
  rw [List.getElem?_eq_getElem (by omega)] at h0
  have hmem : block[0] ∈ inp.rawComps := by
    rw [← Option.some.inj h0]
    exact List.getElem_mem (by omega)
  have hp := hv.2.2.2.2.2.2.2.2.2.2.2.1 block[0] hmem
  have hbl : block[0].1 = lvl := hlvl block[0] (List.getElem_mem hpos)
  rw [← hbl]
  exact ⟨hp.1, hp.2.1⟩

theorem comp_props_at {inp : PrepInput} {mem₀ : ℕ → ℕ} {w : ℕ}
    (hv : inp.Valid mem₀ w) {ci : ℕ} (hci : ci < inp.rawComps.length) :
    let c := inp.rawComps[ci]!
    1 ≤ c.1 ∧ c.1 ≤ inp.d_ℓ ∧ c.2.Pairwise (· < ·) ∧ 2 ≤ c.2.length ∧
    c.2.Nodup ∧ (∀ u ∈ c.2, u < inp.J.n) ∧ (inp.cJSub c).n = c.2.length ∧
    (inp.cJSub c).IsValid := by
  have hc_eq : inp.rawComps[ci]! = inp.rawComps[ci] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hci]; rfl
  intro c
  have hcmem : c ∈ inp.rawComps := by
    dsimp only [c]; rw [hc_eq]; exact List.getElem_mem hci
  rcases hv.2.2.2.2.2.2.2.2.2.2.2.1 c hcmem with ⟨hc1, hc2, hpw, hlen⟩
  have hnd : c.2.Nodup := List.Pairwise.imp (fun {a b} h => LT.lt.ne h) hpw
  have hX : c.2.toFinset ∈ inp.decomp.comps c.1 := by
    simp only [PrepInput.decomp, mkDecomposeOutput, List.mem_map, List.mem_filter,
      decide_eq_true_eq]
    exact ⟨c, ⟨hcmem, rfl⟩, rfl⟩
  have hsub := ((hv.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2 c.1 hc1 hc2).2.1
    c.2.toFinset hX).1
  have hu : ∀ u ∈ c.2, u < inp.J.n := by
    intro u hu
    have hmem_v : u ∈ inp.J0_strip.verts := hsub (List.mem_toFinset.mpr hu)
    have hn_eq : inp.J0_strip.n = inp.J.n := by rw [hv.2.2.1]; rfl
    simpa [Graph.verts, hn_eq] using hmem_v
  have hvs : vertsOf c.2.toFinset = c.2 := vertsOf_toFinset_of_pairwise_lt hpw
  have hcard : c.2.toFinset.card = c.2.length := by
    rw [← vertsOf_length, hvs]
  have hn : (inp.cJSub c).n = c.2.length := by
    simp only [PrepInput.cJSub, inducedSubgraph, hcard]
  exact ⟨hc1, hc2, hpw, hlen, hnd, hu, hn, inducedSubgraph_isValid _ _⟩

theorem cVertsPtr_add_le_h {inp : PrepInput} {mem₀ : ℕ → ℕ} {w : ℕ}
    (hv : inp.Valid mem₀ w) {ci : ℕ} (hci : ci < inp.rawComps.length) :
    inp.cVertsPtr ci + inp.rawComps[ci]!.2.length ≤ inp.h := by
  have hdecle := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdl := decompose_encode_length inp.d_ℓ inp.phiNum_dec inp.phiDen_dec inp.level inp.rawComps
  have hllen := hv.2.2.2.2.2.2.2.1
  have hc_eq : inp.rawComps[ci]! = inp.rawComps[ci] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hci]; rfl
  have htake := congrArg (List.map fun p : ℕ × List ℕ => 2 + p.2.length)
    (List.take_append_drop ci inp.rawComps)
  have hsum := congrArg List.sum htake
  rw [List.drop_eq_getElem_cons hci, List.map_append, List.map_cons,
    List.sum_append, List.sum_cons] at hsum
  change ((inp.rawComps.take ci).map fun p => 2 + p.2.length).sum +
      (2 + inp.rawComps[ci].2.length +
        ((inp.rawComps.drop (ci + 1)).map fun p => 2 + p.2.length).sum) = _ at hsum
  have hle_sum : ((inp.rawComps.take ci).map fun p => 2 + p.2.length).sum +
      (2 + inp.rawComps[ci].2.length) ≤
      (inp.rawComps.map fun p => 2 + p.2.length).sum := by
    rw [← hsum]; omega
  simp only [PrepInput.cVertsPtr, hc_eq]
  omega

theorem comp_edges_orig_spec {inp : PrepInput} {mem₀ : ℕ → ℕ} {w : ℕ}
    (hv : inp.Valid mem₀ w) {ci : ℕ} (hci : ci < inp.rawComps.length) :
    let c := inp.rawComps[ci]!
    let filt := (DecomposeOutput.edgesAt inp.J0_strip inp.decomp c.1).filter
      fun b => decide ((inp.J0_strip.edges.getD b (0, 0)).1 ∈ c.2)
    (inp.cJSub c).edges =
      filt.map (fun b =>
        let e := inp.J0_strip.edges.getD b (0, 0)
        (c.2.idxOf e.1, c.2.idxOf e.2)) ∧
    (inp.cJSub c).m = filt.length ∧
    inp.cJOrig c = filt.map (fun b => inp.nlIdx.getD b 0) ∧
    (inp.cJOrig c).length = (inp.cJSub c).m := by
  have hc_eq : inp.rawComps[ci]! = inp.rawComps[ci] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hci]; rfl
  intro c filt
  have hcmem : c ∈ inp.rawComps := by
    dsimp only [c]; rw [hc_eq]; exact List.getElem_mem hci
  rcases hv.2.2.2.2.2.2.2.2.2.2.2.1 c hcmem with ⟨hc1, hc2, hpw, _⟩
  have hX : c.2.toFinset ∈ inp.decomp.comps c.1 := by
    simp only [PrepInput.decomp, mkDecomposeOutput, List.mem_map, List.mem_filter,
      decide_eq_true_eq]
    exact ⟨c, ⟨hcmem, rfl⟩, rfl⟩
  have hiff_set : ∀ e ∈ (DecomposeOutput.graphAt inp.J0_strip inp.decomp c.1).edges,
      e.1 ∈ c.2.toFinset ↔ e.2 ∈ c.2.toFinset :=
    ((hv.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2 c.1 hc1 hc2).2.1 c.2.toFinset hX).2.2.2.2
  have hvs : vertsOf c.2.toFinset = c.2 := vertsOf_toFinset_of_pairwise_lt hpw
  have hed := inducedSubgraph_edges_eq_filter_map (J0 := inp.J0_strip)
    (d := inp.decomp) (lvl := c.1) hiff_set
  have horig := comp_jSubOrigEdges_eq_filter_map (J0 := inp.J0_strip) (nlIdx := inp.nlIdx)
    (d := inp.decomp) (lvl := c.1) hiff_set
  have hfilt_eq :
      (DecomposeOutput.edgesAt inp.J0_strip inp.decomp c.1).filter
        (fun b => decide ((inp.J0_strip.edges.getD b (0, 0)).1 ∈ c.2.toFinset)) = filt := by
    refine List.filter_congr fun b _ => ?_
    simp [List.mem_toFinset]
  have hed' : (inp.cJSub c).edges =
      filt.map (fun b =>
        let e := inp.J0_strip.edges.getD b (0, 0)
        (c.2.idxOf e.1, c.2.idxOf e.2)) := by
    simpa only [PrepInput.cJSub, hvs, hfilt_eq] using hed
  have horig' : inp.cJOrig c = filt.map (fun b => inp.nlIdx.getD b 0) := by
    simpa only [PrepInput.cJOrig, hfilt_eq] using horig
  refine ⟨hed', ?_, horig', ?_⟩
  · simp [Graph.m, hed']
  · simp [Graph.m, hed', horig']

/-- Component table entries `0 .. nDone - 1` together with their compiled blocks. -/
def CompsDoneUpTo (inp : PrepInput) (mem : ℕ → ℕ) (nDone : ℕ) : Prop :=
  ∀ k < nDone,
    let c := inp.rawComps[k]!
    mem (inp.aComps + 7 * k) = c.1 ∧
    mem (inp.aComps + 7 * k + 1) = c.2.length ∧
    mem (inp.aComps + 7 * k + 2) = inp.cVertsPtr k ∧
    mem (inp.aComps + 7 * k + 3) = inp.cJSubPtr k ∧
    mem (inp.aComps + 7 * k + 4) = inp.cJOrigPtr k ∧
    mem (inp.aComps + 7 * k + 5) = inp.cDegPtr k ∧
    mem (inp.aComps + 7 * k + 6) = (inp.cJSub c).m ∧
    GraphAt mem (inp.cJSubPtr k) (inp.cJSub c) ∧
    ListAt mem (inp.cJOrigPtr k) (inp.cJOrig c) ∧
    ListAt mem (inp.cDegPtr k) ((List.range c.2.length).map (inp.cJSub c).deg)

/-- Component table entries `startIdx .. rawComps.length - 1` after `prepParseStmt`. -/
def CompsParsedFrom (inp : PrepInput) (mem : ℕ → ℕ) (startIdx : ℕ) : Prop :=
  ∀ k, startIdx ≤ k → k < inp.rawComps.length →
    let c := inp.rawComps[k]!
    mem (inp.aComps + 7 * k) = c.1 ∧
    mem (inp.aComps + 7 * k + 1) = c.2.length ∧
    mem (inp.aComps + 7 * k + 2) = inp.cVertsPtr k ∧
    mem (inp.aComps + 7 * k + 3) = 0 ∧
    mem (inp.aComps + 7 * k + 4) = 0 ∧
    mem (inp.aComps + 7 * k + 5) = 0 ∧
    mem (inp.aComps + 7 * k + 6) = 0

/-- Both vertex scratch arrays (`v_comp`, `v_loc`) are all zero. -/
def VertMarksZero (inp : PrepInput) (mem : ℕ → ℕ) : Prop :=
  (∀ u < inp.J.n, mem (inp.aVComp + u) = 0) ∧
  (∀ u < inp.J.n, mem (inp.aVLoc + u) = 0)

/-- Partial vertex scratch marks inside block `[i₀, ci]` up to vertex index `k`. -/
def VertMarksPartial (inp : PrepInput) (mem : ℕ → ℕ) (i₀ ci k : ℕ) : Prop :=
  (∀ cj (hcj : cj < inp.rawComps.length), i₀ ≤ cj → cj < ci →
    ∀ p (hp : p < inp.rawComps[cj].2.length),
      mem (inp.aVComp + inp.rawComps[cj].2[p]) = cj + 1 ∧
      mem (inp.aVLoc + inp.rawComps[cj].2[p]) = p) ∧
  (∀ (hci : ci < inp.rawComps.length),
    ∀ p, p < k → ∀ (hp2 : p < inp.rawComps[ci].2.length),
      mem (inp.aVComp + inp.rawComps[ci].2[p]) = ci + 1 ∧
      mem (inp.aVLoc + inp.rawComps[ci].2[p]) = p) ∧
  (∀ u < inp.J.n,
    (∀ cj (hcj : cj < inp.rawComps.length), i₀ ≤ cj → cj < ci → u ∉ inp.rawComps[cj].2) →
    (∀ (hci : ci < inp.rawComps.length), ∀ p, p < k → ∀ (hp2 : p < inp.rawComps[ci].2.length),
      inp.rawComps[ci].2[p] ≠ u) →
    mem (inp.aVComp + u) = 0 ∧ mem (inp.aVLoc + u) = 0)

/-- Completed vertex scratch marks for the level block `[i₀, i₁)`. -/
def VertMarksBlock (inp : PrepInput) (mem : ℕ → ℕ) (i₀ i₁ : ℕ) : Prop :=
  VertMarksPartial inp mem i₀ i₁ 0

theorem compsDoneUpTo_of_agree {inp : PrepInput} {mem₀ mem mem' : ℕ → ℕ} {w nDone : ℕ}
    (hv : inp.Valid mem₀ w) (hn : nDone ≤ inp.rawComps.length)
    (hd : CompsDoneUpTo inp mem nDone)
    (htab : ∀ x, inp.aComps ≤ x → x < inp.aComps + 7 * nDone → mem' x = mem x)
    (hblk : ∀ x, inp.hBlocksStart ≤ x → x < inp.cJSubPtr nDone → mem' x = mem x) :
    CompsDoneUpTo inp mem' nDone := by
  intro k hk
  have hk_len : k < inp.rawComps.length := lt_of_lt_of_le hk hn
  rcases hd k hk with ⟨h0, h1, h2, h3, h4, h5, h6, hg, ho, hdeg⟩
  have htab_k : ∀ off < 7, mem' (inp.aComps + 7 * k + off) = mem (inp.aComps + 7 * k + off) :=
    fun off hoff => htab _ (by omega) (by omega)
  have hcd_eq : inp.rawComps.getD k (0, []) = inp.rawComps[k]! := rawComps_getD_eq_getBang _ hk_len
  have hlo : inp.hBlocksStart ≤ inp.cJSubPtr k := by
    rw [← inp.cJSubPtr_zero]; exact inp.cJSubPtr_mono (Nat.zero_le k)
  have hhi : inp.cEndPtr k ≤ inp.cJSubPtr nDone := by
    rw [← inp.cJSubPtr_succ hk_len]; exact inp.cJSubPtr_mono hk
  have horig_len := (comp_edges_orig_spec hv hk_len).2.2.2
  have hdeg_len : ((List.range inp.rawComps[k]!.2.length).map (inp.cJSub inp.rawComps[k]!).deg).length =
      inp.rawComps[k]!.2.length := by simp
  refine ⟨(htab_k 0 (by omega)).trans h0, (htab_k 1 (by omega)).trans h1,
    (htab_k 2 (by omega)).trans h2, (htab_k 3 (by omega)).trans h3,
    (htab_k 4 (by omega)).trans h4, (htab_k 5 (by omega)).trans h5,
    (htab_k 6 (by omega)).trans h6, ?_, ?_, ?_⟩
  · refine listAt_of_congr hg fun j hj => hblk _ ?_ ?_
    · omega
    · rw [graph_encode_length] at hj
      simp only [PrepInput.cEndPtr, PrepInput.cDegPtr, PrepInput.cJOrigPtr] at hhi ⊢
      rw [hcd_eq] at hhi; omega
  · refine listAt_of_congr ho fun j hj => hblk _ ?_ ?_
    · simp only [PrepInput.cJOrigPtr]; omega
    · rw [horig_len] at hj
      simp only [PrepInput.cEndPtr, PrepInput.cDegPtr, PrepInput.cJOrigPtr] at hhi ⊢
      rw [hcd_eq] at hhi ⊢; omega
  · refine listAt_of_congr hdeg fun j hj => hblk _ ?_ ?_
    · simp only [PrepInput.cDegPtr, PrepInput.cJOrigPtr]; omega
    · rw [hdeg_len] at hj
      simp only [PrepInput.cEndPtr, PrepInput.cDegPtr, PrepInput.cJOrigPtr] at hhi ⊢
      rw [hcd_eq] at hhi ⊢; omega

theorem compsParsedFrom_of_agree {inp : PrepInput} {mem mem' : ℕ → ℕ} {s : ℕ}
    (hp : CompsParsedFrom inp mem s)
    (hag : ∀ x, inp.aComps + 7 * s ≤ x → x < inp.aComps + 7 * inp.rawComps.length → mem' x = mem x) :
    CompsParsedFrom inp mem' s := by
  intro k hk1 hk2
  rcases hp k hk1 hk2 with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  have h : ∀ off < 7, mem' (inp.aComps + 7 * k + off) = mem (inp.aComps + 7 * k + off) :=
    fun off hoff => hag _ (by omega) (by omega)
  exact ⟨(h 0 (by omega)).trans h0, (h 1 (by omega)).trans h1, (h 2 (by omega)).trans h2,
    (h 3 (by omega)).trans h3, (h 4 (by omega)).trans h4, (h 5 (by omega)).trans h5,
    (h 6 (by omega)).trans h6⟩

theorem vertMarksZero_of_zeroFrom {inp : PrepInput} {mem : ℕ → ℕ}
    (hz : ZeroFrom mem inp.aVComp) : VertMarksZero inp mem :=
  ⟨fun u _ => hz (inp.aVComp + u) (by omega),
   fun u _ => hz (inp.aVLoc + u) (by simp only [PrepInput.aVLoc]; omega)⟩

theorem vertMarksZero_of_agree {inp : PrepInput} {mem mem' : ℕ → ℕ}
    (hvz : VertMarksZero inp mem)
    (hag : ∀ x, inp.aVComp ≤ x → x < inp.hBlocksStart → mem' x = mem x) :
    VertMarksZero inp mem' := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have hx : inp.aVComp ≤ inp.aVComp + u ∧ inp.aVComp + u < inp.hBlocksStart := by
      rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc]; omega
    exact (hag _ hx.1 hx.2).trans (hvz.1 u hu)
  · have hx : inp.aVComp ≤ inp.aVLoc + u ∧ inp.aVLoc + u < inp.hBlocksStart := by
      rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc]; omega
    exact (hag _ hx.1 hx.2).trans (hvz.2 u hu)

theorem vertMarksPartial_zero {inp : PrepInput} {mem : ℕ → ℕ} {i₀ : ℕ}
    (hvz : VertMarksZero inp mem) : VertMarksPartial inp mem i₀ i₀ 0 :=
  ⟨fun _ _ _ _ => by omega, fun _ _ _ _ => by omega, fun u hu _ _ => ⟨hvz.1 u hu, hvz.2 u hu⟩⟩

end MinCostFlow.Spanner
