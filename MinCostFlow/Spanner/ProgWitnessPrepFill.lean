module

public import MinCostFlow.Spanner.ProgWitnessPrepBlockHelpers
import MinCostFlow.Spanner.ProgWitnessPrepFillInv

/-!
# Verification of `prepFillStmt`

Proves `prepFill_triple` via the step lemma `prepFill_step` using the flat state combinators
`runs_seq_assign_flat` and `runs_seq_store_flat` and the invariant lemma `prepFill_fin_inv`.
-/

public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

private theorem prepFill_step {w : ℕ} {p : Program} (inp : PrepInput) (mem₀ : ℕ → ℕ)
    (hv : inp.Valid mem₀ w)
    {done rest : List (ℕ × ℕ × List (ℕ × List ℕ))} {i₀ lvl : ℕ} {block : List (ℕ × List ℕ)}
    (hcb : compBlocksAux 0 inp.rawComps = done ++ (i₀, lvl, block) :: rest)
    {b : ℕ} {bs : List ℕ} {st : State} :
    PrepFillInv inp mem₀ i₀ lvl block (b :: bs) st →
      ∃ c, (Expr.bin BinOp.lt (Expr.const 0) (Expr.reg 29)).eval w st = some c ∧ c ≠ 0 ∧
        ∀ s ω, s = st → ∃ o st' c_cost,
          Runs w p ω prepFillBody s o st' c_cost ∧
          (match o with
           | Outcome.returned _ => False
           | Outcome.normal => PrepFillInv inp mem₀ i₀ lvl block bs st') ∧
          c_cost ≤ 155 := by
  intro hinv
  have hsz := inp.size_bounds hv
  have hw1 := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwb := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hpw_rc := hv.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨_, _, hle, hlvl_blk, hget_blk, _, _⟩ := compBlocksAux_split_spec hpw_rc hcb
  obtain ⟨hlvl1, hlvl2⟩ := block_lvl_bounds hv hcb
  let i₁ := i₀ + block.length
  let edges := DecomposeOutput.edgesAt inp.J0_strip inp.decomp lvl
  dsimp only [PrepFillInv] at hinv
  rcases hinv with ⟨pref, heq, hf, h16, h17, h22, h23, hch, hst, hdone, hparsed, hvm, hzf, hfill⟩
  rw [ChainAt.eq_2] at hch
  rcases hch with ⟨h29, hch_tail⟩
  have hb_mem : b ∈ edges := by dsimp only [edges]; rw [heq]; simp
  have hb_m : b < inp.J0_strip.m := by
    simp only [edges, DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hb_mem
    exact hb_mem.1
  have hb1_lt : b + 1 < 2 ^ w := by omega
  have hcond_ev : (Expr.bin BinOp.lt (Expr.const 0) (Expr.reg 29)).eval w st = some 1 :=
    ev_lt_t (ev_const (by omega)) (ev_reg h29 hb1_lt) (by omega) hw1
  refine ⟨1, hcond_ev, by omega, ?_⟩
  intro s ω h_eq
  subst h_eq
  rcases edge_unique_comp_at_lvl hv hcb hb_mem with
    ⟨ci, hci_len, hci_lo, hci_hi, he1_ci, he2_ci, huniq, he1_n, he2_n⟩
  have hc_eq : inp.rawComps[ci]! = inp.rawComps[ci] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hci_len]; rfl
  let c := inp.rawComps[ci]!
  have hc_props := comp_props_at hv hci_len
  let e := inp.J0_strip.edges.getD b (0, 0)
  let u := e.1
  let v := e.2
  let u' := c.2.idxOf u
  let v' := c.2.idxOf v
  have he1_c2 : u ∈ c.2 := by dsimp only [u, e, c]; rw [hc_eq]; exact he1_ci
  have he2_c2 : v ∈ c.2 := by dsimp only [v, e, c]; rw [hc_eq]; exact he2_ci
  have hu'_lt : u' < c.2.length := List.idxOf_lt_length_iff.mpr he1_c2
  have hv'_lt : v' < c.2.length := List.idxOf_lt_length_iff.mpr he2_c2
  have hu'_lt_ci : u' < inp.rawComps[ci].2.length := by rw [← hc_eq]; exact hu'_lt
  have hv'_lt_ci : v' < inp.rawComps[ci].2.length := by rw [← hc_eq]; exact hv'_lt
  have hget_u' : c.2[u']'hu'_lt = u := List.getElem_idxOf hu'_lt
  have hget_v' : c.2[v']'hv'_lt = v := List.getElem_idxOf hv'_lt
  have hidx_u_eq : inp.rawComps[ci].2[u']'hu'_lt_ci = u := by
    have hopt : inp.rawComps[ci].2[u']? = some u := by
      rw [← hc_eq, List.getElem?_eq_getElem hu'_lt, hget_u']
    exact Option.some.inj ((List.getElem?_eq_getElem hu'_lt_ci).symm.trans hopt)
  have hidx_v_eq : inp.rawComps[ci].2[v']'hv'_lt_ci = v := by
    have hopt : inp.rawComps[ci].2[v']? = some v := by
      rw [← hc_eq, List.getElem?_eq_getElem hv'_lt, hget_v']
    exact Option.some.inj ((List.getElem?_eq_getElem hv'_lt_ci).symm.trans hopt)
  have hvc_u : s.mem (inp.aVComp + u) = ci + 1 := by
    have hv1 := (hvm.1 ci hci_len hci_lo hci_hi u' hu'_lt_ci).1
    rw [hidx_u_eq] at hv1; exact hv1
  have hvl_u : s.mem (inp.aVLoc + u) = u' := by
    have hv2 := (hvm.1 ci hci_len hci_lo hci_hi u' hu'_lt_ci).2
    rw [hidx_u_eq] at hv2; exact hv2
  have hvl_v : s.mem (inp.aVLoc + v) = v' := by
    have hv2 := (hvm.1 ci hci_len hci_lo hci_hi v' hv'_lt_ci).2
    rw [hidx_v_eq] at hv2; exact hv2
  have hgJ0 : GraphAt s.mem inp.j0Addr inp.J0_strip :=
    GraphAt.of_agree_below hv.2.2.2.1 hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hst.1
  have he1_val : s.mem (inp.j0Addr + 2 + 2 * b) = u := by
    have hget := graphAt_edge_fst hgJ0 hb_m
    dsimp only [u, e]
    rw [List.getD_eq_getElem _ _ (by simpa [Graph.m] using hb_m)]
    exact hget
  have he2_val : s.mem (inp.j0Addr + 3 + 2 * b) = v := by
    have hget := graphAt_edge_snd hgJ0 hb_m
    dsimp only [v, e]
    rw [List.getD_eq_getElem _ _ (by simpa [Graph.m] using hb_m)]
    exact hget
  have hnl_len : inp.nlIdx.length = inp.J0_strip.m := by
    have hnl_eq := hv.2.2.2.2.1
    have hj0_eq := hv.2.2.1
    rw [hj0_eq, stripLoops]; simp [Graph.m, hnl_eq]
  have hb_nl : b < inp.nlIdx.length := by rw [hnl_len]; exact hb_m
  have horig_eq : inp.nlIdx.getD b 0 = inp.nlIdx[b]'hb_nl :=
    List.getD_eq_getElem inp.nlIdx 0 hb_nl
  have horig_val : s.mem (inp.nlAddr + b) = inp.nlIdx.getD b 0 := by
    have hlNl := hv.2.2.2.2.2.1
    have hst_nl := listAt_getElem hlNl hb_nl
    rw [hst.1 (inp.nlAddr + b) (by have := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega), hst_nl,
      horig_eq]
  have horig_lt : inp.nlIdx.getD b 0 < 2 ^ w := by
    rw [horig_eq]
    have hmem_nl : inp.nlIdx[b]'hb_nl ∈ nonloopIndices inp.J := by
      rw [← hv.2.2.2.2.1]; exact List.getElem_mem hb_nl
    have hm_j : (inp.nlIdx[b]'hb_nl) < inp.J.m := (mem_nonloopIndices.mp hmem_nl).1
    have hj_enc := graph_encode_length inp.J
    have hjle := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    omega
  have hfill_ci := hfill ci hci_lo hci_hi
  let m_fill := (pref.filter fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2)).length
  have hedges_spec := comp_edges_orig_spec hv hci_len
  have hclvl : c.1 = lvl := by
    have hidx : ci - i₀ < block.length := by omega
    have hg := hget_blk (ci - i₀) hidx
    rw [show i₀ + (ci - i₀) = ci by omega] at hg
    dsimp only [c]; rw [List.getElem!_eq_getElem?_getD, hg]
    exact hlvl_blk block[ci - i₀] (List.getElem_mem hidx)
  have hm_fill_lt : m_fill < (inp.cJSub c).m := by
    have hed_eq : edges = DecomposeOutput.edgesAt inp.J0_strip inp.decomp c.1 := by
      dsimp only [edges]; rw [hclvl]
    have hm_eq_c : (inp.cJSub c).m =
        ((DecomposeOutput.edgesAt inp.J0_strip inp.decomp c.1).filter fun q =>
          decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2)).length := hedges_spec.2.1
    have heq' : edges = pref ++ b :: bs := heq
    rw [hm_eq_c, ← hed_eq, heq', List.filter_append, List.filter_cons]
    have hdec_b : decide ((inp.J0_strip.edges.getD b (0, 0)).1 ∈ c.2) = true := by
      simpa [u, e, decide_eq_true_eq] using he1_c2
    simp only [hdec_b, ↓reduceIte, List.length_append, List.length_cons]
    dsimp only [m_fill]
    omega
  have hc_mem : c ∈ inp.rawComps := by dsimp only [c]; rw [hc_eq]; exact List.getElem_mem hci_len
  have hmc_lt : (inp.cJSub c).m < 2 ^ w := by
    have hmm : (inp.cJSub c).m ∈ inp.rawComps.map fun p => (inp.cJSub p).m :=
      List.mem_map.mpr ⟨c, hc_mem, rfl⟩
    have := List.single_le_sum (fun x _ => Nat.zero_le x) _ hmm
    omega
  have hc2_lt : c.2.length < 2 ^ w := by
    have hm2 : 2 + c.2.length ∈ inp.rawComps.map fun p => 2 + p.2.length :=
      List.mem_map.mpr ⟨c, hc_mem, rfl⟩
    have := List.single_le_sum (fun x _ => Nat.zero_le x) _ hm2
    omega
  have ha_end_lt : inp.aComps + 7 * inp.rawComps.length < 2 ^ w := by
    simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]
    omega
  have hsucc_eq : inp.cJSubPtr (ci + 1) = inp.cEndPtr ci := inp.cJSubPtr_succ hci_len
  have hsucc_le : inp.cJSubPtr (ci + 1) ≤ inp.hEnd := inp.cJSubPtr_le_hEnd (by omega)
  have hsucc_lt : inp.cJSubPtr (ci + 1) < 2 ^ w := by omega
  have hc_eq_getD : inp.rawComps.getD ci (0, []) = c := rawComps_getD_eq_getBang _ hci_len
  have hptr_eqs :
      inp.cJOrigPtr ci = inp.cJSubPtr ci + 2 + 2 * (inp.cJSub c).m ∧
      inp.cDegPtr ci = inp.cJOrigPtr ci + (inp.cJSub c).m ∧
      inp.cJSubPtr (ci + 1) = inp.cDegPtr ci + c.2.length := by
    rw [hsucc_eq]
    dsimp only [PrepInput.cEndPtr, PrepInput.cDegPtr, PrepInput.cJOrigPtr]
    rw [hc_eq_getD]; refine ⟨rfl, rfl, rfl⟩
  have hptr_lt : inp.cJSubPtr ci < 2 ^ w := by omega
  have horigptr_lt : inp.cJOrigPtr ci < 2 ^ w := by omega
  have hdegptr_lt : inp.cDegPtr ci < 2 ^ w := by omega
  have hjsub_edge_addr_lt : inp.cJSubPtr ci + 2 + 2 * m_fill + 1 < 2 ^ w := by omega
  have hjsub_edge_base_lt : inp.cJSubPtr ci + 2 + 2 * m_fill < 2 ^ w := by omega
  have hjsub_2_lt : inp.cJSubPtr ci + 2 < 2 ^ w := by omega
  have h2mfill_lt : 2 * m_fill < 2 ^ w := by omega
  have horig_write_lt : inp.cJOrigPtr ci + m_fill < 2 ^ w := by omega
  have hdeg_u_addr_lt : inp.cDegPtr ci + u' < 2 ^ w := by omega
  have hdeg_v_addr_lt : inp.cDegPtr ci + v' < 2 ^ w := by omega
  have hmfill1_lt : m_fill + 1 < 2 ^ w := by omega
  have hm_fill_lt_w : m_fill < 2 ^ w := by omega
  have hu'_lt_w : u' < 2 ^ w := by omega
  have hv'_lt_w : v' < 2 ^ w := by omega
  have hb_lt_w : b < 2 ^ w := by omega
  have haen_base_lt_w : inp.aEdgeNext < 2 ^ w := by
    simp only [PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
  have hnl_base_lt_w : inp.nlAddr < 2 ^ w := by
    have := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have h2_lt_w : 2 < 2 ^ w := by omega
  have h6_lt_w : 6 < 2 ^ w := by omega
  have ha7_lt : inp.aComps + 7 * ci < 2 ^ w := by omega
  have ha76_lt : inp.aComps + 7 * ci + 6 < 2 ^ w := by omega
  have hnl_addr_lt : inp.nlAddr + b < 2 ^ w := by
    have := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have hne_nl1 : inp.nlAddr + b ≠ inp.cJSubPtr ci + 2 + 2 * m_fill + 1 := by
    have := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hbs : inp.h ≤ inp.hBlocksStart := by
      rw [inp.hBlocksStart_eq]
      simp only [PrepInput.aVLoc, PrepInput.aVComp, PrepInput.aComps, PrepInput.aJ0Out,
        PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
    have := inp.cJSubPtr_zero ▸ inp.cJSubPtr_mono (Nat.zero_le ci)
    omega
  have hne_nl0 : inp.nlAddr + b ≠ inp.cJSubPtr ci + 2 + 2 * m_fill := by
    have := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hbs : inp.h ≤ inp.hBlocksStart := by
      rw [inp.hBlocksStart_eq]
      simp only [PrepInput.aVLoc, PrepInput.aVComp, PrepInput.aComps, PrepInput.aJ0Out,
        PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
    have := inp.cJSubPtr_zero ▸ inp.cJSubPtr_mono (Nat.zero_le ci)
    omega
  have hpref_len_le : pref.length + 1 ≤ inp.J0_strip.m := by
    have hl1 : pref.length + (b :: bs).length = edges.length := by rw [← List.length_append, ← heq]
    have hl2 : edges.length ≤ inp.J0_strip.m := by
      simpa [edges, DecomposeOutput.edgesAt] using
        List.length_filter_le (fun j => decide (inp.decomp.level j = lvl)) (List.range inp.J0_strip.m)
    simp at hl1; omega
  have hdu_val : s.mem (inp.cDegPtr ci + u') =
      ((pref.filter fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2)).filter
        fun q => decide (c.2.idxOf (inp.J0_strip.edges.getD q (0, 0)).1 = u')).length +
      ((pref.filter fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2)).filter
        fun q => decide (c.2.idxOf (inp.J0_strip.edges.getD q (0, 0)).2 = u')).length :=
    hfill_ci.2.2.2.2.2.2.2.2.2.2 u' hu'_lt
  have hdv_val : s.mem (inp.cDegPtr ci + v') =
      ((pref.filter fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2)).filter
        fun q => decide (c.2.idxOf (inp.J0_strip.edges.getD q (0, 0)).1 = v')).length +
      ((pref.filter fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2)).filter
        fun q => decide (c.2.idxOf (inp.J0_strip.edges.getD q (0, 0)).2 = v')).length :=
    hfill_ci.2.2.2.2.2.2.2.2.2.2 v' hv'_lt
  have hdu_le : s.mem (inp.cDegPtr ci + u') ≤ 2 * pref.length := by
    rw [hdu_val]
    have h1 := List.length_filter_le
      (fun q => decide (c.2.idxOf (inp.J0_strip.edges.getD q (0, 0)).1 = u'))
      (pref.filter fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2))
    have h2 := List.length_filter_le
      (fun q => decide (c.2.idxOf (inp.J0_strip.edges.getD q (0, 0)).2 = u'))
      (pref.filter fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2))
    have h3 := List.length_filter_le
      (fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2)) pref
    omega
  have hdv_le : s.mem (inp.cDegPtr ci + v') ≤ 2 * pref.length := by
    rw [hdv_val]
    have h1 := List.length_filter_le
      (fun q => decide (c.2.idxOf (inp.J0_strip.edges.getD q (0, 0)).1 = v'))
      (pref.filter fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2))
    have h2 := List.length_filter_le
      (fun q => decide (c.2.idxOf (inp.J0_strip.edges.getD q (0, 0)).2 = v'))
      (pref.filter fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2))
    have h3 := List.length_filter_le
      (fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2)) pref
    omega
  have hdu1_lt : s.mem (inp.cDegPtr ci + u') + 1 < 2 ^ w := by omega
  have hdu2_lt : s.mem (inp.cDegPtr ci + u') + 2 < 2 ^ w := by omega
  have hdv1_lt : s.mem (inp.cDegPtr ci + v') + 1 < 2 ^ w := by omega
  have haen_lt : inp.aEdgeNext + b < 2 ^ w := by
    simp only [PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
  have hnext_lt : s.mem (inp.aEdgeNext + b) < 2 ^ w := by
    cases h_bs : bs with
    | nil =>
      rw [h_bs, ChainAt.eq_1] at hch_tail
      rw [hch_tail]; exact lt_trans Nat.zero_lt_one hw1
    | cons b' bs' =>
      rw [h_bs, ChainAt.eq_2] at hch_tail
      have hb'_m : b' < inp.J0_strip.m := by
        have hmem : b' ∈ edges := by dsimp only [edges]; rw [heq, h_bs]; simp
        simp only [edges, DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hmem
        exact hmem.1
      rw [hch_tail.1]; omega
  let m4 := prepFillM4 s.mem inp ci m_fill u' v' b
  let d_u := s.mem (inp.cDegPtr ci + u')
  let m5 := Function.update m4 (inp.cDegPtr ci + u') (d_u + 1)
  let d_v_mid := m5 (inp.cDegPtr ci + v')
  let m6 := prepFillM6 s.mem inp ci m_fill u' v' b
  have hm4_agree_deg : ∀ z, inp.cDegPtr ci ≤ z → z < inp.cJSubPtr (ci + 1) → m4 z = s.mem z := by
    intro z hz1 hz2
    have hbs : inp.aComps + 7 * inp.rawComps.length ≤ inp.hBlocksStart := by
      rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
    have := inp.cJSubPtr_zero ▸ inp.cJSubPtr_mono (Nat.zero_le ci)
    have hne1 : z ≠ inp.aComps + 7 * ci + 6 := by omega
    have hne2 : z ≠ inp.cJOrigPtr ci + m_fill := by omega
    have hne3 : z ≠ inp.cJSubPtr ci + 2 + 2 * m_fill + 1 := by omega
    have hne4 : z ≠ inp.cJSubPtr ci + 2 + 2 * m_fill := by omega
    dsimp only [m4, prepFillM4]
    rw [Function.update_of_ne hne1, Function.update_of_ne hne2,
      Function.update_of_ne hne3, Function.update_of_ne hne4]
  have hm4_du : m4 (inp.cDegPtr ci + u') = d_u := hm4_agree_deg _ (by omega) (by omega)
  have hm4_dv : m4 (inp.cDegPtr ci + v') = s.mem (inp.cDegPtr ci + v') :=
    hm4_agree_deg _ (by omega) (by omega)
  have hdvmid_lt : d_v_mid + 1 < 2 ^ w := by
    dsimp only [d_v_mid, m5]
    by_cases huv : inp.cDegPtr ci + v' = inp.cDegPtr ci + u'
    · rw [huv, Function.update_self]; omega
    · rw [Function.update_of_ne huv, hm4_dv]; omega
  have hm6_aen : m6 (inp.aEdgeNext + b) = s.mem (inp.aEdgeNext + b) := by
    have hbs : inp.aComps + 7 * inp.rawComps.length ≤ inp.hBlocksStart := by
      rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
    have hptr0 : inp.hBlocksStart ≤ inp.cJSubPtr ci := by
      rw [← inp.cJSubPtr_zero]; exact inp.cJSubPtr_mono (Nat.zero_le ci)
    have haen_lt_ac : inp.aEdgeNext + b < inp.aComps := by
      simp only [PrepInput.aComps, PrepInput.aJ0Out]; omega
    have hac_le_cdeg : inp.cJSubPtr ci ≤ inp.cDegPtr ci := by
      simp only [PrepInput.cDegPtr, PrepInput.cJOrigPtr]; omega
    have hne_m6_1 : inp.aEdgeNext + b ≠ inp.cDegPtr ci + v' := by omega
    have hne_m6_2 : inp.aEdgeNext + b ≠ inp.cDegPtr ci + u' := by omega
    have hne_m6_3 : inp.aEdgeNext + b ≠ inp.aComps + 7 * ci + 6 := by omega
    have hne_m6_4 : inp.aEdgeNext + b ≠ inp.cJOrigPtr ci + m_fill := by omega
    have hne_m6_5 : inp.aEdgeNext + b ≠ inp.cJSubPtr ci + 2 + 2 * m_fill + 1 := by omega
    have hne_m6_6 : inp.aEdgeNext + b ≠ inp.cJSubPtr ci + 2 + 2 * m_fill := by omega
    dsimp only [m6, prepFillM6, m4, prepFillM4]
    rw [Function.update_of_ne hne_m6_1, Function.update_of_ne hne_m6_2,
      Function.update_of_ne hne_m6_3, Function.update_of_ne hne_m6_4,
      Function.update_of_ne hne_m6_5, Function.update_of_ne hne_m6_6]
  have h_stage3 :
      ∀ {k : ℕ}, k + 33 ≤ 155 → ∀ s17 : State,
        s17.mem = m4 →
        PrepFullRegs inp s17 →
        s17.regs 16 = inp.cJSubPtr i₁ →
        s17.regs 17 = i₀ →
        s17.regs 20 = b →
        s17.regs 22 = i₁ →
        s17.regs 23 = lvl →
        s17.regs 25 = u' →
        s17.regs 28 = inp.cDegPtr ci →
        s17.regs 30 = v' →
        ∃ o st' c_cost,
          Runs w p ω
            ((Stmt.assign 21 (Expr.bin BinOp.add (Expr.reg 28) (Expr.reg 25)).load).seq
              ((Stmt.store (Expr.bin BinOp.add (Expr.reg 28) (Expr.reg 25))
                (Expr.bin BinOp.add (Expr.reg 21) (Expr.const 1))).seq
              ((Stmt.assign 21 (Expr.bin BinOp.add (Expr.reg 28) (Expr.reg 30)).load).seq
              ((Stmt.store (Expr.bin BinOp.add (Expr.reg 28) (Expr.reg 30))
                (Expr.bin BinOp.add (Expr.reg 21) (Expr.const 1))).seq
              (Stmt.assign 29 (Expr.bin BinOp.add (Expr.reg 10) (Expr.reg 20)).load)))))
            s17 o st' c_cost ∧
          (match o with
           | Outcome.returned u => False
           | Outcome.normal => PrepFillInv inp mem₀ i₀ lvl block bs st') ∧
          k + c_cost ≤ 155 := by
    intro k hk ⟨m_17, rg_17, pos_17⟩ hm17 hf17 h16_17 h17_17 h20_17 h22_17 h23_17 h25_17 h28_17 h30_17
    rw [state_mem_mk] at hm17; subst hm17
    refine runs_seq_assign_flat (v := d_u)
      (ev_load (ev_add (ev_reg h28_17 hdegptr_lt) (ev_reg h25_17 hu'_lt_w) hdeg_u_addr_lt)
        hm4_du (Nat.lt_of_succ_lt hdu1_lt)) ?_
    refine runs_seq_store_flat (x := inp.cDegPtr ci + u') (v := d_u + 1)
      (ev_add (ev_reg (by rw [state_regs_mk, Function.update_of_ne (by decide)]; exact h28_17) hdegptr_lt)
        (ev_reg (by rw [state_regs_mk, Function.update_of_ne (by decide)]; exact h25_17) hu'_lt_w) hdeg_u_addr_lt)
      (ev_add (ev_reg (by rw [state_regs_mk]; exact Function.update_self _ _ _) (Nat.lt_of_succ_lt hdu1_lt)) (ev_const hw1) hdu1_lt) ?_
    refine runs_seq_assign_flat (v := d_v_mid)
      (ev_load (ev_add (ev_reg (by rw [state_regs_mk, Function.update_of_ne (by decide)]; exact h28_17) hdegptr_lt)
        (ev_reg (by rw [state_regs_mk, Function.update_of_ne (by decide)]; exact h30_17) hv'_lt_w) hdeg_v_addr_lt)
        (by rw [state_mem_mk]) (Nat.lt_of_succ_lt hdvmid_lt)) ?_
    refine runs_seq_store_flat (x := inp.cDegPtr ci + v') (v := d_v_mid + 1)
      (ev_add (ev_reg (by rw [state_regs_mk, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h28_17) hdegptr_lt)
        (ev_reg (by rw [state_regs_mk, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h30_17) hv'_lt_w) hdeg_v_addr_lt)
      (ev_add (ev_reg (by rw [state_regs_mk]; exact Function.update_self _ _ _) (Nat.lt_of_succ_lt hdvmid_lt)) (ev_const hw1) hdvmid_lt) ?_
    let rg21 := Function.update (Function.update rg_17 21 d_u) 21 d_v_mid
    let s22 : State := ⟨m6, Function.update rg21 29 (s.mem (inp.aEdgeNext + b)), pos_17⟩
    have hm21 : m6 (inp.aEdgeNext + b) = s.mem (inp.aEdgeNext + b) := hm6_aen
    have hev_last : (Expr.bin BinOp.add (Expr.reg 10) (Expr.reg 20)).load.eval w
        ⟨m6, rg21, pos_17⟩ = some (s.mem (inp.aEdgeNext + b)) :=
      ev_load (ev_add
        (ev_reg (by rw [state_regs_mk]; dsimp only [rg21]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
                    exact hf17.1.2.2.2.2.2.2.2.2.2.2.1) haen_base_lt_w)
        (ev_reg (by rw [state_regs_mk]; dsimp only [rg21]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
                    exact h20_17) hb_lt_w) haen_lt)
        (by rw [state_mem_mk]; exact hm21) hnext_lt
    have hs22_inv : PrepFillInv inp mem₀ i₀ lvl block bs s22 := by
      refine prepFill_fin_inv inp mem₀ hv hcb heq hch_tail hst hdone hparsed hvm hzf hfill
        hci_len hci_lo hci_hi he1_ci he2_ci huniq rfl
        (prepFullRegs_congr hf17 fun r hr => by
          dsimp only [s22, rg21]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)])
        (by dsimp only [s22, rg21]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h16_17)
        (by dsimp only [s22, rg21]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h17_17)
        (by dsimp only [s22, rg21]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h22_17)
        (by dsimp only [s22, rg21]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h23_17)
        (by dsimp only [s22]; exact Function.update_self _ _ _)
    refine ⟨.normal, s22, (Expr.bin BinOp.add (Expr.reg 10) (Expr.reg 20)).load.size + 1,
      runs_assign_iff.mpr ⟨_, hev_last, rfl, rfl, rfl⟩, hs22_inv, ?_⟩
    · norm_num [Expr.size]
      omega
  have h_stage2 :
      ∀ {k : ℕ}, k + 72 ≤ 155 → ∀ s11 : State,
        s11.mem = s.mem →
        PrepFullRegs inp s11 →
        s11.regs 16 = inp.cJSubPtr i₁ →
        s11.regs 17 = i₀ →
        s11.regs 19 = m_fill →
        s11.regs 20 = b →
        s11.regs 22 = i₁ →
        s11.regs 23 = lvl →
        s11.regs 25 = u' →
        s11.regs 26 = inp.cJSubPtr ci →
        s11.regs 27 = inp.cJOrigPtr ci →
        s11.regs 28 = inp.cDegPtr ci →
        s11.regs 30 = v' →
        s11.regs 31 = inp.aComps + 7 * ci →
        ∃ o st' c_cost,
          Runs w p ω
            ((Stmt.assign 21 (Expr.bin BinOp.add (Expr.bin BinOp.add (Expr.reg 26) (Expr.const 2))
              (Expr.bin BinOp.mul (Expr.const 2) (Expr.reg 19)))).seq
            ((Stmt.store (Expr.reg 21) (Expr.reg 25)).seq
            ((Stmt.store (Expr.bin BinOp.add (Expr.reg 21) (Expr.const 1)) (Expr.reg 30)).seq
            ((Stmt.assign 21 (Expr.bin BinOp.add (Expr.reg 2) (Expr.reg 20)).load).seq
            ((Stmt.store (Expr.bin BinOp.add (Expr.reg 27) (Expr.reg 19)) (Expr.reg 21)).seq
            ((Stmt.store (Expr.bin BinOp.add (Expr.reg 31) (Expr.const 6))
              (Expr.bin BinOp.add (Expr.reg 19) (Expr.const 1))).seq
            ((Stmt.assign 21 (Expr.bin BinOp.add (Expr.reg 28) (Expr.reg 25)).load).seq
            ((Stmt.store (Expr.bin BinOp.add (Expr.reg 28) (Expr.reg 25))
              (Expr.bin BinOp.add (Expr.reg 21) (Expr.const 1))).seq
            ((Stmt.assign 21 (Expr.bin BinOp.add (Expr.reg 28) (Expr.reg 30)).load).seq
            ((Stmt.store (Expr.bin BinOp.add (Expr.reg 28) (Expr.reg 30))
              (Expr.bin BinOp.add (Expr.reg 21) (Expr.const 1))).seq
            (Stmt.assign 29 (Expr.bin BinOp.add (Expr.reg 10) (Expr.reg 20)).load)))))))))))
            s11 o st' c_cost ∧
          (match o with
           | Outcome.returned u => False
           | Outcome.normal => PrepFillInv inp mem₀ i₀ lvl block bs st') ∧
          k + c_cost ≤ 155 := by
    intro k hk ⟨m_11, rg_11, pos_11⟩ hm11 hf11 h16_11 h17_11 h19_11 h20_11 h22_11 h23_11 h25_11 h26_11
      h27_11 h28_11 h30_11 h31_11
    rw [state_mem_mk] at hm11; subst hm11
    refine runs_seq_assign_flat (v := inp.cJSubPtr ci + 2 + 2 * m_fill)
      (ev_add (ev_add (ev_reg h26_11 hptr_lt) (ev_const h2_lt_w) hjsub_2_lt)
        (ev_mul (ev_const h2_lt_w) (ev_reg h19_11 hm_fill_lt_w) h2mfill_lt) hjsub_edge_base_lt) ?_
    refine runs_seq_store_flat (x := inp.cJSubPtr ci + 2 + 2 * m_fill) (v := u')
      (ev_reg (by rw [state_regs_mk]; exact Function.update_self _ _ _) hjsub_edge_base_lt)
      (ev_reg (by rw [state_regs_mk, Function.update_of_ne (by decide)]; exact h25_11) hu'_lt_w) ?_
    refine runs_seq_store_flat (x := inp.cJSubPtr ci + 2 + 2 * m_fill + 1) (v := v')
      (ev_add (ev_reg (by rw [state_regs_mk]; exact Function.update_self _ _ _) hjsub_edge_base_lt) (ev_const hw1) hjsub_edge_addr_lt)
      (ev_reg (by rw [state_regs_mk, Function.update_of_ne (by decide)]; exact h30_11) hv'_lt_w) ?_
    refine runs_seq_assign_flat (v := inp.nlIdx.getD b 0)
      (ev_load (ev_add (ev_reg (by rw [state_regs_mk, Function.update_of_ne (by decide)]; exact hf11.1.2.2.1) hnl_base_lt_w)
        (ev_reg (by rw [state_regs_mk, Function.update_of_ne (by decide)]; exact h20_11) hb_lt_w) hnl_addr_lt)
        (by rw [state_mem_mk, Function.update_of_ne hne_nl1, Function.update_of_ne hne_nl0]
            exact horig_val) horig_lt) ?_
    refine runs_seq_store_flat (x := inp.cJOrigPtr ci + m_fill) (v := inp.nlIdx.getD b 0)
      (ev_add (ev_reg (by rw [state_regs_mk, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h27_11) horigptr_lt)
        (ev_reg (by rw [state_regs_mk, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h19_11) hm_fill_lt_w) horig_write_lt)
      (ev_reg (by rw [state_regs_mk]; exact Function.update_self _ _ _) horig_lt) ?_
    refine runs_seq_store_flat (x := inp.aComps + 7 * ci + 6) (v := m_fill + 1)
      (ev_add (ev_reg (by rw [state_regs_mk, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h31_11) ha7_lt) (ev_const h6_lt_w) ha76_lt)
      (ev_add (ev_reg (by rw [state_regs_mk, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h19_11) hm_fill_lt_w) (ev_const hw1) hmfill1_lt) ?_
    let rg17 := Function.update (Function.update rg_11 21 (inp.cJSubPtr ci + 2 + 2 * m_fill))
      21 (inp.nlIdx.getD b 0)
    let s17 : State := ⟨m4, rg17, pos_11⟩
    have hk39 : k + 39 + 33 ≤ 155 := by omega
    have hs17_res := h_stage3 (k := k + 39) hk39 s17 rfl
      (prepFullRegs_congr hf11 fun r hr => by
        dsimp only [s17, rg17]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
      (by dsimp only [s17, rg17]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h16_11)
      (by dsimp only [s17, rg17]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h17_11)
      (by dsimp only [s17, rg17]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h20_11)
      (by dsimp only [s17, rg17]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h22_11)
      (by dsimp only [s17, rg17]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h23_11)
      (by dsimp only [s17, rg17]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h25_11)
      (by dsimp only [s17, rg17]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h28_11)
      (by dsimp only [s17, rg17]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h30_11)
    rcases hs17_res with ⟨o', st', c', hruns', hpost', hcost'⟩
    refine ⟨o', st', c', hruns', hpost', ?_⟩
    · norm_num [Expr.size]
      omega
  have ha7_lt : inp.aComps + 7 * ci < 2 ^ w := by omega
  have ha73_lt : inp.aComps + 7 * ci + 3 < 2 ^ w := by omega
  have ha74_lt : inp.aComps + 7 * ci + 4 < 2 ^ w := by omega
  have ha75_lt : inp.aComps + 7 * ci + 5 < 2 ^ w := by omega
  have ha76_lt : inp.aComps + 7 * ci + 6 < 2 ^ w := by omega
  have h7ci_lt : 7 * ci < 2 ^ w := by omega
  have hci1_lt : ci + 1 < 2 ^ w := by omega
  have hj02_lt : inp.j0Addr + 2 < 2 ^ w := by
    have := graph_encode_length inp.J0_strip
    have := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have hj03_lt : inp.j0Addr + 3 < 2 ^ w := by
    have := graph_encode_length inp.J0_strip
    have := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have h2b_lt : 2 * b < 2 ^ w := by omega
  have hj02b_lt : inp.j0Addr + 2 + 2 * b < 2 ^ w := by
    have := graph_encode_length inp.J0_strip
    have := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have hj03b_lt : inp.j0Addr + 3 + 2 * b < 2 ^ w := by
    have := graph_encode_length inp.J0_strip
    have := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have hbs_lt : inp.hBlocksStart < 2 ^ w := by
    have : inp.hBlocksStart ≤ inp.hEnd := by simp [PrepInput.hEnd]
    omega
  have hu_lt_n : u < inp.J.n := he1_n
  have hv_lt_n : v < inp.J.n := he2_n
  have hvc_lt : inp.aVComp + u < 2 ^ w := by
    have hbseq := inp.hBlocksStart_eq
    simp only [PrepInput.aVLoc] at hbseq
    omega
  have hvl_u_lt : inp.aVLoc + u < 2 ^ w := by
    have hbseq := inp.hBlocksStart_eq
    omega
  have hvl_v_lt : inp.aVLoc + v < 2 ^ w := by
    have hbseq := inp.hBlocksStart_eq
    omega
  have hmfill_cur := hfill_ci.2.2.2.2.2.2.1
  have hptr_cur := hfill_ci.2.2.2.1
  have horig_cur := hfill_ci.2.2.2.2.1
  have hdeg_cur := hfill_ci.2.2.2.2.2.1
  dsimp only [prepFillBody]
  refine runs_seq_assign0 (v := b)
    (by simpa using ev_sub (ev_reg h29 hb1_lt) (ev_const hw1) (by omega) (by omega)) ?_
  refine runs_seq_assign_flat (v := u)
    (ev_load (ev_add (ev_add (ev_reg (by simp [hf.1.2.1]) (by omega)) (ev_const (by omega)) hj02_lt)
      (ev_mul (ev_const (by omega)) (ev_reg (by simp) (by omega)) h2b_lt) hj02b_lt)
      (by rw [state_mem_mk]; exact he1_val) (by omega)) ?_
  refine runs_seq_assign_flat (v := v)
    (ev_load (ev_add (ev_add (ev_reg (by simp [hf.1.2.1]) (by omega)) (ev_const (by omega)) hj03_lt)
      (ev_mul (ev_const (by omega)) (ev_reg (by simp) (by omega)) h2b_lt) hj03b_lt)
      (by rw [state_mem_mk]; exact he2_val) (by omega)) ?_
  refine runs_seq_assign_flat (v := ci + 1)
    (ev_load (ev_add (ev_reg (by simp [hf.2.2.2.1]) (by omega)) (ev_reg (by simp) (by omega)) hvc_lt)
      (by rw [state_mem_mk]; exact hvc_u) hci1_lt) ?_
  refine runs_seq_assign_flat (v := inp.aComps + 7 * ci)
    (ev_add (ev_reg (by simp [hf.2.2.1]) (by omega))
      (ev_mul (ev_const (by omega))
        (by simpa using ev_sub (ev_reg (by simp) hci1_lt) (ev_const hw1) (by omega) (by omega)) h7ci_lt)
      ha7_lt) ?_
  refine runs_seq_assign_flat (v := u')
    (ev_load (ev_add (ev_reg (by simp [hf.2.2.2.2]) (by omega)) (ev_reg (by simp) (by omega)) hvl_u_lt)
      (by rw [state_mem_mk]; exact hvl_u) (by omega)) ?_
  refine runs_seq_assign_flat (v := v')
    (ev_load (ev_add (ev_reg (by simp [hf.2.2.2.2]) (by omega)) (ev_reg (by simp) (by omega)) hvl_v_lt)
      (by rw [state_mem_mk]; exact hvl_v) (by omega)) ?_
  refine runs_seq_assign_flat (v := inp.cJSubPtr ci)
    (ev_load (ev_add (ev_reg (by simp) ha7_lt) (ev_const (by omega)) ha73_lt)
      (by rw [state_mem_mk]; exact hptr_cur) hptr_lt) ?_
  refine runs_seq_assign_flat (v := inp.cJOrigPtr ci)
    (ev_load (ev_add (ev_reg (by simp) ha7_lt) (ev_const (by omega)) ha74_lt)
      (by rw [state_mem_mk]; exact horig_cur) horigptr_lt) ?_
  refine runs_seq_assign_flat (v := inp.cDegPtr ci)
    (ev_load (ev_add (ev_reg (by simp) ha7_lt) (ev_const (by omega)) ha75_lt)
      (by rw [state_mem_mk]; exact hdeg_cur) hdegptr_lt) ?_
  refine runs_seq_assign_flat (v := m_fill)
    (ev_load (ev_add (ev_reg (by simp) ha7_lt) (ev_const (by omega)) ha76_lt)
      (by rw [state_mem_mk]; exact hmfill_cur) (by omega)) ?_
  let r11 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update s.regs 20 b) 19 u) 21 v) 30 (ci + 1)) 31 (inp.aComps + 7 * ci))
    25 u') 30 v') 26 (inp.cJSubPtr ci)) 27 (inp.cJOrigPtr ci)) 28 (inp.cDegPtr ci)) 19 m_fill
  let s11 : State := ⟨s.mem, r11, s.pos⟩
  have hs11_res := h_stage2 (k := 78) (by omega) s11 rfl
    (prepFullRegs_congr hf fun r hr => by
      dsimp only [s11, r11]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)])
    (by dsimp only [s11, r11]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact h16)
    (by dsimp only [s11, r11]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact h17)
    (by dsimp only [s11, r11]; rw [Function.update_self])
    (by dsimp only [s11, r11]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_self])
    (by dsimp only [s11, r11]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact h22)
    (by dsimp only [s11, r11]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact h23)
    (by dsimp only [s11, r11]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_self])
    (by dsimp only [s11, r11]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_self])
    (by dsimp only [s11, r11]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_self])
    (by dsimp only [s11, r11]
        rw [Function.update_of_ne (by decide), Function.update_self])
    (by dsimp only [s11, r11]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_self])
    (by dsimp only [s11, r11]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_self])
  rcases hs11_res with ⟨o', st', c', hruns', hpost', hcost'⟩
  refine ⟨o', st', c', ?_, hpost', ?_⟩
  · exact hruns'
  · norm_num [Expr.size]
    omega

/-- Verification of `prepFillStmt`: populates `J_sub`, `jSubOrigEdges`, and `deg` for every
component in the current level block `[i₀, i₁)` by traversing the level bucket chain once. -/
theorem prepFill_triple {w : ℕ} {p : Program} (inp : PrepInput) (mem₀ : ℕ → ℕ)
    (hv : inp.Valid mem₀ w)
    {done rest : List (ℕ × ℕ × List (ℕ × List ℕ))} {i₀ lvl : ℕ} {block : List (ℕ × List ℕ)}
    (hcb : compBlocksAux 0 inp.rawComps = done ++ (i₀, lvl, block) :: rest) :
    let i₁ := i₀ + block.length
    let edges := DecomposeOutput.edgesAt inp.J0_strip inp.decomp lvl
    Triple w p
      (fun st =>
        PrepFullRegs inp st ∧
        st.regs 16 = inp.cJSubPtr i₁ ∧
        st.regs 17 = i₀ ∧
        st.regs 22 = i₁ ∧
        st.regs 23 = lvl ∧
        PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem i₀ ∧
        CompsParsedFrom inp st.mem i₁ ∧
        VertMarksBlock inp st.mem i₀ i₁ ∧
        ZeroFrom st.mem (inp.cJSubPtr i₁) ∧
        (∀ k, i₀ ≤ k → k < i₁ →
          let c := inp.rawComps[k]!
          st.mem (inp.aComps + 7 * k) = c.1 ∧
          st.mem (inp.aComps + 7 * k + 1) = c.2.length ∧
          st.mem (inp.aComps + 7 * k + 2) = inp.cVertsPtr k ∧
          st.mem (inp.aComps + 7 * k + 3) = inp.cJSubPtr k ∧
          st.mem (inp.aComps + 7 * k + 4) = inp.cJOrigPtr k ∧
          st.mem (inp.aComps + 7 * k + 5) = inp.cDegPtr k ∧
          st.mem (inp.aComps + 7 * k + 6) = 0 ∧
          st.mem (inp.cJSubPtr k) = c.2.length ∧
          st.mem (inp.cJSubPtr k + 1) = (inp.cJSub c).m ∧
          (∀ x, inp.cJSubPtr k + 2 ≤ x → x < inp.cJSubPtr (k + 1) → st.mem x = 0)))
      prepFillStmt
      (normalPost fun st =>
        PrepFullRegs inp st ∧
        st.regs 16 = inp.cJSubPtr i₁ ∧
        st.regs 17 = i₀ ∧
        st.regs 22 = i₁ ∧
        st.regs 23 = lvl ∧
        PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem i₁ ∧
        CompsParsedFrom inp st.mem i₁ ∧
        VertMarksBlock inp st.mem i₀ i₁ ∧
        ZeroFrom st.mem (inp.cJSubPtr i₁))
      (fun _ => 165 * edges.length + 20) := by
  have hsz := inp.size_bounds hv
  have hw1 := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwb := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hpw_rc := hv.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨_, _, hle, hlvl_blk, hget_blk, _, _⟩ := compBlocksAux_split_spec hpw_rc hcb
  obtain ⟨hlvl1, hlvl2⟩ := block_lvl_bounds hv hcb
  intro i₁ edges st₀ ω₀ ⟨hf0, h16_0, h17_0, h22_0, h23_0, hst0, hdone0, hparsed0, hvm0, hzf0, hblk0⟩
  have hchain0 : ChainAt st₀.mem inp.aEdgeNext (st₀.mem (inp.aLvlHead + lvl)) edges :=
    hst0.2.2.2.2.2.2.2.2.2.2 lvl hlvl2
  have hptr0_lt : st₀.mem (inp.aLvlHead + lvl) < 2 ^ w := by
    cases h_ed : edges with
    | nil =>
      rw [h_ed, ChainAt.eq_1] at hchain0
      rw [hchain0]; exact lt_trans Nat.zero_lt_one hw1
    | cons b bs =>
      rw [h_ed, ChainAt.eq_2] at hchain0
      have hb_m : b < inp.J0_strip.m := by
        have hmem : b ∈ edges := by rw [h_ed]; exact List.mem_cons_self
        simp only [edges, DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hmem
        exact hmem.1
      rw [hchain0.1]; omega
  have hahead_lt : inp.aLvlHead + lvl < 2 ^ w := by
    simp only [PrepInput.aLvlHead]; omega
  have hloop :
      Triple w p (PrepFillInv inp mem₀ i₀ lvl block edges)
        (Stmt.loop (Expr.bin BinOp.lt (Expr.const 0) (Expr.reg 29)) prepFillBody)
        (normalPost fun st =>
          PrepFullRegs inp st ∧
          st.regs 16 = inp.cJSubPtr i₁ ∧
          st.regs 17 = i₀ ∧
          st.regs 22 = i₁ ∧
          st.regs 23 = lvl ∧
          PrepStaticState inp mem₀ st.mem ∧
          CompsDoneUpTo inp st.mem i₁ ∧
          CompsParsedFrom inp st.mem i₁ ∧
          VertMarksBlock inp st.mem i₀ i₁ ∧
          ZeroFrom st.mem (inp.cJSubPtr i₁))
        (fun _ => (edges.map (fun _ : ℕ => 155)).sum +
          edges.length * ((Expr.bin BinOp.lt (Expr.const 0) (Expr.reg 29)).size + 1) +
          (Expr.bin BinOp.lt (Expr.const 0) (Expr.reg 29)).size + 1) := by
    refine Triple.loop_list (Inv := PrepFillInv inp mem₀ i₀ lvl block) (fun _ => 155) ?_ ?_ edges
    · intro st hinv
      dsimp only [PrepFillInv] at hinv
      rcases hinv with ⟨pref, heq, hf, h16, h17, h22, h23, hch, hst, hdone, hparsed, hvm, hzf, hfill⟩
      rw [ChainAt.eq_1] at hch
      have h_ev : (Expr.bin BinOp.lt (Expr.const 0) (Expr.reg 29)).eval w st = some 0 :=
        ev_lt_f (ev_const (by omega)) (ev_reg hch (by omega)) (by omega) hw1
      have hpref_eq : pref = edges := by simpa using heq.symm
      have hpref_edges : pref = DecomposeOutput.edgesAt inp.J0_strip inp.decomp lvl := hpref_eq
      have hdone_ext : CompsDoneUpTo inp st.mem i₁ := by
        intro k hk
        by_cases hk_i0 : k < i₀
        · exact hdone k hk_i0
        · have hk_len : k < inp.rawComps.length := by omega
          have hprops_k := comp_props_at hv hk_len
          have hed_spec := comp_edges_orig_spec hv hk_len
          have hclvl : inp.rawComps[k]!.1 = lvl := by
            have hidx : k - i₀ < block.length := by omega
            have hg := hget_blk (k - i₀) hidx
            rw [show i₀ + (k - i₀) = k by omega] at hg
            rw [List.getElem!_eq_getElem?_getD, hg]
            exact hlvl_blk block[k - i₀] (List.getElem_mem hidx)
          rcases hfill k (by omega) hk with ⟨ht0, ht1, ht2, ht3, ht4, ht5, ht6, hgn, hgm, hge, hdeg⟩
          have hpf_len : (pref.filter fun q =>
              decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ inp.rawComps[k]!.2)).length =
              (inp.cJSub inp.rawComps[k]!).m := by
            rw [hpref_eq, hed_spec.2.1, hclvl]
          refine ⟨ht0, ht1, ht2, ht3, ht4, ht5, ht6.trans hpf_len, ?_, ?_, ?_⟩
          · refine graphAt_of_cells (hgn.trans hprops_k.2.2.2.2.2.2.1.symm) hgm ?_
            intro j hj
            have hj' : j < (pref.filter fun q =>
                decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ inp.rawComps[k]!.2)).length := by
              omega
            rcases hge j hj' with ⟨hfst, hsnd, _⟩
            have he_eq := hed_spec.1
            rw [hclvl, ← hpref_edges] at he_eq
            have hget_edge : (inp.cJSub inp.rawComps[k]!).edges[j]'hj =
                ((inp.rawComps[k]!).2.idxOf
                  (inp.J0_strip.edges.getD (pref.filter fun q =>
                    decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ inp.rawComps[k]!.2))[j] (0, 0)).1,
                 (inp.rawComps[k]!).2.idxOf
                  (inp.J0_strip.edges.getD (pref.filter fun q =>
                    decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ inp.rawComps[k]!.2))[j] (0, 0)).2) := by
              simp only [he_eq, List.getElem_map]
            rw [hget_edge]
            exact ⟨hfst, hsnd⟩
          · have hor_eq := hed_spec.2.2.1
            rw [hclvl, ← hpref_edges] at hor_eq
            rw [hor_eq]
            intro j hj
            simp only [List.length_map] at hj
            have hor := (hge j hj).2.2
            simpa only [List.getElem_map] using hor
          · intro z hz
            simp only [List.length_map, List.length_range] at hz
            have hget_z := hdeg z hz
            have hrange_elem : ((List.range inp.rawComps[k]!.2.length).map
                (inp.cJSub inp.rawComps[k]!).deg)[z]'(by simp only [List.length_map, List.length_range]; exact hz) =
                (inp.cJSub inp.rawComps[k]!).deg z := by simp
            rw [hrange_elem, deg_eq_filter_edges hprops_k.2.2.2.2.2.2.2 z]
            have he_eq := hed_spec.1
            rw [hclvl, ← hpref_edges] at he_eq
            rw [he_eq, List.filter_map, List.length_map, List.filter_map, List.length_map]
            simpa [Function.comp_apply] using hget_z
      exact ⟨h_ev, hf, h16, h17, h22, h23, hst, hdone_ext, hparsed, hvm, hzf⟩
    · intro b bs st hinv
      exact prepFill_step inp mem₀ hv hcb hinv
  dsimp only [prepFillStmt]
  refine runs_seq_assign0 (v := st₀.mem (inp.aLvlHead + lvl))
    (ev_load (ev_add (ev_reg hf0.1.2.2.2.2.2.2.2.2.2.1 (by omega))
      (ev_reg h23_0 (by omega)) hahead_lt) rfl hptr0_lt) ?_
  have hinv0 : PrepFillInv inp mem₀ i₀ lvl block edges { st₀ with regs := Function.update st₀.regs 29 (st₀.mem (inp.aLvlHead + lvl)) } := by
    dsimp only [PrepFillInv]
    refine ⟨[], by dsimp only [edges]; simp,
      prepFullRegs_congr hf0 (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]),
      by rw [Function.update_of_ne (by decide)]; exact h16_0,
      by rw [Function.update_of_ne (by decide)]; exact h17_0,
      by rw [Function.update_of_ne (by decide)]; exact h22_0,
      by rw [Function.update_of_ne (by decide)]; exact h23_0,
      by simpa using hchain0,
      hst0, hdone0, hparsed0, hvm0, hzf0, ?_⟩
    intro k hk1 hk2
    have hbk := hblk0 k hk1 hk2
    refine ⟨hbk.1, hbk.2.1, hbk.2.2.1, hbk.2.2.2.1, hbk.2.2.2.2.1, hbk.2.2.2.2.2.1,
      by simp [hbk.2.2.2.2.2.2.1], hbk.2.2.2.2.2.2.2.1, hbk.2.2.2.2.2.2.2.2.1,
      fun j hj => by simp at hj,
      fun z hz => by
        simp only [List.filter_nil, List.length_nil, Nat.add_zero]
        exact hbk.2.2.2.2.2.2.2.2.2 (inp.cDegPtr k + z)
          (by dsimp only [PrepInput.cDegPtr, PrepInput.cJOrigPtr]; omega)
          (by have hk_len : k < inp.rawComps.length := by omega
              rw [inp.cJSubPtr_succ hk_len]
              dsimp only [PrepInput.cEndPtr, PrepInput.cDegPtr, PrepInput.cJOrigPtr]
              rw [rawComps_getD_eq_getBang _ hk_len]; omega)⟩
  rcases hloop _ ω₀ hinv0 with ⟨o, st', c_cost, hruns, hpost, hcost⟩
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    refine ⟨.normal, st', c_cost, hruns, hpost, ?_⟩
    norm_num [Expr.size] at hcost ⊢
    omega

end MinCostFlow.Spanner
