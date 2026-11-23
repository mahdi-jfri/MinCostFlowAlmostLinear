module

public import MinCostFlow.Spanner.ProgWitnessPrepBlockHelpers

/-!
# Verification of `prepCountStmt` and `prepAllocStmt`

Proves Hoare triples for counting edges per component in a level block and allocating/zero-filling
the induced subgraph, original-edge map, and degree arrays.
-/

public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-- Verification of `prepCountStmt`: scans the level bucket chain once and increments each
component's subgraph edge counter at `aComps + 7*k + 6`. -/
theorem prepCount_triple {w : ℕ} {p : Program} (inp : PrepInput) (mem₀ : ℕ → ℕ)
    (hv : inp.Valid mem₀ w)
    {done rest : List (ℕ × ℕ × List (ℕ × List ℕ))} {i₀ lvl : ℕ} {block : List (ℕ × List ℕ)}
    (hcb : compBlocksAux 0 inp.rawComps = done ++ (i₀, lvl, block) :: rest) :
    let i₁ := i₀ + block.length
    let edges := DecomposeOutput.edgesAt inp.J0_strip inp.decomp lvl
    Triple w p
      (fun st =>
        PrepFullRegs inp st ∧
        st.regs 16 = inp.cJSubPtr i₀ ∧
        st.regs 17 = i₀ ∧
        st.regs 22 = i₁ ∧
        st.regs 23 = lvl ∧
        PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem i₀ ∧
        CompsParsedFrom inp st.mem i₀ ∧
        VertMarksBlock inp st.mem i₀ i₁ ∧
        ZeroFrom st.mem (inp.cJSubPtr i₀))
      prepCountStmt
      (normalPost fun st =>
        PrepFullRegs inp st ∧
        st.regs 16 = inp.cJSubPtr i₀ ∧
        st.regs 17 = i₀ ∧
        st.regs 22 = i₁ ∧
        st.regs 23 = lvl ∧
        PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem i₀ ∧
        CompsParsedFrom inp st.mem i₁ ∧
        VertMarksBlock inp st.mem i₀ i₁ ∧
        ZeroFrom st.mem (inp.cJSubPtr i₀) ∧
        (∀ k, i₀ ≤ k → k < i₁ →
          let c := inp.rawComps[k]!
          st.mem (inp.aComps + 7 * k) = c.1 ∧
          st.mem (inp.aComps + 7 * k + 1) = c.2.length ∧
          st.mem (inp.aComps + 7 * k + 2) = inp.cVertsPtr k ∧
          st.mem (inp.aComps + 7 * k + 3) = 0 ∧
          st.mem (inp.aComps + 7 * k + 4) = 0 ∧
          st.mem (inp.aComps + 7 * k + 5) = 0 ∧
          st.mem (inp.aComps + 7 * k + 6) = (inp.cJSub c).m))
      (fun _ => 60 * edges.length + 20) := by
  have hsz := inp.size_bounds hv
  have hw1 := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwb := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hpw_rc := hv.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨_, _, hle, hlvl_blk, hget_blk, _, _⟩ := compBlocksAux_split_spec hpw_rc hcb
  obtain ⟨hlvl1, hlvl2⟩ := block_lvl_bounds hv hcb
  intro i₁ edges st₀ ω₀ ⟨hf0, h16_0, h17_0, h22_0, h23_0, hst0, hdone0, hparsed0, hvm0, hzf0⟩
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
    simp only [PrepInput.aLvlHead] at *; omega
  let Inv : List ℕ → State → Prop := fun rem st =>
    ∃ pref : List ℕ,
      edges = pref ++ rem ∧
      PrepFullRegs inp st ∧
      st.regs 16 = inp.cJSubPtr i₀ ∧
      st.regs 17 = i₀ ∧
      st.regs 22 = i₁ ∧
      st.regs 23 = lvl ∧
      ChainAt st.mem inp.aEdgeNext (st.regs 29) rem ∧
      PrepStaticState inp mem₀ st.mem ∧
      CompsDoneUpTo inp st.mem i₀ ∧
      CompsParsedFrom inp st.mem i₁ ∧
      VertMarksBlock inp st.mem i₀ i₁ ∧
      ZeroFrom st.mem (inp.cJSubPtr i₀) ∧
      (∀ k, i₀ ≤ k → k < i₁ →
        let c := inp.rawComps[k]!
        st.mem (inp.aComps + 7 * k) = c.1 ∧
        st.mem (inp.aComps + 7 * k + 1) = c.2.length ∧
        st.mem (inp.aComps + 7 * k + 2) = inp.cVertsPtr k ∧
        st.mem (inp.aComps + 7 * k + 3) = 0 ∧
        st.mem (inp.aComps + 7 * k + 4) = 0 ∧
        st.mem (inp.aComps + 7 * k + 5) = 0 ∧
        st.mem (inp.aComps + 7 * k + 6) =
          (pref.filter fun b => decide ((inp.J0_strip.edges.getD b (0, 0)).1 ∈ c.2)).length)
  have hloop :
      Triple w p (Inv edges)
        (Stmt.loop (Expr.bin BinOp.lt (Expr.const 0) (Expr.reg 29)) prepCountBody)
        (normalPost fun st =>
          PrepFullRegs inp st ∧
          st.regs 16 = inp.cJSubPtr i₀ ∧
          st.regs 17 = i₀ ∧
          st.regs 22 = i₁ ∧
          st.regs 23 = lvl ∧
          PrepStaticState inp mem₀ st.mem ∧
          CompsDoneUpTo inp st.mem i₀ ∧
          CompsParsedFrom inp st.mem i₁ ∧
          VertMarksBlock inp st.mem i₀ i₁ ∧
          ZeroFrom st.mem (inp.cJSubPtr i₀) ∧
          ∀ k, i₀ ≤ k → k < i₁ →
            let c := inp.rawComps[k]!
            st.mem (inp.aComps + 7 * k) = c.1 ∧
            st.mem (inp.aComps + 7 * k + 1) = c.2.length ∧
            st.mem (inp.aComps + 7 * k + 2) = inp.cVertsPtr k ∧
            st.mem (inp.aComps + 7 * k + 3) = 0 ∧
            st.mem (inp.aComps + 7 * k + 4) = 0 ∧
            st.mem (inp.aComps + 7 * k + 5) = 0 ∧
            st.mem (inp.aComps + 7 * k + 6) = (inp.cJSub c).m)
        (fun _ => (edges.map (fun _ : ℕ => 54)).sum +
          edges.length * ((Expr.bin BinOp.lt (Expr.const 0) (Expr.reg 29)).size + 1) +
          (Expr.bin BinOp.lt (Expr.const 0) (Expr.reg 29)).size + 1) := by
    refine Triple.loop_list (Inv := Inv) (fun _ => 54) ?_ ?_ edges
    · intro st ⟨pref, heq, hf, h16, h17, h22, h23, hch, hst, hdone, hparsed, hvm, hzf, hk⟩
      rw [ChainAt.eq_1] at hch
      have h_ev : (Expr.bin BinOp.lt (Expr.const 0) (Expr.reg 29)).eval w st = some 0 :=
        ev_lt_f (ev_const (by omega)) (ev_reg hch (by omega)) (by omega) hw1
      refine ⟨h_ev, hf, h16, h17, h22, h23, hst, hdone, hparsed, hvm, hzf, ?_⟩
      intro k hk1 hk2
      rcases hk k hk1 hk2 with ⟨h0, h1, h2, h3, h4, h5, h6⟩
      refine ⟨h0, h1, h2, h3, h4, h5, ?_⟩
      have hpref_eq : pref = edges := by simpa using heq.symm
      rw [hpref_eq] at h6
      have hsub_len : inp.rawComps[k]!.1 = lvl := by
        have hidx : k - i₀ < block.length := by omega
        have hg := hget_blk (k - i₀) hidx
        rw [show i₀ + (k - i₀) = k by omega] at hg
        rw [List.getElem!_eq_getElem?_getD, hg]
        exact hlvl_blk block[k - i₀] (List.getElem_mem hidx)
      have hm_eq := (comp_edges_orig_spec hv (by omega : k < inp.rawComps.length)).2.1
      rw [h6, hm_eq, hsub_len]
    · intro b bs st ⟨pref, heq, hf, h16, h17, h22, h23, hch, hst, hdone, hparsed, hvm, hzf, hk⟩
      rw [ChainAt.eq_2] at hch
      rcases hch with ⟨h29, hch_tail⟩
      have hb_mem : b ∈ edges := by rw [heq]; simp
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
        ⟨ci, hci_len, hci_lo, hci_hi, he1_ci, _, huniq, he1_n, _⟩
      set u := (inp.J0_strip.edges.getD b (0, 0)).1
      obtain ⟨p, hp_lt, hp_eq⟩ := List.mem_iff_getElem.mp he1_ci
      have hvc_u : s.mem (inp.aVComp + u) = ci + 1 := by
        rw [← hp_eq]; exact (hvm.1 ci hci_len hci_lo hci_hi p hp_lt).1
      have hgJ0 : GraphAt s.mem inp.j0Addr inp.J0_strip :=
        GraphAt.of_agree_below hv.2.2.2.1 hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hst.1
      have he1_val : s.mem (inp.j0Addr + 2 + 2 * b) = u := by
        have hget := graphAt_edge_fst hgJ0 hb_m
        dsimp only [u]
        rw [List.getD_eq_getElem _ _ (by simpa [Graph.m] using hb_m)]
        exact hget
      have h2b_lt : 2 * b < 2 ^ w := by
        have := graph_encode_length inp.J0_strip
        have := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        omega
      have hj02b_lt : inp.j0Addr + 2 + 2 * b < 2 ^ w := by
        have := graph_encode_length inp.J0_strip
        have := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        omega
      have hj02_lt : inp.j0Addr + 2 < 2 ^ w := by omega
      have hvc_lt : inp.aVComp + u < 2 ^ w := by
        simp only [PrepInput.aVComp, PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext,
          PrepInput.aLvlHead]; omega
      have ha7_lt : inp.aComps + 7 * ci < 2 ^ w := by
        simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]
        omega
      have ha76_lt : inp.aComps + 7 * ci + 6 < 2 ^ w := by
        simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]
        omega
      have h7ci_lt : 7 * ci < 2 ^ w := by omega
      have hci1_lt : ci + 1 < 2 ^ w := by omega
      have hcnt_cur := hk ci hci_lo hci_hi
      set cnt := (pref.filter fun q =>
        decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ inp.rawComps[ci]!.2)).length
      have hcnt_le : cnt ≤ inp.J0_strip.m := by
        have hlen1 : cnt ≤ pref.length := List.length_filter_le _ _
        have hlen2 : pref.length + (b :: bs).length = edges.length := by
          rw [← List.length_append, ← heq]
        have hlen3 : edges.length ≤ inp.J0_strip.m := by
          have := List.length_filter_le
            (fun j => decide (inp.decomp.level j = lvl)) (List.range inp.J0_strip.m)
          simpa [edges, DecomposeOutput.edgesAt] using this
        omega
      have hcnt1_lt : cnt + 1 < 2 ^ w := by omega
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
            have hmem : b' ∈ edges := by rw [heq, h_bs]; simp
            simp only [edges, DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hmem
            exact hmem.1
          rw [hch_tail.1]; omega
      dsimp only [prepCountBody]
      refine runs_seq_assign0 (v := b)
        (by simpa using ev_sub (ev_reg h29 hb1_lt) (ev_const hw1) (by omega) (by omega)) ?_
      refine runs_seq_assign_le (v := u)
        (ev_load (ev_add (ev_add (ev_reg (by simp [hf.1.2.1]) (by omega)) (ev_const (by omega)) hj02_lt)
          (ev_mul (ev_const (by omega)) (ev_reg (by simp) (by omega)) h2b_lt) hj02b_lt)
          (by simpa using he1_val) (by omega)) ?_
      refine runs_seq_assign_le (v := ci + 1)
        (ev_load (ev_add (ev_reg (by simp [hf.2.2.2.1]) (by omega)) (ev_reg (by simp) (by omega)) hvc_lt)
          (by simpa using hvc_u) hci1_lt) ?_
      refine runs_seq_assign_le (v := ci)
        (by simpa using ev_sub (ev_reg (by simp) hci1_lt) (ev_const hw1) (by omega) (by omega)) ?_
      refine runs_seq_assign_le (v := inp.aComps + 7 * ci + 6)
        (ev_add (ev_add (ev_reg (by simp [hf.2.2.1]) (by omega))
          (ev_mul (ev_const (by omega)) (ev_reg (by simp) (by omega)) h7ci_lt) ha7_lt)
          (ev_const (by omega)) ha76_lt) ?_
      refine runs_seq_assign_le (v := cnt)
        (ev_load (ev_reg (by simp) ha76_lt) (by simpa [cnt] using hcnt_cur.2.2.2.2.2.2) (by omega)) ?_
      refine runs_seq_store_le (x := inp.aComps + 7 * ci + 6) (v := cnt + 1)
        (ev_reg (by simp) ha76_lt)
        (ev_add (ev_reg (by simp) (by omega)) (ev_const hw1) hcnt1_lt) ?_
      have hne_next : inp.aEdgeNext + b ≠ inp.aComps + 7 * ci + 6 := by
        simp only [PrepInput.aComps, PrepInput.aJ0Out]; omega
      have hev_next : (Expr.bin BinOp.add (Expr.reg 10) (Expr.reg 20)).load.eval w
          { mem := Function.update s.mem (inp.aComps + 7 * ci + 6) (cnt + 1),
            regs := Function.update (Function.update (Function.update (Function.update
              (Function.update (Function.update s.regs 20 b) 19 u) 30 (ci + 1)) 31 ci)
              26 (inp.aComps + 7 * ci + 6)) 27 cnt,
            pos := s.pos } = some (s.mem (inp.aEdgeNext + b)) :=
        ev_load (ev_add (ev_reg (by simp [hf.1.2.2.2.2.2.2.2.2.2.2.1]) (by omega))
          (ev_reg (by simp) (by omega)) haen_lt)
          (by dsimp only; rw [Function.update_of_ne hne_next]) hnext_lt
      refine ⟨.normal, _, _,
        runs_assign_iff.mpr ⟨_, hev_next, rfl, rfl, rfl⟩, ?_,
        by norm_num [Expr.size]⟩
      set m' := Function.update s.mem (inp.aComps + 7 * ci + 6) (cnt + 1)
      have hag_m' : ∀ x, x ≠ inp.aComps + 7 * ci + 6 → m' x = s.mem x :=
        fun x hx => by dsimp only [m']; rw [Function.update_of_ne hx]
      have hchain_bs : ChainAt m' inp.aEdgeNext (s.mem (inp.aEdgeNext + b)) bs :=
        chainAt_of_agree hch_tail fun q hq => by
          have hq_ed : q ∈ edges := by rw [heq]; simp [hq]
          simp only [edges, DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hq_ed
          have hqm := hq_ed.1
          exact hag_m' _ (by simp only [PrepInput.aComps, PrepInput.aJ0Out]; omega)
      refine ⟨pref ++ [b], by simpa [List.append_assoc] using heq,
        prepFullRegs_congr hf (fun r hr => by
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]),
        by simp [h16], by simp [h17], by simp [h22], by simp [h23],
        by simpa using hchain_bs,
        prepStaticState_of_agree hst (fun x hx => hag_m' x (by omega)),
        compsDoneUpTo_of_agree hv (by omega) hdone
          (fun x hx1 hx2 => hag_m' x (by omega))
          (fun x hx1 hx2 => hag_m' x (by
            have := inp.cJSubPtr_zero ▸ inp.cJSubPtr_mono (Nat.zero_le 0)
            rw [inp.hBlocksStart_eq] at hx1
            simp only [PrepInput.aVLoc, PrepInput.aVComp] at hx1; omega)),
        compsParsedFrom_of_agree hparsed (fun x hx1 hx2 => hag_m' x (by omega)),
        ?_,
        fun x hx => (hag_m' x (by
          have := inp.cJSubPtr_zero ▸ inp.cJSubPtr_mono (Nat.zero_le i₀)
          rw [inp.hBlocksStart_eq] at this
          simp only [PrepInput.aVLoc, PrepInput.aVComp] at this; omega)).trans (hzf x hx),
        ?_⟩
      · refine ⟨?_, fun hci1' => by omega, ?_⟩
        · intro cj hcj hcj1 hcj2 p hp
          have hvc_ne : inp.aVComp + inp.rawComps[cj].2[p] ≠ inp.aComps + 7 * ci + 6 := by
            simp only [PrepInput.aVComp]; omega
          have hvl_ne : inp.aVLoc + inp.rawComps[cj].2[p] ≠ inp.aComps + 7 * ci + 6 := by
            simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
          have hprev := hvm.1 cj hcj hcj1 hcj2 p hp
          exact ⟨(hag_m' _ hvc_ne).trans hprev.1, (hag_m' _ hvl_ne).trans hprev.2⟩
        · intro u' hu' hnot_prev _
          have hvc_ne : inp.aVComp + u' ≠ inp.aComps + 7 * ci + 6 := by
            simp only [PrepInput.aVComp]; omega
          have hvl_ne : inp.aVLoc + u' ≠ inp.aComps + 7 * ci + 6 := by
            simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
          have hprev := hvm.2.2 u' hu' hnot_prev (fun hci' => by omega)
          exact ⟨(hag_m' _ hvc_ne).trans hprev.1, (hag_m' _ hvl_ne).trans hprev.2⟩
      · intro k hk1 hk2
        have hkp := hk k hk1 hk2
        have hoff_ne : ∀ off < 6, inp.aComps + 7 * k + off ≠ inp.aComps + 7 * ci + 6 := by
          intro off hoff; omega
        refine ⟨(hag_m' _ (hoff_ne 0 (by omega))).trans hkp.1,
          (hag_m' _ (hoff_ne 1 (by omega))).trans hkp.2.1,
          (hag_m' _ (hoff_ne 2 (by omega))).trans hkp.2.2.1,
          (hag_m' _ (hoff_ne 3 (by omega))).trans hkp.2.2.2.1,
          (hag_m' _ (hoff_ne 4 (by omega))).trans hkp.2.2.2.2.1,
          (hag_m' _ (hoff_ne 5 (by omega))).trans hkp.2.2.2.2.2.1,
          ?_⟩
        by_cases hkc : k = ci
        · subst hkc
          have hdec : decide ((inp.J0_strip.edges.getD b (0, 0)).1 ∈ inp.rawComps[k]!.2) = true := by
            simp only [decide_eq_true_eq]
            rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hci_len]
            exact he1_ci
          simp only [m', Function.update_self, List.filter_append, List.filter_cons,
            List.filter_nil, hdec, ↓reduceIte, List.length_append, List.length_singleton]
          rfl
        · have hnot_mem : (inp.J0_strip.edges.getD b (0, 0)).1 ∉ inp.rawComps[k]!.2 := by
            intro hmem
            rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k < inp.rawComps.length)] at hmem
            exact hkc (huniq k (by omega) hk1 hk2 hmem)
          have hdec : decide ((inp.J0_strip.edges.getD b (0, 0)).1 ∈ inp.rawComps[k]!.2) = false := by
            simpa using hnot_mem
          have hne6 : inp.aComps + 7 * k + 6 ≠ inp.aComps + 7 * ci + 6 := by omega
          simp only [hag_m' _ hne6, hkp.2.2.2.2.2.2, List.filter_append, List.filter_cons,
            List.filter_nil, hdec, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  dsimp only [prepCountStmt]
  refine runs_seq_assign0 (v := st₀.mem (inp.aLvlHead + lvl))
    (ev_load (ev_add (ev_reg hf0.1.2.2.2.2.2.2.2.2.2.1 (by omega))
      (ev_reg h23_0 (by omega)) hahead_lt) rfl hptr0_lt) ?_
  have hinv0 : Inv edges { st₀ with regs := Function.update st₀.regs 29 (st₀.mem (inp.aLvlHead + lvl)) } := by
    refine ⟨[], by simp,
      prepFullRegs_congr hf0 (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]),
      by simp [h16_0], by simp [h17_0], by simp [h22_0], by simp [h23_0],
      by simpa using hchain0,
      hst0, hdone0,
      fun k hk1 hk2 => hparsed0 k (by omega) hk2,
      hvm0, hzf0, ?_⟩
    intro k hk1 hk2
    have hpk := hparsed0 k hk1 (by omega)
    exact ⟨hpk.1, hpk.2.1, hpk.2.2.1, hpk.2.2.2.1, hpk.2.2.2.2.1, hpk.2.2.2.2.2.1,
      by simp [hpk.2.2.2.2.2.2]⟩
  rcases hloop _ ω₀ hinv0 with ⟨o, st', c, hruns, hpost, hcost⟩
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    refine ⟨.normal, st', c, hruns, hpost, ?_⟩
    norm_num [Expr.size] at hcost ⊢
    omega

/-- Verification of `prepAllocStmt`: initializes component subgraph headers (`n`, `m`), zero-fills
edge/origin/degree slices, and records heap slice pointers in `[i₀, i₁)`. -/
theorem prepAlloc_triple {w : ℕ} {p : Program} (inp : PrepInput) (mem₀ : ℕ → ℕ)
    (hv : inp.Valid mem₀ w)
    {done rest : List (ℕ × ℕ × List (ℕ × List ℕ))} {i₀ lvl : ℕ} {block : List (ℕ × List ℕ)}
    (hcb : compBlocksAux 0 inp.rawComps = done ++ (i₀, lvl, block) :: rest) :
    let i₁ := i₀ + block.length
    Triple w p
      (fun st =>
        PrepFullRegs inp st ∧
        st.regs 16 = inp.cJSubPtr i₀ ∧
        st.regs 17 = i₀ ∧
        st.regs 22 = i₁ ∧
        st.regs 23 = lvl ∧
        PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem i₀ ∧
        CompsParsedFrom inp st.mem i₁ ∧
        VertMarksBlock inp st.mem i₀ i₁ ∧
        ZeroFrom st.mem (inp.cJSubPtr i₀) ∧
        (∀ k, i₀ ≤ k → k < i₁ →
          let c := inp.rawComps[k]!
          st.mem (inp.aComps + 7 * k) = c.1 ∧
          st.mem (inp.aComps + 7 * k + 1) = c.2.length ∧
          st.mem (inp.aComps + 7 * k + 2) = inp.cVertsPtr k ∧
          st.mem (inp.aComps + 7 * k + 3) = 0 ∧
          st.mem (inp.aComps + 7 * k + 4) = 0 ∧
          st.mem (inp.aComps + 7 * k + 5) = 0 ∧
          st.mem (inp.aComps + 7 * k + 6) = (inp.cJSub c).m))
      prepAllocStmt
      (normalPost fun st =>
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
      (fun _ => 95 * block.length + 10) := by
  have hsz := inp.size_bounds hv
  have hw1 := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwb := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hpw_rc := hv.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨_, _, hle, _, _, _, _⟩ := compBlocksAux_split_spec hpw_rc hcb
  intro i₁
  let Inv : ℕ → State → Prop := fun ci st =>
    PrepFullRegs inp st ∧
    st.regs 16 = inp.cJSubPtr ci ∧
    st.regs 17 = i₀ ∧
    st.regs 22 = i₁ ∧
    st.regs 23 = lvl ∧
    st.regs 24 = ci ∧
    PrepStaticState inp mem₀ st.mem ∧
    CompsDoneUpTo inp st.mem i₀ ∧
    CompsParsedFrom inp st.mem i₁ ∧
    VertMarksBlock inp st.mem i₀ i₁ ∧
    ZeroFrom st.mem (inp.cJSubPtr ci) ∧
    (∀ k, i₀ ≤ k → k < ci →
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
      (∀ x, inp.cJSubPtr k + 2 ≤ x → x < inp.cJSubPtr (k + 1) → st.mem x = 0)) ∧
    (∀ k, ci ≤ k → k < i₁ →
      let c := inp.rawComps[k]!
      st.mem (inp.aComps + 7 * k) = c.1 ∧
      st.mem (inp.aComps + 7 * k + 1) = c.2.length ∧
      st.mem (inp.aComps + 7 * k + 2) = inp.cVertsPtr k ∧
      st.mem (inp.aComps + 7 * k + 3) = 0 ∧
      st.mem (inp.aComps + 7 * k + 4) = 0 ∧
      st.mem (inp.aComps + 7 * k + 5) = 0 ∧
      st.mem (inp.aComps + 7 * k + 6) = (inp.cJSub c).m)
  have hfor :=
    Triple.forRange_const (w := w) (p := p) (P := fun st =>
        PrepFullRegs inp st ∧ st.regs 16 = inp.cJSubPtr i₀ ∧ st.regs 17 = i₀ ∧
        st.regs 22 = i₁ ∧ st.regs 23 = lvl ∧ PrepStaticState inp mem₀ st.mem ∧
        CompsDoneUpTo inp st.mem i₀ ∧ CompsParsedFrom inp st.mem i₁ ∧
        VertMarksBlock inp st.mem i₀ i₁ ∧ ZeroFrom st.mem (inp.cJSubPtr i₀) ∧
        (∀ k, i₀ ≤ k → k < i₁ →
          let c := inp.rawComps[k]!
          st.mem (inp.aComps + 7 * k) = c.1 ∧ st.mem (inp.aComps + 7 * k + 1) = c.2.length ∧
          st.mem (inp.aComps + 7 * k + 2) = inp.cVertsPtr k ∧ st.mem (inp.aComps + 7 * k + 3) = 0 ∧
          st.mem (inp.aComps + 7 * k + 4) = 0 ∧ st.mem (inp.aComps + 7 * k + 5) = 0 ∧
          st.mem (inp.aComps + 7 * k + 6) = (inp.cJSub c).m))
      (r := 24) (lo := Expr.reg 17) (hi := Expr.reg 22) (body := prepAllocBody)
      (Inv := Inv) 85 i₀ i₁ (Nat.le_add_right i₀ block.length) hw1 (fun _ => by omega)
      (fun st ⟨hf, h16, h17, h22, h23, hst, hdone, hparsed, hvm, hzf, hrem⟩ =>
        ⟨ev_reg h17 (by omega),
          ⟨prepFullRegs_congr hf (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]),
           by simp [h16], by simp [h17], by simp [h22], by simp [h23], by simp,
           hst, hdone, hparsed, hvm, hzf, fun _ _ _ => by omega, fun k hk1 hk2 => hrem k hk1 hk2⟩⟩)
      (fun _ _ _ _ h => h.2.2.2.2.2.1)
      (fun _ _ _ _ h => ev_reg h.2.2.2.1 (by omega))
      ?_
  · refine hfor.conseq (fun _ h => h) (fun o st' h => ?_) (fun _ _ => ?_)
    · cases o with
      | returned _ => exact h
      | normal =>
        rcases h with ⟨hf, h16, h17, h22, h23, _, hst, hdone, hparsed, hvm, hzf, hk, _⟩
        exact ⟨hf, h16, h17, h22, h23, hst, hdone, hparsed, hvm, hzf, hk⟩
    · simp only [Expr.size]; omega
  · intro ci hci_lo hci_hi st ω
      ⟨hf, h16, h17, h22, h23, h24, hst, hdone, hparsed, hvm, hzf, hk_done, hk_rem⟩
    have hci_len : ci < inp.rawComps.length := by omega
    set c := inp.rawComps[ci]!
    have hci_tab := hk_rem ci le_rfl hci_hi
    have hc_eq_getD : inp.rawComps.getD ci (0, []) = c := rawComps_getD_eq_getBang _ hci_len
    have hc_mem : c ∈ inp.rawComps := by
      have : inp.rawComps[ci]! = inp.rawComps[ci] := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hci_len]; rfl
      dsimp only [c]; rw [this]; exact List.getElem_mem hci_len
    have hc2_lt : c.2.length < 2 ^ w := by
      have hm2 : 2 + c.2.length ∈ inp.rawComps.map fun p => 2 + p.2.length :=
        List.mem_map.mpr ⟨c, hc_mem, rfl⟩
      have := List.single_le_sum (fun x _ => Nat.zero_le x) _ hm2
      omega
    have hmc_lt : (inp.cJSub c).m < 2 ^ w := by
      have hmm : (inp.cJSub c).m ∈ inp.rawComps.map fun p => (inp.cJSub p).m :=
        List.mem_map.mpr ⟨c, hc_mem, rfl⟩
      have := List.single_le_sum (fun x _ => Nat.zero_le x) _ hmm
      omega
    have hsucc_eq : inp.cJSubPtr (ci + 1) = inp.cEndPtr ci := inp.cJSubPtr_succ hci_len
    have hsucc_le : inp.cJSubPtr (ci + 1) ≤ inp.hEnd := inp.cJSubPtr_le_hEnd (by omega)
    have hsucc_lt : inp.cJSubPtr (ci + 1) < 2 ^ w := by omega
    have hptr_eqs :
        inp.cJOrigPtr ci = inp.cJSubPtr ci + 2 + 2 * (inp.cJSub c).m ∧
        inp.cDegPtr ci = inp.cJOrigPtr ci + (inp.cJSub c).m ∧
        inp.cJSubPtr (ci + 1) = inp.cDegPtr ci + c.2.length := by
      rw [hsucc_eq]
      dsimp only [PrepInput.cEndPtr, PrepInput.cDegPtr, PrepInput.cJOrigPtr]
      rw [hc_eq_getD]; refine ⟨rfl, rfl, rfl⟩
    have hptr_lt : inp.cJSubPtr ci < 2 ^ w := by omega
    have hptr1_lt : inp.cJSubPtr ci + 1 < 2 ^ w := by omega
    have hptr2_lt : inp.cJSubPtr ci + 2 < 2 ^ w := by omega
    have h2mc_lt : 2 * (inp.cJSub c).m < 2 ^ w := by omega
    have horig_lt : inp.cJOrigPtr ci < 2 ^ w := by omega
    have hdeg_lt : inp.cDegPtr ci < 2 ^ w := by omega
    have ha_end_lt : inp.aComps + 7 * inp.rawComps.length < 2 ^ w := by
      simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]
      omega
    have h7ci_lt : 7 * ci < 2 ^ w := by omega
    have ha7_lt : inp.aComps + 7 * ci < 2 ^ w := by omega
    have ha71_lt : inp.aComps + 7 * ci + 1 < 2 ^ w := by omega
    have ha73_lt : inp.aComps + 7 * ci + 3 < 2 ^ w := by omega
    have ha74_lt : inp.aComps + 7 * ci + 4 < 2 ^ w := by omega
    have ha75_lt : inp.aComps + 7 * ci + 5 < 2 ^ w := by omega
    have ha76_lt : inp.aComps + 7 * ci + 6 < 2 ^ w := by omega
    let m1 := Function.update st.mem (inp.cJSubPtr ci) c.2.length
    let m2 := Function.update m1 (inp.cJSubPtr ci + 1) (inp.cJSub c).m
    let m3 := Function.update m2 (inp.aComps + 7 * ci + 3) (inp.cJSubPtr ci)
    let m4 := Function.update m3 (inp.aComps + 7 * ci + 4) (inp.cJOrigPtr ci)
    let m5 := Function.update m4 (inp.aComps + 7 * ci + 5) (inp.cDegPtr ci)
    let m6 := Function.update m5 (inp.aComps + 7 * ci + 6) 0
    let r_fin := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update st.regs
        31 (inp.aComps + 7 * ci)) 20 c.2.length) 26 (inp.cJSub c).m)
        27 (inp.cJSubPtr ci)) 28 (inp.cJOrigPtr ci)) 30 (inp.cDegPtr ci))
        16 (inp.cJSubPtr (ci + 1))
    let s_fin : State := { mem := m6, regs := r_fin, pos := st.pos }
    have hptr_ge_bs : inp.hBlocksStart ≤ inp.cJSubPtr ci := by
      rw [← inp.cJSubPtr_zero]; exact inp.cJSubPtr_mono (Nat.zero_le ci)
    have h_m6_out : ∀ x,
        (x < inp.aComps + 7 * ci + 3 ∨
          (inp.aComps + 7 * ci + 7 ≤ x ∧ x < inp.cJSubPtr ci) ∨
          inp.cJSubPtr ci + 2 ≤ x) → m6 x = st.mem x := by
      intro x hx
      have hbs_ge : inp.aComps + 7 * inp.rawComps.length ≤ inp.hBlocksStart := by
        rw [inp.hBlocksStart_eq]
        simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
      have hne_a3 : x ≠ inp.aComps + 7 * ci + 3 := by rcases hx with h | ⟨h, _⟩ | h <;> omega
      have hne_a4 : x ≠ inp.aComps + 7 * ci + 4 := by rcases hx with h | ⟨h, _⟩ | h <;> omega
      have hne_a5 : x ≠ inp.aComps + 7 * ci + 5 := by rcases hx with h | ⟨h, _⟩ | h <;> omega
      have hne_a6 : x ≠ inp.aComps + 7 * ci + 6 := by rcases hx with h | ⟨h, _⟩ | h <;> omega
      have hne_p0 : x ≠ inp.cJSubPtr ci := by rcases hx with h | ⟨_, h⟩ | h <;> omega
      have hne_p1 : x ≠ inp.cJSubPtr ci + 1 := by rcases hx with h | ⟨_, h⟩ | h <;> omega
      dsimp only [m6, m5, m4, m3, m2, m1]
      rw [Function.update_of_ne hne_a6, Function.update_of_ne hne_a5,
        Function.update_of_ne hne_a4, Function.update_of_ne hne_a3,
        Function.update_of_ne hne_p1, Function.update_of_ne hne_p0]
    have hle_succ : inp.cJSubPtr ci + 2 ≤ inp.cJSubPtr (ci + 1) := by omega
    have hs_fin : Inv (ci + 1) { s_fin with regs := Function.update s_fin.regs 24 (ci + 1) } ∧
        s_fin.regs 24 = ci := by
      refine ⟨⟨?_, by dsimp only [s_fin, r_fin]; simp, by dsimp only [s_fin, r_fin]; simp [h17],
        by dsimp only [s_fin, r_fin]; simp [h22], by dsimp only [s_fin, r_fin]; simp [h23],
        by simp,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by dsimp only [s_fin, r_fin]; simp [h24]⟩
      · exact prepFullRegs_congr hf fun r hr => by
          dsimp only [s_fin, r_fin]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · exact prepStaticState_of_agree hst fun x hx =>
          h_m6_out x (Or.inl (by omega))
      · refine compsDoneUpTo_of_agree hv (by omega) hdone
          (fun x hx1 hx2 => h_m6_out x (Or.inl (by omega)))
          (fun x hx1 hx2 => h_m6_out x (Or.inr (Or.inl ⟨by
            have : inp.aComps + 7 * inp.rawComps.length ≤ inp.hBlocksStart := by
              rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
            omega, by
            have := inp.cJSubPtr_mono hci_lo
            omega⟩)))
      · exact compsParsedFrom_of_agree hparsed fun x hx1 hx2 =>
          h_m6_out x (Or.inr (Or.inl ⟨by omega, by
            have : inp.aComps + 7 * inp.rawComps.length ≤ inp.hBlocksStart := by
              rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
            omega⟩))
      · refine ⟨?_, fun hci1' => by omega, ?_⟩
        · intro cj hcj hcj1 hcj2 p hp
          have hcj_eq : inp.rawComps[cj]! = inp.rawComps[cj] := by
            rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hcj]; rfl
          have hvc_gt : inp.aComps + 7 * ci + 7 ≤ inp.aVComp + inp.rawComps[cj].2[p] ∧
              inp.aVComp + inp.rawComps[cj].2[p] < inp.cJSubPtr ci := by
            have hu_n := (comp_props_at hv hcj).2.2.2.2.2.1 _ (by rw [hcj_eq]; exact List.getElem_mem hp)
            have hblk_s : inp.aComps + 7 * inp.rawComps.length + inp.J.n + inp.J.n = inp.hBlocksStart := by
              rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]
            simp only [PrepInput.aVComp]
            omega
          have hvl_gt : inp.aComps + 7 * ci + 7 ≤ inp.aVLoc + inp.rawComps[cj].2[p] ∧
              inp.aVLoc + inp.rawComps[cj].2[p] < inp.cJSubPtr ci := by
            have hu_n := (comp_props_at hv hcj).2.2.2.2.2.1 _ (by rw [hcj_eq]; exact List.getElem_mem hp)
            have hblk_s : inp.aComps + 7 * inp.rawComps.length + inp.J.n + inp.J.n = inp.hBlocksStart := by
              rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]
            simp only [PrepInput.aVLoc, PrepInput.aVComp]
            omega
          have hprev := hvm.1 cj hcj hcj1 hcj2 p hp
          exact ⟨(h_m6_out _ (Or.inr (Or.inl hvc_gt))).trans hprev.1,
            (h_m6_out _ (Or.inr (Or.inl hvl_gt))).trans hprev.2⟩
        · intro u' hu' hnot_prev _
          have hvc_gt : inp.aComps + 7 * ci + 7 ≤ inp.aVComp + u' ∧
              inp.aVComp + u' < inp.cJSubPtr ci := by
            have : inp.aVComp + inp.J.n ≤ inp.hBlocksStart := by
              rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc]; omega
            simp only [PrepInput.aVComp] at *; omega
          have hvl_gt : inp.aComps + 7 * ci + 7 ≤ inp.aVLoc + u' ∧
              inp.aVLoc + u' < inp.cJSubPtr ci := by
            have : inp.aVLoc + inp.J.n = inp.hBlocksStart := inp.hBlocksStart_eq.symm
            simp only [PrepInput.aVLoc, PrepInput.aVComp] at *; omega
          have hprev := hvm.2.2 u' hu' hnot_prev (fun hci' => by omega)
          exact ⟨(h_m6_out _ (Or.inr (Or.inl hvc_gt))).trans hprev.1,
            (h_m6_out _ (Or.inr (Or.inl hvl_gt))).trans hprev.2⟩
      · intro x hx
        exact (h_m6_out x (Or.inr (Or.inr (by omega)))).trans (hzf x (by omega))
      · intro k hk1 hk2
        by_cases hkc : k = ci
        · subst hkc
          have hge : inp.aComps + 7 * k + 7 ≤ inp.cJSubPtr k := by
            have : inp.aComps + 7 * inp.rawComps.length ≤ inp.hBlocksStart := by
              rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
            omega
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · dsimp only [s_fin]; rw [h_m6_out _ (Or.inl (by omega))]; exact hci_tab.1
          · dsimp only [s_fin]; rw [h_m6_out _ (Or.inl (by omega))]; exact hci_tab.2.1
          · dsimp only [s_fin]; rw [h_m6_out _ (Or.inl (by omega))]; exact hci_tab.2.2.1
          · dsimp only [s_fin, m6, m5, m4, m3]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_self]
          · dsimp only [s_fin, m6, m5, m4]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_self]
          · dsimp only [s_fin, m6, m5]
            rw [Function.update_of_ne (by omega), Function.update_self]
          · dsimp only [s_fin, m6]; rw [Function.update_self]
          · dsimp only [s_fin, m6, m5, m4, m3, m2, m1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_self]
          · dsimp only [s_fin, m6, m5, m4, m3, m2]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_self]
          · intro x hx1 hx2
            exact (h_m6_out x (Or.inr (Or.inr hx1))).trans (hzf x (by omega))
        · have hkp := hk_done k hk1 (by omega)
          have hlt_a : ∀ off < 7, inp.aComps + 7 * k + off < inp.aComps + 7 * ci + 3 :=
            fun _ _ => by omega
          have hblk_lt : inp.cJSubPtr (k + 1) ≤ inp.cJSubPtr ci := inp.cJSubPtr_mono (by omega)
          have hblk_le : inp.cJSubPtr k < inp.aComps + 7 * ci + 3 ∨
              inp.aComps + 7 * ci + 7 ≤ inp.cJSubPtr k ∧ inp.cJSubPtr k < inp.cJSubPtr ci := by
            right; constructor
            · have : inp.aComps + 7 * inp.rawComps.length ≤ inp.hBlocksStart := by
                rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
              have := inp.cJSubPtr_zero ▸ inp.cJSubPtr_mono (Nat.zero_le k)
              omega
            · have : 2 ≤ (inp.cEndPtr k) - inp.cJSubPtr k := by
                dsimp only [PrepInput.cEndPtr, PrepInput.cDegPtr, PrepInput.cJOrigPtr]; omega
              have := inp.cJSubPtr_succ (by omega : k < inp.rawComps.length)
              omega
          refine ⟨(h_m6_out _ (Or.inl (hlt_a 0 (by omega)))).trans hkp.1,
            (h_m6_out _ (Or.inl (hlt_a 1 (by omega)))).trans hkp.2.1,
            (h_m6_out _ (Or.inl (hlt_a 2 (by omega)))).trans hkp.2.2.1,
            (h_m6_out _ (Or.inl (hlt_a 3 (by omega)))).trans hkp.2.2.2.1,
            (h_m6_out _ (Or.inl (hlt_a 4 (by omega)))).trans hkp.2.2.2.2.1,
            (h_m6_out _ (Or.inl (hlt_a 5 (by omega)))).trans hkp.2.2.2.2.2.1,
            (h_m6_out _ (Or.inl (hlt_a 6 (by omega)))).trans hkp.2.2.2.2.2.2.1,
            (h_m6_out _ (by rcases hblk_le with h | h; exact Or.inl h; exact Or.inr (Or.inl h))).trans
              hkp.2.2.2.2.2.2.2.1,
            (h_m6_out _ (by
              right; left; constructor
              · have : inp.aComps + 7 * inp.rawComps.length ≤ inp.hBlocksStart := by
                  rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
                have := inp.cJSubPtr_zero ▸ inp.cJSubPtr_mono (Nat.zero_le k)
                omega
              · have := inp.cJSubPtr_succ (by omega : k < inp.rawComps.length)
                dsimp only [PrepInput.cEndPtr, PrepInput.cDegPtr, PrepInput.cJOrigPtr] at hblk_lt this ⊢
                omega)).trans hkp.2.2.2.2.2.2.2.2.1,
            fun x hx1 hx2 => (h_m6_out x (by
              right; left; constructor
              · have : inp.aComps + 7 * inp.rawComps.length ≤ inp.hBlocksStart := by
                  rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
                have := inp.cJSubPtr_zero ▸ inp.cJSubPtr_mono (Nat.zero_le k)
                omega
              · omega)).trans (hkp.2.2.2.2.2.2.2.2.2 x hx1 hx2)⟩
      · intro k hk1 hk2
        have hkp := hk_rem k (by omega) hk2
        have hgt_a : ∀ off < 7, inp.aComps + 7 * ci + 7 ≤ inp.aComps + 7 * k + off ∧
            inp.aComps + 7 * k + off < inp.cJSubPtr ci := fun _ _ => by
          have : inp.aComps + 7 * inp.rawComps.length ≤ inp.hBlocksStart := by
            rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
          have := inp.cJSubPtr_zero ▸ inp.cJSubPtr_mono (Nat.zero_le ci)
          omega
        exact ⟨(h_m6_out _ (Or.inr (Or.inl (hgt_a 0 (by omega))))).trans hkp.1,
          (h_m6_out _ (Or.inr (Or.inl (hgt_a 1 (by omega))))).trans hkp.2.1,
          (h_m6_out _ (Or.inr (Or.inl (hgt_a 2 (by omega))))).trans hkp.2.2.1,
          (h_m6_out _ (Or.inr (Or.inl (hgt_a 3 (by omega))))).trans hkp.2.2.2.1,
          (h_m6_out _ (Or.inr (Or.inl (hgt_a 4 (by omega))))).trans hkp.2.2.2.2.1,
          (h_m6_out _ (Or.inr (Or.inl (hgt_a 5 (by omega))))).trans hkp.2.2.2.2.2.1,
          (h_m6_out _ (Or.inr (Or.inl (hgt_a 6 (by omega))))).trans hkp.2.2.2.2.2.2⟩
    dsimp only [prepAllocBody]
    refine runs_seq_assign0 (v := inp.aComps + 7 * ci)
      (ev_add (ev_reg hf.2.2.1 (by omega))
        (ev_mul (ev_const (by omega)) (ev_reg h24 (by omega)) h7ci_lt) ha7_lt) ?_
    refine runs_seq_assign_le (v := c.2.length)
      (ev_load (ev_add (ev_reg (by simp) ha7_lt) (ev_const hw1) ha71_lt)
        hci_tab.2.1 hc2_lt) ?_
    refine runs_seq_assign_le (v := (inp.cJSub c).m)
      (ev_load (ev_add (ev_reg (by simp) ha7_lt) (ev_const (by omega)) ha76_lt)
        hci_tab.2.2.2.2.2.2 hmc_lt) ?_
    refine runs_seq_assign_le (v := inp.cJSubPtr ci)
      (ev_reg (by simp [h16]) hptr_lt) ?_
    refine runs_seq_store_le (x := inp.cJSubPtr ci) (v := c.2.length)
      (ev_reg (by simp) hptr_lt) (ev_reg (by simp) hc2_lt) ?_
    refine runs_seq_store_le (x := inp.cJSubPtr ci + 1) (v := (inp.cJSub c).m)
      (ev_add (ev_reg (by simp) hptr_lt) (ev_const hw1) hptr1_lt) (ev_reg (by simp) hmc_lt) ?_
    refine runs_seq_assign_le (v := inp.cJOrigPtr ci)
      (by rw [hptr_eqs.1]
          exact ev_add (ev_add (ev_reg (by simp) hptr_lt) (ev_const (by omega)) hptr2_lt)
            (ev_mul (ev_const (by omega)) (ev_reg (by simp) hmc_lt) h2mc_lt)
            (by rw [← hptr_eqs.1]; exact horig_lt)) ?_
    refine runs_seq_assign_le (v := inp.cDegPtr ci)
      (by rw [hptr_eqs.2.1]
          exact ev_add (ev_reg (by simp) horig_lt) (ev_reg (by simp) hmc_lt)
            (by rw [← hptr_eqs.2.1]; exact hdeg_lt)) ?_
    refine runs_seq_assign_le (v := inp.cJSubPtr (ci + 1))
      (by rw [hptr_eqs.2.2]
          exact ev_add (ev_reg (by simp) hdeg_lt) (ev_reg (by simp) hc2_lt)
            (by rw [← hptr_eqs.2.2]; exact hsucc_lt)) ?_
    refine runs_seq_store_le (x := inp.aComps + 7 * ci + 3) (v := inp.cJSubPtr ci)
      (ev_add (ev_reg (by simp) ha7_lt) (ev_const (by omega)) ha73_lt)
      (ev_reg (by simp) hptr_lt) ?_
    refine runs_seq_store_le (x := inp.aComps + 7 * ci + 4) (v := inp.cJOrigPtr ci)
      (ev_add (ev_reg (by simp) ha7_lt) (ev_const (by omega)) ha74_lt)
      (ev_reg (by simp) horig_lt) ?_
    refine runs_seq_store_le (x := inp.aComps + 7 * ci + 5) (v := inp.cDegPtr ci)
      (ev_add (ev_reg (by simp) ha7_lt) (ev_const (by omega)) ha75_lt)
      (ev_reg (by simp) hdeg_lt) ?_
    refine ⟨.normal, s_fin, _,
      runs_store_iff.mpr ⟨_, _,
        ev_add (ev_reg (by simp) ha7_lt) (ev_const (by omega)) ha76_lt,
        ev_const (by omega), rfl, rfl, rfl⟩,
      by simpa [s_fin] using hs_fin,
      by norm_num [Expr.size]⟩

end MinCostFlow.Spanner
