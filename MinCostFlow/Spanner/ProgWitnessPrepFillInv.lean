module

public import MinCostFlow.Spanner.ProgWitnessPrepBlockHelpers

/-!
# Loop Invariant Preservation for `prepFillStmt`

Defines the functional subgraph-fill memory transforms (`prepFillM4`, `prepFillM6`), the
loop invariant `PrepFillInv`, and proves `prepFill_fin_inv` showing that writing a level edge
into its unique component preserves `PrepFillInv`.
-/

public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-- First four stores of `prepFillBody`: appends edge endpoints `(u', v')`, writes original edge
index, and increments `aComps + 7 * ci + 6`. -/
@[expose] def prepFillM4 (s_mem : ℕ → ℕ) (inp : PrepInput) (ci m_fill u' v' b : ℕ) : ℕ → ℕ :=
  Function.update
    (Function.update
      (Function.update
        (Function.update s_mem (inp.cJSubPtr ci + 2 + 2 * m_fill) u')
        (inp.cJSubPtr ci + 2 + 2 * m_fill + 1) v')
      (inp.cJOrigPtr ci + m_fill) (inp.nlIdx.getD b 0))
    (inp.aComps + 7 * ci + 6) (m_fill + 1)

/-- Full six-store memory transform of `prepFillBody` (adding both endpoint degree increments). -/
@[expose] def prepFillM6 (s_mem : ℕ → ℕ) (inp : PrepInput) (ci m_fill u' v' b : ℕ) : ℕ → ℕ :=
  let m4 := prepFillM4 s_mem inp ci m_fill u' v' b
  let d_u := s_mem (inp.cDegPtr ci + u')
  let m5 := Function.update m4 (inp.cDegPtr ci + u') (d_u + 1)
  let d_v_mid := m5 (inp.cDegPtr ci + v')
  Function.update m5 (inp.cDegPtr ci + v') (d_v_mid + 1)

/-- Loop invariant for `prepFillStmt` scanning remaining bucket chain `rem`. -/
@[expose] def PrepFillInv (inp : PrepInput) (mem₀ : ℕ → ℕ) (i₀ lvl : ℕ)
    (block : List (ℕ × List ℕ)) (rem : List ℕ) (st : State) : Prop :=
  let i₁ := i₀ + block.length
  let edges := DecomposeOutput.edgesAt inp.J0_strip inp.decomp lvl
  ∃ pref : List ℕ,
    edges = pref ++ rem ∧
    PrepFullRegs inp st ∧
    st.regs 16 = inp.cJSubPtr i₁ ∧
    st.regs 17 = i₀ ∧
    st.regs 22 = i₁ ∧
    st.regs 23 = lvl ∧
    ChainAt st.mem inp.aEdgeNext (st.regs 29) rem ∧
    PrepStaticState inp mem₀ st.mem ∧
    CompsDoneUpTo inp st.mem i₀ ∧
    CompsParsedFrom inp st.mem i₁ ∧
    VertMarksBlock inp st.mem i₀ i₁ ∧
    ZeroFrom st.mem (inp.cJSubPtr i₁) ∧
    (∀ k, i₀ ≤ k → k < i₁ →
      let c := inp.rawComps[k]!
      let pref_f := pref.filter fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2)
      st.mem (inp.aComps + 7 * k) = c.1 ∧
      st.mem (inp.aComps + 7 * k + 1) = c.2.length ∧
      st.mem (inp.aComps + 7 * k + 2) = inp.cVertsPtr k ∧
      st.mem (inp.aComps + 7 * k + 3) = inp.cJSubPtr k ∧
      st.mem (inp.aComps + 7 * k + 4) = inp.cJOrigPtr k ∧
      st.mem (inp.aComps + 7 * k + 5) = inp.cDegPtr k ∧
      st.mem (inp.aComps + 7 * k + 6) = pref_f.length ∧
      st.mem (inp.cJSubPtr k) = c.2.length ∧
      st.mem (inp.cJSubPtr k + 1) = (inp.cJSub c).m ∧
      (∀ j (hj : j < pref_f.length),
        let q := pref_f[j]
        let eq := inp.J0_strip.edges.getD q (0, 0)
        st.mem (inp.cJSubPtr k + 2 + 2 * j) = c.2.idxOf eq.1 ∧
        st.mem (inp.cJSubPtr k + 3 + 2 * j) = c.2.idxOf eq.2 ∧
        st.mem (inp.cJOrigPtr k + j) = inp.nlIdx.getD q 0) ∧
      (∀ z < c.2.length,
        st.mem (inp.cDegPtr k + z) =
          (pref_f.filter fun q => decide (c.2.idxOf (inp.J0_strip.edges.getD q (0, 0)).1 = z)).length +
          (pref_f.filter fun q => decide (c.2.idxOf (inp.J0_strip.edges.getD q (0, 0)).2 = z)).length))

/-- One edge-fill step (`prepFillM6`) preserves `PrepFillInv`. -/
theorem prepFill_fin_inv {w : ℕ} (inp : PrepInput) (mem₀ : ℕ → ℕ)
    (hv : inp.Valid mem₀ w)
    {done rest : List (ℕ × ℕ × List (ℕ × List ℕ))} {i₀ lvl : ℕ} {block : List (ℕ × List ℕ)}
    (hcb : compBlocksAux 0 inp.rawComps = done ++ (i₀, lvl, block) :: rest)
    {pref : List ℕ} {b : ℕ} {bs : List ℕ} {s : State}
    (heq : DecomposeOutput.edgesAt inp.J0_strip inp.decomp lvl = pref ++ b :: bs)
    (hch_tail : ChainAt s.mem inp.aEdgeNext (s.mem (inp.aEdgeNext + b)) bs)
    (hst : PrepStaticState inp mem₀ s.mem)
    (hdone : CompsDoneUpTo inp s.mem i₀)
    (hparsed : CompsParsedFrom inp s.mem (i₀ + block.length))
    (hvm : VertMarksBlock inp s.mem i₀ (i₀ + block.length))
    (hzf : ZeroFrom s.mem (inp.cJSubPtr (i₀ + block.length)))
    (hfill : ∀ k, i₀ ≤ k → k < i₀ + block.length →
      let c := inp.rawComps[k]!
      let pref_f := pref.filter fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2)
      s.mem (inp.aComps + 7 * k) = c.1 ∧
      s.mem (inp.aComps + 7 * k + 1) = c.2.length ∧
      s.mem (inp.aComps + 7 * k + 2) = inp.cVertsPtr k ∧
      s.mem (inp.aComps + 7 * k + 3) = inp.cJSubPtr k ∧
      s.mem (inp.aComps + 7 * k + 4) = inp.cJOrigPtr k ∧
      s.mem (inp.aComps + 7 * k + 5) = inp.cDegPtr k ∧
      s.mem (inp.aComps + 7 * k + 6) = pref_f.length ∧
      s.mem (inp.cJSubPtr k) = c.2.length ∧
      s.mem (inp.cJSubPtr k + 1) = (inp.cJSub c).m ∧
      (∀ j (hj : j < pref_f.length),
        let q := pref_f[j]
        let eq := inp.J0_strip.edges.getD q (0, 0)
        s.mem (inp.cJSubPtr k + 2 + 2 * j) = c.2.idxOf eq.1 ∧
        s.mem (inp.cJSubPtr k + 3 + 2 * j) = c.2.idxOf eq.2 ∧
        s.mem (inp.cJOrigPtr k + j) = inp.nlIdx.getD q 0) ∧
      (∀ z < c.2.length,
        s.mem (inp.cDegPtr k + z) =
          (pref_f.filter fun q => decide (c.2.idxOf (inp.J0_strip.edges.getD q (0, 0)).1 = z)).length +
          (pref_f.filter fun q => decide (c.2.idxOf (inp.J0_strip.edges.getD q (0, 0)).2 = z)).length))
    {ci : ℕ} (hci_len : ci < inp.rawComps.length) (hci_lo : i₀ ≤ ci) (hci_hi : ci < i₀ + block.length)
    (he1_ci : (inp.J0_strip.edges.getD b (0, 0)).1 ∈ inp.rawComps[ci].2)
    (_he2_ci : (inp.J0_strip.edges.getD b (0, 0)).2 ∈ inp.rawComps[ci].2)
    (huniq : ∀ (cj : ℕ) (hcj : cj < inp.rawComps.length), i₀ ≤ cj → cj < i₀ + block.length →
      (inp.J0_strip.edges.getD b (0, 0)).1 ∈ inp.rawComps[cj].2 → cj = ci)
    {s_fin : State}
    (hm_eq : s_fin.mem = prepFillM6 s.mem inp ci
      (pref.filter fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ inp.rawComps[ci]!.2)).length
      (inp.rawComps[ci]!.2.idxOf (inp.J0_strip.edges.getD b (0, 0)).1)
      (inp.rawComps[ci]!.2.idxOf (inp.J0_strip.edges.getD b (0, 0)).2)
      b)
    (hf' : PrepFullRegs inp s_fin)
    (h16' : s_fin.regs 16 = inp.cJSubPtr (i₀ + block.length))
    (h17' : s_fin.regs 17 = i₀)
    (h22' : s_fin.regs 22 = i₀ + block.length)
    (h23' : s_fin.regs 23 = lvl)
    (h29' : s_fin.regs 29 = s.mem (inp.aEdgeNext + b)) :
    PrepFillInv inp mem₀ i₀ lvl block bs s_fin := by
  have hsz := inp.size_bounds hv
  have hw1 := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwb := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hpw_rc := hv.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨_, _, hle, hlvl_blk, hget_blk, _, _⟩ := compBlocksAux_split_spec hpw_rc hcb
  obtain ⟨hlvl1, hlvl2⟩ := block_lvl_bounds hv hcb
  let i₁ := i₀ + block.length
  let edges := DecomposeOutput.edgesAt inp.J0_strip inp.decomp lvl
  have hb_mem : b ∈ edges := by dsimp only [edges]; rw [heq]; simp
  have hb_m : b < inp.J0_strip.m := by
    simp only [edges, DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hb_mem
    exact hb_mem.1
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
  have he2_c2 : v ∈ c.2 := by dsimp only [v, e, c]; rw [hc_eq]; exact _he2_ci
  have hu'_lt : u' < c.2.length := List.idxOf_lt_length_iff.mpr he1_c2
  have hv'_lt : v' < c.2.length := List.idxOf_lt_length_iff.mpr he2_c2
  let m_fill := (pref.filter fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2)).length
  have hfill_ci := hfill ci hci_lo hci_hi
  dsimp only at hfill_ci
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
  have hsucc_eq : inp.cJSubPtr (ci + 1) = inp.cEndPtr ci := inp.cJSubPtr_succ hci_len
  have hsucc_le : inp.cJSubPtr (ci + 1) ≤ inp.hEnd := inp.cJSubPtr_le_hEnd (by omega)
  have hc_eq_getD : inp.rawComps.getD ci (0, []) = c := rawComps_getD_eq_getBang _ hci_len
  have hptr_eqs :
      inp.cJOrigPtr ci = inp.cJSubPtr ci + 2 + 2 * (inp.cJSub c).m ∧
      inp.cDegPtr ci = inp.cJOrigPtr ci + (inp.cJSub c).m ∧
      inp.cJSubPtr (ci + 1) = inp.cDegPtr ci + c.2.length := by
    rw [hsucc_eq]
    dsimp only [PrepInput.cEndPtr, PrepInput.cDegPtr, PrepInput.cJOrigPtr]
    rw [hc_eq_getD]; refine ⟨rfl, rfl, rfl⟩
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
  have hm_eq' : s_fin.mem = m6 := hm_eq
  have hm4_du : m4 (inp.cDegPtr ci + u') = d_u := hm4_agree_deg _ (by omega) (by omega)
  have hm4_dv : m4 (inp.cDegPtr ci + v') = s.mem (inp.cDegPtr ci + v') :=
    hm4_agree_deg _ (by omega) (by omega)
  have h_m6_out : ∀ x,
      x ≠ inp.cJSubPtr ci + 2 + 2 * m_fill →
      x ≠ inp.cJSubPtr ci + 2 + 2 * m_fill + 1 →
      x ≠ inp.cJOrigPtr ci + m_fill →
      x ≠ inp.aComps + 7 * ci + 6 →
      (x < inp.cDegPtr ci ∨ inp.cJSubPtr (ci + 1) ≤ x) →
      m6 x = s.mem x := by
    intro x h1 h2 h3 h4 h5
    have hne_u : x ≠ inp.cDegPtr ci + u' := by rcases h5 with h | h <;> omega
    have hne_v : x ≠ inp.cDegPtr ci + v' := by rcases h5 with h | h <;> omega
    dsimp only [m6, prepFillM6, m4, prepFillM4]
    rw [Function.update_of_ne hne_v, Function.update_of_ne hne_u,
      Function.update_of_ne h4, Function.update_of_ne h3,
      Function.update_of_ne h2, Function.update_of_ne h1]
  have h_m6_block_out : ∀ x,
      (x < inp.aComps + 7 * ci + 6 ∨
        (inp.aComps + 7 * ci + 7 ≤ x ∧ x < inp.cJSubPtr ci) ∨
        inp.cJSubPtr (ci + 1) ≤ x) →
      m6 x = s.mem x := by
    intro x hx
    have hbs : inp.aComps + 7 * inp.rawComps.length ≤ inp.hBlocksStart := by
      rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
    have hptr0 : inp.hBlocksStart ≤ inp.cJSubPtr ci := by
      rw [← inp.cJSubPtr_zero]; exact inp.cJSubPtr_mono (Nat.zero_le ci)
    exact h_m6_out x
      (by rcases hx with h | ⟨_, h⟩ | h <;> omega)
      (by rcases hx with h | ⟨_, h⟩ | h <;> omega)
      (by rcases hx with h | ⟨_, h⟩ | h <;> omega)
      (by rcases hx with h | ⟨_, h⟩ | h <;> omega)
      (by rcases hx with h | ⟨_, h⟩ | h <;> [left; left; right] <;> omega)
  have hm6_a6 : m6 (inp.aComps + 7 * ci + 6) = m_fill + 1 := by
    have hbs : inp.aComps + 7 * inp.rawComps.length ≤ inp.hBlocksStart := by
      rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
    have hptr0 : inp.hBlocksStart ≤ inp.cJSubPtr ci := by
      rw [← inp.cJSubPtr_zero]; exact inp.cJSubPtr_mono (Nat.zero_le ci)
    dsimp only [m6, prepFillM6, m4, prepFillM4]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_self]
  have hm6_edge1 : m6 (inp.cJSubPtr ci + 2 + 2 * m_fill) = u' := by
    have hbs : inp.aComps + 7 * inp.rawComps.length ≤ inp.hBlocksStart := by
      rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
    have hptr0 : inp.hBlocksStart ≤ inp.cJSubPtr ci := by
      rw [← inp.cJSubPtr_zero]; exact inp.cJSubPtr_mono (Nat.zero_le ci)
    dsimp only [m6, prepFillM6, m4, prepFillM4]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self]
  have hm6_edge2 : m6 (inp.cJSubPtr ci + 2 + 2 * m_fill + 1) = v' := by
    have hbs : inp.aComps + 7 * inp.rawComps.length ≤ inp.hBlocksStart := by
      rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
    have hptr0 : inp.hBlocksStart ≤ inp.cJSubPtr ci := by
      rw [← inp.cJSubPtr_zero]; exact inp.cJSubPtr_mono (Nat.zero_le ci)
    dsimp only [m6, prepFillM6, m4, prepFillM4]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_self]
  have hm6_orig : m6 (inp.cJOrigPtr ci + m_fill) = inp.nlIdx.getD b 0 := by
    have hbs : inp.aComps + 7 * inp.rawComps.length ≤ inp.hBlocksStart := by
      rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
    have hptr0 : inp.hBlocksStart ≤ inp.cJSubPtr ci := by
      rw [← inp.cJSubPtr_zero]; exact inp.cJSubPtr_mono (Nat.zero_le ci)
    dsimp only [m6, prepFillM6, m4, prepFillM4]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self]
  have hm6_deg : ∀ z < c.2.length,
      m6 (inp.cDegPtr ci + z) =
        s.mem (inp.cDegPtr ci + z) + (if z = u' then 1 else 0) + (if z = v' then 1 else 0) := by
    intro z hz
    have h_upd : m6 (inp.cDegPtr ci + z) =
        m4 (inp.cDegPtr ci + z) +
          (if inp.cDegPtr ci + z = inp.cDegPtr ci + u' then 1 else 0) +
          (if inp.cDegPtr ci + z = inp.cDegPtr ci + v' then 1 else 0) := by
      dsimp only [m6, prepFillM6]
      change Function.update (Function.update m4 (inp.cDegPtr ci + u') (d_u + 1))
          (inp.cDegPtr ci + v')
          (Function.update m4 (inp.cDegPtr ci + u') (d_u + 1) (inp.cDegPtr ci + v') + 1)
          (inp.cDegPtr ci + z) =
        m4 (inp.cDegPtr ci + z) +
          (if inp.cDegPtr ci + z = inp.cDegPtr ci + u' then 1 else 0) +
          (if inp.cDegPtr ci + z = inp.cDegPtr ci + v' then 1 else 0)
      rw [← hm4_du]
      simpa using update_inc_inc m4 (inp.cDegPtr ci + u') (inp.cDegPtr ci + v') (inp.cDegPtr ci + z)
    rw [h_upd, hm4_agree_deg _ (by omega) (by omega)]
    simp
  have hbs : inp.aComps + 7 * inp.rawComps.length ≤ inp.hBlocksStart := by
    rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc, PrepInput.aVComp]; omega
  have hptr0 : inp.hBlocksStart ≤ inp.cJSubPtr ci := by
    rw [← inp.cJSubPtr_zero]; exact inp.cJSubPtr_mono (Nat.zero_le ci)
  have hchain_bs : ChainAt s_fin.mem inp.aEdgeNext (s_fin.regs 29) bs := by
    rw [hm_eq, h29']
    refine chainAt_of_agree hch_tail fun q hq => ?_
    have hq_ed : q ∈ edges := by dsimp only [edges]; rw [heq]; simp [hq]
    simp only [edges, DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hq_ed
    have hqm := hq_ed.1
    exact h_m6_block_out _ (Or.inl (by simp only [PrepInput.aComps, PrepInput.aJ0Out]; omega))
  dsimp only [PrepFillInv]
  refine ⟨pref ++ [b], by simpa [List.append_assoc] using heq,
    hf', h16', h17', h22', h23', hchain_bs,
    prepStaticState_of_agree hst (fun x hx => by rw [hm_eq]; exact h_m6_block_out x (Or.inl (by omega))),
    compsDoneUpTo_of_agree hv (by omega) hdone
      (fun x hx1 hx2 => by rw [hm_eq]; exact h_m6_block_out x (Or.inl (by omega)))
      (fun x hx1 hx2 => by
        rw [hm_eq]
        have := inp.cJSubPtr_mono hci_lo
        exact h_m6_block_out x (Or.inr (Or.inl ⟨by omega, by omega⟩))),
    compsParsedFrom_of_agree hparsed (fun x hx1 hx2 => by
      rw [hm_eq]; exact h_m6_block_out x (Or.inr (Or.inl ⟨by omega, by omega⟩))),
    ?_,
    fun x hx => by
      rw [hm_eq]
      have := inp.cJSubPtr_mono (show ci + 1 ≤ i₀ + block.length by omega)
      exact (h_m6_block_out x (Or.inr (Or.inr (by omega)))).trans (hzf x hx),
    ?_⟩
  · refine ⟨?_, fun hci1' => by omega, ?_⟩
    · intro cj hcj hcj1 hcj2 p hp
      have hcj_eq : inp.rawComps[cj]! = inp.rawComps[cj] := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hcj]; rfl
      have hu_n := (comp_props_at hv hcj).2.2.2.2.2.1 _ (by rw [hcj_eq]; exact List.getElem_mem hp)
      have hvc_gt : inp.aComps + 7 * ci + 7 ≤ inp.aVComp + inp.rawComps[cj].2[p] ∧
          inp.aVComp + inp.rawComps[cj].2[p] < inp.cJSubPtr ci := by
        have : inp.aVComp + inp.J.n ≤ inp.hBlocksStart := by
          rw [inp.hBlocksStart_eq]; simp only [PrepInput.aVLoc]; omega
        simp only [PrepInput.aVComp] at *; omega
      have hvl_gt : inp.aComps + 7 * ci + 7 ≤ inp.aVLoc + inp.rawComps[cj].2[p] ∧
          inp.aVLoc + inp.rawComps[cj].2[p] < inp.cJSubPtr ci := by
        have : inp.aVLoc + inp.J.n = inp.hBlocksStart := inp.hBlocksStart_eq.symm
        simp only [PrepInput.aVLoc, PrepInput.aVComp] at *; omega
      have hprev := hvm.1 cj hcj hcj1 hcj2 p hp
      rw [hm_eq]
      exact ⟨(h_m6_block_out _ (Or.inr (Or.inl hvc_gt))).trans hprev.1,
        (h_m6_block_out _ (Or.inr (Or.inl hvl_gt))).trans hprev.2⟩
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
      rw [hm_eq]
      exact ⟨(h_m6_block_out _ (Or.inr (Or.inl hvc_gt))).trans hprev.1,
        (h_m6_block_out _ (Or.inr (Or.inl hvl_gt))).trans hprev.2⟩
  · intro k hk1 hk2
    have hkp := hfill k hk1 hk2
    dsimp only at hkp
    by_cases hkc : k = ci
    · subst hkc
      have hdec_b : decide ((inp.J0_strip.edges.getD b (0, 0)).1 ∈ c.2) = true := by
        simpa [u, e, decide_eq_true_eq] using he1_c2
      have hfilt_step :
          (pref ++ [b]).filter (fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ inp.rawComps[k]!.2)) =
          pref.filter (fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2)) ++ [b] := by
        change (pref ++ [b]).filter (fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2)) = _
        rw [List.filter_append, List.filter_cons, List.filter_nil, hdec_b]
        rfl
      rw [hm_eq', hfilt_step]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h_m6_block_out _ (Or.inl (by omega))]; exact hkp.1
      · rw [h_m6_block_out _ (Or.inl (by omega))]; exact hkp.2.1
      · rw [h_m6_block_out _ (Or.inl (by omega))]; exact hkp.2.2.1
      · rw [h_m6_block_out _ (Or.inl (by omega))]; exact hkp.2.2.2.1
      · rw [h_m6_block_out _ (Or.inl (by omega))]; exact hkp.2.2.2.2.1
      · rw [h_m6_block_out _ (Or.inl (by omega))]; exact hkp.2.2.2.2.2.1
      · simp only [List.length_append, List.length_singleton]
        exact hm6_a6
      · rw [h_m6_out _ (by omega) (by omega) (by omega) (by omega) (by left; omega)]
        exact hkp.2.2.2.2.2.2.2.1
      · rw [h_m6_out _ (by omega) (by omega) (by omega) (by omega) (by left; omega)]
        exact hkp.2.2.2.2.2.2.2.2.1
      · intro j hj
        simp only [List.length_append, List.length_singleton] at hj
        by_cases hjm : j = m_fill
        · subst hjm
          have hget_last : (pref.filter (fun q =>
              decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2)) ++ [b])[m_fill] = b := by
            rw [List.getElem_append_right (le_refl _)]; simp
          simp only [hget_last]
          exact ⟨hm6_edge1, by rw [show inp.cJSubPtr k + 3 + 2 * m_fill =
            inp.cJSubPtr k + 2 + 2 * m_fill + 1 by omega]; exact hm6_edge2, hm6_orig⟩
        · have hj_lt : j < m_fill := by omega
          have hget_prev : (pref.filter (fun q =>
              decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2)) ++ [b])[j] =
              (pref.filter (fun q =>
                decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ c.2)))[j]'hj_lt :=
            List.getElem_append_left hj_lt
          simp only [hget_prev]
          have hprev_j := hkp.2.2.2.2.2.2.2.2.2.1 j hj_lt
          refine ⟨?_, ?_, ?_⟩
          · rw [h_m6_out _ (by omega) (by omega) (by omega) (by omega) (by left; omega)]
            exact hprev_j.1
          · rw [h_m6_out _ (by omega) (by omega) (by omega) (by omega) (by left; omega)]
            exact hprev_j.2.1
          · rw [h_m6_out _ (by omega) (by omega) (by omega) (by omega) (by left; omega)]
            exact hprev_j.2.2
      · intro z hz
        have hm6z := hm6_deg z hz
        have hkpz := hkp.2.2.2.2.2.2.2.2.2.2 z hz
        rw [hm6z, hkpz]
        dsimp only [c]
        rw [List.filter_append, List.filter_append, List.length_append, List.length_append]
        have h1_elem : inp.rawComps[k]!.2.idxOf (inp.J0_strip.edges.getD b (0, 0)).1 = u' := rfl
        have h2_elem : inp.rawComps[k]!.2.idxOf (inp.J0_strip.edges.getD b (0, 0)).2 = v' := rfl
        have h1 : ([b].filter fun q =>
            decide (inp.rawComps[k]!.2.idxOf (inp.J0_strip.edges.getD q (0, 0)).1 = z)).length =
            (if z = u' then 1 else 0) := by
          rw [List.filter_cons, List.filter_nil, h1_elem]
          by_cases hzu : z = u'
          · have hdec : decide (u' = z) = true := decide_eq_true hzu.symm
            rw [hdec]; simp [hzu]
          · have hdec : decide (u' = z) = false := decide_eq_false (Ne.symm hzu)
            rw [hdec]; simp [hzu]
        have h2 : ([b].filter fun q =>
            decide (inp.rawComps[k]!.2.idxOf (inp.J0_strip.edges.getD q (0, 0)).2 = z)).length =
            (if z = v' then 1 else 0) := by
          rw [List.filter_cons, List.filter_nil, h2_elem]
          by_cases hzv : z = v'
          · have hdec : decide (v' = z) = true := decide_eq_true hzv.symm
            rw [hdec]; simp [hzv]
          · have hdec : decide (v' = z) = false := decide_eq_false (Ne.symm hzv)
            rw [hdec]; simp [hzv]
        rw [h1, h2]
        omega
    · have hnot_mem : (inp.J0_strip.edges.getD b (0, 0)).1 ∉ inp.rawComps[k]!.2 := by
        intro hmem
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k < inp.rawComps.length)] at hmem
        exact hkc (huniq k (by omega) hk1 hk2 hmem)
      have hdec_b : decide ((inp.J0_strip.edges.getD b (0, 0)).1 ∈ inp.rawComps[k]!.2) = false := by
        simpa using hnot_mem
      have hfilt_same :
          (pref ++ [b]).filter (fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ inp.rawComps[k]!.2)) =
          pref.filter (fun q => decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ inp.rawComps[k]!.2)) := by
        rw [List.filter_append, List.filter_cons, List.filter_nil, hdec_b]
        simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
      have hdisj_mem : ∀ x, inp.cJSubPtr k ≤ x → x < inp.cJSubPtr (k + 1) → m6 x = s.mem x := by
        intro x hx1 hx2
        rcases lt_or_gt_of_ne hkc with hlt | hgt
        · have hle_k1 : inp.cJSubPtr (k + 1) ≤ inp.cJSubPtr ci := inp.cJSubPtr_mono hlt
          have hk0 : inp.hBlocksStart ≤ inp.cJSubPtr k := by
            rw [← inp.cJSubPtr_zero]; exact inp.cJSubPtr_mono (Nat.zero_le k)
          exact h_m6_block_out x (Or.inr (Or.inl ⟨by omega, by omega⟩))
        · have hle_ci1 : inp.cJSubPtr (ci + 1) ≤ inp.cJSubPtr k := inp.cJSubPtr_mono hgt
          exact h_m6_block_out x (Or.inr (Or.inr (by omega)))
      have hk_len : k < inp.rawComps.length := by omega
      have hk_eqD : inp.rawComps.getD k (0, []) = inp.rawComps[k]! :=
        rawComps_getD_eq_getBang _ hk_len
      have hkp_eqs :
          inp.cJOrigPtr k = inp.cJSubPtr k + 2 + 2 * (inp.cJSub inp.rawComps[k]!).m ∧
          inp.cDegPtr k = inp.cJOrigPtr k + (inp.cJSub inp.rawComps[k]!).m ∧
          inp.cJSubPtr (k + 1) = inp.cDegPtr k + inp.rawComps[k]!.2.length := by
        rw [inp.cJSubPtr_succ hk_len]
        dsimp only [PrepInput.cEndPtr, PrepInput.cDegPtr, PrepInput.cJOrigPtr]
        rw [hk_eqD]; refine ⟨rfl, rfl, rfl⟩
      have hpf_le_m : (pref.filter fun q =>
          decide ((inp.J0_strip.edges.getD q (0, 0)).1 ∈ inp.rawComps[k]!.2)).length ≤
          (inp.cJSub inp.rawComps[k]!).m := by
        have hclvl_k : inp.rawComps[k]!.1 = lvl := by
          have hidx : k - i₀ < block.length := by omega
          have hg := hget_blk (k - i₀) hidx
          rw [show i₀ + (k - i₀) = k by omega] at hg
          rw [List.getElem!_eq_getElem?_getD, hg]
          exact hlvl_blk block[k - i₀] (List.getElem_mem hidx)
        have hed_k := (comp_edges_orig_spec hv hk_len).2.1
        have hpref_sub : pref.Sublist edges := by
          dsimp only [edges]; rw [heq]; exact List.sublist_append_left pref (b :: bs)
        have hed_eq_k : edges = DecomposeOutput.edgesAt inp.J0_strip inp.decomp inp.rawComps[k]!.1 := by
          dsimp only [edges]; rw [hclvl_k]
        rw [hed_k, ← hed_eq_k]
        exact (List.Sublist.filter _ hpref_sub).length_le
      have hoff_out : ∀ off < 7, m6 (inp.aComps + 7 * k + off) = s.mem (inp.aComps + 7 * k + off) := by
        intro off hoff
        rcases lt_or_gt_of_ne hkc with hlt | hgt
        · exact h_m6_block_out _ (Or.inl (by omega))
        · exact h_m6_block_out _ (Or.inr (Or.inl ⟨by omega, by
            have := inp.cJSubPtr_zero ▸ inp.cJSubPtr_mono (Nat.zero_le ci); omega⟩))
      rw [hm_eq', hfilt_same]
      refine ⟨(hoff_out 0 (by omega)).trans hkp.1, (hoff_out 1 (by omega)).trans hkp.2.1,
        (hoff_out 2 (by omega)).trans hkp.2.2.1, (hoff_out 3 (by omega)).trans hkp.2.2.2.1,
        (hoff_out 4 (by omega)).trans hkp.2.2.2.2.1, (hoff_out 5 (by omega)).trans hkp.2.2.2.2.2.1,
        (hoff_out 6 (by omega)).trans hkp.2.2.2.2.2.2.1,
        (hdisj_mem _ (by omega) (by omega)).trans hkp.2.2.2.2.2.2.2.1,
        (hdisj_mem _ (by omega) (by omega)).trans hkp.2.2.2.2.2.2.2.2.1,
        ?_, ?_⟩
      · intro j hj
        have hprev_j := hkp.2.2.2.2.2.2.2.2.2.1 j hj
        refine ⟨(hdisj_mem _ (by omega) (by omega)).trans hprev_j.1,
          (hdisj_mem _ (by omega) (by omega)).trans hprev_j.2.1,
          (hdisj_mem _ (by omega) (by omega)).trans hprev_j.2.2⟩
      · intro z hz
        exact (hdisj_mem _ (by omega) (by omega)).trans (hkp.2.2.2.2.2.2.2.2.2.2 z hz)

end MinCostFlow.Spanner
