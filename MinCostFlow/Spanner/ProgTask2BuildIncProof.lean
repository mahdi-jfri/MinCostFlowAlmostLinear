module

public import MinCostFlow.Spanner.ProgTask2BuildInc

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Inner and middle loop proofs for `t2BuildIncBody` -/

lemma t2BuildInc_inner_step {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} {p : Program} (ctx : T2Ctx impl inp mem₀ w) {memStart : ℕ → ℕ}
    {ci b j v15 v16 : ℕ} (hci : ci < ctx.wd.comps.length) (hb : b < ctx.wd.comps[ci].J_sub.m)
    (hEmbStart : EmbAt memStart inp.embJHAddr inp.J.m inp.embJH)
    (hEmbBnd : EmbBounded memStart inp.embJHAddr inp.J.m inp.embJH inp.t1OutAddr)
    (hW : 1 < 2 ^ w) (hMax : inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length + 3 * inp.embVertSum < 2 ^ w) :
    let eJ := ctx.wd.comps[ci].jSubOrigEdges.getD b 0
    let walk := inp.embJH eJ
    j < walk.verts.length →
    Triple w p
      (fun st => T2IncInv ctx memStart (ci + 1) ci b j st ∧
        st.regs 12 = ci ∧ st.regs 15 = v15 ∧ st.regs 16 = v16 ∧ st.regs 17 = b ∧ st.regs 21 = j ∧
        st.regs 19 = memStart (inp.embJHAddr + eJ) ∧ st.regs 20 = walk.verts.length)
      (Stmt.assign 22 (t2Ld (.reg 19) (t2Add (.const 1) (.reg 21))) ;;
       Stmt.assign 23 (t2Ld (.reg 8) (.reg 22)) ;;
       Stmt.store (.reg 11) (.reg 12) ;;
       t2St (.reg 11) (.const 1) (.reg 17) ;;
       t2St (.reg 11) (.const 2) (.reg 23) ;;
       t2St (.reg 8) (.reg 22) (.reg 11) ;;
       Stmt.assign 11 (t2Add (.reg 11) (.const 3)))
      (normalPost fun st₁ =>
        (T2IncInv ctx memStart (ci + 1) ci b (j + 1)
          { st₁ with regs := Function.update st₁.regs 21 (j + 1) } ∧
          st₁.regs 12 = ci ∧ st₁.regs 15 = v15 ∧ st₁.regs 16 = v16 ∧ st₁.regs 17 = b ∧
          st₁.regs 19 = memStart (inp.embJHAddr + eJ) ∧ st₁.regs 20 = walk.verts.length) ∧
        st₁.regs 21 = j)
      (fun _ => 40) := by
  intro eJ walk hj st ω ⟨hinv, hr12, hr15, hr16, hr17, hr21, hr19, hr20⟩
  rcases hinv with ⟨hr0, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hptr_lo, hptr_hi, hzf,
    hfr, hceb, hvho, hInc⟩
  set mW := ctx.wd.W.m
  set K := ctx.wd.comps.length
  set nodesAddr := inp.nodesAddr mW K
  set ptr := st.regs 11
  set walkPtr := memStart (inp.embJHAddr + eJ)
  set x := walk.verts[j]
  have heJ_lt : eJ < inp.J.m := by
    have hprops := ctx.hw_okW.comp_props ci hci
    have ho : b < ctx.wd.comps[ci].jSubOrigEdges.length := by
      rw [hprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hb
    have hmem : eJ ∈ ctx.wd.comps[ci].jSubOrigEdges := by
      dsimp only [eJ]; rw [List.getD_eq_getElem _ _ ho]; exact List.getElem_mem ho
    exact ctx.hWInpJ ▸ hprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 eJ hmem
  have hWalkAt0 : WalkAt memStart walkPtr walk := hEmbStart eJ heJ_lt
  have hWalkBnd : walkPtr + (Walk.encode walk).length ≤ inp.t1OutAddr := hEmbBnd.2 eJ heJ_lt
  have hchain := t2_prep_chain_bounds ctx
  have hdisj : inp.v1 + 32 ≤ inp.compEdgeBaseAddr mW K ∧
      inp.compEdgeBaseAddr mW K + K = inp.vhatOffsetAddr mW K ∧
      inp.vhatOffsetAddr mW K + K = inp.compEdgeDelRoundAddr mW K ∧
      inp.compEdgeDelRoundAddr mW K ≤ inp.vHeadAddr mW K ∧
      inp.vHeadAddr mW K + inp.H'.n ≤ inp.nodesAddr mW K ∧
      2 * inp.J.m ≤ inp.nodesAddr mW K ∧ inp.H'.n ≤ inp.nodesAddr mW K :=
    t2_v1_le_compEdgeBase ctx
  have hnodes_lt_w : inp.nodesAddr mW K + 3 * inp.embVertSum < 2 ^ w := hMax
  have hWalkAt : WalkAt st.mem walkPtr walk :=
    hWalkAt0.of_agree_below (le_trans hWalkBnd (show inp.t1OutAddr ≤ inp.compEdgeBaseAddr mW K by omega))
      fun a ha => hfr a (Or.inl ha)
  have hx_lt_nH : x < inp.H'.n :=
    Walk.isWalk_verts_lt ctx.hH' (ctx.hembJH.2 eJ heJ_lt) x (List.getElem_mem hj)
  have hx_val : st.mem (walkPtr + (1 + j)) = x := by
    have hget := hWalkAt.verts_listAt.getElem hj
    rwa [show walkPtr + 1 + j = walkPtr + (1 + j) by omega] at hget
  have hp_pref : t2PrefixVerts ctx.wd.comps inp.embJH ci b + (j + 1) ≤ inp.embVertSum := by
    have h1 := t2PrefixVerts_add_j hci hj
    have h2 : t2PrefixVerts ctx.wd.comps inp.embJH ci (b + 1) ≤
        t2PrefixVerts ctx.wd.comps inp.embJH (ci + 1) 0 := by
      have hg := List.getD_eq_getElem ctx.wd.comps defaultCompInfo hci
      calc t2PrefixVerts ctx.wd.comps inp.embJH ci (b + 1)
          = (∑ c ∈ Finset.range ci,
              ∑ b' ∈ Finset.range (ctx.wd.comps.getD c defaultCompInfo).J_sub.m,
                (inp.embJH ((ctx.wd.comps.getD c defaultCompInfo).jSubOrigEdges.getD b' 0)).verts.length) +
              ∑ b' ∈ Finset.range (b + 1),
                (inp.embJH ((ctx.wd.comps.getD ci defaultCompInfo).jSubOrigEdges.getD b' 0)).verts.length := rfl
        _ ≤ (∑ c ∈ Finset.range ci,
              ∑ b' ∈ Finset.range (ctx.wd.comps.getD c defaultCompInfo).J_sub.m,
                (inp.embJH ((ctx.wd.comps.getD c defaultCompInfo).jSubOrigEdges.getD b' 0)).verts.length) +
              ∑ b' ∈ Finset.range ctx.wd.comps[ci].J_sub.m,
                (inp.embJH ((ctx.wd.comps.getD ci defaultCompInfo).jSubOrigEdges.getD b' 0)).verts.length :=
            Nat.add_le_add_left (Finset.sum_le_sum_of_subset (Finset.range_mono hb)) _
        _ = t2PrefixVerts ctx.wd.comps inp.embJH (ci + 1) 0 := by
            rw [← t2PrefixVerts_comp_end hci]; unfold t2PrefixVerts; rw [hg]
    exact Nat.le_trans h1 (Nat.le_trans h2 (t2PrefixVerts_le_embVertSum ctx (by omega)))
  have hptr_w : ptr + 3 < 2 ^ w := by omega
  have hwp_w : walkPtr + (1 + j) < 2 ^ w := by have := walk_encode_length walk; omega
  have hvhead_w : inp.vHeadAddr mW K + x < 2 ^ w := by omega
  have hx_w : x < 2 ^ w := by omega
  have hci_w : ci < 2 ^ w := by have := ctx.hK_le; omega
  have hb_w : b < 2 ^ w := by
    have hsum : (ctx.wd.comps.map fun c => c.J_sub.m).sum ≤ inp.J.m := by
      have h := mkW_sum_comp_j_m_le_J ctx.hstat ctx.hw_okW ctx.hws
      change ctx.wd.j0Edges.length + (ctx.wd.comps.map fun c => c.J_sub.m).sum ≤ ctx.wInp.prep.J.m at h
      rw [ctx.hWInpJ] at h; omega
    have hcb : ctx.wd.comps[ci].J_sub.m ≤ (ctx.wd.comps.map fun c => c.J_sub.m).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem (f := fun c : CompInfo => c.J_sub.m) (List.getElem_mem hci))
    omega
  have h1j_w : 1 + j < 2 ^ w := by omega
  set oldHead := st.mem (inp.vHeadAddr mW K + x)
  have holdHead_w : oldHead < 2 ^ w := by
    obtain ⟨L_of, hL_of, _⟩ := hInc
    obtain ⟨hc_x, _, _⟩ := hL_of x hx_lt_nH
    rcases hc_x.head_lt with h0 | hhi <;> omega
  have hr19_w : walkPtr < 2 ^ w := by omega
  have hr21_w : j < 2 ^ w := by omega
  suffices hres : ∃ o st' c, Runs w p ω
      (Stmt.assign 22 (t2Ld (.reg 19) (t2Add (.const 1) (.reg 21))) ;;
       Stmt.assign 23 (t2Ld (.reg 8) (.reg 22)) ;;
       Stmt.store (.reg 11) (.reg 12) ;;
       t2St (.reg 11) (.const 1) (.reg 17) ;;
       t2St (.reg 11) (.const 2) (.reg 23) ;;
       t2St (.reg 8) (.reg 22) (.reg 11) ;;
       Stmt.assign 11 (t2Add (.reg 11) (.const 3))) st o st' c ∧
      normalPost (fun st₁ =>
        (T2IncInv ctx memStart (ci + 1) ci b (j + 1)
          { st₁ with regs := Function.update st₁.regs 21 (j + 1) } ∧
          st₁.regs 12 = ci ∧ st₁.regs 15 = v15 ∧ st₁.regs 16 = v16 ∧ st₁.regs 17 = b ∧
          st₁.regs 19 = memStart (inp.embJHAddr + eJ) ∧ st₁.regs 20 = walk.verts.length) ∧
        st₁.regs 21 = j) o st' ∧ 0 + c ≤ 40 by
    simpa only [Nat.zero_add] using hres
  refine runs_seq_assign_le (v := x)
    (ev_load (ev_add (ev_reg hr19 hr19_w) (ev_add (ev_const hW) (ev_reg hr21 hr21_w) h1j_w) hwp_w)
      hx_val hx_w) ?_
  set r22 := Function.update st.regs 22 x
  refine runs_seq_assign_le (v := oldHead)
    (ev_load (ev_add (ev_reg (r := 8) (by simp [r22, hr8]) (by omega))
      (ev_reg (r := 22) (by simp [r22]) hx_w) hvhead_w) rfl holdHead_w) ?_
  set r23 := Function.update r22 23 oldHead
  refine runs_seq_store_le (x := ptr) (v := ci)
    (ev_reg (r := 11) (by simp [r23, r22, ptr]) (by omega))
    (ev_reg (r := 12) (by simp [r23, r22, hr12]) hci_w) ?_
  set m1 := Function.update st.mem ptr ci
  refine runs_seq_store_le (x := ptr + 1) (v := b)
    (ev_add (ev_reg (r := 11) (by simp [r23, r22, ptr]) (by omega)) (ev_const hW) (by omega))
    (ev_reg (r := 17) (by simp [r23, r22, hr17]) hb_w) ?_
  set m2 := Function.update m1 (ptr + 1) b
  refine runs_seq_store_le (x := ptr + 2) (v := oldHead)
    (ev_add (ev_reg (r := 11) (by simp [r23, r22, ptr]) (by omega))
      (ev_const (w := w) (by omega)) (by omega))
    (ev_reg (r := 23) (by simp [r23]) holdHead_w) ?_
  set m3 := Function.update m2 (ptr + 2) oldHead
  refine runs_seq_store_le (x := inp.vHeadAddr mW K + x) (v := ptr)
    (ev_add (ev_reg (r := 8) (by simp [r23, r22, hr8]) (by omega))
      (ev_reg (r := 22) (by simp [r23, r22]) hx_w) hvhead_w)
    (ev_reg (r := 11) (by simp [r23, r22, ptr]) (by omega)) ?_
  set m4 := Function.update m3 (inp.vHeadAddr mW K + x) ptr
  have he_ptr3 : (t2Add (.reg 11) (.const 3)).eval w { st with regs := r23, mem := m4 } =
      some (ptr + 3) :=
    ev_add (ev_reg (r := 11) (by simp [r23, r22, ptr]) (by omega))
      (ev_const (w := w) (by omega)) hptr_w
  refine ⟨.normal, { st with regs := Function.update r23 11 (ptr + 3), mem := m4 }, 4,
    runs_assign_iff.mpr ⟨ptr + 3, he_ptr3, rfl, rfl, rfl⟩, ?_, by simp only [Expr.size]; omega⟩
  have hnodes_le_ptr : inp.nodesAddr mW K ≤ ptr := hptr_lo
  have hne0 : ptr ≠ inp.vHeadAddr mW K + x := by omega
  have hne1 : ptr + 1 ≠ inp.vHeadAddr mW K + x := by omega
  have hne2 : ptr + 2 ≠ inp.vHeadAddr mW K + x := by omega
  have hm4_0 : m4 ptr = ci := by simp [m4, m3, m2, m1, hne0]
  have hm4_1 : m4 (ptr + 1) = b := by simp [m4, m3, m2, hne1]
  have hm4_2 : m4 (ptr + 2) = oldHead := by simp [m4, m3, hne2]
  have hm4_hd : m4 (inp.vHeadAddr mW K + x) = ptr := by simp [m4]
  have hzf' : ZeroFrom m4 (ptr + 3) := fun a ha => by
    simp only [m4, m3, m2, m1, Function.update_of_ne (by omega : a ≠ inp.vHeadAddr mW K + x),
      Function.update_of_ne (by omega : a ≠ ptr + 2),
      Function.update_of_ne (by omega : a ≠ ptr + 1),
      Function.update_of_ne (by omega : a ≠ ptr)]
    exact hzf a (by omega)
  have hptr_ctx : inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length ≤ ptr := hnodes_le_ptr
  have hfr' : T2BuildIncFrame ctx memStart m4 :=
    t2BuildIncFrame_upd_vHead ctx
      (t2BuildIncFrame_upd_node ctx (t2BuildIncFrame_upd_node ctx
        (t2BuildIncFrame_upd_node ctx hfr hptr_ctx) (by omega)) (by omega)) hx_lt_nH
  have hceb' : ∀ c < ci + 1, m4 (inp.compEdgeBaseAddr mW K + c) = compEdgeBase ctx.wd c := fun c hc => by
    simp only [m4, m3, m2, m1,
      Function.update_of_ne (by omega : inp.compEdgeBaseAddr mW K + c ≠ inp.vHeadAddr mW K + x),
      Function.update_of_ne (by omega : inp.compEdgeBaseAddr mW K + c ≠ ptr + 2),
      Function.update_of_ne (by omega : inp.compEdgeBaseAddr mW K + c ≠ ptr + 1),
      Function.update_of_ne (by omega : inp.compEdgeBaseAddr mW K + c ≠ ptr)]
    exact hceb c hc
  have hvho' : ∀ c < ci + 1, m4 (inp.vhatOffsetAddr mW K + c) = vhatBase ctx.wd c := fun c hc => by
    simp only [m4, m3, m2, m1,
      Function.update_of_ne (by omega : inp.vhatOffsetAddr mW K + c ≠ inp.vHeadAddr mW K + x),
      Function.update_of_ne (by omega : inp.vhatOffsetAddr mW K + c ≠ ptr + 2),
      Function.update_of_ne (by omega : inp.vhatOffsetAddr mW K + c ≠ ptr + 1),
      Function.update_of_ne (by omega : inp.vhatOffsetAddr mW K + c ≠ ptr)]
    exact hvho c hc
  have hInc_push := incListForPairs_push hci hb hx_lt_nH (List.getElem_mem hj) hptr_lo hInc
    hm4_0 hm4_1 hm4_2 hm4_hd
    (fun y _ hne => by
      simp only [m4, m3, m2, m1,
        Function.update_of_ne (by omega : inp.vHeadAddr mW K + y ≠ inp.vHeadAddr mW K + x),
        Function.update_of_ne (by omega : inp.vHeadAddr mW K + y ≠ ptr + 2),
        Function.update_of_ne (by omega : inp.vHeadAddr mW K + y ≠ ptr + 1),
        Function.update_of_ne (by omega : inp.vHeadAddr mW K + y ≠ ptr)])
    (fun a _ ha_lt => by
      simp only [m4, m3, m2, m1,
        Function.update_of_ne (by omega : a ≠ inp.vHeadAddr mW K + x),
        Function.update_of_ne (by omega : a ≠ ptr + 2),
        Function.update_of_ne (by omega : a ≠ ptr + 1),
        Function.update_of_ne (by omega : a ≠ ptr)])
  have hj_opt : walk.verts[j]? = some x := by simp [x, hj]
  have hInc' := incListForPairs_mono hInc_push (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun ci' b' x' h => t2DonePred_succ_j hci hj_opt h)
  refine ⟨⟨?_, by simpa [r23, r22, walkPtr] using ⟨hr12, hr15, hr16, hr17, hr19, hr20⟩⟩,
    by simp [r23, r22, hr21]⟩
  refine ⟨by simp [r23, r22, hr0], by simp [r23, r22, hr2], by simpa [r23, r22] using hr3,
      by simp [r23, r22, hr4], by simpa [r23, r22] using hr5, by simpa [r23, r22] using hr6,
      by simp [r23, r22, hr7], by simpa [r23, r22] using hr8,
      by simp [r23, r22, hr9], by simp [r23, r22, hr10], ?_, ?_, hzf', hfr', hceb', hvho', hInc'⟩
  · simp [ptr]; exact hptr_lo.trans (Nat.le_add_right _ _)
  · change ptr + 3 ≤ inp.nodesAddr mW K + 3 * _; dsimp only [ptr] at hptr_hi; omega

lemma t2BuildInc_mid_step {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} {p : Program} (ctx : T2Ctx impl inp mem₀ w) {memStart : ℕ → ℕ}
    {ci b : ℕ} (hci : ci < ctx.wd.comps.length) (hb : b < ctx.wd.comps[ci].J_sub.m)
    (hEmbStart : EmbAt memStart inp.embJHAddr inp.J.m inp.embJH)
    (hEmbBnd : EmbBounded memStart inp.embJHAddr inp.J.m inp.embJH inp.t1OutAddr)
    (hCompsStart : CompsDoneUpTo ctx.wInp.prep memStart ctx.wInp.prep.rawComps.length)
    (hW : 1 < 2 ^ w) (hMax : inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length + 3 * inp.embVertSum < 2 ^ w) :
    let eJ := ctx.wd.comps[ci].jSubOrigEdges.getD b 0
    let vertsLen := (inp.embJH eJ).verts.length
    Triple w p
      (fun st => T2IncInv ctx memStart (ci + 1) ci b 0 st ∧
        st.regs 12 = ci ∧ st.regs 15 = ctx.wInp.prep.cJOrigPtr ci ∧
        st.regs 16 = ctx.wd.comps[ci].J_sub.m ∧ st.regs 17 = b)
      (Stmt.assign 18 (t2Ld (.reg 15) (.reg 17)) ;;
       Stmt.assign 19 (t2Ld (.reg 7) (.reg 18)) ;;
       Stmt.assign 20 (.load (.reg 19)) ;;
       forRange 21 (.const 0) (.reg 20) (
         Stmt.assign 22 (t2Ld (.reg 19) (t2Add (.const 1) (.reg 21))) ;;
         Stmt.assign 23 (t2Ld (.reg 8) (.reg 22)) ;;
         Stmt.store (.reg 11) (.reg 12) ;;
         t2St (.reg 11) (.const 1) (.reg 17) ;;
         t2St (.reg 11) (.const 2) (.reg 23) ;;
         t2St (.reg 8) (.reg 22) (.reg 11) ;;
         Stmt.assign 11 (t2Add (.reg 11) (.const 3))
       ))
      (normalPost fun st₁ =>
        (T2IncInv ctx memStart (ci + 1) ci (b + 1) 0
          { st₁ with regs := Function.update st₁.regs 17 (b + 1) } ∧
          st₁.regs 12 = ci ∧ st₁.regs 15 = ctx.wInp.prep.cJOrigPtr ci ∧
          st₁.regs 16 = ctx.wd.comps[ci].J_sub.m) ∧
        st₁.regs 17 = b)
      (fun _ => 49 * vertsLen + 23) := by
  intro eJ vertsLen st ω ⟨hinv, hr12, hr15, hr16, hr17⟩
  have hrc := hinv
  rcases hrc with ⟨hr0, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hptr_lo, hptr_hi, hzf,
    hfr, hceb, hvho, hInc⟩
  set mW := ctx.wd.W.m
  set K := ctx.wd.comps.length
  have hlen := ctx.wInp.buildCompsFrom_length ctx.wInp.prep.j0Edges.length
    ctx.wInp.prep.rawComps ctx.WSubs ctx.hws.1
  have hci_r : ci < ctx.wInp.prep.rawComps.length := by
    change ci < (ctx.wInp.buildCompsFrom _ _ _).length at hci; omega
  have hchain := t2_prep_chain_bounds ctx
  have hdisj : inp.v1 + 32 ≤ inp.compEdgeBaseAddr mW K ∧
      inp.compEdgeBaseAddr mW K + K = inp.vhatOffsetAddr mW K ∧
      inp.vhatOffsetAddr mW K + K = inp.compEdgeDelRoundAddr mW K ∧
      inp.compEdgeDelRoundAddr mW K ≤ inp.vHeadAddr mW K ∧
      inp.vHeadAddr mW K + inp.H'.n ≤ inp.nodesAddr mW K ∧
      2 * inp.J.m ≤ inp.nodesAddr mW K ∧ inp.H'.n ≤ inp.nodesAddr mW K :=
    t2_v1_le_compEdgeBase ctx
  have hnodes_lt_w : inp.nodesAddr mW K + 3 * inp.embVertSum < 2 ^ w := hMax
  have hprep_ptrs := t2_prep_comp_ptrs_le ctx hci
  have hfr_lo : ∀ a < inp.v1 + 32, st.mem a = memStart a := fun a ha =>
    hfr a (Or.inl (show a < inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length by
      have := t2_v1_le_compEdgeBase ctx; omega))
  have heJ_val : st.mem (ctx.wInp.prep.cJOrigPtr ci + b) = eJ := by
    have hcomp_orig := (t2_prep_cJSub_m_eq ctx hci).2.1
    have hlat := (hCompsStart ci hci_r).2.2.2.2.2.2.2.2.1
    have ho : b < (ctx.wInp.prep.cJOrig ctx.wInp.prep.rawComps[ci]).length := by
      have hprops := ctx.hw_okW.comp_props ci hci
      rw [← hcomp_orig, hprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hb
    rw [hfr_lo _ (by omega)]
    have hrc_eq : ctx.wInp.prep.rawComps[ci]! = ctx.wInp.prep.rawComps[ci] :=
      getElem!_pos ctx.wInp.prep.rawComps ci hci_r
    have hlat' : ListAt memStart (ctx.wInp.prep.cJOrigPtr ci)
        (ctx.wInp.prep.cJOrig ctx.wInp.prep.rawComps[ci]) := hrc_eq ▸ hlat
    have hget := hlat'.getElem ho
    simpa only [eJ, hcomp_orig, List.getD_eq_getElem _ _ ho] using hget
  have heJ_lt : eJ < inp.J.m := by
    have hprops := ctx.hw_okW.comp_props ci hci
    have ho : b < ctx.wd.comps[ci].jSubOrigEdges.length := by
      rw [hprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hb
    have hmem : eJ ∈ ctx.wd.comps[ci].jSubOrigEdges := by
      dsimp only [eJ]; rw [List.getD_eq_getElem _ _ ho]; exact List.getElem_mem ho
    exact ctx.hWInpJ ▸ hprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 eJ hmem
  set walkPtr := memStart (inp.embJHAddr + eJ)
  have hWalkAt0 : WalkAt memStart walkPtr (inp.embJH eJ) := hEmbStart eJ heJ_lt
  have hWalkBnd : walkPtr + (Walk.encode (inp.embJH eJ)).length ≤ inp.t1OutAddr :=
    hEmbBnd.2 eJ heJ_lt
  have hwalkPtr_val : st.mem (inp.embJHAddr + eJ) = walkPtr :=
    hfr_lo _ (by have := hEmbBnd.1; omega)
  have hvertsLen_val : st.mem walkPtr = vertsLen := by
    rw [hfr_lo _ (by have := walk_encode_length (inp.embJH eJ); omega)]
    exact hWalkAt0.verts_len
  have hvertsLen_le : vertsLen ≤ inp.embVertSum :=
    Finset.single_le_sum (f := fun e => (inp.embJH e).verts.length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr heJ_lt)
  have heJ_w : eJ < 2 ^ w := by omega
  have hvertsLen_w : vertsLen < 2 ^ w := by omega
  have hcjp_w : ctx.wInp.prep.cJOrigPtr ci + b < 2 ^ w := by omega
  have hwp_w : walkPtr < 2 ^ w := by omega
  have hembAddr_lt_w : inp.embJHAddr + eJ < 2 ^ w := by have := hEmbBnd.1; omega
  suffices hres : ∃ o st' c, Runs w p ω
      (Stmt.assign 18 (t2Ld (.reg 15) (.reg 17)) ;;
       Stmt.assign 19 (t2Ld (.reg 7) (.reg 18)) ;;
       Stmt.assign 20 (.load (.reg 19)) ;;
       forRange 21 (.const 0) (.reg 20) (
         Stmt.assign 22 (t2Ld (.reg 19) (t2Add (.const 1) (.reg 21))) ;;
         Stmt.assign 23 (t2Ld (.reg 8) (.reg 22)) ;;
         Stmt.store (.reg 11) (.reg 12) ;;
         t2St (.reg 11) (.const 1) (.reg 17) ;;
         t2St (.reg 11) (.const 2) (.reg 23) ;;
         t2St (.reg 8) (.reg 22) (.reg 11) ;;
         Stmt.assign 11 (t2Add (.reg 11) (.const 3))
       )) st o st' c ∧
      normalPost (fun st₁ =>
        (T2IncInv ctx memStart (ci + 1) ci (b + 1) 0
          { st₁ with regs := Function.update st₁.regs 17 (b + 1) } ∧
          st₁.regs 12 = ci ∧ st₁.regs 15 = ctx.wInp.prep.cJOrigPtr ci ∧
          st₁.regs 16 = ctx.wd.comps[ci].J_sub.m) ∧
        st₁.regs 17 = b) o st' ∧ 0 + c ≤ 49 * vertsLen + 23 by
    simpa only [Nat.zero_add] using hres
  refine runs_seq_assign_le (v := eJ)
    (ev_load (ev_add (ev_reg hr15 (by omega)) (ev_reg hr17 (by omega)) hcjp_w) heJ_val heJ_w) ?_
  set r18 := Function.update st.regs 18 eJ
  refine runs_seq_assign_le (v := walkPtr)
    (ev_load (ev_add (ev_reg (r := 7) (by simp [r18, hr7]) (by omega))
      (ev_reg (r := 18) (by simp [r18]) heJ_w) hembAddr_lt_w)
      hwalkPtr_val hwp_w) ?_
  set r19 := Function.update r18 19 walkPtr
  refine runs_seq_assign_le (v := vertsLen)
    (ev_load (ev_reg (r := 19) (by simp [r19]) hwp_w) hvertsLen_val hvertsLen_w) ?_
  set r20 := Function.update r19 20 vertsLen
  let InvJ := fun j (s : State) =>
    T2IncInv ctx memStart (ci + 1) ci b j s ∧
    s.regs 12 = ci ∧ s.regs 15 = ctx.wInp.prep.cJOrigPtr ci ∧
    s.regs 16 = ctx.wd.comps[ci].J_sub.m ∧ s.regs 17 = b ∧ s.regs 21 = j ∧
    s.regs 19 = walkPtr ∧ s.regs 20 = vertsLen
  have hloop := (Triple.forRange_const (p := p) (P := fun st_ => st_ = { st with regs := r20 })
    (Inv := InvJ) 40 0 vertsLen (Nat.zero_le _) hW
    (fun _ => hvertsLen_w)
    (fun s hs => by
      subst hs
      refine ⟨ev_const (Nat.zero_lt_of_lt hW), ?_, by simp [r20, r19, r18, hr12],
        by simp [r20, r19, r18, hr15], by simp [r20, r19, r18, hr16],
        by simp [r20, r19, r18, hr17], rfl, by simp [r20, r19], by simp [r20]⟩
      refine ⟨by simp [r20, r19, r18, hr0], by simp [r20, r19, r18, hr2],
        by simpa [r20, r19, r18] using hr3, by simp [r20, r19, r18, hr4],
        by simpa [r20, r19, r18] using hr5, by simpa [r20, r19, r18] using hr6,
        by simp [r20, r19, r18, hr7], by simpa [r20, r19, r18] using hr8,
        by simp [r20, r19, r18, hr9], by simp [r20, r19, r18, hr10],
        hptr_lo, by simpa [r20, r19, r18] using hptr_hi, hzf, hfr, hceb, hvho, hInc⟩)
    (fun j s _ _ h => h.2.2.2.2.2.1)
    (fun j s _ _ h => ev_reg h.2.2.2.2.2.2.2 hvertsLen_w)
    (fun j _ hj => (t2BuildInc_inner_step ctx hci hb hEmbStart hEmbBnd hW hMax hj).conseq
      (fun s hs => ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1,
        hs.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2⟩)
      (fun o s ho => by
        cases o with
        | normal =>
          rcases ho with ⟨⟨hinv', h12, h15, h16, h17, h19, h20⟩, h21⟩
          exact ⟨⟨hinv', h12, h15, h16, h17, by simp, h19, h20⟩, h21⟩
        | returned _ => exact ho)
      (fun _ _ => le_refl _)))
  obtain ⟨o, st₁, c_loop, hr_loop, hq_loop, hc_loop⟩ := hloop { st with regs := r20 } ω rfl
  cases o with
  | returned _ => exact False.elim hq_loop
  | normal =>
    rcases hq_loop with ⟨⟨h0, h2, h3, h4, h5, h6, h7, h8, h9, h10, hlo, hhi, hzf', hfr', hceb',
      hvho', hInc'⟩, h12, h15', h16', h17', _, _, _⟩
    simp only [Expr.size] at hc_loop ⊢
    refine ⟨.normal, st₁, c_loop, hr_loop, ?_, by omega⟩
    refine ⟨⟨⟨by simp [h0], by simp [h2], by simpa using h3, by simp [h4], by simpa using h5,
      by simpa using h6, by simp [h7], by simpa using h8, by simp [h9], by simp [h10], hlo, ?_,
      hzf', hfr', hceb', hvho', ?_⟩, by simp [h12], by simp [h15'], by simp [h16']⟩, h17'⟩
    · exact le_trans hhi (Nat.add_le_add_left (Nat.mul_le_mul_left 3 (t2PrefixVerts_add_j hci (le_refl _))) _)
    · exact incListForPairs_mono hInc' (fun _ _ => rfl) (fun _ _ _ => rfl)
        (fun _ _ _ hp => t2DonePred_b_step hci hp)

end MinCostFlow.Spanner
