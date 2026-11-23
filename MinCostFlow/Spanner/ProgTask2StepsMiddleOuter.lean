module

public import MinCostFlow.Spanner.ProgTask2StepsMiddleOuterMath

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Word-RAM `outerEdges` `forRange` loop spec for `t2MiddleEdgeBody` -/

lemma t2Middle_outerEdges_forRange {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {g₀ : T2Ghost impl.pathDS} {memStart : ℕ → ℕ} (hS : T2StepInv ctx stc g₀ memStart)
    {ci eL eW : ℕ} (hci : ci < ctx.wd.comps.length)
    (heL : eL < (ctx.wd.comps[ci]'hci).W_sub.m)
    (heW_eq : eW = (ctx.wd.comps[ci]'hci).wStart + eL)
    (msf : MiddleStaticFacts ctx stc g₀ ci eL eW memStart)
    {hCurNew arena0 u_loc v_loc : ℕ} {P_sub : Walk}
    (hcw_sub : P_sub.IsWalk (ctx.wd.comps[ci]'hci).J_sub u_loc v_loc)
    (hPsub_nd : P_sub.verts.Nodup)
    (hPsub_le_γ : P_sub.edges.length ≤ ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params)
    (mem : ℕ → ℕ)
    (hwk_sub : WalkAt mem g₀.hCur P_sub) (hz_new : WordRAM.ZeroFrom mem hCurNew)
    (hCur_le : g₀.hCur ≤ hCurNew) (hCur_hi : hCurNew ≤ Task2Input.maxHeapEnd impl inp)
    (hds_hCur : stc.dsBaseAddr ≤ g₀.hCur)
    (har_lo : stc.nodesEnd ≤ arena0)
    (har_hi : arena0 + 2 + P_sub.verts.length + P_sub.edges.length ≤ stc.dsBaseAddr)
    (hmem_agr : ∀ a < stc.dsBaseAddr, a ≠ inp.v1 + 26 →
      ¬(arena0 ≤ a ∧ a ≤ arena0 + 1 + P_sub.verts.length) → mem a = memStart a)
    (hr_init : ℕ → ℕ)
    (hr9 : hr_init 9 = msf.cJOrigPtr) (hr20 : hr_init 20 = g₀.hCur + 1 + P_sub.verts.length)
    (hr21 : hr_init 21 = P_sub.edges.length) (hr24 : hr_init 24 = arena0 + 1 + P_sub.verts.length)
    (hr25 : hr_init 25 = g₀.queryId + 1) (hr26 : hr_init 26 = memStart (msf.wWNumAddr + eW))
    (hr27 : hr_init 27 = inp.embJHAddr)
    (hr28 : hr_init 28 = inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (hr29 : hr_init 29 = inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length)
    (hr30 : hr_init 30 = inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (hr31 : hr_init 31 = memStart (inp.v1 + 28)) (hr32 : hr_init 32 = g₀.η₁)
    (hr33 : hr_init 33 = inp.queueAddr ctx.wd.W.m ctx.wd.comps.length)
    (hr34 : hr_init 34 = 0) (hr35 : hr_init 35 = 0)
    (pos₀ : ℕ) (ω : ℕ → Bool) :
    let c := ctx.wd.comps[ci]'hci
    let P_J := liftJSubWalk c P_sub
    let vcA := inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length
    let psA := inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length
    let ewA := inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length
    let qA := inp.queueAddr ctx.wd.W.m ctx.wd.comps.length
    let vcong0 := fun x => memStart (vcA + x)
    let wVal := memStart (msf.wWNumAddr + eW)
    let innerBody :=
      Stmt.assign 41 (t2Ld (.reg 38) (t2Add (.const 1) (.reg 40))) ;;
      Stmt.cond (t2Ne (t2Ld (.reg 28) (.reg 41)) (.reg 25)) (
        t2St (.reg 28) (.reg 41) (.reg 25) ;;
        Stmt.assign 42 (t2Add (t2Ld (.reg 29) (.reg 41)) (.reg 26)) ;;
        t2St (.reg 29) (.reg 41) (.reg 42) ;;
        Stmt.cond (t2Lt (t2Ld (.reg 30) (.reg 41)) (.reg 32)) (
          Stmt.cond (t2Le (.reg 31) (.reg 42)) (
            t2St (.reg 30) (.reg 41) (.reg 32) ;;
            t2St (.reg 33) (.reg 34) (.reg 41) ;;
            Stmt.assign 34 (t2Add (.reg 34) (.const 1))
          ) Stmt.nop
        ) Stmt.nop
      ) Stmt.nop
    let outerBody :=
      Stmt.assign 36 (t2Ld (.reg 20) (t2Add (.const 1) (.reg 22))) ;;
      Stmt.assign 37 (t2Ld (.reg 9) (.reg 36)) ;;
      t2St (.reg 24) (t2Add (.const 1) (.reg 22)) (.reg 37) ;;
      Stmt.assign 38 (t2Ld (.reg 27) (.reg 37)) ;;
      Stmt.assign 39 (.load (.reg 38)) ;;
      Stmt.assign 35 (t2Add (.reg 35) (.reg 39)) ;;
      forRange 40 (.const 0) (.reg 39) innerBody
    let res := t2MiddleOuterFold inp.embJH g₀.procVerts vcong0 (memStart (inp.v1 + 28)) wVal
      c.jSubOrigEdges P_sub.edges P_sub.edges.length
    let updV := t2MiddleUpdVerts inp.embJH c.jSubOrigEdges P_sub.edges P_sub.edges.length
    ∃ st' c_run,
      Runs w p ω (forRange 22 (.const 0) (.reg 21) outerBody) ⟨mem, hr_init, pos₀⟩ .normal st' c_run ∧
      (∀ r ≤ 21, st'.regs r = hr_init r) ∧
      st'.regs 24 = arena0 + 1 + P_sub.verts.length ∧
      st'.regs 34 = res.2.length ∧
      st'.regs 35 = updV ∧
      (∀ a, ¬(arena0 + 2 + P_sub.verts.length ≤ a ∧ a < arena0 + 2 + P_sub.verts.length + P_sub.edges.length) →
        ¬(vcA ≤ a ∧ a < qA + inp.H'.n) → st'.mem a = mem a) ∧
      (∀ k < P_sub.edges.length, st'.mem (arena0 + 2 + P_sub.verts.length + k) = P_J.edges.getD k 0) ∧
      (∀ x, x ∈ res.1 ↔ ∃ j ∈ P_J.edges, x ∈ (inp.embJH j).verts) ∧
      res.1 ⊆ Finset.range inp.H'.n ∧
      res.2.toFinset ⊆ res.1 ∧
      res.2.Nodup ∧
      (∀ x, x ∈ res.2 ↔ x ∈ res.1 ∧ x ∉ g₀.procVerts ∧ memStart (inp.v1 + 28) ≤ vcong0 x + wVal) ∧
      (∀ x < inp.H'.n, st'.mem (ewA + x) = if x ∈ res.1 then g₀.queryId + 1 else memStart (ewA + x)) ∧
      (∀ x < inp.H'.n, st'.mem (vcA + x) = vcong0 x + (if x ∈ res.1 then wVal else 0)) ∧
      (∀ x < inp.H'.n, st'.mem (psA + x) = if x ∈ res.2 then g₀.η₁ else memStart (psA + x)) ∧
      (∀ (k : ℕ) (hk : k < res.2.length), st'.mem (qA + k) = res.2[k]'hk) ∧
      updV ≤ P_sub.edges.length * (length inp.J inp.embJH + 1) ∧
      c_run ≤ P_sub.edges.length * ((length inp.J inp.embJH + 1) * 75 + 55) + 7 := by
  intro c P_J vcA psA ewA qA vcong0 wVal innerBody outerBody res updV
  have db := msf.db
  have _ := db.e_v1; have _ := db.e_emb; have _ := db.e_hdl; have _ := db.e_ceb; have _ := db.e_vho
  have _ := db.e_del; have _ := db.e_vh; have _ := db.e_vhd
  have _ := db.e_vc; have _ := db.e_ps; have _ := db.e_ew; have _ := db.e_q
  have _ := db.h_nlo; have _ := db.h_nds; have _ := db.h_dsc; have _ := db.h_stc; have _ := db.h_mhe
  have hmwb := db.h_mwb
  have hw1 := db.h_w1
  have hmax3 := msf.hmax_3
  have hwk_bd := t2_walkAt_add_le hcw_sub hPsub_nd hwk_sub hz_new hCur_le
  have hjOrig := (ctx.hw_okW.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hc_olen_c : c.jSubOrigEdges.length = c.J_sub.m := hjOrig.1
  have hc_orig_J : ∀ j ∈ c.jSubOrigEdges, j < inp.J.m := fun j hj => by
    rw [← ctx.hWInpJ]; exact hjOrig.2.2.1 j hj
  have h_orig : ∀ k < P_sub.edges.length,
      c.jSubOrigEdges.getD (P_sub.edges.getD k 0) 0 < inp.J.m := by
    intro k hk
    have hmem : P_sub.edges.getD k 0 ∈ P_sub.edges := by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have he_lt : P_sub.edges.getD k 0 < c.J_sub.m := by
      rcases hcw_sub with ⟨_, _, ⟨_, hpe, _⟩ | ⟨_, _, _, _, he, _⟩⟩
      · simp [hpe] at hk
      · exact he _ hmem
    have he_ol : P_sub.edges.getD k 0 < c.jSubOrigEdges.length := hc_olen_c ▸ he_lt
    rw [List.getD_eq_getElem _ _ he_ol]
    exact hc_orig_J _ (List.getElem_mem he_ol)
  have hH_valid : inp.H'.IsValid := ctx.hH'
  have hJH : IsEmbedding inp.J inp.H' inp.embJH := ctx.hembJH
  have hlen_H_w : inp.H'.n < 2 ^ w := by omega
  have hlen_edges_w : P_sub.edges.length < 2 ^ w := by omega
  have hv1_w : inp.v1 < 2 ^ w := by omega
  have ht1_v1 : inp.t1OutAddr ≤ inp.v1 := msf.ht1_v1
  have hv1_vcA : inp.v1 + 32 ≤ vcA := by dsimp only [vcA]; omega
  have hvc_ps : vcA + inp.H'.n = psA := db.e_vc
  have hps_ew : psA + inp.H'.n = ewA := db.e_ps
  have hew_q : ewA + inp.H'.n = qA := db.e_ew
  have hq_ar : qA + inp.H'.n ≤ arena0 := by
    have : qA + inp.H'.n = inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length := db.e_q
    omega
  have har_hCur : arena0 + 2 + P_sub.verts.length + P_sub.edges.length ≤ g₀.hCur :=
    le_trans har_hi hds_hCur
  have hCurNew_w : hCurNew < 2 ^ w := by omega
  have h_upd_cap : P_sub.edges.length * (length inp.J inp.embJH + 1) ≤
      ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params * (length inp.J inp.embJH + 1) :=
    Nat.mul_le_mul_right _ hPsub_le_γ
  have h_upd_w : P_sub.edges.length * (length inp.J inp.embJH + 1) < 2 ^ w := by
    have h1 := msf.hup_w
    exact Nat.lt_of_le_of_lt (le_trans (Nat.le_trans h_upd_cap (Nat.le_add_left _ _)) h1) hmwb
  have hcJ_ptrs := t2_prep_comp_ptrs_le ctx hci
  have hcJ_v1 : msf.cJOrigPtr + c.J_sub.m ≤ inp.v1 := by
    have heq1 : msf.cJOrigPtr = ctx.wInp.prep.cJOrigPtr ci := by
      have hcd := (ctx.agrees_preserves_static hS.agr_pre).2.2.2.2.2.1
      have hlen_r := ctx.wInp.buildCompsFrom_length ctx.wInp.prep.j0Edges.length ctx.wInp.prep.rawComps ctx.WSubs ctx.hws.1
      have hci_r : ci < ctx.wInp.prep.rawComps.length := by
        simpa [T2Ctx.wd, WitnessCoreInput.mkWitnessData, hlen_r] using hci
      have h1 := (hcd ci hci_r).2.2.2.2.1
      have ha1 := (ctx.agrees_preserves_static hS.agr_pre).2.2.2.2.1.2.2.2.2.1
      have haC : msf.aComps = ctx.wInp.prep.aComps := by
        rw [← msf.haComps_ptr]; exact ha1
      rw [← msf.hcJOrig_ptr, haC]; exact h1
    have hch := t2_prep_chain_bounds ctx
    rw [heq1]; exact le_trans hcJ_ptrs.2 hch.2.2.2
  have hcJ_ar : msf.cJOrigPtr + c.J_sub.m ≤ arena0 := by omega
  let foldK := fun k => t2MiddleOuterFold inp.embJH g₀.procVerts vcong0 (memStart (inp.v1 + 28)) wVal
    c.jSubOrigEdges P_sub.edges k
  let updK := fun k => t2MiddleUpdVerts inp.embJH c.jSubOrigEdges P_sub.edges k
  let stepBound := (length inp.J inp.embJH + 1) * 75 + 46
  let Inv : ℕ → State → Prop := fun k st =>
    (∀ r ≤ 21, st.regs r = hr_init r) ∧ st.regs 22 = k ∧
    st.regs 24 = arena0 + 1 + P_sub.verts.length ∧
    (∀ r, 25 ≤ r → r ≤ 33 → st.regs r = hr_init r) ∧
    st.regs 34 = (foldK k).2.length ∧
    st.regs 35 = updK k ∧
    (∀ a, ¬(arena0 + 2 + P_sub.verts.length ≤ a ∧ a < arena0 + 2 + P_sub.verts.length + P_sub.edges.length) →
      ¬(vcA ≤ a ∧ a < qA + inp.H'.n) → st.mem a = mem a) ∧
    (∀ idx < k, st.mem (arena0 + 2 + P_sub.verts.length + idx) = P_J.edges.getD idx 0) ∧
    (∀ x, x ∈ (foldK k).1 ↔ ∃ idx < k, x ∈ (inp.embJH (P_J.edges.getD idx 0)).verts) ∧
    (foldK k).1 ⊆ Finset.range inp.H'.n ∧
    (foldK k).2.toFinset ⊆ (foldK k).1 ∧
    (foldK k).2.Nodup ∧
    (∀ x, x ∈ (foldK k).2 ↔ x ∈ (foldK k).1 ∧ x ∉ g₀.procVerts ∧ memStart (inp.v1 + 28) ≤ vcong0 x + wVal) ∧
    (∀ x < inp.H'.n, st.mem (ewA + x) = if x ∈ (foldK k).1 then g₀.queryId + 1 else memStart (ewA + x)) ∧
    (∀ x < inp.H'.n, st.mem (vcA + x) = vcong0 x + (if x ∈ (foldK k).1 then wVal else 0)) ∧
    (∀ x < inp.H'.n, st.mem (psA + x) = if x ∈ (foldK k).2 then g₀.η₁ else memStart (psA + x)) ∧
    (∀ (idx : ℕ) (hidx : idx < (foldK k).2.length), st.mem (qA + idx) = (foldK k).2[idx]'hidx)
  let P0 : State → Prop := fun st =>
    (∀ r ≤ 39, st.regs r = hr_init r) ∧
    st.mem = mem
  have hmem_ew0 : ∀ x < inp.H'.n, mem (ewA + x) = memStart (ewA + x) := fun x hx =>
    hmem_agr _ (by omega) (by omega) (by omega)
  have hmem_vc0 : ∀ x < inp.H'.n, mem (vcA + x) = vcong0 x := fun x hx =>
    hmem_agr _ (by omega) (by omega) (by omega)
  have hmem_ps0 : ∀ x < inp.H'.n, mem (psA + x) = memStart (psA + x) := fun x hx =>
    hmem_agr _ (by omega) (by omega) (by omega)
  have htrip : Triple w p P0 (forRange 22 (.const 0) (.reg 21) outerBody)
      (normalPost (Inv P_sub.edges.length)) (fun _ => P_sub.edges.length * (stepBound + 9) + 7) := by
    have hfor := Triple.forRange_const (w := w) (p := p) (P := P0) (r := 22) (lo := .const 0)
      (hi := .reg 21) (body := outerBody) (Inv := Inv) (stepBound := stepBound) (loVal := 0)
      (hiVal := P_sub.edges.length) (Nat.zero_le _) hw1 (fun _ => hlen_edges_w)
      (fun st hP0 => by
        refine ⟨Expr.eval_const (by omega), ?_⟩
        rcases hP0 with ⟨hr, hmem_eq⟩
        refine ⟨fun r hr_le => ?_, by simp, ?_, fun r hr1 hr2 => ?_, ?_, ?_,
          fun a _ _ => congrFun hmem_eq a,
          fun _ hk => by omega, ?_, Finset.empty_subset _, Finset.Subset.rfl, List.nodup_nil,
          ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun idx hidx => ?_⟩
        · dsimp only; rw [Function.update_of_ne (by omega)]; exact hr r (by omega)
        · dsimp only; rw [Function.update_of_ne (by omega)]; exact (hr 24 (by omega)).trans hr24
        · dsimp only; rw [Function.update_of_ne (by omega)]; exact hr r (by omega)
        · simp [foldK, t2MiddleOuterFold, (hr 34 (by omega)).trans hr34]
        · simp [updK, t2MiddleUpdVerts, (hr 35 (by omega)).trans hr35]
        · simp [foldK, t2MiddleOuterFold]
        · simp [foldK, t2MiddleOuterFold]
        · simp only [foldK, t2MiddleOuterFold, List.range_zero, List.foldl_nil, Finset.notMem_empty, ↓reduceIte]
          rw [hmem_eq]; exact hmem_ew0 x hx
        · simp only [foldK, t2MiddleOuterFold, List.range_zero, List.foldl_nil, Finset.notMem_empty, ↓reduceIte, add_zero]
          rw [hmem_eq]; exact hmem_vc0 x hx
        · simp only [foldK, t2MiddleOuterFold, List.range_zero, List.foldl_nil, List.not_mem_nil, ↓reduceIte]
          rw [hmem_eq]; exact hmem_ps0 x hx
        · simp [foldK, t2MiddleOuterFold] at hidx)
      (fun k _ _ _ hI => hI.2.1)
      (fun k st _ _ hI => Expr.eval_reg_of_eq ((hI.1 21 (by omega)).trans hr21))
      fun k _ hk => by
        intro st ω_run hI
        rcases hI with ⟨hregs_lo, hr22, hr24_eq, hregs_hi, hr34_eq, hr35_eq, hagr,
          hm_edges_k, hF1_eq, hF1_sub, hF2_sub, hF2_nd, hF2_spec, hm_ew_k, hm_vc_k, hm_ps_k, hm_q_k⟩
        have he_pos : P_sub.edges.length ≥ 1 := by omega
        set eL_edge := P_sub.edges[k]'hk
        set eJ := c.jSubOrigEdges.getD eL_edge 0
        have heL_lt : eL_edge < c.J_sub.m := by
          rcases hcw_sub with ⟨_, _, ⟨_, hpe, _⟩ | ⟨_, _, _, _, he, _⟩⟩
          · simp [hpe] at hk
          · exact he _ (List.getElem_mem hk)
        have heJ_eq : eJ = c.jSubOrigEdges[eL_edge]'(hc_olen_c ▸ heL_lt) :=
          List.getD_eq_getElem _ _ (hc_olen_c ▸ heL_lt)
        have heJ_lt : eJ < inp.J.m := hc_orig_J _ (heJ_eq ▸ List.getElem_mem (hc_olen_c ▸ heL_lt))
        have hPJ_k : P_J.edges.getD k 0 = eJ := by
          have hk_PJ : k < P_J.edges.length := by simpa [P_J, liftJSubWalk] using hk
          rw [List.getD_eq_getElem _ _ hk_PJ]
          simp [P_J, liftJSubWalk, eJ, eL_edge]
        have heL_w : eL_edge < 2 ^ w := by omega
        have heJ_w : eJ < 2 ^ w := by omega
        have hsrc_e_le : g₀.hCur + 2 + P_sub.verts.length + k ≤ hCurNew :=
          (hwk_bd.2.2.2 he_pos).2 k hk
        have hsrc_e_w : g₀.hCur + 1 + P_sub.verts.length + (1 + k) < 2 ^ w := by omega
        have hm_eL : st.mem (g₀.hCur + 1 + P_sub.verts.length + (1 + k)) = eL_edge := by
          rw [hagr _ (by omega) (by omega),
            show g₀.hCur + 1 + P_sub.verts.length + (1 + k) =
              g₀.hCur + 2 + P_sub.verts.length + k by omega]
          exact hwk_sub.edges_listAt k hk
        have hs1 : Runs w p ω_run (Stmt.assign 36 (t2Ld (.reg 20) (t2Add (.const 1) (.reg 22)))) st .normal
            { st with regs := Function.update st.regs 36 eL_edge } 7 := by
          have ha1 := Expr.eval_add (w := w) (Expr.eval_const hw1) (Expr.eval_reg_of_eq hr22) (by omega)
          have ha2 := Expr.eval_add (w := w) (Expr.eval_reg_of_eq ((hregs_lo 20 (by omega)).trans hr20)) ha1 hsrc_e_w
          exact runs_assign_iff.mpr ⟨eL_edge, by simpa only [t2Ld, hm_eL] using Expr.eval_load ha2,
            rfl, rfl, by simp [Expr.size]⟩
        set st1 : State := { st with regs := Function.update st.regs 36 eL_edge }
        have hr1_lo : ∀ r ≤ 24, st1.regs r = st.regs r := fun r hr => by
          dsimp only [st1]; rw [Function.update_of_ne (by omega)]
        have hr1_hi : ∀ r, 25 ≤ r → r ≤ 35 → st1.regs r = st.regs r := fun r h1 h2 => by
          dsimp only [st1]; rw [Function.update_of_ne (by omega)]
        have hm_orig : st1.mem (msf.cJOrigPtr + eL_edge) = eJ := by
          change st.mem (msf.cJOrigPtr + eL_edge) = eJ
          rw [hagr _ (by omega) (by omega), hmem_agr _ (by omega) (by omega) (by omega)]
          have hcJ := msf.hcJOrig_list
          rw [List.getD_eq_getElem _ _ hci] at hcJ
          simpa [heJ_eq] using hcJ eL_edge (hc_olen_c ▸ heL_lt)
        have hs2 : Runs w p ω_run (Stmt.assign 37 (t2Ld (.reg 9) (.reg 36))) st1 .normal
            { st1 with regs := Function.update st1.regs 37 eJ } 5 := by
          have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq ((hr1_lo 9 (by omega)).trans ((hregs_lo 9 (by omega)).trans hr9)))
            (Expr.eval_reg_of_eq (show st1.regs 36 = eL_edge by simp [st1])) (by omega)
          exact runs_assign_iff.mpr ⟨eJ, by simpa only [t2Ld, hm_orig] using Expr.eval_load ha,
            rfl, rfl, by simp [Expr.size]⟩
        set st2 : State := { st1 with regs := Function.update st1.regs 37 eJ }
        have hr2_lo : ∀ r ≤ 24, st2.regs r = st.regs r := fun r hr => by
          dsimp only [st2]; rw [Function.update_of_ne (by omega)]; exact hr1_lo r hr
        have hr2_hi : ∀ r, 25 ≤ r → r ≤ 35 → st2.regs r = st.regs r := fun r h1 h2 => by
          dsimp only [st2]; rw [Function.update_of_ne (by omega)]; exact hr1_hi r h1 h2
        have har_e_w : arena0 + 1 + P_sub.verts.length + (1 + k) < 2 ^ w := by omega
        have hs3 : Runs w p ω_run (t2St (.reg 24) (t2Add (.const 1) (.reg 22)) (.reg 37)) st2 .normal
            { st2 with mem := Function.update st2.mem (arena0 + 1 + P_sub.verts.length + (1 + k)) eJ } 7 := by
          have ha1 := Expr.eval_add (w := w) (Expr.eval_const hw1)
            (Expr.eval_reg_of_eq ((hr2_lo 22 (by omega)).trans hr22)) (by omega)
          have ha2 := Expr.eval_add (w := w) (Expr.eval_reg_of_eq ((hr2_lo 24 (by omega)).trans hr24_eq)) ha1 har_e_w
          have hv := Expr.eval_reg_of_eq (w := w) (show st2.regs 37 = eJ by simp [st2])
          exact runs_store_iff.mpr ⟨arena0 + 1 + P_sub.verts.length + (1 + k), eJ, ha2, hv, rfl, rfl, by simp [Expr.size]⟩
        set st3 : State := { st2 with mem := Function.update st2.mem (arena0 + 1 + P_sub.verts.length + (1 + k)) eJ }
        have h_emb_ptr_w : inp.embJHAddr + eJ < inp.t1OutAddr := lt_of_lt_of_le (Nat.add_lt_add_left heJ_lt _) msf.hembJH_bd.1
        have h_walk_ptr : memStart (inp.embJHAddr + eJ) + (inp.embJH eJ).encode.length ≤ inp.t1OutAddr :=
          msf.hembJH_bd.2 eJ heJ_lt
        set walkPtr := memStart (inp.embJHAddr + eJ)
        have hwalk_lt_v1 : walkPtr + (inp.embJH eJ).encode.length ≤ inp.v1 :=
          le_trans h_walk_ptr ht1_v1
        have hm_emb_ptr : st3.mem (inp.embJHAddr + eJ) = walkPtr := by
          dsimp only [st3]
          rw [Function.update_of_ne (by omega)]
          change st.mem (inp.embJHAddr + eJ) = walkPtr
          rw [hagr _ (by omega) (by omega), hmem_agr _ (by omega) (by omega) (by omega)]
        have hemb_add_w : inp.embJHAddr + eJ < 2 ^ w :=
          lt_trans h_emb_ptr_w (lt_of_le_of_lt ht1_v1 hv1_w)
        have hs4 : Runs w p ω_run (Stmt.assign 38 (t2Ld (.reg 27) (.reg 37))) st3 .normal
            { st3 with regs := Function.update st3.regs 38 walkPtr } 5 := by
          have ha := Expr.eval_add (w := w)
            (Expr.eval_reg_of_eq (show st3.regs 27 = inp.embJHAddr from
              (hr2_hi 27 (by omega) (by omega)).trans ((hregs_hi 27 (by omega) (by omega)).trans hr27)))
            (Expr.eval_reg_of_eq (show st3.regs 37 = eJ by simp [st3, st2])) hemb_add_w
          exact runs_assign_iff.mpr ⟨walkPtr, by simpa only [t2Ld, hm_emb_ptr] using Expr.eval_load ha,
            rfl, rfl, by simp [Expr.size]⟩
        set st4 : State := { st3 with regs := Function.update st3.regs 38 walkPtr }
        have heVerts_lt : ∀ x ∈ (inp.embJH eJ).verts, x < inp.H'.n :=
          Walk.isWalk_verts_lt hH_valid (hJH.2 eJ heJ_lt)
        have heVerts_len_le : (inp.embJH eJ).verts.length ≤ length inp.J inp.embJH + 1 := by
          have := t2_isWalk_verts_length_le (hJH.2 eJ heJ_lt)
          have := edges_length_le_length inp.embJH heJ_lt
          omega
        have heVerts_len_w : (inp.embJH eJ).verts.length < 2 ^ w := by
          have hm : (inp.embJH eJ).verts.length ≤ P_sub.edges.length * (length inp.J inp.embJH + 1) := by
            calc (inp.embJH eJ).verts.length ≤ 1 * (length inp.J inp.embJH + 1) := by omega
              _ ≤ P_sub.edges.length * (length inp.J inp.embJH + 1) := Nat.mul_le_mul_right _ he_pos
          exact lt_of_le_of_lt hm h_upd_w
        have hwk_e : WalkAt memStart walkPtr (inp.embJH eJ) := msf.hembJH_at eJ heJ_lt
        have hm_vlen : st4.mem walkPtr = (inp.embJH eJ).verts.length := by
          dsimp only [st4, st3]
          rw [Function.update_of_ne (by omega)]
          change st.mem walkPtr = _
          rw [hagr _ (by omega) (by omega), hmem_agr _ (by omega) (by omega) (by omega)]
          exact hwk_e.verts_len
        have hs5 : Runs w p ω_run (Stmt.assign 39 (.load (.reg 38))) st4 .normal
            { st4 with regs := Function.update st4.regs 39 (inp.embJH eJ).verts.length } 3 := by
          have ha := Expr.eval_reg_of_eq (w := w) (show st4.regs 38 = walkPtr by simp [st4])
          exact runs_assign_iff.mpr ⟨(inp.embJH eJ).verts.length, by simpa only [hm_vlen] using Expr.eval_load ha,
            rfl, rfl, by simp [Expr.size]⟩
        set st5 : State := { st4 with regs := Function.update st4.regs 39 (inp.embJH eJ).verts.length }
        have hupd_le_k : updK k ≤ k * (length inp.J inp.embJH + 1) :=
          t2MiddleUpdVerts_le hJH h_orig k (Nat.le_of_lt hk)
        have hupd_next_w : updK k + (inp.embJH eJ).verts.length < 2 ^ w := by
          have h1 : updK k + (inp.embJH eJ).verts.length ≤ (k + 1) * (length inp.J inp.embJH + 1) := by
            rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_le_add hupd_le_k heVerts_len_le
          have h2 : (k + 1) * (length inp.J inp.embJH + 1) ≤ P_sub.edges.length * (length inp.J inp.embJH + 1) :=
            Nat.mul_le_mul_right _ hk
          exact lt_of_le_of_lt (le_trans h1 h2) h_upd_w
        have hr5_lo : ∀ r ≤ 24, st5.regs r = st.regs r := fun r hr => by
          dsimp only [st5, st4]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr2_lo r hr
        have hr5_hi : ∀ r, 25 ≤ r → r ≤ 35 → st5.regs r = st.regs r := fun r h1 h2 => by
          dsimp only [st5, st4]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr2_hi r h1 h2
        have hs6 : Runs w p ω_run (Stmt.assign 35 (t2Add (.reg 35) (.reg 39))) st5 .normal
            { st5 with regs := Function.update st5.regs 35 (updK k + (inp.embJH eJ).verts.length) } 4 := by
          have h35 : st5.regs 35 = updK k := (hr5_hi 35 (by omega) (by omega)).trans hr35_eq
          have h39 : st5.regs 39 = (inp.embJH eJ).verts.length := by simp [st5]
          have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq h35) (Expr.eval_reg_of_eq h39) hupd_next_w
          exact runs_assign_iff.mpr ⟨updK k + (inp.embJH eJ).verts.length, ha, rfl, rfl, by simp [Expr.size]⟩
        set st6 : State := { st5 with regs := Function.update st5.regs 35 (updK k + (inp.embJH eJ).verts.length) }
        have hr6_lo : ∀ r ≤ 24, st6.regs r = st.regs r := fun r hr => by
          dsimp only [st6]; rw [Function.update_of_ne (by omega)]; exact hr5_lo r hr
        have hr6_hi : ∀ r, 25 ≤ r → r ≤ 34 → st6.regs r = st.regs r := fun r h1 h2 => by
          dsimp only [st6]; rw [Function.update_of_ne (by omega)]; exact hr5_hi r h1 (by omega)
        have hvc_bd : ∀ x < inp.H'.n, vcong0 x + wVal < 2 ^ w := fun x hx => by
          have := msf.hVc_w x hx
          simpa [vcong0, wVal, msf.hwWNum_ptr] using this
        have hst6_agr_wk : ∀ j < (inp.embJH eJ).verts.length,
            st6.mem (walkPtr + 1 + j) = memStart (walkPtr + 1 + j) := fun j hj => by
          have hlen_enc : walkPtr + 1 + j < walkPtr + (inp.embJH eJ).encode.length := by
            rw [walk_encode_length]; omega
          dsimp only [st6, st5, st4, st3]
          rw [Function.update_of_ne (by omega)]
          change st.mem _ = memStart _
          rw [hagr _ (by omega) (by omega), hmem_agr _ (by omega) (by omega) (by omega)]
        have hst6_ew : ∀ x < inp.H'.n, st6.mem (ewA + x) =
            if x ∈ (foldK k).1 then g₀.queryId + 1 else memStart (ewA + x) := fun x hx => by
          dsimp only [st6, st5, st4, st3]
          rw [Function.update_of_ne (by omega)]
          exact hm_ew_k x hx
        have hst6_vc : ∀ x < inp.H'.n, st6.mem (vcA + x) =
            vcong0 x + (if x ∈ (foldK k).1 then wVal else 0) := fun x hx => by
          dsimp only [st6, st5, st4, st3]
          rw [Function.update_of_ne (by omega)]
          exact hm_vc_k x hx
        have hst6_ps : ∀ x < inp.H'.n, st6.mem (psA + x) =
            if x ∈ (foldK k).2 then g₀.η₁ else memStart (psA + x) := fun x hx => by
          dsimp only [st6, st5, st4, st3]
          rw [Function.update_of_ne (by omega)]
          exact hm_ps_k x hx
        have hst6_q : ∀ (idx : ℕ) (hidx : idx < (foldK k).2.length), st6.mem (qA + idx) = (foldK k).2[idx]'hidx := by
          intro idx hidx
          have hcard := Finset.card_le_card (Finset.Subset.trans hF2_sub hF1_sub)
          rw [List.toFinset_card_of_nodup hF2_nd, Finset.card_range] at hcard
          dsimp only [st6, st5, st4, st3]
          rw [Function.update_of_ne (by omega)]
          exact hm_q_k idx hidx
        obtain ⟨stF, c_inner, hr_inner, hregsF, hr34F, hagrF, hF1_in, hF1_sub_in, hF2_sub_in,
            hF2_nd_in, hF2_spec_in, hewF, hvcF, hpsF, hqF, hc_in⟩ :=
          t2Middle_innerVerts_forRange (p := p) ctx stc hS heJ_lt heVerts_lt heVerts_len_w hwk_e h_walk_ptr
            msf.ht1_v1 (foldK k).1 (foldK k).2 hF1_sub hF2_sub hF2_nd hF2_spec hvc_bd hlen_H_w hmwb
            hw1 st6.mem hst6_agr_wk hst6_ew hst6_vc hst6_ps hst6_q st6.regs
            ((hr6_hi 25 (by omega) (by omega)).trans ((hregs_hi 25 (by omega) (by omega)).trans hr25))
            ((hr6_hi 26 (by omega) (by omega)).trans ((hregs_hi 26 (by omega) (by omega)).trans hr26))
            ((hr6_hi 28 (by omega) (by omega)).trans ((hregs_hi 28 (by omega) (by omega)).trans hr28))
            ((hr6_hi 29 (by omega) (by omega)).trans ((hregs_hi 29 (by omega) (by omega)).trans hr29))
            ((hr6_hi 30 (by omega) (by omega)).trans ((hregs_hi 30 (by omega) (by omega)).trans hr30))
            ((hr6_hi 31 (by omega) (by omega)).trans ((hregs_hi 31 (by omega) (by omega)).trans hr31))
            ((hr6_hi 32 (by omega) (by omega)).trans ((hregs_hi 32 (by omega) (by omega)).trans hr32))
            ((hr6_hi 33 (by omega) (by omega)).trans ((hregs_hi 33 (by omega) (by omega)).trans hr33))
            ((hr6_hi 34 (by omega) (by omega)).trans hr34_eq)
            (show st6.regs 38 = walkPtr by dsimp only [st6, st5]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; simp [st4])
            (show st6.regs 39 = (inp.embJH eJ).verts.length by dsimp only [st6]; rw [Function.update_of_ne (by omega)]; simp [st5])
            st6.pos ω_run
        have hr_body : Runs w p ω_run outerBody st .normal stF (7 + 1 + 5 + 1 + 7 + 1 + 5 + 1 + 3 + 1 + 4 + 1 + c_inner) :=
          runs_seq_iff.mpr (Or.inr ⟨st1, 7, 5 + 1 + (7 + 1 + (5 + 1 + (3 + 1 + (4 + 1 + c_inner)))), hs1,
            runs_seq_iff.mpr (Or.inr ⟨st2, 5, 7 + 1 + (5 + 1 + (3 + 1 + (4 + 1 + c_inner))), hs2,
              runs_seq_iff.mpr (Or.inr ⟨st3, 7, 5 + 1 + (3 + 1 + (4 + 1 + c_inner)), hs3,
                runs_seq_iff.mpr (Or.inr ⟨st4, 5, 3 + 1 + (4 + 1 + c_inner), hs4,
                  runs_seq_iff.mpr (Or.inr ⟨st5, 3, 4 + 1 + c_inner, hs5,
                    runs_seq_iff.mpr (Or.inr ⟨st6, 4, c_inner, hs6, hr_inner, by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩)
        have hfold_succ : foldK (k + 1) = t2MiddleInnerFold inp.embJH g₀.procVerts vcong0 (memStart (inp.v1 + 28)) wVal eJ
            (inp.embJH eJ).verts.length (foldK k) := by
          dsimp only [foldK]; rw [t2MiddleOuterFold_step]
          have : P_sub.edges.getD k 0 = eL_edge := List.getD_eq_getElem _ _ hk
          simp only [this, eJ]
        have hupd_succ : updK (k + 1) = updK k + (inp.embJH eJ).verts.length := by
          dsimp only [updK]; rw [t2MiddleUpdVerts_step]
          have : P_sub.edges.getD k 0 = eL_edge := List.getD_eq_getElem _ _ hk
          simp only [this, eJ]
        have hstF_mem_out : ∀ a, ¬(vcA ≤ a ∧ a < qA + inp.H'.n) → stF.mem a = st3.mem a := fun a ha =>
          hagrF a ha
        have hrF22 : stF.regs 22 = k := (hregsF 22 (by omega) (by omega)).trans ((hr6_lo 22 (by omega)).trans hr22)
        refine ⟨.normal, stF, _, hr_body, ⟨?_, hrF22⟩, by
          dsimp only; have := Nat.mul_le_mul_right 75 heVerts_len_le; omega⟩
        refine ⟨fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact (hregsF r (by omega) (by omega)).trans ((hr6_lo r (by omega)).trans (hregs_lo r hr)),
          by simp,
          by dsimp only; rw [Function.update_of_ne (by omega)]; exact (hregsF 24 (by omega) (by omega)).trans ((hr6_lo 24 (by omega)).trans hr24_eq),
          fun r h1 h2 => by dsimp only; rw [Function.update_of_ne (by omega)]; exact (hregsF r (by omega) (by omega)).trans ((hr6_hi r h1 (by omega)).trans (hregs_hi r h1 h2)),
          by dsimp only; rw [Function.update_of_ne (by omega), hfold_succ]; exact hr34F,
          by dsimp only; rw [Function.update_of_ne (by omega), hupd_succ]; exact (hregsF 35 (by omega) (by omega)).trans (by simp [st6]),
          fun a ha1 ha2 => by
            rw [hstF_mem_out a ha2]
            dsimp only [st3]; rw [Function.update_of_ne (by omega)]
            exact hagr a ha1 ha2,
          fun idx hidx => by
            rw [hstF_mem_out _ (by omega)]
            dsimp only [st3]
            by_cases hik : idx = k
            · subst hik; rw [show arena0 + 2 + P_sub.verts.length + idx = arena0 + 1 + P_sub.verts.length + (1 + idx) by omega,
                Function.update_self, hPJ_k]
            · rw [Function.update_of_ne (by omega)]
              exact hm_edges_k idx (by omega),
          fun x => by
            rw [hfold_succ, hF1_in, Finset.mem_union, hF1_eq x, List.mem_toFinset]
            constructor
            · rintro (⟨idx, hi, hx⟩ | hx)
              · exact ⟨idx, by omega, hx⟩
              · exact ⟨k, by omega, by rwa [hPJ_k]⟩
            · rintro ⟨idx, hi, hx⟩
              by_cases hik : idx = k
              · subst hik; rw [hPJ_k] at hx; exact Or.inr hx
              · exact Or.inl ⟨idx, by omega, hx⟩,
          hfold_succ ▸ hF1_sub_in, hfold_succ ▸ hF2_sub_in, hfold_succ ▸ hF2_nd_in,
          fun x => by rw [hfold_succ]; exact hF2_spec_in x,
          fun x hx => by rw [hfold_succ]; exact hewF x hx,
          fun x hx => by rw [hfold_succ]; exact hvcF x hx,
          fun x hx => by rw [hfold_succ]; exact hpsF x hx,
          fun idx hidx => by simp only [hfold_succ] at hidx ⊢; exact hqF idx hidx⟩
    exact hfor.mono_cost fun _ _ => by
      simp only [Nat.sub_zero, Expr.size]
      rw [show stepBound + (1 + 8) = stepBound + 9 by omega]
  obtain ⟨o, st', c_run, hr, hq, hc⟩ := htrip ⟨mem, hr_init, pos₀⟩ ω
    ⟨fun _ _ => rfl, rfl⟩
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    rcases hq with ⟨hregs_lo, _, hr24_o, hregs_hi, hr34_o, hr35_o, hagr_o, hm_edges_o,
      hF1_o, hF1_sub_o, hF2_sub_o, hF2_nd_o, hF2_spec_o, hew_o, hvc_o, hps_o, hq_o⟩
    have hF1_mem : ∀ x, x ∈ res.1 ↔ ∃ j ∈ P_J.edges, x ∈ (inp.embJH j).verts := fun x => by
      rw [hF1_o x]
      constructor
      · rintro ⟨idx, hidx, hx⟩
        have hidx_PJ : idx < P_J.edges.length := by simpa [P_J, liftJSubWalk] using hidx
        rw [List.getD_eq_getElem _ _ hidx_PJ] at hx
        exact ⟨P_J.edges[idx]'hidx_PJ, List.getElem_mem hidx_PJ, hx⟩
      · rintro ⟨j, hj, hx⟩
        obtain ⟨idx, hidx_PJ, rfl⟩ := List.getElem_of_mem hj
        have hidx : idx < P_sub.edges.length := by simpa [P_J, liftJSubWalk] using hidx_PJ
        refine ⟨idx, hidx, ?_⟩
        rw [List.getD_eq_getElem _ _ hidx_PJ]; exact hx
    have hupd_le := t2MiddleUpdVerts_le hJH h_orig P_sub.edges.length le_rfl
    exact ⟨st', c_run, hr, hregs_lo, hr24_o, hr34_o, hr35_o, hagr_o, hm_edges_o,
      hF1_mem, hF1_sub_o, hF2_sub_o, hF2_nd_o, hF2_spec_o, hew_o, hvc_o, hps_o, hq_o,
      hupd_le, by dsimp only [stepBound] at hc; exact hc⟩

end MinCostFlow.Spanner
