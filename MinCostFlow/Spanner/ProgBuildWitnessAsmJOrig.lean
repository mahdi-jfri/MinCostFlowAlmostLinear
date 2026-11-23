module

public import MinCostFlow.Spanner.ProgBuildWitnessAsm

/-!
# Verification of Component Original-Edge Recording (`ProgBuildWitnessAsmJOrig`)

Verifies `buildCompJOrigBody` and `forRange 37 (.const 0) (.reg 32) buildCompJOrigBody`,
transitioning from `CompJOrigInv ... 0` to `AsmCompInv ... (ci + 1)`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited WitnessCoreInput

private lemma jOrig_updates_agree {m m' : ℕ → ℕ} (jSrcAddr eJ : ℕ)
    (hm_out : ∀ x, x ≠ jSrcAddr + 3 * eJ → x ≠ jSrcAddr + (3 * eJ + 1) →
      x ≠ jSrcAddr + (3 * eJ + 2) → m' x = m x) :
    (∀ x < jSrcAddr, m' x = m x) ∧
    (∀ eJ', eJ' ≠ eJ → ∀ t < 3, m' (jSrcAddr + 3 * eJ' + t) = m (jSrcAddr + 3 * eJ' + t)) ∧
    (∀ Jm x, jSrcAddr + 3 * Jm ≤ x → eJ < Jm → m' x = m x) :=
  ⟨fun x hx => hm_out x (by omega) (by omega) (by omega),
   fun eJ' hne t ht => hm_out _ (by omega) (by omega) (by omega),
   fun Jm x hx hej => hm_out x (by omega) (by omega) (by omega)⟩

private lemma jOrig_writes_cell (m : ℕ → ℕ) (jSrcAddr eJ ci jL : ℕ) :
    let m1 := Function.update (Function.update (Function.update m (jSrcAddr + 3 * eJ) 2)
      (jSrcAddr + (3 * eJ + 1)) ci) (jSrcAddr + (3 * eJ + 2)) jL
    m1 (jSrcAddr + 3 * eJ) = 2 ∧ m1 (jSrcAddr + 3 * eJ + 1) = ci ∧ m1 (jSrcAddr + 3 * eJ + 2) = jL := by
  intro m1
  dsimp only [m1]
  refine ⟨?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_of_ne (by omega),
      show jSrcAddr + 3 * eJ + 1 = jSrcAddr + (3 * eJ + 1) by omega, Function.update_self]
  · rw [show jSrcAddr + 3 * eJ + 2 = jSrcAddr + (3 * eJ + 2) by omega, Function.update_self]

private theorem buildCompJOrigBody_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {mem₀ : ℕ → ℕ} {WSubs : List Graph} {aCompExt wAddr ci jL : ℕ}
    (hvalid : inp.Valid ce pds mem₀ w) (hci : ci < inp.prep.rawComps.length) :
    let wd := inp.mkWitnessData ce pds WSubs
    let comp := wd.comps.getD ci defaultCompInfo
    Triple w p
      (fun st => CompJOrigInv inp ce pds mem₀ WSubs aCompExt wAddr ci jL st ∧ jL < comp.J_sub.m)
      buildCompJOrigBody
      (normalPost fun st =>
        CompJOrigInv inp ce pds mem₀ WSubs aCompExt wAddr ci (jL + 1)
          { st with regs := Function.update st.regs 37 (jL + 1) } ∧ st.regs 37 = jL)
      (fun _ => asmJOrigCost) := by
  intro wd comp st ω ⟨hP, hjL⟩
  cases st with | mk m regs pos =>
  rcases hP with ⟨_, hbase, hr18, hr23, hr24, hr25, hr26, hr27, hr28, hr29, hr31, hr32, hr37,
    hws, ha_ext, hmax_le, hcomp_ext, hbelow, hhdr0, hm12, hm13, hm14, hm15, hm16,
    hm_n, hm_m, hprev_j0, hprev_w, hprev_j, hcur_j, hzero_w, hzero_j, hzf⟩
  dsimp only at hr18 hr23 hr24 hr25 hr26 hr27 hr28 hr29 hr31 hr32 hr37
  dsimp only at hcomp_ext hbelow hhdr0 hm12 hm13 hm14 hm15 hm16 hm_n hm_m hprev_j0 hprev_w hprev_j hcur_j hzero_w hzero_j hzf
  set Wm := wd.W.m
  set wWNumAddr := wAddr + (2 + 2 * Wm)
  set wSrcAddr := wWNumAddr + Wm
  set jSrcAddr := wSrcAddr + 3 * Wm
  set hEnd := jSrcAddr + 3 * inp.prep.J.m
  rcases ce_word_bounds hvalid with ⟨h1w, hheap_w, _⟩
  have hv := hvalid.2.2.1
  have hdone := hvalid.2.2.2.2.2.2.2.2.2.1
  have h_in_lt := inp.input_reads_lt_h hvalid
  have hEnd_lt_w : hEnd < 2 ^ w := lt_of_le_of_lt hmax_le hheap_w
  have ha_lo : inp.h + 20 ≤ aCompExt := by
    rw [← hr18]; exact hbase.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcomps_len : wd.comps.length = inp.prep.rawComps.length :=
    buildCompsFrom_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  have hci_wd : ci < wd.comps.length := by rw [hcomps_len]; exact hci
  have hcomp_eq : wd.comps[ci] = comp := by simp [comp, List.getD_eq_getElem?_getD, hci_wd]
  have hw_ci := buildCompsFrom_getElem inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hci
  have hc_jsub : comp.J_sub = inp.prep.cJSub inp.prep.rawComps[ci] := by
    rw [← hcomp_eq]; exact hw_ci.2.2.2.2.2.1
  have hc_jorig : comp.jSubOrigEdges = inp.prep.cJOrig inp.prep.rawComps[ci] := by
    rw [← hcomp_eq]; exact hw_ci.2.2.2.2.2.2.1
  have hcj_p := cJOrig_props hv hci
  have hjL_orig : jL < comp.jSubOrigEdges.length := by rw [hc_jorig, hcj_p.1, ← hc_jsub]; exact hjL
  set eJ := comp.jSubOrigEdges[jL]!
  have heJ_eq : comp.jSubOrigEdges[jL]'hjL_orig = eJ := by
    dsimp only [eJ]; rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hjL_orig]; rfl
  have heJ_mem_comp : eJ ∈ comp.jSubOrigEdges := by rw [← heJ_eq]; exact List.getElem_mem hjL_orig
  have heJ_mem_orig : eJ ∈ inp.prep.cJOrig inp.prep.rawComps[ci] := by
    rw [← hc_jorig]; exact heJ_mem_comp
  have heJ_lt_m : eJ < inp.prep.J.m := hcj_p.2.2.1 eJ heJ_mem_orig
  have hlist_jorig := (hdone ci hci).2.2.2.2.2.2.2.2.1
  have hrc_lt : inp.prep.cJOrigPtr ci + (inp.prep.cJSub inp.prep.rawComps[ci]).m ≤ inp.h :=
    (h_in_lt.2.2.2.2.2.2.2 ci hci).2.1
  have hjL_m : jL < (inp.prep.cJSub inp.prep.rawComps[ci]).m := by rw [← hc_jsub]; exact hjL
  have hm_eJ : m (inp.prep.cJOrigPtr ci + jL) = eJ := by
    have hmem0 := hbelow (inp.prep.cJOrigPtr ci + jL) (by omega)
    have hrc_bang : inp.prep.rawComps[ci]! = inp.prep.rawComps[ci] := by simp [hci]
    have hlen_o : jL < (inp.prep.cJOrig inp.prep.rawComps[ci]!).length := by
      rw [hrc_bang, hcj_p.1]; exact hjL_m
    have h1_bang : mem₀ (inp.prep.cJOrigPtr ci + jL) = (inp.prep.cJOrig inp.prep.rawComps[ci]!)[jL]! := by
      have h2 := hlist_jorig jL hlen_o
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlen_o]
      exact h2
    have hc_orig' : comp.jSubOrigEdges = inp.prep.cJOrig inp.prep.rawComps[ci]! := by
      rw [hc_jorig, hrc_bang]
    rw [hmem0, h1_bang, ← hc_orig']
  have heJ_lt_w : eJ < 2 ^ w := by omega
  have hjL_lt_w : jL < 2 ^ w := by omega
  have hj0_le_Wm : inp.prep.j0Edges.length ≤ Wm := by
    change inp.prep.j0Edges.length ≤ wd.W.m
    rw [mkWitnessData_W_m_eq_sum inp ce pds hws.1]; omega
  have hwEnd_lt_w : wAddr + (2 + 2 * Wm) + Wm + 3 * Wm + 3 * inp.prep.J.m < 2 ^ w := hEnd_lt_w
  have h1_w : 1 < 2 ^ w := h1w
  have h2_w : 2 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have hci_w : ci < 2 ^ w := by
    have : inp.prep.rawComps.length ≤ inp.h := by
      have := h_in_lt.2.2.2.2.2.1; omega
    have : inp.h ≤ inp.maxHeapEnd ce pds := by simp [maxHeapEnd]; omega
    omega
  have hjS_w : jSrcAddr < 2 ^ w := by dsimp only [jSrcAddr, wSrcAddr, wWNumAddr]; omega
  have hjOrig_w : inp.prep.cJOrigPtr ci < 2 ^ w := by
    have : inp.h ≤ inp.maxHeapEnd ce pds := by simp [maxHeapEnd]; omega
    omega
  have h3eJ_w : 3 * eJ < 2 ^ w := by omega
  have h3eJ1_w : 3 * eJ + 1 < 2 ^ w := by omega
  have h3eJ2_w : 3 * eJ + 2 < 2 ^ w := by omega
  have hjS0_w : jSrcAddr + 3 * eJ < 2 ^ w := by dsimp only [jSrcAddr, wSrcAddr, wWNumAddr]; omega
  have hjS1_w : jSrcAddr + (3 * eJ + 1) < 2 ^ w := by dsimp only [jSrcAddr, wSrcAddr, wWNumAddr]; omega
  have hjS2_w : jSrcAddr + (3 * eJ + 2) < 2 ^ w := by dsimp only [jSrcAddr, wSrcAddr, wWNumAddr]; omega
  have hptr_lt_w : inp.prep.cJOrigPtr ci + jL < 2 ^ w := by
    have : inp.h ≤ inp.maxHeapEnd ce pds := by simp [maxHeapEnd]; omega
    omega
  dsimp only [buildCompJOrigBody]
  refine runs_start_le ?_
  refine runs_seq_assign_flat (v := eJ) (e := .load (.bin .add (.reg 31) (.reg 37)))
    (ev_load (ev_add (ev_reg hr31 hjOrig_w) (ev_reg hr37 hjL_lt_w) hptr_lt_w) hm_eJ heJ_lt_w) ?_
  refine runs_seq_store_flat (x := jSrcAddr + 3 * eJ) (v := 2)
    (ea := .bin .add (.reg 27) (.bin .mul (.const 3) (.reg 38))) (ev := .const 2)
    (ev_add (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide)]; exact hr27) hjS_w)
      (ev_mul (ev_const h3_w) (ev_reg (by dsimp only; rw [Function.update_self]) heJ_lt_w) h3eJ_w) hjS0_w)
    (ev_const h2_w) ?_
  refine runs_seq_store_flat (x := jSrcAddr + (3 * eJ + 1)) (v := ci)
    (ea := .bin .add (.reg 27) (.bin .add (.bin .mul (.const 3) (.reg 38)) (.const 1)))
    (ev := .reg 29)
    (ev_add (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide)]; exact hr27) hjS_w)
      (ev_add (ev_mul (ev_const h3_w) (ev_reg (by dsimp only; rw [Function.update_self]) heJ_lt_w) h3eJ_w)
        (ev_const h1_w) h3eJ1_w) hjS1_w)
    (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide)]; exact hr29) hci_w) ?_
  set m' := Function.update (Function.update (Function.update m (jSrcAddr + 3 * eJ) 2)
    (jSrcAddr + (3 * eJ + 1)) ci) (jSrcAddr + (3 * eJ + 2)) jL
  set regs' := Function.update regs 38 eJ
  refine ⟨.normal, ⟨m', regs', pos⟩, _,
    runs_store_iff.mpr ⟨jSrcAddr + (3 * eJ + 2), jL,
      ev_add (ev_reg (by dsimp only [regs']; rw [Function.update_of_ne (by decide)]; exact hr27) hjS_w)
        (ev_add (ev_mul (ev_const h3_w) (ev_reg (by dsimp only [regs']; rw [Function.update_self]) heJ_lt_w)
          h3eJ_w) (ev_const h2_w) h3eJ2_w) hjS2_w,
      ev_reg (by dsimp only [regs']; rw [Function.update_of_ne (by decide)]; exact hr37) hjL_lt_w,
      rfl, rfl, rfl⟩,
    ?_, by norm_num [asmJOrigCost, Expr.size]⟩
  have hm_out : ∀ x, x ≠ jSrcAddr + 3 * eJ → x ≠ jSrcAddr + (3 * eJ + 1) →
      x ≠ jSrcAddr + (3 * eJ + 2) → m' x = m x := by
    intro x h1 h2 h3
    dsimp only [m']
    rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  rcases jOrig_updates_agree jSrcAddr eJ hm_out with ⟨hm_below_j, hm_j_ne, hm_zf⟩
  have hjs_def : wAddr + (2 + 2 * Wm) + Wm + 3 * Wm = jSrcAddr := rfl
  have hww_def : wAddr + (2 + 2 * Wm) = wWNumAddr := rfl
  have hws_def : wWNumAddr + Wm = wSrcAddr := rfl
  have hw_lt_js : wAddr + 1 < jSrcAddr := by rw [← hjs_def]; omega
  have hw0_lt_js : wAddr < jSrcAddr := by rw [← hjs_def]; omega
  have hslot_lt_js : ∀ idx < Wm,
      wAddr + 2 + 2 * idx < jSrcAddr ∧ wAddr + 3 + 2 * idx < jSrcAddr ∧
      wWNumAddr + idx < jSrcAddr ∧ wSrcAddr + 3 * idx < jSrcAddr ∧
      wSrcAddr + 3 * idx + 1 < jSrcAddr ∧ wSrcAddr + 3 * idx + 2 < jSrcAddr := fun idx hidx => by
    rw [← hjs_def, ← hws_def, ← hww_def]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hm_below_w0 : ∀ x < wAddr, m' x = m x :=
    fun x hx => hm_below_j x (lt_trans hx hw0_lt_js)
  have hst_stat := asm_preserves_static hhdr0 hm12 hm13 hm14 hm15 hm16 hbelow ha_lo ha_ext hm_below_w0
  have hr_36 : ∀ r ≤ 36, Function.update regs' 37 (jL + 1) r = regs r := by
    intro r hr; dsimp only [regs']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hnd_comp : comp.jSubOrigEdges.Nodup := by rw [hc_jorig]; exact hcj_p.2.1
  refine ⟨?_, ?_⟩
  · unfold CompJOrigInv
    dsimp only
    refine ⟨hjL, @ceBaseInv_of_agree inp ce pds mem₀ m' aCompExt wAddr ⟨m, regs, pos⟩
        hbase hr18 ha_ext hm_below_w0 (Function.update regs' 37 (jL + 1))
        (fun r hr => hr_36 r (Nat.le_trans hr (by decide))),
      (hr_36 18 (by decide)).trans hr18, (hr_36 23 (by decide)).trans hr23,
      (hr_36 24 (by decide)).trans hr24, (hr_36 25 (by decide)).trans hr25,
      (hr_36 26 (by decide)).trans hr26, (hr_36 27 (by decide)).trans hr27,
      (hr_36 28 (by decide)).trans hr28, (hr_36 29 (by decide)).trans hr29,
      (hr_36 31 (by decide)).trans hr31, (hr_36 32 (by decide)).trans hr32,
      by rw [Function.update_self],
      hws, ha_ext, hmax_le, compExtAt_of_agree_below hcomp_ext hm_below_w0,
      hst_stat.1, hst_stat.2.1, hst_stat.2.2.1, hst_stat.2.2.2.1, hst_stat.2.2.2.2.1,
      hst_stat.2.2.2.2.2.1, hst_stat.2.2.2.2.2.2,
      (hm_below_j wAddr hw0_lt_js).trans hm_n,
      (hm_below_j (wAddr + 1) hw_lt_js).trans hm_m,
      ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => (hm_zf inp.prep.J.m x hx heJ_lt_m).trans (hzf x hx)⟩
    · intro k hk
      have hp := hprev_j0 k hk
      have hk_wm : k < Wm := lt_of_lt_of_le hk hj0_le_Wm
      have hs := hslot_lt_js k hk_wm
      set eJk := inp.prep.j0Edges[k]!
      have hne : eJk ≠ eJ := by
        have hk_len : k < inp.prep.j0Edges.length := hk
        have hmem_k : eJk ∈ inp.prep.j0Edges := by
          dsimp only [eJk]; rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk_len]
          exact List.getElem_mem hk_len
        intro heq
        rw [heq] at hmem_k
        exact Finset.disjoint_left.mp hcj_p.2.2.2.1 (List.mem_toFinset.mpr heJ_mem_orig)
          (List.mem_toFinset.mpr hmem_k)
      exact ⟨(hm_below_j _ hs.1).trans hp.1, (hm_below_j _ hs.2.1).trans hp.2.1,
        (hm_below_j _ hs.2.2.1).trans hp.2.2.1, (hm_below_j _ hs.2.2.2.1).trans hp.2.2.2.1,
        (hm_below_j _ hs.2.2.2.2.1).trans hp.2.2.2.2.1, (hm_below_j _ hs.2.2.2.2.2).trans hp.2.2.2.2.2.1,
        (hm_j_ne eJk hne 0 (by decide)).trans hp.2.2.2.2.2.2.1,
        (hm_j_ne eJk hne 1 (by decide)).trans hp.2.2.2.2.2.2.2.1,
        (hm_j_ne eJk hne 2 (by decide)).trans hp.2.2.2.2.2.2.2.2⟩
    · intro j hj eL' heL'
      have hp := hprev_w j hj eL' heL'
      have hw_bound : (wd.comps.getD j defaultCompInfo).wStart + eL' < Wm := by
        have hj_rc : j < inp.prep.rawComps.length := by omega
        have hj_wd : j < wd.comps.length := by rw [hcomps_len]; exact hj_rc
        have hwj := buildCompsFrom_getElem inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 j hj_rc
        have hjeq : (inp.buildCompsFrom inp.prep.j0Edges.length inp.prep.rawComps WSubs)[j]'(by
            rw [buildCompsFrom_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1]; exact hj_rc) =
            wd.comps.getD j defaultCompInfo := by
          change wd.comps[j]'hj_wd = _; simp [List.getD_eq_getElem?_getD, hj_wd]
        have hwm_sum := mkWitnessData_W_m_eq_sum inp ce pds hws.1
        rw [← hjeq, hwj.1]; rw [← hjeq, hwj.2.1] at heL'
        have htake_j : ((WSubs.take (j + 1)).map Graph.m).sum =
            ((WSubs.take j).map Graph.m).sum + (WSubs[j]'(by rw [hws.1]; exact hj_rc)).m := by
          rw [List.take_succ_eq_append_getElem (by rw [hws.1]; exact hj_rc), List.map_append, List.sum_append]
          simp
        have hle_j := hwj.2.2.2.2.2.2.2
        change _ < wd.W.m; rw [hwm_sum]; omega
      have hs := hslot_lt_js ((wd.comps.getD j defaultCompInfo).wStart + eL') hw_bound
      exact ⟨(hm_below_j _ hs.1).trans hp.1, (hm_below_j _ hs.2.1).trans hp.2.1,
        (hm_below_j _ hs.2.2.1).trans hp.2.2.1, (hm_below_j _ hs.2.2.2.1).trans hp.2.2.2.1,
        (hm_below_j _ hs.2.2.2.2.1).trans hp.2.2.2.2.1, (hm_below_j _ hs.2.2.2.2.2).trans hp.2.2.2.2.2⟩
    · intro j hj jL' hjL'
      have hp := hprev_j j hj jL' hjL'
      have hj_rc : j < inp.prep.rawComps.length := lt_trans hj hci
      have hj_wd : j < wd.comps.length := by rw [hcomps_len]; exact hj_rc
      have hwj := buildCompsFrom_getElem inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 j hj_rc
      have hjeq : (inp.buildCompsFrom inp.prep.j0Edges.length inp.prep.rawComps WSubs)[j]'(by
          rw [buildCompsFrom_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1]; exact hj_rc) =
          wd.comps.getD j defaultCompInfo := by
        change wd.comps[j]'hj_wd = _; simp [List.getD_eq_getElem?_getD, hj_wd]
      have hj_orig : (wd.comps.getD j defaultCompInfo).jSubOrigEdges = inp.prep.cJOrig inp.prep.rawComps[j] := by
        rw [← hjeq]; exact hwj.2.2.2.2.2.2.1
      have hj_sub : (wd.comps.getD j defaultCompInfo).J_sub = inp.prep.cJSub inp.prep.rawComps[j] := by
        rw [← hjeq]; exact hwj.2.2.2.2.2.1
      have hlen_j : (wd.comps.getD j defaultCompInfo).jSubOrigEdges.length =
          (wd.comps.getD j defaultCompInfo).J_sub.m := by
        rw [hj_orig, hj_sub]; exact (cJOrig_props hv hj_rc).1
      set eJj := (wd.comps.getD j defaultCompInfo).jSubOrigEdges[jL']!
      have heJj_mem : eJj ∈ inp.prep.cJOrig inp.prep.rawComps[j] := by
        rw [← hj_orig]; dsimp only [eJj]
        have hl : jL' < (wd.comps.getD j defaultCompInfo).jSubOrigEdges.length := by rw [hlen_j]; exact hjL'
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hl]
        exact List.getElem_mem hl
      have hne : eJj ≠ eJ := fun heq => by
        rw [heq] at heJj_mem
        exact Finset.disjoint_left.mp (hcj_p.2.2.2.2 j hj) (List.mem_toFinset.mpr heJj_mem)
          (List.mem_toFinset.mpr heJ_mem_orig)
      exact ⟨(hm_j_ne eJj hne 0 (by decide)).trans hp.1,
        (hm_j_ne eJj hne 1 (by decide)).trans hp.2.1,
        (hm_j_ne eJj hne 2 (by decide)).trans hp.2.2⟩
    · intro jL' hjL'
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hjL') with hj_lt | hjeq
      · have hp := hcur_j jL' hj_lt
        set eJ' := comp.jSubOrigEdges[jL']!
        have hne : eJ' ≠ eJ := by
          have hj_len' : jL' < comp.jSubOrigEdges.length := lt_trans hj_lt hjL_orig
          have hg' : comp.jSubOrigEdges[jL']'hj_len' = eJ' := by
            dsimp only [eJ']; rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj_len']; rfl
          rw [← heJ_eq, ← hg']
          exact fun heq => absurd ((hnd_comp.getElem_inj_iff).mp heq) (Nat.ne_of_lt hj_lt)
        exact ⟨(hm_j_ne eJ' hne 0 (by decide)).trans hp.1,
          (hm_j_ne eJ' hne 1 (by decide)).trans hp.2.1,
          (hm_j_ne eJ' hne 2 (by decide)).trans hp.2.2⟩
      · subst hjeq
        exact jOrig_writes_cell m jSrcAddr eJ ci jL'
    · intro k hk hkw
      have hz := hzero_w k hk hkw
      have hs := hslot_lt_js k hkw
      exact ⟨(hm_below_j _ hs.1).trans hz.1, (hm_below_j _ hs.2.1).trans hz.2.1,
        (hm_below_j _ hs.2.2.1).trans hz.2.2.1,
        fun t ht => by
          cases t with
          | zero => exact (hm_below_j _ hs.2.2.2.1).trans (hz.2.2.2 0 ht)
          | succ t => cases t with
            | zero => exact (hm_below_j _ hs.2.2.2.2.1).trans (hz.2.2.2 1 ht)
            | succ t => cases t with
              | zero => exact (hm_below_j _ hs.2.2.2.2.2).trans (hz.2.2.2 2 ht)
              | succ _ => omega⟩
    · intro eJ' heJ' hnot1 hnot2 hnot3 t ht
      rw [List.take_succ_eq_append_getElem hjL_orig, List.mem_append, List.mem_singleton] at hnot3
      push Not at hnot3
      have hne : eJ' ≠ eJ := by rw [← heJ_eq]; exact hnot3.2
      exact (hm_j_ne eJ' hne t ht).trans (hzero_j eJ' heJ' hnot1 hnot2 hnot3.1 t ht)
  · dsimp only [regs']; rw [Function.update_of_ne (by omega)]; exact hr37

private lemma comp_J_sub_m_le {inp : WitnessCoreInput} {mem₀ : ℕ → ℕ} {w : ℕ}
    (_hv : inp.prep.StaticValid mem₀ w) :
    ∀ (off : ℕ) (raw : List (ℕ × List ℕ)) (ws : List Graph) (ci : ℕ),
      (∀ rc ∈ raw, (inp.prep.cJSub rc).m ≤ inp.prep.J0_strip.m) →
      ((inp.buildCompsFrom off raw ws).getD ci defaultCompInfo).J_sub.m ≤ inp.prep.J0_strip.m := by
  intro off raw ws ci hraw
  induction raw generalizing off ws ci with
  | nil => simp [buildCompsFrom, defaultCompInfo, Graph.m]
  | cons p ps ih =>
    cases ws with
    | nil => simp [buildCompsFrom, defaultCompInfo, Graph.m]
    | cons W ws' =>
      cases ci with
      | zero =>
        change (inp.prep.cJSub p).m ≤ inp.prep.J0_strip.m
        exact hraw p List.mem_cons_self
      | succ ci' =>
        simp only [buildCompsFrom, List.getD_cons_succ]
        exact ih (off + W.m) ws' ci' fun rc hrc => hraw rc (List.mem_cons_of_mem p hrc)

theorem buildCompJOrigLoop_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {mem₀ : ℕ → ℕ} {WSubs : List Graph} {aCompExt wAddr ci : ℕ}
    (hvalid : inp.Valid ce pds mem₀ w) (hci : ci < inp.prep.rawComps.length) :
    let wd := inp.mkWitnessData ce pds WSubs
    let comp := wd.comps.getD ci defaultCompInfo
    Triple w p
      (fun st => CompJOrigInv inp ce pds mem₀ WSubs aCompExt wAddr ci 0
        { st with regs := Function.update st.regs 37 0 })
      (forRange 37 (.const 0) (.reg 32) buildCompJOrigBody)
      (normalPost fun st =>
        AsmCompInv inp ce pds mem₀ WSubs aCompExt wAddr (ci + 1)
          { st with regs := Function.update st.regs 29 (ci + 1) } ∧ st.regs 29 = ci)
      (fun _ => asmJOrigCost * comp.J_sub.m + 9 * comp.J_sub.m + 7) := by
  intro wd comp
  have h1w : 1 < 2 ^ w := (ce_word_bounds hvalid).1
  have h0w : 0 < 2 ^ w := lt_trans Nat.zero_lt_one h1w
  have hjm_lt : comp.J_sub.m < 2 ^ w := by
    have hv := hvalid.2.2.1
    have hm_le : comp.J_sub.m ≤ inp.prep.J0_strip.m := by
      refine comp_J_sub_m_le hv inp.prep.j0Edges.length inp.prep.rawComps WSubs ci fun rc hrc => ?_
      have hsum := (PrepInput.StaticValid.size_bounds hv).2.2.2.1
      have hmem : (inp.prep.cJSub rc).m ≤
          (inp.prep.rawComps.map fun p => (inp.prep.cJSub p).m).sum :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨rc, hrc, rfl⟩)
      omega
    have hwb := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    omega
  refine (Triple.seq_normal_const
    (R := CompJOrigInv inp ce pds mem₀ WSubs aCompExt wAddr ci 0)
    (c₁ := (Expr.const 0).size + 1)
    (c₂ := (comp.J_sub.m - 0) * (asmJOrigCost + (Expr.reg 32).size + 8) + ((Expr.reg 32).size + 3))
    ?_ ?_).mono_cost (fun _ _ => by dsimp only [asmJOrigCost]; simp [Expr.size]; omega)
  · exact Triple.assign (val := fun _ => 0) (fun _ _ => ev_const h0w) fun _ hP => hP
  · refine (Triple.forUp_const asmJOrigCost 0 comp.J_sub.m
      (Nat.zero_le _) h1w (fun _ => hjm_lt)
      (fun _ _ _ _ hP => hP.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (fun _ _ _ _ hP => by
        have hm := hP.2.2.2.2.2.2.2.2.2.2.2.1
        simp only [Expr.eval, hm]; rfl)
      (fun k _ hk => Triple.weaken_pre (buildCompJOrigBody_triple hvalid hci (jL := k))
        fun _ hinv => ⟨hinv, hk⟩)).strengthen_post ?_
    intro o st hpost
    cases o with
    | normal =>
      rcases hpost with ⟨_, hbase, hr18, hr23, hr24, hr25, hr26, hr27, hr28, hr29, _, _, _,
        hws, ha_ext, hmax_le, hcomp_ext, hbelow, hhdr0, hm12, hm13, hm14, hm15, hm16,
        hm_n, hm_m, hprev_j0, hprev_w, hprev_j, hcur_j, hzero_w, hzero_j, hzf⟩
      have htake_succ : inp.prep.j0Edges.length + ((WSubs.take (ci + 1)).map Graph.m).sum =
          comp.wStart + comp.W_sub.m := by
        have hclen : wd.comps.length = inp.prep.rawComps.length :=
          buildCompsFrom_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
        have hceq : (inp.buildCompsFrom inp.prep.j0Edges.length inp.prep.rawComps WSubs)[ci]'(by
            rw [buildCompsFrom_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1]; exact hci) =
            comp := by
          change wd.comps[ci]'(by rw [hclen]; exact hci) = comp
          simp [comp, List.getD_eq_getElem?_getD, hclen, hci]
        have hw_ci := buildCompsFrom_getElem inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hci
        rw [List.take_succ_eq_append_getElem (by rw [hws.1]; exact hci), List.map_append, List.sum_append]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rw [← hceq, hw_ci.1, hw_ci.2.1]; omega
      have hj_orig_eq : comp.jSubOrigEdges.take comp.J_sub.m = comp.jSubOrigEdges := by
        have hclen : wd.comps.length = inp.prep.rawComps.length :=
          buildCompsFrom_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
        have hceq : (inp.buildCompsFrom inp.prep.j0Edges.length inp.prep.rawComps WSubs)[ci]'(by
            rw [buildCompsFrom_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1]; exact hci) =
            comp := by
          change wd.comps[ci]'(by rw [hclen]; exact hci) = comp
          simp [comp, List.getD_eq_getElem?_getD, hclen, hci]
        have hw_ci := buildCompsFrom_getElem inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hci
        have hcj := cJOrig_props hvalid.2.2.1 hci
        have hlen_o : comp.jSubOrigEdges.length = comp.J_sub.m := by
          rw [← hceq, hw_ci.2.2.2.2.2.1, hw_ci.2.2.2.2.2.2.1]; exact hcj.1
        rw [← hlen_o, List.take_length]
      refine ⟨?_, hr29⟩
      unfold AsmCompInv
      dsimp only
      refine ⟨hci, @ceBaseInv_of_agree inp ce pds mem₀ st.mem aCompExt wAddr st
          hbase hr18 ha_ext (fun _ _ => rfl) (Function.update st.regs 29 (ci + 1))
          (fun r hr => by rw [Function.update_of_ne (by omega)]),
        by rw [Function.update_of_ne (by omega)]; exact hr18,
        by rw [Function.update_of_ne (by omega)]; exact hr23,
        by rw [Function.update_of_ne (by omega)]; exact hr24,
        by rw [Function.update_of_ne (by omega)]; exact hr25,
        by rw [Function.update_of_ne (by omega)]; exact hr26,
        by rw [Function.update_of_ne (by omega)]; exact hr27,
        by rw [Function.update_of_ne (by omega)]; exact hr28,
        by rw [Function.update_self],
        hws, ha_ext, hmax_le, hcomp_ext, hbelow, hhdr0, hm12, hm13, hm14, hm15, hm16,
        hm_n, hm_m, hprev_j0, hprev_w, ?_, ?_, ?_, hzf⟩
      · intro j hj jL' hjL'
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj_lt | rfl
        · exact hprev_j j hj_lt jL' hjL'
        · exact hcur_j jL' hjL'
      · intro k hk hkw
        exact hzero_w k (by rw [← htake_succ]; exact hk) hkw
      · intro eJ heJ hnot1 hnot2 t ht
        refine hzero_j eJ heJ hnot1 (fun j hj => hnot2 j (lt_trans hj (Nat.lt_succ_self ci))) ?_ t ht
        rw [hj_orig_eq]
        exact hnot2 ci (Nat.lt_succ_self ci)
    | returned _ => exact False.elim hpost

end MinCostFlow.Spanner