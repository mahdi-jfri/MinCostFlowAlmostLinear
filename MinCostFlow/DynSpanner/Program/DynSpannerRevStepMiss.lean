module

public import MinCostFlow.DynSpanner.Program.DynSpannerRevCons
public import MinCostFlow.DynSpanner.Program.DynSpannerRevHelpers

import Mathlib.Tactic.Linarith

/-!
# Unvisited-vertex branch for `dsInsertWalkRev` (`DynSpannerRevStepMiss`)

Proves `dsInsertWalkRev_step_miss_triple`, handling the `cur ∉ walkVertices` branch of
`dsInsertWalkRev_step_triple` where `vStamp[cur]` is updated and `dsRevCons` prepends `e` to
`revLists i cur`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

theorem dsInsertWalkRev_step_miss_triple {w L vCap eCap b i e uStart wPtr hPtr heapPtr heapCur gen0 k k₀ : ℕ}
    {H : MGraph} {W : List (ℕ × Bool)} {rev0 : ℕ → List ℕ} {foot0 : ℕ → Prop}
    {mem : ℕ → ℕ} {p : Program} {bOps bRev : ℕ}
    (hpRev : p.HasAt bRev (revProcs bOps bRev))
    (hw16 : 16 ≤ 2 ^ w) (hfix_le : b + dsFixedSize L vCap eCap ≤ heapPtr)
    (hheap_lt : heapPtr + 2 * (W.length + 1) < 2 ^ w)
    (hiL : i ≤ L) (he_lt : e < 2 ^ w)
    (hb_h : b + dsHdrSize ≤ hPtr) (hh_min : hPtr + dynGraphSize vCap eCap ≤ dsMinHBase b vCap eCap)
    (hL : mem (b + dsLOff) = L) (hvC : mem (b + dsVCapOff) = vCap) (heC : mem (b + dsECapOff) = eCap)
    (_hgen_lt : gen0 + 1 < 2 ^ w)
    (hdom_pos : 0 < mem (dsDomGenBase b L vCap eCap + i))
    (hfoot0 : ∀ a, foot0 a → b + dsFixedSize L vCap eCap ≤ a ∧ a < heapPtr)
    (hvH : ∀ v ∈ H.V, v < vCap)
    (hb_ltw : b < 2 ^ w) (hi_ltw : i < 2 ^ w) (he_ltw : e < 2 ^ w)
    (hk : k < W.length) (hc₀ : k₀ ≤ 120)
    {st st_d : State} {ω : ℕ → Bool}
    (hhp1 : heapPtr + 2 ≤ heapCur) (hhp2 : heapCur ≤ heapPtr + 2 * (k + 1))
    (dr0 : st_d.regs 0 = b) (dr1 : st_d.regs 1 = i) (dr2 : st_d.regs 2 = e)
    (dr4 : st_d.regs 4 = wPtr) (dr5 : st_d.regs 5 = hPtr) (dr6 : st_d.regs 6 = heapCur)
    (dr10 : st_d.regs 10 = dsVStampBase b L vCap eCap) (dr11 : st_d.regs 11 = gen0 + 1)
    (dr12 : st_d.regs 12 = W.length) (dr13 : st_d.regs 13 = k)
    (hm_d : st_d.mem = st.mem)
    (dr15 : st_d.regs 15 = H.dst (W[k].1, W[k].2))
    (hmg : st.mem (b + dsGenOff) = gen0 + 1)
    (hvst : ∀ v < vCap,
      if v ∈ H.walkVertices uStart (W.take k)
      then st.mem (dsVStampBase b L vCap eCap + v) = gen0 + 1
      else st.mem (dsVStampBase b L vCap eCap + v) ≤ gen0)
    (hrev : ∀ v < vCap,
      if v ∈ H.walkVertices uStart (W.take k) then
        st.mem (dsRevGenBase b L vCap eCap + i * vCap + v) = mem (dsDomGenBase b L vCap eCap + i) ∧
        LinkedListIn (fun a => foot0 a ∨ (heapPtr ≤ a ∧ a < heapCur)) st.mem
          (st.mem (dsRevHeadBase b L vCap eCap + i * vCap + v)) (e :: rev0 v)
      else
        st.mem (dsRevGenBase b L vCap eCap + i * vCap + v) =
          mem (dsRevGenBase b L vCap eCap + i * vCap + v) ∧
        st.mem (dsRevHeadBase b L vCap eCap + i * vCap + v) =
          mem (dsRevHeadBase b L vCap eCap + i * vCap + v) ∧
        (if st.mem (dsRevGenBase b L vCap eCap + i * vCap + v) = mem (dsDomGenBase b L vCap eCap + i)
         then LinkedListIn (fun a => foot0 a ∨ (heapPtr ≤ a ∧ a < heapCur)) st.mem
                (st.mem (dsRevHeadBase b L vCap eCap + i * vCap + v)) (rev0 v)
         else rev0 v = []))
    (hfr : ∀ addr,
      addr ≠ b + dsGenOff →
      (∀ v < vCap, addr ≠ dsVStampBase b L vCap eCap + v) →
      (∀ v < vCap, addr ≠ dsRevGenBase b L vCap eCap + i * vCap + v) →
      (∀ v < vCap, addr ≠ dsRevHeadBase b L vCap eCap + i * vCap + v) →
      (addr < heapPtr ∨ heapCur ≤ addr) →
      st.mem addr = mem addr)
    (hcur_V : H.dst W[k] ∈ H.V)
    (hhit : H.dst W[k] ∉ H.walkVertices uStart (W.take k)) :
    ∃ o st' c, Runs w p ω
      (.store (.bin .add (.reg 10) (.reg 15)) (.reg 11) ;;
       .call 6 (bRev + revIdxRevCons) [.reg 0, .reg 1, .reg 15, .reg 2, .reg 6])
      { st_d with
        regs := Function.update st_d.regs 14 (st.mem (dsVStampBase b L vCap eCap + H.dst W[k])) } o st' c ∧
      normalPost (fun st₁ =>
        dsInsertWalkRevInv L vCap eCap b i e uStart wPtr hPtr heapPtr gen0 H W rev0 foot0 mem (k + 1)
          { st₁ with regs := Function.update st₁.regs 13 (k + 1) } ∧
        st₁.regs 13 = k) o st' ∧
      k₀ + c ≤ 360 := by
  let vStamp := dsVStampBase b L vCap eCap
  let domAddr := dsDomGenBase b L vCap eCap + i
  let domVal := mem domAddr
  let footOf (heapCur : ℕ) (a : ℕ) : Prop := foot0 a ∨ (heapPtr ≤ a ∧ a < heapCur)
  let cur := H.dst W[k]
  have hcur_vCap : cur < vCap := hvH _ hcur_V
  have hstep_b : heapCur + 2 < 2 ^ w := by linarith only [hhp2, hk, hheap_lt]
  have hdisj := dsLayout_facts hiL hcur_vCap hiL hcur_vCap hfix_le
  have hdom_fix := hdisj.dom_lt_fix
  have had := dsAddrs_bound (w := w) (L := L) (vCap := vCap) (eCap := eCap) hfix_le (by omega)
  have hvs_fix : vStamp + vCap ≤ b + dsFixedSize L vCap eCap := had.2.2.2.2.2.2.2.2.2.1
  have hvs_ltw : vStamp + cur < 2 ^ w := by linarith only [hdisj.vs_lt_hp, hheap_lt]
  have hmin_fix : hPtr + dynGraphSize vCap eCap ≤ b + dsFixedSize L vCap eCap := by
    have h1 := dsMinHBase_eq b vCap eCap
    have h2 := dsDomGenBase_eq b L vCap eCap
    have h3 := dsRevGenBase_eq b L vCap eCap
    have h4 := dsRevHeadBase_eq b L vCap eCap
    have h5 := dsVStampBase_eq b L vCap eCap
    have hm := dsMEmbTempBase_eq_rev b L vCap eCap
    have hf := dsFixedSize_add b L vCap eCap
    omega
  have hgen_lt_fix : b + dsGenOff < b + dsFixedSize L vCap eCap := by
    have : dsGenOff < dsHdrSize := by decide
    have h1 := dsMinHBase_eq b vCap eCap
    have h2 := dsDomGenBase_eq b L vCap eCap
    have h3 := dsRevGenBase_eq b L vCap eCap
    have h4 := dsRevHeadBase_eq b L vCap eCap
    have h5 := dsVStampBase_eq b L vCap eCap
    have hm := dsMEmbTempBase_eq_rev b L vCap eCap
    have hf := dsFixedSize_add b L vCap eCap
    omega
  have hcur_eq : H.dst (W[k].1, W[k].2) = cur := rfl
  have hvs_ltw' : vStamp + H.dst (W[k].1, W[k].2) < 2 ^ w := hcur_eq ▸ hvs_ltw
  have heval_vs_addr : (Expr.bin .add (.reg 10) (.reg 15)).eval w
      { st_d with regs := Function.update st_d.regs 14 (st.mem (vStamp + cur)) } =
      some (vStamp + cur) := by
    dsimp only [vStamp] at dr10 hvs_ltw ⊢
    simp [Expr.eval, BinOp.eval, dr10, dr15, hcur_eq, hvs_ltw]
  refine runs_seq_store_le (x := vStamp + cur) (v := gen0 + 1) heval_vs_addr
    (by simp [Expr.eval, dr11]) ?_
  let stS := { st_d with
    regs := Function.update st_d.regs 14 (st.mem (vStamp + cur)),
    mem := Function.update st_d.mem (vStamp + cur) (gen0 + 1) }
  have hrev_cur := hrev cur hcur_vCap
  have hhit_cur : cur ∉ H.walkVertices uStart (W.take k) := hhit
  simp only [hhit_cur, ↓reduceIte] at hrev_cur
  have hcur_ltw : cur < 2 ^ w := by dsimp only [cur] at hvs_ltw' ⊢; omega
  have hdom_mem : st.mem domAddr = domVal := by
    dsimp only [domAddr, domVal] at hdom_fix ⊢
    exact hfr (dsDomGenBase b L vCap eCap + i) hdisj.dom_ne_gen
      (fun v hv => (dsLayout_facts hiL hv hiL hcur_vCap hfix_le).vs_ne_dom.symm)
      (fun v hv => (dsLayout_facts hiL hv hiL hcur_vCap hfix_le).rg_ne_dom.symm)
      (fun v hv => (dsLayout_facts hiL hv hiL hcur_vCap hfix_le).rh_ne_dom.symm)
      (Or.inl (by linarith only [hdom_fix, hfix_le]))
  have hhdr_lt_vs : ∀ off < dsHdrSize, ∀ v < vCap, b + off ≠ vStamp + v := fun off hoff v hv => by
    have := (dsLayout_facts hiL hv hiL hv hfix_le).vs_lt_fix
    have := dsFixedSize_ge_aux b L vCap eCap
    have := dsVStampBase_eq b L vCap eCap
    have := dsRevHeadBase_eq b L vCap eCap
    have := dsRevGenBase_eq b L vCap eCap
    have := dsDomGenBase_eq b L vCap eCap
    have := dsMinHBase_eq b vCap eCap
    dsimp only [vStamp]
    omega
  have hhdr_mem_eq : ∀ off < dsHdrSize, b + off ≠ b + dsGenOff → stS.mem (b + off) = mem (b + off) :=
    fun off hoff hne_gen => by
      dsimp only [stS]
      rw [Function.update_of_ne (hhdr_lt_vs off hoff cur hcur_vCap), hm_d]
      exact hfr (b + off) hne_gen (hhdr_lt_vs off hoff)
        (fun v hv => by
          have := dsRevGenBase_eq b L vCap eCap; have := dsDomGenBase_eq b L vCap eCap
          have := dsMinHBase_eq b vCap eCap; omega)
        (fun v hv => by
          have := dsRevHeadBase_eq b L vCap eCap; have := dsRevGenBase_eq b L vCap eCap
          have := dsDomGenBase_eq b L vCap eCap; have := dsMinHBase_eq b vCap eCap; omega)
        (Or.inl (by linarith only [hoff, hb_h, hh_min, hmin_fix, hfix_le]))
  have hpre_c : (dsRevConsContract w L vCap eCap b i cur e (rev0 cur) (footOf heapCur)).pre
      [b, i, cur, e, heapCur] stS.mem := by
    refine ⟨heapCur, rfl, hw16, by linarith only [hfix_le, hhp1], hstep_b, hiL, hcur_vCap, he_lt,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hhdr_mem_eq dsLOff (by decide) (by simp [dsLOff, dsGenOff])).trans hL
    · exact (hhdr_mem_eq dsVCapOff (by decide) (by simp [dsVCapOff, dsGenOff])).trans hvC
    · exact (hhdr_mem_eq dsECapOff (by decide) (by simp [dsECapOff, dsGenOff])).trans heC
    · dsimp only [stS]; rw [Function.update_of_ne hdisj.vs_ne_dom.symm, hm_d, hdom_mem]
      exact hdom_pos
    · intro a ha
      rcases ha with ha0 | ⟨ha1, ha2⟩
      · exact ⟨(hfoot0 a ha0).1, lt_of_lt_of_le (hfoot0 a ha0).2 (Nat.le_trans (Nat.le_add_right _ 2) hhp1)⟩
      · exact ⟨le_trans hfix_le ha1, ha2⟩
    · have hrg_s : stS.mem (dsRevGenBase b L vCap eCap + i * vCap + cur) =
          st.mem (dsRevGenBase b L vCap eCap + i * vCap + cur) := by
        dsimp only [stS, vStamp]
        rw [Function.update_of_ne hdisj.vs_ne_rg.symm, hm_d]
      have hdom_s : stS.mem (dsDomGenBase b L vCap eCap + i) =
          mem (dsDomGenBase b L vCap eCap + i) := by
        dsimp only [stS, vStamp]
        rw [Function.update_of_ne hdisj.vs_ne_dom.symm, hm_d]
        exact hdom_mem
      by_cases hcond : mem (dsRevGenBase b L vCap eCap + i * vCap + cur) =
          mem (dsDomGenBase b L vCap eCap + i)
      · simp only [hrg_s, hdom_s, hrev_cur.1, hcond, ↓reduceIte] at hrev_cur ⊢
        dsimp only [stS, vStamp]
        rw [Function.update_of_ne hdisj.vs_ne_rh.symm, hm_d]
        refine hrev_cur.2.2.of_agree fun a ha => by
          have hne : a ≠ dsVStampBase b L vCap eCap + cur := by
            rcases ha with ha0 | ⟨ha1, ha2⟩
            · have := hfoot0 a ha0; linarith only [this.1, hdisj.vs_lt_fix]
            · linarith only [hfix_le, ha1, hdisj.vs_lt_fix]
          rw [Function.update_of_ne hne]
      · simp only [hrg_s, hdom_s, hrev_cur.1, hcond, ↓reduceIte] at hrev_cur ⊢
        exact hrev_cur.2.2
  refine runs_call_le (r := 6) (dsRevCons_meetsContract hpRev)
    (by simp [Expr.eval, evalArgs, dr0, dr1, dr15, dr2, dr6, cur])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> linarith only [hb_ltw, hi_ltw, hcur_ltw, he_ltw, hstep_b])
    hpre_c ?_
  intro retC memC posC hpostC
  rcases hpostC with ⟨_, hEqC, rfl, hrgC, hllC, hfrC⟩
  simp only [List.cons.injEq, true_and, and_true] at hEqC
  subst hEqC
  have hfoot_mono : ∀ a, (footOf heapCur a ∨ a = heapCur ∨ a = heapCur + 1) → footOf (heapCur + 2) a := by
    intro a ha
    rcases ha with (ha0 | ⟨ha1, ha2⟩) | rfl | rfl
    · exact Or.inl ha0
    · exact Or.inr ⟨ha1, by omega⟩
    · exact Or.inr ⟨by linarith only [hhp1], by omega⟩
    · exact Or.inr ⟨by linarith only [hhp1], by omega⟩
  have hmemC_dom : Function.update st_d.mem (vStamp + cur) (gen0 + 1) domAddr = domVal := by
    rw [Function.update_of_ne hdisj.vs_ne_dom.symm, hm_d]
    exact hdom_mem
  have hhp0 : heapPtr ≤ heapCur := Nat.le_trans (Nat.le_add_right _ 2) hhp1
  have hagreeC : ∀ a, footOf heapCur a → memC a = st.mem a := fun a ha => by
    have ha_b : b + dsFixedSize L vCap eCap ≤ a ∧ a < heapCur := by
      rcases ha with ha0 | ⟨ha1, ha2⟩
      · exact ⟨(hfoot0 a ha0).1, lt_of_lt_of_le (hfoot0 a ha0).2 hhp0⟩
      · exact ⟨le_trans hfix_le ha1, ha2⟩
    refine (hfrC a (Nat.ne_of_gt (by linarith only [ha_b.1, hdisj.rg_lt_fix]))
      (Nat.ne_of_gt (by linarith only [ha_b.1, hdisj.rh_lt_fix])) (by linarith only [ha_b.2])
      (by linarith only [ha_b.2])).trans ?_
    dsimp only [stS]
    rw [Function.update_of_ne (Nat.ne_of_gt (by linarith only [ha_b.1, hdisj.vs_lt_fix])), hm_d]
  have hrg_hp_lt : ∀ v < vCap, dsRevGenBase b L vCap eCap + i * vCap + v < heapCur := fun v hv =>
    lt_of_lt_of_le (dsLayout_facts hiL hv hiL hv hfix_le).rg_lt_hp hhp0
  have hrh_hp_lt : ∀ v < vCap, dsRevHeadBase b L vCap eCap + i * vCap + v < heapCur := fun v hv =>
    lt_of_lt_of_le (dsLayout_facts hiL hv hiL hv hfix_le).rh_lt_hp hhp0
  have hvs_hp_lt : ∀ v < vCap, vStamp + v < heapCur := fun v hv =>
    lt_of_lt_of_le (dsLayout_facts hiL hv hiL hv hfix_le).vs_lt_hp hhp0
  dsimp only [normalPost]
  refine ⟨⟨⟨heapCur + 2, by linarith only [hhp1], by linarith only [hhp2],
    by simp [dr0], by simp [dr1], by simp [dr2], by simp [dr4],
    by simp [dr5], by simp, by simp [dr10], by simp [dr11], by simp [dr12],
    by simp, ?_, ?_, ?_, ?_⟩, by simp [dr13]⟩, ?_⟩
  · dsimp only
    rw [hfrC (b + dsGenOff) hdisj.rg_ne_gen.symm
      hdisj.rh_ne_gen.symm
      (Nat.ne_of_lt (by linarith only [hgen_lt_fix, hfix_le, hhp1]))
      (Nat.ne_of_lt (by linarith only [hgen_lt_fix, hfix_le, hhp1]))]
    dsimp only [stS]
    rw [Function.update_of_ne hdisj.vs_ne_gen.symm, hm_d, hmg]
  · intro v hv
    have hsucc := walkVertices_take_succ (H := H) (uStart := uStart) hk v
    have hvt := hvst v hv
    have hd_v := dsLayout_facts hiL hv hiL hcur_vCap hfix_le
    have hvs_v_hp : vStamp + v < heapCur := hvs_hp_lt v hv
    dsimp only
    by_cases hvc : v = cur
    · subst hvc
      have hv1 : cur ∈ H.walkVertices uStart (W.take (k + 1)) := hsucc.mpr (Or.inr rfl)
      simp only [hv1, ↓reduceIte]
      rw [hfrC (vStamp + cur) hd_v.vs_ne_rg hd_v.vs_ne_rh
        (by linarith only [hvs_v_hp]) (by linarith only [hvs_v_hp])]
      dsimp only [stS]
      exact Function.update_self _ _ _
    · have hvs_eq : memC (vStamp + v) = st.mem (vStamp + v) := by
        rw [hfrC (vStamp + v) hd_v.vs_ne_rg hd_v.vs_ne_rh
          (by linarith only [hvs_v_hp]) (by linarith only [hvs_v_hp])]
        dsimp only [stS]
        rw [Function.update_of_ne (by omega), hm_d]
      by_cases hv_k : v ∈ H.walkVertices uStart (W.take k)
      · have hv1 : v ∈ H.walkVertices uStart (W.take (k + 1)) := hsucc.mpr (Or.inl hv_k)
        simp only [hv1, ↓reduceIte]
        rw [hvs_eq]
        simpa [hv_k] using hvt
      · have hv1 : v ∉ H.walkVertices uStart (W.take (k + 1)) := fun h => (hsucc.mp h).elim hv_k hvc
        simp only [hv1, ↓reduceIte]
        rw [hvs_eq]
        simpa [hv_k] using hvt
  · intro v hv
    have hsucc := walkVertices_take_succ (H := H) (uStart := uStart) hk v
    dsimp only
    by_cases hvc : v = cur
    · subst hvc
      have hv1 : cur ∈ H.walkVertices uStart (W.take (k + 1)) := hsucc.mpr (Or.inr rfl)
      simp only [hv1, ↓reduceIte]
      refine ⟨hrgC.trans hmemC_dom, hllC.mono hfoot_mono⟩
    · have hd_cur := dsLayout_facts hiL hcur_vCap hiL hv hfix_le
      have hne_rg_rh_cur : dsRevGenBase b L vCap eCap + i * vCap + v ≠
          dsRevHeadBase b L vCap eCap + i * vCap + cur := dsRevGen_ne_dsRevHead hiL hv
      have hne_rh_rg_cur : dsRevHeadBase b L vCap eCap + i * vCap + v ≠
          dsRevGenBase b L vCap eCap + i * vCap + cur := (dsRevGen_ne_dsRevHead hiL hcur_vCap).symm
      have hrg_stay : memC (dsRevGenBase b L vCap eCap + i * vCap + v) =
          st.mem (dsRevGenBase b L vCap eCap + i * vCap + v) := by
        rw [hfrC _ (by simp [hvc]) hne_rg_rh_cur
          (Nat.ne_of_lt (hrg_hp_lt v hv)) (Nat.ne_of_lt (Nat.lt_succ_of_lt (hrg_hp_lt v hv)))]
        dsimp only [stS]
        rw [Function.update_of_ne hd_cur.vs_ne_rg.symm, hm_d]
      have hrh_stay : memC (dsRevHeadBase b L vCap eCap + i * vCap + v) =
          st.mem (dsRevHeadBase b L vCap eCap + i * vCap + v) := by
        rw [hfrC _ hne_rh_rg_cur (by simp [hvc])
          (Nat.ne_of_lt (hrh_hp_lt v hv)) (Nat.ne_of_lt (Nat.lt_succ_of_lt (hrh_hp_lt v hv)))]
        dsimp only [stS]
        rw [Function.update_of_ne hd_cur.vs_ne_rh.symm, hm_d]
      have hr_v := hrev v hv
      by_cases hv_k : v ∈ H.walkVertices uStart (W.take k)
      · have hv1 : v ∈ H.walkVertices uStart (W.take (k + 1)) := hsucc.mpr (Or.inl hv_k)
        simp only [hv1, ↓reduceIte]
        simp only [hv_k, ↓reduceIte] at hr_v
        refine ⟨hrg_stay.trans hr_v.1, ?_⟩
        rw [hrh_stay]
        exact (hr_v.2.of_agree hagreeC).mono fun a ha => hfoot_mono a (Or.inl ha)
      · have hv1 : v ∉ H.walkVertices uStart (W.take (k + 1)) := fun h => (hsucc.mp h).elim hv_k hvc
        simp only [hv1, ↓reduceIte]
        simp only [hv_k, ↓reduceIte] at hr_v
        refine ⟨hrg_stay.trans hr_v.1, hrh_stay.trans hr_v.2.1, ?_⟩
        by_cases hcond : st.mem (dsRevGenBase b L vCap eCap + i * vCap + v) =
            mem (dsDomGenBase b L vCap eCap + i)
        · simp only [hrg_stay, hrh_stay, hcond, ↓reduceIte] at hr_v ⊢
          exact (hr_v.2.2.of_agree hagreeC).mono fun a ha => hfoot_mono a (Or.inl ha)
        · simp only [hrg_stay, hcond, ↓reduceIte] at hr_v ⊢
          exact hr_v.2.2
  · intro addr ha1 ha2 ha3 ha4 ha5
    dsimp only
    have ha_ne_hp : addr ≠ heapCur := by rcases ha5 with h | h; linarith only [h, hhp1]; linarith only [h]
    have ha_ne_hp1 : addr ≠ heapCur + 1 := by rcases ha5 with h | h; linarith only [h, hhp1]; linarith only [h]
    rw [hfrC addr (ha3 cur hcur_vCap) (ha4 cur hcur_vCap) ha_ne_hp ha_ne_hp1]
    dsimp only [stS]
    rw [Function.update_of_ne (ha2 cur hcur_vCap), hm_d]
    exact hfr addr ha1 ha2 ha3 ha4 (by rcases ha5 with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])
  · dsimp only [dsRevConsContract, argsSize, Expr.size]; omega

end

end MinCostFlow.DynSpanner.Program
