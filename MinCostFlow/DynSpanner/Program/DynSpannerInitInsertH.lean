module

public import MinCostFlow.DynSpanner.Program.DynSpannerInitDefs
import MinCostFlow.DynSpanner.Program.DynGraphInsert

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Initialization `Jtilde` insertion loop triple (`DynSpannerInitInsertH`)
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

lemma dsInsertJtildeH_triple {w L vCap eCap b heapSp : ℕ}
    {G Jt : MGraph}
    {p : Program} {bOps bEdge bPhase : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpPhase : p.HasAt bPhase (phaseProcs bOps bEdge))
    (hw16 : 16 ≤ 2 ^ w)
    (hb_fix_w : b + dsFixedSize L vCap eCap < 2 ^ w)
    (hG_v : ∀ v ∈ G.V, v < vCap) (hG_e : ∀ e ∈ G.E, e < eCap) (hG_val : G.IsValid)
    (hJt_sub : Jt.E ⊆ G.E) (hJm_w : Jt.m < 2 ^ w) :
    let gPtr := dsGPtr b
    let hPtr := dsHPtr b vCap eCap
    ∀ (jtPtr mEmbOutPtr : ℕ) (mem0 : ℕ → ℕ),
      b + dsFixedSize L vCap eCap ≤ jtPtr →
      jtPtr + dynGraphSize vCap eCap ≤ heapSp →
      heapSp < 2 ^ w →
      mem0 (b + dsLOff) = L → mem0 (b + dsVCapOff) = vCap → mem0 (b + dsECapOff) = eCap →
      DynGraphAt mem0 gPtr vCap eCap G →
      DynGraphAt mem0 hPtr vCap eCap { V := G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 } →
      DynGraphAt mem0 jtPtr vCap eCap Jt →
      (∀ e < eCap, mem0 (dsMinHBase b vCap eCap + e) = 0) →
      IsDoublyLinkedList mem0 (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
        (dsHHeadBase b vCap eCap) eCap [] →
      mem0 (dsHDegDummyBase b L vCap eCap) = 0 →
      Triple w p
        (fun st => st.mem = mem0 ∧ st.regs 0 = b ∧ st.regs 2 = vCap ∧
          st.regs 3 = eCap ∧ st.regs 4 = L ∧ st.regs 6 = gPtr ∧ st.regs 7 = hPtr ∧
          st.regs 8 = dsAuxPtr b vCap eCap ∧ st.regs 11 = G.m ∧ st.regs 15 = heapSp ∧
          st.regs 16 = jtPtr ∧ st.regs 17 = mEmbOutPtr ∧ st.regs 18 = Jt.m ∧
          st.regs 19 = dgEListBase jtPtr vCap eCap)
        (forRange 20 (.const 0) (.reg 18)
          (.assign 21 (.load (.bin .add (.reg 19) (.reg 20))) ;;
           .call 22 (bOps + dgIdxGetTail) [.reg 6, .reg 21] ;;
           .call 23 (bOps + dgIdxGetHead) [.reg 6, .reg 21] ;;
           .call 24 (bEdge + dgIdxInsertEdge) [.reg 7, .reg 21, .reg 22, .reg 23] ;;
           .call 24 (bPhase + phaseIdxHBucketCons) [.reg 0, .const 0, .reg 21]))
        (normalPost fun st =>
          st.regs 0 = b ∧ st.regs 2 = vCap ∧ st.regs 3 = eCap ∧ st.regs 6 = gPtr ∧
          st.regs 7 = hPtr ∧ st.regs 8 = dsAuxPtr b vCap eCap ∧
          st.regs 11 = G.m ∧ st.regs 15 = heapSp ∧ st.regs 17 = mEmbOutPtr ∧
          DynGraphAt st.mem hPtr vCap eCap { V := G.V, E := Jt.E, tail := G.tail, head := G.head } ∧
          (∀ e < eCap, (st.mem (dsMinHBase b vCap eCap + e) = 0 ↔ e ∉ Jt.E) ∧
            (e ∈ Jt.E → st.mem (dsMinHBase b vCap eCap + e) = 1)) ∧
          (∃ buck0 : List ℕ,
            IsDoublyLinkedList st.mem (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
              (dsHHeadBase b vCap eCap) eCap buck0 ∧
            st.mem (dsHDegDummyBase b L vCap eCap) = buck0.length ∧
            (∀ e, e ∈ buck0 ↔ e ∈ Jt.E)) ∧
          ∀ addr,
            (addr < hPtr ∨ hPtr + dynGraphSize vCap eCap ≤ addr) →
            (∀ e < eCap, addr ≠ dsMinHBase b vCap eCap + e) →
            addr ≠ dsHHeadBase b vCap eCap → addr ≠ dsHDegDummyBase b L vCap eCap →
            (∀ e < eCap, addr ≠ dsHPrevBase b vCap eCap + e) →
            (∀ e < eCap, addr ≠ dsHNextBase b vCap eCap + e) →
            st.mem addr = mem0 addr)
        (fun _ => Jt.m * (780 + (.reg 18 : Expr).size + 8) + ((.const 0 : Expr).size + (.reg 18 : Expr).size + 5)) := by
  intro gPtr hPtr jtPtr mEmbOutPtr mem0 hjt_fix hjt_hp hsp_w hL hvC heC hG hH0 hJt hmin0 hdll0 hdeg0
  obtain ⟨eL_jt, hj1, hj2, hj3, hj4, _⟩ := hJt.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have hg_lt_w : gPtr + dynGraphSize vCap eCap < 2 ^ w := by
    have : gPtr + dynGraphSize vCap eCap = hPtr := rfl
    have : hPtr + dynGraphSize vCap eCap ≤ b + dsFixedSize L vCap eCap := by
      have := dsFixedSize_ge_aux b L vCap eCap
      have : dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap := rfl
      omega
    omega
  have hh_lt_w : hPtr + dynGraphSize vCap eCap < 2 ^ w := by
    have := dsFixedSize_ge_aux b L vCap eCap
    have : dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap := rfl
    omega
  have hf := dsFixedSize_add b L vCap eCap
  have hmin_eq := dsMinHBase_eq b vCap eCap
  have hdom_eq := dsDomGenBase_eq b L vCap eCap
  have hhd_eq : dsHHeadBase b vCap eCap + (L + 1) = dsHDegDummyBase b L vCap eCap := rfl
  have hdg_eq : dsHDegDummyBase b L vCap eCap + (L + 1) = dsDomGenBase b L vCap eCap := rfl
  let Inv : ℕ → State → Prop := fun k st => ∃ (Hk : MGraph) (buck : List ℕ),
    Hk.V = G.V ∧ Hk.E = (eL_jt.take k).toFinset ∧
    (∀ e ∈ Hk.E, Hk.tail e = G.tail e ∧ Hk.head e = G.head e) ∧
    st.regs 0 = b ∧ st.regs 2 = vCap ∧ st.regs 3 = eCap ∧ st.regs 6 = gPtr ∧ st.regs 7 = hPtr ∧
    st.regs 8 = dsAuxPtr b vCap eCap ∧ st.regs 11 = G.m ∧ st.regs 15 = heapSp ∧
    st.regs 16 = jtPtr ∧ st.regs 17 = mEmbOutPtr ∧ st.regs 18 = Jt.m ∧
    st.regs 19 = dgEListBase jtPtr vCap eCap ∧ st.regs 20 = k ∧
    DynGraphAt st.mem hPtr vCap eCap Hk ∧
    (∀ e < eCap, st.mem (dsMinHBase b vCap eCap + e) = if e ∈ Hk.E then 1 else 0) ∧
    IsDoublyLinkedList st.mem (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
      (dsHHeadBase b vCap eCap) eCap buck ∧
    st.mem (dsHDegDummyBase b L vCap eCap) = buck.length ∧
    (∀ e, e ∈ buck ↔ e ∈ Hk.E) ∧
    ∀ addr,
      (addr < hPtr ∨ hPtr + dynGraphSize vCap eCap ≤ addr) →
      (∀ e < eCap, addr ≠ dsMinHBase b vCap eCap + e) →
      addr ≠ dsHHeadBase b vCap eCap → addr ≠ dsHDegDummyBase b L vCap eCap →
      (∀ e < eCap, addr ≠ dsHPrevBase b vCap eCap + e) →
      (∀ e < eCap, addr ≠ dsHNextBase b vCap eCap + e) →
      st.mem addr = mem0 addr
  refine (Triple.forRange_const (P := fun st => st.mem = mem0 ∧ st.regs 0 = b ∧
      st.regs 2 = vCap ∧ st.regs 3 = eCap ∧ st.regs 4 = L ∧ st.regs 6 = gPtr ∧ st.regs 7 = hPtr ∧
      st.regs 8 = dsAuxPtr b vCap eCap ∧ st.regs 11 = G.m ∧ st.regs 15 = heapSp ∧
      st.regs 16 = jtPtr ∧ st.regs 17 = mEmbOutPtr ∧ st.regs 18 = Jt.m ∧
      st.regs 19 = dgEListBase jtPtr vCap eCap) (Inv := Inv)
    780 0 Jt.m (Nat.zero_le _) h1_lt (fun _ => hJm_w)
    (fun st ⟨hm, r0, r2, r3, _, r6, r7, r8, r11, r15, r16, r17, r18, r19⟩ => by
      refine ⟨by eval_expr, { V := G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 }, [],
        rfl, by simp, (fun _ he => by cases he), by simp [r0], by simp [r2], by simp [r3],
        by simp [r6], by simp [r7], by simp [r8], by simp [r11], by simp [r15], by simp [r16],
        by simp [r17], by simp [r18], by simp [r19], by simp, hm ▸ hH0,
        (fun e he => by simpa [hm] using hmin0 e he),
        hm ▸ hdll0, hm ▸ hdeg0, by simp, (fun _ _ _ _ _ _ _ => hm ▸ rfl)⟩)
    (fun k st _ _ h => by rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h20, _⟩; exact h20)
    (fun k st _ _ h => by rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h18, _⟩; simp [Expr.eval, h18])
    (fun k _ hk st ω hInv => by
      rcases hInv with ⟨Hk, buck, hkV, hkE, hkEnds, hr0, hr2, hr3, hr6, hr7, hr8, hr11, hr15, hr16,
        hr17, hr18, hr19, hr20, hHk, hmink, hdllk, hdegk, hbuckk, hfr⟩
      have hj_k : k < eL_jt.length := by omega
      let e := eL_jt[k]'hj_k
      have heJt : e ∈ Jt.E := (hj3 e).mp (List.getElem_mem hj_k)
      have heG : e ∈ G.E := hJt_sub heJt
      have heCap : e < eCap := hG_e e heG
      have hJm_le : Jt.m ≤ eCap := by
        calc Jt.m = Jt.E.card := rfl
          _ ≤ (Finset.range eCap).card :=
            Finset.card_le_card (fun x hx => Finset.mem_range.mpr (hG_e x (hJt_sub hx)))
          _ = eCap := Finset.card_range eCap
      have hdom_fix : dsDomGenBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := by
        have h3 := dsRevGenBase_eq b L vCap eCap
        have h4 := dsRevHeadBase_eq b L vCap eCap
        have h5 := dsVStampBase_eq b L vCap eCap
        have hm := dsMEmbTempBase_eq b L vCap eCap
        omega
      have hdg_def : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
      have hfix_ge_aux : dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ b + dsFixedSize L vCap eCap :=
        dsFixedSize_ge_aux b L vCap eCap
      have h_h_aux : hPtr + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap := rfl
      have h_aux_min : dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap := rfl
      have h_min_hn : dsMinHBase b vCap eCap + eCap = dsHNextBase b vCap eCap := rfl
      have h_hn_hp : dsHNextBase b vCap eCap + eCap = dsHPrevBase b vCap eCap := rfl
      have h_hp_hh : dsHPrevBase b vCap eCap + eCap = dsHHeadBase b vCap eCap := rfl
      have hbL_lt : b + dsLOff < hPtr := by simp [hPtr, dsHPtr, dsGPtr, dsHdrSize, dsLOff]; omega
      have hbV_lt : b + dsVCapOff < hPtr := by simp [hPtr, dsHPtr, dsGPtr, dsHdrSize, dsVCapOff]; omega
      have hbE_lt : b + dsECapOff < hPtr := by simp [hPtr, dsHPtr, dsGPtr, dsHdrSize, dsECapOff]; omega
      have hbuck_lt : ∀ x ∈ buck, x < eCap := fun x hx =>
        hG_e x (hJt_sub ((hj3 x).mp (List.take_subset k eL_jt (by simpa [hkE] using (hbuckk x).mp hx))))
      have he_ltw : e < 2 ^ w := by omega
      have hG_tailV : G.tail e ∈ G.V := (hG_val e heG).1
      have hG_headV : G.head e ∈ G.V := (hG_val e heG).2
      have hG_tail_w : G.tail e < 2 ^ w := by have := hG_v _ hG_tailV; omega
      have hG_head_w : G.head e < 2 ^ w := by have := hG_v _ hG_headV; omega
      have he_not_take : e ∉ eL_jt.take k := by
        intro hmem
        rw [List.mem_take_iff_getElem] at hmem
        rcases hmem with ⟨i, hi, heq⟩
        have hik : i < k := lt_of_lt_of_le hi (Nat.min_le_left _ _)
        exact absurd (hj2.getElem_inj_iff.mp heq) (Nat.ne_of_lt hik)
      have he_not_Hk : e ∉ Hk.E := by rw [hkE, List.mem_toFinset]; exact he_not_take
      have he_not_buck : e ∉ buck := fun hb => he_not_Hk ((hbuckk e).mp hb)
      have haddr_jt : dgEListBase jtPtr vCap eCap + k < 2 ^ w := by
        simp only [dgEListBase]; omega
      have hjt_fr : st.mem (dgEListBase jtPtr vCap eCap + k) = e := by
        have hdisj_h : dgEListBase jtPtr vCap eCap + k < hPtr ∨
            hPtr + dynGraphSize vCap eCap ≤ dgEListBase jtPtr vCap eCap + k := by
          right
          have : hPtr + dynGraphSize vCap eCap ≤ b + dsFixedSize L vCap eCap := by
            have := dsFixedSize_ge_aux b L vCap eCap
            have : dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap := rfl
            omega
          simp only [dgEListBase]; omega
        have hdisj_min : ∀ e' < eCap, dgEListBase jtPtr vCap eCap + k ≠ dsMinHBase b vCap eCap + e' := by
          intro e' he'; simp only [dgEListBase]; omega
        have hdisj_hh : dgEListBase jtPtr vCap eCap + k ≠ dsHHeadBase b vCap eCap := by
          simp only [dgEListBase]; omega
        have hdisj_hd : dgEListBase jtPtr vCap eCap + k ≠ dsHDegDummyBase b L vCap eCap := by
          simp only [dgEListBase]; omega
        have hdisj_hp : ∀ e' < eCap, dgEListBase jtPtr vCap eCap + k ≠ dsHPrevBase b vCap eCap + e' := by
          intro e' he'; simp only [dgEListBase, dsHPrevBase, dsHNextBase]; omega
        have hdisj_hn : ∀ e' < eCap, dgEListBase jtPtr vCap eCap + k ≠ dsHNextBase b vCap eCap + e' := by
          intro e' he'; simp only [dgEListBase, dsHNextBase]; omega
        exact (hfr _ hdisj_h hdisj_min hdisj_hh hdisj_hd hdisj_hp hdisj_hn).trans (hj4 k hj_k)
      have hG_st : DynGraphAt st.mem gPtr vCap eCap G := by
        refine dynGraphAt_of_agree hG fun a ha1 ha2 => ?_
        have h1 : dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap := rfl
        have h2 : dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap := rfl
        have h3 : dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap := rfl
        have h4 : dsMinHBase b vCap eCap + 3 * eCap = dsHHeadBase b vCap eCap := by
          simp only [dsHHeadBase, dsHPrevBase, dsHNextBase]; omega
        exact hfr a (Or.inl (by omega)) (fun _ _ => by omega) (by omega) (by omega)
          (fun _ _ => by simp only [dsHPrevBase, dsHNextBase]; omega)
          (fun _ _ => by simp only [dsHNextBase]; omega)
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := e)
        (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr19, hr20, haddr_jt]) hjt_fr) ?_
      have hpre_t : (dgGetTailContract w vCap eCap _).pre [gPtr, e] st.mem :=
        ⟨gPtr, e, rfl, hw16, hg_lt_w, heG, hG_st⟩
      refine runs_seq_call_le (r := 22) (dgGetTail_meetsContract hpOps)
        (by simp [Expr.eval, evalArgs, hr6])
        (fun z hz => by simp at hz; rcases hz with rfl | rfl <;> omega)
        hpre_t ?_
      intro retT memT posT ⟨gPtrT, eT, hEqT, hmemT, hretT⟩
      simp only [List.cons.injEq, and_true] at hEqT
      rcases hEqT with ⟨rfl, rfl⟩
      subst hmemT
      have hpre_hd : (dgGetHeadContract w vCap eCap _).pre [gPtr, e] st.mem :=
        ⟨gPtr, e, rfl, hw16, hg_lt_w, heG, hG_st⟩
      refine runs_seq_call_le (r := 23) (dgGetHead_meetsContract hpOps)
        (by simp [Expr.eval, evalArgs, hr6])
        (fun z hz => by simp at hz; rcases hz with rfl | rfl <;> omega)
        hpre_hd ?_
      intro retH memH posH ⟨gPtrH, eH, hEqH, hmemH, hretH⟩
      simp only [List.cons.injEq, and_true] at hEqH
      rcases hEqH with ⟨rfl, rfl⟩
      subst hmemH
      have hHk_mH : DynGraphAt st.mem hPtr vCap eCap Hk := hHk
      have hpre_ins : (dgInsertEdgeContract w vCap eCap _).pre [hPtr, e, G.tail e, G.head e] st.mem :=
        ⟨hPtr, e, G.tail e, G.head e, rfl, hw16, hh_lt_w,
          hkV.symm ▸ hG_tailV, hkV.symm ▸ hG_headV, hHk_mH⟩
      refine runs_seq_call_le (r := 24) (dgInsertEdge_meetsContract hpEdge hpOps)
        (by simp [Expr.eval, evalArgs, hr7, hretT, hretH])
        (fun z hz => by simp at hz; rcases hz with rfl | rfl | rfl | rfl <;> omega)
        hpre_ins ?_
      intro retI memI posI ⟨gPtrI, eI, uI, vI, hEqI, _, hHk', hfrI⟩
      simp only [List.cons.injEq, and_true] at hEqI
      rcases hEqI with ⟨rfl, rfl, rfl, rfl⟩
      rw [if_pos ⟨heCap, he_not_Hk⟩] at hHk'
      have hdisj_h_meta : ∀ a, dsMinHBase b vCap eCap ≤ a → a < dsDomGenBase b L vCap eCap →
          a < hPtr ∨ hPtr + dynGraphSize vCap eCap ≤ a := by
        intro a ha1 ha2; right
        have := dsFixedSize_ge_aux b L vCap eCap
        have : hPtr + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap := rfl
        omega
      have hfrI_meta : ∀ a, dsMinHBase b vCap eCap ≤ a → a < dsDomGenBase b L vCap eCap →
          memI a = st.mem a := by
        intro a ha1 ha2
        exact hfrI a (hdisj_h_meta a ha1 ha2)
      have hL_I : memI (b + dsLOff) = L := by
        rw [hfrI _ (Or.inl (by omega))]
        exact (hfr _ (Or.inl (by omega)) (fun _ _ => by omega) (by omega) (by omega)
          (fun _ _ => by omega) (fun _ _ => by omega)).trans hL
      have hvC_I : memI (b + dsVCapOff) = vCap := by
        rw [hfrI _ (Or.inl (by omega))]
        exact (hfr _ (Or.inl (by omega)) (fun _ _ => by omega) (by omega) (by omega)
          (fun _ _ => by omega) (fun _ _ => by omega)).trans hvC
      have heC_I : memI (b + dsECapOff) = eCap := by
        rw [hfrI _ (Or.inl (by omega))]
        exact (hfr _ (Or.inl (by omega)) (fun _ _ => by omega) (by omega) (by omega)
          (fun _ _ => by omega) (fun _ _ => by omega)).trans heC
      have hmin_I : memI (dsMinHBase b vCap eCap + e) = 0 := by
        rw [hfrI_meta _ (by omega) (by omega)]
        rw [hmink e heCap, if_neg he_not_Hk]
      have hdll_I : IsDoublyLinkedList memI (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
          (dsHHeadBase b vCap eCap) eCap buck := by
        refine IsDoublyLinkedList.of_agree hdllk ?_ ?_ ?_
        · exact hfrI_meta _ (by omega) (by omega)
        · intro x hx
          have := hbuck_lt x hx
          exact hfrI_meta _ (by omega) (by omega)
        · intro x hx
          have := hbuck_lt x hx
          exact hfrI_meta _ (by omega) (by omega)
      have hdeg_I : memI (dsHDegDummyBase b L vCap eCap) = buck.length := by
        rw [hfrI_meta _ (by omega) (by omega)]
        exact hdegk
      have hpre_hc : (hBucketConsContract w L vCap eCap b buck 0 e).pre [b, 0, e] memI :=
        ⟨rfl, hw16, hb_fix_w, Nat.zero_le _, heCap, he_not_buck, hL_I, hvC_I, heC_I,
          by simpa using hdll_I, hdeg_I⟩
      refine runs_call_le (r := 24) (hBucketCons_meetsContract hpPhase hpOps)
        (by simp [Expr.eval, evalArgs, hr0])
        (fun z hz => by simp at hz; rcases hz with rfl | rfl | rfl <;> omega)
        hpre_hc ?_
      intro retC memC posC ⟨_, _, hminC, hdllC, hdegC, hfrC⟩
      let H_next := Hk.applyUpdate (.insert e (G.tail e) (G.head e))
      have hH_next_V : H_next.V = G.V := by
        simp only [H_next, MGraph.applyUpdate, hkV]
      have hH_next_E : H_next.E = (eL_jt.take (k + 1)).toFinset := by
        simp only [H_next, MGraph.applyUpdate]
        rw [List.take_succ_eq_append_getElem hj_k, List.toFinset_append, List.toFinset_cons,
          List.toFinset_nil, hkE]
        ext x; simp [e, Finset.mem_insert, or_comm]
      have hHk'_C : DynGraphAt memC hPtr vCap eCap H_next := by
        refine dynGraphAt_of_agree hHk' fun a ha1 ha2 => hfrC a ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · intro x hx _; omega
        · intro x hx _; omega
      dsimp only [normalPost]
      refine ⟨⟨⟨H_next, e :: buck, hH_next_V, hH_next_E, ?_, by simp [hr0], by simp [hr2],
        by simp [hr3], by simp [hr6], by simp [hr7], by simp [hr8], by simp [hr11], by simp [hr15],
        by simp [hr16], by simp [hr17], by simp [hr18], by simp [hr19], by simp, hHk'_C, ?_, hdllC,
        ?_, ?_, ?_⟩, by simp [hr20]⟩, ?_⟩
      · intro e' he'
        simp only [H_next, MGraph.applyUpdate, Finset.mem_insert] at he' ⊢
        rcases he' with rfl | he'
        · simp
        · have hne : e' ≠ e := fun h => he_not_Hk (h ▸ he')
          simp [hne, hkEnds e' he']
      · intro e' he'
        dsimp only
        by_cases hne : e' = e
        · subst hne; simp [H_next, MGraph.applyUpdate, hminC]
        · rw [hfrC _ (by omega) (by omega) (by omega) (fun x hx _ => by omega)
            (fun x hx _ => by omega)]
          dsimp only
          rw [hfrI _ (Or.inr (by omega)), hmink e' he']
          simp [H_next, MGraph.applyUpdate, hne]
      · simpa using hdegC
      · intro e'
        simp [H_next, MGraph.applyUpdate, List.mem_cons, hbuckk e', Finset.mem_insert]
      · intro addr h1 h2 h3 h4 h5 h6
        dsimp only
        rw [hfrC addr (fun ha => h2 e heCap (by simpa using ha)) (by simpa using h3)
          (by simpa using h4)
          (fun x hx hmem => h5 x (by rcases List.mem_cons.mp hmem with rfl | hm' <;> [exact heCap; exact hbuck_lt x hm']) hx)
          (fun x hx hmem => h6 x (by rcases List.mem_cons.mp hmem with rfl | hm' <;> [exact heCap; exact hbuck_lt x hm']) hx)]
        dsimp only
        rw [hfrI addr h1]
        exact hfr addr h1 h2 h3 h4 h5 h6
      · dsimp only [dgGetTailContract, dgGetHeadContract, dgInsertEdgeContract, hBucketConsContract,
          argsSize, Expr.size]
        omega)).strengthen_post ?_
  intro o st hq
  cases o with
  | returned _ => exact hq
  | normal =>
    rcases hq with ⟨Hf, buck, hfV, hfE, hfEnds, hr0, hr2, hr3, hr6, hr7, hr8, hr11, hr15, _, hr17,
      _, _, _, hHf, hminf, hdllf, hdegf, hbuckf, hfr⟩
    have hfE_eq : Hf.E = Jt.E := by
      rw [hfE, ← hj1, List.take_length]
      ext e; simp [hj3 e]
    refine ⟨hr0, hr2, hr3, hr6, hr7, hr8, hr11, hr15, hr17,
      dynGraphAt_congr hfV hfE_eq (fun e he => hfEnds e (hfE_eq ▸ he)) hHf,
      fun e he => ⟨?_, ?_⟩,
      ⟨buck, hdllf, hdegf, fun e => by rw [hbuckf e, hfE_eq]⟩,
      hfr⟩
    · rw [hminf e he, hfE_eq]; simp
    · intro heJ
      have he' := hJt_sub heJ
      rw [hminf e (hG_e e he'), hfE_eq, if_pos heJ]

end

end MinCostFlow.DynSpanner.Program
