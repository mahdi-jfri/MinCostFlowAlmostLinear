module

public import MinCostFlow.DynSpanner.Program.DynSpannerLevelWalksDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerRev

import Mathlib.Tactic.Linarith
import MinCostFlow.DynSpanner.Program.DynSpannerSetLevelWalksPost
import Mathlib.Tactic.Ring

/-!
# Loop step lemma for `dsSetLevelWalksStmt` (`DynSpannerSetLevelWalksStep`)

Proves `dsSetLevelWalks_step_triple`, verifying one iteration of the `forRange 6 0 eL.length` loop
that updates `edgeDomGen`, `piPtr`, and reverse incidence lists `revLists lvl`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

theorem dsSetLevelWalks_step_triple {w L vCap eCap b lvl eListPtr mEmbPtr heapPtr gen0 k : ℕ}
    {G H : MGraph} {eL : List ℕ} {emb : MinCostFlow.Embedding} {foot0 : ℕ → Prop}
    {mem : ℕ → ℕ} {p : Program} {bOps bRev : ℕ}
    (hpRev : p.HasAt bRev (revProcs bOps bRev))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hw16 : 16 ≤ 2 ^ w) (hlvlL : lvl ≤ L)
    (hfix_le : b + dsFixedSize L vCap eCap ≤ heapPtr)
    (hheap_lt : heapPtr + 2 * (eL.map fun e => (emb e).length + 1).sum < 2 ^ w)
    (heList_lt : eListPtr + eL.length < 2 ^ w) (hmEmb_lt : mEmbPtr + eCap < 2 ^ w)
    (hL : mem (b + dsLOff) = L) (hvC : mem (b + dsVCapOff) = vCap) (heC : mem (b + dsECapOff) = eCap)
    (hgen_lt : gen0 + 1 + eL.length < 2 ^ w)
    (hfoot0 : ∀ a, foot0 a → b + dsFixedSize L vCap eCap ≤ a ∧ a < heapPtr)
    (hfr_eList : ∀ j < eL.length,
      dsLevelWalksFrameCond L vCap eCap b lvl heapPtr
        (heapPtr + 2 * (eL.map fun e => (emb e).length + 1).sum) (eListPtr + j))
    (hfr_mEmb : ∀ e ∈ eL,
      dsLevelWalksFrameCond L vCap eCap b lvl heapPtr
        (heapPtr + 2 * (eL.map fun e => (emb e).length + 1).sum) (mEmbPtr + e))
    (heL_nd : eL.Nodup) (heL_at : ∀ j (hj : j < eL.length), mem (eListPtr + j) = eL[j])
    (hG : DynGraphAt mem (dsGPtr b) vCap eCap G) (hG_val : G.IsValid)
    (heG_cov : ∀ e ∈ G.E, e < eCap)
    (hH : DynGraphAt mem (dsHPtr b vCap eCap) vCap eCap H) (hH_val : H.IsValid)
    (hGV_HV : G.V ⊆ H.V) (hvH : ∀ v ∈ H.V, v < vCap) (heH : ∀ e ∈ H.E, e < eCap)
    (heL_spec : ∀ e ∈ eL,
      e ∈ G.E ∧ H.IsWalk (G.tail e) (G.head e) (emb e) ∧
      MWalkAt mem (mem (mEmbPtr + e)) (emb e) ∧
      b + dsFixedSize L vCap eCap ≤ mem (mEmbPtr + e) ∧
      mem (mEmbPtr + e) + (mWalkEncode (emb e)).length ≤ heapPtr)
    (hb_ltw : b < 2 ^ w) (hlvl_ltw : lvl < 2 ^ w)
    (_h1_lt : (1 : ℕ) < 2 ^ w) (_h0_lt : (0 : ℕ) < 2 ^ w)
    (hg_ltw : dsGPtr b < 2 ^ w) (hh_ltw : dsHPtr b vCap eCap < 2 ^ w)
    (_hdg_lt : dynGraphSize vCap eCap < 2 ^ w)
    (hmin_lt : dsMinHBase b vCap eCap < 2 ^ w) (hdom_lt : dsDomGenBase b L vCap eCap < 2 ^ w)
    (hedg_lt : dsEdgeDomGenBase b L vCap eCap < 2 ^ w) (hpi_lt : dsPiPtrBase b L vCap eCap < 2 ^ w)
    (hrevG_lt : dsRevGenBase b L vCap eCap < 2 ^ w) (hrevH_lt : dsRevHeadBase b L vCap eCap < 2 ^ w)
    (hdom_i_lt : dsDomGenBase b L vCap eCap + lvl < 2 ^ w)
    (hk : k < eL.length) {st : State} {ω : ℕ → Bool}
    (hInv : dsSetLevelWalksInv L vCap eCap b lvl eListPtr mEmbPtr heapPtr gen0 G H eL emb foot0 mem k st) :
    ∃ o st' c, Runs w p ω
      (.assign 9 (.load (.bin .add (.reg 2) (.reg 6))) ;;
       .assign 14 (.bin .add (.bin .mul (.reg 1) (.reg 7)) (.reg 9)) ;;
       .store (.bin .add (.reg 12) (.reg 14)) (.reg 8) ;;
       .assign 15 (.load (.bin .add (.reg 4) (.reg 9))) ;;
       .store (.bin .add (.reg 13) (.reg 14)) (.reg 15) ;;
       .call 14 (bOps + dgIdxGetTail) [.reg 10, .reg 9] ;;
       .call 5 (bRev + revIdxInsertWalk) [.reg 0, .reg 1, .reg 9, .reg 14, .reg 15, .reg 11, .reg 5])
      st o st' c ∧
      normalPost (fun st₁ =>
        dsSetLevelWalksInv L vCap eCap b lvl eListPtr mEmbPtr heapPtr gen0 G H eL emb foot0 mem (k + 1)
          { st₁ with regs := Function.update st₁.regs 6 (k + 1) } ∧
        st₁.regs 6 = k) o st' ∧
      c ≤ 380 * (emb (eL[k]'hk)).length + 540 := by
  let domAddr := dsDomGenBase b L vCap eCap + lvl
  let footOf (heapCur : ℕ) (a : ℕ) : Prop := foot0 a ∨ (heapPtr ≤ a ∧ a < heapCur)
  let heapMax := heapPtr + 2 * (eL.map fun e => (emb e).length + 1).sum
  have hf := dsFixedSize_add b L vCap eCap
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have h4 := dsRevHeadBase_eq b L vCap eCap
  have h5 := dsVStampBase_eq b L vCap eCap
  refine runs_start_le ?_
  rcases hInv with ⟨heapCur, revCur, hhp1, hhp2, hr0, hr1, hr2, hr3, hr4, hr5, hr6,
    hr7, hr8, hr10, hr11, hr12, hr13, hgen_st, hdom_st, hvst_st, hedg_le, hedg_st, hpi_st,
    hrev_st, hfr⟩
  let e := eL[k]'hk
  obtain ⟨heG, hWalk, hMWalk, hwPtr_lo, hwPtr_hi⟩ := heL_spec e (List.getElem_mem hk)
  have he_cap : e < eCap := heG_cov e heG
  have he_ltw : e < 2 ^ w := by omega
  have hsum_succ : ((eL.take k).map fun e => (emb e).length + 1).sum + ((emb e).length + 1) ≤
      (eL.map fun e => (emb e).length + 1).sum := by
    rw [← take_succ_sum_walks eL emb hk]; exact take_sum_walks_le eL emb (k + 1)
  have hheap_cur_max : heapCur ≤ heapMax := by omega
  have hheap_step_lt : heapCur + 2 * ((emb e).length + 1) < 2 ^ w := by omega
  have heList_k : st.mem (eListPtr + k) = e :=
    (hfr _ (dsLevelWalksFrameCond_mono hheap_cur_max (hfr_eList k hk))).trans (heL_at k hk)
  have heList_k_lt : eListPtr + k < 2 ^ w := by omega
  have hmul_idx : lvl * eCap + e < (L + 1) * eCap := by
    calc lvl * eCap + e < lvl * eCap + eCap := Nat.add_lt_add_left he_cap _
      _ = (lvl + 1) * eCap := by ring
      _ ≤ (L + 1) * eCap := Nat.mul_le_mul_right eCap (Nat.succ_le_succ hlvlL)
  have hed_pi : dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap ≤ dsPiPtrBase b L vCap eCap := by
    simp [dsPiPtrBase]
  have hpi_rev : dsPiPtrBase b L vCap eCap + (L + 1) * eCap = dsRevGenBase b L vCap eCap := rfl
  have hvst_fix : dsVStampBase b L vCap eCap + vCap ≤ b + dsFixedSize L vCap eCap := by
    rw [← hf]; simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase]; omega
  have heC_ltw : eCap < 2 ^ w := by
    have : eCap ≤ (L + 1) * eCap := Nat.le_mul_of_pos_left eCap (Nat.succ_pos L)
    omega
  have hmul_ltw : lvl * eCap < 2 ^ w := by omega
  have hmul_add_ltw : lvl * eCap + e < 2 ^ w := by omega
  have hed_addr_lt : dsEdgeDomGenBase b L vCap eCap + (lvl * eCap + e) < 2 ^ w := by omega
  have hpi_addr_lt : dsPiPtrBase b L vCap eCap + (lvl * eCap + e) < 2 ^ w := by omega
  have hed_eq : dsEdgeDomGenBase b L vCap eCap + (lvl * eCap + e) =
      dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e := by omega
  have hpi_eq : dsPiPtrBase b L vCap eCap + (lvl * eCap + e) =
      dsPiPtrBase b L vCap eCap + lvl * eCap + e := by omega
  have hmEmb_e : st.mem (mEmbPtr + e) = mem (mEmbPtr + e) :=
    hfr _ (dsLevelWalksFrameCond_mono hheap_cur_max (hfr_mEmb e (List.getElem_mem hk)))
  have hmEmb_e_lt : mEmbPtr + e < 2 ^ w := by omega
  have hwPtr_lt : mem (mEmbPtr + e) + (1 + 2 * (emb e).length) ≤ heapCur := by
    have hml := mWalkEncode_length (emb e)
    omega
  have hwPtr_ltw : mem (mEmbPtr + e) < 2 ^ w := by omega
  have hmWalk_st : MWalkAt st.mem (mem (mEmbPtr + e)) (emb e) := by
    refine hMWalk.of_agree fun addr ha1 ha2 => ?_
    have hml := mWalkEncode_length (emb e)
    exact hfr addr (dsLevelWalksFrameCond_heap_lt hlvlL (le_trans hwPtr_lo ha1) (by omega))
  have hg_dom : dsGPtr b + dynGraphSize vCap eCap ≤ dsDomGenBase b L vCap eCap := by
    rw [h2, h1]; simp [dsGPtr]; omega
  have hh_dom : dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsDomGenBase b L vCap eCap := by
    rw [h2, h1]; simp [dsHPtr, dsGPtr, dsHdrSize]; omega
  have h_hb : b + dsHdrSize ≤ dsHPtr b vCap eCap := by simp [dsHPtr, dsGPtr]
  have hb_gen_lt : b + dsGenOff < b + dsHdrSize := by simp [dsGenOff, dsHdrSize]
  have hmin_ge : b + dsHdrSize ≤ dsMinHBase b vCap eCap := by rw [h1]; omega
  have hdom_ge_min : dsMinHBase b vCap eCap ≤ dsDomGenBase b L vCap eCap := by rw [h2]; omega
  have hdom_ed : dsDomGenBase b L vCap eCap + (L + 1) = dsEdgeDomGenBase b L vCap eCap := rfl
  have hdom_eq : domAddr = dsDomGenBase b L vCap eCap + lvl := rfl
  have hdom_lt_ed : domAddr < dsEdgeDomGenBase b L vCap eCap := by dsimp [domAddr]; omega
  have hed_addr : dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e < b + dsFixedSize L vCap eCap := by
    omega
  have hpi_addr : dsPiPtrBase b L vCap eCap + lvl * eCap + e < b + dsFixedSize L vCap eCap := by
    omega
  have hne_mEmb_ed : mEmbPtr + e ≠ dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e := by
    intro heq
    have := hfr_mEmb e (List.getElem_mem hk)
    rw [heq] at this
    exact this.2.2.1 e he_cap rfl
  have hed_ne_pi : ∀ e', dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e ≠
      dsPiPtrBase b L vCap eCap + lvl * eCap + e' := by
    intro e'
    omega
  have hed'_ne_pi : ∀ e' < eCap, dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e' ≠
      dsPiPtrBase b L vCap eCap + lvl * eCap + e := by
    intro e' he'
    have hm' : lvl * eCap + e' < (L + 1) * eCap := by
      calc lvl * eCap + e' < lvl * eCap + eCap := Nat.add_lt_add_left he' _
        _ = (lvl + 1) * eCap := by ring
        _ ≤ (L + 1) * eCap := Nat.mul_le_mul_right eCap (Nat.succ_le_succ hlvlL)
    omega
  refine runs_seq_assign_le (v := e)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr2, hr6, heList_k_lt]) heList_k) ?_
  refine runs_seq_assign_le (v := lvl * eCap + e)
    (by simp [Expr.eval, BinOp.eval, hr1, hr7, hmul_ltw, hmul_add_ltw]) ?_
  refine runs_seq_store_le (x := dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e) (v := gen0 + 1)
    (by rw [← hed_eq]; simp [Expr.eval, BinOp.eval, hr12, hed_addr_lt])
    (by simp [Expr.eval, hr8]) ?_
  refine runs_seq_assign_le (v := mem (mEmbPtr + e))
    (Expr.eval_load_of_eq (x := mEmbPtr + e) (by simp [Expr.eval, BinOp.eval, hr4, hmEmb_e_lt])
      (by dsimp; rw [Function.update_of_ne hne_mEmb_ed, hmEmb_e])) ?_
  refine runs_seq_store_le (x := dsPiPtrBase b L vCap eCap + lvl * eCap + e)
    (v := mem (mEmbPtr + e))
    (by rw [← hpi_eq]; simp [Expr.eval, BinOp.eval, hr13, hpi_addr_lt])
    (by simp [Expr.eval]) ?_
  let mem2 := Function.update
    (Function.update st.mem (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e) (gen0 + 1))
    (dsPiPtrBase b L vCap eCap + lvl * eCap + e) (mem (mEmbPtr + e))
  have hmem2_fr : ∀ a,
      a ≠ dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e →
      a ≠ dsPiPtrBase b L vCap eCap + lvl * eCap + e →
      mem2 a = st.mem a := fun a ha1 ha2 => by
    dsimp only [mem2]
    rw [Function.update_of_ne ha2, Function.update_of_ne ha1]
  have hG_st : DynGraphAt mem2 (dsGPtr b) vCap eCap G := by
    refine dynGraphAt_of_agree hG fun a ha1 ha2 => ?_
    dsimp only [dsGPtr] at ha1
    rw [hmem2_fr a (by omega) (by omega)]
    exact hfr a (dsLevelWalksFrameCond_lt_domGen hfix_le (by omega)
      (by simp [dsGenOff, dsHdrSize] at *; omega))
  have hpre_tail : (dgGetTailContract w vCap eCap G).pre [dsGPtr b, e] mem2 :=
    ⟨dsGPtr b, e, rfl, hw16, by omega, heG, hG_st⟩
  refine runs_seq_call_le (r := 14) (dgGetTail_meetsContract hpOps)
    (by simp [Expr.eval, evalArgs, hr10])
    (fun z hz => by simp at hz; rcases hz with rfl | rfl <;> omega)
    hpre_tail ?_
  intro retT memT posT ⟨_, _, hEqT, hmT, hretT⟩
  simp only [List.cons.injEq, and_true] at hEqT
  rcases hEqT with ⟨rfl, rfl⟩
  subst hmT
  have hH_st : DynGraphAt mem2 (dsHPtr b vCap eCap) vCap eCap H := by
    refine dynGraphAt_of_agree hH fun a ha1 ha2 => ?_
    rw [hmem2_fr a (by omega) (by omega)]
    exact hfr a (dsLevelWalksFrameCond_lt_domGen hfix_le (by omega)
      (by simp [dsGenOff, dsHdrSize] at *; omega))
  have hmWalk_2 : MWalkAt mem2 (mem (mEmbPtr + e)) (emb e) :=
    hmWalk_st.of_agree fun a ha1 ha2 => hmem2_fr a (by omega) (by omega)
  have htail_V : G.tail e ∈ H.V := hGV_HV ((hG_val e heG).1)
  have htail_vCap : G.tail e < vCap := hvH _ htail_V
  have hpre_ins : (dsInsertWalkRevContract w L vCap eCap b lvl e (G.tail e)
      H (emb e) revCur (footOf heapCur)).pre
      [b, lvl, e, G.tail e, mem (mEmbPtr + e), dsHPtr b vCap eCap, heapCur] mem2 := by
    refine ⟨mem (mEmbPtr + e), dsHPtr b vCap eCap, heapCur, rfl, hw16, by omega,
      by omega, hlvlL, he_ltw, htail_vCap, hwPtr_lo, ?_, by simp [dsHPtr, dsGPtr],
      by rw [h1]; simp [dsHPtr, dsGPtr]; omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hH_st, hH_val, hvH, heH, htail_V,
      ⟨G.head e, hWalk⟩, hmWalk_2, ?_⟩
    · omega
    · rw [hmem2_fr _ (by simp [dsLOff, dsGenOff, dsHdrSize] at *; omega)
        (by simp [dsLOff, dsGenOff, dsHdrSize] at *; omega)]
      exact (hfr _ (dsLevelWalksFrameCond_lt_domGen hfix_le (by simp [dsLOff]; omega)
        (by simp [dsLOff, dsGenOff]))).trans hL
    · rw [hmem2_fr _ (by simp [dsVCapOff, dsGenOff, dsHdrSize] at *; omega)
        (by simp [dsVCapOff, dsGenOff, dsHdrSize] at *; omega)]
      exact (hfr _ (dsLevelWalksFrameCond_lt_domGen hfix_le (by simp [dsVCapOff]; omega)
        (by simp [dsVCapOff, dsGenOff]))).trans hvC
    · rw [hmem2_fr _ (by simp [dsECapOff, dsGenOff, dsHdrSize] at *; omega)
        (by simp [dsECapOff, dsGenOff, dsHdrSize] at *; omega)]
      exact (hfr _ (dsLevelWalksFrameCond_lt_domGen hfix_le (by simp [dsECapOff]; omega)
        (by simp [dsECapOff, dsGenOff]))).trans heC
    · rw [hmem2_fr _ (by simp [dsGenOff, dsHdrSize] at *; omega)
        (by simp [dsGenOff, dsHdrSize] at *; omega), hgen_st]
      omega
    · rw [hmem2_fr _ (by omega) (by omega), hdom_st]; omega
    · intro v hv
      rw [hmem2_fr _ (by omega) (by omega),
        hmem2_fr _ (by simp [dsGenOff, dsHdrSize] at *; omega)
          (by simp [dsGenOff, dsHdrSize] at *; omega)]
      exact hvst_st v hv
    · intro a ha
      rcases ha with ha0 | ⟨ha1, ha2⟩
      · exact ⟨(hfoot0 a ha0).1, lt_of_lt_of_le (hfoot0 a ha0).2 hhp1⟩
      · exact ⟨le_trans hfix_le ha1, ha2⟩
    · intro v hv
      rw [hmem2_fr _ (by omega) (by omega), hmem2_fr _ (by omega) (by omega)]
      have hr_v := hrev_st v hv
      rw [hdom_st] at hr_v ⊢
      by_cases hcond : st.mem (dsRevGenBase b L vCap eCap + lvl * vCap + v) = gen0 + 1
      · simp only [hcond, Nat.zero_lt_succ, and_self, ↓reduceIte] at hr_v ⊢
        rw [hmem2_fr _ (by omega) (by omega)]
        exact hr_v.2.2.2.of_agree fun a ha => by
          rcases ha with ha0 | ⟨ha1, ha2⟩
          · exact hmem2_fr a (by have := (hfoot0 a ha0).1; omega) (by have := (hfoot0 a ha0).1; omega)
          · exact hmem2_fr a (by omega) (by omega)
      · simp only [hcond, and_false, ↓reduceIte] at hr_v ⊢
        exact hr_v.2.2.2
  refine runs_call_le (r := 5) (dsInsertWalkRev_meetsContract hpRev hpOps)
    (by simp [Expr.eval, evalArgs, hr0, hr1, hr5, hr11, hretT])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    hpre_ins ?_
  intro heapNext mem3 pos3 hpost3
  change (dsInsertWalkRevContract w L vCap eCap b lvl e (G.tail e)
      H (emb e) revCur (footOf heapCur)).post
      [b, lvl, e, G.tail e, mem (mEmbPtr + e), dsHPtr b vCap eCap, heapCur]
      mem2 heapNext mem3 at hpost3
  rcases hpost3 with ⟨wPtr3, hPtr3, heapPtr3, hEq3, hhpN1, hhpN2, hgen3, hvst3, hrev3, hfr3⟩
  simp only [List.cons.injEq, and_true] at hEq3
  rcases hEq3 with ⟨_, _, _, _, rfl, rfl, rfl⟩
  obtain ⟨hhp_ub, hmem3_gen, hmem3_dom, hedg_le3, hedg_st3, hpi_st3, hrev_st3, hfr3_out⟩ :=
    dsSetLevelWalks_step_post hlvlL hfix_le heL_nd heG_cov hvH heL_spec hk hhp1 hhp2
      hgen_st hdom_st hedg_le hedg_st hpi_st hrev_st hfr he_cap hmWalk_2 hhpN1 hhpN2 hgen3
      hrev3 hfr3
  dsimp only [normalPost]
  refine ⟨⟨⟨heapNext, fun v => if v ∈ H.walkVertices (G.tail e) (emb e) then e :: revCur v else revCur v,
    le_trans hhp1 (by omega), hhp_ub,
    by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
    by simp, by simp, by simp [hr7], by simp [hr8],
    by simp [hr10], by simp [hr11], by simp [hr12], by simp [hr13],
    hmem3_gen, hmem3_dom, hvst3, hedg_le3, hedg_st3, hpi_st3, hrev_st3, hfr3_out⟩,
    by simp [hr6]⟩, ?_⟩
  · dsimp only [e, dsInsertWalkRevContract, dgGetTailContract, argsSize, Expr.size]
    omega

end

end MinCostFlow.DynSpanner.Program
