module

public import MinCostFlow.DynSpanner.Program.DynSpannerRevDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerRevCons

import Mathlib.Tactic.Linarith
import MinCostFlow.DynSpanner.Program.DynSpannerRevHelpers
import MinCostFlow.DynSpanner.Program.DynSpannerRevStep

/-!
# Reverse-index walk insertion verification (`DynSpannerRev`)

Re-exports `revProcs`, contracts, and `dsRevCons_meetsContract` from `DynSpannerRevDefs` and
`DynSpannerRevCons`, and proves `dsInsertWalkRev_meetsContract` (`revIdxInsertWalk = 1`),
inserting edge `e` into `revLists i v` for every vertex `v ∈ H.walkVertices uStart W` in
`O(W.length + 1)` time.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public theorem dsInsertWalkRev_meetsContract {w L vCap eCap b i e uStart : ℕ}
    {H : MGraph} {W : List (ℕ × Bool)} {rev0 : ℕ → List ℕ} {foot0 : ℕ → Prop}
    {p : Program} {bOps bRev : ℕ}
    (hpRev : p.HasAt bRev (revProcs bOps bRev))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bRev + revIdxInsertWalk)
      (dsInsertWalkRevContract w L vCap eCap b i e uStart H W rev0 foot0) := by
  refine meetsContract_of_runs
    (hpRev.get (i := revIdxInsertWalk) (by simp [revProcs, revIdxInsertWalk]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨wPtr, hPtr, heapPtr, rfl, hw16, hfix_le, hheap_lt,
    hiL, he_lt, hu_vCap, hfix_w, hw_hp, hb_h, hh_min,
    hL, hvC, heC, hgen_lt, hdom_pos, hvst0, hfoot0, hH, hH_val, hvH, heH, huH, ⟨vEnd, hWalk⟩,
    hMWalk, hrev0⟩
  have hb_ltw : b < 2 ^ w := hargs b (by simp)
  have hi_ltw : i < 2 ^ w := hargs i (by simp)
  have he_ltw : e < 2 ^ w := hargs e (by simp)
  have hu_ltw : uStart < 2 ^ w := hargs uStart (by simp)
  have hwPtr_ltw : wPtr < 2 ^ w := hargs wPtr (by simp)
  have hhPtr_ltw : hPtr < 2 ^ w := hargs hPtr (by simp)
  have hh_ltw : hPtr + dynGraphSize vCap eCap < 2 ^ w := by
    have := dsFixedSize_ge_aux b L vCap eCap
    have := dsMinHBase_eq b vCap eCap
    have := dsDomGenBase_eq b L vCap eCap
    have := dsRevGenBase_eq b L vCap eCap
    have := dsRevHeadBase_eq b L vCap eCap
    have := dsVStampBase_eq b L vCap eCap
    have := dsMEmbTempBase_eq_rev b L vCap eCap
    have := dsFixedSize_add b L vCap eCap
    omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h5_lt : (5 : ℕ) < 2 ^ w := by omega
  have hdisjU := dsLayout_facts hiL hu_vCap hiL hu_vCap hfix_le
  have hvs_u_lt : dsVStampBase b L vCap eCap + uStart < 2 ^ w := by linarith only [hdisjU.vs_lt_hp, hheap_lt]
  have hgen_lt_fix : b + dsGenOff < b + dsFixedSize L vCap eCap := by
    have hgd : dsGenOff < dsHdrSize := by decide
    have h1 := dsMinHBase_eq b vCap eCap; have h2 := dsDomGenBase_eq b L vCap eCap
    have h3 := dsRevGenBase_eq b L vCap eCap; have h4 := dsRevHeadBase_eq b L vCap eCap
    have h5 := dsVStampBase_eq b L vCap eCap; have hm := dsMEmbTempBase_eq_rev b L vCap eCap
    have hf := dsFixedSize_add b L vCap eCap; omega
  refine runs_start_le ?_
  dsimp only [revProcs, revIdxInsertWalk, List.getElem_cons_succ, List.getElem_cons_zero,
    dsInsertWalkRevStmt]
  refine dsInsertWalkRevPrep_cont hw16 hb_ltw hfix_le (by linarith only [hheap_lt]) hL hvC heC
    (cCont := 380 * W.length + 330)
    (cTot := (dsInsertWalkRevContract w L vCap eCap b i e uStart H W rev0 foot0).cost
      [b, i, e, uStart, wPtr, hPtr, heapPtr] mem)
    (by dsimp [dsInsertWalkRevContract]; omega) ?_
  intro st1 ω1 ⟨hm1, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩
  set gen0 := mem (b + dsGenOff)
  set domAddr := dsDomGenBase b L vCap eCap + i
  set domVal := mem domAddr
  set vStamp := dsVStampBase b L vCap eCap
  have hgen5_lt : mem (b + 5) + 1 < 2 ^ w := by simpa [gen0, dsGenOff] using hgen_lt
  have hb5_ltw : b + 5 < 2 ^ w := by
    have hdg5 : dsGenOff = 5 := rfl
    linarith only [hgen_lt_fix, hfix_le, hheap_lt, hdg5]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := gen0 + 1)
    (Expr.eval_bin (Expr.eval_load_of_eq (x := b + dsGenOff)
        (by simp [Expr.eval, BinOp.eval, r0, dsGenOff, h5_lt, hb5_ltw])
      (by simpa [gen0, dsGenOff] using congrFun hm1 (b + dsGenOff)))
      (Expr.eval_const h1_lt) (by simp [BinOp.eval, hgen_lt])) ?_
  refine runs_seq_store_le (x := b + dsGenOff) (v := gen0 + 1)
    (by simp [Expr.eval, BinOp.eval, r0, dsGenOff, h5_lt, hb5_ltw])
    (by simp [Expr.eval]) ?_
  refine runs_seq_store_le (x := vStamp + uStart) (v := gen0 + 1)
    (by simp [Expr.eval, BinOp.eval, r3, r10, vStamp, hvs_u_lt])
    (by simp [Expr.eval]) ?_
  have h_l_vs : b + dsLOff ≠ vStamp + uStart := by
    have : dsLOff < dsHdrSize := by decide
    have := dsFixedSize_ge_aux b L vCap eCap; have := dsVStampBase_eq b L vCap eCap
    have := dsRevHeadBase_eq b L vCap eCap; have := dsRevGenBase_eq b L vCap eCap
    have := dsDomGenBase_eq b L vCap eCap; have := dsMinHBase_eq b vCap eCap
    omega
  have h_vc_vs : b + dsVCapOff ≠ vStamp + uStart := by
    have : dsVCapOff < dsHdrSize := by decide
    have := dsFixedSize_ge_aux b L vCap eCap; have := dsVStampBase_eq b L vCap eCap
    have := dsRevHeadBase_eq b L vCap eCap; have := dsRevGenBase_eq b L vCap eCap
    have := dsDomGenBase_eq b L vCap eCap; have := dsMinHBase_eq b vCap eCap
    omega
  have h_ec_vs : b + dsECapOff ≠ vStamp + uStart := by
    have : dsECapOff < dsHdrSize := by decide
    have := dsFixedSize_ge_aux b L vCap eCap; have := dsVStampBase_eq b L vCap eCap
    have := dsRevHeadBase_eq b L vCap eCap; have := dsRevGenBase_eq b L vCap eCap
    have := dsDomGenBase_eq b L vCap eCap; have := dsMinHBase_eq b vCap eCap
    omega
  have hpre_cons0 : (dsRevConsContract w L vCap eCap b i uStart e (rev0 uStart) foot0).pre
      [b, i, uStart, e, heapPtr]
      (Function.update (Function.update mem (b + dsGenOff) (gen0 + 1)) (vStamp + uStart) (gen0 + 1)) := by
    refine ⟨heapPtr, rfl, hw16, hfix_le, by linarith only [hheap_lt], hiL, hu_vCap, he_lt,
      ?_, ?_, ?_, ?_, hfoot0, ?_⟩
    · rw [Function.update_of_ne h_l_vs, Function.update_of_ne (by simp [dsLOff, dsGenOff])]
      exact hL
    · rw [Function.update_of_ne h_vc_vs, Function.update_of_ne (by simp [dsVCapOff, dsGenOff])]
      exact hvC
    · rw [Function.update_of_ne h_ec_vs, Function.update_of_ne (by simp [dsECapOff, dsGenOff])]
      exact heC
    · rw [Function.update_of_ne hdisjU.vs_ne_dom.symm, Function.update_of_ne hdisjU.dom_ne_gen]
      exact hdom_pos
    · rw [Function.update_of_ne hdisjU.vs_ne_dom.symm, Function.update_of_ne hdisjU.dom_ne_gen,
        Function.update_of_ne hdisjU.vs_ne_rg.symm,
        Function.update_of_ne hdisjU.rg_ne_gen]
      have hh0 := hrev0 uStart hu_vCap
      split_ifs at hh0 ⊢ with hcond
      · rw [Function.update_of_ne hdisjU.vs_ne_rh.symm,
          Function.update_of_ne hdisjU.rh_ne_gen]
        refine hh0.of_agree fun a ha => ?_
        have hab := hfoot0 a ha
        rw [Function.update_of_ne (by linarith only [hab.1, hdisjU.vs_lt_fix]),
          Function.update_of_ne (by linarith only [hab.1, hgen_lt_fix])]
      · exact hh0
  have hpre_cons0_st : (dsRevConsContract w L vCap eCap b i uStart e (rev0 uStart) foot0).pre
      [b, i, uStart, e, heapPtr]
      (Function.update (Function.update st1.mem (b + dsGenOff) (gen0 + 1)) (vStamp + uStart) (gen0 + 1)) := by
    simpa [hm1] using hpre_cons0
  refine runs_seq_call_le (r := 6) (dsRevCons_meetsContract hpRev)
    (by simp [Expr.eval, evalArgs, r0, r1, r3, r2, r6])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> linarith only [hb_ltw, hi_ltw, hu_ltw, he_ltw, hheap_lt])
    hpre_cons0_st ?_
  intro ret0 mem0 pos0 hpost0
  rcases hpost0 with ⟨hp0, hEq0, rfl, hrg0, hll0, hfr0⟩
  simp only [List.cons.injEq, true_and, and_true] at hEq0
  subst hEq0
  have hfr0' : ∀ addr,
      addr ≠ dsRevGenBase b L vCap eCap + i * vCap + uStart →
      addr ≠ dsRevHeadBase b L vCap eCap + i * vCap + uStart →
      addr ≠ heapPtr → addr ≠ heapPtr + 1 →
      mem0 addr = Function.update (Function.update mem (b + dsGenOff) (gen0 + 1))
        (vStamp + uStart) (gen0 + 1) addr := fun addr a1 a2 a3 a4 => by
    have := hfr0 addr a1 a2 a3 a4
    simpa [hm1] using this
  have hrg0' : mem0 (dsRevGenBase b L vCap eCap + i * vCap + uStart) =
      Function.update (Function.update mem (b + dsGenOff) (gen0 + 1))
        (vStamp + uStart) (gen0 + 1) domAddr := by
    simpa [hm1] using hrg0
  have hw_gen : wPtr ≠ b + dsGenOff := Nat.ne_of_gt (by linarith only [hfix_w, hgen_lt_fix])
  have hw_ne_hp : wPtr ≠ heapPtr := Nat.ne_of_lt (by linarith only [hw_hp])
  have hw_ne_hp1 : wPtr ≠ heapPtr + 1 := Nat.ne_of_lt (by linarith only [hw_hp])
  have hmW0 : mem0 wPtr = W.length := by
    have hagree : mem0 wPtr = mem wPtr := by
      refine (hfr0' wPtr (Nat.ne_of_gt (by linarith only [hfix_w, hdisjU.rg_lt_fix]))
        (Nat.ne_of_gt (by linarith only [hfix_w, hdisjU.rh_lt_fix]))
        hw_ne_hp hw_ne_hp1).trans ?_
      rw [Function.update_of_ne (Nat.ne_of_gt (by linarith only [hfix_w, hdisjU.vs_lt_fix])),
        Function.update_of_ne hw_gen]
    exact hagree.trans (MWalkAt_head hMWalk)
  refine runs_seq_assign_le (v := W.length)
    (Expr.eval_load_of_eq (by simp [Expr.eval, r4]) hmW0) ?_
  let Inv := dsInsertWalkRevInv L vCap eCap b i e uStart wPtr hPtr heapPtr gen0 H W rev0 foot0 mem
  let P0 : State → Prop := fun st => Inv 0 { st with regs := Function.update st.regs 13 0 }
  have hLoop : Triple w p P0
      (WordRAM.forRange 13 (.const 0) (.reg 12)
        (.assign 14 (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 13))) ;;
         .assign 15 (.load (.bin .add (.reg 4) (.reg 14))) ;;
         .assign 14 (.load (.bin .add (.bin .add (.reg 4) (.reg 14)) (.const 1))) ;;
         .cond (.reg 14)
           (.call 15 (bOps + dgIdxGetHead) [.reg 5, .reg 15])
           (.call 15 (bOps + dgIdxGetTail) [.reg 5, .reg 15]) ;;
         .assign 14 (.load (.bin .add (.reg 10) (.reg 15))) ;;
         .cond (.bin .eq (.reg 14) (.reg 11))
           (.nop)
           (.store (.bin .add (.reg 10) (.reg 15)) (.reg 11) ;;
            .call 6 (bRev + revIdxRevCons) [.reg 0, .reg 1, .reg 15, .reg 2, .reg 6])))
      (normalPost (Inv W.length))
      (fun _ => (W.length - 0) * (360 + (.reg 12 : Expr).size + 8) +
        ((.const 0 : Expr).size + (.reg 12 : Expr).size + 5)) := by
    clear hpre_cons0 hpre_cons0_st hrg0 hll0 hfr0 hfr0' hrg0' hmW0
    refine Triple.forRange_const (P := P0) (Inv := Inv) 360 0 W.length (Nat.zero_le _) h1_lt
      (fun _ => show W.length < 2 ^ w by linarith only [hheap_lt])
      (fun st hP0 => ⟨by eval_expr, hP0⟩)
      (fun k st _ _ hInv => by
        rcases hInv with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hr13, _⟩
        exact hr13)
      (fun k st _ _ hInv => by
        rcases hInv with ⟨_, _, _, _, _, _, _, _, _, _, _, hr12, _⟩
        simp [Expr.eval, hr12])
      (fun k _ hk st ω hInv =>
        dsInsertWalkRev_step_triple hpRev hpOps hw16 hfix_le hheap_lt hiL he_lt hfix_w hw_hp
          hb_h hh_min hL hvC heC hgen_lt hdom_pos hfoot0 hH hH_val hvH heH huH hWalk hMWalk
          hb_ltw hi_ltw he_ltw hwPtr_ltw hhPtr_ltw hh_ltw hk (ω := ω) hInv)
  refine runs_seq_triple_le hLoop ?_ ?_
  · refine ⟨heapPtr + 2, le_rfl, by omega, by simp [r0], by simp [r1], by simp [r2],
      by simp [r4], by simp [r5], by simp, by simp [r10, vStamp], by simp, by simp, by simp, ?_, ?_, ?_, ?_⟩
    · dsimp only
      rw [hfr0' (b + dsGenOff) hdisjU.rg_ne_gen.symm
        hdisjU.rh_ne_gen.symm
        (Nat.ne_of_lt (by linarith only [hfix_le, hgen_lt_fix]))
        (Nat.ne_of_lt (by linarith only [hfix_le, hgen_lt_fix])),
        Function.update_of_ne hdisjU.vs_ne_gen.symm, Function.update_self]
    · intro v hv
      dsimp only
      have hwalk0 : H.walkVertices uStart (W.take 0) = [uStart] := by simp [MGraph.walkVertices]
      rw [hwalk0]
      have hd_v := dsLayout_facts hiL hv hiL hu_vCap hfix_le
      by_cases hvu : v = uStart
      · subst hvu
        simp only [List.mem_singleton, ↓reduceIte]
        rw [hfr0' (dsVStampBase b L vCap eCap + v) hd_v.vs_ne_rg hd_v.vs_ne_rh
          (Nat.ne_of_lt hd_v.vs_lt_hp)
          (Nat.ne_of_lt (Nat.lt_succ_of_lt hd_v.vs_lt_hp)),
          Function.update_self]
      · simp only [List.mem_singleton, hvu, ↓reduceIte]
        rw [hfr0' (dsVStampBase b L vCap eCap + v) hd_v.vs_ne_rg hd_v.vs_ne_rh
          (Nat.ne_of_lt hd_v.vs_lt_hp)
          (Nat.ne_of_lt (Nat.lt_succ_of_lt hd_v.vs_lt_hp)),
          Function.update_of_ne (by omega), Function.update_of_ne hd_v.vs_ne_gen]
        exact hvst0 v hv
    · intro v hv
      dsimp only
      have hwalk0 : H.walkVertices uStart (W.take 0) = [uStart] := by simp [MGraph.walkVertices]
      rw [hwalk0]
      have hd_v := dsLayout_facts hiL hv hiL hu_vCap hfix_le
      by_cases hvu : v = uStart
      · subst hvu
        simp only [List.mem_singleton, ↓reduceIte]
        have hdom_mem : Function.update (Function.update mem (b + dsGenOff) (gen0 + 1))
            (vStamp + v) (gen0 + 1) domAddr = domVal := by
          dsimp only [vStamp, domAddr, domVal]
          rw [Function.update_of_ne hdisjU.vs_ne_dom.symm, Function.update_of_ne hdisjU.dom_ne_gen]
        refine ⟨hrg0'.trans hdom_mem, ?_⟩
        exact hll0.mono fun a ha => by
          rcases ha with ha0 | rfl | rfl
          · exact Or.inl ha0
          · exact Or.inr ⟨le_rfl, by omega⟩
          · exact Or.inr ⟨by omega, by omega⟩
      · simp only [List.mem_singleton, hvu, ↓reduceIte]
        have hne_rg_rh0 : dsRevGenBase b L vCap eCap + i * vCap + v ≠
            dsRevHeadBase b L vCap eCap + i * vCap + uStart := dsRevGen_ne_dsRevHead hiL hv
        have hne_rh_rg0 : dsRevHeadBase b L vCap eCap + i * vCap + v ≠
            dsRevGenBase b L vCap eCap + i * vCap + uStart := (dsRevGen_ne_dsRevHead hiL hu_vCap).symm
        have hd_u := dsLayout_facts hiL hu_vCap hiL hv hfix_le
        have hrg_stay : mem0 (dsRevGenBase b L vCap eCap + i * vCap + v) =
            mem (dsRevGenBase b L vCap eCap + i * vCap + v) := by
          rw [hfr0' _ (by simp [hvu]) hne_rg_rh0
            (Nat.ne_of_lt hd_v.rg_lt_hp)
            (Nat.ne_of_lt (Nat.lt_succ_of_lt hd_v.rg_lt_hp)),
            Function.update_of_ne hd_u.vs_ne_rg.symm,
            Function.update_of_ne hd_v.rg_ne_gen]
        have hrh_stay : mem0 (dsRevHeadBase b L vCap eCap + i * vCap + v) =
            mem (dsRevHeadBase b L vCap eCap + i * vCap + v) := by
          rw [hfr0' _ hne_rh_rg0 (by simp [hvu])
            (Nat.ne_of_lt hd_v.rh_lt_hp)
            (Nat.ne_of_lt (Nat.lt_succ_of_lt hd_v.rh_lt_hp)),
            Function.update_of_ne hd_u.vs_ne_rh.symm,
            Function.update_of_ne hd_v.rh_ne_gen]
        refine ⟨hrg_stay, hrh_stay, ?_⟩
        have hr_v := hrev0 v hv
        dsimp only [domVal, domAddr] at hr_v
        by_cases hc : mem (dsRevGenBase b L vCap eCap + i * vCap + v) =
            mem (dsDomGenBase b L vCap eCap + i)
        · have hc0 : mem0 (dsRevGenBase b L vCap eCap + i * vCap + v) =
              mem (dsDomGenBase b L vCap eCap + i) := hrg_stay.trans hc
          simp only [hc, ↓reduceIte] at hr_v
          simp only [hc0, ↓reduceIte, hrh_stay]
          refine (hr_v.of_agree fun a ha => ?_).mono fun a ha => Or.inl ha
          have hab := hfoot0 a ha
          rw [hfr0' a (Nat.ne_of_gt (by linarith only [hab.1, hdisjU.rg_lt_fix]))
            (Nat.ne_of_gt (by linarith only [hab.1, hdisjU.rh_lt_fix]))
            (Nat.ne_of_lt hab.2) (Nat.ne_of_lt (Nat.lt_succ_of_lt hab.2)),
            Function.update_of_ne (Nat.ne_of_gt (by
              dsimp only [vStamp]; linarith only [hab.1, hdisjU.vs_lt_fix])),
            Function.update_of_ne (Nat.ne_of_gt (by linarith only [hab.1, hgen_lt_fix]))]
        · have hc0 : mem0 (dsRevGenBase b L vCap eCap + i * vCap + v) ≠
              mem (dsDomGenBase b L vCap eCap + i) := fun h => hc (hrg_stay.symm.trans h)
          simp only [hc, ↓reduceIte] at hr_v
          simp only [hc0, ↓reduceIte]
          exact hr_v
    · intro addr ha1 ha2 ha3 ha4 ha5
      have ha_ne_hp : addr ≠ heapPtr := by rcases ha5 with h | h; linarith only [h]; linarith only [h]
      have ha_ne_hp1 : addr ≠ heapPtr + 1 := by rcases ha5 with h | h; linarith only [h]; linarith only [h]
      dsimp only
      rw [hfr0' addr (ha3 uStart hu_vCap) (ha4 uStart hu_vCap) ha_ne_hp ha_ne_hp1,
        Function.update_of_ne (ha2 uStart hu_vCap), Function.update_of_ne ha1]
  · intro stF ⟨heapF, hhp1, hhp2, _, _, _, _, _, hr6, _, _, _, _, hmg, hvst, hrev, hfr⟩
    rw [List.take_length] at hvst hrev
    refine runs_ret_le (by simp [Expr.eval, hr6])
      ⟨wPtr, hPtr, heapPtr, rfl, hhp1, hhp2, hmg, ?_, hrev, hfr⟩ ?_
    · intro v hv
      have hvt := hvst v hv
      rw [hmg]
      split_ifs at hvt <;> omega
    · dsimp only [dsRevConsContract, argsSize, Expr.size]
      omega

end MinCostFlow.DynSpanner.Program
