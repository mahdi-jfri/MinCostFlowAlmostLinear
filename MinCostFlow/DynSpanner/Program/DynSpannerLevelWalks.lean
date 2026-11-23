module

public import MinCostFlow.DynSpanner.Program.DynSpannerLevelWalksDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerWriteIdEmb

import Mathlib.Tactic.Linarith
import MinCostFlow.DynSpanner.Program.DynSpannerSetLevelWalksStep

/-!
# Level-walk initialization verification (`DynSpannerLevelWalks`)

Re-exports `levelWalkProcs`, contracts, and `dsWriteIdEmb_meetsContract`, and proves
`dsSetLevelWalks_meetsContract` (`lwIdxSetLevelWalks = 1`), rebuilding a level's `edgeDomGen`,
`piPtr`, and reverse incidence lists `revLists` in `O(|eL| + ∑ (emb e).length + 1)` time.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

private lemma dsSetLevelWalks_initInv {L vCap eCap b lvl eListPtr mEmbPtr heapPtr : ℕ}
    {G H : MGraph} {eL : List ℕ} {emb : MinCostFlow.Embedding} {foot0 : ℕ → Prop}
    {mem mem0 : ℕ → ℕ} {regs0 : ℕ → ℕ} {pos0 : ℕ}
    (hlvlL : lvl ≤ L) (hdom_ge : dsMinHBase b vCap eCap ≤ dsDomGenBase b L vCap eCap)
    (hvst0 : ∀ v < vCap, mem (dsVStampBase b L vCap eCap + v) ≤ mem (b + dsGenOff))
    (hedg0 : ∀ e < eCap, mem (dsEdgeDomGenBase b L vCap eCap + lvl * eCap + e) ≤ mem (b + dsGenOff))
    (hrevg0 : ∀ v < vCap, mem (dsRevGenBase b L vCap eCap + lvl * vCap + v) ≤ mem (b + dsGenOff))
    (hne_gen_dom : b + dsGenOff ≠ dsDomGenBase b L vCap eCap + lvl)
    (hmem0 : mem0 = Function.update (Function.update mem (b + dsGenOff) (mem (b + dsGenOff) + 1))
      (dsDomGenBase b L vCap eCap + lvl) (mem (b + dsGenOff) + 1))
    (hr0 : regs0 0 = b) (hr1 : regs0 1 = lvl) (hr2 : regs0 2 = eListPtr) (hr3 : regs0 3 = eL.length)
    (hr4 : regs0 4 = mEmbPtr) (hr5 : regs0 5 = heapPtr) (hr6 : regs0 6 = 0)
    (hr7 : regs0 7 = eCap) (hr8 : regs0 8 = mem (b + dsGenOff) + 1) (hr10 : regs0 10 = dsGPtr b)
    (hr11 : regs0 11 = dsHPtr b vCap eCap) (hr12 : regs0 12 = dsEdgeDomGenBase b L vCap eCap)
    (hr13 : regs0 13 = dsPiPtrBase b L vCap eCap) :
    dsSetLevelWalksInv L vCap eCap b lvl eListPtr mEmbPtr heapPtr (mem (b + dsGenOff)) G H eL emb
      foot0 mem 0 { mem := mem0, regs := regs0, pos := pos0 } := by
  subst hmem0
  have hf := dsFixedSize_add b L vCap eCap
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have h4 := dsRevHeadBase_eq b L vCap eCap
  have h5 := dsVStampBase_eq b L vCap eCap
  have hb_gen_lt : b + dsGenOff < b + dsHdrSize := by simp [dsGenOff, dsHdrSize]
  have hmin_ge : b + dsHdrSize ≤ dsMinHBase b vCap eCap := by rw [h1]; omega
  have hdom_ed : dsDomGenBase b L vCap eCap + (L + 1) = dsEdgeDomGenBase b L vCap eCap := rfl
  have hed_pi : dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap ≤ dsPiPtrBase b L vCap eCap := by
    simp [dsPiPtrBase]
  have hpi_rev : dsPiPtrBase b L vCap eCap + (L + 1) * eCap = dsRevGenBase b L vCap eCap := rfl
  have hdom_lt_ed : dsDomGenBase b L vCap eCap + lvl < dsEdgeDomGenBase b L vCap eCap := by omega
  refine ⟨heapPtr, fun _ => [], le_rfl, by simp, hr0, hr1, hr2, hr3, hr4, hr5, hr6,
    hr7, hr8, hr10, hr11, hr12, hr13,
    by simp [Function.update_of_ne hne_gen_dom], Function.update_self _ _ _,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    dsimp only
    rw [Function.update_of_ne hne_gen_dom, Function.update_self,
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact le_trans (hvst0 v hv) (Nat.le_succ _)
  · intro e he
    dsimp only
    rw [Function.update_of_ne hne_gen_dom, Function.update_self,
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact le_trans (hedg0 e he) (Nat.le_succ _)
  · intro e he
    dsimp only
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    simp [Nat.ne_of_lt (Nat.lt_succ_of_le (hedg0 e he))]
  · simp
  · intro v hv
    dsimp only
    have hrg := hrevg0 v hv
    refine ⟨?_, List.nodup_nil, by simp, ?_⟩
    · rw [Function.update_of_ne hne_gen_dom, Function.update_self,
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact le_trans hrg (Nat.le_succ _)
    · simp only [Function.update_self,
        Function.update_of_ne (by omega : dsRevGenBase b L vCap eCap + lvl * vCap + v ≠ dsDomGenBase b L vCap eCap + lvl),
        Function.update_of_ne (by omega : dsRevGenBase b L vCap eCap + lvl * vCap + v ≠ b + dsGenOff),
        Nat.ne_of_lt (Nat.lt_succ_of_le hrg), and_false, ↓reduceIte]
  · intro addr hfc
    dsimp only
    rw [Function.update_of_ne hfc.2.1, Function.update_of_ne hfc.1]

public theorem dsSetLevelWalks_meetsContract {w L vCap eCap b lvl : ℕ}
    {G H : MGraph} {eL : List ℕ} {emb : MinCostFlow.Embedding} {foot0 : ℕ → Prop}
    {p : Program} {bOps bRev bLW : ℕ}
    (hpLW : p.HasAt bLW (levelWalkProcs bOps bRev))
    (hpRev : p.HasAt bRev (revProcs bOps bRev))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bLW + lwIdxSetLevelWalks)
      (dsSetLevelWalksContract w L vCap eCap b lvl G H eL emb foot0) := by
  refine meetsContract_of_runs
    (hpLW.get (i := lwIdxSetLevelWalks) (by simp [levelWalkProcs, lwIdxSetLevelWalks]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨eListPtr, mEmbPtr, heapPtr, rfl, hw16, hb1, hlvlL, hfix_le, hheap_lt,
    heList_lt, hmEmb_lt, hL, hvC, heC, hgen_lt, hvst0, hedg0, hrevg0, hfoot0, hfr_eList, hfr_mEmb,
    heL_nd, heL_at, hG, hG_val, hvG, heG_cov, hH, hH_val, hGV_HV, hvH, heH, heL_spec⟩
  have hb_ltw : b < 2 ^ w := hargs b (by simp)
  have hlvl_ltw : lvl < 2 ^ w := hargs lvl (by simp)
  have heList_ltw : eListPtr < 2 ^ w := hargs eListPtr (by simp)
  have hlen_ltw : eL.length < 2 ^ w := hargs eL.length (by simp)
  have hmEmb_ltw : mEmbPtr < 2 ^ w := hargs mEmbPtr (by simp)
  have hhPtr_ltw : heapPtr < 2 ^ w := hargs heapPtr (by simp)
  have had := dsAddrs_bound (w := w) (L := L) (vCap := vCap) (eCap := eCap) hfix_le (by omega)
  rcases had with ⟨hdg_sz, hdg_lt, hmin_eq, hmin_lt, hdom_lt, hedg_lt, hpi_lt, hrevG_lt,
    hrevH_lt, hvs_fix, _, _⟩
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have h4 := dsRevHeadBase_eq b L vCap eCap
  have h5 := dsVStampBase_eq b L vCap eCap
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have h3_lt : (3 : ℕ) < 2 ^ w := by omega
  have h4_lt : (4 : ℕ) < 2 ^ w := by omega
  have h5_lt : (5 : ℕ) < 2 ^ w := by omega
  have h6_lt : (6 : ℕ) < 2 ^ w := by omega
  have h7_lt : (7 : ℕ) < 2 ^ w := by omega
  have h9_lt : (9 : ℕ) < 2 ^ w := by omega
  set gen0 := mem (b + dsGenOff)
  set domAddr := dsDomGenBase b L vCap eCap + lvl
  set heapMax := heapPtr + 2 * (eL.map fun e => (emb e).length + 1).sum
  have hg_ltw : dsGPtr b < 2 ^ w := by simp [dsGPtr]; omega
  have hh_ltw : dsHPtr b vCap eCap < 2 ^ w := by
    simp [dsHPtr, dsGPtr, dsHdrSize]; omega
  have hg_end : dsGPtr b + dynGraphSize vCap eCap ≤ dsHPtr b vCap eCap := le_rfl
  have hh_end : dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsAuxPtr b vCap eCap := le_rfl
  have ha_end : dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsMinHBase b vCap eCap := le_rfl
  have hdom_ge : dsMinHBase b vCap eCap ≤ dsDomGenBase b L vCap eCap := by omega
  have hdom_i_lt : dsDomGenBase b L vCap eCap + lvl < 2 ^ w := by omega
  have hf := dsFixedSize_add b L vCap eCap
  have hne_gen_dom : b + dsGenOff ≠ domAddr := by
    simp only [domAddr, dsDomGenBase_eq, dsMinHBase_eq, dsGenOff, dsHdrSize]; omega
  have hL_ltw : L < 2 ^ w := by
    have : L ≤ dsRevGenBase b L vCap eCap := by rw [h3]; omega
    omega
  have heC_ltw : eCap < 2 ^ w := by dsimp [dynGraphSize] at hdg_lt; omega
  refine runs_start_le ?_
  dsimp only [levelWalkProcs, lwIdxSetLevelWalks, List.getElem_cons_succ, List.getElem_cons_zero,
    dsSetLevelWalksStmt]
  refine runs_seq_assign_le (v := vCap)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, startState, dsVCapOff, h3_lt,
      show b + 3 < 2 ^ w by omega]) hvC) ?_
  refine runs_seq_assign_le (v := eCap)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, startState, dsECapOff, h4_lt,
      show b + 4 < 2 ^ w by omega]) heC) ?_
  refine runs_seq_assign_le (v := L)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, startState, dsLOff, h2_lt,
      show b + 2 < 2 ^ w by omega]) hL) ?_
  refine runs_seq_assign_le (v := dynGraphSize vCap eCap)
    (by simp [Expr.eval, BinOp.eval, h4_lt, h7_lt, h9_lt,
      show 7 * vCap < 2 ^ w by omega, show 9 * eCap < 2 ^ w by omega,
      show 7 * vCap + 9 * eCap < 2 ^ w by omega,
      show 4 + (7 * vCap + 9 * eCap) < 2 ^ w by omega]; omega) ?_
  have hb6_ltw : b + 6 < 2 ^ w := by dsimp only [dsGPtr, dsHdrSize] at hg_ltw; exact hg_ltw
  have hh_val_ltw : dsGPtr b + dynGraphSize vCap eCap < 2 ^ w := by
    dsimp only [dsHPtr] at hh_ltw; exact hh_ltw
  have hmin_sum_ltw : b + 6 + 3 * dynGraphSize vCap eCap < 2 ^ w := by
    have : b + 6 + 3 * dynGraphSize vCap eCap = dsMinHBase b vCap eCap := by
      simpa [dsHdrSize] using hmin_eq
    omega
  have hL1_ltw : L + 1 < 2 ^ w := by omega
  have hLe_ltw : (L + 1) * eCap < 2 ^ w := by
    have : dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap = dsPiPtrBase b L vCap eCap := rfl
    omega
  have hedg_unfold_ltw : dsDomGenBase b L vCap eCap + (L + 1) < 2 ^ w := hedg_lt
  have hpi_unfold_ltw : dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap < 2 ^ w := hpi_lt
  refine runs_seq_assign_le (v := dsGPtr b)
    (by simp [Expr.eval, BinOp.eval, startState, dsGPtr, dsHdrSize, h6_lt, hb6_ltw]) ?_
  refine runs_seq_assign_le (v := dsHPtr b vCap eCap)
    (by simp [Expr.eval, BinOp.eval, dsHPtr, hg_ltw, hh_val_ltw]) ?_
  refine runs_seq_assign_le (v := dsMinHBase b vCap eCap)
    (by rw [← hmin_eq]
        simp [Expr.eval, BinOp.eval, dsGPtr, dsHdrSize, h3_lt,
          show 3 * dynGraphSize vCap eCap < 2 ^ w by omega, hmin_sum_ltw]) ?_
  refine runs_seq_assign_le (v := dsDomGenBase b L vCap eCap)
    (by rw [dsDomGenBase_eq]
        simp [Expr.eval, BinOp.eval, h3_lt, h2_lt, h1_lt,
          show 3 * eCap < 2 ^ w by omega, hL1_ltw,
          show 2 * (L + 1) < 2 ^ w by omega, show 3 * eCap + 2 * (L + 1) < 2 ^ w by omega,
          show dsMinHBase b vCap eCap + (3 * eCap + 2 * (L + 1)) < 2 ^ w by
            rw [← dsDomGenBase_eq]; omega]) ?_
  refine runs_seq_assign_le (v := dsEdgeDomGenBase b L vCap eCap)
    (by simp [Expr.eval, BinOp.eval, dsEdgeDomGenBase, h1_lt, hL1_ltw,
      hedg_unfold_ltw]) ?_
  refine runs_seq_assign_le (v := dsPiPtrBase b L vCap eCap)
    (by simp [Expr.eval, BinOp.eval, dsPiPtrBase, h1_lt, hL1_ltw, hLe_ltw, hpi_unfold_ltw]) ?_
  refine runs_seq_assign_le (v := gen0 + 1)
    (by have hgen5_lt : mem (b + 5) + 1 < 2 ^ w := by
          simpa [gen0, dsGenOff] using (by omega : gen0 + 1 < 2 ^ w)
        simp [Expr.eval, BinOp.eval, startState, gen0, dsGenOff, h5_lt, h1_lt, hgen5_lt,
          show b + 5 < 2 ^ w by omega]) ?_
  refine runs_seq_store_le (x := b + dsGenOff) (v := gen0 + 1)
    (by simp [Expr.eval, BinOp.eval, startState, dsGenOff, h5_lt, show b + 5 < 2 ^ w by omega])
    (by simp [Expr.eval]) ?_
  refine runs_seq_store_le (x := domAddr) (v := gen0 + 1)
    (by simp [Expr.eval, BinOp.eval, startState, domAddr, hdom_i_lt])
    (by simp [Expr.eval]) ?_
  let footOf (heapCur : ℕ) (a : ℕ) : Prop := foot0 a ∨ (heapPtr ≤ a ∧ a < heapCur)
  let stepCost := fun k : ℕ => match eL[k]? with | some e => 380 * (emb e).length + 540 | none => 0
  let Inv := dsSetLevelWalksInv L vCap eCap b lvl eListPtr mEmbPtr heapPtr gen0 G H eL emb foot0 mem
  let P0 : State → Prop := fun st => Inv 0 { st with regs := Function.update st.regs 6 0 }
  have hLoop : Triple w p P0
      (WordRAM.forRange 6 (.const 0) (.reg 3)
        (.assign 9 (.load (.bin .add (.reg 2) (.reg 6))) ;;
         .assign 14 (.bin .add (.bin .mul (.reg 1) (.reg 7)) (.reg 9)) ;;
         .store (.bin .add (.reg 12) (.reg 14)) (.reg 8) ;;
         .assign 15 (.load (.bin .add (.reg 4) (.reg 9))) ;;
         .store (.bin .add (.reg 13) (.reg 14)) (.reg 15) ;;
         .call 14 (bOps + dgIdxGetTail) [.reg 10, .reg 9] ;;
         .call 5 (bRev + revIdxInsertWalk) [.reg 0, .reg 1, .reg 9, .reg 14, .reg 15, .reg 11, .reg 5]))
      (normalPost (Inv eL.length))
      (fun _ => rangeCost stepCost 0 eL.length + (eL.length - 0) * ((.reg 3 : Expr).size + 8) +
        ((.const 0 : Expr).size + (.reg 3 : Expr).size + 5)) := by
    refine Triple.forRange_le (P := P0) (Inv := Inv) stepCost 0 eL.length (Nat.zero_le _) h1_lt
      (fun _ => hlen_ltw)
      (fun st hP0 => ⟨by eval_expr, hP0⟩)
      (fun k st _ _ hInv => by
        rcases hInv with ⟨_, _, _, _, _, _, _, _, _, _, hr6, _⟩
        exact hr6)
      (fun k st _ _ hInv => by
        rcases hInv with ⟨_, _, _, _, _, _, _, hr3, _⟩
        simp [Expr.eval, hr3])
      (fun k _ hk st ω hInv => by
        simpa [stepCost, hk] using
          dsSetLevelWalks_step_triple hpRev hpOps hw16 hlvlL hfix_le hheap_lt heList_lt hmEmb_lt
            hL hvC heC hgen_lt hfoot0 hfr_eList hfr_mEmb heL_nd heL_at hG hG_val heG_cov hH hH_val
            hGV_HV hvH heH heL_spec hb_ltw hlvl_ltw h1_lt h0_lt hg_ltw hh_ltw hdg_lt hmin_lt hdom_lt
            hedg_lt hpi_lt hrevG_lt hrevH_lt hdom_i_lt hk (ω := ω) hInv)
  refine runs_seq_triple_le hLoop ?_ ?_
  · exact dsSetLevelWalks_initInv hlvlL hdom_ge hvst0 hedg0 hrevg0 hne_gen_dom rfl
      (by simp [startState]) (by simp [startState]) (by simp [startState]) (by simp [startState])
      (by simp [startState]) (by simp [startState]) (by simp) (by simp) (by simp [gen0]) (by simp)
      (by simp) (by simp) (by simp)
  · intro stF ⟨heapF, revF, hhp1, hhp2, _, _, _, _, _, hr5, _, _, _, _, _, _, _,
      hgen_st, hdom_st, hvst_st, hedg_le, hedg_st, hpi_st, hrev_st, hfr⟩
    rw [List.take_length] at hhp2 hedg_st hpi_st hrev_st
    refine runs_ret_le (by simp [Expr.eval, hr5])
      ⟨eListPtr, mEmbPtr, heapPtr, rfl, hhp1, hhp2, hgen_st, hdom_st, hvst_st, hedg_le,
        ?_, hpi_st, ⟨revF, ?_⟩, hfr⟩ ?_
    · intro e he
      rw [hdom_st, hedg_st e he]
      simp
    · intro v hv
      have := hrev_st v hv
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩
    · have hsum_le : rangeCost stepCost 0 eL.length ≤
          380 * (eL.map fun e => (emb e).length).sum + 540 * eL.length := by
        exact (rangeCost_setWalks eL emb).le
      dsimp only [dsSetLevelWalksContract, dsRevConsContract, argsSize, Expr.size] at hsum_le ⊢
      omega

end MinCostFlow.DynSpanner.Program
