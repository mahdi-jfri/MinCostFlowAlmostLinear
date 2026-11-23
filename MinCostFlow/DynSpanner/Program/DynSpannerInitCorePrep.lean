module

public import MinCostFlow.DynSpanner.Program.DynSpannerInitVerts

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verification of `dsInitCorePrepStmt` (`DynSpannerInitCorePrep`)

Proves `dsInitCorePrep_triple`: loads fixed parameters, computes all base pointers of
`DynSpannerStateAt` into registers `r2..r12`, and populates `H.V := G.V` in `O(G.n)` time.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

private lemma cont_step {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt}
    {st : State} {k k' T : ℕ} {P : State → Prop} {Q : Outcome → State → Prop}
    (hrest : ∀ st₁, P st₁ → ∃ o st' c, Runs w p ω s st₁ o st' c ∧ Q o st' ∧ k' + c ≤ T)
    (hP : P st) (hk : k ≤ k') :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases hrest st hP with ⟨o, st', c, hr, hq, hc⟩
  exact ⟨o, st', c, hr, hq, Nat.le_trans (Nat.add_le_add_right hk c) hc⟩

private lemma dsInitCorePrep_p1_cont {w L vCap eCap b heapPtr : ℕ} {mem : ℕ → ℕ}
    {p : Program} (hw16 : 16 ≤ 2 ^ w)
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) (hheap_w : heapPtr < 2 ^ w)
    (hL : mem (b + dsLOff) = L) (hvC : mem (b + dsVCapOff) = vCap) (heC : mem (b + dsECapOff) = eCap)
    {s : Stmt} {st : State} {ω : ℕ → Bool} {k T : ℕ} {Q : Outcome → State → Prop}
    (hst : st.mem = mem ∧ st.regs 0 = b ∧ st.regs 1 = heapPtr)
    (hrest : ∀ st₁ : State,
      (st₁.mem = mem ∧
        st₁.regs 0 = b ∧ st₁.regs 1 = heapPtr ∧ st₁.regs 2 = vCap ∧ st₁.regs 3 = eCap ∧
        st₁.regs 4 = L ∧ st₁.regs 5 = dynGraphSize vCap eCap ∧ st₁.regs 6 = dsGPtr b ∧
        st₁.regs 7 = dsHPtr b vCap eCap ∧ st₁.regs 8 = dsAuxPtr b vCap eCap) →
      ∃ o st' c, Runs w p ω s st₁ o st' c ∧ Q o st' ∧ (k + 44) + c ≤ T) :
    ∃ o st' c, Runs w p ω
      (.assign 2 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
       .assign 3 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
       .assign 4 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
       .assign 5 (.bin .add (.const 4)
         (.bin .add (.bin .mul (.const 7) (.reg 2)) (.bin .mul (.const 9) (.reg 3)))) ;;
       .assign 6 (.bin .add (.reg 0) (.const dsHdrSize)) ;;
       .assign 7 (.bin .add (.reg 6) (.reg 5)) ;;
       .assign 8 (.bin .add (.reg 7) (.reg 5)) ;; s) st o st' c ∧
      Q o st' ∧ k + c ≤ T := by
  rcases hst with ⟨hmem, hr0, hr1⟩
  subst hmem
  have had := dsAddrs_bound (w := w) (L := L) (vCap := vCap) (eCap := eCap) hfix (by omega)
  rcases had with ⟨_, hdg_lt, _, hmin_lt, _, _, _, _, _, _, hh_aux, ha_min⟩
  have hdg_expr : 4 + (7 * vCap + 9 * eCap) = dynGraphSize vCap eCap := by
    simp only [dynGraphSize]; omega
  have h_g_h : dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap := rfl
  have h_h_a : dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap := rfl
  have h4_w : (4 : ℕ) < 2 ^ w := by omega
  have h7_w : (7 : ℕ) < 2 ^ w := by omega
  have h9_w : (9 : ℕ) < 2 ^ w := by omega
  have hdsV_w : dsVCapOff < 2 ^ w := by simp only [dsVCapOff]; omega
  have hdsE_w : dsECapOff < 2 ^ w := by simp only [dsECapOff]; omega
  have hdsL_w : dsLOff < 2 ^ w := by simp only [dsLOff]; omega
  have hdsH_w : dsHdrSize < 2 ^ w := by simp only [dsHdrSize]; omega
  have hbv_lt : b + dsVCapOff < 2 ^ w := by simp only [dsVCapOff]; omega
  have hbe_lt : b + dsECapOff < 2 ^ w := by simp only [dsECapOff]; omega
  have hbl_lt : b + dsLOff < 2 ^ w := by simp only [dsLOff]; omega
  have hg_ltw : b + dsHdrSize < 2 ^ w := by simp only [dsHdrSize] at *; omega
  have hh_ltw : dsHPtr b vCap eCap < 2 ^ w := by omega
  have ha_ltw : dsAuxPtr b vCap eCap < 2 ^ w := by omega
  refine runs_seq_assign_le (v := vCap)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr0, hdsV_w, hbv_lt]) hvC) ?_
  refine runs_seq_assign_le (v := eCap)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr0, hdsE_w, hbe_lt]) heC) ?_
  refine runs_seq_assign_le (v := L)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr0, hdsL_w, hbl_lt]) hL) ?_
  refine runs_seq_assign_le (v := dynGraphSize vCap eCap)
    (by simp [Expr.eval, BinOp.eval, h4_w, h7_w, h9_w, hdg_expr, hdg_lt,
      show 7 * vCap < 2 ^ w by omega, show 9 * eCap < 2 ^ w by omega,
      show 7 * vCap + 9 * eCap < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := dsGPtr b)
    (by simp [Expr.eval, BinOp.eval, hr0, dsGPtr, hdsH_w, hg_ltw]) ?_
  refine runs_seq_assign_le (v := dsHPtr b vCap eCap)
    (by simp [Expr.eval, BinOp.eval, h_g_h, hh_ltw]) ?_
  refine runs_seq_assign_le (v := dsAuxPtr b vCap eCap)
    (by simp [Expr.eval, BinOp.eval, h_h_a, ha_ltw]) ?_
  refine cont_step hrest ⟨rfl, by simp [hr0], by simp [hr1], by simp, by simp, by simp, by simp,
    by simp, by simp, by simp⟩ (by dsimp only [Expr.size]; omega)

private lemma dsInitCorePrep_p2_bounds {w L vCap eCap b heapPtr : ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) (hheap_w : heapPtr < 2 ^ w) :
    dsMEmbTempBase b L vCap eCap < 2 ^ w ∧
    3 * dynGraphSize vCap eCap < 2 ^ w ∧
    b + dsHdrSize + 3 * dynGraphSize vCap eCap < 2 ^ w ∧
    3 * eCap < 2 ^ w ∧
    L + 1 < 2 ^ w ∧
    2 * (L + 1) < 2 ^ w ∧
    3 * eCap + 2 * (L + 1) < 2 ^ w ∧
    dsMinHBase b vCap eCap + (3 * eCap + 2 * (L + 1)) < 2 ^ w ∧
    (L + 1) * eCap < 2 ^ w ∧
    2 * ((L + 1) * eCap) < 2 ^ w ∧
    L + 1 + 2 * ((L + 1) * eCap) < 2 ^ w ∧
    dsDomGenBase b L vCap eCap + (L + 1 + 2 * ((L + 1) * eCap)) < 2 ^ w ∧
    (L + 1) * vCap < 2 ^ w ∧
    3 * ((L + 1) * vCap) < 2 ^ w ∧
    2 * (L + 1) + vCap < 2 ^ w ∧
    3 * ((L + 1) * vCap) + (2 * (L + 1) + vCap) < 2 ^ w ∧
    dsRevGenBase b L vCap eCap + (3 * ((L + 1) * vCap) + (2 * (L + 1) + vCap)) < 2 ^ w ∧
    2 * eCap < 2 ^ w ∧
    vCap + 2 * eCap < 2 ^ w ∧
    dsRevGenBase b L vCap eCap + (3 * ((L + 1) * vCap) + (2 * (L + 1) + vCap)) + (vCap + 2 * eCap) < 2 ^ w ∧
    dsGPtr b + dgNOff < 2 ^ w ∧
    dsGPtr b + dgMOff < 2 ^ w ∧
    dsGPtr b + 4 < 2 ^ w ∧
    dsGPtr b + 4 + vCap < 2 ^ w := by
  have hf := dsFixedSize_add b L vCap eCap
  have hm_lt : dsMEmbTempBase b L vCap eCap < 2 ^ w := by
    have := hf; exact Nat.lt_of_le_of_lt (by omega) (lt_of_le_of_lt hfix hheap_w)
  have hm := dsMEmbTempBase_eq b L vCap eCap
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have hdg : 4 + 7 * vCap + 9 * eCap = dynGraphSize vCap eCap := rfl
  have hgp : dsGPtr b = b + dsHdrSize := rfl
  have hgN : dsGPtr b + dgNOff ≤ dsMinHBase b vCap eCap := by
    simp only [dsGPtr, dgNOff, dynGraphSize] at *; omega
  have hgM : dsGPtr b + dgMOff ≤ dsMinHBase b vCap eCap := by
    simp only [dsGPtr, dgMOff, dynGraphSize] at *; omega
  have hg4 : dsGPtr b + 4 + vCap ≤ dsMinHBase b vCap eCap := by
    simp only [dsGPtr, dynGraphSize] at *; omega
  refine ⟨hm_lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | (rw [← hm]; exact hm_lt)
    | (linarith only [hm_lt, hm, h1, h2, h3,
        Nat.zero_le b, Nat.zero_le dsHdrSize, Nat.zero_le (dynGraphSize vCap eCap),
        Nat.zero_le vCap, Nat.zero_le eCap, Nat.zero_le L,
        Nat.zero_le ((L + 1) * eCap), Nat.zero_le ((L + 1) * vCap),
        Nat.zero_le (dsMinHBase b vCap eCap), Nat.zero_le (dsDomGenBase b L vCap eCap),
        Nat.zero_le (dsRevGenBase b L vCap eCap),
        hgN, hgM, hg4, hdg, hgp])

private lemma dsInitCorePrep_p2_cont {w L vCap eCap b heapPtr : ℕ} {G : MGraph} {mem : ℕ → ℕ}
    {p : Program} (hw16 : 16 ≤ 2 ^ w)
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) (hheap_w : heapPtr < 2 ^ w)
    (hG : DynGraphAt mem (dsGPtr b) vCap eCap G)
    {s : Stmt} {st : State} {ω : ℕ → Bool} {k T : ℕ} {Q : Outcome → State → Prop}
    (hst : st.mem = mem ∧
      st.regs 0 = b ∧ st.regs 1 = heapPtr ∧ st.regs 2 = vCap ∧ st.regs 3 = eCap ∧
      st.regs 4 = L ∧ st.regs 5 = dynGraphSize vCap eCap ∧ st.regs 6 = dsGPtr b ∧
      st.regs 7 = dsHPtr b vCap eCap ∧ st.regs 8 = dsAuxPtr b vCap eCap)
    (hrest : ∀ st₂ : State,
      (st₂.mem = mem ∧
        st₂.regs 0 = b ∧ st₂.regs 1 = heapPtr ∧ st₂.regs 2 = vCap ∧ st₂.regs 3 = eCap ∧
        st₂.regs 4 = L ∧ st₂.regs 5 = dynGraphSize vCap eCap ∧ st₂.regs 6 = dsGPtr b ∧
        st₂.regs 7 = dsHPtr b vCap eCap ∧ st₂.regs 8 = dsAuxPtr b vCap eCap ∧
        st₂.regs 9 = dsMEmbTempBase b L vCap eCap ∧ st₂.regs 10 = G.n ∧ st₂.regs 11 = G.m ∧
        st₂.regs 12 = dgVListBase (dsGPtr b) vCap) →
      ∃ o st' c, Runs w p ω s st₂ o st' c ∧ Q o st' ∧ (k + 82) + c ≤ T) :
    ∃ o st' c, Runs w p ω
      (.assign 9 (.bin .add (.reg 6) (.bin .mul (.const 3) (.reg 5))) ;;
       .assign 9 (.bin .add (.reg 9)
         (.bin .add (.bin .mul (.const 3) (.reg 3))
           (.bin .mul (.const 2) (.bin .add (.reg 4) (.const 1))))) ;;
       .assign 9 (.bin .add (.reg 9)
         (.bin .add (.bin .add (.reg 4) (.const 1))
           (.bin .mul (.const 2) (.bin .mul (.bin .add (.reg 4) (.const 1)) (.reg 3))))) ;;
       .assign 9 (.bin .add (.reg 9)
         (.bin .add (.bin .mul (.const 3) (.bin .mul (.bin .add (.reg 4) (.const 1)) (.reg 2)))
           (.bin .add (.bin .mul (.const 2) (.bin .add (.reg 4) (.const 1))) (.reg 2)))) ;;
       .assign 9 (.bin .add (.reg 9) (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 3)))) ;;
       .assign 10 (.load (.bin .add (.reg 0) (.const (dsHdrSize + dgNOff)))) ;;
       .assign 11 (.load (.bin .add (.reg 0) (.const (dsHdrSize + dgMOff)))) ;;
       .assign 12 (.bin .add (.bin .add (.reg 6) (.const 4)) (.reg 2)) ;; s) st o st' c ∧
      Q o st' ∧ k + c ≤ T := by
  rcases hst with ⟨hmem, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8⟩
  subst hmem
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have hm := dsMEmbTempBase_eq b L vCap eCap
  obtain ⟨_, hb_3dg, hb_min, hb_3e, hb_L1, hb_2L1, hb_3e2L, hb_dom, hb_Le, hb_2Le, hb_L2Le,
    hb_revG, hb_Lv, hb_3Lv, hb_2Lv, hb_3Lv2, hb_revV, hb_2e, hb_v2e, hb_memB, hgN_lt, hgM_lt,
    hg4_lt, hvl_lt⟩ := dsInitCorePrep_p2_bounds hfix hheap_w
  have hG_n : st.mem (dsGPtr b + dgNOff) = G.n := hG.2.2.2.2.2.1
  have hG_m : st.mem (dsGPtr b + dgMOff) = G.m := hG.2.2.2.2.2.2.1
  have h1_w : (1 : ℕ) < 2 ^ w := by omega
  have h2_w : (2 : ℕ) < 2 ^ w := by omega
  have h3_w : (3 : ℕ) < 2 ^ w := by omega
  have h4_w : (4 : ℕ) < 2 ^ w := by omega
  have hHN_w : dsHdrSize + dgNOff < 2 ^ w := by simp only [dsHdrSize, dgNOff]; omega
  have hHM_w : dsHdrSize + dgMOff < 2 ^ w := by simp only [dsHdrSize, dgMOff]; omega
  have hbN_eq : b + (dsHdrSize + dgNOff) = dsGPtr b + dgNOff := by simp [dsGPtr]; omega
  have hbM_eq : b + (dsHdrSize + dgMOff) = dsGPtr b + dgMOff := by simp [dsGPtr]; omega
  refine runs_seq_assign_le (v := dsMinHBase b vCap eCap)
    (by rw [h1]
        simp [Expr.eval, BinOp.eval, hr5, hr6, dsGPtr, h3_w, hb_3dg, hb_min]) ?_
  refine runs_seq_assign_le (v := dsDomGenBase b L vCap eCap)
    (by rw [h2]
        simp [Expr.eval, BinOp.eval, hr3, hr4, h1_w, h2_w, h3_w, hb_3e, hb_L1, hb_2L1,
          hb_3e2L, hb_dom]) ?_
  refine runs_seq_assign_le (v := dsRevGenBase b L vCap eCap)
    (by rw [h3]
        simp [Expr.eval, BinOp.eval, hr3, hr4, h1_w, h2_w, hb_L1, hb_Le, hb_2Le,
          hb_L2Le, hb_revG]) ?_
  refine runs_seq_assign_le (v := dsRevGenBase b L vCap eCap + (3 * ((L + 1) * vCap) + (2 * (L + 1) + vCap)))
    (by simp [Expr.eval, BinOp.eval, hr2, hr4, h1_w, h2_w, h3_w, hb_L1, hb_Lv, hb_3Lv,
      hb_2L1, hb_2Lv, hb_3Lv2, hb_revV]) ?_
  refine runs_seq_assign_le (v := dsMEmbTempBase b L vCap eCap)
    (by rw [hm]
        simp [Expr.eval, BinOp.eval, hr2, hr3, h2_w, hb_2e, hb_v2e, hb_memB]) ?_
  refine runs_seq_assign_le (v := G.n)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr0, hHN_w, hbN_eq, hgN_lt]) hG_n) ?_
  refine runs_seq_assign_le (v := G.m)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr0, hHM_w, hbM_eq, hgM_lt]) hG_m) ?_
  refine runs_seq_assign_le (v := dgVListBase (dsGPtr b) vCap)
    (by simp [Expr.eval, BinOp.eval, hr2, hr6, dgVListBase, h4_w, hg4_lt, hvl_lt]) ?_
  refine cont_step hrest ⟨rfl, by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3],
    by simp [hr4], by simp [hr5], by simp [hr6], by simp [hr7], by simp [hr8],
    by simp, by simp, by simp, by simp⟩ (by dsimp only [Expr.size]; omega)

lemma dsInitCorePrep_triple {w L vCap eCap b heapPtr : ℕ} {G : MGraph} {mem : ℕ → ℕ}
    {p : Program} {bOps : ℕ} (hpOps : p.HasAt bOps dgOpsProcs)
    (hw16 : 16 ≤ 2 ^ w) (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) (hheap_w : heapPtr < 2 ^ w)
    (hL : mem (b + dsLOff) = L) (hvC : mem (b + dsVCapOff) = vCap) (heC : mem (b + dsECapOff) = eCap)
    (hG : DynGraphAt mem (dsGPtr b) vCap eCap G)
    (hH0 : DynGraphAt mem (dsHPtr b vCap eCap) vCap eCap emptyMGraph)
    {st : State} {ω : ℕ → Bool}
    (hst : st.mem = mem ∧ st.regs 0 = b ∧ st.regs 1 = heapPtr) :
    ∃ o st' c, Runs w p ω (dsInitCorePrepStmt bOps) st o st' c ∧
      normalPost (fun st₁ =>
        st₁.regs 0 = b ∧ st₁.regs 1 = heapPtr ∧ st₁.regs 2 = vCap ∧ st₁.regs 3 = eCap ∧
        st₁.regs 4 = L ∧ st₁.regs 5 = dynGraphSize vCap eCap ∧ st₁.regs 6 = dsGPtr b ∧
        st₁.regs 7 = dsHPtr b vCap eCap ∧ st₁.regs 8 = dsAuxPtr b vCap eCap ∧
        st₁.regs 9 = dsMEmbTempBase b L vCap eCap ∧ st₁.regs 10 = G.n ∧ st₁.regs 11 = G.m ∧
        st₁.regs 12 = dgVListBase (dsGPtr b) vCap ∧
        DynGraphAt st₁.mem (dsHPtr b vCap eCap) vCap eCap
          { V := G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 } ∧
        ∀ addr, addr < dsHPtr b vCap eCap ∨
            dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr →
          st₁.mem addr = mem addr) o st' ∧
      c ≤ 129 * G.n + 140 := by
  have had := dsAddrs_bound (w := w) (L := L) (vCap := vCap) (eCap := eCap) hfix (by omega)
  rcases had with ⟨_, _, _, _, _, _, _, _, _, _, hh_aux, _⟩
  have h_h_a : dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap := rfl
  have h_a_ltw : dsAuxPtr b vCap eCap < 2 ^ w := by omega
  have h_h_lt : dsHPtr b vCap eCap + dynGraphSize vCap eCap < 2 ^ w := by omega
  obtain ⟨vL, hvL_len, _, hvL_mem, hvL_at, _⟩ := hG.2.2.2.2.2.2.2.2.1
  have hG_v := hG.2.1
  have hGn_le : G.n ≤ vCap :=
    (Finset.card_le_card (show G.V ⊆ Finset.range vCap from
      fun v hv => Finset.mem_range.mpr (hG_v v hv))).trans_eq (Finset.card_range vCap)
  have hGn_w : G.n < 2 ^ w := by omega
  have hvL_disj : dgVListBase (dsGPtr b) vCap + G.n ≤ dsHPtr b vCap eCap := by
    have h_g_h : dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap := rfl
    have hdg : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
    simp only [dgVListBase]; omega
  refine runs_start_le ?_
  dsimp only [dsInitCorePrepStmt]
  refine dsInitCorePrep_p1_cont hw16 hfix hheap_w hL hvC heC hst ?_
  intro st₁ h1
  refine dsInitCorePrep_p2_cont hw16 hfix hheap_w hG h1 ?_
  intro st₂ ⟨hm2, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12⟩
  refine runs_triple_le (dsAddVerts_triple hpOps hw16 h_h_lt hG_v hGn_w hvL_len hvL_mem
    mem st₂.regs (hm2 ▸ hH0) (hm2 ▸ hvL_at) hvL_disj) ?_ ?_ ?_
  · exact ⟨hm2, fun _ _ _ => rfl, hr6, hr7, hr10, hr12⟩
  · intro o st' hq
    cases o with
    | returned _ => exact hq
    | normal =>
      rcases hq with ⟨hH_out, hregs, hr6', hr7', hr10', hr12', hfr'⟩
      exact ⟨hregs 0 (by decide) (by decide) ▸ hr0,
        hregs 1 (by decide) (by decide) ▸ hr1,
        hregs 2 (by decide) (by decide) ▸ hr2,
        hregs 3 (by decide) (by decide) ▸ hr3,
        hregs 4 (by decide) (by decide) ▸ hr4,
        hregs 5 (by decide) (by decide) ▸ hr5,
        hr6', hr7',
        hregs 8 (by decide) (by decide) ▸ hr8,
        hregs 9 (by decide) (by decide) ▸ hr9,
        hr10',
        hregs 11 (by decide) (by decide) ▸ hr11,
        hr12', hH_out, hfr'⟩
  · dsimp only [Expr.size]; omega

end

end MinCostFlow.DynSpanner.Program
