module

public import MinCostFlow.LinkCut.Prog.MathForestPtrSafeBase

/-!
# Auxiliary Splay Procedure Memory and Pointer Safety

Proves `SafeMem` preservation across `revNodeBody`, `applyTagBody`, `pushDownBody`, and `pullBody`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section PtrSafeHelpers

theorem SafeMem.ptrAllowed_field {mem0 mem : ℕ → ℕ} {nb cap hp0 u off : ℕ}
    (hs : SafeMem mem0 nb cap hp0 mem) (hz0 : SlotZeroOk mem0 nb)
    (hu : u ≤ cap) (hoff : off ∈ ptrOffs) :
    PtrAllowed mem0 nb cap hp0 (nodeField mem nb u off) := by
  by_cases hu0 : u = 0
  · subst hu0
    have hlt := ptrOffs_lt_stride hoff
    have ha : nb ≤ nb + NODE_STRIDE * 0 + off ∧
        nb + NODE_STRIDE * 0 + off < nb + NODE_STRIDE := by omega
    have heq : nodeField mem nb 0 off = 0 := by
      change mem (nb + NODE_STRIDE * 0 + off) = 0
      rw [hs.2.1 _ (Or.inr (Or.inl ha))]
      simpa using hz0 off hlt
    rw [heq]; exact Or.inl rfl
  · exact hs.2.2.2 u off (Nat.pos_of_ne_zero hu0) hu hoff

theorem SafeMem.update_nonStruct {mem0 mem : ℕ → ℕ} {nb cap hp0 x off v : ℕ}
    (hs : SafeMem mem0 nb cap hp0 mem) (hnb : 3 ≤ nb) (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    (hx1 : 1 ≤ x) (hx2 : x ≤ cap) (hoff : off < NODE_STRIDE)
    (hnstr : off ≠ OFF_LEFT ∧ off ≠ OFF_RIGHT ∧ off ≠ OFF_PARENT)
    (hptr : off ∈ ptrOffs → PtrAllowed mem0 nb cap hp0 v) :
    SafeMem mem0 nb cap hp0 (Function.update mem (nb + NODE_STRIDE * x + off) v) :=
  hs.update_field hnb harena hx1 hx2 hoff
    (fun h => by rcases h with rfl | rfl | rfl <;> simp_all) hptr

theorem stmtNoRet_swapFields {p f1 f2 t1 t2 : ℕ} :
    stmtNoRet (swapFieldsStmt p f1 f2 t1 t2) = true := rfl

theorem stmtNoRet_shiftPtr {sp : SplayProcs} {e : Expr} {a b c d f : ℕ} :
    stmtNoRet (shiftPtrStmt sp e a b c d f) = true := by
  simp [shiftPtrStmt, stmtNoRet]

theorem stmtNoRet_addOptPtr {sp : SplayProcs} {a b c d f : ℕ} :
    stmtNoRet (addOptPtrStmt sp a b c d f) = true := by
  simp [addOptPtrStmt, stmtNoRet]

theorem stmtNoRet_pullMinNum {sp : SplayProcs} {a b c d e f g h i : ℕ} :
    stmtNoRet (pullMinNumStmt sp a b c d e f g h i) = true := by
  simp [pullMinNumStmt, combineNumAggStmt, stmtNoRet]

theorem stmtNoRet_setChildAndParent {a b c d e : ℕ} :
    stmtNoRet (setChildAndParentStmt a b c d e) = true := by
  simp [setChildAndParentStmt, stmtNoRet]

end PtrSafeHelpers

section SplayProcSafety

theorem revNode_safeExec {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem0 : ℕ → ℕ} {nb cap hp0 : ℕ} (hnb : 3 ≤ nb) (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    {fuel : ℕ} {st st' : State} {o : Outcome} {c x : ℕ}
    (hx : x ≤ cap) (h0 : st.regs 0 = nb) (h1 : st.regs 1 = x)
    (hs : SafeMem mem0 nb cap hp0 st.mem)
    (hex : exec w p ω fuel revNodeBody st = some (o, st', c)) :
    o = .returned 0 ∧ SafeMem mem0 nb cap hp0 st'.mem := by
  dsimp only [revNodeBody] at hex
  rcases exec_cond_elim hex with ⟨_, vx, _, _, hex1, hbr, _⟩
  simp only [Expr.eval, h1] at hex1; cases hex1
  by_cases hx0 : x = 0
  · simp only [hx0, ↓reduceIte] at hbr
    rcases exec_ret_iff.1 hbr with ⟨_, v0, _, hv0, rfl, rfl, _⟩
    simp [Expr.eval] at hv0; cases hv0; exact ⟨rfl, hs⟩
  · simp only [hx0, ↓reduceIte] at hbr
    have hx1 : 1 ≤ x := Nat.pos_of_ne_zero hx0
    rcases exec_seq_assign_elim hbr with ⟨_, v2, _, _, hv2, h2, _⟩
    have hv2_eq : v2 = nb + NODE_STRIDE * x := by
      rcases eval_nodePtr_some hv2 with ⟨rfl, _⟩; rw [h0, h1]
    have hsw : ∀ (f1 f2 : ℕ), f1 < NODE_STRIDE → f2 < NODE_STRIDE →
        (f1 = OFF_LEFT ∨ f1 = OFF_RIGHT ∨ f1 = OFF_PARENT ↔
          f2 = OFF_LEFT ∨ f2 = OFF_RIGHT ∨ f2 = OFF_PARENT) ∧ (f1 ∈ ptrOffs ↔ f2 ∈ ptrOffs) →
        ∀ {fu st0 o0 c0 t},
          exec w p ω fu (swapFieldsStmt 2 f1 f2 3 4 ;; t) st0 = some (o0, st', c0) →
          st0.regs 2 = nb + NODE_STRIDE * x → SafeMem mem0 nb cap hp0 st0.mem →
          ∃ f1' st1 c2, exec w p ω f1' t st1 = some (o0, st', c2) ∧
            st1.regs 2 = nb + NODE_STRIDE * x ∧ SafeMem mem0 nb cap hp0 st1.mem := by
      intro f1 f2 hf1 hf2 hsym fu st0 o0 c0 t hex_sw hr2 hs0
      rcases exec_seq_of_noRet stmtNoRet_swapFields hex_sw with ⟨f1', st1, _, c2, _, hs1_ex, ht_ex, _⟩
      rcases swapFields_safeExec hnb harena hf1 hf2 hsym hx1 hx hr2 hs0 hs1_ex
        (by decide) (by decide) (by decide) with ⟨_, hs1, hregs1⟩
      refine ⟨f1', st1, c2, ht_ex, ?_, hs1⟩
      rw [hregs1 2 (by decide) (by decide), hr2]
    rcases hsw OFF_LEFT OFF_RIGHT (by decide) (by decide) (by decide) h2
      (by simp [hv2_eq]) hs with ⟨_, st1, _, h3, hr2_1, hs1⟩
    rcases hsw OFF_MIN1_HAS OFF_MIN2_HAS (by decide) (by decide) (by decide) h3 hr2_1 hs1
      with ⟨_, st2, _, h4, hr2_2, hs2⟩
    rcases hsw OFF_MIN1_VAL OFF_MIN2_VAL (by decide) (by decide) (by decide) h4 hr2_2 hs2
      with ⟨_, st3, _, h5, hr2_3, hs3⟩
    rcases hsw OFF_MIN1_FIRST OFF_MIN2_LAST (by decide) (by decide) (by decide) h5 hr2_3 hs3
      with ⟨_, st4, _, h6, hr2_4, hs4⟩
    rcases hsw OFF_MIN1_LAST OFF_MIN2_FIRST (by decide) (by decide) (by decide) h6 hr2_4 hs4
      with ⟨_, st5, _, h7, hr2_5, hs5⟩
    rcases hsw OFF_CSUM_FWD OFF_CSUM_BWD (by decide) (by decide) (by decide) h7 hr2_5 hs5
      with ⟨_, st6, _, h8, hr2_6, hs6⟩
    rcases exec_seq_assign_elim h8 with ⟨_, v3r, _, _, _, h9, _⟩
    rcases exec_seq_store_elim h9 with ⟨_, a_rev, v_rev, _, _, ha_rev, _, h10, _⟩
    have ha_rev_eq : a_rev = nb + NODE_STRIDE * x + OFF_REV := by
      rcases eval_fieldAddr_some ha_rev with ⟨rfl, _⟩
      dsimp only; rw [Function.update_of_ne (by decide), hr2_6]
    have hs7 : SafeMem mem0 nb cap hp0 (Function.update st6.mem a_rev v_rev) := by
      rw [ha_rev_eq]
      exact hs6.update_nonStruct hnb harena hx1 hx (by decide) (by decide)
        (fun h => False.elim ((by decide : OFF_REV ∉ ptrOffs) h))
    have hr2_7 : Function.update st6.regs 3 v3r 2 = nb + NODE_STRIDE * x := by
      rw [Function.update_of_ne (by decide), hr2_6]
    have hc1_nr : stmtNoRet (Stmt.cond (fieldLoadExpr 2 OFF_HASE)
        (Stmt.assign 3 (fieldLoadExpr 2 OFF_DIR) ;;
         Stmt.store (fieldAddrExpr 2 OFF_DIR) (.bin .sub (.const 1) (.reg 3)) ;;
         swapFieldsStmt 2 OFF_AF_PTR OFF_AB_PTR 3 4 ;;
         swapFieldsStmt 2 OFF_COST_FWD OFF_COST_BWD 3 4) Stmt.nop) = true := by
      simp [stmtNoRet, swapFieldsStmt]
    rcases exec_seq_of_noRet hc1_nr h10 with ⟨_, st8, _, _, _, hc1_ex, h11, _⟩
    have hc1_res : SafeMem mem0 nb cap hp0 st8.mem ∧ st8.regs 2 = nb + NODE_STRIDE * x := by
      rcases exec_cond_elim hc1_ex with ⟨_, vh, _, _, _, hbr1, _⟩
      by_cases hh0 : vh = 0
      · simp only [hh0, ↓reduceIte] at hbr1
        rcases exec_nop_iff.1 hbr1 with ⟨_, _, rfl, _⟩; exact ⟨hs7, hr2_7⟩
      · simp only [hh0, ↓reduceIte] at hbr1
        rcases exec_seq_assign_elim hbr1 with ⟨_, v3d, _, _, _, ha_e, _⟩
        rcases exec_seq_store_elim ha_e with ⟨_, adir, vdir, _, _, had, _, hsw1, _⟩
        have had_eq : adir = nb + NODE_STRIDE * x + OFF_DIR := by
          rcases eval_fieldAddr_some had with ⟨rfl, _⟩
          dsimp only; rw [Function.update_of_ne (by decide), hr2_7]
        have hs7d : SafeMem mem0 nb cap hp0
            (Function.update (Function.update st6.mem a_rev v_rev) adir vdir) := by
          rw [had_eq]
          exact hs7.update_nonStruct hnb harena hx1 hx (by decide) (by decide)
            (fun h => False.elim ((by decide : OFF_DIR ∉ ptrOffs) h))
        have hr2_7d : Function.update (Function.update st6.regs 3 v3r) 3 v3d 2 = nb + NODE_STRIDE * x := by
          rw [Function.update_of_ne (by decide)]; exact hr2_7
        rcases exec_seq_of_noRet stmtNoRet_swapFields hsw1 with ⟨_, st_a, _, _, _, hsw1_ex, hsw2_ex, _⟩
        rcases swapFields_safeExec hnb harena (by decide) (by decide) (by decide) hx1 hx
          (by simpa using hr2_7d) hs7d hsw1_ex (by decide) (by decide) (by decide) with
          ⟨_, hs_a, hr_a⟩
        have hr2_a : st_a.regs 2 = nb + NODE_STRIDE * x := by
          rw [hr_a 2 (by decide) (by decide)]; exact hr2_7d
        rcases swapFields_safeExec hnb harena (by decide) (by decide) (by decide) hx1 hx hr2_a
          hs_a hsw2_ex (by decide) (by decide) (by decide) with ⟨_, hs_b, hr_b⟩
        exact ⟨hs_b, by rw [hr_b 2 (by decide) (by decide), hr2_a]⟩
    rcases hc1_res with ⟨hs8, hr2_8⟩
    have hc2_nr : stmtNoRet (Stmt.cond (fieldLoadExpr 2 OFF_HAS_TAG)
        (Stmt.assign 3 (fieldLoadExpr 2 OFF_TAG_NEG) ;;
         Stmt.store (fieldAddrExpr 2 OFF_TAG_NEG) (.bin .sub (.const 1) (.reg 3))) Stmt.nop) = true := by
      simp [stmtNoRet]
    rcases exec_seq_of_noRet hc2_nr h11 with ⟨_, st9, _, _, _, hc2_ex, h12, _⟩
    have hs9 : SafeMem mem0 nb cap hp0 st9.mem := by
      rcases exec_cond_elim hc2_ex with ⟨_, vt, _, _, _, hbr2, _⟩
      by_cases ht0 : vt = 0
      · simp only [ht0, ↓reduceIte] at hbr2
        rcases exec_nop_iff.1 hbr2 with ⟨_, _, rfl, _⟩; exact hs8
      · simp only [ht0, ↓reduceIte] at hbr2
        rcases exec_seq_assign_elim hbr2 with ⟨_, _, _, _, _, ha_t, _⟩
        rcases exec_store_iff.1 ha_t with ⟨_, atn, vtn, _, hatn, _, _, rfl, rfl, _⟩
        have hatn_eq : atn = nb + NODE_STRIDE * x + OFF_TAG_NEG := by
          rcases eval_fieldAddr_some hatn with ⟨rfl, _⟩
          dsimp only; rw [Function.update_of_ne (by decide), hr2_8]
        dsimp only; rw [hatn_eq]
        exact hs8.update_nonStruct hnb harena hx1 hx (by decide) (by decide)
          (fun h => False.elim ((by decide : OFF_TAG_NEG ∉ ptrOffs) h))
    rcases exec_ret_iff.1 h12 with ⟨_, vret, _, hvret, rfl, rfl, _⟩
    simp [Expr.eval] at hvret; cases hvret; exact ⟨rfl, hs9⟩

theorem applyTag_safeExec {w h spBase : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp_prog : p.HasAt spBase (splayBodies (SplayProcs.atBase spBase) h))
    {mem0 : ℕ → ℕ} {nb cap hp0 : ℕ} (hnb : 3 ≤ nb) (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    {fuel : ℕ} {st st' : State} {o : Outcome} {c x : ℕ}
    (hx : x ≤ cap) (h0 : st.regs 0 = nb) (h1 : st.regs 1 = x)
    (htptr : PtrAllowed mem0 nb cap hp0 (st.regs 2))
    (hs : SafeMem mem0 nb cap hp0 st.mem)
    (hex : exec w p ω fuel (applyTagBody (SplayProcs.atBase spBase)) st = some (o, st', c)) :
    o = .returned 0 ∧ SafeMem mem0 nb cap hp0 st'.mem := by
  dsimp only [applyTagBody] at hex
  rcases exec_cond_elim hex with ⟨_, vx, _, _, hvx, hbr1, _⟩
  simp only [Expr.eval, h1] at hvx; cases hvx
  by_cases hx0 : x = 0
  · simp only [hx0, ↓reduceIte] at hbr1
    rcases exec_ret_iff.1 hbr1 with ⟨_, v0, _, hv0, rfl, rfl, _⟩
    simp [Expr.eval] at hv0; cases hv0; exact ⟨rfl, hs⟩
  · simp only [hx0, ↓reduceIte] at hbr1
    have hx1 : 1 ≤ x := Nat.pos_of_ne_zero hx0
    rcases exec_seq_assign_elim hbr1 with ⟨_, v4, _, _, hv4, h2, _⟩
    rcases exec_seq_assign_elim h2 with ⟨_, v5, _, _, _, h3, _⟩
    rcases exec_cond_elim h3 with ⟨_, vc5, _, _, he5, hbr2, _⟩
    simp only [Expr.eval, Function.update_self] at he5; cases he5
    by_cases hv5_0 : v5 = 0
    · simp only [hv5_0, ↓reduceIte] at hbr2
      rcases exec_ret_iff.1 hbr2 with ⟨_, v0, _, hv0, rfl, rfl, _⟩
      simp [Expr.eval] at hv0; cases hv0; exact ⟨rfl, hs⟩
    · simp only [hv5_0, ↓reduceIte] at hbr2
      have hv4_eq : v4 = nb + NODE_STRIDE * x := by
        rcases eval_nodePtr_some hv4 with ⟨rfl, _⟩; rw [h0, h1]
      rcases exec_seq_assign_elim hbr2 with ⟨_, vL, _, _, _, h4, _⟩
      rcases exec_seq_assign_elim h4 with ⟨_, vhp, _, _, hvhp, h5, _⟩
      have hvhp_eq : hp0 ≤ vhp := by
        simp only [Expr.eval, Option.map_eq_some_iff] at hvhp
        rcases hvhp with ⟨a, ha, rfl⟩
        rcases eval_sub_reg_const ha with rfl
        rw [h0]
        exact hs.1
      have h_sh : ∀ {e : Expr} (off : ℕ),
          off < NODE_STRIDE → off ∈ ptrOffs →
          (off = OFF_AF_PTR ∨ off = OFF_AB_PTR ∨ off = OFF_FLOW_PTR ∨
            off = OFF_MIN1_VAL ∨ off = OFF_MIN2_VAL ∨ off = OFF_TAG_PTR) →
          ∀ {fu st0 o0 st_end c0 t},
          exec w p ω fu (Stmt.assign 8 (fieldLoadExpr 4 off) ;;
            shiftPtrStmt (SplayProcs.atBase spBase) e 8 2 6 7 9 ;;
            Stmt.store (fieldAddrExpr 4 off) (.reg 9) ;; t) st0 = some (o0, st_end, c0) →
          st0.regs 4 = nb + NODE_STRIDE * x → hp0 ≤ st0.regs 7 →
          SafeMem mem0 nb cap hp0 st0.mem →
          ∃ f1' st1 c2, exec w p ω f1' t st1 = some (o0, st_end, c2) ∧
            st1.regs 4 = nb + NODE_STRIDE * x ∧ hp0 ≤ st1.regs 7 ∧
            SafeMem mem0 nb cap hp0 st1.mem ∧
            (∀ r, r ≠ 7 → r ≠ 8 → r ≠ 9 → st1.regs r = st0.regs r) := by
        intro e off hoff_lt hoff_ptr hoff_ns fu st0 o0 st_end c0 t hex_s hr4 hhp0 hs0
        rcases exec_seq_assign_elim hex_s with ⟨_, v8, _, _, _, hsh, _⟩
        rcases exec_seq_of_noRet stmtNoRet_shiftPtr hsh with ⟨_, st_sh, _, _, _, hsh_ex, hst_ex, _⟩
        rcases shiftPtr_safeExec hp_prog harena (LReg := 6) (hpReg := 7) (outPtrReg := 9)
          (st := { st0 with regs := Function.update st0.regs 8 v8 })
          (by decide) (by decide) (by simpa using hs0)
          (by dsimp only; rw [Function.update_of_ne (by decide)]; exact hhp0) hsh_ex with
          ⟨_, hs_sh, hhp_sh, hp9, hregs_sh⟩
        rcases exec_seq_store_elim hst_ex with ⟨_, a_f, val_f, _, _, ha_f, hval_f, ht_ex, _⟩
        have hr4_sh : st_sh.regs 4 = nb + NODE_STRIDE * x := by
          rw [hregs_sh 4 (by decide) (by decide)]; simp [Function.update_of_ne, hr4]
        have ha_f_eq : a_f = nb + NODE_STRIDE * x + off := by
          rcases eval_fieldAddr_some ha_f with ⟨rfl, _⟩; rw [hr4_sh]
        have hval_f_eq : val_f = st_sh.regs 9 := by
          simp [Expr.eval] at hval_f; exact hval_f.symm
        have hp9_al : PtrAllowed mem0 nb cap hp0 val_f := by
          rw [hval_f_eq]; exact Or.inr (Or.inl hp9)
        have hnstr : off ≠ OFF_LEFT ∧ off ≠ OFF_RIGHT ∧ off ≠ OFF_PARENT := by
          rcases hoff_ns with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        have hs1 : SafeMem mem0 nb cap hp0 (Function.update st_sh.mem a_f val_f) := by
          rw [ha_f_eq]
          exact hs_sh.update_nonStruct hnb harena hx1 hx hoff_lt hnstr (fun _ => hp9_al)
        refine ⟨_, _, _, ht_ex, hr4_sh, ?_, hs1, fun r hr7 hr8 hr9 => ?_⟩
        · simpa [Function.update_of_ne] using hhp_sh.trans' hhp0
        · dsimp only; rw [hregs_sh r hr7 hr9]; dsimp only; rw [Function.update_of_ne hr8]
      have he_nr : stmtNoRet (Stmt.cond (fieldLoadExpr 4 OFF_HASE)
          (Stmt.assign 8 (fieldLoadExpr 4 OFF_AF_PTR) ;;
           shiftPtrStmt (SplayProcs.atBase spBase) (.reg 3) 8 2 6 7 9 ;;
           Stmt.store (fieldAddrExpr 4 OFF_AF_PTR) (.reg 9) ;;
           Stmt.assign 8 (fieldLoadExpr 4 OFF_AB_PTR) ;;
           shiftPtrStmt (SplayProcs.atBase spBase) (.bin .sub (.const 1) (.reg 3)) 8 2 6 7 9 ;;
           Stmt.store (fieldAddrExpr 4 OFF_AB_PTR) (.reg 9) ;;
           Stmt.assign 8 (fieldLoadExpr 4 OFF_FLOW_PTR) ;;
           Stmt.assign 10 (fieldLoadExpr 4 OFF_DIR) ;;
           shiftPtrStmt (SplayProcs.atBase spBase)
             (.bin .sub (.const 1) (.bin .eq (.reg 10) (.reg 3))) 8 2 6 7 9 ;;
           Stmt.store (fieldAddrExpr 4 OFF_FLOW_PTR) (.reg 9)) Stmt.nop) = true := by
        simp [stmtNoRet, shiftPtrStmt]
      rcases exec_seq_of_noRet he_nr h5 with ⟨_, st1, _, _, _, he_ex, h6, _⟩
      have hst_e_r4 : Function.update (Function.update (Function.update
          (Function.update st.regs 4 v4) 5 v5) 6 vL) 7 vhp 4 = nb + NODE_STRIDE * x := by
        simp [Function.update_of_ne, hv4_eq]
      have hst_e_r7 : hp0 ≤ Function.update (Function.update (Function.update
          (Function.update st.regs 4 v4) 5 v5) 6 vL) 7 vhp 7 := by
        simpa [Function.update_self] using hvhp_eq
      have he_ok : SafeMem mem0 nb cap hp0 st1.mem ∧ st1.regs 4 = nb + NODE_STRIDE * x ∧
          hp0 ≤ st1.regs 7 ∧ st1.regs 0 = nb ∧ st1.regs 2 = st.regs 2 ∧ st1.regs 3 = st.regs 3 := by
        rcases exec_cond_elim he_ex with ⟨_, ve, _, _, _, hbre, _⟩
        by_cases he0 : ve = 0
        · simp only [he0, ↓reduceIte] at hbre
          rcases exec_nop_iff.1 hbre with ⟨_, _, rfl, _⟩
          refine ⟨hs, hst_e_r4, hst_e_r7, ?_, ?_, ?_⟩ <;>
            simp [Function.update_of_ne, h0]
        · simp only [he0, ↓reduceIte] at hbre
          rcases h_sh OFF_AF_PTR (by decide) (by decide) (Or.inl rfl) hbre
            hst_e_r4 hst_e_r7 hs with ⟨_, st_a, _, ha_b, hr4_a, hr7_a, hs_a, hregs_a⟩
          rcases h_sh OFF_AB_PTR (by decide) (by decide) (Or.inr (Or.inl rfl)) ha_b hr4_a hr7_a hs_a with
            ⟨_, st_b, _, hb_f, hr4_b, hr7_b, hs_b, hregs_b⟩
          rcases exec_seq_assign_elim hb_f with ⟨_, v8, _, _, _, hb_d, _⟩
          rcases exec_seq_assign_elim hb_d with ⟨_, v10, _, _, _, hb_sh, _⟩
          rcases exec_seq_of_noRet stmtNoRet_shiftPtr hb_sh with ⟨_, st_c, _, _, _, hsh_c, hst_c, _⟩
          let rs_c := Function.update (Function.update st_b.regs 8 v8) 10 v10
          rcases shiftPtr_safeExec hp_prog harena (LReg := 6) (hpReg := 7) (outPtrReg := 9)
            (st := { st_b with regs := rs_c }) (by decide) (by decide) (by simpa using hs_b)
            (by dsimp only [rs_c]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr7_b)
            hsh_c with ⟨_, hs_c, hhp_c, hp9_c, hregs_c⟩
          rcases exec_store_iff.1 hst_c with ⟨_, af, vf, _, haf, hvf, _, rfl, rfl, _⟩
          have hr4_c : st_c.regs 4 = nb + NODE_STRIDE * x := by
            rw [hregs_c 4 (by decide) (by decide)]; dsimp only [rs_c]; simp [Function.update_of_ne, hr4_b]
          have haf_eq : af = nb + NODE_STRIDE * x + OFF_FLOW_PTR := by
            rcases eval_fieldAddr_some haf with ⟨rfl, _⟩; rw [hr4_c]
          have hvf_eq : vf = st_c.regs 9 := by simp [Expr.eval] at hvf; exact hvf.symm
          have hs_final : SafeMem mem0 nb cap hp0 (Function.update st_c.mem af vf) := by
            rw [haf_eq]
            exact hs_c.update_nonStruct hnb harena hx1 hx (by decide) (by decide)
              (fun _ => hvf_eq ▸ Or.inr (Or.inl hp9_c))
          have hr_pres : ∀ r, r ∈ [0, 2, 3] → st_c.regs r = st.regs r := fun r hr => by
            have hneq : r ≠ 7 ∧ r ≠ 8 ∧ r ≠ 9 ∧ r ≠ 10 ∧ r ≠ 4 ∧ r ≠ 5 ∧ r ≠ 6 := by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl <;> decide
            rw [hregs_c r hneq.1 hneq.2.2.1]
            dsimp only [rs_c]
            rw [Function.update_of_ne hneq.2.2.2.1, Function.update_of_ne hneq.2.1,
              hregs_b r hneq.1 hneq.2.1 hneq.2.2.1,
              hregs_a r hneq.1 hneq.2.1 hneq.2.2.1]
            simp [Function.update_of_ne hneq.1, Function.update_of_ne hneq.2.2.2.2.2.2,
              Function.update_of_ne hneq.2.2.2.2.2.1, Function.update_of_ne hneq.2.2.2.2.1]
          exact ⟨hs_final, hr4_c, hhp_c.trans' (by dsimp only [rs_c]; simp [Function.update_of_ne, hr7_b]),
            by simpa [h0] using hr_pres 0 (by simp), hr_pres 2 (by simp), hr_pres 3 (by simp)⟩
      rcases he_ok with ⟨hs1, hr4_1, hr7_1, hr0_1, hr2_1, hr3_1⟩
      rcases h_sh OFF_MIN1_VAL (by decide) (by decide) (by decide) h6 hr4_1 hr7_1 hs1 with
        ⟨_, st2, _, h7, hr4_2, hr7_2, hs2, hregs2⟩
      rcases h_sh OFF_MIN2_VAL (by decide) (by decide) (by decide) h7 hr4_2 hr7_2 hs2 with
        ⟨_, st3, _, h8, hr4_3, hr7_3, hs3, hregs3⟩
      rcases exec_seq_assign_elim h8 with ⟨_, v10a, _, _, _, h9, _⟩
      rcases exec_seq_assign_elim h9 with ⟨_, v10b, _, _, _, h10, _⟩
      rcases exec_seq_assign_elim h10 with ⟨_, v11a, _, _, _, h11, _⟩
      rcases exec_seq_assign_elim h11 with ⟨_, v11b, _, _, _, h12, _⟩
      rcases exec_seq_assign_elim h12 with ⟨_, v9c, _, _, _, h13, _⟩
      have htg_nr : stmtNoRet (Stmt.cond (.reg 9)
          (Stmt.cond (fieldLoadExpr 4 OFF_HAS_TAG)
            (Stmt.assign 8 (fieldLoadExpr 4 OFF_TAG_PTR) ;;
             Stmt.assign 10 (fieldLoadExpr 4 OFF_TAG_NEG) ;;
             shiftPtrStmt (SplayProcs.atBase spBase) (.bin .eq (.reg 10) (.reg 3)) 8 2 6 7 9 ;;
             Stmt.store (fieldAddrExpr 4 OFF_TAG_PTR) (.reg 9))
            (Stmt.store (fieldAddrExpr 4 OFF_HAS_TAG) (.const 1) ;;
             Stmt.store (fieldAddrExpr 4 OFF_TAG_PTR) (.reg 2) ;;
             Stmt.store (fieldAddrExpr 4 OFF_TAG_NEG) (.reg 3))) Stmt.nop) = true := by
        simp [stmtNoRet, shiftPtrStmt]
      rcases exec_seq_of_noRet htg_nr h13 with ⟨_, st4, _, _, _, htg_ex, h14, _⟩
      have hr_mid : ∀ r, r ∈ [0, 2, 4, 7] →
          Function.update (Function.update (Function.update (Function.update
            (Function.update st3.regs 10 v10a) 10 v10b) 11 v11a) 11 v11b) 9 v9c r =
          st3.regs r := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp [Function.update_of_ne]
      have hr0_3 : st3.regs 0 = nb := by
        rw [hregs3 0 (by decide) (by decide) (by decide),
          hregs2 0 (by decide) (by decide) (by decide), hr0_1]
      have hr2_3 : st3.regs 2 = st.regs 2 := by
        rw [hregs3 2 (by decide) (by decide) (by decide),
          hregs2 2 (by decide) (by decide) (by decide), hr2_1]
      have htg_ok : SafeMem mem0 nb cap hp0 st4.mem ∧ st4.regs 0 = nb ∧ hp0 ≤ st4.regs 7 := by
        rcases exec_cond_elim htg_ex with ⟨_, v9, _, _, _, hbr9, _⟩
        by_cases hv9_0 : v9 = 0
        · simp only [hv9_0, ↓reduceIte] at hbr9
          rcases exec_nop_iff.1 hbr9 with ⟨_, _, rfl, _⟩
          refine ⟨hs3, ?_, ?_⟩
          · dsimp only; rw [hr_mid 0 (by simp), hr0_3]
          · dsimp only; rw [hr_mid 7 (by simp)]; exact hr7_3
        · simp only [hv9_0, ↓reduceIte] at hbr9
          rcases exec_cond_elim hbr9 with ⟨_, vht, _, _, _, hbrt, _⟩
          by_cases hvht_0 : vht = 0
          · simp only [hvht_0, ↓reduceIte] at hbrt
            rcases exec_seq_store_elim hbrt with ⟨_, aht, vht', _, _, haht, _, hbrt2, _⟩
            rcases exec_seq_store_elim hbrt2 with ⟨_, atp, vtp, _, _, hatp, hvtp, hbrt3, _⟩
            rcases exec_store_iff.1 hbrt3 with ⟨_, atn, vtn, _, hatn, _, _, rfl, rfl, _⟩
            have hm4 := hr_mid 4 (by simp)
            rw [hr4_3] at hm4
            have haht_eq : aht = nb + NODE_STRIDE * x + OFF_HAS_TAG := by
              rcases eval_fieldAddr_some haht with ⟨rfl, _⟩; exact congrArg (· + OFF_HAS_TAG) hm4
            have hatp_eq : atp = nb + NODE_STRIDE * x + OFF_TAG_PTR := by
              rcases eval_fieldAddr_some hatp with ⟨rfl, _⟩; exact congrArg (· + OFF_TAG_PTR) hm4
            have hatn_eq : atn = nb + NODE_STRIDE * x + OFF_TAG_NEG := by
              rcases eval_fieldAddr_some hatn with ⟨rfl, _⟩; exact congrArg (· + OFF_TAG_NEG) hm4
            have hvtp_eq : vtp = st.regs 2 := by
              simp only [Expr.eval] at hvtp; cases hvtp; rw [hr_mid 2 (by simp), hr2_3]
            have hs_ht : SafeMem mem0 nb cap hp0 (Function.update st3.mem aht vht') := by
              rw [haht_eq]; exact hs3.update_nonStruct hnb harena hx1 hx
                (by decide) (by decide) (fun h => False.elim ((by decide : OFF_HAS_TAG ∉ ptrOffs) h))
            have hs_tp : SafeMem mem0 nb cap hp0 (Function.update (Function.update st3.mem aht vht') atp vtp) := by
              rw [hatp_eq, hvtp_eq]; exact hs_ht.update_nonStruct hnb harena hx1 hx
                (by decide) (by decide) (fun _ => htptr)
            have hs_tn : SafeMem mem0 nb cap hp0 (Function.update (Function.update
                (Function.update st3.mem aht vht') atp vtp) atn vtn) := by
              rw [hatn_eq]; exact hs_tp.update_nonStruct hnb harena hx1 hx
                (by decide) (by decide) (fun h => False.elim ((by decide : OFF_TAG_NEG ∉ ptrOffs) h))
            exact ⟨by simpa using hs_tn,
              by simp [hr0_3],
              by dsimp only; rw [hr_mid 7 (by simp)]; exact hr7_3⟩
          · simp only [hvht_0, ↓reduceIte] at hbrt
            rcases exec_seq_assign_elim hbrt with ⟨_, v8t, _, _, _, hbt1, _⟩
            rcases exec_seq_assign_elim hbt1 with ⟨_, v10t, _, _, _, hbt2, _⟩
            rcases exec_seq_of_noRet stmtNoRet_shiftPtr hbt2 with ⟨_, st_t, _, _, _, hsh_t, hst_t, _⟩
            let rs_t := Function.update (Function.update
              (Function.update (Function.update (Function.update (Function.update
              (Function.update st3.regs 10 v10a) 10 v10b) 11 v11a) 11 v11b) 9 v9c)
              8 v8t) 10 v10t
            rcases shiftPtr_safeExec hp_prog harena (LReg := 6) (hpReg := 7) (outPtrReg := 9)
              (st := { st3 with regs := rs_t }) (by decide) (by decide) (by simpa using hs3)
              (by dsimp only [rs_t]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                hr_mid 7 (by simp)]; exact hr7_3) hsh_t with ⟨_, hs_t, hhp_t, hp9_t, hregs_t⟩
            rcases exec_store_iff.1 hst_t with ⟨_, atp, vtp, _, hatp, hvtp, _, rfl, rfl, _⟩
            have hm4 : st_t.regs 4 = nb + NODE_STRIDE * x := by
              rw [hregs_t 4 (by decide) (by decide)]; dsimp only [rs_t]
              simp [Function.update_of_ne, hr4_3]
            have hatp_eq : atp = nb + NODE_STRIDE * x + OFF_TAG_PTR := by
              rcases eval_fieldAddr_some hatp with ⟨rfl, _⟩; rw [hm4]
            have hvtp_eq : vtp = st_t.regs 9 := by simp [Expr.eval] at hvtp; exact hvtp.symm
            have hs_fin : SafeMem mem0 nb cap hp0 (Function.update st_t.mem atp vtp) := by
              rw [hatp_eq]
              exact hs_t.update_nonStruct hnb harena hx1 hx (by decide) (by decide)
                (fun _ => hvtp_eq ▸ Or.inr (Or.inl hp9_t))
            refine ⟨hs_fin, ?_, ?_⟩
            · dsimp only
              rw [hregs_t 0 (by decide) (by decide)]; dsimp only [rs_t]
              rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                hr_mid 0 (by simp), hr0_3]
            · refine hhp_t.trans' ?_
              dsimp only [rs_t]
              rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                hr_mid 7 (by simp)]
              exact hr7_3
      rcases htg_ok with ⟨hs4, hr0_4, hr7_4⟩
      rcases exec_seq_store_elim h14 with ⟨_, ahp, vhp', _, _, hahp, hvhp', h15, _⟩
      have hahp_eq : ahp = nb - 1 := by rw [eval_sub_reg_const hahp, hr0_4]
      have hvhp'_eq : vhp' = st4.regs 7 := by simp [Expr.eval] at hvhp'; exact hvhp'.symm
      have hs5 : SafeMem mem0 nb cap hp0 (Function.update st4.mem ahp vhp') := by
        rw [hahp_eq, hvhp'_eq]; exact hs4.update_hp hnb hr7_4
      rcases exec_ret_iff.1 h15 with ⟨_, vret, _, hvret, rfl, rfl, _⟩
      simp [Expr.eval] at hvret; cases hvret
      exact ⟨rfl, by simpa using hs5⟩

theorem pushDown_safeExec {w h spBase : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp_prog : p.HasAt spBase (splayBodies (SplayProcs.atBase spBase) h))
    {mem0 : ℕ → ℕ} {nb cap hp0 : ℕ} (hnb : 3 ≤ nb) (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    {fuel : ℕ} {st st' : State} {o : Outcome} {c x : ℕ}
    (hx : x ≤ cap) (h0 : st.regs 0 = nb) (h1 : st.regs 1 = x)
    (hs : SafeMem mem0 nb cap hp0 st.mem)
    (hex : exec w p ω fuel (pushDownBody (SplayProcs.atBase spBase)) st = some (o, st', c)) :
    o = .returned 0 ∧ SafeMem mem0 nb cap hp0 st'.mem := by
  rcases splayBodies_procs_eq hp_prog with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hrev, happ, _⟩
  let sp := SplayProcs.atBase spBase
  dsimp only [pushDownBody] at hex
  rcases exec_cond_elim hex with ⟨_, vx, _, _, hvx, hbr1, _⟩
  simp only [Expr.eval, h1] at hvx; cases hvx
  by_cases hx0 : x = 0
  · simp only [hx0, ↓reduceIte] at hbr1
    rcases exec_ret_iff.1 hbr1 with ⟨_, v0, _, hv0, rfl, rfl, _⟩
    simp [Expr.eval] at hv0; cases hv0; exact ⟨rfl, hs⟩
  · simp only [hx0, ↓reduceIte] at hbr1
    have hx1 : 1 ≤ x := Nat.pos_of_ne_zero hx0
    rcases exec_seq_assign_elim hbr1 with ⟨_, v2, _, _, hv2, h2, _⟩
    rcases exec_seq_assign_elim h2 with ⟨_, v3i, _, _, _, h3, _⟩
    have hv2_eq : v2 = nb + NODE_STRIDE * x := by
      rcases eval_nodePtr_some hv2 with ⟨rfl, _⟩; rw [h0, h1]
    have hcr_nr : stmtNoRet (Stmt.cond (.reg 3)
        (Stmt.assign 4 (fieldLoadExpr 2 OFF_LEFT) ;;
         Stmt.call 5 sp.revNode [.reg 0, .reg 4] ;;
         Stmt.assign 4 (fieldLoadExpr 2 OFF_RIGHT) ;;
         Stmt.call 5 sp.revNode [.reg 0, .reg 4] ;;
         Stmt.store (fieldAddrExpr 2 OFF_REV) (.const 0)) Stmt.nop) = true := by
      simp [stmtNoRet]
    rcases exec_seq_of_noRet hcr_nr h3 with ⟨_, st1, _, _, _, hcr_ex, h4, _⟩
    have hr0_e : Function.update (Function.update st.regs 2 v2) 3 v3i 0 = nb := by
      simp [Function.update_of_ne, h0]
    have hr2_e : Function.update (Function.update st.regs 2 v2) 3 v3i 2 = nb + NODE_STRIDE * x := by
      simp [Function.update_of_ne, hv2_eq]
    have hcr_ok : SafeMem mem0 nb cap hp0 st1.mem ∧ st1.regs 0 = nb ∧
        st1.regs 2 = nb + NODE_STRIDE * x := by
      rcases exec_cond_elim hcr_ex with ⟨_, v3, _, _, _, hbr3, _⟩
      by_cases hv3_0 : v3 = 0
      · simp only [hv3_0, ↓reduceIte] at hbr3
        rcases exec_nop_iff.1 hbr3 with ⟨_, _, rfl, _⟩; exact ⟨hs, hr0_e, hr2_e⟩
      · simp only [hv3_0, ↓reduceIte] at hbr3
        rcases exec_seq_assign_elim hbr3 with ⟨_, vl, _, _, hvl, hcall1, _⟩
        rcases exec_seq_call_elim hcall1 with ⟨_, _, _, b1, _, st_r1, _, _, _, _, hvs1, hpb1, hrec1, ha_r, _⟩
        have hb1 : b1 = revNodeBody := Option.some.inj (hpb1.symm.trans hrev)
        subst hb1
        rcases evalArgs_cons.1 hvs1 with ⟨a0, rest1, ha0, hrest1, rfl⟩
        rcases evalArgs_cons.1 hrest1 with ⟨a1, nil1, ha1, hnil1, rfl⟩
        rw [evalArgs_nil.1 hnil1] at *
        have ha0_eq : a0 = nb := by
          simp [Expr.eval, Function.update_of_ne, h0] at ha0; exact ha0.symm
        have ha1_eq : a1 = vl := by simp [Expr.eval, Function.update_self] at ha1; exact ha1.symm
        have hvl_eq : vl ≤ cap := by
          rw [eval_fieldLoad_some hvl]; dsimp only
          rw [Function.update_of_ne (by decide), hv2_eq]; exact (hs.2.2.1 x hx1 hx).1
        let st_c1 : State := { st with regs := fun i => [a0, a1].getD i 0 }
        rcases revNode_safeExec hnb harena (st := st_c1) (ha1_eq ▸ hvl_eq)
          (by simp [st_c1, ha0_eq]) (by simp [st_c1, ha1_eq]) (by simpa [st_c1] using hs) hrec1 with
          ⟨_, hs_r1⟩
        rcases exec_seq_assign_elim ha_r with ⟨_, vr, _, _, hvr, hcall2, _⟩
        rcases exec_seq_call_elim hcall2 with ⟨_, _, _, b2, _, _, _, _, _, _, hvs2, hpb2, hrec2, hst_rev, _⟩
        have hb2 : b2 = revNodeBody := Option.some.inj (hpb2.symm.trans hrev)
        subst hb2
        rcases evalArgs_cons.1 hvs2 with ⟨b0, rest2, hb0, hrest2, rfl⟩
        rcases evalArgs_cons.1 hrest2 with ⟨b1, nil2, hb1', hnil2, rfl⟩
        rw [evalArgs_nil.1 hnil2] at *
        have hb0_eq : b0 = nb := by
          simp only [Expr.eval] at hb0
          cases hb0
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), hr0_e]
        have hb1_eq : b1 = vr := by simp [Expr.eval, Function.update_self] at hb1'; exact hb1'.symm
        have hvr_eq : vr ≤ cap := by
          rw [eval_fieldLoad_some hvr]
          dsimp only
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr2_e]
          exact (hs_r1.2.2.1 x hx1 hx).2.1
        let st_c2 : State := { st_r1 with regs := fun i => [b0, b1].getD i 0 }
        rcases revNode_safeExec hnb harena (st := st_c2) (hb1_eq ▸ hvr_eq)
          (by simp [st_c2, hb0_eq]) (by simp [st_c2, hb1_eq]) hs_r1 hrec2 with ⟨_, hs_r2⟩
        rcases exec_store_iff.1 hst_rev with ⟨_, arev, _, _, harev, _, _, rfl, rfl, _⟩
        have harev_eq : arev = nb + NODE_STRIDE * x + OFF_REV := by
          rcases eval_fieldAddr_some harev with ⟨rfl, _⟩
          dsimp only
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr2_e]
        dsimp only; rw [harev_eq]
        refine ⟨hs_r2.update_nonStruct hnb harena hx1 hx (by decide) (by decide)
          (fun h => False.elim ((by decide : OFF_REV ∉ ptrOffs) h)), ?_, ?_⟩
        · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr0_e]
        · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr2_e]
    rcases hcr_ok with ⟨hs1, hr0_1, hr2_1⟩
    rcases exec_seq_assign_elim h4 with ⟨_, vht_r, _, _, _, h5, _⟩
    have htg_cond_nr : stmtNoRet (Stmt.cond (.reg 3)
        (Stmt.assign 4 (fieldLoadExpr 2 OFF_TAG_PTR) ;;
         Stmt.assign 5 (fieldLoadExpr 2 OFF_TAG_NEG) ;;
         Stmt.store (fieldAddrExpr 2 OFF_HAS_TAG) (.const 0) ;;
         Stmt.store (fieldAddrExpr 2 OFF_TAG_PTR) (.const 0) ;;
         Stmt.store (fieldAddrExpr 2 OFF_TAG_NEG) (.const 0) ;;
         Stmt.assign 6 (fieldLoadExpr 2 OFF_LEFT) ;;
         Stmt.call 7 sp.applyTag [.reg 0, .reg 6, .reg 4, .reg 5] ;;
         Stmt.assign 6 (fieldLoadExpr 2 OFF_RIGHT) ;;
         Stmt.call 7 sp.applyTag [.reg 0, .reg 6, .reg 4, .reg 5]) Stmt.nop) = true := by
      simp [stmtNoRet]
    rcases exec_seq_of_noRet htg_cond_nr h5 with ⟨_, st2, _, _, _, htg_cond_ex, hret, _⟩
    rcases exec_cond_elim htg_cond_ex with ⟨_, vht, _, _, _, hbrt, _⟩
    by_cases hvht_0 : vht = 0
    · simp only [hvht_0, ↓reduceIte] at hbrt
      rcases exec_nop_iff.1 hbrt with ⟨_, _, rfl, _⟩
      rcases exec_ret_iff.1 hret with ⟨_, v0, _, hv0, rfl, rfl, _⟩
      simp [Expr.eval] at hv0; cases hv0; exact ⟨rfl, hs1⟩
    · simp only [hvht_0, ↓reduceIte] at hbrt
      rcases exec_seq_assign_elim hbrt with ⟨_, v4t, _, _, hv4t, ht2, _⟩
      rcases exec_seq_assign_elim ht2 with ⟨_, v5t, _, _, _, ht3, _⟩
      rcases exec_seq_store_elim ht3 with ⟨_, aht, vht'', _, _, haht, _, ht4, _⟩
      rcases exec_seq_store_elim ht4 with ⟨_, atp, vtp'', _, _, hatp, hvtp'', ht5, _⟩
      rcases exec_seq_store_elim ht5 with ⟨_, atn, vtn'', _, _, hatn, _, ht6, _⟩
      rcases exec_seq_assign_elim ht6 with ⟨_, vl, _, _, hvl, ht7, _⟩
      rcases exec_seq_call_elim ht7 with ⟨_, _, _, b1, _, st_a1, _, _, _, _, hvs1, hpb1, hrec1, ht8, _⟩
      have hvtp_0 : vtp'' = 0 := by simp [Expr.eval] at hvtp''; exact hvtp''.symm
      have hv4t_eq : PtrAllowed mem0 nb cap hp0 v4t := by
        rw [eval_fieldLoad_some hv4t]; dsimp only
        rw [Function.update_of_ne (by decide), hr2_1]
        exact hs1.2.2.2 x OFF_TAG_PTR hx1 hx (by decide)
      have haht_eq : aht = nb + NODE_STRIDE * x + OFF_HAS_TAG := by
        rcases eval_fieldAddr_some haht with ⟨rfl, _⟩; simp [Function.update_of_ne, hr2_1]
      have hatp_eq : atp = nb + NODE_STRIDE * x + OFF_TAG_PTR := by
        rcases eval_fieldAddr_some hatp with ⟨rfl, _⟩; simp [Function.update_of_ne, hr2_1]
      have hatn_eq : atn = nb + NODE_STRIDE * x + OFF_TAG_NEG := by
        rcases eval_fieldAddr_some hatn with ⟨rfl, _⟩; simp [Function.update_of_ne, hr2_1]
      let mem_t1 := Function.update (Function.update (Function.update st1.mem aht vht'') atp vtp'') atn vtn''
      have hs_t1 : SafeMem mem0 nb cap hp0 mem_t1 := by
        dsimp only [mem_t1]
        rw [haht_eq, hatp_eq, hatn_eq]
        refine ((hs1.update_nonStruct hnb harena hx1 hx (by decide) (by decide)
            (fun h => False.elim ((by decide : OFF_HAS_TAG ∉ ptrOffs) h))).update_nonStruct
            hnb harena hx1 hx (by decide) (by decide) (fun _ => hvtp_0 ▸ Or.inl rfl)).update_nonStruct
            hnb harena hx1 hx (by decide) (by decide)
            (fun h => False.elim ((by decide : OFF_TAG_NEG ∉ ptrOffs) h))
      have hb1 : b1 = applyTagBody sp := Option.some.inj (hpb1.symm.trans happ)
      subst hb1
      rcases evalArgs_cons.1 hvs1 with ⟨a0, r1, ha0, hr1, rfl⟩
      rcases evalArgs_cons.1 hr1 with ⟨a1, r2, ha1, hr2, rfl⟩
      rcases evalArgs_cons.1 hr2 with ⟨a2, r3, ha2, hr3, rfl⟩
      rcases evalArgs_cons.1 hr3 with ⟨a3, nil1, ha3, hnil1, rfl⟩
      rw [evalArgs_nil.1 hnil1] at *
      have ha0_eq : a0 = nb := by
        simp [Expr.eval, Function.update_of_ne, hr0_1] at ha0; exact ha0.symm
      have ha1_eq : a1 = vl := by simp [Expr.eval, Function.update_self] at ha1; exact ha1.symm
      have ha2_eq : a2 = v4t := by
        simp [Expr.eval, Function.update_of_ne] at ha2; exact ha2.symm
      have hvl_eq : vl ≤ cap := by
        rw [eval_fieldLoad_some hvl]; dsimp only
        simp only [Function.update_of_ne (by decide : (2 : ℕ) ≠ 5),
          Function.update_of_ne (by decide : (2 : ℕ) ≠ 4),
          Function.update_of_ne (by decide : (2 : ℕ) ≠ 3), hr2_1]
        exact (hs_t1.2.2.1 x hx1 hx).1
      let st_ca1 : State := { mem := mem_t1, regs := fun i => [a0, a1, a2, a3].getD i 0, pos := st1.pos }
      rcases applyTag_safeExec hp_prog hnb harena (mem0 := mem0) (st := st_ca1) (ha1_eq ▸ hvl_eq)
        (by simp [st_ca1, ha0_eq]) (by simp [st_ca1, ha1_eq])
        (by simpa [st_ca1, ha2_eq] using hv4t_eq) hs_t1 hrec1 with ⟨_, hs_a1⟩
      rcases exec_seq_assign_elim ht8 with ⟨_, vr, _, _, hvr, ht9, _⟩
      rcases exec_call_elim ht9 with ⟨_, vs2, b2, _, _, _, _, hvs2, hpb2, hrec2, _, rfl, _⟩
      have hb2 : b2 = applyTagBody sp := Option.some.inj (hpb2.symm.trans happ)
      subst hb2
      rcases evalArgs_cons.1 hvs2 with ⟨b0, rb1, hb0, hrb1, rfl⟩
      rcases evalArgs_cons.1 hrb1 with ⟨b1, rb2, hb1', hrb2, rfl⟩
      rcases evalArgs_cons.1 hrb2 with ⟨b2, rb3, hb2', hrb3, rfl⟩
      rcases evalArgs_cons.1 hrb3 with ⟨b3, nil2, hb3', hnil2, rfl⟩
      rw [evalArgs_nil.1 hnil2] at *
      have hb0_eq : b0 = nb := by
        simp [Expr.eval, Function.update_of_ne, hr0_1] at hb0; exact hb0.symm
      have hb1_eq : b1 = vr := by simp [Expr.eval, Function.update_self] at hb1'; exact hb1'.symm
      have hb2_eq : b2 = v4t := by
        simp [Expr.eval, Function.update_of_ne] at hb2'; exact hb2'.symm
      have hvr_eq : vr ≤ cap := by
        rw [eval_fieldLoad_some hvr]; dsimp only
        simp only [Function.update_of_ne (by decide : (2 : ℕ) ≠ 7),
          Function.update_of_ne (by decide : (2 : ℕ) ≠ 6),
          Function.update_of_ne (by decide : (2 : ℕ) ≠ 5),
          Function.update_of_ne (by decide : (2 : ℕ) ≠ 4),
          Function.update_of_ne (by decide : (2 : ℕ) ≠ 3), hr2_1]
        exact (hs_a1.2.2.1 x hx1 hx).2.1
      let st_ca2 : State := { st_a1 with regs := fun i => [b0, b1, b2, b3].getD i 0 }
      rcases applyTag_safeExec hp_prog hnb harena (mem0 := mem0) (st := st_ca2) (hb1_eq ▸ hvr_eq)
        (by simp [st_ca2, hb0_eq]) (by simp [st_ca2, hb1_eq])
        (by simpa [st_ca2, hb2_eq] using hv4t_eq) hs_a1 hrec2 with ⟨_, hs_a2⟩
      rcases exec_ret_iff.1 hret with ⟨_, v0, _, hv0, rfl, rfl, _⟩
      simp [Expr.eval] at hv0; cases hv0; exact ⟨rfl, by simpa using hs_a2⟩

theorem pull_safeExec {w h spBase : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp_prog : p.HasAt spBase (splayBodies (SplayProcs.atBase spBase) h))
    {mem0 : ℕ → ℕ} {nb cap hp0 : ℕ} (hnb : 3 ≤ nb) (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    (hz0 : SlotZeroOk mem0 nb)
    {fuel : ℕ} {st st' : State} {o : Outcome} {c x : ℕ}
    (hx : x ≤ cap) (h0 : st.regs 0 = nb) (h1 : st.regs 1 = x)
    (hs : SafeMem mem0 nb cap hp0 st.mem)
    (hex : exec w p ω fuel (pullBody (SplayProcs.atBase spBase)) st = some (o, st', c)) :
    o = .returned 0 ∧ SafeMem mem0 nb cap hp0 st'.mem := by
  let sp := SplayProcs.atBase spBase
  dsimp only [pullBody] at hex
  rcases exec_cond_elim hex with ⟨_, vx, _, _, hvx, hbr1, _⟩
  simp only [Expr.eval, h1] at hvx; cases hvx
  by_cases hx0 : x = 0
  · simp only [hx0, ↓reduceIte] at hbr1
    rcases exec_ret_iff.1 hbr1 with ⟨_, v0, _, hv0, rfl, rfl, _⟩
    simp [Expr.eval] at hv0; cases hv0; exact ⟨rfl, hs⟩
  · simp only [hx0, ↓reduceIte] at hbr1
    have hx1 : 1 ≤ x := Nat.pos_of_ne_zero hx0
    rcases exec_seq_assign_elim hbr1 with ⟨_, v2, _, _, hv2, h2, _⟩
    rcases exec_seq_assign_elim h2 with ⟨_, l, _, _, hvl, h3, _⟩
    rcases exec_seq_assign_elim h3 with ⟨_, v4, _, _, hv4, h4, _⟩
    rcases exec_seq_assign_elim h4 with ⟨_, r, _, _, hvr, h5, _⟩
    rcases exec_seq_assign_elim h5 with ⟨_, v6, _, _, hv6, h6, _⟩
    rcases exec_seq_assign_elim h6 with ⟨_, v7a, _, _, _, h7, _⟩
    rcases exec_seq_store_elim h7 with ⟨_, avc, vvc, _, _, havc, _, h8, _⟩
    have hv2_eq : v2 = nb + NODE_STRIDE * x := by
      rcases eval_nodePtr_some hv2 with ⟨rfl, _⟩; rw [h0, h1]
    have hl_le : l ≤ cap := by
      rw [eval_fieldLoad_some hvl]; dsimp only
      rw [Function.update_self, hv2_eq]; exact (hs.2.2.1 x hx1 hx).1
    have hv4_eq : v4 = nb + NODE_STRIDE * l := by
      rcases eval_nodePtr_some hv4 with ⟨rfl, _⟩
      simp [Function.update_of_ne, h0]
    have hr_le : r ≤ cap := by
      rw [eval_fieldLoad_some hvr]; dsimp only
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self, hv2_eq]
      exact (hs.2.2.1 x hx1 hx).2.1
    have hv6_eq : v6 = nb + NODE_STRIDE * r := by
      rcases eval_nodePtr_some hv6 with ⟨rfl, _⟩
      simp [Function.update_of_ne, h0]
    have havc_eq : avc = nb + NODE_STRIDE * x + OFF_VCNT := by
      rcases eval_fieldAddr_some havc with ⟨rfl, _⟩
      simp [Function.update_of_ne, hv2_eq]
    have hs1 : SafeMem mem0 nb cap hp0 (Function.update st.mem avc vvc) := by
      rw [havc_eq]
      exact hs.update_nonStruct hnb harena hx1 hx (by decide) (by decide)
        (fun h => False.elim ((by decide : OFF_VCNT ∉ ptrOffs) h))
    rcases exec_seq_assign_elim h8 with ⟨_, v15, _, _, _, h9, _⟩
    rcases exec_seq_assign_elim h9 with ⟨_, v16, _, _, hv16, h10, _⟩
    have hv16_eq : hp0 ≤ v16 := by
      simp only [Expr.eval, Option.map_eq_some_iff] at hv16
      rcases hv16 with ⟨a, ha, rfl⟩
      rcases eval_sub_reg_const ha with rfl
      rw [h0]; exact hs1.1
    rcases exec_seq_assign_elim h10 with ⟨_, v7, _, _, hv7, h11, _⟩
    rcases exec_seq_assign_elim h11 with ⟨_, v8, _, _, hv8, h12, _⟩
    rcases exec_seq_of_noRet stmtNoRet_addOptPtr h12 with ⟨_, st1, _, _, _, ha1_ex, h13, _⟩
    have hv7_p : PtrAllowed mem0 nb cap hp0 v7 := by
      rw [eval_fieldLoad_some hv7]
      have hreg4 : Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update st.regs 2 v2) 3 l) 4 v4) 5 r) 6 v6)
          7 v7a) 15 v15) 16 v16 4 = nb + NODE_STRIDE * l := by
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_self, hv4_eq]
      dsimp only; rw [hreg4]; exact hs1.ptrAllowed_field hz0 hl_le (by decide)
    have hv8_p : PtrAllowed mem0 nb cap hp0 v8 := by
      rw [eval_fieldLoad_some hv8]
      have hreg2 : Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (Function.update st.regs 2 v2) 3 l)
          4 v4) 5 r) 6 v6) 7 v7a) 15 v15) 16 v16) 7 v7 2 = nb + NODE_STRIDE * x := by
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_self, hv2_eq]
      dsimp only; rw [hreg2]; exact hs1.ptrAllowed_field hz0 hx (by decide)
    let rs_p1 := Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      st.regs 2 v2) 3 l) 4 v4) 5 r) 6 v6) 7 v7a) 15 v15) 16 v16) 7 v7) 8 v8
    rcases addOptPtr_safeExec hp_prog harena (p1Reg := 7) (p2Reg := 8) (LReg := 15) (hpReg := 16)
      (outReg := 18) (st := { st with mem := Function.update st.mem avc vvc, regs := rs_p1 })
      (by decide) (by decide) (by simpa using hs1)
      (by dsimp only [rs_p1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self]; exact hv16_eq)
      (by dsimp only [rs_p1]; rw [Function.update_of_ne (by decide), Function.update_self]; exact hv7_p)
      (by dsimp only [rs_p1]; rw [Function.update_self]; exact hv8_p) ha1_ex with
      ⟨_, hs2, hhp2, hp18, hregs2⟩
    rcases exec_seq_assign_elim h13 with ⟨_, v7', _, _, hv7', h14, _⟩
    rcases exec_seq_of_noRet stmtNoRet_addOptPtr h14 with ⟨_, st2, _, _, _, ha2_ex, h15, _⟩
    have hst1_pres : ∀ reg ∈ [0, 1], st1.regs reg = st.regs reg := fun reg hreg => by
      have hr8 : reg ≠ 8 := by rcases List.mem_cons.1 hreg with rfl | hreg <;> simp_all
      have hr7 : reg ≠ 7 := by rcases List.mem_cons.1 hreg with rfl | hreg <;> simp_all
      have hr16 : reg ≠ 16 := by rcases List.mem_cons.1 hreg with rfl | hreg <;> simp_all
      have hr15 : reg ≠ 15 := by rcases List.mem_cons.1 hreg with rfl | hreg <;> simp_all
      have hr6 : reg ≠ 6 := by rcases List.mem_cons.1 hreg with rfl | hreg <;> simp_all
      have hr5 : reg ≠ 5 := by rcases List.mem_cons.1 hreg with rfl | hreg <;> simp_all
      have hr4 : reg ≠ 4 := by rcases List.mem_cons.1 hreg with rfl | hreg <;> simp_all
      have hr3 : reg ≠ 3 := by rcases List.mem_cons.1 hreg with rfl | hreg <;> simp_all
      have hr2 : reg ≠ 2 := by rcases List.mem_cons.1 hreg with rfl | hreg <;> simp_all
      rw [hregs2 reg hr16 (by rcases List.mem_cons.1 hreg with rfl | hreg <;> simp_all)]
      dsimp only [rs_p1]
      simp [Function.update_of_ne hr8, Function.update_of_ne hr7, Function.update_of_ne hr16,
        Function.update_of_ne hr15, Function.update_of_ne hr6, Function.update_of_ne hr5,
        Function.update_of_ne hr4, Function.update_of_ne hr3, Function.update_of_ne hr2]
    have hst1_2 : st1.regs 2 = nb + NODE_STRIDE * x := by
      rw [hregs2 2 (by decide) (by decide)]; dsimp only [rs_p1]; simp [Function.update_of_ne, hv2_eq]
    have hst1_4 : st1.regs 4 = nb + NODE_STRIDE * l := by
      rw [hregs2 4 (by decide) (by decide)]; dsimp only [rs_p1]; simp [Function.update_of_ne, hv4_eq]
    have hst1_6 : st1.regs 6 = nb + NODE_STRIDE * r := by
      rw [hregs2 6 (by decide) (by decide)]; dsimp only [rs_p1]; simp [Function.update_of_ne, hv6_eq]
    have hst1_0 : st1.regs 0 = nb := by rw [hst1_pres 0 (by simp), h0]
    have hst1_1 : st1.regs 1 = x := by rw [hst1_pres 1 (by simp), h1]
    have hst1_16 : hp0 ≤ st1.regs 16 := by
      refine hhp2.trans' ?_
      dsimp only [rs_p1]; simp [Function.update_of_ne, hv16_eq]
    have hv7'_p : PtrAllowed mem0 nb cap hp0 v7' := by
      rw [eval_fieldLoad_some hv7', hst1_6]; exact hs2.ptrAllowed_field hz0 hr_le (by decide)
    let rs_p2 := Function.update st1.regs 7 v7'
    rcases addOptPtr_safeExec hp_prog harena (p1Reg := 18) (p2Reg := 7) (LReg := 15) (hpReg := 16)
      (outReg := 8) (st := { st1 with regs := rs_p2 })
      (by decide) (by decide) (by simpa using hs2)
      (by dsimp only [rs_p2]; rw [Function.update_of_ne (by decide)]; exact hst1_16)
      (by dsimp only [rs_p2]; rw [Function.update_of_ne (by decide)]; exact hp18)
      (by dsimp only [rs_p2]; rw [Function.update_self]; exact hv7'_p) ha2_ex with
      ⟨_, hs3, hhp3, hp8_f, hregs3⟩
    rcases exec_seq_store_elim h15 with ⟨_, acf, vcf, _, _, hacf, hvcf, h16, _⟩
    have hst2_2 : st2.regs 2 = nb + NODE_STRIDE * x := by
      rw [hregs3 2 (by decide) (by decide)]; dsimp only [rs_p2]
      rw [Function.update_of_ne (by decide), hst1_2]
    have hacf_eq : acf = nb + NODE_STRIDE * x + OFF_CSUM_FWD := by
      rcases eval_fieldAddr_some hacf with ⟨rfl, _⟩; rw [hst2_2]
    have hvcf_p : PtrAllowed mem0 nb cap hp0 vcf := by
      simp only [Expr.eval] at hvcf; cases hvcf; exact hp8_f
    have hs4 : SafeMem mem0 nb cap hp0 (Function.update st2.mem acf vcf) := by
      rw [hacf_eq]
      exact hs3.update_nonStruct hnb harena hx1 hx (by decide) (by decide) (fun _ => hvcf_p)
    -- Backward csum
    rcases exec_seq_assign_elim h16 with ⟨_, v7b, _, _, hv7b, h17, _⟩
    rcases exec_seq_assign_elim h17 with ⟨_, v8b, _, _, hv8b, h18, _⟩
    rcases exec_seq_of_noRet stmtNoRet_addOptPtr h18 with ⟨_, st3, _, _, _, ha3_ex, h19, _⟩
    have hst2_16 : hp0 ≤ st2.regs 16 := by
      refine hhp3.trans' ?_; dsimp only [rs_p2]; rw [Function.update_of_ne (by decide)]; exact hst1_16
    have hst2_4 : st2.regs 4 = nb + NODE_STRIDE * l := by
      rw [hregs3 4 (by decide) (by decide)]; dsimp only [rs_p2]
      rw [Function.update_of_ne (by decide), hst1_4]
    have hst2_6 : st2.regs 6 = nb + NODE_STRIDE * r := by
      rw [hregs3 6 (by decide) (by decide)]; dsimp only [rs_p2]
      rw [Function.update_of_ne (by decide), hst1_6]
    have hv7b_p : PtrAllowed mem0 nb cap hp0 v7b := by
      rw [eval_fieldLoad_some hv7b, hst2_4]; exact hs4.ptrAllowed_field hz0 hl_le (by decide)
    have hv8b_p : PtrAllowed mem0 nb cap hp0 v8b := by
      rw [eval_fieldLoad_some hv8b]; dsimp only
      rw [Function.update_of_ne (by decide : (2 : ℕ) ≠ 7), hst2_2]
      exact hs4.ptrAllowed_field hz0 hx (by decide)
    let rs_p3 := Function.update (Function.update st2.regs 7 v7b) 8 v8b
    rcases addOptPtr_safeExec hp_prog harena (p1Reg := 7) (p2Reg := 8) (LReg := 15) (hpReg := 16)
      (outReg := 18) (st := { st2 with mem := Function.update st2.mem acf vcf, regs := rs_p3 })
      (by decide) (by decide) (by simpa using hs4)
      (by dsimp only [rs_p3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hst2_16)
      (by dsimp only [rs_p3]; rw [Function.update_of_ne (by decide), Function.update_self]; exact hv7b_p)
      (by dsimp only [rs_p3]; rw [Function.update_self]; exact hv8b_p) ha3_ex with
      ⟨_, hs5, hhp5, hp18b, hregs5⟩
    rcases exec_seq_assign_elim h19 with ⟨_, v7b', _, _, hv7b', h20, _⟩
    rcases exec_seq_of_noRet stmtNoRet_addOptPtr h20 with ⟨_, st4, _, _, _, ha4_ex, h21, _⟩
    have hst3_6 : st3.regs 6 = nb + NODE_STRIDE * r := by
      rw [hregs5 6 (by decide) (by decide)]; dsimp only [rs_p3]; simp [Function.update_of_ne, hst2_6]
    have hv7b'_p : PtrAllowed mem0 nb cap hp0 v7b' := by
      rw [eval_fieldLoad_some hv7b', hst3_6]; exact hs5.ptrAllowed_field hz0 hr_le (by decide)
    have hst3_16 : hp0 ≤ st3.regs 16 := by
      refine hhp5.trans' ?_; dsimp only [rs_p3]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hst2_16
    let rs_p4 := Function.update st3.regs 7 v7b'
    rcases addOptPtr_safeExec hp_prog harena (p1Reg := 18) (p2Reg := 7) (LReg := 15) (hpReg := 16)
      (outReg := 8) (st := { st3 with regs := rs_p4 })
      (by decide) (by decide) (by simpa using hs5)
      (by dsimp only [rs_p4]; rw [Function.update_of_ne (by decide)]; exact hst3_16)
      (by dsimp only [rs_p4]; rw [Function.update_of_ne (by decide)]; exact hp18b)
      (by dsimp only [rs_p4]; rw [Function.update_self]; exact hv7b'_p)
      ha4_ex with ⟨_, hs6, hhp6, hp8_b, hregs6⟩
    rcases exec_seq_store_elim h21 with ⟨_, acb, vcb, _, _, hacb, hvcb, h22, _⟩
    have hst4_2 : st4.regs 2 = nb + NODE_STRIDE * x := by
      rw [hregs6 2 (by decide) (by decide)]; dsimp only [rs_p4]
      rw [Function.update_of_ne (by decide), hregs5 2 (by decide) (by decide)]
      dsimp only [rs_p3]; simp [Function.update_of_ne, hst2_2]
    have hst4_4 : st4.regs 4 = nb + NODE_STRIDE * l := by
      rw [hregs6 4 (by decide) (by decide)]; dsimp only [rs_p4]
      rw [Function.update_of_ne (by decide), hregs5 4 (by decide) (by decide)]
      dsimp only [rs_p3]; simp [Function.update_of_ne, hst2_4]
    have hst4_6 : st4.regs 6 = nb + NODE_STRIDE * r := by
      rw [hregs6 6 (by decide) (by decide)]; dsimp only [rs_p4]
      rw [Function.update_of_ne (by decide), hst3_6]
    have hst4_0 : st4.regs 0 = nb := by
      rw [hregs6 0 (by decide) (by decide)]; dsimp only [rs_p4]
      rw [Function.update_of_ne (by decide), hregs5 0 (by decide) (by decide)]
      dsimp only [rs_p3]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hregs3 0 (by decide) (by decide)]
      dsimp only [rs_p2]; rw [Function.update_of_ne (by decide), hst1_0]
    have hst4_16 : hp0 ≤ st4.regs 16 := by
      refine hhp6.trans' ?_; dsimp only [rs_p4]; rw [Function.update_of_ne (by decide)]; exact hst3_16
    have hacb_eq : acb = nb + NODE_STRIDE * x + OFF_CSUM_BWD := by
      rcases eval_fieldAddr_some hacb with ⟨rfl, _⟩; rw [hst4_2]
    have hvcb_p : PtrAllowed mem0 nb cap hp0 vcb := by
      simp only [Expr.eval] at hvcb; cases hvcb; exact hp8_b
    have hs7 : SafeMem mem0 nb cap hp0 (Function.update st4.mem acb vcb) := by
      rw [hacb_eq]
      exact hs6.update_nonStruct hnb harena hx1 hx (by decide) (by decide) (fun _ => hvcb_p)
    -- Two pullMinNumStmt calls + store hp + ret
    rcases exec_seq_of_noRet stmtNoRet_pullMinNum h22 with ⟨_, st5, _, _, _, hpm1, h23, _⟩
    rcases pullMinNum_safeExec hp_prog hnb harena (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hx1 hx
      (by simpa using hst4_2) (by simpa using hst4_4) (by simpa using hst4_6) hs7
      (by simpa using hs7.ptrAllowed_field hz0 hl_le (by decide))
      (by simpa using hs7.ptrAllowed_field hz0 hr_le (by decide)) hpm1 with
      ⟨_, hs8, hpres5⟩
    rcases exec_seq_of_noRet stmtNoRet_pullMinNum h23 with ⟨_, st6, _, _, _, hpm2, h24, _⟩
    have hst5_2 : st5.regs 2 = nb + NODE_STRIDE * x := by rw [hpres5 2 (by simp), hst4_2]
    have hst5_4 : st5.regs 4 = nb + NODE_STRIDE * l := by rw [hpres5 4 (by simp), hst4_4]
    have hst5_6 : st5.regs 6 = nb + NODE_STRIDE * r := by rw [hpres5 6 (by simp), hst4_6]
    have hst5_0 : st5.regs 0 = nb := by rw [hpres5 0 (by simp), hst4_0]
    have hst5_16 : hp0 ≤ st5.regs 16 := by rw [hpres5 16 (by simp)]; exact hst4_16
    rcases pullMinNum_safeExec hp_prog hnb harena (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hx1 hx hst5_2 hst5_4 hst5_6 hs8
      (hs8.ptrAllowed_field hz0 hl_le (by decide))
      (hs8.ptrAllowed_field hz0 hr_le (by decide)) hpm2 with
      ⟨_, hs9, hpres6⟩
    rcases exec_seq_store_elim h24 with ⟨_, ahp, vhp', _, _, hahp, hvhp', hret, _⟩
    have hahp_eq : ahp = nb - 1 := by
      rw [eval_sub_reg_const hahp, hpres6 0 (by simp), hst5_0]
    have hvhp'_eq : hp0 ≤ vhp' := by
      simp only [Expr.eval] at hvhp'; cases hvhp'
      rw [hpres6 16 (by simp)]; exact hst5_16
    have hs10 : SafeMem mem0 nb cap hp0 (Function.update st6.mem ahp vhp') := by
      rw [hahp_eq]; exact hs9.update_hp hnb hvhp'_eq
    rcases exec_ret_iff.1 hret with ⟨_, vret, _, hvret, rfl, rfl, _⟩
    simp [Expr.eval] at hvret; cases hvret
    exact ⟨rfl, by simpa using hs10⟩


end SplayProcSafety

end MinCostFlow.LinkCut.Prog
