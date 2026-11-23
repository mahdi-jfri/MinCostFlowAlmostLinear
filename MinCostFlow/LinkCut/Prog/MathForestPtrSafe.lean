module

public import MinCostFlow.LinkCut.Prog.MathForestPtrSafeAux

/-!
# Splay Safety, Determinism, and `PtrFootOk` Bridge

Proves `SafeMem` preservation across `pushPathBody`, `rotateBody`, and `splayBody`,
proves `NoRand` for `splayBodies`, and packages `SafeMem.ptrFootOk_of_treeMemMatch` to
close `PtrFootOk` at Word-RAM LCT operation exit.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section SplayProcSafety

theorem pushPath_safeExec {w h spBase : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp_prog : p.HasAt spBase (splayBodies (SplayProcs.atBase spBase) h))
    {mem0 : ℕ → ℕ} {nb cap hp0 : ℕ} (hnb : 3 ≤ nb) (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    (fuel : ℕ) :
    ∀ st st' o c x, x ≤ cap → st.regs 0 = nb → st.regs 1 = x → SafeMem mem0 nb cap hp0 st.mem →
      exec w p ω fuel (pushPathBody (SplayProcs.atBase spBase)) st = some (o, st', c) →
      (∃ rv, o = .returned rv) ∧ SafeMem mem0 nb cap hp0 st'.mem := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro st st' o c x hx h0 h1 hs hex
      rcases splayBodies_procs_eq hp_prog with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpd, _, hpp, _⟩
      let sp := SplayProcs.atBase spBase
      dsimp only [pushPathBody] at hex
      rcases exec_cond_elim hex with ⟨f1, vx, _, hf1, hvx, hbr1, _⟩
      simp only [Expr.eval, h1] at hvx; cases hvx
      by_cases hx0 : x = 0
      · simp only [hx0, ↓reduceIte] at hbr1
        rcases exec_ret_iff.1 hbr1 with ⟨_, v0, _, _, rfl, rfl, _⟩
        exact ⟨⟨v0, rfl⟩, hs⟩
      · simp only [hx0, ↓reduceIte] at hbr1
        have hx1 : 1 ≤ x := Nat.pos_of_ne_zero hx0
        rcases exec_seq_assign_elim hbr1 with ⟨f2, v2, _, hf2, hv2, h2, _⟩
        rcases exec_seq_assign_elim h2 with ⟨f3, px, _, hf3, hpx, hcond, _⟩
        have hv2_eq : v2 = nb + NODE_STRIDE * x := by
          rcases eval_nodePtr_some hv2 with ⟨rfl, _⟩; rw [h0, h1]
        have hpx_le : px ≤ cap := by
          rw [eval_fieldLoad_some hpx]; dsimp only
          rw [Function.update_self, hv2_eq]; exact (hs.2.2.1 x hx1 hx).2.2
        rcases exec_cond_elim hcond with ⟨f4, vpx, _, hf4, hepx, hbr2, _⟩
        simp only [Expr.eval, Function.update_self] at hepx; cases hepx
        by_cases hpx0 : px = 0
        · simp only [hpx0, ↓reduceIte] at hbr2
          rcases exec_seq_call_elim hbr2 with
            ⟨_, _, vs, body, _, _, _, _, _, _, hvs, hpb, hrec, hret, _⟩
          have hb : body = pushDownBody sp := Option.some.inj (hpb.symm.trans hpd)
          subst hb
          rcases evalArgs_cons.1 hvs with ⟨a0, r1, ha0, hr1, rfl⟩
          rcases evalArgs_cons.1 hr1 with ⟨a1, nil1, ha1, hnil1, rfl⟩
          rw [evalArgs_nil.1 hnil1] at *
          have ha0_eq : a0 = nb := by
            simp [Expr.eval, Function.update_of_ne, h0] at ha0; exact ha0.symm
          have ha1_eq : a1 = x := by
            simp [Expr.eval, Function.update_of_ne, h1] at ha1; exact ha1.symm
          let st_c : State := { st with regs := fun i => [a0, a1].getD i 0 }
          rcases pushDown_safeExec hp_prog hnb harena (st := st_c) hx
            (by simp [st_c, ha0_eq]) (by simp [st_c, ha1_eq]) (by simpa [st_c] using hs) hrec with
            ⟨_, hs1⟩
          rcases exec_ret_iff.1 hret with ⟨_, rv, _, _, rfl, rfl, _⟩
          exact ⟨⟨rv, rfl⟩, by simpa using hs1⟩
        · simp only [hpx0, ↓reduceIte] at hbr2
          rcases exec_seq_call_elim hbr2 with
            ⟨f5, f5', vs, body, _, st_p1, _, _, hf5, hf5', hvs, hpb, hrec, hrest, _⟩
          have hb : body = pushPathBody sp := Option.some.inj (hpb.symm.trans hpp)
          subst hb
          rcases evalArgs_cons.1 hvs with ⟨a0, r1, ha0, hr1, rfl⟩
          rcases evalArgs_cons.1 hr1 with ⟨a1, nil1, ha1, hnil1, rfl⟩
          rw [evalArgs_nil.1 hnil1] at *
          have ha0_eq : a0 = nb := by
            simp [Expr.eval, Function.update_of_ne, h0] at ha0; exact ha0.symm
          have ha1_eq : a1 = px := by
            simp [Expr.eval, Function.update_self] at ha1; exact ha1.symm
          have hlt : f5' < fuel := by omega
          let st_p0 : State := { st with regs := fun i => [a0, a1].getD i 0 }
          rcases ih f5' hlt st_p0 _ _ _ px hpx_le (by simp [st_p0, ha0_eq])
            (by simp [st_p0, ha1_eq]) (by simpa [st_p0] using hs) hrec with ⟨_, hs1⟩
          rcases exec_seq_call_elim hrest with
            ⟨_, _, vs2, body2, _, _, _, _, _, _, hvs2, hpb2, hrec2, hret, _⟩
          have hb2 : body2 = pushDownBody sp := Option.some.inj (hpb2.symm.trans hpd)
          subst hb2
          rcases evalArgs_cons.1 hvs2 with ⟨b0, rb1, hb0, hrb1, rfl⟩
          rcases evalArgs_cons.1 hrb1 with ⟨b1, nil2, hb1, hnil2, rfl⟩
          rw [evalArgs_nil.1 hnil2] at *
          have hb0_eq : b0 = nb := by
            simp [Expr.eval, Function.update_of_ne, h0] at hb0; exact hb0.symm
          have hb1_eq : b1 = x := by
            simp [Expr.eval, Function.update_of_ne, h1] at hb1; exact hb1.symm
          let st_p2 : State := { st_p1 with regs := fun i => [b0, b1].getD i 0 }
          rcases pushDown_safeExec hp_prog hnb harena (st := st_p2) hx
            (by simp [st_p2, hb0_eq]) (by simp [st_p2, hb1_eq]) hs1 hrec2 with ⟨_, hs2⟩
          rcases exec_ret_iff.1 hret with ⟨_, rv, _, _, rfl, rfl, _⟩
          exact ⟨⟨rv, rfl⟩, by simpa using hs2⟩

theorem rotate_safeExec {w h spBase : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp_prog : p.HasAt spBase (splayBodies (SplayProcs.atBase spBase) h))
    {mem0 : ℕ → ℕ} {nb cap hp0 : ℕ} (hnb : 3 ≤ nb) (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    (hz0 : SlotZeroOk mem0 nb)
    {fuel : ℕ} {st st' : State} {o : Outcome} {c x : ℕ}
    (hx : x ≤ cap) (h0 : st.regs 0 = nb) (h1 : st.regs 1 = x)
    (hs : SafeMem mem0 nb cap hp0 st.mem)
    (hex : exec w p ω fuel (rotateBody (SplayProcs.atBase spBase)) st = some (o, st', c)) :
    o = .returned 0 ∧ SafeMem mem0 nb cap hp0 st'.mem := by
  rcases splayBodies_procs_eq hp_prog with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpull, _⟩
  let sp := SplayProcs.atBase spBase
  dsimp only [rotateBody] at hex
  rcases exec_seq_assign_elim hex with ⟨_, v2, _, _, hv2, h2, _⟩
  rcases exec_seq_assign_elim h2 with ⟨_, pv, _, _, hpv, hcond, _⟩
  rcases exec_cond_elim hcond with ⟨_, vpv, _, _, hepv, hbr, _⟩
  simp only [Expr.eval, Function.update_self] at hepv; cases hepv
  by_cases hpv0 : pv = 0
  · simp only [hpv0, ↓reduceIte] at hbr
    rcases exec_ret_iff.1 hbr with ⟨_, v0, _, hv0, rfl, rfl, _⟩
    simp [Expr.eval] at hv0; cases hv0; exact ⟨rfl, hs⟩
  · simp only [hpv0, ↓reduceIte] at hbr
    have hv2_eq : v2 = nb + NODE_STRIDE * x := by
      rcases eval_nodePtr_some hv2 with ⟨rfl, _⟩; rw [h0, h1]
    have hx1 : 1 ≤ x := by
      by_contra hlt
      have hx0 : x = 0 := by omega
      have hp_eval : pv = nodeField st.mem nb 0 OFF_PARENT := by
        rw [eval_fieldLoad_some hpv]; dsimp only
        rw [Function.update_self, hv2_eq, hx0]; rfl
      have h0p := hs.slot0_parent (by simpa [nodeField] using hz0 OFF_PARENT (by decide))
      rw [h0p] at hp_eval; exact hpv0 hp_eval
    have hpv_1 : 1 ≤ pv := Nat.pos_of_ne_zero hpv0
    have hpv_le : pv ≤ cap := by
      rw [eval_fieldLoad_some hpv]; dsimp only
      rw [Function.update_self, hv2_eq]; exact (hs.2.2.1 x hx1 hx).2.2
    rcases exec_seq_assign_elim hbr with ⟨_, v4, _, _, hv4, h3, _⟩
    rcases exec_seq_assign_elim h3 with ⟨_, gpv, _, _, hgpv, h4, _⟩
    rcases exec_seq_assign_elim h4 with ⟨_, v6, _, _, _, h5, _⟩
    rcases exec_seq_store_elim h5 with ⟨_, apx, vpx, _, _, hapx, _, h6, _⟩
    rcases exec_seq_store_elim h6 with ⟨_, app, vpp, _, _, happ, _, h7, _⟩
    have hv4_eq : v4 = nb + NODE_STRIDE * pv := by
      rcases eval_nodePtr_some hv4 with ⟨rfl, _⟩
      simp [Function.update_of_ne, h0]
    have hgpv_le : gpv ≤ cap := by
      rw [eval_fieldLoad_some hgpv]; dsimp only
      rw [Function.update_self, hv4_eq]; exact (hs.2.2.1 pv hpv_1 hpv_le).2.2
    have hapx_eq : apx = nb + NODE_STRIDE * x + OFF_PPAR := by
      rcases eval_fieldAddr_some hapx with ⟨rfl, _⟩
      simp [Function.update_of_ne, hv2_eq]
    have happ_eq : app = nb + NODE_STRIDE * pv + OFF_PPAR := by
      rcases eval_fieldAddr_some happ with ⟨rfl, _⟩
      simp [Function.update_of_ne, hv4_eq]
    have hs1 : SafeMem mem0 nb cap hp0 (Function.update (Function.update st.mem apx vpx) app vpp) := by
      rw [hapx_eq, happ_eq]
      exact (hs.update_nonStruct hnb harena hx1 hx (by decide) (by decide)
          (fun h => False.elim ((by decide : OFF_PPAR ∉ ptrOffs) h))).update_nonStruct
        hnb harena hpv_1 hpv_le (by decide) (by decide)
        (fun h => False.elim ((by decide : OFF_PPAR ∉ ptrOffs) h))
    rcases exec_seq_assign_elim h7 with ⟨_, v7i, _, _, _, h8, _⟩
    rcases exec_seq_assign_elim h8 with ⟨_, v8i, _, _, _, h9, _⟩
    have hch_nr : stmtNoRet (Stmt.cond (.reg 8)
        (Stmt.assign 9 (fieldLoadExpr 2 OFF_LEFT) ;;
         setChildAndParentStmt 4 OFF_RIGHT 9 3 10 ;;
         Stmt.store (fieldAddrExpr 2 OFF_LEFT) (.reg 3))
        (Stmt.assign 9 (fieldLoadExpr 2 OFF_RIGHT) ;;
         setChildAndParentStmt 4 OFF_LEFT 9 3 10 ;;
         Stmt.store (fieldAddrExpr 2 OFF_RIGHT) (.reg 3))) = true := by
      simp [stmtNoRet, stmtNoRet_setChildAndParent]
    rcases exec_seq_of_noRet hch_nr h9 with ⟨_, st1, _, _, _, hch_ex, h10, _⟩
    have hpre_r : ∀ r ∈ [0, 1, 2, 3, 4, 5],
        Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update st.regs 2 v2) 3 pv) 4 v4) 5 gpv)
          6 v6) 7 v7i) 8 v8i r =
        if r = 0 then nb else if r = 1 then x else if r = 2 then nb + NODE_STRIDE * x else
        if r = 3 then pv else if r = 4 then nb + NODE_STRIDE * pv else gpv := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Function.update_of_ne, h0, h1, hv2_eq, hv4_eq]
    have hch_ok : SafeMem mem0 nb cap hp0 st1.mem ∧
        (∀ r ∈ [0, 1, 2, 3, 4, 5], st1.regs r =
          if r = 0 then nb else if r = 1 then x else if r = 2 then nb + NODE_STRIDE * x else
          if r = 3 then pv else if r = 4 then nb + NODE_STRIDE * pv else gpv) := by
      have hr0' := hpre_r 0 (by simp)
      have hr2' := hpre_r 2 (by simp)
      have hr3' := hpre_r 3 (by simp)
      have hr4' := hpre_r 4 (by simp)
      simp only at hr0' hr2' hr3' hr4'
      have run_branch : ∀ {co1 co2 fu st0 st_end c0},
          co1 = OFF_LEFT ∨ co1 = OFF_RIGHT → co2 = OFF_LEFT ∨ co2 = OFF_RIGHT →
          exec w p ω fu (Stmt.assign 9 (fieldLoadExpr 2 co1) ;;
            setChildAndParentStmt 4 co2 9 3 10 ;;
            Stmt.store (fieldAddrExpr 2 co1) (.reg 3)) st0 = some (.normal, st_end, c0) →
          SafeMem mem0 nb cap hp0 st0.mem →
          (∀ r ∈ [0, 1, 2, 3, 4, 5], st0.regs r =
            if r = 0 then nb else if r = 1 then x else if r = 2 then nb + NODE_STRIDE * x else
            if r = 3 then pv else if r = 4 then nb + NODE_STRIDE * pv else gpv) →
          SafeMem mem0 nb cap hp0 st_end.mem ∧
            (∀ r ∈ [0, 1, 2, 3, 4, 5], st_end.regs r =
              if r = 0 then nb else if r = 1 then x else if r = 2 then nb + NODE_STRIDE * x else
              if r = 3 then pv else if r = 4 then nb + NODE_STRIDE * pv else gpv) := by
        intro co1 co2 fu st0 st_end c0 hco1 hco2 hbr_b hs0 hr_b
        rcases exec_seq_assign_elim hbr_b with ⟨_, bv, _, _, hbv, hsc_ex, _⟩
        rcases exec_seq_of_noRet stmtNoRet_setChildAndParent hsc_ex with ⟨_, st_sc, _, _, _, hsc, hst_f, _⟩
        have hbv_le : bv ≤ cap := by
          rw [eval_fieldLoad_some hbv, hr_b 2 (by simp)]
          rcases hco1 with rfl | rfl
          · exact (hs0.2.2.1 x hx1 hx).1
          · exact (hs0.2.2.1 x hx1 hx).2.1
        rcases setChildAndParent_safeExec hnb harena hco2 (by decide) hpv_1 hpv_le hbv_le
          (st := { st0 with regs := Function.update st0.regs 9 bv })
          (by dsimp only; rw [Function.update_of_ne (by decide), hr_b 0 (by simp)]; simp)
          (by dsimp only; rw [Function.update_of_ne (by decide), hr_b 4 (by simp)]; simp)
          (by dsimp only; rw [Function.update_of_ne (by decide), hr_b 3 (by simp)]; simp)
          (by simp) (by simpa using hs0) hsc with ⟨_, hs_sc, hregs_sc⟩
        rcases exec_store_iff.1 hst_f with ⟨_, af, vf, _, haf, hvf, _, rfl, rfl, _⟩
        have hr_sc : ∀ r ∈ [0, 1, 2, 3, 4, 5], st_sc.regs r = st0.regs r := fun r hr => by
          have hne10 : r ≠ 10 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          have hne9 : r ≠ 9 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          rw [hregs_sc r hne10]; dsimp only; rw [Function.update_of_ne hne9]
        have haf_eq : af = nb + NODE_STRIDE * x + co1 := by
          rcases eval_fieldAddr_some haf with ⟨rfl, _⟩
          rw [hr_sc 2 (by simp), hr_b 2 (by simp)]; simp
        have hvf_eq : vf = pv := by
          simp only [Expr.eval] at hvf; cases hvf
          rw [hr_sc 3 (by simp), hr_b 3 (by simp)]; simp
        have hco1_lt : co1 < NODE_STRIDE := by rcases hco1 with rfl | rfl <;> decide
        have hco1_np : co1 ∉ ptrOffs := by rcases hco1 with rfl | rfl <;> decide
        have hs_end : SafeMem mem0 nb cap hp0 (Function.update st_sc.mem af vf) := by
          rw [haf_eq, hvf_eq]
          exact hs_sc.update_field hnb harena hx1 hx hco1_lt (fun _ => hpv_le)
            (fun h => False.elim (hco1_np h))
        exact ⟨hs_end, fun r hr => by dsimp only; rw [hr_sc r hr, hr_b r hr]⟩
      rcases exec_cond_elim hch_ex with ⟨_, v8, _, _, _, hbr8, _⟩
      by_cases hv8_0 : v8 = 0
      · simp only [hv8_0, ↓reduceIte] at hbr8
        exact run_branch (Or.inr rfl) (Or.inl rfl) hbr8 (by simpa using hs1) hpre_r
      · simp only [hv8_0, ↓reduceIte] at hbr8
        exact run_branch (Or.inl rfl) (Or.inr rfl) hbr8 (by simpa using hs1) hpre_r
    rcases hch_ok with ⟨hs2, hr1⟩
    rcases exec_seq_store_elim h10 with ⟨_, app2, vpp2, _, _, happ2, hvpp2, h11, _⟩
    rcases exec_seq_store_elim h11 with ⟨_, apx2, vpx2, _, _, hapx2, hvpx2, h12, _⟩
    have happ2_eq : app2 = nb + NODE_STRIDE * pv + OFF_PARENT := by
      rcases eval_fieldAddr_some happ2 with ⟨rfl, _⟩; rw [hr1 4 (by simp)]; simp
    have hvpp2_eq : vpp2 = x := by
      simp only [Expr.eval] at hvpp2; cases hvpp2; rw [hr1 1 (by simp)]; simp
    have hapx2_eq : apx2 = nb + NODE_STRIDE * x + OFF_PARENT := by
      rcases eval_fieldAddr_some hapx2 with ⟨rfl, _⟩; rw [hr1 2 (by simp)]; simp
    have hvpx2_eq : vpx2 = gpv := by
      simp only [Expr.eval] at hvpx2; cases hvpx2; rw [hr1 5 (by simp)]; simp
    have hs3 : SafeMem mem0 nb cap hp0 (Function.update (Function.update st1.mem app2 vpp2) apx2 vpx2) := by
      rw [happ2_eq, hvpp2_eq, hapx2_eq, hvpx2_eq]
      exact (hs2.update_field hnb harena hpv_1 hpv_le (by decide) (fun _ => hx)
          (fun h => False.elim ((by decide : OFF_PARENT ∉ ptrOffs) h))).update_field
        hnb harena hx1 hx (by decide) (fun _ => hgpv_le)
        (fun h => False.elim ((by decide : OFF_PARENT ∉ ptrOffs) h))
    have hgp_nr : stmtNoRet (Stmt.cond (.reg 5)
        (Stmt.assign 10 (nodePtrExpr 0 5) ;;
         Stmt.assign 11 (fieldLoadExpr 10 OFF_LEFT) ;;
         Stmt.cond (.bin .eq (.reg 3) (.reg 11))
           (Stmt.store (fieldAddrExpr 10 OFF_LEFT) (.reg 1))
           (Stmt.store (fieldAddrExpr 10 OFF_RIGHT) (.reg 1))) Stmt.nop) = true := by
      simp [stmtNoRet]
    rcases exec_seq_of_noRet hgp_nr h12 with ⟨_, st2, _, _, _, hgp_ex, h13, _⟩
    have hgp_ok : SafeMem mem0 nb cap hp0 st2.mem ∧ st2.regs 0 = nb ∧ st2.regs 1 = x ∧ st2.regs 3 = pv := by
      rcases exec_cond_elim hgp_ex with ⟨_, v5, _, _, he5, hbr5, _⟩
      simp only [Expr.eval] at he5; cases he5
      rw [show st1.regs 5 = gpv from by rw [hr1 5 (by simp)]; simp] at hbr5
      by_cases hgp0 : gpv = 0
      · simp only [hgp0, ↓reduceIte] at hbr5
        rcases exec_nop_iff.1 hbr5 with ⟨_, _, rfl, _⟩
        exact ⟨hs3, by rw [hr1 0 (by simp)]; simp, by rw [hr1 1 (by simp)]; simp,
          by rw [hr1 3 (by simp)]; simp⟩
      · simp only [hgp0, ↓reduceIte] at hbr5
        have hgp1 : 1 ≤ gpv := Nat.pos_of_ne_zero hgp0
        rcases exec_seq_assign_elim hbr5 with ⟨_, v10, _, _, hv10, hb2, _⟩
        rcases exec_seq_assign_elim hb2 with ⟨_, v11, _, _, _, hb3, _⟩
        have hv10_eq : v10 = nb + NODE_STRIDE * gpv := by
          rcases eval_nodePtr_some hv10 with ⟨rfl, _⟩
          dsimp only; rw [hr1 0 (by simp), hr1 5 (by simp)]; simp
        have hpr_gp : ∀ r ∈ [0, 1, 3, 10],
            Function.update (Function.update st1.regs 10 v10) 11 v11 r =
            if r = 0 then nb else if r = 1 then x else if r = 3 then pv else nb + NODE_STRIDE * gpv := fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · simp [Function.update_of_ne, hr1 0 (by simp)]
          · simp [Function.update_of_ne, hr1 1 (by simp)]
          · simp [Function.update_of_ne, hr1 3 (by simp)]
          · simp [Function.update_of_ne, hv10_eq]
        rcases exec_cond_elim hb3 with ⟨_, vcmp, _, _, _, hb4, _⟩
        let st_gp : State :=
          { mem := Function.update (Function.update st1.mem app2 vpp2) apx2 vpx2,
            regs := Function.update (Function.update st1.regs 10 v10) 11 v11,
            pos := st1.pos }
        have hstore_gp : ∀ {off fu c0}, off = OFF_LEFT ∨ off = OFF_RIGHT →
            exec w p ω fu (Stmt.store (fieldAddrExpr 10 off) (.reg 1)) st_gp = some (.normal, st2, c0) →
            SafeMem mem0 nb cap hp0 st2.mem ∧ st2.regs 0 = nb ∧ st2.regs 1 = x ∧ st2.regs 3 = pv := by
          intro off fu c0 hoff hst_g
          rcases exec_store_iff.1 hst_g with ⟨_, ag, vg, _, hag, hvg, _, hst2_eq, _⟩
          have hag_eq : ag = nb + NODE_STRIDE * gpv + off := by
            rcases eval_fieldAddr_some hag with ⟨rfl, _⟩
            have h10' := hpr_gp 10 (by simp)
            simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.reduceEqDiff] at h10'
            exact congrArg (· + off) h10'
          have hvg_eq : vg = x := by
            simp only [Expr.eval] at hvg; cases hvg
            have h1' := hpr_gp 1 (by simp)
            simp only [↓reduceIte, Nat.reduceEqDiff] at h1'
            exact h1'
          have hoff_lt : off < NODE_STRIDE := by rcases hoff with rfl | rfl <;> decide
          have hoff_np : off ∉ ptrOffs := by rcases hoff with rfl | rfl <;> decide
          have hs_gfin : SafeMem mem0 nb cap hp0 (Function.update st_gp.mem ag vg) := by
            rw [hag_eq, hvg_eq]
            exact hs3.update_field hnb harena hgp1 hgpv_le hoff_lt (fun _ => hx)
              (fun h => False.elim (hoff_np h))
          rw [hst2_eq]
          refine ⟨by simpa [st_gp] using hs_gfin, ?_, ?_, ?_⟩
          · have h0' := hpr_gp 0 (by simp); simpa [st_gp] using h0'
          · have h1' := hpr_gp 1 (by simp); simpa [st_gp] using h1'
          · have h3' := hpr_gp 3 (by simp); simpa [st_gp] using h3'
        by_cases hvc0 : vcmp = 0
        · simp only [hvc0, ↓reduceIte] at hb4
          exact hstore_gp (Or.inr rfl) hb4
        · simp only [hvc0, ↓reduceIte] at hb4
          exact hstore_gp (Or.inl rfl) hb4
    rcases hgp_ok with ⟨hs4, hr2_0, hr2_1, hr2_3⟩
    rcases exec_seq_call_elim h13 with ⟨_, _, vs1, bp1, _, st_p1, _, _, _, _, hvs1, hpb1, hrec1, h14, _⟩
    have hbp1_eq : bp1 = pullBody sp := Option.some.inj (hpb1.symm.trans hpull)
    subst hbp1_eq
    rcases evalArgs_cons.1 hvs1 with ⟨a0, r1', ha0, hr1', rfl⟩
    rcases evalArgs_cons.1 hr1' with ⟨a1, nil1, ha1, hnil1, rfl⟩
    rw [evalArgs_nil.1 hnil1] at *
    have ha0_eq : a0 = nb := by simp [Expr.eval, hr2_0] at ha0; exact ha0.symm
    have ha1_eq : a1 = pv := by simp [Expr.eval, hr2_3] at ha1; exact ha1.symm
    let st_pull1 : State := { st2 with regs := fun i => [a0, a1].getD i 0 }
    rcases pull_safeExec hp_prog hnb harena hz0 (st := st_pull1) hpv_le
      (by simp [st_pull1, ha0_eq]) (by simp [st_pull1, ha1_eq])
      (by simpa [st_pull1] using hs4) hrec1 with ⟨_, hs5⟩
    rcases exec_seq_call_elim h14 with ⟨_, _, vs2, bp2, _, _, _, _, _, _, hvs2, hpb2, hrec2, hret, _⟩
    have hbp2_eq : bp2 = pullBody sp := Option.some.inj (hpb2.symm.trans hpull)
    subst hbp2_eq
    rcases evalArgs_cons.1 hvs2 with ⟨b0, rb1, hb0, hrb1, rfl⟩
    rcases evalArgs_cons.1 hrb1 with ⟨b1, nil2, hb1, hnil2, rfl⟩
    rw [evalArgs_nil.1 hnil2] at *
    have hb0_eq : b0 = nb := by
      simp [Expr.eval, Function.update_of_ne, hr2_0] at hb0; exact hb0.symm
    have hb1_eq : b1 = x := by
      simp [Expr.eval, Function.update_of_ne, hr2_1] at hb1; exact hb1.symm
    let st_pull2 : State := { st_p1 with regs := fun i => [b0, b1].getD i 0 }
    rcases pull_safeExec hp_prog hnb harena hz0 (st := st_pull2) hx
      (by simp [st_pull2, hb0_eq]) (by simp [st_pull2, hb1_eq]) hs5 hrec2 with ⟨_, hs6⟩
    rcases exec_ret_iff.1 hret with ⟨_, v0, _, hv0, rfl, rfl, _⟩
    simp [Expr.eval] at hv0; cases hv0
    exact ⟨rfl, by simpa using hs6⟩

private theorem splayLoop_safeExec {w h spBase : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp_prog : p.HasAt spBase (splayBodies (SplayProcs.atBase spBase) h))
    {mem0 : ℕ → ℕ} {nb cap hp0 : ℕ} (hnb : 3 ≤ nb) (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    (hz0 : SlotZeroOk mem0 nb) {x : ℕ} (hx1 : 1 ≤ x) (hx2 : x ≤ cap)
    (fuel : ℕ) :
    ∀ st st' o c,
      st.regs 0 = nb → st.regs 1 = x → st.regs 3 = nb + NODE_STRIDE * x → st.regs 4 ≤ cap →
      SafeMem mem0 nb cap hp0 st.mem →
      exec w p ω fuel (Stmt.loop (.reg 4)
        (Stmt.assign 5 (nodePtrExpr 0 4) ;;
         Stmt.assign 6 (fieldLoadExpr 5 OFF_PARENT) ;;
         Stmt.cond (.reg 6)
           (Stmt.assign 7 (nodePtrExpr 0 6) ;;
            Stmt.assign 8 (fieldLoadExpr 7 OFF_LEFT) ;;
            Stmt.assign 9 (fieldLoadExpr 5 OFF_LEFT) ;;
            Stmt.assign 10 (.bin .eq (.reg 4) (.reg 8)) ;;
            Stmt.assign 11 (.bin .eq (.reg 1) (.reg 9)) ;;
            Stmt.cond (.bin .eq (.reg 10) (.reg 11))
              (Stmt.call 12 (SplayProcs.atBase spBase).rotate [.reg 0, .reg 4] ;;
               Stmt.call 12 (SplayProcs.atBase spBase).rotate [.reg 0, .reg 1])
              (Stmt.call 12 (SplayProcs.atBase spBase).rotate [.reg 0, .reg 1] ;;
               Stmt.call 12 (SplayProcs.atBase spBase).rotate [.reg 0, .reg 1]))
           (Stmt.call 12 (SplayProcs.atBase spBase).rotate [.reg 0, .reg 1]) ;;
         Stmt.assign 4 (fieldLoadExpr 3 OFF_PARENT))) st = some (o, st', c) →
      o = .normal ∧ SafeMem mem0 nb cap hp0 st'.mem ∧
      (∀ r, r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 →
        st'.regs r = st.regs r) := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro st st' o c h0 h1 h3 h4 hs hex
      rcases splayBodies_procs_eq hp_prog with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrot, _⟩
      let sp := SplayProcs.atBase spBase
      rcases exec_loop_elim hex with ⟨f, v4, hf, he4, hbr⟩
      simp only [Expr.eval] at he4; cases he4
      rcases hbr with ⟨hv4_0, rfl, rfl, _⟩ | ⟨_, u, c1, hb, _, _⟩ | ⟨hv4_ne, st1, c1, c2, hb, hl, _⟩
      · exact ⟨rfl, hs, fun _ _ _ _ _ _ _ _ _ _ => rfl⟩
      · exact Outcome.noConfusion (exec_noRet_normal f _ st _ st' c1 (by simp [stmtNoRet]) hb)
      · have h4_1 : 1 ≤ st.regs 4 := Nat.pos_of_ne_zero hv4_ne
        rcases exec_seq_assign_elim hb with ⟨_, v5, _, _, hv5, hb2, _⟩
        rcases exec_seq_assign_elim hb2 with ⟨_, v6, _, _, hv6, hb3, _⟩
        rcases exec_seq_of_noRet (by simp [stmtNoRet]) hb3 with ⟨_, st_m, _, _, _, hcond_ex, hb4, _⟩
        have hv5_eq : v5 = nb + NODE_STRIDE * st.regs 4 := by
          rcases eval_nodePtr_some hv5 with ⟨rfl, _⟩; rw [h0]
        have hv6_le : v6 ≤ cap := by
          rw [eval_fieldLoad_some hv6]; dsimp only
          rw [Function.update_self, hv5_eq]; exact (hs.2.2.1 _ h4_1 h4).2.2
        have call_rot : ∀ {fu st_c st_d c_d rNode},
            st_c.regs 0 = nb → st_c.regs rNode ≤ cap →
            exec w p ω fu (Stmt.call 12 sp.rotate [.reg 0, .reg rNode]) st_c =
              some (.normal, st_d, c_d) →
            SafeMem mem0 nb cap hp0 st_c.mem →
            SafeMem mem0 nb cap hp0 st_d.mem ∧ (∀ r, r ≠ 12 → st_d.regs r = st_c.regs r) := by
          intro fu st_c st_d c_d rn hr0 hrn hex_r hs_c
          rcases exec_call_elim hex_r with ⟨_, vs, body, _, _, _, _, hvs, hpb, hrec, _, rfl, _⟩
          have hb_eq : body = rotateBody sp := Option.some.inj (hpb.symm.trans hrot)
          subst hb_eq
          rcases evalArgs_cons.1 hvs with ⟨a0, ar, ha0, har, rfl⟩
          rcases evalArgs_cons.1 har with ⟨a1, anil, ha1, hnil, rfl⟩
          rw [evalArgs_nil.1 hnil] at *
          have ha0_eq : a0 = nb := by simp [Expr.eval, hr0] at ha0; exact ha0.symm
          have ha1_eq : a1 = st_c.regs rn := by simp [Expr.eval] at ha1; exact ha1.symm
          let st_rot : State := { st_c with regs := fun i => [a0, a1].getD i 0 }
          rcases rotate_safeExec hp_prog hnb harena hz0 (st := st_rot) (ha1_eq ▸ hrn)
            (by simp [st_rot, ha0_eq]) (by simp [st_rot, ha1_eq])
            (by simpa [st_rot] using hs_c) hrec with ⟨_, hs_d⟩
          exact ⟨hs_d, fun r hr12 => by dsimp only; exact Function.update_of_ne hr12 _ _⟩
        have hcond_ok : SafeMem mem0 nb cap hp0 st_m.mem ∧
            (∀ r, r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 →
              st_m.regs r = st.regs r) := by
          have hr_init : ∀ r, r ≠ 5 → r ≠ 6 →
              Function.update (Function.update st.regs 5 v5) 6 v6 r = st.regs r :=
            fun r hr5 hr6 => by rw [Function.update_of_ne hr6, Function.update_of_ne hr5]
          rcases exec_cond_elim hcond_ex with ⟨_, vc6, _, _, _, hbr6, _⟩
          by_cases hvc6_0 : vc6 = 0
          · simp only [hvc6_0, ↓reduceIte] at hbr6
            rcases call_rot (by dsimp only; rw [hr_init 0 (by decide) (by decide), h0])
              (by dsimp only; rw [hr_init 1 (by decide) (by decide), h1]; exact hx2) hbr6
              (by simpa using hs) with ⟨hs_d, hregs_d⟩
            exact ⟨hs_d, fun r _ hr5 hr6 _ _ _ _ _ hr12 => by
              rw [hregs_d r hr12]; dsimp only; rw [hr_init r hr5 hr6]⟩
          · simp only [hvc6_0, ↓reduceIte] at hbr6
            rcases exec_seq_assign_elim hbr6 with ⟨_, v7, _, _, _, hb_a, _⟩
            rcases exec_seq_assign_elim hb_a with ⟨_, v8, _, _, _, hb_b, _⟩
            rcases exec_seq_assign_elim hb_b with ⟨_, v9, _, _, _, hb_c, _⟩
            rcases exec_seq_assign_elim hb_c with ⟨_, v10, _, _, _, hb_d, _⟩
            rcases exec_seq_assign_elim hb_d with ⟨_, v11, _, _, _, hb_e, _⟩
            rcases exec_cond_elim hb_e with ⟨_, vc, _, _, _, hbr_rot, _⟩
            have hr_pre : ∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
                Function.update (Function.update (Function.update (Function.update (Function.update
                  (Function.update (Function.update st.regs 5 v5) 6 v6) 7 v7) 8 v8) 9 v9)
                  10 v10) 11 v11 r = st.regs r :=
              fun r hr5 hr6 hr7 hr8 hr9 hr10 hr11 => by
                rw [Function.update_of_ne hr11, Function.update_of_ne hr10,
                  Function.update_of_ne hr9, Function.update_of_ne hr8, Function.update_of_ne hr7,
                  Function.update_of_ne hr6, Function.update_of_ne hr5]
            by_cases hvrot0 : vc = 0
            · simp only [hvrot0, ↓reduceIte] at hbr_rot
              rcases exec_seq_of_noRet (by simp [stmtNoRet]) hbr_rot with
                ⟨_, st_mid, _, _, _, hrc1, hrc2, _⟩
              rcases call_rot
                (by dsimp only; rw [hr_pre 0 (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide), h0])
                (by dsimp only; rw [hr_pre 1 (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide), h1]; exact hx2) hrc1 (by simpa using hs) with
                ⟨hs_mid, hregs_mid⟩
              rcases call_rot
                (by rw [hregs_mid 0 (by decide)]; dsimp only; rw [hr_pre 0 (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide), h0])
                (by rw [hregs_mid 1 (by decide)]; dsimp only; rw [hr_pre 1 (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide), h1]; exact hx2)
                hrc2 hs_mid with ⟨hs_end, hregs_end⟩
              exact ⟨hs_end, fun r _ hr5 hr6 hr7 hr8 hr9 hr10 hr11 hr12 => by
                rw [hregs_end r hr12, hregs_mid r hr12]; dsimp only
                rw [hr_pre r hr5 hr6 hr7 hr8 hr9 hr10 hr11]⟩
            · simp only [hvrot0, ↓reduceIte] at hbr_rot
              rcases exec_seq_of_noRet (by simp [stmtNoRet]) hbr_rot with
                ⟨_, st_mid, _, _, _, hrc1, hrc2, _⟩
              rcases call_rot
                (by dsimp only; rw [hr_pre 0 (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide), h0])
                (by dsimp only; rw [hr_pre 4 (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide)]; exact h4) hrc1 (by simpa using hs) with
                ⟨hs_mid, hregs_mid⟩
              rcases call_rot
                (by rw [hregs_mid 0 (by decide)]; dsimp only; rw [hr_pre 0 (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide), h0])
                (by rw [hregs_mid 1 (by decide)]; dsimp only; rw [hr_pre 1 (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide), h1]; exact hx2)
                hrc2 hs_mid with ⟨hs_end, hregs_end⟩
              exact ⟨hs_end, fun r _ hr5 hr6 hr7 hr8 hr9 hr10 hr11 hr12 => by
                rw [hregs_end r hr12, hregs_mid r hr12]; dsimp only
                rw [hr_pre r hr5 hr6 hr7 hr8 hr9 hr10 hr11]⟩
        rcases hcond_ok with ⟨hs_m, hregs_m⟩
        rcases exec_assign_iff.1 hb4 with ⟨_, v4n, _, hv4n, _, rfl, _⟩
        have hrm0 : st_m.regs 0 = st.regs 0 :=
          hregs_m 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have hrm1 : st_m.regs 1 = st.regs 1 :=
          hregs_m 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have hrm3 : st_m.regs 3 = st.regs 3 :=
          hregs_m 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have hv4n_le : v4n ≤ cap := by
          rw [eval_fieldLoad_some hv4n, hrm3, h3]
          exact (hs_m.2.2.1 x hx1 hx2).2.2
        rcases ih f (by omega) { st_m with regs := Function.update st_m.regs 4 v4n } st' o c2
          (by simp [Function.update_of_ne, hrm0, h0])
          (by simp [Function.update_of_ne, hrm1, h1])
          (by simp [Function.update_of_ne, hrm3, h3])
          (by simpa [Function.update_self] using hv4n_le) (by simpa using hs_m) hl with
          ⟨ho, hs_fin, hregs_fin⟩
        refine ⟨ho, hs_fin, fun r hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11 hr12 => ?_⟩
        rw [hregs_fin r hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11 hr12]
        dsimp only; rw [Function.update_of_ne hr4]
        exact hregs_m r hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11 hr12

theorem splay_safeExec {w h spBase : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp_prog : p.HasAt spBase (splayBodies (SplayProcs.atBase spBase) h))
    {mem0 : ℕ → ℕ} {nb cap hp0 : ℕ} (hnb : 3 ≤ nb) (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    (hz0 : SlotZeroOk mem0 nb)
    {fuel : ℕ} {st st' : State} {o : Outcome} {c x : ℕ}
    (hx : x ≤ cap) (h0 : st.regs 0 = nb) (h1 : st.regs 1 = x)
    (hs : SafeMem mem0 nb cap hp0 st.mem)
    (hex : exec w p ω fuel (splayBody (SplayProcs.atBase spBase)) st = some (o, st', c)) :
    o = .returned x ∧ SafeMem mem0 nb cap hp0 st'.mem := by
  rcases splayBodies_procs_eq hp_prog with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpp, _, _⟩
  let sp := SplayProcs.atBase spBase
  dsimp only [splayBody] at hex
  rcases exec_cond_elim hex with ⟨_, vx, _, _, hvx, hbr1, _⟩
  simp only [Expr.eval, h1] at hvx; cases hvx
  by_cases hx0 : x = 0
  · simp only [hx0, ↓reduceIte] at hbr1
    rcases exec_ret_iff.1 hbr1 with ⟨_, v0, _, hv0, rfl, rfl, _⟩
    simp [Expr.eval] at hv0; cases hv0; exact ⟨by rw [hx0], hs⟩
  · simp only [hx0, ↓reduceIte] at hbr1
    have hx1 : 1 ≤ x := Nat.pos_of_ne_zero hx0
    rcases exec_seq_call_elim hbr1 with ⟨_, _, vs, bp, o1_pp, st1_pp, _, _, _, _, hvs, hpb, hrec, hrest, _⟩
    have hbp_eq : bp = pushPathBody sp := Option.some.inj (hpb.symm.trans hpp)
    subst hbp_eq
    rcases evalArgs_cons.1 hvs with ⟨a0, ar, ha0, har, rfl⟩
    rcases evalArgs_cons.1 har with ⟨a1, anil, ha1, hnil, rfl⟩
    rw [evalArgs_nil.1 hnil] at *
    have ha0_eq : a0 = nb := by simp [Expr.eval, h0] at ha0; exact ha0.symm
    have ha1_eq : a1 = x := by simp [Expr.eval, h1] at ha1; exact ha1.symm
    let st_pp : State := { st with regs := fun i => [a0, a1].getD i 0 }
    rcases pushPath_safeExec hp_prog hnb harena _ st_pp _ _ _ x hx
      (by simp [st_pp, ha0_eq]) (by simp [st_pp, ha1_eq]) (by simpa [st_pp] using hs) hrec with
      ⟨_, hs1⟩
    rcases exec_seq_assign_elim hrest with ⟨_, v3, _, _, hv3, hrest2, _⟩
    rcases exec_seq_assign_elim hrest2 with ⟨_, v4, _, _, hv4, hloop_seq, _⟩
    have hv3_eq : v3 = nb + NODE_STRIDE * x := by
      rcases eval_nodePtr_some hv3 with ⟨rfl, _⟩
      simp [Function.update_of_ne, h0, h1]
    have hv4_le : v4 ≤ cap := by
      rw [eval_fieldLoad_some hv4]; dsimp only
      rw [Function.update_self, hv3_eq]; exact (hs1.2.2.1 x hx1 hx).2.2
    rcases exec_seq_of_noRet (by simp [stmtNoRet]) hloop_seq with ⟨_, st2, _, _, _, hloop_ex, hret, _⟩
    let rs_loop := Function.update (Function.update
      (Function.update st.regs 2 (Outcome.rec 0 (fun v => v) o1_pp)) 3 v3) 4 v4
    let st_loop : State := { st1_pp with regs := rs_loop }
    rcases splayLoop_safeExec hp_prog hnb harena hz0 hx1 hx _ st_loop _ _ _
      (by dsimp only [st_loop, rs_loop]; simp [Function.update_of_ne, h0])
      (by dsimp only [st_loop, rs_loop]; simp [Function.update_of_ne, h1])
      (by dsimp only [st_loop, rs_loop]; simp [Function.update_of_ne, hv3_eq])
      (by dsimp only [st_loop, rs_loop]; simpa [Function.update_self] using hv4_le)
      (by simpa [st_loop] using hs1) hloop_ex with ⟨_, hs2, hpres2⟩
    rcases exec_ret_iff.1 hret with ⟨_, vret, _, hvret, rfl, rfl, _⟩
    have hvret_eq : vret = x := by
      simp only [Expr.eval] at hvret; cases hvret
      rw [hpres2 1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      dsimp only [st_loop, rs_loop]; simp [Function.update_of_ne, h1]
    exact ⟨by rw [hvret_eq], by simpa using hs2⟩

end SplayProcSafety

section DeterminismAndPtrFoot

theorem splayBodies_noRand (sp : SplayProcs) (h : ℕ) :
    ∀ s ∈ splayBodies sp h, s.NoRand := by
  intro s hs
  dsimp only [splayBodies] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (((((h0 | h1) | h2) | h3) | h4) | h5) | h6
  · simp [zeroModule] at h0; subst h0; exact zeroBody_noRand
  · simp [copyModule] at h1; subst h1; exact copyBody_noRand
  · exact addModule_noRand _ h s h2
  · exact subtractModule_noRand _ h s h3
  · exact lessModule_noRand _ h s h4
  · simp [equalModule] at h5; subst h5; exact equalBody_noRand _
  · rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [revNodeBody, applyTagBody, pushDownBody, pullBody, pushPathBody, rotateBody,
      splayBody, swapFieldsStmt, shiftPtrStmt, addOptPtrStmt, combineNumAggStmt, pullMinNumStmt,
      setChildAndParentStmt, Stmt.NoRand]

theorem treeMemMatch_ptr_bounds {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ}
    {t : AuxTree} {p pp u off : ℕ}
    (ht : TreeMemMatch w h L mem nb cap t p pp) (hu : u ∈ t.toList) (hoff : off ∈ ptrOffs) :
    let ptr := nodeField mem nb u off
    ptr = 0 ∨ (nb + NODE_STRIDE * (cap + 1) ≤ ptr ∧ ptr + L ≤ mem (nb - 1)) := by
  induction t generalizing p pp with
  | leaf => simp [AuxTree.toList] at hu
  | node x l r ihl ihr =>
      dsimp only [TreeMemMatch] at ht
      rcases ht with ⟨_, _, _, _, _, _, _, _, hhe, _, _, hht, _, _, _, _, hhe1, hhe0, hcf, hcb, hht1, hht0,
          hmh1, _, hm1, hm0, _, hl, hr⟩
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
      rcases hu with (hul | rfl) | hur
      · exact ihl hl hul
      · rcases (by simpa [ptrOffs] using hoff :
          off = OFF_FLOW_PTR ∨ off = OFF_AF_PTR ∨ off = OFF_AB_PTR ∨ off = OFF_COST_FWD ∨
          off = OFF_COST_BWD ∨ off = OFF_CSUM_FWD ∨ off = OFF_CSUM_BWD ∨ off = OFF_TAG_PTR ∨
          off = OFF_MIN1_VAL ∨ off = OFF_MIN2_VAL) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · by_cases hhe_eq : nodeField mem nb u OFF_HASE = 1
          · exact Or.inr ⟨(hhe1 hhe_eq).1.2.1, (hhe1 hhe_eq).1.2.2.1⟩
          · exact Or.inl (hhe0 (by omega)).2.1
        · by_cases hhe_eq : nodeField mem nb u OFF_HASE = 1
          · exact Or.inr ⟨(hhe1 hhe_eq).2.1.2.1, (hhe1 hhe_eq).2.1.2.2.1⟩
          · exact Or.inl (hhe0 (by omega)).2.2.1
        · by_cases hhe_eq : nodeField mem nb u OFF_HASE = 1
          · exact Or.inr ⟨(hhe1 hhe_eq).2.2.1.2.1, (hhe1 hhe_eq).2.2.1.2.2.1⟩
          · exact Or.inl (hhe0 (by omega)).2.2.2.1
        · by_cases hhe_eq : nodeField mem nb u OFF_HASE = 1
          · exact Or.inr ⟨(hhe1 hhe_eq).2.2.2.1.2.1, (hhe1 hhe_eq).2.2.2.1.2.2.1⟩
          · exact Or.inl (hhe0 (by omega)).2.2.2.2.1
        · by_cases hhe_eq : nodeField mem nb u OFF_HASE = 1
          · exact Or.inr ⟨(hhe1 hhe_eq).2.2.2.2.1.2.1, (hhe1 hhe_eq).2.2.2.2.1.2.2.1⟩
          · exact Or.inl (hhe0 (by omega)).2.2.2.2.2
        · rcases hcf with h0 | ⟨h1, h2, _⟩
          · exact Or.inl h0
          · exact Or.inr ⟨h1, h2⟩
        · rcases hcb with h0 | ⟨h1, h2, _⟩
          · exact Or.inl h0
          · exact Or.inr ⟨h1, h2⟩
        · by_cases hht_eq : nodeField mem nb u OFF_HAS_TAG = 1
          · exact Or.inr ⟨(hht1 hht_eq).1.2.1, (hht1 hht_eq).1.2.2.1⟩
          · exact Or.inl (hht0 (by omega)).1
        · by_cases hm_eq : nodeField mem nb u OFF_MIN1_HAS = 1
          · exact Or.inr ⟨(hm1 hm_eq).1.2.1, (hm1 hm_eq).1.2.2.1⟩
          · exact Or.inl (hm0 (by omega)).1
        · by_cases hm_eq : nodeField mem nb u OFF_MIN1_HAS = 1
          · exact Or.inr ⟨(hm1 hm_eq).2.1.2.1, (hm1 hm_eq).2.1.2.2.1⟩
          · exact Or.inl (hm0 (by omega)).2.2.2.1
      · exact ihr hr hur

theorem SafeMem.ptrFootOk_of_treeMemMatch {w h L b hp0 hp_caller : ℕ}
    {mem0 mem : ℕ → ℕ} {x0 x1 : LctConc}
    (hx_n : x1.n = x0.n)
    (hs : SafeMem mem0 (lctNodesBase b) (lctCap x0.n) hp0 mem)
    (hz0 : SlotZeroOk mem0 (lctNodesBase b))
    (hpf0 : PtrFootOk b mem0 x0 L)
    (hperm : (x1.trees.flatMap AuxTree.toList).Perm ((List.range (lctCap x0.n)).map (· + 1)))
    (htrees : ∀ t ∈ x1.trees, TreeMemMatch w h L mem (lctNodesBase b) (lctCap x0.n) t 0
      (nodeField mem (lctNodesBase b) t.rootId OFF_PPAR))
    (hcaller_le : hp_caller ≤ hp0)
    (_hhp_le : hp0 ≤ mem (lctNodesBase b - 1))
    (hreg_old : ∀ iv ∈ x0.regions, iv ∈ x1.regions)
    (hreg_new : (hp_caller, mem (lctNodesBase b - 1) + 1) ∈ x1.regions) :
    PtrFootOk b mem x1 L := by
  intro u hu off hoff
  rw [hx_n] at hu
  by_cases hu0 : u = 0
  · subst hu0
    have hlt := ptrOffs_lt_stride hoff
    have ha : lctNodesBase b ≤ lctNodesBase b + NODE_STRIDE * 0 + off ∧
        lctNodesBase b + NODE_STRIDE * 0 + off < lctNodesBase b + NODE_STRIDE := by omega
    have heq : nodeField mem (lctNodesBase b) 0 off = 0 := by
      change mem (lctNodesBase b + NODE_STRIDE * 0 + off) = 0
      rw [hs.2.1 _ (Or.inr (Or.inl ha))]
      simpa using hz0 off hlt
    exact Or.inl heq
  · have hu1 : 1 ≤ u := Nat.pos_of_ne_zero hu0
    have hum : u ∈ (x1.trees.flatMap AuxTree.toList) := by
      rw [hperm.mem_iff]
      exact List.mem_map.2 ⟨u - 1, List.mem_range.2 (by omega), by omega⟩
    rcases List.mem_flatMap.1 hum with ⟨t, ht, hut⟩
    have htb := treeMemMatch_ptr_bounds (htrees t ht) hut hoff
    rcases htb with hzero | ⟨harena_ptr, hptrL⟩
    · exact Or.inl hzero
    · refine Or.inr ⟨by dsimp only [lctArenaHi]; rw [hx_n]; exact harena_ptr, hptrL, fun a ha1 ha2 => ?_⟩
      have hpos_str : 1 ≤ NODE_STRIDE * (lctCap x0.n + 1) := Nat.mul_pos (by decide) (Nat.succ_pos _)
      rcases hs.2.2.2 u off hu1 hu hoff with h0 | hge0 | ⟨y, off', _, hy2, hoff', hy_eq⟩
      · rw [h0] at harena_ptr; omega
      · exact Or.inr ⟨(hp_caller, mem (lctNodesBase b - 1) + 1), hreg_new, by omega, by omega⟩
      · rw [hy_eq] at ha1 ha2 harena_ptr
        rcases hpf0 y hy2 off' hoff' with h0 | ⟨_, _, hfoot0⟩
        · rw [h0] at harena_ptr; omega
        · rcases hfoot0 a ha1 ha2 with ⟨h1, h2⟩ | ⟨iv, hiv, h1, h2⟩
          · exact Or.inl ⟨h1, by simpa [lctArenaHi, hx_n] using h2⟩
          · exact Or.inr ⟨iv, hreg_old iv hiv, h1, h2⟩

end DeterminismAndPtrFoot

end MinCostFlow.LinkCut.Prog
