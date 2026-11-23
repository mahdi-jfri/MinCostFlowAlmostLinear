module

public import MinCostFlow.SparseCore.Program.OrdStoreInsertSplice
import Mathlib.Tactic

/-!
# Order Store `insertBefore` Procedure

This file implements and verifies `ordInsertBeforeBody` on `[b, v, keyX, yWord]`, dispatching to
`insertSplice_runs` when the target `endOfKey (yWord - 1)` is in `ord v`, and falling back to
`insertBack_runs` otherwise.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

def ORD_INS_AMORT : ℕ := 14000

/-- `ordInsertBefore` on `[b, v, keyX, yWord]`: inserts `endOfKey keyX` before
`endOfKey (yWord - 1)` in `ord v` (or at the back when `yWord = 0` or the target is not in
`ord v`). -/
def ordInsertBeforeBody (allocProc splayRootProc joinProc : ℕ) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.const 4))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 7 (.const 0) ;;
  .cond (.reg 3)
    (.assign 8 (.bin .sub (.reg 3) (.const 1)) ;;
     .cond (.bin .lt (.reg 8) (.bin .add (.reg 6) (.reg 6)))
       (.assign 9 (.load (.bin .add (.reg 0) (.const 3))) ;;
        .assign 10 (.load (.bin .add (.reg 9) (.reg 8))) ;;
        .cond (.reg 10)
          (.call 11 splayRootProc [.reg 0, .reg 10] ;;
           .cond (.bin .eq (.reg 11) (.bin .add (.reg 1) (.const 1)))
             (.call 4 allocProc [.reg 0, .reg 2] ;;
              .assign 12 (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 4))) ;;
              .assign 13 (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 10))) ;;
              .assign 14 (.load (.reg 13)) ;;
              .store (.reg 12) (.reg 14) ;;
              .cond (.reg 14)
                (.store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 14))) (.const 2)) (.reg 4))
                .nop ;;
              .store (.bin .add (.reg 12) (.const 1)) (.reg 10) ;;
              .store (.bin .add (.reg 12) (.const 3)) (.reg 11) ;;
              .assign 15 (.load (.bin .add (.reg 13) (.const 4))) ;;
              .store (.bin .add (.reg 12) (.const 4)) (.bin .add (.reg 15) (.const 1)) ;;
              .store (.reg 13) (.const 0) ;;
              .store (.bin .add (.reg 13) (.const 2)) (.reg 4) ;;
              .store (.bin .add (.reg 13) (.const 3)) (.const 0) ;;
              .assign 16 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 14))) (.const 4))) ;;
              .store (.bin .add (.reg 13) (.const 4)) (.bin .sub (.reg 15) (.reg 16)) ;;
              .assign 17 (.load (.bin .add (.reg 0) (.const 2))) ;;
              .store (.bin .add (.reg 17) (.reg 1)) (.reg 4) ;;
              .assign 7 (.const 1))
             .nop)
          .nop)
       .nop)
    .nop ;;
  .cond (.bin .eq (.reg 7) (.const 0))
    (.call 4 allocProc [.reg 0, .reg 2] ;;
     .assign 8 (.load (.bin .add (.reg 0) (.const 2))) ;;
     .assign 9 (.load (.bin .add (.reg 8) (.reg 1))) ;;
     .call 10 joinProc [.reg 5, .reg 9, .reg 4, .bin .add (.reg 1) (.const 1)] ;;
     .store (.bin .add (.reg 8) (.reg 1)) (.reg 10))
    .nop ;;
  .ret (.const 0)

theorem ordInsertBeforeBody_noRand (aP srP jP : ℕ) :
    (ordInsertBeforeBody aP srP jP).NoRand := by
  simp [ordInsertBeforeBody, Stmt.NoRand]

theorem ordInsertBeforeBody_runs
    {w b v keyX yWord pos rotProc stepProc splayProc splayRootProc walkProc joinProc allocProc : ℕ}
    {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc))
    (hsplayRoot : p.procs[splayRootProc]? = some (ordSplayRootBody splayProc))
    (hwalk : p.procs[walkProc]? = some (ordWalkExtremeBody splayProc))
    (hjoin : p.procs[joinProc]? = some (ordJoinBody walkProc))
    (halloc : p.procs[allocProc]? = some ordAllocBody) (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {ord : ℕ → List End} {S : OrdStoreState} {heap : ℕ}
    (hinv : OrdInv ord S) (harena : OrdArenaAt b S mem) (hy_w : yWord < 2 ^ w)
    (huniq' : OrdUniqueWithin S.vCap S.eCap
      (applyOrdEdit ord (.insertBefore v (endOfKey keyX)
        (if yWord = 0 then none else some (endOfKey (yWord - 1))))))
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ heap)
    (hz : ZeroFrom mem heap) (hw : heap < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ o st' c, Runs w p ω (ordInsertBeforeBody allocProc splayRootProc joinProc)
        (startState [b, v, keyX, yWord] mem pos) o st' c ∧
      (∃ S' : OrdStoreState,
        OrdInv (applyOrdEdit ord (.insertBefore v (endOfKey keyX)
          (if yWord = 0 then none else some (endOfKey (yWord - 1))))) S' ∧
        OrdArenaAt b S' st'.mem ∧
        OrdFrame b S.vCap S.eCap heap mem st'.mem ∧
        S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
        c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' ≤
          ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + ORD_INS_AMORT * ordStoreLog S.eCap) := by
  have hlog : 1 ≤ ordStoreLog S.eCap := ordStoreLog_pos S.eCap
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ heap := hfoot
  obtain ⟨hv, hkX, hx_nmem⟩ := insertBefore_pre_facts huniq'
  have hunused_S : S.eNode keyX = 0 := by
    rcases hinv.eNode_spec keyX hkX with ⟨h0, _⟩ | ⟨w0, hw0, hmem, hval⟩
    · exact h0
    · exfalso; apply hx_nmem w0; rw [← hinv.list_eq w0 hw0]
      exact List.mem_map.mpr ⟨_, hmem, by rw [hval]⟩
  set yOpt : Option End := if yWord = 0 then none else some (endOfKey (yWord - 1)) with hyOpt
  set nb := ordNodesBase b S.vCap S.eCap with hnb
  set st0 : State := startState [b, v, keyX, yWord] mem pos
  have ha5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const 4)))) st0 .normal
      { st0 with regs := Function.update st0.regs 5 nb } _ :=
    runs_assign_iff.mpr ⟨nb, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st0, startState]))
      (Expr.eval_const (by omega)) (by omega)) harena.hdr_nodes, rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 5 nb }
  have ha6 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const 1)))) st1 .normal
      { st1 with regs := Function.update st1.regs 6 S.eCap } _ :=
    runs_assign_iff.mpr ⟨S.eCap, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1, st0, startState]))
      (Expr.eval_const (by omega)) (by omega)) harena.hdr_eCap, rfl, rfl, rfl⟩
  set st2 : State := { st1 with regs := Function.update st1.regs 6 S.eCap }
  have ha7 : Runs w p ω (.assign 7 (.const 0)) st2 .normal
      { st2 with regs := Function.update st2.regs 7 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set st3 : State := { st2 with regs := Function.update st2.regs 7 0 }
  set spliceCond : Stmt :=
    .cond (.reg 3)
      (.assign 8 (.bin .sub (.reg 3) (.const 1)) ;;
       .cond (.bin .lt (.reg 8) (.bin .add (.reg 6) (.reg 6)))
         (.assign 9 (.load (.bin .add (.reg 0) (.const 3))) ;;
          .assign 10 (.load (.bin .add (.reg 9) (.reg 8))) ;;
          .cond (.reg 10)
            (.call 11 splayRootProc [.reg 0, .reg 10] ;;
             .cond (.bin .eq (.reg 11) (.bin .add (.reg 1) (.const 1)))
               (.call 4 allocProc [.reg 0, .reg 2] ;;
                .assign 12 (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 4))) ;;
                .assign 13 (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 10))) ;;
                .assign 14 (.load (.reg 13)) ;;
                .store (.reg 12) (.reg 14) ;;
                .cond (.reg 14)
                  (.store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 14))) (.const 2)) (.reg 4))
                  .nop ;;
                .store (.bin .add (.reg 12) (.const 1)) (.reg 10) ;;
                .store (.bin .add (.reg 12) (.const 3)) (.reg 11) ;;
                .assign 15 (.load (.bin .add (.reg 13) (.const 4))) ;;
                .store (.bin .add (.reg 12) (.const 4)) (.bin .add (.reg 15) (.const 1)) ;;
                .store (.reg 13) (.const 0) ;;
                .store (.bin .add (.reg 13) (.const 2)) (.reg 4) ;;
                .store (.bin .add (.reg 13) (.const 3)) (.const 0) ;;
                .assign 16 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 14))) (.const 4))) ;;
                .store (.bin .add (.reg 13) (.const 4)) (.bin .sub (.reg 15) (.reg 16)) ;;
                .assign 17 (.load (.bin .add (.reg 0) (.const 2))) ;;
                .store (.bin .add (.reg 17) (.reg 1)) (.reg 4) ;;
                .assign 7 (.const 1))
               .nop)
            .nop)
         .nop)
      .nop
  have hphase1 : ∃ stM cM done S_mid,
      Runs w p ω spliceCond st3 .normal stM cM ∧
      stM.regs 7 = done ∧ (done = 0 ∨ done = 1) ∧
      OrdArenaAt b S_mid stM.mem ∧
      OrdFrame b S.vCap S.eCap heap mem stM.mem ∧
      S_mid.vCap = S.vCap ∧ S_mid.eCap = S.eCap ∧
      (done = 1 →
        OrdInv (applyOrdEdit ord (.insertBefore v (endOfKey keyX) yOpt)) S_mid ∧
        cM + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S_mid ≤
          ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + 6500 * ordStoreLog S.eCap) ∧
      (done = 0 →
        stM.regs 0 = b ∧ stM.regs 1 = v ∧ stM.regs 2 = keyX ∧ stM.regs 5 = nb ∧
        OrdInv ord S_mid ∧ S_mid.eNode keyX = 0 ∧
        (∀ y0, yOpt = some y0 → y0 ∉ ord v) ∧
        cM + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S_mid ≤
          ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + 4500 * ordStoreLog S.eCap) := by
    by_cases hy0 : yWord = 0
    · have hc : (Expr.reg 3).eval w st3 = some 0 := Expr.eval_reg_of_eq (by simp [st3, st2, st1, st0, startState, hy0])
      refine ⟨st3, _, 0, S, ord_runs_cond_false hc (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
        by simp [st3], Or.inl rfl, harena, OrdFrame.refl hz, rfl, rfl, fun h => by omega,
        fun _ => ⟨by simp [st3, st2, st1, st0, startState], by simp [st3, st2, st1, st0, startState],
          by simp [st3, st2, st1, st0, startState], by simp [st3, st2, st1], hinv, hunused_S,
          fun y0 hy => by simp [hyOpt, hy0] at hy, by simp [Expr.size_reg]; omega⟩⟩
    · have hc1 : (Expr.reg 3).eval w st3 = some yWord := Expr.eval_reg_of_eq (by simp [st3, st2, st1, st0, startState])
      set keyY := yWord - 1 with hkeyY
      have ha8 : Runs w p ω (.assign 8 (.bin .sub (.reg 3) (.const 1))) st3 .normal
          { st3 with regs := Function.update st3.regs 8 keyY } _ :=
        runs_assign_iff.mpr ⟨keyY, Expr.eval_sub (Expr.eval_reg_of_eq (by simp [st3, st2, st1, st0, startState]))
          (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
      set st4 : State := { st3 with regs := Function.update st3.regs 8 keyY }
      by_cases hkY : keyY < S.eCap + S.eCap
      · have hkY2 : keyY < 2 * S.eCap := by omega
        have hc2 : (Expr.bin .lt (.reg 8) (.bin .add (.reg 6) (.reg 6))).eval w st4 = some 1 :=
          Expr.eval_lt_true (Expr.eval_reg_of_eq (by simp [st4]))
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4, st3, st2]))
              (Expr.eval_reg_of_eq (by simp [st4, st3, st2])) (by omega)) hkY (by omega)
        set en := ordENodeBase b S.vCap with hen
        have ha9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 0) (.const 3)))) st4 .normal
            { st4 with regs := Function.update st4.regs 9 en } _ :=
          runs_assign_iff.mpr ⟨en, Expr.eval_load_of_eq (Expr.eval_add
            (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, st0, startState]))
            (Expr.eval_const (by omega)) (by omega)) harena.hdr_eNode, rfl, rfl, rfl⟩
        set st5 : State := { st4 with regs := Function.update st4.regs 9 en }
        have ha10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 9) (.reg 8)))) st5 .normal
            { st5 with regs := Function.update st5.regs 10 (S.eNode keyY) } _ :=
          runs_assign_iff.mpr ⟨S.eNode keyY, Expr.eval_load_of_eq (Expr.eval_add
            (Expr.eval_reg_of_eq (v := en) (by simp [st5]))
            (Expr.eval_reg_of_eq (v := keyY) (by simp [st5, st4]))
            (by rw [hen]; unfold ordENodeBase; omega)) (harena.eNode_at keyY hkY2), rfl, rfl, rfl⟩
        set st6 : State := { st5 with regs := Function.update st5.regs 10 (S.eNode keyY) }
        rcases hinv.eNode_spec keyY hkY2 with ⟨he0, hnone⟩ | ⟨w0, hw0, hu_mem, hu_val⟩
        · have hc3 : (Expr.reg 10).eval w st6 = some 0 := Expr.eval_reg_of_eq (by simp [st6, he0])
          refine ⟨st6, _, 0, S,
            ord_runs_cond_true hc1 hy0 (ord_runs_seq_normal ha8 (ord_runs_cond_true hc2 Nat.one_ne_zero
              (ord_runs_seq_normal ha9 (ord_runs_seq_normal ha10 (ord_runs_cond_false hc3 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)))))),
            by simp [st6, st5, st4, st3], Or.inl rfl, harena, OrdFrame.refl hz, rfl, rfl, fun h => by omega,
            fun _ => ⟨by simp [st6, st5, st4, st3, st2, st1, st0, startState],
              by simp [st6, st5, st4, st3, st2, st1, st0, startState],
              by simp [st6, st5, st4, st3, st2, st1, st0, startState],
              by simp [st6, st5, st4, st3, st2, st1], hinv, hunused_S,
              fun y0 hy => by
                simp only [hyOpt, hy0, ite_false, Option.some.injEq] at hy; subst hy
                rw [← hinv.list_eq v hv]; rintro hm
                rcases List.mem_map.mp hm with ⟨x, hx, hxe⟩
                exact hnone v hv x hx (endOfKey_injective hxe),
              by simp [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega⟩⟩
        · set uy := S.eNode keyY with huy_def
          have huy_nz : uy ≠ 0 := SplayState.SubtreeInv_nonZero (hinv.tree_inv w0 hw0).sub hu_mem
          have hc3 : (Expr.reg 10).eval w st6 = some uy := Expr.eval_reg_of_eq (by simp [st6, huy_def])
          obtain ⟨oSR, stSR, cSR, hrunSR, ⟨S1, hoSR, hinv1, harena1, hfr1, hv1, he1, hrt1, hlist1, -, hcnt1, hphi1⟩, hcSR⟩ :=
            ordSplayRootBody_runs hrot hstep hsplay ω hinv harena hw0 hu_mem hfoot hz hw hwide (pos := st6.pos)
          have hcallSR : Runs w p ω (.call 11 splayRootProc [.reg 0, .reg 10]) st6 .normal
              { stSR with regs := Function.update st6.regs 11 (w0 + 1) }
              (argsSize [.reg 0, .reg 10] + cSR + 1) :=
            runs_call_iff.mpr ⟨[b, uy], ordSplayRootBody splayProc, oSR, stSR, cSR,
              evalArgs_cons (Expr.eval_reg_of_eq (by simp [st6, st5, st4, st3, st2, st1, st0, startState]))
                (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st6, huy_def])) (evalArgs_nil _ _)),
              hsplayRoot, hrunSR, rfl, by simp [hoSR], rfl⟩
          set st7 : State := { stSR with regs := Function.update st6.regs 11 (w0 + 1) }
          have hphi1_mul : cSR + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S1 ≤
              ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + 4000 * ordStoreLog S.eCap := by
            unfold ordPhi; rw [hcnt1]
            have h1 := Nat.mul_le_mul_left ORD_PHI_WEIGHT hphi1
            have h2 : ORD_PHI_WEIGHT * (sumTreePhi S1 + (S.trees w0).depthOf uy / 2) =
                ORD_PHI_WEIGHT * sumTreePhi S1 + ORD_PHI_WEIGHT * ((S.trees w0).depthOf uy / 2) := by ring
            have h3 : ORD_PHI_WEIGHT * (sumTreePhi S + 3 * ordStoreLog S.eCap) =
                ORD_PHI_WEIGHT * sumTreePhi S + 3 * ORD_PHI_WEIGHT * ordStoreLog S.eCap := by ring
            unfold ORD_PHI_WEIGHT at h1 h2 h3 ⊢; unfold ORD_SPLAY_RATE at hcSR
            have h650 : ((S.trees w0).depthOf uy / 2) * 650 ≤ 1000 * ((S.trees w0).depthOf uy / 2) := by omega
            omega
          have hunused_S1 : S1.eNode keyX = 0 := by
            rcases hinv1.eNode_spec keyX (by rw [he1]; exact hkX) with ⟨h0, _⟩ | ⟨w1, hw1, hmem1, hval1⟩
            · exact h0
            · exfalso; apply hx_nmem w1; rw [← hinv1.list_eq w1 hw1]
              exact List.mem_map.mpr ⟨_, hmem1, by rw [hval1]⟩
          by_cases hwv : v = w0
          · subst hwv
            have hc4 : (Expr.bin .eq (.reg 11) (.bin .add (.reg 1) (.const 1))).eval w st7 = some 1 :=
              Expr.eval_eq_true (Expr.eval_reg_of_eq (v := v + 1) (by simp [st7]))
                (Expr.eval_add (Expr.eval_reg_of_eq (v := v) (by simp [st7, st6, st5, st4, st3, st2, st1, st0, startState]))
                  (Expr.eval_const (by omega)) (by omega)) rfl (by omega)
            have huy_val1 : (S1.splay.nodes uy).val = keyY := by
              have h1 := hinv1.list_eq v (by rw [hv1]; exact hv)
              have h2 := hinv.list_eq v hv
              rw [hlist1] at h1; rw [← h1] at h2
              rcases List.getElem_of_mem hu_mem with ⟨i, hi, hgi⟩
              have hm := congrArg (fun l => l[i]?) h2
              simp [hi, hgi, hu_val] at hm; exact endOfKey_injective hm.symm
            have hyOpt_eq : yOpt = some (endOfKey keyY) := by simp [hyOpt, hy0, hkeyY]
            obtain ⟨stS, cS, hrunS, hr7S, S2, hinv2, harena2, hfr2, hv2, he2, hphi2⟩ :=
              insertSplice_runs halloc ω (stM := st7) hinv1 harena1 (by rw [hv1]; exact hv) (by rw [he1]; exact hkX)
                hunused_S1 hrt1 (hlist1 ▸ hu_mem) huy_val1 (by rw [hv1, he1, ← hyOpt_eq]; exact huniq')
                (by simp [st7, st6, st5, st4, st3, st2, st1, st0, startState])
                (by simp [st7, st6, st5, st4, st3, st2, st1, st0, startState])
                (by simp [st7, st6, st5, st4, st3, st2, st1, st0, startState])
                (by simp [st7, st6, st5, st4, st3, st2, st1, hv1, he1, hnb])
                (by simp [st7, st6, huy_def]) (by simp [st7])
                (by rw [hv1, he1]; exact hfoot) hfr1.1 hw hwide
            refine ⟨stS, _, 1, S2,
              ord_runs_cond_true hc1 hy0 (ord_runs_seq_normal ha8 (ord_runs_cond_true hc2 Nat.one_ne_zero
                (ord_runs_seq_normal ha9 (ord_runs_seq_normal ha10 (ord_runs_cond_true hc3 huy_nz
                  (ord_runs_seq_normal hcallSR (ord_runs_cond_true hc4 Nat.one_ne_zero hrunS))))))),
              hr7S, Or.inr rfl, harena2, hfr1.trans (by rw [hv1, he1] at hfr2; exact hfr2),
              hv2.trans hv1, he2.trans he1, fun _ => ⟨by rw [hyOpt_eq]; exact hinv2, ?_⟩, fun h => by omega⟩
            rw [he1] at hphi2
            simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const,
              argsSize_cons, argsSize_nil] at *
            omega
          · have hc4 : (Expr.bin .eq (.reg 11) (.bin .add (.reg 1) (.const 1))).eval w st7 = some 0 :=
              Expr.eval_eq_false (Expr.eval_reg_of_eq (v := w0 + 1) (by simp [st7]))
                (Expr.eval_add (Expr.eval_reg_of_eq (v := v) (by simp [st7, st6, st5, st4, st3, st2, st1, st0, startState]))
                  (Expr.eval_const (by omega)) (by omega)) (by omega) (by omega)
            refine ⟨st7, _, 0, S1,
              ord_runs_cond_true hc1 hy0 (ord_runs_seq_normal ha8 (ord_runs_cond_true hc2 Nat.one_ne_zero
                (ord_runs_seq_normal ha9 (ord_runs_seq_normal ha10 (ord_runs_cond_true hc3 huy_nz
                  (ord_runs_seq_normal hcallSR (ord_runs_cond_false hc4 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)))))))),
              by simp [st7, st6, st5, st4, st3], Or.inl rfl, harena1, hfr1, hv1, he1, fun h => by omega,
              fun _ => ⟨by simp [st7, st6, st5, st4, st3, st2, st1, st0, startState],
                by simp [st7, st6, st5, st4, st3, st2, st1, st0, startState],
                by simp [st7, st6, st5, st4, st3, st2, st1, st0, startState],
                by simp [st7, st6, st5, st4, st3, st2, st1], hinv1, hunused_S1,
                fun y0 hy => by
                  simp only [hyOpt, hy0, ite_false, Option.some.injEq] at hy; subst hy
                  intro hmv
                  have hmw0 : endOfKey keyY ∈ ord w0 := by
                    rw [← hinv.list_eq w0 hw0]; exact List.mem_map.mpr ⟨uy, hu_mem, by rw [hu_val]⟩
                  exact hwv (hinv.ord_unique.unique_v hmv hmw0),
                by simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const,
                     argsSize_cons, argsSize_nil] at *; omega⟩⟩
      · have hc2 : (Expr.bin .lt (.reg 8) (.bin .add (.reg 6) (.reg 6))).eval w st4 = some 0 :=
          Expr.eval_lt_false (Expr.eval_reg_of_eq (v := keyY) (by simp [st4]))
            (Expr.eval_add (Expr.eval_reg_of_eq (v := S.eCap) (by simp [st4, st3, st2]))
              (Expr.eval_reg_of_eq (v := S.eCap) (by simp [st4, st3, st2])) (by omega)) (by omega) (by omega)
        refine ⟨st4, _, 0, S,
          ord_runs_cond_true hc1 hy0 (ord_runs_seq_normal ha8 (ord_runs_cond_false hc2 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩))),
          by simp [st4, st3], Or.inl rfl, harena, OrdFrame.refl hz, rfl, rfl, fun h => by omega,
          fun _ => ⟨by simp [st4, st3, st2, st1, st0, startState],
            by simp [st4, st3, st2, st1, st0, startState],
            by simp [st4, st3, st2, st1, st0, startState],
            by simp [st4, st3, st2, st1], hinv, hunused_S,
            fun y0 hy => by
              simp only [hyOpt, hy0, ite_false, Option.some.injEq] at hy; subst hy
              intro hmv; have := hinv.ord_unique.edge_lt hmv; simp [endOfKey] at this; omega,
            by simp [Expr.size_bin, Expr.size_reg, Expr.size_const]; omega⟩⟩
  obtain ⟨stM, cM, done, S_mid, hrun1, hr7M, hdone, harenaM, hfrM, hvM, heM, hcase1, hcase0⟩ := hphase1
  unfold ordInsertBeforeBody
  rcases hdone with rfl | rfl
  · obtain ⟨hr0M, hr1M, hr2M, hr5M, hinvM, hunusedM, hnm_y, hphiM⟩ := hcase0 rfl
    have hord_eq : applyOrdEdit ord (.insertBefore v (endOfKey keyX) yOpt) =
        Function.update ord v (ord v ++ [endOfKey keyX]) := by
      funext u; simp only [applyOrdEdit]
      by_cases h : u = v
      · subst h; simp [insertBeforeList_not_mem hnm_y]
      · simp [h]
    have hc2 : (Expr.bin .eq (.reg 7) (.const 0)).eval w stM = some 1 :=
      Expr.eval_eq_true (Expr.eval_reg_of_eq hr7M) (Expr.eval_const (by omega)) rfl (by omega)
    obtain ⟨stB, cB, hrunB, S', hinv', harena', hfrB, hv', he', hphiB⟩ :=
      insertBack_runs hrot hstep hsplay hwalk hjoin halloc ω hinvM harenaM
        (by rw [hvM]; exact hv) (by rw [heM]; exact hkX) hunusedM
        (by rw [hvM, heM, ← hord_eq]; exact huniq') hr0M hr1M hr2M (by rw [hvM, heM]; exact hr5M)
        (by rw [hvM, heM]; exact hfoot) hfrM.1 hw hwide
    have hret : Runs w p ω (.ret (.const 0)) stB (.returned 0) stB _ :=
      runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
    refine ⟨.returned 0, stB, _,
      ord_runs_seq_normal ha5 (ord_runs_seq_normal ha6 (ord_runs_seq_normal ha7
        (ord_runs_seq_normal hrun1 (ord_runs_seq_normal (ord_runs_cond_true hc2 Nat.one_ne_zero hrunB) hret)))),
      S', by rwa [hord_eq], harena', hfrM.trans (by rw [hvM, heM] at hfrB; exact hfrB),
      hv'.trans hvM, he'.trans heM, ?_⟩
    rw [heM] at hphiB
    unfold ORD_INS_AMORT
    simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
    omega
  · obtain ⟨hinvM, hphiM⟩ := hcase1 rfl
    have hc2 : (Expr.bin .eq (.reg 7) (.const 0)).eval w stM = some 0 :=
      Expr.eval_eq_false (Expr.eval_reg_of_eq hr7M) (Expr.eval_const (by omega)) (by omega) (by omega)
    have hret : Runs w p ω (.ret (.const 0)) stM (.returned 0) stM _ :=
      runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
    refine ⟨.returned 0, stM, _,
      ord_runs_seq_normal ha5 (ord_runs_seq_normal ha6 (ord_runs_seq_normal ha7
        (ord_runs_seq_normal hrun1 (ord_runs_seq_normal (ord_runs_cond_false hc2 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)) hret)))),
      S_mid, hinvM, harenaM, hfrM, hvM, heM, ?_⟩
    unfold ORD_INS_AMORT
    simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
    omega

end MinCostFlow.SparseCore.Program
