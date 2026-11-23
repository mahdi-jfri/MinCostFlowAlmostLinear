module

public import MinCostFlow.LinkCut.Prog.SplayStepShift

namespace MinCostFlow.LinkCut.Prog

/-!
Word-RAM specification for `shiftPtrStmt` and `applyTagBody`:
- `listIntMinAgg_mem` for bounding shifted path-minima via `StepsShiftFit`,
- `shiftPtrStmt_triple` and `shiftFieldStmt_triple` wrapping `Num.add` / `Num.subtract`,
- `applyTagBody_zero_triple` and `applyTagBody_runs_subtree`.
-/

open WordRAM MinCostFlow.Num

@[expose] public section

/-! ### `applyTagBody` specification -/

theorem applyTagBody_zero_triple {w _h L nodesBase : ℕ} (p : Program) (sp : SplayProcs)
    (mem₀ : ℕ → ℕ) (pos tPtr tNeg : ℕ)
    (hw0 : 0 < 2 ^ w) (_ht1 : tPtr < 2 ^ w) (_ht2 : tNeg < 2 ^ w) :
    Triple w p
      (fun st => st = startState [nodesBase, 0, tPtr, tNeg] mem₀ pos)
      (applyTagBody sp)
      (retPost fun v st' => v = 0 ∧ st'.mem = mem₀)
      (fun _ => K_APPLY_TAG L) := by
  intro st ω hst
  subst hst
  refine runs_start_le ?_
  have hcond : (Expr.reg 1).eval w (startState [nodesBase, 0, tPtr, tNeg] mem₀ pos) = some 0 := by
    simp [startState, Expr.eval]
  refine ⟨.returned 0, startState [nodesBase, 0, tPtr, tNeg] mem₀ pos, 4, ?_, ⟨rfl, rfl⟩,
    by dsimp only; unfold K_APPLY_TAG; omega⟩
  refine runs_cond_iff.mpr ⟨0, 2, hcond, ?_, rfl⟩
  exact runs_ret_iff.mpr ⟨0, Expr.eval_const hw0, rfl, rfl, rfl⟩

theorem applyTagHaseBlock_runs {w h L nodesBase cap x tPtr tNeg hp₀ : ℕ}
    {sp : SplayProcs} {p : Program} {mem₀ : ℕ → ℕ}
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hx1 : 1 ≤ x) (hx2 : x ≤ cap)
    (harena_pos : 1 ≤ nodesBase + NODE_STRIDE * (cap + 1))
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ hp₀)
    (hz : ZeroFrom mem₀ hp₀)
    (hhp_lt : hp₀ + 6 * L < 2 ^ w)
    (ht_ok : NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) hp₀ h L tPtr)
    (htNeg : tNeg ≤ 1)
    (hdir_le : nodeField mem₀ nodesBase x OFF_DIR ≤ 1)
    (hhe_le : nodeField mem₀ nodesBase x OFF_HASE ≤ 1)
    (he1 : nodeField mem₀ nodesBase x OFF_HASE = 1 →
      NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) hp₀ h L (nodeField mem₀ nodesBase x OFF_FLOW_PTR) ∧
      NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) hp₀ h L (nodeField mem₀ nodesBase x OFF_AF_PTR) ∧
      NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) hp₀ h L (nodeField mem₀ nodesBase x OFF_AB_PTR) ∧
      NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) hp₀ h L (nodeField mem₀ nodesBase x OFF_COST_FWD) ∧
      NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) hp₀ h L (nodeField mem₀ nodesBase x OFF_COST_BWD) ∧
      intVal mem₀ (nodeField mem₀ nodesBase x OFF_COST_BWD) h L =
        wrap h L (-intVal mem₀ (nodeField mem₀ nodesBase x OFF_COST_FWD) h L))
    (st4 : State) (hm4 : st4.mem = mem₀)
    (hr0 : st4.regs 0 = nodesBase) (hr2 : st4.regs 2 = tPtr) (hr3 : st4.regs 3 = tNeg)
    (hr4 : st4.regs 4 = nodesBase + NODE_STRIDE * x) (hr6 : st4.regs 6 = L) (hr7 : st4.regs 7 = hp₀) :
    ∀ ω, ∃ st5 c5 hp5,
      Runs w p ω
        (Stmt.cond (fieldLoadExpr 4 OFF_HASE)
          (Stmt.assign 8 (fieldLoadExpr 4 OFF_AF_PTR) ;;
           shiftPtrStmt sp (.reg 3) 8 2 6 7 9 ;;
           Stmt.store (fieldAddrExpr 4 OFF_AF_PTR) (.reg 9) ;;
           Stmt.assign 8 (fieldLoadExpr 4 OFF_AB_PTR) ;;
           shiftPtrStmt sp (.bin .sub (.const 1) (.reg 3)) 8 2 6 7 9 ;;
           Stmt.store (fieldAddrExpr 4 OFF_AB_PTR) (.reg 9) ;;
           Stmt.assign 8 (fieldLoadExpr 4 OFF_FLOW_PTR) ;;
           Stmt.assign 10 (fieldLoadExpr 4 OFF_DIR) ;;
           shiftPtrStmt sp (.bin .sub (.const 1) (.bin .eq (.reg 10) (.reg 3))) 8 2 6 7 9 ;;
           Stmt.store (fieldAddrExpr 4 OFF_FLOW_PTR) (.reg 9))
          Stmt.nop)
        st4 .normal st5 c5 ∧
      st5.regs 7 = hp5 ∧ hp₀ ≤ hp5 ∧ hp5 ≤ hp₀ + 6 * L ∧
      c5 + (hp5 - hp₀) ≤ 228 * L + 250 ∧
      st5.regs 0 = nodesBase ∧ st5.regs 2 = tPtr ∧ st5.regs 3 = tNeg ∧
      st5.regs 4 = nodesBase + NODE_STRIDE * x ∧ st5.regs 6 = L ∧
      NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1)) (nodesBase + NODE_STRIDE * x) hp₀ hp5 mem₀ st5.mem ∧
      (∀ off < NODE_STRIDE, off ≠ OFF_AF_PTR → off ≠ OFF_AB_PTR → off ≠ OFF_FLOW_PTR →
        st5.mem (nodesBase + NODE_STRIDE * x + off) = mem₀ (nodesBase + NODE_STRIDE * x + off)) ∧
      (nodeField mem₀ nodesBase x OFF_HASE = 0 → st5.mem = mem₀) ∧
      (nodeField mem₀ nodesBase x OFF_HASE = 1 →
        ∃ s₀, nodeOwnRawStep mem₀ nodesBase h L x = some s₀ ∧
          NumPtrOk st5.mem (nodesBase + NODE_STRIDE * (cap + 1)) hp5 h L (st5.mem (nodesBase + NODE_STRIDE * x + OFF_AF_PTR)) ∧
          NumPtrOk st5.mem (nodesBase + NODE_STRIDE * (cap + 1)) hp5 h L (st5.mem (nodesBase + NODE_STRIDE * x + OFF_AB_PTR)) ∧
          NumPtrOk st5.mem (nodesBase + NODE_STRIDE * (cap + 1)) hp5 h L (st5.mem (nodesBase + NODE_STRIDE * x + OFF_FLOW_PTR)) ∧
          nodeOwnRawStep st5.mem nodesBase h L x =
            some (s₀.addDeltaMod h L (if tNeg = 0 then intVal mem₀ tPtr h L else -intVal mem₀ tPtr h L))) := by
  intro ω
  let arenaHi := nodesBase + NODE_STRIDE * (cap + 1)
  let ptr := nodesBase + NODE_STRIDE * x
  let δ : ℤ := if tNeg = 0 then intVal mem₀ tPtr h L else -intVal mem₀ tPtr h L
  have hw1 : (1 : ℕ) < 2 ^ w := by unfold NODE_STRIDE at hbase; omega
  have hal : ∀ off < NODE_STRIDE, ptr + off < 2 ^ w := fun off hoff => nodeAddr_lt_pow hbase hx2 hoff
  have hev_he : (fieldLoadExpr 4 OFF_HASE).eval w st4 = some (mem₀ (ptr + OFF_HASE)) := by
    simpa [hm4] using eval_fieldLoadExpr hr4 (hal OFF_HASE (by decide))
  by_cases hhe0 : mem₀ (ptr + OFF_HASE) = 0
  · refine ⟨st4, _, hp₀, runs_cond_iff.mpr ⟨0, 1, by simpa [hhe0] using hev_he,
      by simp only; exact (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩ : Runs w p ω Stmt.nop st4 .normal st4 1), rfl⟩,
      hr7, le_rfl, by omega,
      by simp [fieldLoadExpr, fieldAddrExpr, Expr.size], hr0, hr2, hr3, hr4, hr6,
      by rw [hm4]; exact nodeHeapStepMem_refl _ _ _ _ hz, fun _ _ _ _ _ => hm4 ▸ rfl,
      fun _ => hm4, fun h1 => by dsimp only [nodeField, ptr] at h1 hhe0; omega⟩
  · have hhe1 : nodeField mem₀ nodesBase x OFF_HASE = 1 := by
      dsimp only [nodeField, ptr] at hhe_le hhe0 ⊢; omega
    rcases he1 hhe1 with ⟨pf, paf, pab, pcf, pcb, _⟩
    have hm4_pf : NumPtrOk st4.mem arenaHi hp₀ h L (st4.mem (ptr + OFF_AF_PTR)) := by
      rw [hm4]; exact paf
    have hm4_t : NumPtrOk st4.mem arenaHi hp₀ h L tPtr := by rw [hm4]; exact ht_ok
    have hz4 : ZeroFrom st4.mem hp₀ := hm4 ▸ hz
    rcases shiftFieldStmt_triple (fOff := OFF_AF_PTR) (isAddExpr := .reg 3) (isAddVal := tNeg)
        hp_ok st4 hbase hx1 hx2 (by decide) rfl
        (fun _ => Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide)]; exact hr3))
        hr4 hr2 hr6 hp₀ hr7 harena_pos harena hm4_pf hm4_t hz4 (by omega) ω with
      ⟨st5a, c5a, hp5a, out_af, hr5a, hr5a_7, hr5a_oth, h5a_lo, h5a_hi, hc5a, nhs5a,
        hmem5a_af, hmem5a_oth, hout_af_ok, hint_af⟩
    have nhs5a₀ : NodeHeapStepMem arenaHi ptr hp₀ hp5a mem₀ st5a.mem := hm4 ▸ nhs5a
    have hr5a_0 : st5a.regs 0 = nodesBase := (hr5a_oth 0 (by decide) (by decide) (by decide)).trans hr0
    have hr5a_2 : st5a.regs 2 = tPtr := (hr5a_oth 2 (by decide) (by decide) (by decide)).trans hr2
    have hr5a_3 : st5a.regs 3 = tNeg := (hr5a_oth 3 (by decide) (by decide) (by decide)).trans hr3
    have hr5a_4 : st5a.regs 4 = ptr := (hr5a_oth 4 (by decide) (by decide) (by decide)).trans hr4
    have hr5a_6 : st5a.regs 6 = L := (hr5a_oth 6 (by decide) (by decide) (by decide)).trans hr6
    have hab_5a_eq : st5a.mem (ptr + OFF_AB_PTR) = mem₀ (ptr + OFF_AB_PTR) := by
      rw [hmem5a_oth OFF_AB_PTR (by decide) (by decide), hm4]
    have heval_1sub3 : ∀ (st : State) v8, st.regs 3 = tNeg →
        (Expr.bin .sub (.const 1) (.reg 3)).eval w { mem := st.mem, regs := Function.update st.regs 8 v8, pos := st.pos } =
          some (1 - tNeg) := fun st v8 hs => by
      have h := Expr.eval_sub (Expr.eval_const hw1)
        (Expr.eval_reg w 3 { mem := st.mem, regs := Function.update st.regs 8 v8, pos := st.pos }) hw1
      simpa [Function.update_of_ne (by decide : (3 : ℕ) ≠ 8), hs] using h
    rcases shiftFieldStmt_triple (fOff := OFF_AB_PTR)
        (isAddExpr := .bin .sub (.const 1) (.reg 3)) (isAddVal := 1 - tNeg)
        hp_ok st5a hbase hx1 hx2 (by decide) rfl
        (fun v8 => heval_1sub3 st5a v8 hr5a_3)
        hr5a_4 hr5a_2 hr5a_6 hp5a hr5a_7 harena_pos (le_trans harena h5a_lo)
        (by rw [hab_5a_eq]; exact nodeHeapStepMem_numPtrOk nhs5a₀ pab)
        (nodeHeapStepMem_numPtrOk nhs5a₀ ht_ok)
        nhs5a₀.2.1 (by omega) ω with
      ⟨st5b, c5b, hp5b, out_ab, hr5b, hr5b_7, hr5b_oth, h5b_lo, h5b_hi, hc5b, nhs5b,
        hmem5b_ab, hmem5b_oth, hout_ab_ok, hint_ab⟩
    have hr5b_0 : st5b.regs 0 = nodesBase := (hr5b_oth 0 (by decide) (by decide) (by decide)).trans hr5a_0
    have hr5b_2 : st5b.regs 2 = tPtr := (hr5b_oth 2 (by decide) (by decide) (by decide)).trans hr5a_2
    have hr5b_3 : st5b.regs 3 = tNeg := (hr5b_oth 3 (by decide) (by decide) (by decide)).trans hr5a_3
    have hr5b_4 : st5b.regs 4 = ptr := (hr5b_oth 4 (by decide) (by decide) (by decide)).trans hr5a_4
    have hr5b_6 : st5b.regs 6 = L := (hr5b_oth 6 (by decide) (by decide) (by decide)).trans hr5a_6
    have nhs_ab : NodeHeapStepMem arenaHi ptr hp₀ hp5b mem₀ st5b.mem := nodeHeapStepMem_trans nhs5a₀ nhs5b
    have hflow_5b_eq : st5b.mem (ptr + OFF_FLOW_PTR) = mem₀ (ptr + OFF_FLOW_PTR) := by
      rw [hmem5b_oth OFF_FLOW_PTR (by decide) (by decide : OFF_FLOW_PTR ≠ OFF_AB_PTR),
        hmem5a_oth OFF_FLOW_PTR (by decide) (by decide : OFF_FLOW_PTR ≠ OFF_AF_PTR), hm4]
    have hdir_5b_eq : st5b.mem (ptr + OFF_DIR) = mem₀ (ptr + OFF_DIR) := by
      rw [hmem5b_oth OFF_DIR (by decide) (by decide : OFF_DIR ≠ OFF_AB_PTR),
        hmem5a_oth OFF_DIR (by decide) (by decide : OFF_DIR ≠ OFF_AF_PTR), hm4]
    let st5b' : State := ⟨st5b.mem, Function.update st5b.regs 8 (mem₀ (ptr + OFF_FLOW_PTR)), st5b.pos⟩
    have ha8_5b : Runs w p ω (Stmt.assign 8 (fieldLoadExpr 4 OFF_FLOW_PTR)) st5b .normal st5b' _ :=
      runs_assign_iff.mpr ⟨mem₀ (ptr + OFF_FLOW_PTR), by
        simpa [hflow_5b_eq] using eval_fieldLoadExpr hr5b_4 (hal OFF_FLOW_PTR (by decide)), rfl, rfl, rfl⟩
    have hr5b'_4 : st5b'.regs 4 = ptr := by dsimp [st5b']; rw [Function.update_of_ne (by decide)]; exact hr5b_4
    let st5c₀ : State := ⟨st5b.mem, Function.update st5b'.regs 10 (mem₀ (ptr + OFF_DIR)), st5b.pos⟩
    have ha10_5b : Runs w p ω (Stmt.assign 10 (fieldLoadExpr 4 OFF_DIR)) st5b' .normal st5c₀ _ :=
      runs_assign_iff.mpr ⟨mem₀ (ptr + OFF_DIR), by
        simpa [st5b', hdir_5b_eq] using eval_fieldLoadExpr hr5b'_4 (hal OFF_DIR (by decide)), rfl, rfl, rfl⟩
    have hr5c₀_10 : st5c₀.regs 10 = mem₀ (ptr + OFF_DIR) := by dsimp [st5c₀]; exact Function.update_self _ _ _
    have hr5c₀_3 : st5c₀.regs 3 = tNeg := by dsimp [st5c₀, st5b']; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr5b_3
    have hr5c₀_8 : st5c₀.regs 8 = mem₀ (ptr + OFF_FLOW_PTR) := by dsimp [st5c₀, st5b']; rw [Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
    have hr5c₀_2 : st5c₀.regs 2 = tPtr := by dsimp [st5c₀, st5b']; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr5b_2
    have hr5c₀_4 : st5c₀.regs 4 = ptr := by dsimp [st5c₀, st5b']; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr5b_4
    have hr5c₀_6 : st5c₀.regs 6 = L := by dsimp [st5c₀, st5b']; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr5b_6
    have hr5c₀_7 : st5c₀.regs 7 = hp5b := by dsimp [st5c₀, st5b']; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr5b_7
    have hr5c₀_0 : st5c₀.regs 0 = nodesBase := by dsimp [st5c₀, st5b']; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr5b_0
    have hev_eq_fl : (Expr.bin .eq (.reg 10) (.reg 3)).eval w st5c₀ =
        some (if mem₀ (ptr + OFF_DIR) = tNeg then 1 else 0) :=
      (Expr.eval_bin (Expr.eval_reg_of_eq hr5c₀_10) (Expr.eval_reg_of_eq hr5c₀_3)
        (by simp only [BinOp.eval_eq]; split_ifs <;> omega)).trans rfl
    have hev_fl : (Expr.bin .sub (.const 1) (.bin .eq (.reg 10) (.reg 3))).eval w st5c₀ =
        some (1 - if mem₀ (ptr + OFF_DIR) = tNeg then 1 else 0) :=
      Expr.eval_sub (Expr.eval_const hw1) hev_eq_fl hw1
    rcases shiftPtrStmt_triple (vPtr := mem₀ (ptr + OFF_FLOW_PTR)) (tPtr := tPtr)
        hp_ok (by decide : ([8, 2, 6, 7, 9] : List ℕ).Nodup) st5c₀ hev_fl
        hr5c₀_8 hr5c₀_2 hr5c₀_6 hr5c₀_7 harena_pos
        (nodeHeapStepMem_numPtrOk nhs_ab pf) (nodeHeapStepMem_numPtrOk nhs_ab ht_ok)
        nhs_ab.2.1 (by omega) ω with
      ⟨st5c₁, c5c, hp5, out_fl, hr5c, hr5c_7, hr5c_9, hr5c_oth, h5c_lo, h5c_hi, hc5c,
        hpres5c, hz5c, hout_fl_ok, hint_fl⟩
    have hr5c₁_4 : st5c₁.regs 4 = ptr := (hr5c_oth 4 (by decide) (by decide)).trans hr5c₀_4
    let st5 : State := ⟨Function.update st5c₁.mem (ptr + OFF_FLOW_PTR) out_fl, st5c₁.regs, st5c₁.pos⟩
    have hst_fl : Runs w p ω (Stmt.store (fieldAddrExpr 4 OFF_FLOW_PTR) (.reg 9)) st5c₁ .normal st5 _ :=
      runs_store_iff.mpr ⟨ptr + OFF_FLOW_PTR, out_fl,
        eval_fieldAddrExpr hr5c₁_4 (hal OFF_FLOW_PTR (by decide)), Expr.eval_reg_of_eq hr5c_9, rfl, rfl, rfl⟩
    have hslot_lt_arena : ∀ off < NODE_STRIDE, ptr + off < arenaHi := fun off hoff => by
      have hmul := Nat.mul_le_mul_left NODE_STRIDE hx2
      dsimp only [NODE_STRIDE] at hmul hoff ⊢
      dsimp only [arenaHi, ptr, NODE_STRIDE]
      omega
    have nhs5c : NodeHeapStepMem arenaHi ptr hp5b hp5 st5b.mem st5.mem := by
      refine ⟨h5c_lo, zeroFrom_update_lt_hp hz5c (lt_of_lt_of_le (hslot_lt_arena OFF_FLOW_PTR (by decide)) (le_trans (le_trans (le_trans harena h5a_lo) h5b_lo) h5c_lo)), ?_, ?_⟩
      · intro a ha hne
        dsimp [st5]; rw [Function.update_of_ne (hne OFF_FLOW_PTR (by decide))]
        exact hpres5c a (lt_of_lt_of_le ha (le_trans harena (le_trans h5a_lo h5b_lo)))
      · intro a ha1 ha2
        dsimp [st5]; rw [Function.update_of_ne (by have := hslot_lt_arena OFF_FLOW_PTR (by decide); omega), hpres5c a ha2]
    have nhs_total : NodeHeapStepMem arenaHi ptr hp₀ hp5 mem₀ st5.mem := nodeHeapStepMem_trans nhs_ab nhs5c
    have hst5_eq : ∀ off < NODE_STRIDE, off ≠ OFF_AF_PTR → off ≠ OFF_AB_PTR → off ≠ OFF_FLOW_PTR →
        st5.mem (ptr + off) = mem₀ (ptr + off) := by
      intro off hoff h1 h2 h3
      dsimp [st5]
      rw [Function.update_of_ne (by dsimp only [OFF_FLOW_PTR] at h3 ⊢; intro h; have := Nat.add_left_cancel h; exact h3 this),
        hpres5c _ (lt_of_lt_of_le (hslot_lt_arena off hoff) (le_trans harena (le_trans h5a_lo h5b_lo))),
        hmem5b_oth off hoff h2, hmem5a_oth off hoff h1, hm4]
    have hr_branch : Runs w p ω _ st4 .normal st5 _ :=
      runs_seq3_prepend hr5a
        (runs_seq3_prepend hr5b
          (runs_seq_iff.mpr (Or.inr ⟨st5b', _, _, ha8_5b,
            runs_seq_iff.mpr (Or.inr ⟨st5c₀, _, _, ha10_5b,
              runs_seq_iff.mpr (Or.inr ⟨st5c₁, _, _, hr5c, hst_fl, rfl⟩), rfl⟩), rfl⟩)))
    refine ⟨st5, _, hp5, runs_cond_iff.mpr ⟨mem₀ (ptr + OFF_HASE), _, hev_he,
        by rw [ite_eq_right hhe0]; exact hr_branch, rfl⟩, hr5c_7, by omega, by omega, ?_,
      (hr5c_oth 0 (by decide) (by decide)).trans hr5c₀_0,
      (hr5c_oth 2 (by decide) (by decide)).trans hr5c₀_2,
      (hr5c_oth 3 (by decide) (by decide)).trans hr5c₀_3,
      hr5c₁_4,
      (hr5c_oth 6 (by decide) (by decide)).trans hr5c₀_6,
      nhs_total, hst5_eq, (fun h0 => by rw [h0] at hhe1; cases hhe1), ?_⟩
    · simp only [fieldLoadExpr, fieldAddrExpr, Expr.size] at hc5a hc5b hc5c ⊢
      omega
    · intro _
      rcases hout_fl_ok with ⟨fl1, fllo, flhi, flval⟩
      have haf_eq : st5.mem (ptr + OFF_AF_PTR) = out_af := by
        dsimp [st5]
        rw [Function.update_of_ne (by intro h; have := Nat.add_left_cancel h; cases this),
          hpres5c _ (lt_of_lt_of_le (hslot_lt_arena OFF_AF_PTR (by decide)) (le_trans harena (le_trans h5a_lo h5b_lo))),
          hmem5b_oth OFF_AF_PTR (by decide) (by decide), hmem5a_af]
      have hab_eq : st5.mem (ptr + OFF_AB_PTR) = out_ab := by
        dsimp [st5]
        rw [Function.update_of_ne (by intro h; have := Nat.add_left_cancel h; cases this),
          hpres5c _ (lt_of_lt_of_le (hslot_lt_arena OFF_AB_PTR (by decide)) (le_trans harena (le_trans h5a_lo h5b_lo))),
          hmem5b_ab]
      have hfl_eq : st5.mem (ptr + OFF_FLOW_PTR) = out_fl := by dsimp [st5]; exact Function.update_self _ _ _
      have haf_5_ok : NumPtrOk st5.mem arenaHi hp5 h L (st5.mem (ptr + OFF_AF_PTR)) := by
        rw [haf_eq]; exact nodeHeapStepMem_numPtrOk (nodeHeapStepMem_trans nhs5b nhs5c) hout_af_ok
      have hab_5_ok : NumPtrOk st5.mem arenaHi hp5 h L (st5.mem (ptr + OFF_AB_PTR)) := by
        rw [hab_eq]; exact nodeHeapStepMem_numPtrOk nhs5c hout_ab_ok
      have hfl_5_ok : NumPtrOk st5.mem arenaHi hp5 h L (st5.mem (ptr + OFF_FLOW_PTR)) := by
        rw [hfl_eq]
        refine ⟨fl1, fllo, flhi, fun i hi => ?_⟩
        dsimp [st5]
        rw [Function.update_of_ne (by have := hslot_lt_arena OFF_FLOW_PTR (by decide); omega)]
        exact flval i hi
      have haf_5_val : intVal st5.mem out_af h L =
          wrap h L (intVal mem₀ (mem₀ (ptr + OFF_AF_PTR)) h L - δ) := by
        have hagree := intVal_agree_heap (h := h) (nodeHeapStepMem_trans nhs5b nhs5c).2.2.2 hout_af_ok.2.1 hout_af_ok.2.2.1
        rw [hagree, hint_af, hm4]
        by_cases ht0 : tNeg = 0 <;> simp [δ, ptr, ht0, sub_neg_eq_add]
      have hab_5_val : intVal st5.mem out_ab h L =
          wrap h L (intVal mem₀ (mem₀ (ptr + OFF_AB_PTR)) h L + δ) := by
        have hagree := intVal_agree_heap (h := h) nhs5c.2.2.2 hout_ab_ok.2.1 hout_ab_ok.2.2.1
        have hta := intVal_agree_heap (h := h) nhs5a₀.2.2.2 ht_ok.2.1 ht_ok.2.2.1
        have haba := intVal_agree_heap (h := h) nhs5a₀.2.2.2 pab.2.1 pab.2.2.1
        dsimp only [nodeField, ptr] at haba hta
        rw [hagree, hint_ab, hab_5a_eq, hta, haba]
        by_cases ht0 : tNeg = 0
        · simp [δ, ptr, ht0]
        · have ht1 : tNeg = 1 := by omega
          simp [δ, ptr, ht1, ← sub_eq_add_neg]
      have hfl_5_val : intVal st5.mem out_fl h L =
          wrap h L (if mem₀ (ptr + OFF_DIR) = 0
            then intVal mem₀ (mem₀ (ptr + OFF_FLOW_PTR)) h L - δ
            else intVal mem₀ (mem₀ (ptr + OFF_FLOW_PTR)) h L + δ) := by
        have hagree : intVal st5.mem out_fl h L = intVal st5c₁.mem out_fl h L := by
          apply intVal_congr; intro i hi
          dsimp [st5]; rw [Function.update_of_ne (by have := fllo; have := hslot_lt_arena OFF_FLOW_PTR (by decide); omega)]
        have ht_5b := intVal_agree_heap (h := h) nhs_ab.2.2.2 ht_ok.2.1 ht_ok.2.2.1
        have hfl_5b := intVal_agree_heap (h := h) nhs_ab.2.2.2 pf.2.1 pf.2.2.1
        dsimp only [nodeField, ptr] at hfl_5b
        rw [hagree, hint_fl]
        change wrap h L (if (1 - if mem₀ (ptr + OFF_DIR) = tNeg then 1 else 0) = 0 then _ else _) = _
        have hdir_le' : mem₀ (ptr + OFF_DIR) ≤ 1 := hdir_le
        dsimp [st5c₀]
        rw [ht_5b, hfl_5b]
        by_cases hdir0 : mem₀ (ptr + OFF_DIR) = 0 <;> by_cases ht0 : tNeg = 0
        · simp [δ, ptr, hdir0, ht0]
        · have ht1 : tNeg = 1 := by omega
          simp [δ, ptr, hdir0, ht1, sub_neg_eq_add]
        · have hd1 : mem₀ (ptr + OFF_DIR) = 1 := by omega
          simp [δ, ptr, hd1, ht0]
        · have hd1 : mem₀ (ptr + OFF_DIR) = 1 := by omega
          have ht1 : tNeg = 1 := by omega
          simp [δ, ptr, hd1, ht1, ← sub_eq_add_neg]
      have hcf_5 : intVal st5.mem (mem₀ (ptr + OFF_COST_FWD)) h L =
          intVal mem₀ (mem₀ (ptr + OFF_COST_FWD)) h L :=
        intVal_agree_heap (h := h) nhs_total.2.2.2 pcf.2.1 pcf.2.2.1
      have hcb_5 : intVal st5.mem (mem₀ (ptr + OFF_COST_BWD)) h L =
          intVal mem₀ (mem₀ (ptr + OFF_COST_BWD)) h L :=
        intVal_agree_heap (h := h) nhs_total.2.2.2 pcb.2.1 pcb.2.2.1
      have hhe_5 : st5.mem (nodesBase + NODE_STRIDE * x + OFF_HASE) = mem₀ (nodesBase + NODE_STRIDE * x + OFF_HASE) :=
        hst5_eq OFF_HASE (by decide) (by decide) (by decide) (by decide)
      dsimp only [ptr] at hhe0 haf_eq hab_eq hfl_eq haf_5_val hab_5_val hfl_5_val hcf_5 hcb_5 haf_5_ok hab_5_ok hfl_5_ok
      have hhe0_nf : nodeField mem₀ nodesBase x OFF_HASE ≠ 0 := by dsimp only [nodeField]; exact hhe0
      have hhe5_nf : nodeField st5.mem nodesBase x OFF_HASE ≠ 0 := by dsimp only [nodeField]; rw [hhe_5]; exact hhe0
      dsimp only [nodeOwnRawStep]
      rw [ite_eq_right hhe0_nf]
      refine ⟨_, rfl, haf_5_ok, hab_5_ok, hfl_5_ok, ?_⟩
      rw [ite_eq_right hhe5_nf]
      dsimp only [nodeField]
      simp only [show st5.mem (nodesBase + NODE_STRIDE * x + OFF_EID) = mem₀ (nodesBase + NODE_STRIDE * x + OFF_EID) from
          hst5_eq OFF_EID (by decide) (by decide) (by decide) (by decide),
        show st5.mem (nodesBase + NODE_STRIDE * x + OFF_EU) = mem₀ (nodesBase + NODE_STRIDE * x + OFF_EU) from
          hst5_eq OFF_EU (by decide) (by decide) (by decide) (by decide),
        show st5.mem (nodesBase + NODE_STRIDE * x + OFF_EV) = mem₀ (nodesBase + NODE_STRIDE * x + OFF_EV) from
          hst5_eq OFF_EV (by decide) (by decide) (by decide) (by decide),
        show st5.mem (nodesBase + NODE_STRIDE * x + OFF_DIR) = mem₀ (nodesBase + NODE_STRIDE * x + OFF_DIR) from
          hst5_eq OFF_DIR (by decide) (by decide) (by decide) (by decide),
        show st5.mem (nodesBase + NODE_STRIDE * x + OFF_COST_FWD) = mem₀ (nodesBase + NODE_STRIDE * x + OFF_COST_FWD) from
          hst5_eq OFF_COST_FWD (by decide) (by decide) (by decide) (by decide),
        show st5.mem (nodesBase + NODE_STRIDE * x + OFF_COST_BWD) = mem₀ (nodesBase + NODE_STRIDE * x + OFF_COST_BWD) from
          hst5_eq OFF_COST_BWD (by decide) (by decide) (by decide) (by decide),
        haf_eq, hab_eq, hfl_eq, haf_5_val, hab_5_val, hfl_5_val, hcf_5, hcb_5, RawStep.addDeltaMod]
      by_cases hdir0 : mem₀ (nodesBase + NODE_STRIDE * x + OFF_DIR) = 0 <;> simp [δ, hdir0]

theorem applyTagChildTagBlock_runs {w h L nodesBase cap x lId rId tPtr tNeg hp7 : ℕ}
    {sp : SplayProcs} {p : Program} {mem7 : ℕ → ℕ}
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hx1 : 1 ≤ x) (hx2 : x ≤ cap)
    (harena_pos : 1 ≤ nodesBase + NODE_STRIDE * (cap + 1))
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ hp7)
    (hz : ZeroFrom mem7 hp7)
    (hhp_lt : hp7 + 2 * L < 2 ^ w)
    (_h0_m1 : mem7 (nodesBase + OFF_MIN1_HAS) = 0)
    (hlId : mem7 (nodesBase + NODE_STRIDE * x + OFF_LEFT) = lId)
    (hl_bound : lId = 0 ∨ (1 ≤ lId ∧ lId ≤ cap))
    (hl_m1_le : nodeField mem7 nodesBase lId OFF_MIN1_HAS ≤ 1)
    (hrId : mem7 (nodesBase + NODE_STRIDE * x + OFF_RIGHT) = rId)
    (hr_bound : rId = 0 ∨ (1 ≤ rId ∧ rId ≤ cap))
    (hr_m1_le : nodeField mem7 nodesBase rId OFF_MIN1_HAS ≤ 1)
    (hht_le : mem7 (nodesBase + NODE_STRIDE * x + OFF_HAS_TAG) ≤ 1)
    (ht_ok : NumPtrOk mem7 (nodesBase + NODE_STRIDE * (cap + 1)) hp7 h L tPtr)
    (_htNeg : tNeg ≤ 1)
    (htag_ok : mem7 (nodesBase + NODE_STRIDE * x + OFF_HAS_TAG) = 1 →
      NumPtrOk mem7 (nodesBase + NODE_STRIDE * (cap + 1)) hp7 h L (mem7 (nodesBase + NODE_STRIDE * x + OFF_TAG_PTR)))
    (st7 : State) (hm7 : st7.mem = mem7)
    (hr0 : st7.regs 0 = nodesBase) (hr2 : st7.regs 2 = tPtr) (hr3 : st7.regs 3 = tNeg)
    (hr4 : st7.regs 4 = nodesBase + NODE_STRIDE * x) (hr6 : st7.regs 6 = L) (hr7 : st7.regs 7 = hp7) :
    ∀ ω, ∃ st8 c8 hp8,
      Runs w p ω
        (Stmt.assign 10 (fieldLoadExpr 4 OFF_LEFT) ;;
         Stmt.assign 10 (nodePtrExpr 0 10) ;;
         Stmt.assign 11 (fieldLoadExpr 4 OFF_RIGHT) ;;
         Stmt.assign 11 (nodePtrExpr 0 11) ;;
         Stmt.assign 9 (.bin .add (fieldLoadExpr 10 OFF_MIN1_HAS) (fieldLoadExpr 11 OFF_MIN1_HAS)) ;;
         Stmt.cond (.reg 9)
           (Stmt.cond (fieldLoadExpr 4 OFF_HAS_TAG)
             (Stmt.assign 8 (fieldLoadExpr 4 OFF_TAG_PTR) ;;
              Stmt.assign 10 (fieldLoadExpr 4 OFF_TAG_NEG) ;;
              shiftPtrStmt sp (.bin .eq (.reg 10) (.reg 3)) 8 2 6 7 9 ;;
              Stmt.store (fieldAddrExpr 4 OFF_TAG_PTR) (.reg 9))
             (Stmt.store (fieldAddrExpr 4 OFF_HAS_TAG) (.const 1) ;;
              Stmt.store (fieldAddrExpr 4 OFF_TAG_PTR) (.reg 2) ;;
              Stmt.store (fieldAddrExpr 4 OFF_TAG_NEG) (.reg 3)))
           Stmt.nop)
        st7 .normal st8 c8 ∧
      st8.regs 0 = nodesBase ∧
      st8.regs 7 = hp8 ∧ hp7 ≤ hp8 ∧ hp8 ≤ hp7 + 2 * L ∧
      c8 + (hp8 - hp7) ≤ 76 * L + 140 ∧
      NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1)) (nodesBase + NODE_STRIDE * x) hp7 hp8 mem7 st8.mem ∧
      (∀ off < NODE_STRIDE, off ≠ OFF_HAS_TAG → off ≠ OFF_TAG_PTR → off ≠ OFF_TAG_NEG →
        st8.mem (nodesBase + NODE_STRIDE * x + off) = mem7 (nodesBase + NODE_STRIDE * x + off)) ∧
      (nodeField mem7 nodesBase lId OFF_MIN1_HAS + nodeField mem7 nodesBase rId OFF_MIN1_HAS = 0 →
        st8.mem = mem7 ∧ hp8 = hp7) ∧
      (nodeField mem7 nodesBase lId OFF_MIN1_HAS + nodeField mem7 nodesBase rId OFF_MIN1_HAS ≠ 0 →
        st8.mem (nodesBase + NODE_STRIDE * x + OFF_HAS_TAG) = 1 ∧
        NumPtrOk st8.mem (nodesBase + NODE_STRIDE * (cap + 1)) hp8 h L
          (st8.mem (nodesBase + NODE_STRIDE * x + OFF_TAG_PTR)) ∧
        st8.mem (nodesBase + NODE_STRIDE * x + OFF_TAG_NEG) =
          (if mem7 (nodesBase + NODE_STRIDE * x + OFF_HAS_TAG) = 0 then tNeg
           else mem7 (nodesBase + NODE_STRIDE * x + OFF_TAG_NEG)) ∧
        (mem7 (nodesBase + NODE_STRIDE * x + OFF_HAS_TAG) = 0 →
          st8.mem (nodesBase + NODE_STRIDE * x + OFF_TAG_PTR) = tPtr) ∧
        (mem7 (nodesBase + NODE_STRIDE * x + OFF_HAS_TAG) = 1 →
          intVal st8.mem (st8.mem (nodesBase + NODE_STRIDE * x + OFF_TAG_PTR)) h L = wrap h L
            (if mem7 (nodesBase + NODE_STRIDE * x + OFF_TAG_NEG) = tNeg
             then intVal mem7 (mem7 (nodesBase + NODE_STRIDE * x + OFF_TAG_PTR)) h L + intVal mem7 tPtr h L
             else intVal mem7 (mem7 (nodesBase + NODE_STRIDE * x + OFF_TAG_PTR)) h L - intVal mem7 tPtr h L))) := by
  intro ω
  let arenaHi := nodesBase + NODE_STRIDE * (cap + 1)
  let ptr := nodesBase + NODE_STRIDE * x
  have hw2 : (2 : ℕ) < 2 ^ w := by dsimp only [NODE_STRIDE] at hbase; omega
  have hw1 : (1 : ℕ) < 2 ^ w := by omega
  have hstride : NODE_STRIDE < 2 ^ w := by dsimp only [NODE_STRIDE] at hbase ⊢; omega
  have hal : ∀ off < NODE_STRIDE, ptr + off < 2 ^ w := fun off hoff => nodeAddr_lt_pow hbase hx2 hoff
  have hl_addr : nodesBase + NODE_STRIDE * lId + OFF_MIN1_HAS < 2 ^ w := by
    rcases hl_bound with rfl | ⟨_, hl2⟩
    · dsimp only [NODE_STRIDE, OFF_MIN1_HAS] at hbase ⊢; omega
    · exact nodeAddr_lt_pow hbase hl2 (by decide)
  have hr_addr : nodesBase + NODE_STRIDE * rId + OFF_MIN1_HAS < 2 ^ w := by
    rcases hr_bound with rfl | ⟨_, hr2⟩
    · dsimp only [NODE_STRIDE, OFF_MIN1_HAS] at hbase ⊢; omega
    · exact nodeAddr_lt_pow hbase hr2 (by decide)
  have hptr_l : nodesBase + NODE_STRIDE * lId < 2 ^ w := by
    rcases hl_bound with rfl | ⟨_, hl2⟩
    · dsimp only [NODE_STRIDE] at hbase; omega
    · have := Nat.mul_le_mul_left NODE_STRIDE hl2; dsimp only [NODE_STRIDE] at hbase ⊢; omega
  have hptr_r : nodesBase + NODE_STRIDE * rId < 2 ^ w := by
    rcases hr_bound with rfl | ⟨_, hr2⟩
    · dsimp only [NODE_STRIDE] at hbase; omega
    · have := Nat.mul_le_mul_left NODE_STRIDE hr2; dsimp only [NODE_STRIDE] at hbase ⊢; omega
  let stA : State := ⟨st7.mem, Function.update st7.regs 10 lId, st7.pos⟩
  have hmA : stA.mem = mem7 := hm7
  have hA : Runs w p ω (Stmt.assign 10 (fieldLoadExpr 4 OFF_LEFT)) st7 .normal stA _ :=
    runs_assign_iff.mpr ⟨lId, by
      simpa [hm7, hlId] using eval_fieldLoadExpr hr4 (hal OFF_LEFT (by decide)), rfl, rfl, rfl⟩
  let stB : State := ⟨stA.mem, Function.update stA.regs 10 (nodesBase + NODE_STRIDE * lId), stA.pos⟩
  have hmB : stB.mem = mem7 := hmA
  have hrA_0 : stA.regs 0 = nodesBase := by dsimp [stA]; rw [Function.update_of_ne (by decide)]; exact hr0
  have hrA_10 : stA.regs 10 = lId := by dsimp [stA]; exact Function.update_self _ _ _
  have hB : Runs w p ω (Stmt.assign 10 (nodePtrExpr 0 10)) stA .normal stB _ :=
    runs_assign_iff.mpr ⟨nodesBase + NODE_STRIDE * lId,
      eval_nodePtrExpr hstride hrA_0 hrA_10 hptr_l, rfl, rfl, rfl⟩
  have hrB_4 : stB.regs 4 = ptr := by
    dsimp [stB, stA]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr4
  let stC : State := ⟨stB.mem, Function.update stB.regs 11 rId, stB.pos⟩
  have hmC : stC.mem = mem7 := hmB
  have hC : Runs w p ω (Stmt.assign 11 (fieldLoadExpr 4 OFF_RIGHT)) stB .normal stC _ :=
    runs_assign_iff.mpr ⟨rId, by
      simpa [hmB, ptr, hrId] using eval_fieldLoadExpr hrB_4 (hal OFF_RIGHT (by decide)), rfl, rfl, rfl⟩
  have hrC_0 : stC.regs 0 = nodesBase := by
    dsimp [stC, stB, stA]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    exact hr0
  have hrC_11 : stC.regs 11 = rId := by dsimp [stC]; exact Function.update_self _ _ _
  let stD : State := ⟨stC.mem, Function.update stC.regs 11 (nodesBase + NODE_STRIDE * rId), stC.pos⟩
  have hmD : stD.mem = mem7 := hmC
  have hD : Runs w p ω (Stmt.assign 11 (nodePtrExpr 0 11)) stC .normal stD _ :=
    runs_assign_iff.mpr ⟨nodesBase + NODE_STRIDE * rId,
      eval_nodePtrExpr hstride hrC_0 hrC_11 hptr_r, rfl, rfl, rfl⟩
  have hrD_10 : stD.regs 10 = nodesBase + NODE_STRIDE * lId := by
    dsimp [stD, stC, stB]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
  have hrD_11 : stD.regs 11 = nodesBase + NODE_STRIDE * rId := by
    dsimp [stD]; exact Function.update_self _ _ _
  let csum := nodeField mem7 nodesBase lId OFF_MIN1_HAS + nodeField mem7 nodesBase rId OFF_MIN1_HAS
  have hcsum_lt : csum < 2 ^ w := by dsimp [csum]; omega
  let stE : State := ⟨stD.mem, Function.update stD.regs 9 csum, stD.pos⟩
  have hmE : stE.mem = mem7 := hmD
  have hev_csum : (Expr.bin .add (fieldLoadExpr 10 OFF_MIN1_HAS) (fieldLoadExpr 11 OFF_MIN1_HAS)).eval w stD =
      some csum := by
    dsimp only [csum, nodeField]
    have h1 := eval_fieldLoadExpr hrD_10 hl_addr
    have h2 := eval_fieldLoadExpr hrD_11 hr_addr
    rw [hmD] at h1 h2
    exact Expr.eval_add h1 h2 hcsum_lt
  have hE : Runs w p ω (Stmt.assign 9 (.bin .add (fieldLoadExpr 10 OFF_MIN1_HAS) (fieldLoadExpr 11 OFF_MIN1_HAS)))
      stD .normal stE _ :=
    runs_assign_iff.mpr ⟨csum, hev_csum, rfl, rfl, rfl⟩
  have hpre_tail : ∀ {rest : Stmt} {st' : State} {o : Outcome} {c_rest : ℕ},
      Runs w p ω rest stE o st' c_rest →
      Runs w p ω
        (Stmt.assign 10 (fieldLoadExpr 4 OFF_LEFT) ;;
         Stmt.assign 10 (nodePtrExpr 0 10) ;;
         Stmt.assign 11 (fieldLoadExpr 4 OFF_RIGHT) ;;
         Stmt.assign 11 (nodePtrExpr 0 11) ;;
         Stmt.assign 9 (.bin .add (fieldLoadExpr 10 OFF_MIN1_HAS) (fieldLoadExpr 11 OFF_MIN1_HAS)) ;;
         rest)
        st7 o st'
        ((fieldLoadExpr 4 OFF_LEFT).size + 1 +
          ((nodePtrExpr 0 10).size + 1 +
            ((fieldLoadExpr 4 OFF_RIGHT).size + 1 +
              ((nodePtrExpr 0 11).size + 1 +
                ((Expr.bin .add (fieldLoadExpr 10 OFF_MIN1_HAS) (fieldLoadExpr 11 OFF_MIN1_HAS)).size + 1 + c_rest + 1) + 1) + 1) + 1) + 1) :=
    fun hrest =>
      runs_seq_iff.mpr (Or.inr ⟨stA, _, _, hA,
        runs_seq_iff.mpr (Or.inr ⟨stB, _, _, hB,
          runs_seq_iff.mpr (Or.inr ⟨stC, _, _, hC,
            runs_seq_iff.mpr (Or.inr ⟨stD, _, _, hD,
              runs_seq_iff.mpr (Or.inr ⟨stE, _, _, hE, hrest, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hrE_0 : stE.regs 0 = nodesBase := by dsimp [stE]; rw [Function.update_of_ne (by decide)]; exact hrC_0
  have hrE_2 : stE.regs 2 = tPtr := by
    dsimp [stE, stD, stC, stB, stA]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr2
  have hrE_3 : stE.regs 3 = tNeg := by
    dsimp [stE, stD, stC, stB, stA]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr3
  have hrE_4 : stE.regs 4 = ptr := by
    dsimp [stE, stD, stC]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; exact hrB_4
  have hrE_6 : stE.regs 6 = L := by
    dsimp [stE, stD, stC, stB, stA]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr6
  have hrE_7 : stE.regs 7 = hp7 := by
    dsimp [stE, stD, stC, stB, stA]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr7
  have hrE_9 : stE.regs 9 = csum := by dsimp [stE]; exact Function.update_self _ _ _
  by_cases hcz : csum = 0
  · refine ⟨stE, _, hp7, hpre_tail
        (runs_cond_iff.mpr ⟨0, 1, by simpa [hcz] using Expr.eval_reg_of_eq hrE_9,
          by simp only; exact (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩ : Runs w p ω Stmt.nop stE .normal stE 1), rfl⟩),
        hrE_0, hrE_7, le_rfl, by omega, ?_, (by rw [hmE]; exact nodeHeapStepMem_refl _ _ _ _ hz),
        fun _ _ _ _ _ => hmE ▸ rfl, fun _ => ⟨hmE, rfl⟩, fun hnz => by omega⟩
    simp only [fieldLoadExpr, fieldAddrExpr, nodePtrExpr, Expr.size]; omega
  · have hev_ht : (fieldLoadExpr 4 OFF_HAS_TAG).eval w stE = some (mem7 (ptr + OFF_HAS_TAG)) := by
      simpa [hmE] using eval_fieldLoadExpr hrE_4 (hal OFF_HAS_TAG (by decide))
    by_cases hht0 : mem7 (ptr + OFF_HAS_TAG) = 0
    · let mem8a := Function.update stE.mem (ptr + OFF_HAS_TAG) 1
      let st8a : State := ⟨mem8a, stE.regs, stE.pos⟩
      let mem8b := Function.update mem8a (ptr + OFF_TAG_PTR) tPtr
      let st8b : State := ⟨mem8b, stE.regs, stE.pos⟩
      let mem8 := Function.update mem8b (ptr + OFF_TAG_NEG) tNeg
      let st8 : State := ⟨mem8, stE.regs, stE.pos⟩
      have h8a : Runs w p ω (Stmt.store (fieldAddrExpr 4 OFF_HAS_TAG) (.const 1)) stE .normal st8a _ :=
        runs_store_iff.mpr ⟨ptr + OFF_HAS_TAG, 1, eval_fieldAddrExpr hrE_4 (hal OFF_HAS_TAG (by decide)),
          Expr.eval_const hw1, rfl, rfl, rfl⟩
      have h8b : Runs w p ω (Stmt.store (fieldAddrExpr 4 OFF_TAG_PTR) (.reg 2)) st8a .normal st8b _ :=
        runs_store_iff.mpr ⟨ptr + OFF_TAG_PTR, tPtr, eval_fieldAddrExpr hrE_4 (hal OFF_TAG_PTR (by decide)),
          Expr.eval_reg_of_eq hrE_2, rfl, rfl, rfl⟩
      have h8c : Runs w p ω (Stmt.store (fieldAddrExpr 4 OFF_TAG_NEG) (.reg 3)) st8b .normal st8 _ :=
        runs_store_iff.mpr ⟨ptr + OFF_TAG_NEG, tNeg, eval_fieldAddrExpr hrE_4 (hal OFF_TAG_NEG (by decide)),
          Expr.eval_reg_of_eq hrE_3, rfl, rfl, rfl⟩
      have hcond_9 : Runs w p ω
          (Stmt.cond (.reg 9)
            (Stmt.cond (fieldLoadExpr 4 OFF_HAS_TAG)
              (Stmt.assign 8 (fieldLoadExpr 4 OFF_TAG_PTR) ;;
               Stmt.assign 10 (fieldLoadExpr 4 OFF_TAG_NEG) ;;
               shiftPtrStmt sp (.bin .eq (.reg 10) (.reg 3)) 8 2 6 7 9 ;;
               Stmt.store (fieldAddrExpr 4 OFF_TAG_PTR) (.reg 9))
              (Stmt.store (fieldAddrExpr 4 OFF_HAS_TAG) (.const 1) ;;
               Stmt.store (fieldAddrExpr 4 OFF_TAG_PTR) (.reg 2) ;;
               Stmt.store (fieldAddrExpr 4 OFF_TAG_NEG) (.reg 3)))
            Stmt.nop)
          stE .normal st8 _ :=
        runs_cond_iff.mpr ⟨csum, _, Expr.eval_reg_of_eq hrE_9, by
          rw [ite_eq_right hcz]
          exact runs_cond_iff.mpr ⟨0, _, by simpa [hht0] using hev_ht,
            runs_seq_iff.mpr (Or.inr ⟨st8a, _, _, h8a, runs_seq_iff.mpr (Or.inr ⟨st8b, _, _, h8b, h8c, rfl⟩), rfl⟩), rfl⟩, rfl⟩
      have hslot_arena : ∀ off < NODE_STRIDE, ptr + off < arenaHi := fun off hoff => by
        have hm := Nat.mul_le_mul_left NODE_STRIDE hx2
        have ha : arenaHi = nodesBase + (NODE_STRIDE * cap + NODE_STRIDE) := by
          dsimp only [arenaHi]; rw [Nat.mul_add, Nat.mul_one]
        dsimp only [ptr]; omega
      have hslot_lt : ∀ off < NODE_STRIDE, ptr + off < hp7 := fun off hoff =>
        lt_of_lt_of_le (hslot_arena off hoff) harena
      have nhs8 : NodeHeapStepMem arenaHi ptr hp7 hp7 mem7 mem8 := by
        refine ⟨le_rfl, ?_, ?_, ?_⟩
        · exact zeroFrom_update_lt_hp (zeroFrom_update_lt_hp (zeroFrom_update_lt_hp (hmE ▸ hz) (hslot_lt OFF_HAS_TAG (by decide)))
            (hslot_lt OFF_TAG_PTR (by decide))) (hslot_lt OFF_TAG_NEG (by decide))
        · intro a ha hne
          dsimp [mem8, mem8b, mem8a]
          rw [Function.update_of_ne (hne OFF_TAG_NEG (by decide)),
            Function.update_of_ne (hne OFF_TAG_PTR (by decide)),
            Function.update_of_ne (hne OFF_HAS_TAG (by decide)), hmE]
        · intro a ha1 _
          dsimp [mem8, mem8b, mem8a]
          rw [Function.update_of_ne (by have := hslot_arena OFF_TAG_NEG (by decide); omega),
            Function.update_of_ne (by have := hslot_arena OFF_TAG_PTR (by decide); omega),
            Function.update_of_ne (by have := hslot_arena OFF_HAS_TAG (by decide); omega), hmE]
      refine ⟨st8, _, hp7, hpre_tail hcond_9,
        hrE_0, hrE_7, le_rfl, by omega, ?_, nhs8, ?_, fun h0 => by omega, fun _ => ?_⟩
      · simp only [fieldLoadExpr, fieldAddrExpr, nodePtrExpr, Expr.size]; omega
      · intro off hoff h1 h2 h3
        dsimp [st8, mem8, mem8b, mem8a]
        rw [Function.update_of_ne (by omega : ptr + off ≠ ptr + OFF_TAG_NEG),
          Function.update_of_ne (by omega : ptr + off ≠ ptr + OFF_TAG_PTR),
          Function.update_of_ne (by omega : ptr + off ≠ ptr + OFF_HAS_TAG), hmE]
      · have hne1 : OFF_HAS_TAG ≠ OFF_TAG_NEG := by decide
        have hne2 : OFF_HAS_TAG ≠ OFF_TAG_PTR := by decide
        have hne3 : OFF_TAG_PTR ≠ OFF_TAG_NEG := by decide
        refine ⟨?_, ?_, ?_, ?_, fun h1 => by dsimp only [ptr] at hht0; omega⟩
        · dsimp [st8, mem8, mem8b, mem8a]
          rw [Function.update_of_ne (by omega : ptr + OFF_HAS_TAG ≠ ptr + OFF_TAG_NEG),
            Function.update_of_ne (by omega : ptr + OFF_HAS_TAG ≠ ptr + OFF_TAG_PTR), Function.update_self]
        · dsimp [st8, mem8, mem8b, mem8a]
          rw [Function.update_of_ne (by omega : ptr + OFF_TAG_PTR ≠ ptr + OFF_TAG_NEG), Function.update_self]
          exact nodeHeapStepMem_numPtrOk nhs8 ht_ok
        · dsimp [st8, mem8]; rw [Function.update_self]; dsimp only [ptr] at hht0; rw [ite_eq_left hht0]
        · intro _; dsimp [st8, mem8, mem8b]
          rw [Function.update_of_ne (by omega : ptr + OFF_TAG_PTR ≠ ptr + OFF_TAG_NEG), Function.update_self]
    · have hht1 : mem7 (ptr + OFF_HAS_TAG) = 1 := by dsimp only [ptr] at hht0 ⊢; omega
      have htag_ok1 := htag_ok hht1
      let tagOld := mem7 (ptr + OFF_TAG_PTR)
      let tagNegOld := mem7 (ptr + OFF_TAG_NEG)
      let st8a : State := ⟨stE.mem, Function.update stE.regs 8 tagOld, stE.pos⟩
      have h8a : Runs w p ω (Stmt.assign 8 (fieldLoadExpr 4 OFF_TAG_PTR)) stE .normal st8a _ :=
        runs_assign_iff.mpr ⟨tagOld, by simpa [hmE] using eval_fieldLoadExpr hrE_4 (hal OFF_TAG_PTR (by decide)), rfl, rfl, rfl⟩
      have hr8a_4 : st8a.regs 4 = ptr := by dsimp [st8a]; rw [Function.update_of_ne (by decide)]; exact hrE_4
      let st8b : State := ⟨st8a.mem, Function.update st8a.regs 10 tagNegOld, st8a.pos⟩
      have hm8b : st8b.mem = mem7 := hmE
      have h8b : Runs w p ω (Stmt.assign 10 (fieldLoadExpr 4 OFF_TAG_NEG)) st8a .normal st8b _ :=
        runs_assign_iff.mpr ⟨tagNegOld,
          by dsimp [st8a]; rw [hmE]; exact eval_fieldLoadExpr hr8a_4 (hal OFF_TAG_NEG (by decide)), rfl, rfl, rfl⟩
      have hr8b_10 : st8b.regs 10 = tagNegOld := by dsimp [st8b]; exact Function.update_self _ _ _
      have hr8b_3 : st8b.regs 3 = tNeg := by
        dsimp [st8b, st8a]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hrE_3
      have hr8b_8 : st8b.regs 8 = tagOld := by
        dsimp [st8b, st8a]; rw [Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
      have hr8b_2 : st8b.regs 2 = tPtr := by
        dsimp [st8b, st8a]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hrE_2
      have hr8b_6 : st8b.regs 6 = L := by
        dsimp [st8b, st8a]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hrE_6
      have hr8b_7 : st8b.regs 7 = hp7 := by
        dsimp [st8b, st8a]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hrE_7
      have hev_eq : (Expr.bin .eq (.reg 10) (.reg 3)).eval w st8b =
          some (if tagNegOld = tNeg then 1 else 0) :=
        (Expr.eval_bin (Expr.eval_reg_of_eq hr8b_10) (Expr.eval_reg_of_eq hr8b_3)
          (by simp only [BinOp.eval_eq]; split_ifs <;> omega)).trans rfl
      rcases shiftPtrStmt_triple (vPtr := tagOld) (tPtr := tPtr) hp_ok
          (by decide : ([8, 2, 6, 7, 9] : List ℕ).Nodup) st8b hev_eq
          hr8b_8 hr8b_2 hr8b_6 hr8b_7 harena_pos (hm8b ▸ htag_ok1) (hm8b ▸ ht_ok) (hm8b ▸ hz) hhp_lt ω with
        ⟨st8c, c8c, hp8, out_tag, hr8c, hr8c_7, hr8c_9, hr8c_oth, h8_lo, h8_hi, hc8c,
          hpres8c, hz8c, hout_ok, hint_8c⟩
      have hr8c_4 : st8c.regs 4 = ptr := by
        rw [hr8c_oth 4 (by decide) (by decide)]
        dsimp [st8b, st8a]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hrE_4
      have hr8c_0 : st8c.regs 0 = nodesBase := by
        rw [hr8c_oth 0 (by decide) (by decide)]
        dsimp [st8b, st8a]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hrE_0
      let st8 : State := ⟨Function.update st8c.mem (ptr + OFF_TAG_PTR) out_tag, st8c.regs, st8c.pos⟩
      have h8d : Runs w p ω (Stmt.store (fieldAddrExpr 4 OFF_TAG_PTR) (.reg 9)) st8c .normal st8 _ :=
        runs_store_iff.mpr ⟨ptr + OFF_TAG_PTR, out_tag,
          eval_fieldAddrExpr hr8c_4 (hal OFF_TAG_PTR (by decide)), Expr.eval_reg_of_eq hr8c_9, rfl, rfl, rfl⟩
      have hcond_9 : Runs w p ω
          (Stmt.cond (.reg 9)
            (Stmt.cond (fieldLoadExpr 4 OFF_HAS_TAG)
              (Stmt.assign 8 (fieldLoadExpr 4 OFF_TAG_PTR) ;;
               Stmt.assign 10 (fieldLoadExpr 4 OFF_TAG_NEG) ;;
               shiftPtrStmt sp (.bin .eq (.reg 10) (.reg 3)) 8 2 6 7 9 ;;
               Stmt.store (fieldAddrExpr 4 OFF_TAG_PTR) (.reg 9))
              (Stmt.store (fieldAddrExpr 4 OFF_HAS_TAG) (.const 1) ;;
               Stmt.store (fieldAddrExpr 4 OFF_TAG_PTR) (.reg 2) ;;
               Stmt.store (fieldAddrExpr 4 OFF_TAG_NEG) (.reg 3)))
            Stmt.nop)
          stE .normal st8 _ :=
        runs_cond_iff.mpr ⟨csum, _, Expr.eval_reg_of_eq hrE_9, by
          rw [ite_eq_right hcz]
          exact runs_cond_iff.mpr ⟨mem7 (ptr + OFF_HAS_TAG), _, hev_ht, by
            rw [ite_eq_right hht0]
            exact runs_seq_iff.mpr (Or.inr ⟨st8a, _, _, h8a,
              runs_seq_iff.mpr (Or.inr ⟨st8b, _, _, h8b,
                runs_seq_iff.mpr (Or.inr ⟨st8c, _, _, hr8c, h8d, rfl⟩), rfl⟩), rfl⟩), rfl⟩, rfl⟩
      have hslot_tp : ptr + OFF_TAG_PTR < arenaHi := by
        have hm := Nat.mul_le_mul_left NODE_STRIDE hx2
        have ha : arenaHi = nodesBase + (NODE_STRIDE * cap + NODE_STRIDE) := by
          dsimp only [arenaHi]; rw [Nat.mul_add, Nat.mul_one]
        have h30 : NODE_STRIDE = 30 := rfl
        have h20 : OFF_TAG_PTR = 20 := rfl
        omega
      have nhs8 : NodeHeapStepMem arenaHi ptr hp7 hp8 mem7 st8.mem := by
        refine ⟨h8_lo, zeroFrom_update_lt_hp hz8c (lt_of_lt_of_le hslot_tp (le_trans harena h8_lo)), ?_, ?_⟩
        · intro a ha hne
          dsimp [st8]; rw [Function.update_of_ne (hne OFF_TAG_PTR (by decide)),
            hpres8c a (lt_of_lt_of_le ha harena), hm8b]
        · intro a ha1 _
          dsimp [st8]; rw [Function.update_of_ne (by omega : a ≠ ptr + OFF_TAG_PTR),
            hpres8c a (by omega), hm8b]
      refine ⟨st8, _, hp8, hpre_tail hcond_9,
        hr8c_0, hr8c_7, h8_lo, h8_hi, ?_, nhs8, ?_, fun h0 => by omega, fun _ => ?_⟩
      · have hsz_eq : (Expr.bin .eq (.reg 10) (.reg 3)).size = 3 := rfl
        rw [hsz_eq] at hc8c
        simp only [fieldLoadExpr, fieldAddrExpr, nodePtrExpr, Expr.size] at hc8c ⊢
        omega
      · intro off hoff _ h2 _
        dsimp [st8]
        have ho_hi : ptr + off < hp7 := by
          have := Nat.mul_le_mul_left NODE_STRIDE hx2; rw [Nat.mul_add, Nat.mul_one] at *; omega
        rw [Function.update_of_ne (by omega : ptr + off ≠ ptr + OFF_TAG_PTR), hpres8c _ ho_hi, hm8b]
      · have htp_eq : st8.mem (ptr + OFF_TAG_PTR) = out_tag := by dsimp [st8]; exact Function.update_self _ _ _
        have hht_8 : st8.mem (ptr + OFF_HAS_TAG) = 1 := by
          dsimp [st8]
          have h1 : ptr + OFF_HAS_TAG < hp7 := by
            have hm := Nat.mul_le_mul_left NODE_STRIDE hx2
            have ha := harena
            rw [Nat.mul_add, Nat.mul_one] at ha
            have : OFF_HAS_TAG < NODE_STRIDE := by decide
            dsimp only [ptr]; omega
          have hne : OFF_HAS_TAG ≠ OFF_TAG_PTR := by decide
          rw [Function.update_of_ne (by omega : ptr + OFF_HAS_TAG ≠ ptr + OFF_TAG_PTR), hpres8c _ h1, hm8b, hht1]
        have htn_8 : st8.mem (ptr + OFF_TAG_NEG) = tagNegOld := by
          dsimp [st8]
          have h1 : ptr + OFF_TAG_NEG < hp7 := by
            have hm := Nat.mul_le_mul_left NODE_STRIDE hx2
            have ha := harena
            rw [Nat.mul_add, Nat.mul_one] at ha
            have : OFF_TAG_NEG < NODE_STRIDE := by decide
            dsimp only [ptr]; omega
          have hne : OFF_TAG_NEG ≠ OFF_TAG_PTR := by decide
          rw [Function.update_of_ne (by omega : ptr + OFF_TAG_NEG ≠ ptr + OFF_TAG_PTR), hpres8c _ h1, hm8b]
        rcases hout_ok with ⟨o1, olo, ohi, oval⟩
        have hout_ok' : NumPtrOk st8.mem arenaHi hp8 h L out_tag := by
          refine ⟨o1, olo, ohi, fun i hi => ?_⟩
          dsimp [st8]
          have htp_lt := hslot_tp
          rw [Function.update_of_ne (by omega)]
          exact oval i hi
        refine ⟨hht_8, by rw [htp_eq]; exact hout_ok', ?_, fun h0 => ?_, fun _ => ?_⟩
        · rw [htn_8]; dsimp only [ptr] at hht0 tagNegOld; rw [ite_eq_right hht0]
        · dsimp only [ptr] at hht0; exact absurd h0 hht0
        · rw [htp_eq]
          have hagree_out : intVal st8.mem out_tag h L = intVal st8c.mem out_tag h L := by
            apply intVal_congr; intro i hi
            dsimp [st8]; have htp_lt := hslot_tp
            rw [Function.update_of_ne (by omega)]
          rw [hagree_out, hint_8c, hm8b]
          by_cases he : tagNegOld = tNeg <;> simp [ptr, he, tagOld, tagNegOld]

theorem addDelta_addDelta (s : RawStep) (d₀ d : ℤ) :
    (s.addDelta d₀).addDelta d = s.addDelta (d₀ + d) := by
  rcases s with ⟨nid, eid, eu, ev, fwd, cost, flow, af, ab⟩
  cases fwd <;> simp only [RawStep.addDelta, Bool.false_eq_true, ↓reduceIte, RawStep.mk.injEq,
    true_and] <;> refine ⟨by omega, by omega, by omega⟩

theorem treeMemMatch_child_steps_nil {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap x : ℕ}
    {q : AuxTree} (hq : TreeMemMatch w h L mem nodesBase cap q x 0)
    (hzero : q = .leaf ∨ nodeField mem nodesBase q.rootId OFF_MIN1_HAS = 0) :
    ∀ fl δ, evalMemSteps mem nodesBase h L q fl δ = [] := by
  cases q with
  | leaf => intro fl δ; rfl
  | node y l r =>
      have hy0 : nodeField mem nodesBase y OFF_MIN1_HAS = 0 := by
        rcases hzero with h | h
        · cases h
        · simpa [AuxTree.rootId] using h
      have hnil0 : evalMemSteps mem nodesBase h L (.node y l r) false 0 = [] := by
        have hiff := hq.min1Has_iff_evalSteps_ne_nil
        by_contra hne
        have := hiff.mpr hne
        simp [AuxTree.rootId, hy0] at this
      intro fl δ
      cases fl
      · rw [← add_zero δ, evalMemSteps_addDeltaMod hq false δ 0, hnil0, List.map_nil]
      · rw [← neg_neg δ, evalMemSteps_true_eq hq (-δ)]
        have hneg : evalMemSteps mem nodesBase h L (.node y l r) false (-δ) = [] := by
          rw [← add_zero (-δ), evalMemSteps_addDeltaMod hq false (-δ) 0, hnil0, List.map_nil]
        rw [hneg]; rfl

theorem treeMemMatch_min1Has_le {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap x : ℕ}
    {q : AuxTree} (hq : TreeMemMatch w h L mem nodesBase cap q x 0)
    (h0_m1 : mem (nodesBase + OFF_MIN1_HAS) = 0) :
    nodeField mem nodesBase q.rootId OFF_MIN1_HAS ≤ 1 := by
  cases q with
  | leaf => simp [AuxTree.rootId, nodeField, h0_m1]
  | node y l r =>
      rcases hq with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, hm1h_y, _⟩
      exact hm1h_y

end

end MinCostFlow.LinkCut.Prog
