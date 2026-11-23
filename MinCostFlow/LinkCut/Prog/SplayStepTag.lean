module

public import MinCostFlow.LinkCut.Prog.SplayStepTagPost

namespace MinCostFlow.LinkCut.Prog

/-!
Word-RAM specification for `applyTagBody` on subtrees (`applyTagBody_runs_subtree`).
-/

open WordRAM MinCostFlow.Num

@[expose] public section

theorem applyTagBody_runs_subtree {w h L nodesBase cap parId pp tPtr tNeg : ℕ}
    {p : Program} {sp : SplayProcs} {mem₀ : ℕ → ℕ} (pos : ℕ)
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase)
    (hL_hdr : mem₀ (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₀ (nodesBase - 1))
    (hz : ZeroFrom mem₀ (mem₀ (nodesBase - 1)))
    (hhp_lt : mem₀ (nodesBase - 1) + K_APPLY_TAG L < 2 ^ w)
    (h0 : SlotZeroOk mem₀ nodesBase)
    {s : AuxTree} (ht : TreeMemMatch w h L mem₀ nodesBase cap s parId pp)
    (hnd : s.toList.Nodup)
    (htNeg : tNeg ≤ 1)
    (htPtr : NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₀ (nodesBase - 1)) h L tPtr)
    {d : ℤ}
    (hdmod : d % (capacity h L : ℤ) =
      (if tNeg = 0 then intVal mem₀ tPtr h L else -intVal mem₀ tPtr h L) % (capacity h L : ℤ))
    (hfit : StepsShiftFit h L (evalMemSteps mem₀ nodesBase h L s false 0) d) :
    ∀ ω, ∃ st' c,
      Runs w p ω (applyTagBody sp) (startState [nodesBase, s.rootId, tPtr, tNeg] mem₀ pos)
        (.returned 0) st' c ∧
      c + (st'.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤ K_APPLY_TAG L ∧
      mem₀ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      TreeMemMatch w h L st'.mem nodesBase cap s parId pp ∧
      evalMemSteps st'.mem nodesBase h L s false 0 =
        (evalMemSteps mem₀ nodesBase h L s false 0).map (fun q => q.addDelta d) ∧
      (∀ u ≤ cap, ∀ off < NODE_STRIDE,
        off ≠ OFF_AF_PTR → off ≠ OFF_AB_PTR → off ≠ OFF_FLOW_PTR →
        off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL →
        off ≠ OFF_HAS_TAG → off ≠ OFF_TAG_PTR → off ≠ OFF_TAG_NEG →
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      (∀ addr, addr < nodesBase + NODE_STRIDE * s.rootId ∨
          nodesBase + NODE_STRIDE * s.rootId + NODE_STRIDE ≤ addr →
        addr ≠ nodesBase - 1 → addr < mem₀ (nodesBase - 1) →
        st'.mem addr = mem₀ addr) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) mem₀ st'.mem := by
  intro ω
  let arenaHi := nodesBase + NODE_STRIDE * (cap + 1)
  let hp₀ := mem₀ (nodesBase - 1)
  have harena_pos : 1 ≤ arenaHi := by unfold arenaHi NODE_STRIDE; omega
  have hw0 : (0 : ℕ) < 2 ^ w := by unfold NODE_STRIDE at hbase; omega
  have hw1 : (1 : ℕ) < 2 ^ w := by unfold NODE_STRIDE at hbase; omega
  have hw3 : (3 : ℕ) < 2 ^ w := by unfold NODE_STRIDE at hbase; omega
  have htPtr_lt : tPtr < 2 ^ w := by have := htPtr.2.2.1; unfold K_APPLY_TAG at hhp_lt; omega
  have htNeg_lt : tNeg < 2 ^ w := by unfold NODE_STRIDE at hbase; omega
  cases s with
  | leaf =>
      rcases applyTagBody_zero_triple (_h := h) (L := L) p sp mem₀ pos tPtr tNeg hw0 htPtr_lt htNeg_lt _ ω rfl with
        ⟨o, st', c, hrun, hpost, hc⟩
      cases o with
      | normal => contradiction
      | returned v =>
          rcases hpost with ⟨rfl, hmem⟩
          exact ⟨st', c, hrun, by rw [hmem]; simpa using hc, by rw [hmem], trivial,
            by simp [evalMemSteps], fun u _ off _ _ _ _ _ _ _ _ => by simp [nodeField, hmem],
            fun _ _ _ _ => by simp [hmem], by rw [hmem]; exact lctFrame_refl (by omega) harena hz⟩
  | node x l r =>
      have hnd' := hnd
      simp only [AuxTree.toList, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_singleton] at hnd'
      rcases hnd' with ⟨⟨_, _, hx_l_mem⟩, _, hdisj_lr⟩
      have hx_l : x ∉ l.toList := fun hl => hx_l_mem x hl x rfl rfl
      have hx_r : x ∉ r.toList := fun hr => hdisj_lr x (Or.inr rfl) x hr rfl
      have htx := ht
      rcases ht with ⟨hx1, hx2, hL, hR, hP, hPP, hrev, hiv, hhe, hsum, hdir, hht, htn,
        heu, hev, heid, he1, he0, hcf, hcb, htag1, htag0, hm1h, hm2h, hm1_1, hm1_0,
        hagg, hl_m, hr_m⟩
      let ptr := nodesBase + NODE_STRIDE * x
      have hstride : NODE_STRIDE < 2 ^ w := by dsimp only [NODE_STRIDE] at hbase ⊢; omega
      have hptr_lt : ptr < 2 ^ w := nodePtr_lt_pow hbase hx2
      have hal : ∀ off < NODE_STRIDE, ptr + off < 2 ^ w := fun off hoff => nodeAddr_lt_pow hbase hx2 hoff
      have hslot_lt_hp : ∀ off < NODE_STRIDE, ptr + off < hp₀ := fun off hoff => by
        have := Nat.mul_le_mul_left NODE_STRIDE hx2; rw [Nat.mul_add, Nat.mul_one] at *; omega
      let st0 : State := startState [nodesBase, x, tPtr, tNeg] mem₀ pos
      have hxne : x ≠ 0 := by omega
      have hcond0 : (Expr.reg 1).eval w st0 = some x := by simp [st0, startState, Expr.eval]
      have hr0_0 : st0.regs 0 = nodesBase := by simp [st0, startState]
      have hr0_1 : st0.regs 1 = x := by simp [st0, startState]
      have hr0_2 : st0.regs 2 = tPtr := by simp [st0, startState]
      have hr0_3 : st0.regs 3 = tNeg := by simp [st0, startState]
      let st1 : State := { mem := mem₀, regs := Function.update st0.regs 4 ptr, pos := pos }
      have hstep1 : Runs w p ω (Stmt.assign 4 (nodePtrExpr 0 1)) st0 .normal st1 _ :=
        runs_assign_iff.mpr ⟨ptr, eval_nodePtrExpr hstride hr0_0 hr0_1 hptr_lt, rfl, rfl, rfl⟩
      have hr1_4 : st1.regs 4 = ptr := by dsimp [st1]; exact Function.update_self _ _ _
      let st2 : State := { mem := mem₀, regs := Function.update st1.regs 5 (mem₀ (ptr + OFF_MIN1_HAS)), pos := pos }
      have hstep2 : Runs w p ω (Stmt.assign 5 (fieldLoadExpr 4 OFF_MIN1_HAS)) st1 .normal st2 _ :=
        runs_assign_iff.mpr ⟨mem₀ (ptr + OFF_MIN1_HAS),
          eval_fieldLoadExpr hr1_4 (hal OFF_MIN1_HAS (by decide)), rfl, rfl, rfl⟩
      have hr2_0 : st2.regs 0 = nodesBase := by
        dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr0_0
      have hr2_2 : st2.regs 2 = tPtr := by
        dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr0_2
      have hr2_3 : st2.regs 3 = tNeg := by
        dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr0_3
      have hr2_4 : st2.regs 4 = ptr := by dsimp [st2]; rw [Function.update_of_ne (by decide)]; exact hr1_4
      have hr2_5 : st2.regs 5 = mem₀ (ptr + OFF_MIN1_HAS) := by
        dsimp [st2]; exact Function.update_self _ _ _
      by_cases hm1_z : mem₀ (ptr + OFF_MIN1_HAS) = 0
      · have hrun : Runs w p ω (applyTagBody sp) st0 (.returned 0) st2 _ :=
          runs_cond_iff.mpr ⟨x, _, hcond0, (by
            rw [ite_eq_right hxne]
            exact runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hstep1,
              runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hstep2,
                runs_cond_iff.mpr ⟨0, 2, by simpa [hm1_z] using Expr.eval_reg_of_eq hr2_5,
                  runs_ret_iff.mpr ⟨0, Expr.eval_const hw0, rfl, rfl, rfl⟩, rfl⟩, rfl⟩), rfl⟩)), rfl⟩
        have hsteps_nil : evalMemSteps mem₀ nodesBase h L (.node x l r) false 0 = [] := by
          by_contra hne
          have hne' := hagg.2.2.2.1.mpr hne
          dsimp only [nodeField] at hne'
          dsimp only [ptr] at hm1_z
          omega
        have hf1_nil : ∀ u ≤ cap, ∀ off < NODE_STRIDE,
            off ≠ OFF_AF_PTR → off ≠ OFF_AB_PTR → off ≠ OFF_FLOW_PTR →
            off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL →
            off ≠ OFF_HAS_TAG → off ≠ OFF_TAG_PTR → off ≠ OFF_TAG_NEG →
            nodeField st2.mem nodesBase u off = nodeField mem₀ nodesBase u off :=
          fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl
        have hf2_nil : ∀ addr, addr < nodesBase + NODE_STRIDE * (AuxTree.node x l r).rootId ∨
            nodesBase + NODE_STRIDE * (AuxTree.node x l r).rootId + NODE_STRIDE ≤ addr →
            addr ≠ nodesBase - 1 → addr < mem₀ (nodesBase - 1) →
            st2.mem addr = mem₀ addr :=
          fun _ _ _ _ => rfl
        exact ⟨st2, _, hrun,
          (by dsimp only [st2]; simp only [nodePtrExpr, fieldLoadExpr, fieldAddrExpr, Expr.size, K_APPLY_TAG]; omega),
          le_rfl, htx, (by rw [hsteps_nil]; rfl), hf1_nil, hf2_nil,
          lctFrame_refl (by dsimp only [NODE_STRIDE]; omega) harena hz⟩
      · have hm1_one : nodeField mem₀ nodesBase x OFF_MIN1_HAS = 1 := by
          dsimp only [nodeField, ptr] at hm1h hm1_z ⊢; omega
        have hhp₀_lt : hp₀ < 2 ^ w := by unfold K_APPLY_TAG at hhp_lt; omega
        have hev_L : (Expr.load (.bin .sub (.reg 0) (.const 3))).eval w st2 = some L := by
          have hs := Expr.eval_sub (Expr.eval_reg_of_eq hr2_0) (Expr.eval_const hw3)
            (by dsimp only [NODE_STRIDE] at hbase; omega)
          simpa [st2, hL_hdr] using Expr.eval_load hs
        let st3 : State := { mem := mem₀, regs := Function.update st2.regs 6 L, pos := pos }
        have hstep3 : Runs w p ω (Stmt.assign 6 (.load (.bin .sub (.reg 0) (.const 3)))) st2 .normal st3 _ :=
          runs_assign_iff.mpr ⟨L, hev_L, rfl, rfl, rfl⟩
        have hr3_0 : st3.regs 0 = nodesBase := by dsimp [st3]; rw [Function.update_of_ne (by decide)]; exact hr2_0
        have hr3_2 : st3.regs 2 = tPtr := by dsimp [st3]; rw [Function.update_of_ne (by decide)]; exact hr2_2
        have hr3_3 : st3.regs 3 = tNeg := by dsimp [st3]; rw [Function.update_of_ne (by decide)]; exact hr2_3
        have hr3_4 : st3.regs 4 = ptr := by dsimp [st3]; rw [Function.update_of_ne (by decide)]; exact hr2_4
        have hr3_6 : st3.regs 6 = L := by dsimp [st3]; exact Function.update_self _ _ _
        have hev_hp : (Expr.load (.bin .sub (.reg 0) (.const 1))).eval w st3 = some hp₀ := by
          have hs := Expr.eval_sub (Expr.eval_reg_of_eq hr3_0) (Expr.eval_const hw1)
            (by dsimp only [NODE_STRIDE] at hbase; omega)
          exact Expr.eval_load hs
        let st4 : State := { mem := mem₀, regs := Function.update st3.regs 7 hp₀, pos := pos }
        have hstep4 : Runs w p ω (Stmt.assign 7 (.load (.bin .sub (.reg 0) (.const 1)))) st3 .normal st4 _ :=
          runs_assign_iff.mpr ⟨hp₀, hev_hp, rfl, rfl, rfl⟩
        have hr4_0 : st4.regs 0 = nodesBase := by dsimp [st4]; rw [Function.update_of_ne (by decide)]; exact hr3_0
        have hr4_2 : st4.regs 2 = tPtr := by dsimp [st4]; rw [Function.update_of_ne (by decide)]; exact hr3_2
        have hr4_3 : st4.regs 3 = tNeg := by dsimp [st4]; rw [Function.update_of_ne (by decide)]; exact hr3_3
        have hr4_4 : st4.regs 4 = ptr := by dsimp [st4]; rw [Function.update_of_ne (by decide)]; exact hr3_4
        have hr4_6 : st4.regs 6 = L := by dsimp [st4]; rw [Function.update_of_ne (by decide)]; exact hr3_6
        have hr4_7 : st4.regs 7 = hp₀ := by dsimp [st4]; exact Function.update_self _ _ _
        have h12L : hp₀ + 12 * L < 2 ^ w := by unfold K_APPLY_TAG at hhp_lt; omega
        rcases applyTagHaseBlock_runs hp_ok hbase hx1 hx2 harena_pos harena hz (by omega) htPtr
            htNeg hdir hhe he1 st4 rfl hr4_0 hr4_2 hr4_3 hr4_4 hr4_6 hr4_7 ω with
          ⟨st5, c5, hp5, hrun5, hr5_7, h5_lo, h5_hi, hc5, hr5_0, hr5_2, hr5_3, hr5_4, hr5_6,
            nhs5, hmem5_oth, hhe5_zero, hhe5_post⟩
        rcases hm1_1 hm1_one with ⟨pm1, pm2, hm1_f, hm1_l, hm2_f, hm2_l⟩
        have hm1_5_ok : NumPtrOk st5.mem arenaHi hp5 h L (st5.mem (ptr + OFF_MIN1_VAL)) := by
          rw [hmem5_oth OFF_MIN1_VAL (by decide) (by decide) (by decide) (by decide)]
          exact nodeHeapStepMem_numPtrOk nhs5 pm1
        have ht_5_ok : NumPtrOk st5.mem arenaHi hp5 h L tPtr := nodeHeapStepMem_numPtrOk nhs5 htPtr
        rcases shiftFieldStmt_triple (fOff := OFF_MIN1_VAL) (isAddExpr := .reg 3) (isAddVal := tNeg)
            hp_ok st5 hbase hx1 hx2 (by decide) rfl
            (fun _ => Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide)]; exact hr5_3))
            hr5_4 hr5_2 hr5_6 hp5 hr5_7 harena_pos (le_trans harena h5_lo) hm1_5_ok ht_5_ok
            nhs5.2.1 (by omega) ω with
          ⟨st6, c6, hp6, out_m1, hrun6, hr6_7, hr6_oth, h6_lo, h6_hi, hc6, nhs6,
            hmem6_m1, hmem6_oth, hout_m1_ok, hint6⟩
        have nhs56 : NodeHeapStepMem arenaHi ptr hp₀ hp6 mem₀ st6.mem := nodeHeapStepMem_trans nhs5 nhs6
        have hr6_0 : st6.regs 0 = nodesBase := (hr6_oth 0 (by decide) (by decide) (by decide)).trans hr5_0
        have hr6_2 : st6.regs 2 = tPtr := (hr6_oth 2 (by decide) (by decide) (by decide)).trans hr5_2
        have hr6_3 : st6.regs 3 = tNeg := (hr6_oth 3 (by decide) (by decide) (by decide)).trans hr5_3
        have hr6_4 : st6.regs 4 = ptr := (hr6_oth 4 (by decide) (by decide) (by decide)).trans hr5_4
        have hr6_6 : st6.regs 6 = L := (hr6_oth 6 (by decide) (by decide) (by decide)).trans hr5_6
        have hm2_6_eq : st6.mem (ptr + OFF_MIN2_VAL) = mem₀ (ptr + OFF_MIN2_VAL) := by
          rw [hmem6_oth OFF_MIN2_VAL (by decide) (by decide),
            hmem5_oth OFF_MIN2_VAL (by decide) (by decide) (by decide) (by decide)]
        have hm2_6_ok : NumPtrOk st6.mem arenaHi hp6 h L (st6.mem (ptr + OFF_MIN2_VAL)) := by
          rw [hm2_6_eq]; exact nodeHeapStepMem_numPtrOk nhs56 pm2
        have ht_6_ok : NumPtrOk st6.mem arenaHi hp6 h L tPtr := nodeHeapStepMem_numPtrOk nhs56 htPtr
        have heval_1sub3 : ∀ v8,
            (Expr.bin .sub (.const 1) (.reg 3)).eval w { mem := st6.mem, regs := Function.update st6.regs 8 v8, pos := st6.pos } =
              some (1 - tNeg) := fun v8 => by
          have h := Expr.eval_sub (Expr.eval_const hw1)
            (Expr.eval_reg w 3 { mem := st6.mem, regs := Function.update st6.regs 8 v8, pos := st6.pos }) hw1
          simpa [Function.update_of_ne (by decide : (3 : ℕ) ≠ 8), hr6_3] using h
        rcases shiftFieldStmt_triple (fOff := OFF_MIN2_VAL)
            (isAddExpr := .bin .sub (.const 1) (.reg 3)) (isAddVal := 1 - tNeg)
            hp_ok st6 hbase hx1 hx2 (by decide) rfl
            heval_1sub3 hr6_4 hr6_2 hr6_6 hp6 hr6_7 harena_pos (le_trans harena (le_trans h5_lo h6_lo))
            hm2_6_ok ht_6_ok nhs56.2.1 (by omega) ω with
          ⟨st7, c7, hp7, out_m2, hrun7, hr7_7, hr7_oth, h7_lo, h7_hi, hc7, nhs7,
            hmem7_m2, hmem7_oth, hout_m2_ok, hint7⟩
        have nhs567 : NodeHeapStepMem arenaHi ptr hp₀ hp7 mem₀ st7.mem := nodeHeapStepMem_trans nhs56 nhs7
        have hr7_0 : st7.regs 0 = nodesBase := (hr7_oth 0 (by decide) (by decide) (by decide)).trans hr6_0
        have hr7_2 : st7.regs 2 = tPtr := (hr7_oth 2 (by decide) (by decide) (by decide)).trans hr6_2
        have hr7_3 : st7.regs 3 = tNeg := (hr7_oth 3 (by decide) (by decide) (by decide)).trans hr6_3
        have hr7_4 : st7.regs 4 = ptr := (hr7_oth 4 (by decide) (by decide) (by decide)).trans hr6_4
        have hr7_6 : st7.regs 6 = L := (hr7_oth 6 (by decide) (by decide) (by decide)).trans hr6_6
        have hmem7_oth_x : ∀ off < NODE_STRIDE, off ≠ OFF_AF_PTR → off ≠ OFF_AB_PTR → off ≠ OFF_FLOW_PTR →
            off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL →
            st7.mem (ptr + off) = mem₀ (ptr + off) := fun off hoff ha hb hf hm1 hm2 => by
          rw [hmem7_oth off hoff hm2, hmem6_oth off hoff hm1, hmem5_oth off hoff ha hb hf]
        have hmem7_node_le : ∀ u ≤ cap, u ≠ x → ∀ off < NODE_STRIDE,
            nodeField st7.mem nodesBase u off = nodeField mem₀ nodesBase u off :=
          fun u hu hux off hoff => nodeHeapStepMem_node_ne nhs567 hu hux hoff
        have h0_m1_7 : st7.mem (nodesBase + OFF_MIN1_HAS) = 0 := by
          simpa [nodeField] using
            (hmem7_node_le 0 (Nat.zero_le _) hxne.symm OFF_MIN1_HAS (by decide)).trans (h0 OFF_MIN1_HAS (by decide))
        have hlId_7 : st7.mem (ptr + OFF_LEFT) = l.rootId :=
          (hmem7_oth_x OFF_LEFT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
        have hrId_7 : st7.mem (ptr + OFF_RIGHT) = r.rootId :=
          (hmem7_oth_x OFF_RIGHT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hR
        have hl_bound : l.rootId = 0 ∨ (1 ≤ l.rootId ∧ l.rootId ≤ cap) := by
          cases l with | leaf => exact Or.inl rfl | node lx _ _ => exact Or.inr ⟨hl_m.1, hl_m.2.1⟩
        have hr_bound : r.rootId = 0 ∨ (1 ≤ r.rootId ∧ r.rootId ≤ cap) := by
          cases r with | leaf => exact Or.inl rfl | node rx _ _ => exact Or.inr ⟨hr_m.1, hr_m.2.1⟩
        have hl_m1_le : nodeField st7.mem nodesBase l.rootId OFF_MIN1_HAS ≤ 1 := by
          have hl_0 := treeMemMatch_min1Has_le hl_m (h0 OFF_MIN1_HAS (by decide))
          cases l with
          | leaf =>
              simp only [AuxTree.rootId, nodeField, Nat.mul_zero, Nat.add_zero]
              omega
          | node lx _ _ =>
              dsimp only [AuxTree.rootId]
              have hne : lx ≠ x := fun h => hx_l (h ▸ by simp [AuxTree.toList])
              rw [hmem7_node_le lx hl_m.2.1 hne OFF_MIN1_HAS (by decide)]
              exact hl_0
        have hr_m1_le : nodeField st7.mem nodesBase r.rootId OFF_MIN1_HAS ≤ 1 := by
          have hr_0 := treeMemMatch_min1Has_le hr_m (h0 OFF_MIN1_HAS (by decide))
          cases r with
          | leaf =>
              simp only [AuxTree.rootId, nodeField, Nat.mul_zero, Nat.add_zero]
              omega
          | node rx _ _ =>
              dsimp only [AuxTree.rootId]
              have hne : rx ≠ x := fun h => hx_r (h ▸ by simp [AuxTree.toList])
              rw [hmem7_node_le rx hr_m.2.1 hne OFF_MIN1_HAS (by decide)]
              exact hr_0
        have hht_le7 : st7.mem (ptr + OFF_HAS_TAG) ≤ 1 := by
          rw [hmem7_oth_x OFF_HAS_TAG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact hht
        have htag_7_ok : st7.mem (ptr + OFF_HAS_TAG) = 1 →
            NumPtrOk st7.mem arenaHi hp7 h L (st7.mem (ptr + OFF_TAG_PTR)) := fun h1 => by
          rw [hmem7_oth_x OFF_HAS_TAG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at h1
          rw [hmem7_oth_x OFF_TAG_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact nodeHeapStepMem_numPtrOk nhs567 (htag1 h1).1
        rcases applyTagChildTagBlock_runs hp_ok hbase hx1 hx2 harena_pos (le_trans harena (by omega))
            nhs567.2.1 (by omega) h0_m1_7 hlId_7 hl_bound hl_m1_le hrId_7 hr_bound hr_m1_le hht_le7
            (nodeHeapStepMem_numPtrOk nhs567 htPtr) htNeg htag_7_ok
            st7 rfl hr7_0 hr7_2 hr7_3 hr7_4 hr7_6 hr7_7 ω with
          ⟨st8, c8, hp8, hrun8, hr8_0, hr8_7, h8_lo, h8_hi, hc8, nhs8, hmem8_oth, h8_zero, h8_nz⟩
        have nhs5678 : NodeHeapStepMem arenaHi ptr hp₀ hp8 mem₀ st8.mem := nodeHeapStepMem_trans nhs567 nhs8
        have hhp8_lt : hp8 < 2 ^ w := by unfold K_APPLY_TAG at hhp_lt; omega
        have hev_nb1 : (Expr.bin .sub (.reg 0) (.const 1)).eval w st8 = some (nodesBase - 1) :=
          Expr.eval_sub (Expr.eval_reg_of_eq hr8_0) (Expr.eval_const hw1) (by omega)
        let st9 : State := { mem := Function.update st8.mem (nodesBase - 1) hp8, regs := st8.regs, pos := st8.pos }
        have hstep9 : Runs w p ω (Stmt.store (.bin .sub (.reg 0) (.const 1)) (.reg 7)) st8 .normal st9 _ :=
          runs_store_iff.mpr ⟨nodesBase - 1, hp8, hev_nb1, Expr.eval_reg_of_eq hr8_7, rfl, rfl, rfl⟩
        have hstep10 : Runs w p ω (Stmt.ret (.const 0)) st9 (.returned 0) st9 2 :=
          runs_ret_iff.mpr ⟨0, Expr.eval_const hw0, rfl, rfl, rfl⟩
        have hrun_then : Runs w p ω _ st2 (.returned 0) st9 _ :=
          runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hstep3,
            runs_seq_iff.mpr (Or.inr ⟨st4, _, _, hstep4,
              runs_seq_iff.mpr (Or.inr ⟨st5, _, _, hrun5,
                runs_seq3_prepend hrun6
                  (runs_seq3_prepend hrun7
                    (runs_seq6_prepend hrun8
                      (runs_seq_iff.mpr (Or.inr ⟨st9, _, _, hstep9, hstep10, rfl⟩)))), rfl⟩), rfl⟩), rfl⟩)
        have hrun_full : Runs w p ω (applyTagBody sp) st0 (.returned 0) st9 _ :=
          runs_cond_iff.mpr ⟨x, _, hcond0, (by
            rw [ite_eq_right hxne]
            exact runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hstep1,
              runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hstep2,
                runs_cond_iff.mpr ⟨mem₀ (ptr + OFF_MIN1_HAS), _, Expr.eval_reg_of_eq hr2_5,
                  (by rw [ite_eq_right hm1_z]; exact hrun_then), rfl⟩, rfl⟩), rfl⟩)), rfl⟩
        have hm9_hp : st9.mem (nodesBase - 1) = hp8 := by dsimp [st9]; exact Function.update_self _ _ _
        have hm9_ne : ∀ a, a ≠ nodesBase - 1 → st9.mem a = st8.mem a := fun a ha => by
          dsimp [st9]; rw [Function.update_of_ne ha]
        have hm9_ge : ∀ a, nodesBase ≤ a → st9.mem a = st8.mem a := fun a ha => hm9_ne a (by omega)
        have hmem9_oth_x : ∀ off < NODE_STRIDE, off ≠ OFF_AF_PTR → off ≠ OFF_AB_PTR → off ≠ OFF_FLOW_PTR →
            off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL → off ≠ OFF_HAS_TAG → off ≠ OFF_TAG_PTR →
            off ≠ OFF_TAG_NEG → st9.mem (ptr + off) = mem₀ (ptr + off) := by
          intro off hoff h1 h2 h3 h4 h5 h6 h7 h8
          rw [hm9_ge _ (by omega), hmem8_oth off hoff h6 h7 h8, hmem7_oth_x off hoff h1 h2 h3 h4 h5]
        rcases applyTagBody_post_frame_children hnb harena hz hx1 hl_m hr_m hx_l hx_r nhs5678 hm9_hp hm9_ne with
          ⟨hmem9_node_ne, hheap9, hframe9, hl_m', hr_m', hl_steps_eq, hr_steps_eq⟩
        have hstep_agree_x : ∀ off < NODE_STRIDE,
            off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL → off ≠ OFF_HAS_TAG →
            off ≠ OFF_TAG_PTR → off ≠ OFF_TAG_NEG →
            st9.mem (ptr + off) = st5.mem (ptr + off) := fun off hoff h1 h2 h3 h4 h5 => by
          rw [hm9_ge _ (by omega), hmem8_oth off hoff h3 h4 h5, hmem7_oth off hoff h2, hmem6_oth off hoff h1]
        have nhs678 : NodeHeapStepMem arenaHi ptr hp5 hp8 st5.mem st8.mem :=
          nodeHeapStepMem_trans (nodeHeapStepMem_trans nhs6 nhs7) nhs8
        have hhp_ag : ∀ a, arenaHi ≤ a → a < hp5 → st9.mem a = st5.mem a := fun a ha1 ha2 => by
          rw [hm9_ge a (by dsimp only [arenaHi] at ha1; omega)]
          exact nhs678.2.2.2 a ha1 ha2
        have hown_eq := applyTagBody_post_own_eq hhe he1 (htx.nodeOwn_fits x (by simp [AuxTree.toList]))
          hdmod hfit nhs5 hstep_agree_x hhp_ag
          (hmem9_oth_x OFF_HASE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
          ⟨hmem5_oth OFF_COST_FWD (by decide) (by decide) (by decide) (by decide),
           hmem5_oth OFF_COST_BWD (by decide) (by decide) (by decide) (by decide)⟩
          hhe5_post
        have h8_zero' : nodeField st7.mem nodesBase l.rootId OFF_MIN1_HAS +
              nodeField st7.mem nodesBase r.rootId OFF_MIN1_HAS = 0 →
            (∀ off < NODE_STRIDE, st8.mem (ptr + off) = st7.mem (ptr + off)) ∧ hp8 = hp7 :=
          fun h => ⟨fun _ _ => congrFun (h8_zero h).1 _, (h8_zero h).2⟩
        have h8_nz' : nodeField st7.mem nodesBase l.rootId OFF_MIN1_HAS +
              nodeField st7.mem nodesBase r.rootId OFF_MIN1_HAS ≠ 0 →
            nodeField st8.mem nodesBase x OFF_HAS_TAG = 1 ∧
            NumPtrOk st8.mem arenaHi hp8 h L (nodeField st8.mem nodesBase x OFF_TAG_PTR) ∧
            nodeField st8.mem nodesBase x OFF_TAG_NEG =
              (if st7.mem (ptr + OFF_HAS_TAG) = 0 then tNeg else st7.mem (ptr + OFF_TAG_NEG)) ∧
            (st7.mem (ptr + OFF_HAS_TAG) = 0 → nodeField st8.mem nodesBase x OFF_TAG_PTR = tPtr) ∧
            (st7.mem (ptr + OFF_HAS_TAG) ≠ 0 →
              intVal st8.mem (nodeField st8.mem nodesBase x OFF_TAG_PTR) h L =
                wrap h L (if st7.mem (ptr + OFF_TAG_NEG) = tNeg
                  then intVal st7.mem (st7.mem (ptr + OFF_TAG_PTR)) h L + intVal st7.mem tPtr h L
                  else intVal st7.mem (st7.mem (ptr + OFF_TAG_PTR)) h L - intVal st7.mem tPtr h L)) := fun h =>
          let r := h8_nz h
          ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, fun hne => r.2.2.2.2 (by dsimp only [ptr] at hht_le7 hne; omega)⟩
        have hhe5_zero' : mem₀ (ptr + OFF_HASE) = 0 →
            ∀ off < NODE_STRIDE, st5.mem (ptr + off) = mem₀ (ptr + off) :=
          fun h _ _ => congrFun (hhe5_zero h) _
        have htag_and_steps := applyTagBody_post_tag_steps hnb h0 hht htn htag1 htag0 hl_m hr_m hx_l hx_r
          htNeg htPtr hdmod hfit hm9_ne hheap9 hmem9_node_ne hmem7_node_le h0_m1_7 hmem7_oth_x nhs567
          hl_steps_eq hr_steps_eq hown_eq h8_zero' h8_nz'
          (hmem9_oth_x OFF_REV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        rcases applyTagBody_post_min_vals hm9_ge
            (hmem5_oth OFF_MIN1_VAL (by decide) (by decide) (by decide) (by decide)) hm2_6_eq
            h7_lo h8_lo nhs5 nhs56 nhs7 nhs8 hout_m1_ok hout_m2_ok hint6 hint7 htNeg htPtr
            hm1_one hm2h pm1 pm2 hdmod hagg.2.2.2.2.1 hagg.2.2.2.2.2 hfit with
          ⟨hm1_val9, hm2_val9⟩
        have hm1_val_eq : st9.mem (ptr + OFF_MIN1_VAL) = out_m1 := by
          rw [hm9_ge _ (by omega), hmem8_oth OFF_MIN1_VAL (by decide) (by decide) (by decide) (by decide),
            hmem7_oth OFF_MIN1_VAL (by decide) (by decide), hmem6_m1]
        have hm2_val_eq : st9.mem (ptr + OFF_MIN2_VAL) = out_m2 := by
          rw [hm9_ge _ (by omega), hmem8_oth OFF_MIN2_VAL (by decide) (by decide) (by decide) (by decide),
            hmem7_m2]
        rcases applyTagBody_post_treeMemMatch hnb h0 htx hx_l hx_r htNeg h6_lo h7_lo h8_lo hm9_hp hm9_ne
            nhs5 nhs6 nhs7 nhs8 nhs5678 hmem6_oth hmem7_oth hmem8_oth hmem9_oth_x hmem7_oth_x
            hmem9_node_ne hmem7_node_le h0_m1_7 hheap9 hhe5_zero' hhe5_post h8_zero' h8_nz'
            hm1_val_eq hm2_val_eq hout_m1_ok hout_m2_ok hm1_val9 hm2_val9 hm1_one hl_m' hr_m' htag_and_steps with
          ⟨ht9, hnf_eq, haddr_eq⟩
        refine ⟨st9, _, hrun_full, ?_, by rw [hm9_hp]; omega, ht9, htag_and_steps.2.2, hnf_eq, haddr_eq, hframe9⟩
        · unfold K_APPLY_TAG
          simp only [nodePtrExpr, fieldLoadExpr, fieldAddrExpr, Expr.size] at hc5 hc6 hc7 hc8 ⊢
          omega

end

end MinCostFlow.LinkCut.Prog
