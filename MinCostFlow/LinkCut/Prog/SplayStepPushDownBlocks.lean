module

public import MinCostFlow.LinkCut.Prog.SplayStepPushDownPost

namespace MinCostFlow.LinkCut.Prog

/-!
Modular statement executors and base-case specification for `pushDownBody`:
- `runs_seq2_normal` and `runs_seq5_normal` for composing `.normal` statement prefixes,
- `pushDownBody_zero_triple` for node `0`,
- `revChild_exec`, `clearTagFields_exec`, `applyTagChild_exec`.
-/

open WordRAM MinCostFlow.Num

@[expose] public section

theorem runs_seq2_normal {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ rest : Stmt} {st₀ st₂ st₃ : State} {o : Outcome} {c₁₂ c₃ : ℕ}
    (h12 : Runs w p ω (s₁ ;; s₂) st₀ .normal st₂ c₁₂)
    (h3 : Runs w p ω rest st₂ o st₃ c₃) :
    Runs w p ω (s₁ ;; s₂ ;; rest) st₀ o st₃ (c₁₂ + c₃ + 1) := by
  rcases runs_seq_iff.mp h12 with ⟨_, _, _, hret, _⟩ | ⟨st₁, c₁, c₂, h1, h2, hceq⟩
  · cases hret
  · have hseq := runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂ + c₃ + 1, h1,
      runs_seq_iff.mpr (Or.inr ⟨st₂, c₂, c₃, h2, h3, rfl⟩), rfl⟩)
    simpa [hceq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hseq

theorem runs_seq5_normal {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ s₃ s₄ s₅ rest : Stmt} {st₀ st₅ st₆ : State} {o : Outcome} {c₁₅ c₆ : ℕ}
    (h15 : Runs w p ω (s₁ ;; s₂ ;; s₃ ;; s₄ ;; s₅) st₀ .normal st₅ c₁₅)
    (h6 : Runs w p ω rest st₅ o st₆ c₆) :
    Runs w p ω (s₁ ;; s₂ ;; s₃ ;; s₄ ;; s₅ ;; rest) st₀ o st₆ (c₁₅ + c₆ + 1) := by
  rcases runs_seq_iff.mp h15 with ⟨_, _, _, hret, _⟩ | ⟨st₁, c₁, c₂₅, h1, h25, hceq1⟩
  · cases hret
  · rcases runs_seq_iff.mp h25 with ⟨_, _, _, hret, _⟩ | ⟨st₂, c₂, c₃₅, h2, h35, hceq2⟩
    · cases hret
    · rcases runs_seq_iff.mp h35 with ⟨_, _, _, hret, _⟩ | ⟨st₃, c₃, c₄₅, h3, h45, hceq3⟩
      · cases hret
      · have h5rest := runs_seq2_normal h45 h6
        have hseq := runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂ + (c₃ + (c₄₅ + c₆ + 1) + 1) + 1, h1,
          runs_seq_iff.mpr (Or.inr ⟨st₂, c₂, c₃ + (c₄₅ + c₆ + 1) + 1, h2,
            runs_seq_iff.mpr (Or.inr ⟨st₃, c₃, c₄₅ + c₆ + 1, h3, h5rest, rfl⟩), rfl⟩), rfl⟩)
        simpa [hceq1, hceq2, hceq3, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hseq

theorem pushDown_tag_heap_lt {hp L W : ℕ}
    (h : hp + K_PUSH_DOWN L < W) : hp + 2 * K_APPLY_TAG L < W := by
  have hle : 2 * K_APPLY_TAG L ≤ K_PUSH_DOWN L := by
    have h1 : 2 * K_APPLY_TAG L = 1400 * (L + 1) := by simp [K_APPLY_TAG]; ring
    have h2 : K_PUSH_DOWN L = 2200 * (L + 1) := rfl
    rw [h1, h2]
    exact Nat.mul_le_mul_right (L + 1) (by decide)
  omega

theorem pushDown_total_cost_lt {hp_diff c_p1 c_p2 L : ℕ}
    (h1 : c_p1 ≤ 2 * K_REV_NODE + 40)
    (h2 : c_p2 + hp_diff ≤ 2 * K_APPLY_TAG L + 80) :
    1 + (6 + (5 + ((1 + c_p1 + 1) + c_p2 + 1) + 1) + 1) + 1 + hp_diff ≤ K_PUSH_DOWN L := by
  have hrev : 2 * K_REV_NODE = 600 := by decide
  have htag : 2 * K_APPLY_TAG L = 1400 * (L + 1) := by simp [K_APPLY_TAG]; ring
  have hpd : K_PUSH_DOWN L = 1400 * (L + 1) + 800 * (L + 1) := by
    simp [K_PUSH_DOWN]; ring
  have h800 : 800 ≤ 800 * (L + 1) := Nat.le_mul_of_pos_right 800 (Nat.succ_pos L)
  omega

theorem pushDown_norev_cost_lt {hp_diff c_p2 L : ℕ}
    (h2 : c_p2 + hp_diff ≤ 2 * K_APPLY_TAG L + 80) :
    1 + (6 + (5 + (3 + c_p2 + 1) + 1) + 1) + 1 + hp_diff ≤ K_PUSH_DOWN L := by
  have htag : 2 * K_APPLY_TAG L = 1400 * (L + 1) := by simp [K_APPLY_TAG]; ring
  have hpd : K_PUSH_DOWN L = 1400 * (L + 1) + 800 * (L + 1) := by
    simp [K_PUSH_DOWN]; ring
  have h800 : 800 ≤ 800 * (L + 1) := Nat.le_mul_of_pos_right 800 (Nat.succ_pos L)
  omega

theorem pushDownBody_zero_triple {w L nodesBase : ℕ} (p : Program) (sp : SplayProcs)
    (mem₀ : ℕ → ℕ) (pos : ℕ) (hw : 0 < 2 ^ w) :
    Triple w p
      (fun st => st = startState [nodesBase, 0] mem₀ pos)
      (pushDownBody sp)
      (retPost fun v st' => v = 0 ∧ st'.mem = mem₀)
      (fun _ => K_PUSH_DOWN L) := by
  intro st ω hst
  subst hst
  refine runs_start_le ?_
  have hcond : (Expr.reg 1).eval w (startState [nodesBase, 0] mem₀ pos) = some 0 := by
    simp [startState, Expr.eval]
  refine ⟨.returned 0, startState [nodesBase, 0] mem₀ pos, 4, ?_, ⟨rfl, rfl⟩,
    by dsimp only; unfold K_PUSH_DOWN; omega⟩
  refine runs_cond_iff.mpr ⟨0, 2, hcond, ?_, rfl⟩
  exact runs_ret_iff.mpr ⟨0, Expr.eval_const hw, rfl, rfl, rfl⟩

theorem revChild_exec {w h L nodesBase cap x childOff : ℕ}
    {p : Program} {sp : SplayProcs} {q : AuxTree}
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hx2 : x ≤ cap) (hoff : childOff < NODE_STRIDE)
    (st0 : State)
    (hr0 : st0.regs 0 = nodesBase)
    (hr2 : st0.regs 2 = nodesBase + NODE_STRIDE * x)
    (hchild : nodeField st0.mem nodesBase x childOff = q.rootId)
    (hq : TreeMemMatch w h L st0.mem nodesBase cap q x 0)
    (hq_nd : q.toList.Nodup) :
    ∀ ω, ∃ st' c,
      Runs w p ω
        (Stmt.assign 4 (fieldLoadExpr 2 childOff) ;; Stmt.call 5 sp.revNode [.reg 0, .reg 4])
        st0 .normal st' c ∧
      c ≤ K_REV_NODE + 12 ∧
      st'.regs 0 = nodesBase ∧
      st'.regs 2 = nodesBase + NODE_STRIDE * x ∧
      TreeMemMatch w h L st'.mem nodesBase cap q.revRoot x 0 ∧
      evalMemSteps st'.mem nodesBase h L q.revRoot false 0 =
        (evalMemSteps st0.mem nodesBase h L q false 0).reverse.map RawStep.flip ∧
      q.revRoot.evalInorder (revFlag st'.mem nodesBase) false =
        (q.evalInorder (revFlag st0.mem nodesBase) false).reverse ∧
      st'.mem (nodesBase - 1) = st0.mem (nodesBase - 1) ∧
      (∀ u, ∀ off, IsStaticPayloadOff off →
        nodeField st'.mem nodesBase u off = nodeField st0.mem nodesBase u off) ∧
      (∀ addr, addr < nodesBase + NODE_STRIDE * q.rootId ∨
          nodesBase + NODE_STRIDE * q.rootId + NODE_STRIDE ≤ addr →
        st'.mem addr = st0.mem addr) ∧
      MemPreservedOutside (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        st0.mem st'.mem := by
  intro ω
  let st1 : State := { mem := st0.mem, regs := Function.update st0.regs 4 q.rootId, pos := st0.pos }
  have hev : (fieldLoadExpr 2 childOff).eval w st0 = some q.rootId := by
    have hld := eval_fieldLoadExpr hr2 (nodeAddr_lt_pow hbase hx2 hoff)
    have hm : st0.mem (nodesBase + NODE_STRIDE * x + childOff) = q.rootId := hchild
    simpa [hm] using hld
  have hr1 : Runs w p ω (Stmt.assign 4 (fieldLoadExpr 2 childOff)) st0 .normal st1 5 :=
    runs_assign_iff.mpr ⟨q.rootId, hev, rfl, rfl, rfl⟩
  have hr1_0 : st1.regs 0 = nodesBase := by dsimp [st1]; rw [Function.update_of_ne (by decide)]; exact hr0
  have hr1_2 : st1.regs 2 = nodesBase + NODE_STRIDE * x := by
    dsimp [st1]; rw [Function.update_of_ne (by decide)]; exact hr2
  have hr1_4 : st1.regs 4 = q.rootId := by dsimp [st1]; exact Function.update_self _ _ _
  have hargs : evalArgs w st1 [.reg 0, .reg 4] = some [nodesBase, q.rootId] := by
    simp [evalArgs, Expr.eval, hr1_0, hr1_4]
  rcases revNodeBody_subtree_runs st1.pos hbase hq hq_nd ω with
    ⟨st_b, c_b, hrun_b, hc_b, hm_b, hsteps_b, heval_b, hhp_b, hstat_b, hout_b, hpres_b⟩
  let st2 : State := { mem := st_b.mem, regs := Function.update st1.regs 5 0, pos := st_b.pos }
  have hr2_0 : st2.regs 0 = nodesBase := by dsimp [st2]; rw [Function.update_of_ne (by decide)]; exact hr1_0
  have hr2_2 : st2.regs 2 = nodesBase + NODE_STRIDE * x := by
    dsimp [st2]; rw [Function.update_of_ne (by decide)]; exact hr1_2
  have hcall : Runs w p ω (Stmt.call 5 sp.revNode [.reg 0, .reg 4]) st1 .normal st2 (2 + c_b + 1) :=
    runs_call_iff.mpr ⟨[nodesBase, q.rootId], revNodeBody, .returned 0, st_b, c_b,
      hargs, hp_ok.revNode_eq, hrun_b, rfl, rfl, rfl⟩
  exact ⟨st2, 5 + (2 + c_b + 1) + 1, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hr1, hcall, rfl⟩),
    by omega, hr2_0, hr2_2, hm_b, hsteps_b, heval_b, hhp_b, hstat_b, hout_b, hpres_b⟩

theorem clearTagFields_exec {w nodesBase cap x : ℕ} {p : Program}
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w) (hx2 : x ≤ cap)
    (st0 : State)
    (hr0 : st0.regs 0 = nodesBase)
    (hr2 : st0.regs 2 = nodesBase + NODE_STRIDE * x) :
    ∀ ω, ∃ st' c,
      Runs w p ω
        (Stmt.assign 4 (fieldLoadExpr 2 OFF_TAG_PTR) ;;
         Stmt.assign 5 (fieldLoadExpr 2 OFF_TAG_NEG) ;;
         Stmt.store (fieldAddrExpr 2 OFF_HAS_TAG) (.const 0) ;;
         Stmt.store (fieldAddrExpr 2 OFF_TAG_PTR) (.const 0) ;;
         Stmt.store (fieldAddrExpr 2 OFF_TAG_NEG) (.const 0))
        st0 .normal st' c ∧
      c ≤ 30 ∧
      st'.regs 0 = nodesBase ∧
      st'.regs 2 = nodesBase + NODE_STRIDE * x ∧
      st'.regs 4 = nodeField st0.mem nodesBase x OFF_TAG_PTR ∧
      st'.regs 5 = nodeField st0.mem nodesBase x OFF_TAG_NEG ∧
      nodeField st'.mem nodesBase x OFF_HAS_TAG = 0 ∧
      nodeField st'.mem nodesBase x OFF_TAG_PTR = 0 ∧
      nodeField st'.mem nodesBase x OFF_TAG_NEG = 0 ∧
      (∀ off < NODE_STRIDE, off ≠ OFF_HAS_TAG → off ≠ OFF_TAG_PTR → off ≠ OFF_TAG_NEG →
        nodeField st'.mem nodesBase x off = nodeField st0.mem nodesBase x off) ∧
      (∀ a, a < nodesBase + NODE_STRIDE * x ∨
          nodesBase + NODE_STRIDE * x + NODE_STRIDE ≤ a →
        st'.mem a = st0.mem a) := by
  intro ω
  have hw0 : (0 : ℕ) < 2 ^ w := by unfold NODE_STRIDE at hbase; omega
  let ptr := nodesBase + NODE_STRIDE * x
  have hxa : ∀ off < NODE_STRIDE, ptr + off < 2 ^ w :=
    fun off hoff => nodeAddr_lt_pow hbase hx2 hoff
  let tPtr := nodeField st0.mem nodesBase x OFF_TAG_PTR
  let tNeg := nodeField st0.mem nodesBase x OFF_TAG_NEG
  let st1 : State := { mem := st0.mem, regs := Function.update st0.regs 4 tPtr, pos := st0.pos }
  have hr1_0 : st1.regs 0 = nodesBase := by dsimp [st1]; rw [Function.update_of_ne (by decide)]; exact hr0
  have hr1_2 : st1.regs 2 = ptr := by dsimp [st1]; rw [Function.update_of_ne (by decide)]; exact hr2
  have hr1_4 : st1.regs 4 = tPtr := by dsimp [st1]; exact Function.update_self _ _ _
  let st2 : State := { mem := st0.mem, regs := Function.update st1.regs 5 tNeg, pos := st0.pos }
  have hr2_0 : st2.regs 0 = nodesBase := by dsimp [st2]; rw [Function.update_of_ne (by decide)]; exact hr1_0
  have hr2_2 : st2.regs 2 = ptr := by dsimp [st2]; rw [Function.update_of_ne (by decide)]; exact hr1_2
  have hr2_4 : st2.regs 4 = tPtr := by dsimp [st2]; rw [Function.update_of_ne (by decide)]; exact hr1_4
  have hr2_5 : st2.regs 5 = tNeg := by dsimp [st2]; exact Function.update_self _ _ _
  let mem1 := Function.update st0.mem (ptr + OFF_HAS_TAG) 0
  let mem2 := Function.update mem1 (ptr + OFF_TAG_PTR) 0
  let mem3 := Function.update mem2 (ptr + OFF_TAG_NEG) 0
  let st3 : State := { mem := mem1, regs := st2.regs, pos := st0.pos }
  let st4 : State := { mem := mem2, regs := st2.regs, pos := st0.pos }
  let st5 : State := { mem := mem3, regs := st2.regs, pos := st0.pos }
  have h1 : Runs w p ω (Stmt.assign 4 (fieldLoadExpr 2 OFF_TAG_PTR)) st0 .normal st1 5 :=
    runs_assign_iff.mpr ⟨tPtr, by simpa [ptr, nodeField, tPtr] using eval_fieldLoadExpr hr2 (hxa OFF_TAG_PTR (by decide)), rfl, rfl, rfl⟩
  have h2 : Runs w p ω (Stmt.assign 5 (fieldLoadExpr 2 OFF_TAG_NEG)) st1 .normal st2 5 :=
    runs_assign_iff.mpr ⟨tNeg, by simpa [ptr, nodeField, tNeg] using eval_fieldLoadExpr hr1_2 (hxa OFF_TAG_NEG (by decide)), rfl, rfl, rfl⟩
  have h3 : Runs w p ω (Stmt.store (fieldAddrExpr 2 OFF_HAS_TAG) (.const 0)) st2 .normal st3 5 :=
    runs_store_iff.mpr ⟨ptr + OFF_HAS_TAG, 0, eval_fieldAddrExpr hr2_2 (hxa OFF_HAS_TAG (by decide)), Expr.eval_const hw0, rfl, rfl, rfl⟩
  have h4 : Runs w p ω (Stmt.store (fieldAddrExpr 2 OFF_TAG_PTR) (.const 0)) st3 .normal st4 5 :=
    runs_store_iff.mpr ⟨ptr + OFF_TAG_PTR, 0, eval_fieldAddrExpr hr2_2 (hxa OFF_TAG_PTR (by decide)), Expr.eval_const hw0, rfl, rfl, rfl⟩
  have h5 : Runs w p ω (Stmt.store (fieldAddrExpr 2 OFF_TAG_NEG) (.const 0)) st4 .normal st5 5 :=
    runs_store_iff.mpr ⟨ptr + OFF_TAG_NEG, 0, eval_fieldAddrExpr hr2_2 (hxa OFF_TAG_NEG (by decide)), Expr.eval_const hw0, rfl, rfl, rfl⟩
  have hseq := runs_seq_iff.mpr (Or.inr ⟨st1, _, _, h1,
    runs_seq_iff.mpr (Or.inr ⟨st2, _, _, h2,
      runs_seq_iff.mpr (Or.inr ⟨st3, _, _, h3,
        runs_seq_iff.mpr (Or.inr ⟨st4, _, _, h4, h5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨st5, 29, hseq, by decide, hr2_0, hr2_2, hr2_4, hr2_5, ?_, ?_, ?_, ?_, ?_⟩
  · simp [st5, mem3, mem2, mem1, nodeField, ptr, OFF_HAS_TAG, OFF_TAG_PTR, OFF_TAG_NEG]
  · simp [st5, mem3, mem2, mem1, nodeField, ptr, OFF_TAG_PTR, OFF_TAG_NEG]
  · simp [st5, mem3, nodeField, ptr, Function.update_self]
  · intro off _ h1' h2' h3'
    simp only [st5, nodeField, ptr, mem3, mem2, mem1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  · intro a ha
    have hne1 : a ≠ ptr + OFF_HAS_TAG := by dsimp [ptr]; unfold OFF_HAS_TAG NODE_STRIDE at *; omega
    have hne2 : a ≠ ptr + OFF_TAG_PTR := by dsimp [ptr]; unfold OFF_TAG_PTR NODE_STRIDE at *; omega
    have hne3 : a ≠ ptr + OFF_TAG_NEG := by dsimp [ptr]; unfold OFF_TAG_NEG NODE_STRIDE at *; omega
    simp only [st5, mem3, mem2, mem1]
    rw [Function.update_of_ne hne3, Function.update_of_ne hne2, Function.update_of_ne hne1]

theorem applyTagChild_exec {w h L nodesBase cap x childOff tPtr tNeg : ℕ}
    {p : Program} {sp : SplayProcs} {q : AuxTree} {d : ℤ}
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase)
    (hx2 : x ≤ cap) (hoff : childOff < NODE_STRIDE)
    (st0 : State)
    (hL_hdr : st0.mem (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ st0.mem (nodesBase - 1))
    (hz : ZeroFrom st0.mem (st0.mem (nodesBase - 1)))
    (hhp_lt : st0.mem (nodesBase - 1) + K_APPLY_TAG L < 2 ^ w)
    (h0 : SlotZeroOk st0.mem nodesBase)
    (hr0 : st0.regs 0 = nodesBase)
    (hr2 : st0.regs 2 = nodesBase + NODE_STRIDE * x)
    (hr4 : st0.regs 4 = tPtr)
    (hr5 : st0.regs 5 = tNeg)
    (hchild : nodeField st0.mem nodesBase x childOff = q.rootId)
    (hq : TreeMemMatch w h L st0.mem nodesBase cap q x 0)
    (hq_nd : q.toList.Nodup)
    (htNeg : tNeg ≤ 1)
    (htPtr : NumPtrOk st0.mem (nodesBase + NODE_STRIDE * (cap + 1)) (st0.mem (nodesBase - 1)) h L tPtr)
    (hdmod : d % (capacity h L : ℤ) =
      (if tNeg = 0 then intVal st0.mem tPtr h L else -intVal st0.mem tPtr h L) % (capacity h L : ℤ))
    (hfit : StepsShiftFit h L (evalMemSteps st0.mem nodesBase h L q false 0) d) :
    ∀ ω, ∃ st' c,
      Runs w p ω
        (Stmt.assign 6 (fieldLoadExpr 2 childOff) ;;
         Stmt.call 7 sp.applyTag [.reg 0, .reg 6, .reg 4, .reg 5])
        st0 .normal st' c ∧
      c + (st'.mem (nodesBase - 1) - st0.mem (nodesBase - 1)) ≤ K_APPLY_TAG L + 11 ∧
      11 ≤ c ∧
      st'.regs 0 = nodesBase ∧
      st'.regs 2 = nodesBase + NODE_STRIDE * x ∧
      st'.regs 4 = tPtr ∧
      st'.regs 5 = tNeg ∧
      st0.mem (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      TreeMemMatch w h L st'.mem nodesBase cap q x 0 ∧
      evalMemSteps st'.mem nodesBase h L q false 0 =
        (evalMemSteps st0.mem nodesBase h L q false 0).map (fun s => s.addDelta d) ∧
      (∀ u ≤ cap, ∀ off < NODE_STRIDE,
        off ≠ OFF_AF_PTR → off ≠ OFF_AB_PTR → off ≠ OFF_FLOW_PTR →
        off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL →
        off ≠ OFF_HAS_TAG → off ≠ OFF_TAG_PTR → off ≠ OFF_TAG_NEG →
        nodeField st'.mem nodesBase u off = nodeField st0.mem nodesBase u off) ∧
      (∀ addr, addr < nodesBase + NODE_STRIDE * q.rootId ∨
          nodesBase + NODE_STRIDE * q.rootId + NODE_STRIDE ≤ addr →
        addr ≠ nodesBase - 1 → addr < st0.mem (nodesBase - 1) →
        st'.mem addr = st0.mem addr) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) st0.mem st'.mem := by
  intro ω
  let st1 : State := { mem := st0.mem, regs := Function.update st0.regs 6 q.rootId, pos := st0.pos }
  have hev : (fieldLoadExpr 2 childOff).eval w st0 = some q.rootId := by
    have hld := eval_fieldLoadExpr hr2 (nodeAddr_lt_pow hbase hx2 hoff)
    have hm : st0.mem (nodesBase + NODE_STRIDE * x + childOff) = q.rootId := hchild
    simpa [hm] using hld
  have hr1 : Runs w p ω (Stmt.assign 6 (fieldLoadExpr 2 childOff)) st0 .normal st1 5 :=
    runs_assign_iff.mpr ⟨q.rootId, hev, rfl, rfl, rfl⟩
  have hr1_0 : st1.regs 0 = nodesBase := by dsimp [st1]; rw [Function.update_of_ne (by decide)]; exact hr0
  have hr1_2 : st1.regs 2 = nodesBase + NODE_STRIDE * x := by
    dsimp [st1]; rw [Function.update_of_ne (by decide)]; exact hr2
  have hr1_4 : st1.regs 4 = tPtr := by dsimp [st1]; rw [Function.update_of_ne (by decide)]; exact hr4
  have hr1_5 : st1.regs 5 = tNeg := by dsimp [st1]; rw [Function.update_of_ne (by decide)]; exact hr5
  have hr1_6 : st1.regs 6 = q.rootId := by dsimp [st1]; exact Function.update_self _ _ _
  have hargs : evalArgs w st1 [.reg 0, .reg 6, .reg 4, .reg 5] =
      some [nodesBase, q.rootId, tPtr, tNeg] := by
    simp [evalArgs, Expr.eval, hr1_0, hr1_6, hr1_4, hr1_5]
  rcases applyTagBody_runs_subtree st1.pos hp_ok hbase hnb hL_hdr harena hz hhp_lt h0 hq hq_nd
      htNeg htPtr hdmod hfit ω with
    ⟨st_b, c_b, hrun_b, hc_b, hhp_b, hm_b, hsteps_b, hnf_b, hout_b, hlct_b⟩
  let st2 : State := { mem := st_b.mem, regs := Function.update st1.regs 7 0, pos := st_b.pos }
  have hr2_0 : st2.regs 0 = nodesBase := by dsimp [st2]; rw [Function.update_of_ne (by decide)]; exact hr1_0
  have hr2_2 : st2.regs 2 = nodesBase + NODE_STRIDE * x := by
    dsimp [st2]; rw [Function.update_of_ne (by decide)]; exact hr1_2
  have hr2_4 : st2.regs 4 = tPtr := by dsimp [st2]; rw [Function.update_of_ne (by decide)]; exact hr1_4
  have hr2_5 : st2.regs 5 = tNeg := by dsimp [st2]; rw [Function.update_of_ne (by decide)]; exact hr1_5
  have hcall : Runs w p ω (Stmt.call 7 sp.applyTag [.reg 0, .reg 6, .reg 4, .reg 5]) st1 .normal st2
      (4 + c_b + 1) :=
    runs_call_iff.mpr ⟨[nodesBase, q.rootId, tPtr, tNeg], applyTagBody sp, .returned 0, st_b, c_b,
      hargs, hp_ok.applyTag_eq, hrun_b, rfl, rfl, rfl⟩
  exact ⟨st2, 5 + (4 + c_b + 1) + 1, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hr1, hcall, rfl⟩),
    by dsimp [st2, st1] at *; omega, by omega,
    hr2_0, hr2_2, hr2_4, hr2_5, hhp_b, hm_b, hsteps_b, hnf_b, hout_b, hlct_b⟩

end

end MinCostFlow.LinkCut.Prog
