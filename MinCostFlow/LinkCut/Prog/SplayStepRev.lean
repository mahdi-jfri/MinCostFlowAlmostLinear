module

public import MinCostFlow.LinkCut.Prog.SplayStepBase

namespace MinCostFlow.LinkCut.Prog

/-!
Word-RAM specification for `swapFieldsStmt` and `revNodeBody`, including
`revNodeMem`, `revNodeBody_zero_triple`, `revNodeBody_runs_nonzero`,
`revNodeMem_treeMemMatch`, and `revNodeBody_subtree_runs`.
-/

open WordRAM MinCostFlow.Num

@[expose] public section

theorem eval_sub_one_reg {w r : ℕ} {st : State} (hw : 1 < 2 ^ w) :
    (Expr.bin .sub (.const 1) (.reg r)).eval w st = some (1 - st.regs r) :=
  Expr.eval_sub (Expr.eval_const hw) (Expr.eval_reg w r st) hw

theorem swapFieldsStmt_triple {w ptrReg f1 f2 tmp1 tmp2 ptr : ℕ} (p : Program)
    (st₀ : State) (hst : st₀.regs ptrReg = ptr)
    (htmp1_ne_ptr : tmp1 ≠ ptrReg) (htmp2_ne_ptr : tmp2 ≠ ptrReg) (htmp12 : tmp1 ≠ tmp2)
    (_hne : f1 ≠ f2) (hlt1 : ptr + f1 < 2 ^ w) (hlt2 : ptr + f2 < 2 ^ w) :
    Triple w p
      (fun st => st = st₀)
      (swapFieldsStmt ptrReg f1 f2 tmp1 tmp2)
      (normalPost fun st' =>
        st'.mem = Function.update (Function.update st₀.mem (ptr + f1) (st₀.mem (ptr + f2)))
          (ptr + f2) (st₀.mem (ptr + f1)) ∧
        (∀ r, r ≠ tmp1 → r ≠ tmp2 → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos)
      (fun _ => 24) := by
  intro st ω hst0
  subst hst0
  refine runs_start_le ?_
  dsimp only [swapFieldsStmt]
  refine runs_seq_assign_le (v := st.mem (ptr + f1)) (eval_fieldLoadExpr hst hlt1) ?_
  refine runs_seq_assign_le (v := st.mem (ptr + f2))
    (eval_fieldLoadExpr (by simp [Function.update_of_ne htmp1_ne_ptr.symm, hst]) hlt2) ?_
  refine runs_seq_store_le
    (eval_fieldAddrExpr (by simp [Function.update_of_ne htmp2_ne_ptr.symm,
      Function.update_of_ne htmp1_ne_ptr.symm, hst]) hlt1)
    (Expr.eval_reg _ _ _) ?_
  have hr_ptr : Function.update (Function.update st.regs tmp1 (st.mem (ptr + f1))) tmp2
      (st.mem (ptr + f2)) ptrReg = ptr := by
    simp [Function.update_of_ne htmp2_ne_ptr.symm, Function.update_of_ne htmp1_ne_ptr.symm, hst]
  have hr_tmp1 : Function.update (Function.update st.regs tmp1 (st.mem (ptr + f1))) tmp2
      (st.mem (ptr + f2)) tmp1 = st.mem (ptr + f1) := by
    simp [Function.update_of_ne htmp12, Function.update_self]
  refine runs_store_le (eval_fieldAddrExpr hr_ptr hlt2) (Expr.eval_reg_of_eq hr_tmp1) ?_ ?_
  · dsimp only [normalPost]
    refine ⟨?_, ?_, rfl⟩
    · funext a
      simp only [Function.update_apply]
      split_ifs <;> rfl
    · intro r hr1 hr2
      simp [Function.update_of_ne hr2, Function.update_of_ne hr1]
  · simp [fieldLoadExpr, fieldAddrExpr]

/-- Memory resulting from executing `revNodeBody` on a valid nonzero node `x`. -/
def revNodeMem (mem : ℕ → ℕ) (nodesBase x : ℕ) : ℕ → ℕ :=
  let ptr := nodesBase + NODE_STRIDE * x
  let m1 := Function.update (Function.update mem (ptr + OFF_LEFT) (mem (ptr + OFF_RIGHT)))
    (ptr + OFF_RIGHT) (mem (ptr + OFF_LEFT))
  let m2 := Function.update (Function.update m1 (ptr + OFF_MIN1_HAS) (mem (ptr + OFF_MIN2_HAS)))
    (ptr + OFF_MIN2_HAS) (mem (ptr + OFF_MIN1_HAS))
  let m3 := Function.update (Function.update m2 (ptr + OFF_MIN1_VAL) (mem (ptr + OFF_MIN2_VAL)))
    (ptr + OFF_MIN2_VAL) (mem (ptr + OFF_MIN1_VAL))
  let m4 := Function.update (Function.update m3 (ptr + OFF_MIN1_FIRST) (mem (ptr + OFF_MIN2_LAST)))
    (ptr + OFF_MIN2_LAST) (mem (ptr + OFF_MIN1_FIRST))
  let m5 := Function.update (Function.update m4 (ptr + OFF_MIN1_LAST) (mem (ptr + OFF_MIN2_FIRST)))
    (ptr + OFF_MIN2_FIRST) (mem (ptr + OFF_MIN1_LAST))
  let m6 := Function.update (Function.update m5 (ptr + OFF_CSUM_FWD) (mem (ptr + OFF_CSUM_BWD)))
    (ptr + OFF_CSUM_BWD) (mem (ptr + OFF_CSUM_FWD))
  let m7 := Function.update m6 (ptr + OFF_REV) (1 - mem (ptr + OFF_REV))
  let m8 := if mem (ptr + OFF_HASE) = 0 then m7 else
    let m8a := Function.update m7 (ptr + OFF_DIR) (1 - mem (ptr + OFF_DIR))
    let m8b := Function.update (Function.update m8a (ptr + OFF_AF_PTR) (mem (ptr + OFF_AB_PTR)))
      (ptr + OFF_AB_PTR) (mem (ptr + OFF_AF_PTR))
    Function.update (Function.update m8b (ptr + OFF_COST_FWD) (mem (ptr + OFF_COST_BWD)))
      (ptr + OFF_COST_BWD) (mem (ptr + OFF_COST_FWD))
  if mem (ptr + OFF_HAS_TAG) = 0 then m8 else
    Function.update m8 (ptr + OFF_TAG_NEG) (1 - mem (ptr + OFF_TAG_NEG))

theorem revNodeMem_outside_slot {mem : ℕ → ℕ} {nodesBase x addr : ℕ}
    (haddr : addr < nodesBase + NODE_STRIDE * x ∨
      nodesBase + NODE_STRIDE * x + NODE_STRIDE ≤ addr) :
    revNodeMem mem nodesBase x addr = mem addr := by
  have hne : ∀ off < NODE_STRIDE, addr ≠ nodesBase + NODE_STRIDE * x + off := by
    intro off hoff heq; subst heq; omega
  dsimp only [revNodeMem]
  split_ifs
  all_goals
    repeat (rw [Function.update_of_ne (hne _ (by decide))])
    try rfl

private theorem upd_node_ne {m : ℕ → ℕ} {ptr a b v : ℕ} (hab : b ≠ a) :
    Function.update m (ptr + a) v (ptr + b) = m (ptr + b) := by
  rw [Function.update_of_ne (by omega)]

private theorem upd_node_self {m : ℕ → ℕ} {ptr a v : ℕ} :
    Function.update m (ptr + a) v (ptr + a) = v :=
  Function.update_self _ _ _

private theorem revNodeMem_other {mem : ℕ → ℕ} {nodesBase x off : ℕ}
    (h1 : off ≠ OFF_LEFT) (h2 : off ≠ OFF_RIGHT)
    (h3 : off ≠ OFF_MIN1_HAS) (h4 : off ≠ OFF_MIN2_HAS)
    (h5 : off ≠ OFF_MIN1_VAL) (h6 : off ≠ OFF_MIN2_VAL)
    (h7 : off ≠ OFF_MIN1_FIRST) (h8 : off ≠ OFF_MIN2_LAST)
    (h9 : off ≠ OFF_MIN1_LAST) (h10 : off ≠ OFF_MIN2_FIRST)
    (h11 : off ≠ OFF_CSUM_FWD) (h12 : off ≠ OFF_CSUM_BWD)
    (h13 : off ≠ OFF_REV) (h14 : off ≠ OFF_DIR)
    (h15 : off ≠ OFF_AF_PTR) (h16 : off ≠ OFF_AB_PTR)
    (h17 : off ≠ OFF_COST_FWD) (h18 : off ≠ OFF_COST_BWD)
    (h19 : off ≠ OFF_TAG_NEG) :
    revNodeMem mem nodesBase x (nodesBase + NODE_STRIDE * x + off) =
      mem (nodesBase + NODE_STRIDE * x + off) := by
  dsimp only [revNodeMem]
  split_ifs <;> (repeat rw [upd_node_ne (by assumption)])

private theorem revNodeMem_pair1 {mem : ℕ → ℕ} {nodesBase x : ℕ} :
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_LEFT = nodeField mem nodesBase x OFF_RIGHT ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_RIGHT = nodeField mem nodesBase x OFF_LEFT ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_CSUM_FWD = nodeField mem nodesBase x OFF_CSUM_BWD ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_CSUM_BWD = nodeField mem nodesBase x OFF_CSUM_FWD ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_REV = 1 - nodeField mem nodesBase x OFF_REV := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    dsimp only [revNodeMem, nodeField]
    split_ifs
    all_goals
      repeat (first | exact upd_node_self | rw [upd_node_ne (by decide)])

private theorem revNodeMem_pair2 {mem : ℕ → ℕ} {nodesBase x : ℕ} :
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_MIN1_HAS = nodeField mem nodesBase x OFF_MIN2_HAS ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_MIN2_HAS = nodeField mem nodesBase x OFF_MIN1_HAS ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_MIN1_VAL = nodeField mem nodesBase x OFF_MIN2_VAL ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_MIN2_VAL = nodeField mem nodesBase x OFF_MIN1_VAL := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    dsimp only [revNodeMem, nodeField]
    split_ifs
    all_goals
      repeat (first | exact upd_node_self | rw [upd_node_ne (by decide)])

private theorem revNodeMem_pair3 {mem : ℕ → ℕ} {nodesBase x : ℕ} :
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_MIN1_FIRST = nodeField mem nodesBase x OFF_MIN2_LAST ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_MIN2_LAST = nodeField mem nodesBase x OFF_MIN1_FIRST ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_MIN1_LAST = nodeField mem nodesBase x OFF_MIN2_FIRST ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_MIN2_FIRST = nodeField mem nodesBase x OFF_MIN1_LAST := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    dsimp only [revNodeMem, nodeField]
    split_ifs
    all_goals
      repeat (first | exact upd_node_self | rw [upd_node_ne (by decide)])

private theorem revNodeMem_edgeFields {mem : ℕ → ℕ} {nodesBase x : ℕ} :
    (nodeField mem nodesBase x OFF_HASE ≠ 0 →
      nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_DIR = 1 - nodeField mem nodesBase x OFF_DIR ∧
      nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_AF_PTR = nodeField mem nodesBase x OFF_AB_PTR ∧
      nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_AB_PTR = nodeField mem nodesBase x OFF_AF_PTR ∧
      nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_COST_FWD = nodeField mem nodesBase x OFF_COST_BWD ∧
      nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_COST_BWD = nodeField mem nodesBase x OFF_COST_FWD) ∧
    (nodeField mem nodesBase x OFF_HASE = 0 →
      ∀ off, off = OFF_DIR ∨ off = OFF_AF_PTR ∨ off = OFF_AB_PTR ∨ off = OFF_COST_FWD ∨ off = OFF_COST_BWD →
        nodeField (revNodeMem mem nodesBase x) nodesBase x off = nodeField mem nodesBase x off) ∧
    (nodeField mem nodesBase x OFF_HAS_TAG ≠ 0 →
      nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_TAG_NEG = 1 - nodeField mem nodesBase x OFF_TAG_NEG) ∧
    (nodeField mem nodesBase x OFF_HAS_TAG = 0 →
      nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_TAG_NEG = nodeField mem nodesBase x OFF_TAG_NEG) := by
  refine ⟨fun hne => ⟨?_, ?_, ?_, ?_, ?_⟩, fun he0 off hoff => ?_, fun hht => ?_, fun hht => ?_⟩
  · dsimp only [revNodeMem, nodeField] at hne ⊢; rw [ite_eq_right hne]; split_ifs <;>
      repeat (first | exact upd_node_self | rw [upd_node_ne (by decide)])
  · dsimp only [revNodeMem, nodeField] at hne ⊢; rw [ite_eq_right hne]; split_ifs <;>
      repeat (first | exact upd_node_self | rw [upd_node_ne (by decide)])
  · dsimp only [revNodeMem, nodeField] at hne ⊢; rw [ite_eq_right hne]; split_ifs <;>
      repeat (first | exact upd_node_self | rw [upd_node_ne (by decide)])
  · dsimp only [revNodeMem, nodeField] at hne ⊢; rw [ite_eq_right hne]; split_ifs <;>
      repeat (first | exact upd_node_self | rw [upd_node_ne (by decide)])
  · dsimp only [revNodeMem, nodeField] at hne ⊢; rw [ite_eq_right hne]; split_ifs <;>
      repeat (first | exact upd_node_self | rw [upd_node_ne (by decide)])
  · rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
      · dsimp only [revNodeMem, nodeField] at he0 ⊢; rw [ite_eq_left he0]; split_ifs <;>
          repeat rw [upd_node_ne (by decide)]
  · dsimp only [revNodeMem, nodeField] at hht ⊢; rw [ite_eq_right hht]; exact upd_node_self
  · dsimp only [revNodeMem, nodeField] at hht ⊢; rw [ite_eq_left hht]; split_ifs <;>
      repeat rw [upd_node_ne (by decide)]

theorem revNodeMem_nodeField {mem : ℕ → ℕ} {nodesBase x : ℕ} :
    (∀ u ≠ x, ∀ off < NODE_STRIDE,
      nodeField (revNodeMem mem nodesBase x) nodesBase u off = nodeField mem nodesBase u off) ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_LEFT = nodeField mem nodesBase x OFF_RIGHT ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_RIGHT = nodeField mem nodesBase x OFF_LEFT ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_MIN1_HAS = nodeField mem nodesBase x OFF_MIN2_HAS ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_MIN2_HAS = nodeField mem nodesBase x OFF_MIN1_HAS ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_MIN1_VAL = nodeField mem nodesBase x OFF_MIN2_VAL ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_MIN2_VAL = nodeField mem nodesBase x OFF_MIN1_VAL ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_MIN1_FIRST = nodeField mem nodesBase x OFF_MIN2_LAST ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_MIN2_LAST = nodeField mem nodesBase x OFF_MIN1_FIRST ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_MIN1_LAST = nodeField mem nodesBase x OFF_MIN2_FIRST ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_MIN2_FIRST = nodeField mem nodesBase x OFF_MIN1_LAST ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_CSUM_FWD = nodeField mem nodesBase x OFF_CSUM_BWD ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_CSUM_BWD = nodeField mem nodesBase x OFF_CSUM_FWD ∧
    nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_REV = 1 - nodeField mem nodesBase x OFF_REV ∧
    (nodeField mem nodesBase x OFF_HASE ≠ 0 →
      nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_DIR = 1 - nodeField mem nodesBase x OFF_DIR ∧
      nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_AF_PTR = nodeField mem nodesBase x OFF_AB_PTR ∧
      nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_AB_PTR = nodeField mem nodesBase x OFF_AF_PTR ∧
      nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_COST_FWD = nodeField mem nodesBase x OFF_COST_BWD ∧
      nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_COST_BWD = nodeField mem nodesBase x OFF_COST_FWD) ∧
    (nodeField mem nodesBase x OFF_HASE = 0 →
      ∀ off, off = OFF_DIR ∨ off = OFF_AF_PTR ∨ off = OFF_AB_PTR ∨ off = OFF_COST_FWD ∨ off = OFF_COST_BWD →
        nodeField (revNodeMem mem nodesBase x) nodesBase x off = nodeField mem nodesBase x off) ∧
    (nodeField mem nodesBase x OFF_HAS_TAG ≠ 0 →
      nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_TAG_NEG = 1 - nodeField mem nodesBase x OFF_TAG_NEG) ∧
    (nodeField mem nodesBase x OFF_HAS_TAG = 0 →
      nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_TAG_NEG = nodeField mem nodesBase x OFF_TAG_NEG) ∧
    (∀ off, off ≠ OFF_LEFT → off ≠ OFF_RIGHT → off ≠ OFF_MIN1_HAS → off ≠ OFF_MIN2_HAS →
      off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL → off ≠ OFF_MIN1_FIRST → off ≠ OFF_MIN2_LAST →
      off ≠ OFF_MIN1_LAST → off ≠ OFF_MIN2_FIRST → off ≠ OFF_CSUM_FWD → off ≠ OFF_CSUM_BWD →
      off ≠ OFF_REV → off ≠ OFF_DIR → off ≠ OFF_AF_PTR → off ≠ OFF_AB_PTR →
      off ≠ OFF_COST_FWD → off ≠ OFF_COST_BWD → off ≠ OFF_TAG_NEG →
      nodeField (revNodeMem mem nodesBase x) nodesBase x off = nodeField mem nodesBase x off) := by
  refine ⟨?_, revNodeMem_pair1.1, revNodeMem_pair1.2.1, revNodeMem_pair2.1, revNodeMem_pair2.2.1,
    revNodeMem_pair2.2.2.1, revNodeMem_pair2.2.2.2, revNodeMem_pair3.1, revNodeMem_pair3.2.1,
    revNodeMem_pair3.2.2.1, revNodeMem_pair3.2.2.2, revNodeMem_pair1.2.2.1,
    revNodeMem_pair1.2.2.2.1, revNodeMem_pair1.2.2.2.2, revNodeMem_edgeFields.1,
    revNodeMem_edgeFields.2.1, revNodeMem_edgeFields.2.2.1, revNodeMem_edgeFields.2.2.2,
    fun off => revNodeMem_other⟩
  · intro u hux off hoff
    apply revNodeMem_outside_slot
    simp only [NODE_STRIDE] at hoff ⊢
    rcases lt_or_gt_of_ne hux with h | h <;> [left; right] <;> omega

theorem revNodeMem_preserved {mem : ℕ → ℕ} {nodesBase cap x : ℕ}
    (hx1 : 1 ≤ x) (hx2 : x ≤ cap) :
    MemPreservedOutside (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      mem (revNodeMem mem nodesBase x) := by
  intro addr haddr
  apply revNodeMem_outside_slot
  have hmul1 : NODE_STRIDE * 1 ≤ NODE_STRIDE * x := Nat.mul_le_mul_left NODE_STRIDE hx1
  have hmul2 : NODE_STRIDE * x + NODE_STRIDE ≤ NODE_STRIDE * (cap + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left NODE_STRIDE hx2) _
  rcases haddr with h | h <;> [left; right] <;> omega

theorem revNodeBody_zero_triple {w nodesBase cap : ℕ} (p : Program) (mem₀ : ℕ → ℕ) (pos : ℕ)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w) :
    Triple w p
      (fun st => st = startState [nodesBase, 0] mem₀ pos)
      revNodeBody
      (retPost fun v st' => v = 0 ∧ st'.mem = mem₀)
      (fun _ => K_REV_NODE) := by
  intro st ω hst
  subst hst
  refine runs_start_le ?_
  have hw0 : (0 : ℕ) < 2 ^ w := by unfold NODE_STRIDE at hbase; omega
  have hcond : (Expr.reg 1).eval w (startState [nodesBase, 0] mem₀ pos) = some 0 := by
    simp [startState, Expr.eval]
  refine ⟨.returned 0, startState [nodesBase, 0] mem₀ pos, 4, ?_, ⟨rfl, rfl⟩,
    by dsimp only; unfold K_REV_NODE; omega⟩
  refine runs_cond_iff.mpr ⟨0, 2, hcond, ?_, rfl⟩
  exact runs_ret_iff.mpr ⟨0, Expr.eval_const hw0, rfl, rfl, rfl⟩

theorem revNodeBody_runs_nonzero {w nodesBase cap x : ℕ} (p : Program) (mem₀ : ℕ → ℕ) (pos : ℕ)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w) (hx1 : 1 ≤ x) (hx2 : x ≤ cap) :
    ∀ ω, ∃ o st' c, Runs w p ω revNodeBody (startState [nodesBase, x] mem₀ pos) o st' c ∧
      o = .returned 0 ∧ st'.mem = revNodeMem mem₀ nodesBase x ∧ c ≤ K_REV_NODE := by
  intro ω
  let st0 := startState [nodesBase, x] mem₀ pos
  have hr0 : st0.regs 0 = nodesBase := rfl
  have hr1 : st0.regs 1 = x := rfl
  have hw0 : (0 : ℕ) < 2 ^ w := by unfold NODE_STRIDE at hbase; omega
  have hw1 : (1 : ℕ) < 2 ^ w := by unfold NODE_STRIDE at hbase; omega
  have hptr_lt := nodePtr_lt_pow hbase hx2
  let ptr := nodesBase + NODE_STRIDE * x
  have hal : ∀ off < NODE_STRIDE, ptr + off < 2 ^ w := fun off hoff => nodeAddr_lt_pow hbase hx2 hoff
  have hcond0 : (Expr.reg 1).eval w st0 = some x := Expr.eval_reg_of_eq hr1
  have hxne : x ≠ 0 := by omega
  have hstride : NODE_STRIDE < 2 ^ w := by unfold NODE_STRIDE at *; omega
  dsimp only [revNodeBody]
  suffices hsub : ∃ o st' c,
      Runs w p ω
        (Stmt.assign 2 (nodePtrExpr 0 1) ;;
         swapFieldsStmt 2 OFF_LEFT OFF_RIGHT 3 4 ;;
         swapFieldsStmt 2 OFF_MIN1_HAS OFF_MIN2_HAS 3 4 ;;
         swapFieldsStmt 2 OFF_MIN1_VAL OFF_MIN2_VAL 3 4 ;;
         swapFieldsStmt 2 OFF_MIN1_FIRST OFF_MIN2_LAST 3 4 ;;
         swapFieldsStmt 2 OFF_MIN1_LAST OFF_MIN2_FIRST 3 4 ;;
         swapFieldsStmt 2 OFF_CSUM_FWD OFF_CSUM_BWD 3 4 ;;
         Stmt.assign 3 (fieldLoadExpr 2 OFF_REV) ;;
         Stmt.store (fieldAddrExpr 2 OFF_REV) (.bin .sub (.const 1) (.reg 3)) ;;
         Stmt.cond (fieldLoadExpr 2 OFF_HASE)
           (Stmt.assign 3 (fieldLoadExpr 2 OFF_DIR) ;;
            Stmt.store (fieldAddrExpr 2 OFF_DIR) (.bin .sub (.const 1) (.reg 3)) ;;
            swapFieldsStmt 2 OFF_AF_PTR OFF_AB_PTR 3 4 ;;
            swapFieldsStmt 2 OFF_COST_FWD OFF_COST_BWD 3 4)
           Stmt.nop ;;
         Stmt.cond (fieldLoadExpr 2 OFF_HAS_TAG)
           (Stmt.assign 3 (fieldLoadExpr 2 OFF_TAG_NEG) ;;
            Stmt.store (fieldAddrExpr 2 OFF_TAG_NEG) (.bin .sub (.const 1) (.reg 3)))
           Stmt.nop ;;
         Stmt.ret (.const 0))
        st0 o st' c ∧ (o = .returned 0 ∧ st'.mem = revNodeMem mem₀ nodesBase x) ∧
        0 + c ≤ K_REV_NODE - 2 by
    rcases hsub with ⟨o, st', c, hr, ⟨ho, hm⟩, hc⟩
    exact ⟨o, st', 1 + c + 1, runs_cond_iff.mpr ⟨x, c, hcond0, by simpa [hxne] using hr, rfl⟩,
      ho, hm, by unfold K_REV_NODE at *; omega⟩
  refine runs_seq_assign_le (v := ptr) (eval_nodePtrExpr hstride hr0 hr1 hptr_lt) ?_
  have hr2_0 : (Function.update st0.regs 2 ptr) 2 = ptr := Function.update_self _ _ _
  refine runs_seq_triple_le (swapFieldsStmt_triple p _ hr2_0 (by decide) (by decide) (by decide)
    (by unfold OFF_LEFT OFF_RIGHT; decide) (hal OFF_LEFT (by decide)) (hal OFF_RIGHT (by decide))) rfl ?_
  intro st1 ⟨hm1, hreg1, _⟩
  have hr2_1 : st1.regs 2 = ptr := by rw [hreg1 2 (by decide) (by decide)]; exact hr2_0
  refine runs_seq_triple_le (swapFieldsStmt_triple p st1 hr2_1 (by decide) (by decide) (by decide)
    (by unfold OFF_MIN1_HAS OFF_MIN2_HAS; decide) (hal OFF_MIN1_HAS (by decide))
    (hal OFF_MIN2_HAS (by decide))) rfl ?_
  intro st2 ⟨hm2, hreg2, _⟩
  have hr2_2 : st2.regs 2 = ptr := by rw [hreg2 2 (by decide) (by decide)]; exact hr2_1
  refine runs_seq_triple_le (swapFieldsStmt_triple p st2 hr2_2 (by decide) (by decide) (by decide)
    (by unfold OFF_MIN1_VAL OFF_MIN2_VAL; decide) (hal OFF_MIN1_VAL (by decide))
    (hal OFF_MIN2_VAL (by decide))) rfl ?_
  intro st3 ⟨hm3, hreg3, _⟩
  have hr2_3 : st3.regs 2 = ptr := by rw [hreg3 2 (by decide) (by decide)]; exact hr2_2
  refine runs_seq_triple_le (swapFieldsStmt_triple p st3 hr2_3 (by decide) (by decide) (by decide)
    (by unfold OFF_MIN1_FIRST OFF_MIN2_LAST; decide) (hal OFF_MIN1_FIRST (by decide))
    (hal OFF_MIN2_LAST (by decide))) rfl ?_
  intro st4 ⟨hm4, hreg4, _⟩
  have hr2_4 : st4.regs 2 = ptr := by rw [hreg4 2 (by decide) (by decide)]; exact hr2_3
  refine runs_seq_triple_le (swapFieldsStmt_triple p st4 hr2_4 (by decide) (by decide) (by decide)
    (by unfold OFF_MIN1_LAST OFF_MIN2_FIRST; decide) (hal OFF_MIN1_LAST (by decide))
    (hal OFF_MIN2_FIRST (by decide))) rfl ?_
  intro st5 ⟨hm5, hreg5, _⟩
  have hr2_5 : st5.regs 2 = ptr := by rw [hreg5 2 (by decide) (by decide)]; exact hr2_4
  refine runs_seq_triple_le (swapFieldsStmt_triple p st5 hr2_5 (by decide) (by decide) (by decide)
    (by unfold OFF_CSUM_FWD OFF_CSUM_BWD; decide) (hal OFF_CSUM_FWD (by decide))
    (hal OFF_CSUM_BWD (by decide))) rfl ?_
  intro st6 ⟨hm6, hreg6, _⟩
  have hr2_6 : st6.regs 2 = ptr := by rw [hreg6 2 (by decide) (by decide)]; exact hr2_5
  refine runs_seq_assign_le (v := st6.mem (ptr + OFF_REV)) (eval_fieldLoadExpr hr2_6 (hal OFF_REV (by decide))) ?_
  refine runs_seq_store_le
    (eval_fieldAddrExpr (by dsimp only; rw [Function.update_of_ne (by decide : (2 : ℕ) ≠ 3)]; exact hr2_6)
      (hal OFF_REV (by decide)))
    (eval_sub_one_reg hw1) ?_
  let mem7 := Function.update st6.mem (ptr + OFF_REV) (1 - st6.mem (ptr + OFF_REV))
  have hm7_eq : mem7 =
      Function.update
        (Function.update (Function.update
          (Function.update (Function.update
            (Function.update (Function.update
              (Function.update (Function.update
                (Function.update (Function.update
                  (Function.update (Function.update mem₀ (ptr + OFF_LEFT) (mem₀ (ptr + OFF_RIGHT)))
                    (ptr + OFF_RIGHT) (mem₀ (ptr + OFF_LEFT)))
                  (ptr + OFF_MIN1_HAS) (mem₀ (ptr + OFF_MIN2_HAS)))
                (ptr + OFF_MIN2_HAS) (mem₀ (ptr + OFF_MIN1_HAS)))
                (ptr + OFF_MIN1_VAL) (mem₀ (ptr + OFF_MIN2_VAL)))
              (ptr + OFF_MIN2_VAL) (mem₀ (ptr + OFF_MIN1_VAL)))
              (ptr + OFF_MIN1_FIRST) (mem₀ (ptr + OFF_MIN2_LAST)))
            (ptr + OFF_MIN2_LAST) (mem₀ (ptr + OFF_MIN1_FIRST)))
            (ptr + OFF_MIN1_LAST) (mem₀ (ptr + OFF_MIN2_FIRST)))
          (ptr + OFF_MIN2_FIRST) (mem₀ (ptr + OFF_MIN1_LAST)))
          (ptr + OFF_CSUM_FWD) (mem₀ (ptr + OFF_CSUM_BWD)))
        (ptr + OFF_CSUM_BWD) (mem₀ (ptr + OFF_CSUM_FWD)))
        (ptr + OFF_REV) (1 - mem₀ (ptr + OFF_REV)) := by
    have hneq : ∀ a b, a ≠ b → ptr + a ≠ ptr + b := fun _ _ hab h => hab (Nat.add_left_cancel h)
    have hm1' : st1.mem = Function.update (Function.update mem₀ (ptr + OFF_LEFT) (mem₀ (ptr + OFF_RIGHT)))
        (ptr + OFF_RIGHT) (mem₀ (ptr + OFF_LEFT)) := by simpa [st0, startState] using hm1
    have h2_mem : ∀ off, off ≠ OFF_LEFT → off ≠ OFF_RIGHT → st1.mem (ptr + off) = mem₀ (ptr + off) := by
      intro off h1 h2; rw [hm1', Function.update_of_ne (hneq _ _ h2), Function.update_of_ne (hneq _ _ h1)]
    have hm2' : st2.mem = Function.update (Function.update st1.mem (ptr + OFF_MIN1_HAS) (mem₀ (ptr + OFF_MIN2_HAS)))
        (ptr + OFF_MIN2_HAS) (mem₀ (ptr + OFF_MIN1_HAS)) := by
      rw [hm2, h2_mem _ (by decide) (by decide), h2_mem _ (by decide) (by decide)]
    have h3_mem : ∀ off, off ≠ OFF_LEFT → off ≠ OFF_RIGHT → off ≠ OFF_MIN1_HAS → off ≠ OFF_MIN2_HAS →
        st2.mem (ptr + off) = mem₀ (ptr + off) := by
      intro off h1 h2 h3 h4
      rw [hm2', Function.update_of_ne (hneq _ _ h4), Function.update_of_ne (hneq _ _ h3), h2_mem off h1 h2]
    have hm3' : st3.mem = Function.update (Function.update st2.mem (ptr + OFF_MIN1_VAL) (mem₀ (ptr + OFF_MIN2_VAL)))
        (ptr + OFF_MIN2_VAL) (mem₀ (ptr + OFF_MIN1_VAL)) := by
      rw [hm3, h3_mem _ (by decide) (by decide) (by decide) (by decide),
        h3_mem _ (by decide) (by decide) (by decide) (by decide)]
    have h4_mem : ∀ off, off ≠ OFF_LEFT → off ≠ OFF_RIGHT → off ≠ OFF_MIN1_HAS → off ≠ OFF_MIN2_HAS →
        off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL → st3.mem (ptr + off) = mem₀ (ptr + off) := by
      intro off h1 h2 h3 h4 h5 h6
      rw [hm3', Function.update_of_ne (hneq _ _ h6), Function.update_of_ne (hneq _ _ h5), h3_mem off h1 h2 h3 h4]
    have hm4' : st4.mem = Function.update (Function.update st3.mem (ptr + OFF_MIN1_FIRST) (mem₀ (ptr + OFF_MIN2_LAST)))
        (ptr + OFF_MIN2_LAST) (mem₀ (ptr + OFF_MIN1_FIRST)) := by
      rw [hm4, h4_mem _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        h4_mem _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    have h5_mem : ∀ off, off ≠ OFF_LEFT → off ≠ OFF_RIGHT → off ≠ OFF_MIN1_HAS → off ≠ OFF_MIN2_HAS →
        off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL → off ≠ OFF_MIN1_FIRST → off ≠ OFF_MIN2_LAST →
        st4.mem (ptr + off) = mem₀ (ptr + off) := by
      intro off h1 h2 h3 h4 h5 h6 h7 h8
      rw [hm4', Function.update_of_ne (hneq _ _ h8), Function.update_of_ne (hneq _ _ h7),
        h4_mem off h1 h2 h3 h4 h5 h6]
    have hm5' : st5.mem = Function.update (Function.update st4.mem (ptr + OFF_MIN1_LAST) (mem₀ (ptr + OFF_MIN2_FIRST)))
        (ptr + OFF_MIN2_FIRST) (mem₀ (ptr + OFF_MIN1_LAST)) := by
      rw [hm5, h5_mem _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        h5_mem _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    have h6_mem : ∀ off, off ≠ OFF_LEFT → off ≠ OFF_RIGHT → off ≠ OFF_MIN1_HAS → off ≠ OFF_MIN2_HAS →
        off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL → off ≠ OFF_MIN1_FIRST → off ≠ OFF_MIN2_LAST →
        off ≠ OFF_MIN1_LAST → off ≠ OFF_MIN2_FIRST → st5.mem (ptr + off) = mem₀ (ptr + off) := by
      intro off h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      rw [hm5', Function.update_of_ne (hneq _ _ h10), Function.update_of_ne (hneq _ _ h9),
        h5_mem off h1 h2 h3 h4 h5 h6 h7 h8]
    have hm6' : st6.mem = Function.update (Function.update st5.mem (ptr + OFF_CSUM_FWD) (mem₀ (ptr + OFF_CSUM_BWD)))
        (ptr + OFF_CSUM_BWD) (mem₀ (ptr + OFF_CSUM_FWD)) := by
      rw [hm6, h6_mem _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        h6_mem _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    have h6rv : st6.mem (ptr + OFF_REV) = mem₀ (ptr + OFF_REV) := by
      rw [hm6', Function.update_of_ne (hneq _ _ (by decide)), Function.update_of_ne (hneq _ _ (by decide))]
      exact h6_mem _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    dsimp only [mem7]
    rw [h6rv, hm6', hm5', hm4', hm3', hm2', hm1']
  have h7_agree : ∀ off, off = OFF_HASE ∨ off = OFF_HAS_TAG ∨ off = OFF_DIR ∨
      off = OFF_AF_PTR ∨ off = OFF_AB_PTR ∨ off = OFF_COST_FWD ∨ off = OFF_COST_BWD ∨
      off = OFF_TAG_NEG → mem7 (ptr + off) = mem₀ (ptr + off) := by
    intro off hoff
    rw [hm7_eq]
    have hneq : ∀ a b, a ≠ b → ptr + a ≠ ptr + b := fun _ _ hab h => hab (Nat.add_left_cancel h)
    rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · repeat (rw [Function.update_of_ne (hneq _ _ (by decide))])
  have hcond_hase :
      ∃ st8 c8,
        Runs w p ω
          (Stmt.cond (fieldLoadExpr 2 OFF_HASE)
            (Stmt.assign 3 (fieldLoadExpr 2 OFF_DIR) ;;
             Stmt.store (fieldAddrExpr 2 OFF_DIR) (.bin .sub (.const 1) (.reg 3)) ;;
             swapFieldsStmt 2 OFF_AF_PTR OFF_AB_PTR 3 4 ;;
             swapFieldsStmt 2 OFF_COST_FWD OFF_COST_BWD 3 4)
            Stmt.nop)
          ⟨mem7, Function.update st6.regs 3 (st6.mem (ptr + OFF_REV)), st6.pos⟩
          .normal st8 c8 ∧
        st8.regs 2 = ptr ∧
        st8.mem = (if mem₀ (ptr + OFF_HASE) = 0 then mem7 else
          let m8a := Function.update mem7 (ptr + OFF_DIR) (1 - mem₀ (ptr + OFF_DIR))
          let m8b := Function.update (Function.update m8a (ptr + OFF_AF_PTR) (mem₀ (ptr + OFF_AB_PTR)))
            (ptr + OFF_AB_PTR) (mem₀ (ptr + OFF_AF_PTR))
          Function.update (Function.update m8b (ptr + OFF_COST_FWD) (mem₀ (ptr + OFF_COST_BWD)))
            (ptr + OFF_COST_BWD) (mem₀ (ptr + OFF_COST_FWD))) ∧
        c8 ≤ 70 := by
    let st_in : State := ⟨mem7, Function.update st6.regs 3 (st6.mem (ptr + OFF_REV)), st6.pos⟩
    have hr2_in : st_in.regs 2 = ptr := by
      dsimp [st_in]; rw [Function.update_of_ne (by decide)]; exact hr2_6
    have heval_he : (fieldLoadExpr 2 OFF_HASE).eval w st_in = some (mem₀ (ptr + OFF_HASE)) := by
      simpa [st_in, h7_agree OFF_HASE (Or.inl rfl)] using eval_fieldLoadExpr hr2_in (hal OFF_HASE (by decide))
    by_cases hhe : mem₀ (ptr + OFF_HASE) = 0
    · refine ⟨st_in, (fieldLoadExpr 2 OFF_HASE).size + 2, runs_cond_iff.mpr ⟨0, 1, by simpa [hhe] using heval_he,
        by simp only [st_in]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
        hr2_in, by dsimp only [st_in]; simp [hhe], ?_⟩
      simp [fieldLoadExpr, fieldAddrExpr]
    · have ha1 : Runs w p ω (Stmt.assign 3 (fieldLoadExpr 2 OFF_DIR)) st_in .normal
          ⟨st_in.mem, Function.update st_in.regs 3 (mem₀ (ptr + OFF_DIR)), st_in.pos⟩ _ :=
        runs_assign_iff.mpr ⟨mem₀ (ptr + OFF_DIR), by
          simpa [st_in, h7_agree OFF_DIR (Or.inr (Or.inr (Or.inl rfl)))] using
            eval_fieldLoadExpr hr2_in (hal OFF_DIR (by decide)), rfl, rfl, rfl⟩
      let st8a : State := ⟨Function.update mem7 (ptr + OFF_DIR) (1 - mem₀ (ptr + OFF_DIR)),
        Function.update st_in.regs 3 (mem₀ (ptr + OFF_DIR)), st_in.pos⟩
      have hr2_8a : st8a.regs 2 = ptr := by
        dsimp [st8a]; rw [Function.update_of_ne (by decide)]; exact hr2_in
      have hev_dir3 : (Expr.bin .sub (.const 1) (.reg 3)).eval w
          ⟨st_in.mem, Function.update st_in.regs 3 (mem₀ (ptr + OFF_DIR)), st_in.pos⟩ =
          some (1 - mem₀ (ptr + OFF_DIR)) := by
        have h := eval_sub_one_reg (r := 3) (w := w)
          (st := ⟨st_in.mem, Function.update st_in.regs 3 (mem₀ (ptr + OFF_DIR)), st_in.pos⟩) hw1
        simpa [Function.update_self] using h
      have hs1 : Runs w p ω (Stmt.store (fieldAddrExpr 2 OFF_DIR) (.bin .sub (.const 1) (.reg 3)))
          ⟨st_in.mem, Function.update st_in.regs 3 (mem₀ (ptr + OFF_DIR)), st_in.pos⟩ .normal st8a _ :=
        runs_store_iff.mpr ⟨ptr + OFF_DIR, 1 - mem₀ (ptr + OFF_DIR),
          eval_fieldAddrExpr hr2_8a (hal OFF_DIR (by decide)), hev_dir3, rfl, rfl, rfl⟩
      rcases swapFieldsStmt_triple (w := w) (st₀ := st8a) (tmp1 := 3) (tmp2 := 4) p hr2_8a (by decide) (by decide) (by decide)
          (by unfold OFF_AF_PTR OFF_AB_PTR; decide) (hal OFF_AF_PTR (by decide))
          (hal OFF_AB_PTR (by decide)) st8a ω rfl with
        ⟨o_a, st8b, c_a, hr_a, hpost_a, hc_a⟩
      cases o_a with
      | returned _ => contradiction
      | normal =>
          rcases hpost_a with ⟨hm_a, hreg_a, _⟩
          have hr2_8b : st8b.regs 2 = ptr := by rw [hreg_a 2 (by decide) (by decide)]; exact hr2_8a
          rcases swapFieldsStmt_triple (w := w) (st₀ := st8b) (tmp1 := 3) (tmp2 := 4) p hr2_8b (by decide) (by decide) (by decide)
              (by unfold OFF_COST_FWD OFF_COST_BWD; decide) (hal OFF_COST_FWD (by decide))
              (hal OFF_COST_BWD (by decide)) st8b ω rfl with
            ⟨o_c, st8c, c_c, hr_c, hpost_c, hc_c⟩
          cases o_c with
          | returned _ => contradiction
          | normal =>
              rcases hpost_c with ⟨hm_c, hreg_c, _⟩
              refine ⟨st8c, _, runs_cond_iff.mpr ⟨mem₀ (ptr + OFF_HASE), _, heval_he, by
                simpa [hhe] using runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha1,
                  runs_seq_iff.mpr (Or.inr ⟨st8a, _, _, hs1,
                    runs_seq_iff.mpr (Or.inr ⟨st8b, _, _, hr_a, hr_c, rfl⟩), rfl⟩), rfl⟩), rfl⟩,
                by rw [hreg_c 2 (by decide) (by decide)]; exact hr2_8b, ?_, ?_⟩
              · simp only [hhe, ↓reduceIte]
                have hneq : ∀ a b, a ≠ b → ptr + a ≠ ptr + b := fun _ _ hab h => hab (Nat.add_left_cancel h)
                have haf8 : st8a.mem (ptr + OFF_AF_PTR) = mem₀ (ptr + OFF_AF_PTR) := by
                  dsimp [st8a]; rw [Function.update_of_ne (hneq _ _ (by decide))]
                  exact h7_agree _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                have hab8 : st8a.mem (ptr + OFF_AB_PTR) = mem₀ (ptr + OFF_AB_PTR) := by
                  dsimp [st8a]; rw [Function.update_of_ne (hneq _ _ (by decide))]
                  exact h7_agree _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
                have hcf8 : st8b.mem (ptr + OFF_COST_FWD) = mem₀ (ptr + OFF_COST_FWD) := by
                  rw [hm_a, Function.update_of_ne (hneq _ _ (by decide)), Function.update_of_ne (hneq _ _ (by decide))]
                  dsimp [st8a]; rw [Function.update_of_ne (hneq _ _ (by decide))]
                  exact h7_agree _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
                have hcb8 : st8b.mem (ptr + OFF_COST_BWD) = mem₀ (ptr + OFF_COST_BWD) := by
                  rw [hm_a, Function.update_of_ne (hneq _ _ (by decide)), Function.update_of_ne (hneq _ _ (by decide))]
                  dsimp [st8a]; rw [Function.update_of_ne (hneq _ _ (by decide))]
                  exact h7_agree _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
                rw [hm_c, hcf8, hcb8, hm_a, haf8, hab8]
              · simp only [fieldLoadExpr, fieldAddrExpr, Expr.size] at *
                omega
  rcases hcond_hase with ⟨st8, c8, hr8, hr2_8, hm8, hc8⟩
  have hht_eq : st8.mem (ptr + OFF_HAS_TAG) = mem₀ (ptr + OFF_HAS_TAG) := by
    rw [hm8]
    have hneq : ∀ a b, a ≠ b → ptr + a ≠ ptr + b := fun _ _ hab h => hab (Nat.add_left_cancel h)
    split_ifs
    · exact h7_agree _ (Or.inr (Or.inl rfl))
    · repeat (rw [Function.update_of_ne (hneq _ _ (by decide))])
      exact h7_agree _ (Or.inr (Or.inl rfl))
  have htn_eq : st8.mem (ptr + OFF_TAG_NEG) = mem₀ (ptr + OFF_TAG_NEG) := by
    rw [hm8]
    have hneq : ∀ a b, a ≠ b → ptr + a ≠ ptr + b := fun _ _ hab h => hab (Nat.add_left_cancel h)
    split_ifs
    · exact h7_agree _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
    · repeat (rw [Function.update_of_ne (hneq _ _ (by decide))])
      exact h7_agree _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  have hev_ht : (fieldLoadExpr 2 OFF_HAS_TAG).eval w st8 = some (mem₀ (ptr + OFF_HAS_TAG)) := by
    simpa [hht_eq] using eval_fieldLoadExpr hr2_8 (hal OFF_HAS_TAG (by decide))
  by_cases hht : mem₀ (ptr + OFF_HAS_TAG) = 0
  · refine ⟨.returned 0, st8, _, runs_seq_iff.mpr (Or.inr ⟨st8, c8, _, hr8,
      runs_seq_iff.mpr (Or.inr ⟨st8, _, 2,
        runs_cond_iff.mpr ⟨0, 1, by simpa [hht] using hev_ht,
          by simpa using (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩ : Runs w p ω Stmt.nop st8 .normal st8 1), rfl⟩,
        runs_ret_iff.mpr ⟨0, Expr.eval_const hw0, rfl, rfl, rfl⟩, rfl⟩), rfl⟩),
      ⟨rfl, ?_⟩, ?_⟩
    · rw [hm8, hm7_eq]; dsimp only [revNodeMem, nodeField, ptr] at hht ⊢; simp [hht]
    · simp only [nodePtrExpr, fieldLoadExpr, fieldAddrExpr, Expr.size, K_REV_NODE] at *; omega
  · let st9a : State := ⟨st8.mem, Function.update st8.regs 3 (mem₀ (ptr + OFF_TAG_NEG)), st8.pos⟩
    have hr2_9a : st9a.regs 2 = ptr := by dsimp [st9a]; rw [Function.update_of_ne (by decide)]; exact hr2_8
    let st9 : State := ⟨Function.update st8.mem (ptr + OFF_TAG_NEG) (1 - mem₀ (ptr + OFF_TAG_NEG)),
      st9a.regs, st8.pos⟩
    have hcond_ht : ∃ c9, Runs w p ω
        (Stmt.cond (fieldLoadExpr 2 OFF_HAS_TAG)
          (Stmt.assign 3 (fieldLoadExpr 2 OFF_TAG_NEG) ;;
           Stmt.store (fieldAddrExpr 2 OFF_TAG_NEG) (.bin .sub (.const 1) (.reg 3)))
          Stmt.nop) st8 .normal st9 c9 ∧ c9 ≤ 20 := by
      have hev_t3 : (Expr.bin .sub (.const 1) (.reg 3)).eval w st9a =
          some (1 - mem₀ (ptr + OFF_TAG_NEG)) := by
        simpa [st9a, Function.update_self] using eval_sub_one_reg (r := 3) (w := w) (st := st9a) hw1
      refine ⟨_, runs_cond_iff.mpr ⟨mem₀ (ptr + OFF_HAS_TAG), _, hev_ht, by
        simpa [hht] using runs_seq_iff.mpr (Or.inr ⟨st9a, _, _,
          runs_assign_iff.mpr ⟨mem₀ (ptr + OFF_TAG_NEG), by
            simpa [htn_eq] using eval_fieldLoadExpr hr2_8 (hal OFF_TAG_NEG (by decide)), rfl, rfl, rfl⟩,
          runs_store_iff.mpr ⟨ptr + OFF_TAG_NEG, 1 - mem₀ (ptr + OFF_TAG_NEG),
            eval_fieldAddrExpr hr2_9a (hal OFF_TAG_NEG (by decide)), hev_t3, rfl, rfl, rfl⟩, rfl⟩), rfl⟩, ?_⟩
      simp [fieldLoadExpr, fieldAddrExpr, Expr.size]
    rcases hcond_ht with ⟨c9, hcond_ht, hc9⟩
    refine ⟨.returned 0, st9, _, runs_seq_iff.mpr (Or.inr ⟨st8, c8, _, hr8,
      runs_seq_iff.mpr (Or.inr ⟨st9, c9, 2, hcond_ht,
        runs_ret_iff.mpr ⟨0, Expr.eval_const hw0, rfl, rfl, rfl⟩, rfl⟩), rfl⟩),
      ⟨rfl, ?_⟩, ?_⟩
    · dsimp only [st9]; rw [hm8, hm7_eq]; dsimp only [revNodeMem, nodeField, ptr] at hht ⊢; simp [hht]
    · simp only [nodePtrExpr, fieldLoadExpr, fieldAddrExpr, Expr.size, K_REV_NODE] at *; omega

private theorem listRawCost_reverse_map_flip (steps : List RawStep) :
    listRawCost (steps.reverse.map RawStep.flip) = -listRawCost steps := by
  induction steps with
  | nil => simp [listRawCost]
  | cons s ss ih =>
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        listRawCost_append, ih]
      simp [listRawCost, RawStep.signedCost_flip]

private theorem stepsShiftFit_flip_neg {h L : ℕ} {steps : List RawStep} {d : ℤ}
    (hfit : StepsShiftFit h L steps d) :
    StepsShiftFit h L (steps.reverse.map RawStep.flip) (-d) := by
  intro s hs
  rw [List.mem_map] at hs
  rcases hs with ⟨s₀, hs₀_rev, rfl⟩
  have hs₀ := List.mem_reverse.mp hs₀_rev
  rcases hfit s₀ hs₀ with ⟨hf, haf, hab, hfs, hafs, habs⟩
  cases hdir : s₀.fwd <;> simp only [RawStep.flip, hdir, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, ↓reduceIte, sub_neg_eq_add, ← sub_eq_add_neg] at hfs hafs habs ⊢
  · exact ⟨hf, haf, hab, hfs, hafs, habs⟩
  · exact ⟨hf, haf, hab, hfs, hafs, habs⟩

theorem revNodeMem_treeMemMatch {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap x : ℕ}
    {l r : AuxTree} {p pp : ℕ}
    (ht : TreeMemMatch w h L mem nodesBase cap (.node x l r) p pp)
    (hnd : (AuxTree.node x l r).toList.Nodup) :
    TreeMemMatch w h L (revNodeMem mem nodesBase x) nodesBase cap (.node x r l) p pp ∧
    evalMemSteps (revNodeMem mem nodesBase x) nodesBase h L (.node x r l) false 0 =
      (evalMemSteps mem nodesBase h L (.node x l r) false 0).reverse.map RawStep.flip ∧
    (AuxTree.node x r l).evalInorder (revFlag (revNodeMem mem nodesBase x) nodesBase) false =
      ((AuxTree.node x l r).evalInorder (revFlag mem nodesBase) false).reverse := by
  have hnd' := hnd
  simp only [AuxTree.toList, List.nodup_append, List.nodup_cons, List.mem_append,
    List.mem_singleton] at hnd'
  rcases hnd' with ⟨⟨_, _, hx_l_mem⟩, _, hdisj_lr⟩
  have hx_l : x ∉ l.toList := fun hl => hx_l_mem x hl x rfl rfl
  have hx_r : x ∉ r.toList := fun hr => hdisj_lr x (Or.inr rfl) x hr rfl
  rcases ht with ⟨hx1, hx2, hL, hR, hP, hPP, hr, hiv, hhe, hsum, hdir, hht, htn,
    heu, hev, heid, he1, he0, hcf, hcb, htag1, htag0, hm1h, hm2h, hm1_1, hm1_0,
    hagg, hl_m, hr_m⟩
  have hhp_eq : revNodeMem mem nodesBase x (nodesBase - 1) = mem (nodesBase - 1) := by
    apply revNodeMem_outside_slot
    left
    have hmul : NODE_STRIDE * 1 ≤ NODE_STRIDE * x := Nat.mul_le_mul_left NODE_STRIDE hx1
    unfold NODE_STRIDE at *; omega
  have hheap : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem (nodesBase - 1) →
      revNodeMem mem nodesBase x a = mem a := by
    intro a ha _
    apply revNodeMem_outside_slot
    right
    have hmul : NODE_STRIDE * x + NODE_STRIDE ≤ NODE_STRIDE * (cap + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left NODE_STRIDE hx2) _
    omega
  rcases revNodeMem_nodeField (mem := mem) (nodesBase := nodesBase) (x := x) with
    ⟨hother, hfL, hfR, hm1h_sw, hm2h_sw, hm1v_sw, hm2v_sw, h1F, h2L, h1L, h2F,
     hcf_sw, hcb_sw, hrev, he_sw, he_keep, htn_flip, htn_keep, hsame⟩
  have hl_m' : TreeMemMatch w h L (revNodeMem mem nodesBase x) nodesBase cap l x 0 :=
    memAgree_treeMemMatch_of_nodeList hl_m
      (fun u hu off hoff => hother u (fun h => hx_l (h ▸ hu)) off hoff)
      (by omega) hheap
  have hr_m' : TreeMemMatch w h L (revNodeMem mem nodesBase x) nodesBase cap r x 0 :=
    memAgree_treeMemMatch_of_nodeList hr_m
      (fun u hu off hoff => hother u (fun h => hx_r (h ▸ hu)) off hoff)
      (by omega) hheap
  have hl_steps_eq : ∀ fl d,
      evalMemSteps (revNodeMem mem nodesBase x) nodesBase h L l fl d =
        evalMemSteps mem nodesBase h L l fl d :=
    fun fl d => evalMemSteps_agree hl_m
      (fun u hu off hoff => hother u (fun h => hx_l (h ▸ hu)) off hoff) hheap fl d
  have hr_steps_eq : ∀ fl d,
      evalMemSteps (revNodeMem mem nodesBase x) nodesBase h L r fl d =
        evalMemSteps mem nodesBase h L r fl d :=
    fun fl d => evalMemSteps_agree hr_m
      (fun u hu off hoff => hother u (fun h => hx_r (h ▸ hu)) off hoff) hheap fl d
  have hrev_x : revFlag (revNodeMem mem nodesBase x) nodesBase x = !revFlag mem nodesBase x := by
    simp only [revFlag, hrev]; by_cases hx0 : nodeField mem nodesBase x OFF_REV = 0 <;> simp [hx0]; omega
  have heval_l : l.evalInorder (revFlag (revNodeMem mem nodesBase x) nodesBase) =
      l.evalInorder (revFlag mem nodesBase) := by
    funext b; exact l.evalInorder_agree _ _ b fun u hu => by
      simp [revFlag, hother u (fun h => hx_l (h ▸ hu)) OFF_REV (by decide)]
  have heval_r : r.evalInorder (revFlag (revNodeMem mem nodesBase x) nodesBase) =
      r.evalInorder (revFlag mem nodesBase) := by
    funext b; exact r.evalInorder_agree _ _ b fun u hu => by
      simp [revFlag, hother u (fun h => hx_r (h ▸ hu)) OFF_REV (by decide)]
  have heval_node : (AuxTree.node x r l).evalInorder (revFlag (revNodeMem mem nodesBase x) nodesBase) false =
      ((AuxTree.node x l r).evalInorder (revFlag mem nodesBase) false).reverse := by
    cases hrv : revFlag mem nodesBase x <;>
      simp [AuxTree.evalInorder, hrev_x, hrv, heval_l, heval_r, AuxTree.evalInorder_true,
        List.append_assoc]
  have htag_neg_int : nodeTagInt (revNodeMem mem nodesBase x) nodesBase h L x =
      -nodeTagInt mem nodesBase h L x := by
    simp only [nodeTagInt, hsame OFF_HAS_TAG (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    by_cases hht0 : nodeField mem nodesBase x OFF_HAS_TAG = 0
    · simp [hht0]
    · have hht1 : nodeField mem nodesBase x OFF_HAS_TAG = 1 := by omega
      rcases (htag1 hht1).1 with ⟨_, hlo, hhi, hv⟩
      have hptr_eq := hsame OFF_TAG_PTR (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hov : optIntVal (revNodeMem mem nodesBase x) h L
          (nodeField (revNodeMem mem nodesBase x) nodesBase x OFF_TAG_PTR) =
          optIntVal mem h L (nodeField mem nodesBase x OFF_TAG_PTR) := by
        rw [hptr_eq]; exact optIntVal_agree_heap hheap (Or.inr ⟨hlo, hhi, hv⟩)
      simp only [hht0, ↓reduceIte, htn_flip hht0, hov]
      by_cases htn0 : nodeField mem nodesBase x OFF_TAG_NEG = 0 <;> simp [htn0]; omega
  have hown_flip : nodeOwnRawStep (revNodeMem mem nodesBase x) nodesBase h L x =
      (nodeOwnRawStep mem nodesBase h L x).map RawStep.flip := by
    simp only [nodeOwnRawStep, hsame OFF_HASE (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    by_cases hhe0 : nodeField mem nodesBase x OFF_HASE = 0
    · simp [hhe0]
    · have hhe1 : nodeField mem nodesBase x OFF_HASE = 1 := by omega
      rcases he_sw hhe0 with ⟨hd', haf', hab', hcf', hcb'⟩
      rcases he1 hhe1 with ⟨pf, haf_ok, hab_ok, hcf_ok, hcb_ok, _⟩
      have hfl_eq := intVal_agree_heap hheap pf.2.1 pf.2.2.1 (h := h) (L := L)
      have haf_eq := intVal_agree_heap hheap haf_ok.2.1 haf_ok.2.2.1 (h := h) (L := L)
      have hab_eq := intVal_agree_heap hheap hab_ok.2.1 hab_ok.2.2.1 (h := h) (L := L)
      have hcf_eq := intVal_agree_heap hheap hcf_ok.2.1 hcf_ok.2.2.1 (h := h) (L := L)
      have hcb_eq := intVal_agree_heap hheap hcb_ok.2.1 hcb_ok.2.2.1 (h := h) (L := L)
      have hfl := hsame OFF_FLOW_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have heu_eq := hsame OFF_EU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hev_eq := hsame OFF_EV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have heid_eq := hsame OFF_EID (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      simp only [hhe0, ↓reduceIte, Option.map_some, RawStep.flip, hd', hfl, haf', hab', hcf', hcb',
        hfl_eq, haf_eq, hab_eq, hcf_eq, hcb_eq, heu_eq, hev_eq, heid_eq]
      by_cases hd0 : nodeField mem nodesBase x OFF_DIR = 0 <;> simp [hd0]; omega
  have hsteps_rev : evalMemSteps (revNodeMem mem nodesBase x) nodesBase h L (.node x r l) false 0 =
      (evalMemSteps mem nodesBase h L (.node x l r) false 0).reverse.map RawStep.flip := by
    have hown_list : ((nodeOwnRawStep (revNodeMem mem nodesBase x) nodesBase h L x).map
        (fun s => s.addDeltaMod h L 0)).toList =
        (((nodeOwnRawStep mem nodesBase h L x).map (fun s => s.addDeltaMod h L 0)).toList).reverse.map RawStep.flip := by
      rw [hown_flip]
      cases nodeOwnRawStep mem nodesBase h L x with
      | none => rfl
      | some s =>
          simp only [Option.map_some, Option.toList_some, List.reverse_singleton, List.map_singleton]
          simpa [neg_zero] using RawStep.addDeltaMod_flip h L s 0
    cases hrv : revFlag mem nodesBase x
    · have hl_rev : evalMemSteps mem nodesBase h L l true (-nodeTagInt mem nodesBase h L x) =
          (evalMemSteps mem nodesBase h L l false (nodeTagInt mem nodesBase h L x)).reverse.map RawStep.flip :=
        evalMemSteps_true_eq hl_m _
      have hr_rev : evalMemSteps mem nodesBase h L r true (-nodeTagInt mem nodesBase h L x) =
          (evalMemSteps mem nodesBase h L r false (nodeTagInt mem nodesBase h L x)).reverse.map RawStep.flip :=
        evalMemSteps_true_eq hr_m _
      simp only [evalMemSteps, Bool.false_eq_true, ↓reduceIte, Bool.false_xor, hrev_x, hrv,
        Bool.not_false, zero_add, htag_neg_int, List.reverse_append, List.map_append,
        List.append_assoc, hl_steps_eq, hr_steps_eq, hr_rev, hl_rev, hown_list, List.map_reverse]
    · have hl_inv : evalMemSteps mem nodesBase h L l false (-nodeTagInt mem nodesBase h L x) =
          (evalMemSteps mem nodesBase h L l true (nodeTagInt mem nodesBase h L x)).reverse.map RawStep.flip := by
        rw [← neg_neg (nodeTagInt mem nodesBase h L x), evalMemSteps_true_eq hl_m, neg_neg]
        simp [List.map_reverse, List.map_map, Function.comp_def, RawStep.flip]
      have hr_inv : evalMemSteps mem nodesBase h L r false (-nodeTagInt mem nodesBase h L x) =
          (evalMemSteps mem nodesBase h L r true (nodeTagInt mem nodesBase h L x)).reverse.map RawStep.flip := by
        rw [← neg_neg (nodeTagInt mem nodesBase h L x), evalMemSteps_true_eq hr_m, neg_neg]
        simp [List.map_reverse, List.map_map, Function.comp_def, RawStep.flip]
      simp only [evalMemSteps, Bool.false_eq_true, ↓reduceIte, Bool.false_xor, hrev_x, hrv,
        Bool.not_true, zero_add, htag_neg_int, List.reverse_append, List.map_append,
        List.append_assoc, hl_steps_eq, hr_steps_eq, hr_inv, hl_inv, hown_list, List.map_reverse]
  refine ⟨?_, hsteps_rev, heval_node⟩
  refine ⟨hx1, hx2, by rw [hfL, hR], by rw [hfR, hL],
    by rw [hsame OFF_PARENT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hP,
    by rw [hsame OFF_PPAR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hPP,
    by rw [hrev]; omega,
    by rw [hsame OFF_ISV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hiv,
    by rw [hsame OFF_HASE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hhe,
    by rw [hsame OFF_ISV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hsame OFF_HASE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsum,
    ?_,
    by rw [hsame OFF_HAS_TAG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hht,
    ?_,
    by rw [hsame OFF_EU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact heu,
    by rw [hsame OFF_EV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hev,
    by rw [hsame OFF_EID (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact heid,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hr_m', hl_m'⟩
  · by_cases hhe0 : nodeField mem nodesBase x OFF_HASE = 0
    · rw [he_keep hhe0 _ (Or.inl rfl)]; exact hdir
    · rw [(he_sw hhe0).1]; omega
  · by_cases hht0 : nodeField mem nodesBase x OFF_HAS_TAG = 0
    · rw [htn_keep hht0]; exact htn
    · rw [htn_flip hht0]; omega
  · intro hhe1
    rw [hsame OFF_HASE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at hhe1
    rcases he1 hhe1 with ⟨pf, paf, pab, pcf, pcb, hcb_eq⟩
    rcases he_sw (by omega) with ⟨_, haf, hab, hcf', hcb'⟩
    have hfl := hsame OFF_FLOW_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hfl, haf, hab, hcf', hcb']
    refine ⟨numPtrOk_congr (by omega) hheap pf, numPtrOk_congr (by omega) hheap pab,
      numPtrOk_congr (by omega) hheap paf, numPtrOk_congr (by omega) hheap pcb,
      numPtrOk_congr (by omega) hheap pcf, ?_⟩
    rw [intVal_agree_heap hheap pcf.2.1 pcf.2.2.1, intVal_agree_heap hheap pcb.2.1 pcb.2.2.1, hcb_eq,
      wrap_neg_wrap, neg_neg, wrap_of_fits (intVal_fits pcf.2.2.2)]
  · intro hhe0
    rw [hsame OFF_HASE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at hhe0
    rw [he_keep hhe0 _ (Or.inl rfl), he_keep hhe0 _ (Or.inr (Or.inl rfl)),
      he_keep hhe0 _ (Or.inr (Or.inr (Or.inl rfl))),
      he_keep hhe0 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      he_keep hhe0 _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
      hsame OFF_FLOW_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact he0 hhe0
  · rw [hcf_sw]; exact optNumPtrOk_congr (by omega) hheap hcb
  · rw [hcb_sw]; exact optNumPtrOk_congr (by omega) hheap hcf
  · intro hht1
    rw [hsame OFF_HAS_TAG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at hht1
    rcases htag1 hht1 with ⟨pt, hch, d, hdmod, hfit⟩
    have hpt_eq := hsame OFF_TAG_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    refine ⟨by rw [hpt_eq]; exact numPtrOk_congr (by omega) hheap pt, ?_, -d, ?_, ?_⟩
    · rcases hch with hcl | hcr
      · right
        have hlne : l.rootId ≠ x := fun h => by
          cases l with | leaf => exact hcl.1 rfl | node _ _ _ => simp [AuxTree.rootId] at h; subst h; exact hx_l (by simp [AuxTree.toList])
        simpa [hother _ hlne OFF_MIN1_HAS (by decide)] using hcl
      · left
        have hrne : r.rootId ≠ x := fun h => by
          cases r with | leaf => exact hcr.1 rfl | node _ _ _ => simp [AuxTree.rootId] at h; subst h; exact hx_r (by simp [AuxTree.toList])
        simpa [hother _ hrne OFF_MIN1_HAS (by decide)] using hcr
    · rw [htag_neg_int, Int.emod_eq_emod_iff_emod_sub_eq_zero]
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at hdmod
      obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hdmod
      exact Int.emod_eq_zero_of_dvd ⟨-k, by linarith⟩
    · have hf' : evalMemSteps (revNodeMem mem nodesBase x) nodesBase h L r (revFlag (revNodeMem mem nodesBase x) nodesBase x) 0 ++
          evalMemSteps (revNodeMem mem nodesBase x) nodesBase h L l (revFlag (revNodeMem mem nodesBase x) nodesBase x) 0 =
          ((evalMemSteps mem nodesBase h L l (revFlag mem nodesBase x) 0 ++
            evalMemSteps mem nodesBase h L r (revFlag mem nodesBase x) 0).reverse.map RawStep.flip) := by
        have hr_rev : evalMemSteps (revNodeMem mem nodesBase x) nodesBase h L r (revFlag (revNodeMem mem nodesBase x) nodesBase x) 0 =
            (evalMemSteps mem nodesBase h L r (revFlag mem nodesBase x) 0).reverse.map RawStep.flip := by
          rw [hr_steps_eq, hrev_x]
          cases hrv : revFlag mem nodesBase x
          · exact evalMemSteps_true_eq hr_m 0
          · rw [← neg_zero]; rw [evalMemSteps_true_eq hr_m 0]; simp [List.map_reverse, List.map_map, Function.comp_def, RawStep.flip]
        have hl_rev : evalMemSteps (revNodeMem mem nodesBase x) nodesBase h L l (revFlag (revNodeMem mem nodesBase x) nodesBase x) 0 =
            (evalMemSteps mem nodesBase h L l (revFlag mem nodesBase x) 0).reverse.map RawStep.flip := by
          rw [hl_steps_eq, hrev_x]
          cases hrv : revFlag mem nodesBase x
          · exact evalMemSteps_true_eq hl_m 0
          · rw [← neg_zero]; rw [evalMemSteps_true_eq hl_m 0]; simp [List.map_reverse, List.map_map, Function.comp_def, RawStep.flip]
        rw [hr_rev, hl_rev, List.reverse_append, List.map_append]
      rw [hf']
      exact stepsShiftFit_flip_neg hfit
  · intro hht0
    rw [hsame OFF_HAS_TAG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at hht0
    rw [hsame OFF_TAG_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      htn_keep hht0]
    exact htag0 hht0
  · rw [hm1h_sw, hm2h]; exact hm1h
  · rw [hm2h_sw, hm1h_sw, hm2h]
  · intro hm11
    rw [hm1h_sw, hm2h] at hm11
    rcases hm1_1 hm11 with ⟨p1, p2, hf1, hl1, hf2, hl2⟩
    rw [hm1v_sw, hm2v_sw, h1F, h1L, h2F, h2L]
    exact ⟨numPtrOk_congr (by omega) hheap p2, numPtrOk_congr (by omega) hheap p1, hl2, hf2, hl1, hf1⟩
  · intro hm10
    rw [hm1h_sw, hm2h] at hm10
    rw [hm1v_sw, hm2v_sw, h1F, h1L, h2F, h2L]
    rcases hm1_0 hm10 with ⟨a1, a2, a3, a4, a5, a6⟩
    exact ⟨a4, a6, a5, a1, a3, a2⟩
  · dsimp only
    rw [heval_node, hsteps_rev]
    rcases hagg with ⟨hvc, hsf, hsb, hmiff, hm1, hm2⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsame OFF_VCNT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hvc, listVcnt_reverse]
      exact listVcnt_agree_of_mem fun u hu => by
        by_cases hux : u = x
        · subst hux; exact (hsame OFF_ISV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).symm
        · exact (hother u hux OFF_ISV (by decide)).symm
    · rw [hcf_sw, optIntVal_agree_heap hheap hcb, hsb, listRawCost_reverse_map_flip]
    · rw [hcb_sw, optIntVal_agree_heap hheap hcf, hsf, listRawCost_reverse_map_flip, neg_neg]
    · rw [hm1h_sw, hm2h, hmiff]
      simp [List.map_eq_nil_iff]
    · have hrev2 : nodeIntMinAgg1 (revNodeMem mem nodesBase x) nodesBase h L x =
          (nodeIntMinAgg2 mem nodesBase h L x).rev := by
        dsimp only [nodeIntMinAgg1, nodeIntMinAgg2]
        rw [hm1h_sw, hm1v_sw, h1F, h1L]
        by_cases hm20 : nodeField mem nodesBase x OFF_MIN2_HAS = 0
        · have hm10 : nodeField mem nodesBase x OFF_MIN1_HAS = 0 := by omega
          rcases hm1_0 hm10 with ⟨_, _, _, a4, a5, a6⟩
          simp [IntMinAgg.rev, hm20, a4, a5, a6, optIntVal]
        · have hm11 : nodeField mem nodesBase x OFF_MIN1_HAS = 1 := by omega
          rcases hm1_1 hm11 with ⟨_, p2, _⟩
          have hov := optIntVal_agree_heap hheap (Or.inr ⟨p2.2.1, p2.2.2.1, p2.2.2.2⟩)
          simp [IntMinAgg.rev, hm20, hov]
      rw [hrev2, hm2, ← listIntMinAgg_reverse]
      congr 1
      simp [List.map_reverse, Function.comp_def, RawStep.flip]
    · have hrev1 : nodeIntMinAgg2 (revNodeMem mem nodesBase x) nodesBase h L x =
          (nodeIntMinAgg1 mem nodesBase h L x).rev := by
        dsimp only [nodeIntMinAgg1, nodeIntMinAgg2]
        rw [hm2h_sw, hm2v_sw, h2L, h2F]
        by_cases hm10 : nodeField mem nodesBase x OFF_MIN1_HAS = 0
        · rcases hm1_0 hm10 with ⟨a1, a2, a3, _⟩
          simp [IntMinAgg.rev, hm10, a1, a2, a3, optIntVal]
        · have hm11 : nodeField mem nodesBase x OFF_MIN1_HAS = 1 := by omega
          rcases hm1_1 hm11 with ⟨p1, _⟩
          have hov := optIntVal_agree_heap hheap (Or.inr ⟨p1.2.1, p1.2.2.1, p1.2.2.2⟩)
          simp [IntMinAgg.rev, hm10, hov]
      rw [hrev1, hm1, ← listIntMinAgg_reverse]
      congr 1
      simp [List.map_reverse, Function.comp_def, RawStep.flip]

theorem revNodeBody_subtree_runs {w h L nodesBase cap parId : ℕ} {p : Program}
    {mem₀ : ℕ → ℕ} (pos : ℕ)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    {s : AuxTree} (hs : TreeMemMatch w h L mem₀ nodesBase cap s parId 0)
    (hs_nd : s.toList.Nodup) :
    ∀ ω, ∃ st' c, Runs w p ω revNodeBody (startState [nodesBase, s.rootId] mem₀ pos)
        (.returned 0) st' c ∧
      c ≤ K_REV_NODE ∧
      TreeMemMatch w h L st'.mem nodesBase cap s.revRoot parId 0 ∧
      evalMemSteps st'.mem nodesBase h L s.revRoot false 0 =
        (evalMemSteps mem₀ nodesBase h L s false 0).reverse.map RawStep.flip ∧
      s.revRoot.evalInorder (revFlag st'.mem nodesBase) false =
        (s.evalInorder (revFlag mem₀ nodesBase) false).reverse ∧
      st'.mem (nodesBase - 1) = mem₀ (nodesBase - 1) ∧
      (∀ u, ∀ off, IsStaticPayloadOff off →
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      (∀ addr, addr < nodesBase + NODE_STRIDE * s.rootId ∨
          nodesBase + NODE_STRIDE * s.rootId + NODE_STRIDE ≤ addr →
        st'.mem addr = mem₀ addr) ∧
      MemPreservedOutside (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        mem₀ st'.mem := by
  intro ω
  cases s with
  | leaf =>
      rcases revNodeBody_zero_triple p mem₀ pos hbase _ ω rfl with ⟨o, st', c, hr, hp, hc⟩
      cases o with
      | normal => contradiction
      | returned v =>
          rcases hp with ⟨ho, hm⟩
          subst ho
          exact ⟨st', c, hr, hc, trivial, by simp [AuxTree.revRoot, evalMemSteps],
            by simp [AuxTree.revRoot, AuxTree.evalInorder],
            by simp [hm], fun _ _ _ => by simp [nodeField, hm],
            fun _ _ => by simp [hm], fun _ _ => by simp [hm]⟩
  | node x l r =>
      rcases revNodeBody_runs_nonzero p mem₀ pos hbase hs.1 hs.2.1 ω with
        ⟨o, st', c, hrun, ho, hmem, hc⟩
      subst ho
      rcases revNodeMem_treeMemMatch hs hs_nd with ⟨hm_rev, hsteps_rev, heval_rev⟩
      refine ⟨st', c, hrun, hc, by simpa [AuxTree.revRoot, hmem] using hm_rev,
        by simpa [AuxTree.revRoot, hmem] using hsteps_rev,
        by simpa [AuxTree.revRoot, hmem] using heval_rev, ?_, ?_, ?_, ?_⟩
      · rw [hmem]
        apply revNodeMem_outside_slot
        left
        have hmul : NODE_STRIDE * 1 ≤ NODE_STRIDE * x := Nat.mul_le_mul_left NODE_STRIDE hs.1
        unfold NODE_STRIDE at *; omega
      · intro u off hoff
        rw [hmem]
        rcases revNodeMem_nodeField (mem := mem₀) (nodesBase := nodesBase) (x := x) with
          ⟨hother, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsame⟩
        have hoff_lt := (isStaticPayloadOff_ne_struct hoff).1
        by_cases hux : u = x
        · subst hux
          rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
            exact hsame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        · exact hother u hux off hoff_lt
      · intro addr haddr
        rw [hmem]
        exact revNodeMem_outside_slot haddr
      · rw [hmem]
        exact revNodeMem_preserved hs.1 hs.2.1

end

end MinCostFlow.LinkCut.Prog
