module

public import MinCostFlow.LinkCut.Prog.SplayRotateTail

/-!
Top-level rotation execution theorem `rotateBody_runs` for L-limb `Num` path
aggregates: handles the `OFF_PARENT = 0` root no-op case via `rotateBody_zero_runs`,
shares a unified structural rewiring lemma across both `zigRight` and `zigLeft`,
and finishes via `rotateTail_runs` with cost+heap bound `K_ROTATE L`.
-/

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num

@[expose] public section

private theorem fieldAddr_in_arena {nodesBase cap u off : ℕ}
    (hu1 : 1 ≤ u) (hu2 : u ≤ cap) (hoff : off < NODE_STRIDE) :
    nodesBase + NODE_STRIDE ≤ nodesBase + NODE_STRIDE * u + off ∧
      nodesBase + NODE_STRIDE * u + off < nodesBase + NODE_STRIDE * (cap + 1) := by
  have h1 : NODE_STRIDE * 1 ≤ NODE_STRIDE * u := Nat.mul_le_mul_left NODE_STRIDE hu1
  have h2 : NODE_STRIDE * u ≤ NODE_STRIDE * cap := Nat.mul_le_mul_left NODE_STRIDE hu2
  unfold NODE_STRIDE at hoff ⊢
  rw [Nat.mul_add, Nat.mul_one] at *
  omega

private abbrev rotateTailStmt (sp : SplayProcs) : Stmt :=
  (Stmt.cond (.reg 8)
     (Stmt.assign 9 (fieldLoadExpr 2 OFF_LEFT) ;;
      setChildAndParentStmt 4 OFF_RIGHT 9 3 10 ;;
      Stmt.store (fieldAddrExpr 2 OFF_LEFT) (.reg 3))
     (Stmt.assign 9 (fieldLoadExpr 2 OFF_RIGHT) ;;
      setChildAndParentStmt 4 OFF_LEFT 9 3 10 ;;
      Stmt.store (fieldAddrExpr 2 OFF_RIGHT) (.reg 3))) ;;
  Stmt.store (fieldAddrExpr 4 OFF_PARENT) (.reg 1) ;;
  Stmt.store (fieldAddrExpr 2 OFF_PARENT) (.reg 5) ;;
  Stmt.cond (.reg 5)
    (Stmt.assign 10 (nodePtrExpr 0 5) ;;
     Stmt.assign 11 (fieldLoadExpr 10 OFF_LEFT) ;;
     Stmt.cond (.bin .eq (.reg 3) (.reg 11))
       (Stmt.store (fieldAddrExpr 10 OFF_LEFT) (.reg 1))
       (Stmt.store (fieldAddrExpr 10 OFF_RIGHT) (.reg 1)))
    Stmt.nop ;;
  Stmt.call 11 sp.pull [.reg 0, .reg 3] ;;
  Stmt.call 11 sp.pull [.reg 0, .reg 1] ;;
  Stmt.ret (.const 0)

private theorem rotateRewireRaw_runs {w nodesBase cap : ℕ} (pr : Program) (mem₀ : ℕ → ℕ)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    {x p_id pp_p bOff pChildOff bVal : ℕ}
    (hx1 : 1 ≤ x) (hx2 : x ≤ cap) (hp1 : 1 ≤ p_id) (hp2 : p_id ≤ cap) (hpx : p_id ≠ x)
    (hbOff : bOff = OFF_LEFT ∨ bOff = OFF_RIGHT)
    (hpOff : pChildOff = OFF_LEFT ∨ pChildOff = OFF_RIGHT)
    (hb_eq : bVal = nodeField mem₀ nodesBase x bOff)
    (hb_bound : bVal ≠ 0 → 1 ≤ bVal ∧ bVal ≤ cap)
    (hb_ne_x : bVal ≠ x) (hb_ne_p : bVal ≠ p_id)
    (st_pre : State)
    (hst_mem : st_pre.mem =
      Function.update (Function.update mem₀ (nodesBase + NODE_STRIDE * x + OFF_PPAR) pp_p)
        (nodesBase + NODE_STRIDE * p_id + OFF_PPAR) 0)
    (hr0 : st_pre.regs 0 = nodesBase)
    (hr1 : st_pre.regs 1 = x)
    (hr2 : st_pre.regs 2 = nodesBase + NODE_STRIDE * x)
    (hr3 : st_pre.regs 3 = p_id)
    (hr4 : st_pre.regs 4 = nodesBase + NODE_STRIDE * p_id)
    (ω : ℕ → Bool) :
    ∃ st_mid c_br,
      Runs w pr ω
        (Stmt.assign 9 (fieldLoadExpr 2 bOff) ;;
         setChildAndParentStmt 4 pChildOff 9 3 10 ;;
         Stmt.store (fieldAddrExpr 2 bOff) (.reg 3))
        st_pre .normal st_mid c_br ∧
      c_br ≤ 32 ∧
      st_mid.pos = st_pre.pos ∧
      (∀ r < 9, st_mid.regs r = st_pre.regs r) ∧
      nodeField st_mid.mem nodesBase p_id pChildOff = bVal ∧
      nodeField st_mid.mem nodesBase x bOff = p_id ∧
      nodeField st_mid.mem nodesBase x OFF_PPAR = pp_p ∧
      nodeField st_mid.mem nodesBase p_id OFF_PPAR = 0 ∧
      (bVal ≠ 0 → nodeField st_mid.mem nodesBase bVal OFF_PARENT = p_id) ∧
      (∀ u off, off < NODE_STRIDE →
        (u = p_id → off ≠ OFF_PPAR ∧ off ≠ pChildOff) →
        (u = x → off ≠ OFF_PPAR ∧ off ≠ bOff) →
        (bVal ≠ 0 → u = bVal → off ≠ OFF_PARENT) →
        nodeField st_mid.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
        nodeField st_mid.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      MemPreservedOutside (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        mem₀ st_mid.mem := by
  have _ := hr1
  have hbOff_lt : bOff < NODE_STRIDE := by rcases hbOff with rfl | rfl <;> decide
  have hpOff_lt : pChildOff < NODE_STRIDE := by rcases hpOff with rfl | rfl <;> decide
  have hbOff_ne_pp : bOff ≠ OFF_PPAR := by rcases hbOff with rfl | rfl <;> decide
  have hpOff_ne_pp : pChildOff ≠ OFF_PPAR := by rcases hpOff with rfl | rfl <;> decide
  let ptrX := nodesBase + NODE_STRIDE * x
  let ptrP := nodesBase + NODE_STRIDE * p_id
  have hx_off_lt : ptrX + bOff < 2 ^ w := nodeAddr_lt_pow hbase hx2 hbOff_lt
  have hp_off_lt : ptrP + pChildOff < 2 ^ w := nodeAddr_lt_pow hbase hp2 hpOff_lt
  have hload_val : st_pre.mem (ptrX + bOff) = bVal := by
    rw [hst_mem, Function.update_of_ne (node_field_addr_ne hpx.symm hbOff_lt (by decide)),
      Function.update_of_ne (node_same_field_addr_ne hbOff_ne_pp)]
    exact hb_eq.symm
  let st_a : State := { st_pre with regs := Function.update st_pre.regs 9 bVal }
  have hr_a : Runs w pr ω (Stmt.assign 9 (fieldLoadExpr 2 bOff)) st_pre .normal st_a 5 := by
    have hev : (fieldLoadExpr 2 bOff).eval w st_pre = some bVal :=
      (eval_fieldLoadExpr hr2 hx_off_lt).trans (congrArg some hload_val)
    simpa [fieldLoadExpr, fieldAddrExpr, Expr.size] using runs_assign_iff.mpr ⟨bVal, hev, rfl, rfl, rfl⟩
  have ha0 : st_a.regs 0 = nodesBase := by simp [st_a, hr0]
  have ha2 : st_a.regs 2 = ptrX := by dsimp only [ptrX]; simp [st_a, hr2]
  have ha3 : st_a.regs 3 = p_id := by simp [st_a, hr3]
  have ha4 : st_a.regs 4 = ptrP := by dsimp only [ptrP]; simp [st_a, hr4]
  have ha9 : st_a.regs 9 = bVal := by simp [st_a]
  rcases setChildAndParentStmt_runs pr st_a hbase pChildOff ha4 ha9 ha3 ha0 hp_off_lt hb_bound ω with
    ⟨st_b, c_set, hr_b, hc_set, hpos_b, hregs_b, hmem_b⟩
  change (if bVal = 0 then st_b.mem = Function.update st_pre.mem (ptrP + pChildOff) bVal
    else st_b.mem = Function.update (Function.update st_pre.mem (ptrP + pChildOff) bVal)
      (nodesBase + NODE_STRIDE * bVal + OFF_PARENT) p_id) at hmem_b
  have hb2 : st_b.regs 2 = ptrX := (hregs_b 2 (by decide)).trans ha2
  have hb3 : st_b.regs 3 = p_id := (hregs_b 3 (by decide)).trans ha3
  let mem_mid := Function.update st_b.mem (ptrX + bOff) p_id
  let st_mid : State := { mem := mem_mid, regs := st_b.regs, pos := st_b.pos }
  have hr_x : Runs w pr ω (Stmt.store (fieldAddrExpr 2 bOff) (.reg 3)) st_b .normal st_mid 5 := by
    simpa [fieldAddrExpr, Expr.size] using runs_store_iff.mpr
      ⟨ptrX + bOff, p_id, eval_fieldAddrExpr hb2 hx_off_lt, Expr.eval_reg_of_eq hb3, rfl, rfl, rfl⟩
  have hr_all : Runs w pr ω
      (Stmt.assign 9 (fieldLoadExpr 2 bOff) ;;
       setChildAndParentStmt 4 pChildOff 9 3 10 ;;
       Stmt.store (fieldAddrExpr 2 bOff) (.reg 3))
      st_pre .normal st_mid (5 + (c_set + 5 + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st_a, 5, c_set + 5 + 1, hr_a,
      runs_seq_iff.mpr (Or.inr ⟨st_b, c_set, 5, hr_b, hr_x, rfl⟩), rfl⟩)
  have hregs_mid : ∀ r < 9, st_mid.regs r = st_pre.regs r := fun r hr => by
    have hr10 : r < 10 := Nat.lt_succ_of_lt hr
    have hne9 : r ≠ 9 := Nat.ne_of_lt hr
    exact (hregs_b r hr10).trans (Function.update_of_ne hne9 _ _)
  have hagree : ∀ u off, off < NODE_STRIDE →
      (u = p_id → off ≠ OFF_PPAR ∧ off ≠ pChildOff) →
      (u = x → off ≠ OFF_PPAR ∧ off ≠ bOff) →
      (bVal ≠ 0 → u = bVal → off ≠ OFF_PARENT) →
      nodeField st_mid.mem nodesBase u off = nodeField mem₀ nodesBase u off := by
    intro u off hoff hup hux hub
    have hm_x : mem_mid (nodesBase + NODE_STRIDE * u + off) =
        st_b.mem (nodesBase + NODE_STRIDE * u + off) := by
      dsimp only [mem_mid, ptrX]
      by_cases he : u = x
      · subst he; exact Function.update_of_ne (node_same_field_addr_ne (hux rfl).2) _ _
      · exact Function.update_of_ne (node_field_addr_ne he hoff hbOff_lt) _ _
    have hm_b : st_b.mem (nodesBase + NODE_STRIDE * u + off) =
        st_pre.mem (nodesBase + NODE_STRIDE * u + off) := by
      have hm_p : Function.update st_pre.mem (ptrP + pChildOff) bVal (nodesBase + NODE_STRIDE * u + off) =
          st_pre.mem (nodesBase + NODE_STRIDE * u + off) := by
        dsimp only [ptrP]
        by_cases he : u = p_id
        · subst he; exact Function.update_of_ne (node_same_field_addr_ne (hup rfl).2) _ _
        · exact Function.update_of_ne (node_field_addr_ne he hoff hpOff_lt) _ _
      by_cases hbz : bVal = 0
      · simp only [hbz, ↓reduceIte] at hmem_b; rw [hmem_b, ← hbz, hm_p]
      · simp only [hbz, ↓reduceIte] at hmem_b; rw [hmem_b]
        rw [Function.update_of_ne (by
          by_cases he : u = bVal
          · subst he; exact node_same_field_addr_ne (hub hbz rfl)
          · exact node_field_addr_ne he hoff (by decide))]
        exact hm_p
    have hm_pre : st_pre.mem (nodesBase + NODE_STRIDE * u + off) =
        mem₀ (nodesBase + NODE_STRIDE * u + off) := by
      rw [hst_mem]
      rw [Function.update_of_ne (by
        by_cases he : u = p_id
        · subst he; exact node_same_field_addr_ne (hup rfl).1
        · exact node_field_addr_ne he hoff (by decide))]
      by_cases he : u = x
      · subst he; exact Function.update_of_ne (node_same_field_addr_ne (hux rfl).1) _ _
      · exact Function.update_of_ne (node_field_addr_ne he hoff (by decide)) _ _
    dsimp only [nodeField]; change mem_mid _ = mem₀ _; rw [hm_x, hm_b, hm_pre]
  have hp_child_eq : nodeField st_mid.mem nodesBase p_id pChildOff = bVal := by
    have hm_x : mem_mid (ptrP + pChildOff) = st_b.mem (ptrP + pChildOff) :=
      Function.update_of_ne (node_field_addr_ne hpx hpOff_lt hbOff_lt) _ _
    dsimp only [nodeField]; change mem_mid (ptrP + pChildOff) = bVal; rw [hm_x]
    by_cases hbz : bVal = 0
    · simp only [hbz, ↓reduceIte] at hmem_b; rw [hmem_b, Function.update_self, hbz]
    · simp only [hbz, ↓reduceIte] at hmem_b
      rw [hmem_b, Function.update_of_ne (node_field_addr_ne hb_ne_p.symm hpOff_lt (by decide)),
        Function.update_self]
  have hx_b_eq : nodeField st_mid.mem nodesBase x bOff = p_id := by
    dsimp only [nodeField]; change mem_mid (ptrX + bOff) = p_id; exact Function.update_self _ _ _
  have hx_pp_eq : nodeField st_mid.mem nodesBase x OFF_PPAR = pp_p := by
    have hm_x : mem_mid (ptrX + OFF_PPAR) = st_b.mem (ptrX + OFF_PPAR) :=
      Function.update_of_ne (node_same_field_addr_ne hbOff_ne_pp.symm) _ _
    have hm_b : st_b.mem (ptrX + OFF_PPAR) = st_pre.mem (ptrX + OFF_PPAR) := by
      have hm_p : Function.update st_pre.mem (ptrP + pChildOff) bVal (ptrX + OFF_PPAR) =
          st_pre.mem (ptrX + OFF_PPAR) :=
        Function.update_of_ne (node_field_addr_ne hpx.symm (by decide) hpOff_lt) _ _
      by_cases hbz : bVal = 0
      · simp only [hbz, ↓reduceIte] at hmem_b; rw [hmem_b, ← hbz, hm_p]
      · simp only [hbz, ↓reduceIte] at hmem_b; rw [hmem_b]
        rw [Function.update_of_ne (by
          by_cases he : x = bVal
          · subst he; exact absurd rfl hb_ne_x
          · exact node_field_addr_ne he (by decide) (by decide))]
        exact hm_p
    dsimp only [nodeField]; change mem_mid (ptrX + OFF_PPAR) = pp_p
    rw [hm_x, hm_b, hst_mem,
      Function.update_of_ne (node_field_addr_ne hpx.symm (by decide) (by decide)),
      Function.update_self]
  have hp_pp_eq : nodeField st_mid.mem nodesBase p_id OFF_PPAR = 0 := by
    have hm_x : mem_mid (ptrP + OFF_PPAR) = st_b.mem (ptrP + OFF_PPAR) :=
      Function.update_of_ne (node_field_addr_ne hpx (by decide) hbOff_lt) _ _
    have hm_b : st_b.mem (ptrP + OFF_PPAR) = st_pre.mem (ptrP + OFF_PPAR) := by
      have hm_p : Function.update st_pre.mem (ptrP + pChildOff) bVal (ptrP + OFF_PPAR) =
          st_pre.mem (ptrP + OFF_PPAR) :=
        Function.update_of_ne (node_same_field_addr_ne hpOff_ne_pp.symm) _ _
      by_cases hbz : bVal = 0
      · simp only [hbz, ↓reduceIte] at hmem_b; rw [hmem_b, ← hbz, hm_p]
      · simp only [hbz, ↓reduceIte] at hmem_b; rw [hmem_b]
        rw [Function.update_of_ne (node_field_addr_ne hb_ne_p.symm (by decide) (by decide))]
        exact hm_p
    dsimp only [nodeField]; change mem_mid (ptrP + OFF_PPAR) = 0
    rw [hm_x, hm_b, hst_mem, Function.update_self]
  have hb_par_eq : bVal ≠ 0 → nodeField st_mid.mem nodesBase bVal OFF_PARENT = p_id := fun hbz => by
    have hm_x : mem_mid (nodesBase + NODE_STRIDE * bVal + OFF_PARENT) =
        st_b.mem (nodesBase + NODE_STRIDE * bVal + OFF_PARENT) :=
      Function.update_of_ne (node_field_addr_ne hb_ne_x (by decide) hbOff_lt) _ _
    dsimp only [nodeField]
    change mem_mid (nodesBase + NODE_STRIDE * bVal + OFF_PARENT) = p_id
    rw [hm_x]
    simp only [hbz, ↓reduceIte] at hmem_b
    rw [hmem_b, Function.update_self]
  have hns_mid : ∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
      nodeField st_mid.mem nodesBase u off = nodeField mem₀ nodesBase u off := fun u _ off hoff => by
    have hne_b : off ≠ bOff := by rcases hbOff with rfl | rfl <;> [exact hoff.2.1; exact hoff.2.2.1]
    have hne_p : off ≠ pChildOff := by rcases hpOff with rfl | rfl <;> [exact hoff.2.1; exact hoff.2.2.1]
    exact hagree u off hoff.1 (fun _ => ⟨hoff.2.2.2.2.1, hne_p⟩)
      (fun _ => ⟨hoff.2.2.2.2.1, hne_b⟩) (fun _ _ => hoff.2.2.2.1)
  have hpre_mid : MemPreservedOutside (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      mem₀ st_mid.mem := by
    have ax_pp := fieldAddr_in_arena (nodesBase := nodesBase) hx1 hx2 (show OFF_PPAR < NODE_STRIDE by decide)
    have ap_pp := fieldAddr_in_arena (nodesBase := nodesBase) hp1 hp2 (show OFF_PPAR < NODE_STRIDE by decide)
    have ap_c := fieldAddr_in_arena (nodesBase := nodesBase) hp1 hp2 hpOff_lt
    have ax_b := fieldAddr_in_arena (nodesBase := nodesBase) hx1 hx2 hbOff_lt
    have hpre_pre : MemPreservedOutside (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        mem₀ st_pre.mem := by
      rw [hst_mem]
      exact memPreservedOutside_trans (memPreservedOutside_update ax_pp.1 ax_pp.2)
        (memPreservedOutside_update ap_pp.1 ap_pp.2)
    have hpre_b : MemPreservedOutside (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        st_pre.mem st_b.mem := by
      by_cases hbz : bVal = 0
      · simp only [hbz, ↓reduceIte] at hmem_b; rw [hmem_b]
        exact memPreservedOutside_update ap_c.1 ap_c.2
      · rcases hb_bound hbz with ⟨hb1, hb2⟩
        have ab_par := fieldAddr_in_arena (nodesBase := nodesBase) hb1 hb2 (show OFF_PARENT < NODE_STRIDE by decide)
        simp only [hbz, ↓reduceIte] at hmem_b; rw [hmem_b]
        exact memPreservedOutside_trans (memPreservedOutside_update ap_c.1 ap_c.2)
          (memPreservedOutside_update ab_par.1 ab_par.2)
    exact memPreservedOutside_trans hpre_pre
      (memPreservedOutside_trans hpre_b (memPreservedOutside_update ax_b.1 ax_b.2))
  exact ⟨st_mid, _, hr_all, by omega, hpos_b.trans rfl, hregs_mid,
    hp_child_eq, hx_b_eq, hx_pp_eq, hp_pp_eq, hb_par_eq, hagree, hns_mid, hpre_mid⟩

private theorem sibling_preserve_mid {w h L : ℕ} {mem₀ mem_mid : ℕ → ℕ}
    {nodesBase cap parQ p_id x bVal : ℕ} {q : AuxTree}
    (hq : TreeMemMatch w h L mem₀ nodesBase cap q parQ 0)
    (hq_disj : ∀ u ∈ q.toList, u ≠ p_id ∧ u ≠ x ∧ (bVal ≠ 0 → u ≠ bVal))
    (hagree : ∀ u off, off < NODE_STRIDE →
      (u = p_id → False) → (u = x → False) → (bVal ≠ 0 → u = bVal → False) →
      nodeField mem_mid nodesBase u off = nodeField mem₀ nodesBase u off)
    (hle : mem₀ (nodesBase - 1) ≤ mem_mid (nodesBase - 1))
    (hheap : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a →
      a < mem₀ (nodesBase - 1) → mem_mid a = mem₀ a) :
    TreeMemMatch w h L mem_mid nodesBase cap q parQ 0 :=
  memAgree_treeMemMatch_of_nodeList hq
    (fun u hu off hoff => hagree u off hoff (fun he => (hq_disj u hu).1 he)
      (fun he => (hq_disj u hu).2.1 he) (fun hbz he => (hq_disj u hu).2.2 hbz he))
    hle hheap

private theorem movedChild_reparent_mid {w h L : ℕ} {mem₀ mem_mid : ℕ → ℕ}
    {nodesBase cap x p_id : ℕ} {B : AuxTree}
    (hB : TreeMemMatch w h L mem₀ nodesBase cap B x 0) (hB_nd : B.toList.Nodup)
    (hB_disj : ∀ u ∈ B.toList, u ≠ p_id ∧ u ≠ x)
    (hB_par : B ≠ .leaf → nodeField mem_mid nodesBase B.rootId OFF_PARENT = p_id)
    (hagree : ∀ u off, off < NODE_STRIDE →
      (u = p_id → False) → (u = x → False) → (B.rootId ≠ 0 → u = B.rootId → off ≠ OFF_PARENT) →
      nodeField mem_mid nodesBase u off = nodeField mem₀ nodesBase u off)
    (hle : mem₀ (nodesBase - 1) ≤ mem_mid (nodesBase - 1))
    (hheap : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a →
      a < mem₀ (nodesBase - 1) → mem_mid a = mem₀ a) :
    TreeMemMatch w h L mem_mid nodesBase cap B p_id 0 := by
  refine treeMemMatch_reparent_root hB hB_nd hB_par (fun hB_ne => ?_) (fun u hu off hoff hroot => ?_) hle hheap
  · have hbz : B.rootId ≠ 0 := by
      cases B with
      | leaf => exact absurd rfl hB_ne
      | node bid _ _ => exact Nat.ne_of_gt hB.1
    rw [hagree B.rootId OFF_PPAR (by decide)
      (fun h => (hB_disj B.rootId (by cases B with | leaf => exact absurd rfl hB_ne | node bid _ _ => simp [AuxTree.rootId, AuxTree.toList])).1 h)
      (fun h => (hB_disj B.rootId (by cases B with | leaf => exact absurd rfl hB_ne | node bid _ _ => simp [AuxTree.rootId, AuxTree.toList])).2 h)
      (fun _ _ => by decide)]
    cases B with
    | leaf => exact absurd rfl hB_ne
    | node _ _ _ => exact hB.2.2.2.2.2.1
  · exact hagree u off hoff (fun h => (hB_disj u hu).1 h) (fun h => (hB_disj u hu).2 h)
      (fun _ h => (hroot h).1)

private theorem rotateMid_zigRight {w h L nodesBase cap x p_id g_id pp_p pp : ℕ}
    (pr : Program) (sp : SplayProcs) (mem₀ : ℕ → ℕ)
    (hp_ok : SplayProgramOk w h pr sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase) (hL_hdr : mem₀ (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₀ (nodesBase - 1))
    (hz : ZeroFrom mem₀ (mem₀ (nodesBase - 1)))
    (hhp_lt : mem₀ (nodesBase - 1) + 8 * L < 2 ^ w)
    (h0 : SlotZeroOk mem₀ nodesBase)
    {t : AuxTree} (ht : TreeMemMatch w h L mem₀ nodesBase cap t 0 pp) (hnd : t.toList.Nodup)
    (hx_mem : x ∈ t.toList) (hx_ne_root : x ≠ t.rootId)
    (hp_def : p_id = t.parentIn x 0) (hg_def : g_id = t.parentIn p_id 0)
    (hpp_def : pp_p = if t.rootId = p_id then pp else 0)
    (hx_rev0 : nodeField mem₀ nodesBase x OFF_REV = 0)
    (hp_rev0 : nodeField mem₀ nodesBase p_id OFF_REV = 0)
    (hx_ht0 : nodeField mem₀ nodesBase x OFF_HAS_TAG = 0)
    (hp_ht0 : nodeField mem₀ nodesBase p_id OFF_HAS_TAG = 0)
    {A B sr : AuxTree}
    (hsub_eq : t.findSubtree p_id = AuxTree.node p_id (AuxTree.node x A B) sr)
    (st_pre : State)
    (hst_mem : st_pre.mem =
      Function.update (Function.update mem₀ (nodesBase + NODE_STRIDE * x + OFF_PPAR) pp_p)
        (nodesBase + NODE_STRIDE * p_id + OFF_PPAR) 0)
    (hr0 : st_pre.regs 0 = nodesBase) (hr1 : st_pre.regs 1 = x)
    (hr2 : st_pre.regs 2 = nodesBase + NODE_STRIDE * x)
    (hr3 : st_pre.regs 3 = p_id) (hr4 : st_pre.regs 4 = nodesBase + NODE_STRIDE * p_id)
    (hr5 : st_pre.regs 5 = g_id) (hr8 : st_pre.regs 8 = 0) (ω : ℕ → Bool) :
    ∃ st' c_rest,
      Runs w pr ω (rotateTailStmt sp) st_pre (.returned 0) st' c_rest ∧
      c_rest + (st'.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤ 2 * K_PULL L + 95 ∧
      mem₀ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      st'.mem (nodesBase - 1) ≤ mem₀ (nodesBase - 1) + 8 * L ∧
      TreeMemMatch w h L st'.mem nodesBase cap (t.rotateAt x) 0 pp ∧
      (t.rotateAt x).toList.Perm t.toList ∧
      (t.rotateAt x).evalInorder (revFlag st'.mem nodesBase) false =
        t.evalInorder (revFlag mem₀ nodesBase) false ∧
      evalMemSteps st'.mem nodesBase h L (t.rotateAt x) false 0 =
        evalMemSteps mem₀ nodesBase h L t false 0 ∧
      (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) mem₀ st'.mem := by
  have hp_mem : p_id ∈ t.toList := hp_def ▸ (AuxTree.parentIn_mem_and_depth hnd hx_mem hx_ne_root).1
  have hm_p := AuxTree.findSubtree_match ht hp_mem
  rw [hsub_eq, ← hg_def, ← hpp_def] at hm_p
  rcases hm_p with ⟨hp1, hp2, hpL0, hpR0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hxl_m, hsr_m⟩
  rcases hxl_m with ⟨hx1, hx2, hxL0, hxR0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hA_m, hB_m⟩
  have hsub_nd := AuxTree.findSubtree_nodup (subId := p_id) hnd
  rw [hsub_eq] at hsub_nd
  simp only [AuxTree.toList, List.nodup_append, List.nodup_cons, List.mem_append,
    List.mem_singleton] at hsub_nd
  rcases hsub_nd with ⟨⟨⟨⟨_, _, hdisj_A_x⟩, hB_nd, hdisj_Ax_B⟩, _, hdisj_xl_p⟩, _, hdisj_all⟩
  have hpx : p_id ≠ x := fun h => hdisj_xl_p x (Or.inl (Or.inr rfl)) p_id rfl h.symm
  have hb_ne_x : B.rootId ≠ x := fun h => by
    cases B with
    | leaf => simp [AuxTree.rootId] at h; omega
    | node bid bl br =>
        simp only [AuxTree.rootId] at h
        have hm : x ∈ (AuxTree.node bid bl br).toList := h ▸ by simp [AuxTree.toList]
        exact hdisj_Ax_B x (Or.inr rfl) x hm rfl
  have hb_ne_p : B.rootId ≠ p_id := fun h => by
    cases B with
    | leaf => simp [AuxTree.rootId] at h; omega
    | node bid bl br =>
        simp only [AuxTree.rootId] at h
        have hm : p_id ∈ (AuxTree.node bid bl br).toList := h ▸ by simp [AuxTree.toList]
        exact hdisj_xl_p p_id (Or.inr hm) p_id rfl rfl
  have hb_bound : B.rootId ≠ 0 → 1 ≤ B.rootId ∧ B.rootId ≤ cap := fun hbz => by
    cases B with
    | leaf => exact absurd rfl hbz
    | node _ _ _ => exact ⟨hB_m.1, hB_m.2.1⟩
  rcases rotateRewireRaw_runs pr mem₀ hbase hx1 hx2 hp1 hp2 hpx (Or.inr rfl) (Or.inl rfl)
      hxR0.symm hb_bound hb_ne_x hb_ne_p st_pre hst_mem hr0 hr1 hr2 hr3 hr4 ω with
    ⟨st_mid, c_br, hr_br, hc_br, _, hregs_mid, hp_left_mid, hx_right_mid,
     hx_pp_mid, hp_pp_mid, hb_par_mid, hagree, hns_mid, hpre_mid⟩
  have hr_cond : Runs w pr ω
      (Stmt.cond (.reg 8)
        (Stmt.assign 9 (fieldLoadExpr 2 OFF_LEFT) ;;
         setChildAndParentStmt 4 OFF_RIGHT 9 3 10 ;;
         Stmt.store (fieldAddrExpr 2 OFF_LEFT) (.reg 3))
        (Stmt.assign 9 (fieldLoadExpr 2 OFF_RIGHT) ;;
         setChildAndParentStmt 4 OFF_LEFT 9 3 10 ;;
         Stmt.store (fieldAddrExpr 2 OFF_RIGHT) (.reg 3)))
      st_pre .normal st_mid (1 + c_br + 1) :=
    runs_cond_iff.mpr ⟨0, c_br, Expr.eval_reg_of_eq hr8, by simpa using hr_br, rfl⟩
  have hmid_hp : st_mid.mem (nodesBase - 1) = mem₀ (nodesBase - 1) :=
    hpre_mid (nodesBase - 1) (Or.inl (by unfold NODE_STRIDE; omega))
  have hle_mid : mem₀ (nodesBase - 1) ≤ st_mid.mem (nodesBase - 1) := by rw [hmid_hp]
  have hheap_mid : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a →
      a < mem₀ (nodesBase - 1) → st_mid.mem a = mem₀ a := fun a ha1 _ =>
    hpre_mid a (Or.inr ha1)
  have hA_disj : ∀ u ∈ A.toList, u ≠ p_id ∧ u ≠ x ∧ (B.rootId ≠ 0 → u ≠ B.rootId) := fun u hu =>
    ⟨fun h => hdisj_xl_p u (Or.inl (Or.inl hu)) p_id rfl h,
     fun h => hdisj_A_x u hu x rfl h,
     fun hbz h => by
       cases B with
       | leaf => exact hbz rfl
       | node bid bl br =>
           simp only [AuxTree.rootId] at h
           have hm : u ∈ (AuxTree.node bid bl br).toList := h ▸ by simp [AuxTree.toList]
           exact hdisj_Ax_B u (Or.inl hu) u hm rfl⟩
  have hsr_disj : ∀ u ∈ sr.toList, u ≠ p_id ∧ u ≠ x ∧ (B.rootId ≠ 0 → u ≠ B.rootId) := fun u hu =>
    ⟨fun h => hdisj_all p_id (Or.inr rfl) u hu h.symm,
     fun h => hdisj_all x (Or.inl (Or.inl (Or.inr rfl))) u hu h.symm,
     fun hbz h => by
       cases B with
       | leaf => exact hbz rfl
       | node bid bl br =>
           simp only [AuxTree.rootId] at h
           have hm : u ∈ (AuxTree.node bid bl br).toList := h ▸ by simp [AuxTree.toList]
           exact hdisj_all u (Or.inl (Or.inr hm)) u hu rfl⟩
  have hB_disj : ∀ u ∈ B.toList, u ≠ p_id ∧ u ≠ x := fun u hu =>
    ⟨fun h => hdisj_xl_p u (Or.inr hu) p_id rfl h,
     fun h => hdisj_Ax_B x (Or.inr rfl) u hu h.symm⟩
  have hA_mid := sibling_preserve_mid hA_m hA_disj
    (fun u off hoff hp hx hb => hagree u off hoff (fun h => absurd h hp) (fun h => absurd h hx) (fun h1 h2 => absurd h2 (hb h1)))
    hle_mid hheap_mid
  have hsr_mid := sibling_preserve_mid hsr_m hsr_disj
    (fun u off hoff hp hx hb => hagree u off hoff (fun h => absurd h hp) (fun h => absurd h hx) (fun h1 h2 => absurd h2 (hb h1)))
    hle_mid hheap_mid
  have hB_mid := movedChild_reparent_mid hB_m hB_nd hB_disj
    (fun hB_ne => hb_par_mid (by cases B with | leaf => exact absurd rfl hB_ne | node _ _ _ => exact Nat.ne_of_gt hB_m.1))
    (fun u off hoff hp hx hb => hagree u off hoff (fun h => absurd h hp) (fun h => absurd h hx) (fun h1 h2 => hb h1 h2))
    hle_mid hheap_mid
  have hx_left_mid : nodeField st_mid.mem nodesBase x OFF_LEFT = A.rootId := by
    rw [hagree x OFF_LEFT (by decide) (fun h => absurd h hpx.symm) (fun _ => ⟨by decide, by decide⟩)
      (fun _ h => absurd h hb_ne_x.symm)]
    exact hxL0
  have hp_right_mid : nodeField st_mid.mem nodesBase p_id OFF_RIGHT = sr.rootId := by
    rw [hagree p_id OFF_RIGHT (by decide) (fun _ => ⟨by decide, by decide⟩) (fun h => absurd h hpx)
      (fun _ h => absurd h hb_ne_p.symm)]
    exact hpR0
  let s' := AuxTree.node x A (AuxTree.node p_id B sr)
  have hs'_eq : s' = (t.findSubtree p_id).rotateAt x := by
    rw [hsub_eq, AuxTree.rotateAt_zigRight A B sr hpx]
  have hs'_perm : s'.toList.Perm (t.findSubtree p_id).toList := by
    rw [hs'_eq]; exact AuxTree.rotateAt_toList_perm x _
  have hs'_eval : s'.evalInorder (revFlag st_mid.mem nodesBase) false =
      (t.findSubtree p_id).evalInorder (revFlag mem₀ nodesBase) false := by
    have hrev_agree : ∀ u ∈ s'.toList, revFlag st_mid.mem nodesBase u = revFlag mem₀ nodesBase u := fun u hu => by
      have hu_le := (ht.nodup_perm_mem (AuxTree.findSubtree_subset (hs'_perm.mem_iff.1 hu))).2
      simp [revFlag, hns_mid u hu_le OFF_REV (by decide)]
    rw [AuxTree.evalInorder_agree _ (revFlag mem₀ nodesBase) _ false hrev_agree, hsub_eq]
    have hrx : revFlag mem₀ nodesBase x = false := by simp [revFlag, hx_rev0]
    have hrp : revFlag mem₀ nodesBase p_id = false := by simp [revFlag, hp_rev0]
    simp [s', AuxTree.evalInorder, hrx, hrp, List.append_assoc]
  have hout_mid : ∀ u ≤ cap, u ∉ (t.findSubtree p_id).toList → ∀ off < NODE_STRIDE,
      nodeField st_mid.mem nodesBase u off = nodeField mem₀ nodesBase u off := fun u _ hu off hoff => by
    rw [hsub_eq] at hu
    refine hagree u off hoff ?_ ?_ ?_
    · intro h; exact (hu (h ▸ by simp [AuxTree.toList])).elim
    · intro h; exact (hu (h ▸ by simp [AuxTree.toList])).elim
    · intro hbz h
      cases B with
      | leaf => exact absurd rfl hbz
      | node bid _ _ =>
          simp only [AuxTree.rootId] at h
          exact (hu (h ▸ by simp [AuxTree.toList])).elim
  rcases rotateTail_runs pr sp mem₀ hp_ok hbase hnb hL_hdr harena hz hhp_lt h0 ht hnd hx_mem
      hx_ne_root hp_def hg_def hpp_def st_mid
      (Or.inr ⟨rfl, hx_left_mid, hx_right_mid, hA_mid⟩)
      hs'_eq hs'_perm hs'_eval hp_left_mid hp_right_mid hB_mid hsr_mid
      hx_pp_mid hp_pp_mid hx_rev0 hp_rev0 hx_ht0 hp_ht0 hns_mid hout_mid hpre_mid
      (hregs_mid 0 (by decide) |>.trans hr0) (hregs_mid 1 (by decide) |>.trans hr1)
      (hregs_mid 2 (by decide) |>.trans hr2) (hregs_mid 3 (by decide) |>.trans hr3)
      (hregs_mid 4 (by decide) |>.trans hr4) (hregs_mid 5 (by decide) |>.trans hr5) ω with
    ⟨st', c_tail, hr_tail, hc_tail, hhp_ge, hhp_le, ht_rot, hperm_rot, heval_rot,
     hsteps_rot, hns_rot, hout_rot, hlct_rot⟩
  exact ⟨st', (1 + c_br + 1) + c_tail + 1,
    runs_seq_iff.mpr (Or.inr ⟨st_mid, _, _, hr_cond, hr_tail, rfl⟩),
    by omega, hhp_ge, hhp_le, ht_rot, hperm_rot, heval_rot, hsteps_rot, hns_rot, hout_rot, hlct_rot⟩

private theorem rotateMid_zigLeft {w h L nodesBase cap x p_id g_id pp_p pp : ℕ}
    (pr : Program) (sp : SplayProcs) (mem₀ : ℕ → ℕ)
    (hp_ok : SplayProgramOk w h pr sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase) (hL_hdr : mem₀ (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₀ (nodesBase - 1))
    (hz : ZeroFrom mem₀ (mem₀ (nodesBase - 1)))
    (hhp_lt : mem₀ (nodesBase - 1) + 8 * L < 2 ^ w)
    (h0 : SlotZeroOk mem₀ nodesBase)
    {t : AuxTree} (ht : TreeMemMatch w h L mem₀ nodesBase cap t 0 pp) (hnd : t.toList.Nodup)
    (hx_mem : x ∈ t.toList) (hx_ne_root : x ≠ t.rootId)
    (hp_def : p_id = t.parentIn x 0) (hg_def : g_id = t.parentIn p_id 0)
    (hpp_def : pp_p = if t.rootId = p_id then pp else 0)
    (hx_rev0 : nodeField mem₀ nodesBase x OFF_REV = 0)
    (hp_rev0 : nodeField mem₀ nodesBase p_id OFF_REV = 0)
    (hx_ht0 : nodeField mem₀ nodesBase x OFF_HAS_TAG = 0)
    (hp_ht0 : nodeField mem₀ nodesBase p_id OFF_HAS_TAG = 0)
    {sl C D : AuxTree}
    (hsl_cond : sl = AuxTree.leaf ∨ sl.rootId ≠ x)
    (hsub_eq : t.findSubtree p_id = AuxTree.node p_id sl (AuxTree.node x C D))
    (st_pre : State)
    (hst_mem : st_pre.mem =
      Function.update (Function.update mem₀ (nodesBase + NODE_STRIDE * x + OFF_PPAR) pp_p)
        (nodesBase + NODE_STRIDE * p_id + OFF_PPAR) 0)
    (hr0 : st_pre.regs 0 = nodesBase) (hr1 : st_pre.regs 1 = x)
    (hr2 : st_pre.regs 2 = nodesBase + NODE_STRIDE * x)
    (hr3 : st_pre.regs 3 = p_id) (hr4 : st_pre.regs 4 = nodesBase + NODE_STRIDE * p_id)
    (hr5 : st_pre.regs 5 = g_id) (hr8 : st_pre.regs 8 = 1) (ω : ℕ → Bool) :
    ∃ st' c_rest,
      Runs w pr ω (rotateTailStmt sp) st_pre (.returned 0) st' c_rest ∧
      c_rest + (st'.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤ 2 * K_PULL L + 95 ∧
      mem₀ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      st'.mem (nodesBase - 1) ≤ mem₀ (nodesBase - 1) + 8 * L ∧
      TreeMemMatch w h L st'.mem nodesBase cap (t.rotateAt x) 0 pp ∧
      (t.rotateAt x).toList.Perm t.toList ∧
      (t.rotateAt x).evalInorder (revFlag st'.mem nodesBase) false =
        t.evalInorder (revFlag mem₀ nodesBase) false ∧
      evalMemSteps st'.mem nodesBase h L (t.rotateAt x) false 0 =
        evalMemSteps mem₀ nodesBase h L t false 0 ∧
      (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) mem₀ st'.mem := by
  have hp_mem : p_id ∈ t.toList := hp_def ▸ (AuxTree.parentIn_mem_and_depth hnd hx_mem hx_ne_root).1
  have hm_p := AuxTree.findSubtree_match ht hp_mem
  rw [hsub_eq, ← hg_def, ← hpp_def] at hm_p
  rcases hm_p with ⟨hp1, hp2, hpL0, hpR0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsl_m, hxr_m⟩
  rcases hxr_m with ⟨hx1, hx2, hxL0, hxR0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hC_m, hD_m⟩
  have hsub_nd := AuxTree.findSubtree_nodup (subId := p_id) hnd
  rw [hsub_eq] at hsub_nd
  simp only [AuxTree.toList, List.nodup_append, List.nodup_cons, List.mem_append,
    List.mem_singleton] at hsub_nd
  rcases hsub_nd with ⟨⟨_, _, hdisj_sl_p⟩, ⟨⟨hC_nd, _, hdisj_C_x⟩, _, hdisj_Cx_D⟩, hdisj_all⟩
  have hpx : p_id ≠ x := fun h => hdisj_all p_id (Or.inr rfl) x (Or.inl (Or.inr rfl)) h
  have hc_ne_x : C.rootId ≠ x := fun h => by
    cases C with
    | leaf => simp [AuxTree.rootId] at h; omega
    | node cid cl cr =>
        simp only [AuxTree.rootId] at h
        have hm : x ∈ (AuxTree.node cid cl cr).toList := h ▸ by simp [AuxTree.toList]
        exact hdisj_C_x x hm x rfl rfl
  have hc_ne_p : C.rootId ≠ p_id := fun h => by
    cases C with
    | leaf => simp [AuxTree.rootId] at h; omega
    | node cid cl cr =>
        simp only [AuxTree.rootId] at h
        have hm : p_id ∈ (AuxTree.node cid cl cr).toList := h ▸ by simp [AuxTree.toList]
        exact hdisj_all p_id (Or.inr rfl) p_id (Or.inl (Or.inl hm)) rfl
  have hc_bound : C.rootId ≠ 0 → 1 ≤ C.rootId ∧ C.rootId ≤ cap := fun hcz => by
    cases C with
    | leaf => exact absurd rfl hcz
    | node _ _ _ => exact ⟨hC_m.1, hC_m.2.1⟩
  rcases rotateRewireRaw_runs pr mem₀ hbase hx1 hx2 hp1 hp2 hpx (Or.inl rfl) (Or.inr rfl)
      hxL0.symm hc_bound hc_ne_x hc_ne_p st_pre hst_mem hr0 hr1 hr2 hr3 hr4 ω with
    ⟨st_mid, c_br, hr_br, hc_br, _, hregs_mid, hp_right_mid, hx_left_mid,
     hx_pp_mid, hp_pp_mid, hc_par_mid, hagree, hns_mid, hpre_mid⟩
  have hr_cond : Runs w pr ω
      (Stmt.cond (.reg 8)
        (Stmt.assign 9 (fieldLoadExpr 2 OFF_LEFT) ;;
         setChildAndParentStmt 4 OFF_RIGHT 9 3 10 ;;
         Stmt.store (fieldAddrExpr 2 OFF_LEFT) (.reg 3))
        (Stmt.assign 9 (fieldLoadExpr 2 OFF_RIGHT) ;;
         setChildAndParentStmt 4 OFF_LEFT 9 3 10 ;;
         Stmt.store (fieldAddrExpr 2 OFF_RIGHT) (.reg 3)))
      st_pre .normal st_mid (1 + c_br + 1) :=
    runs_cond_iff.mpr ⟨1, c_br, Expr.eval_reg_of_eq hr8, by simpa using hr_br, rfl⟩
  have hmid_hp : st_mid.mem (nodesBase - 1) = mem₀ (nodesBase - 1) :=
    hpre_mid (nodesBase - 1) (Or.inl (by unfold NODE_STRIDE; omega))
  have hle_mid : mem₀ (nodesBase - 1) ≤ st_mid.mem (nodesBase - 1) := by rw [hmid_hp]
  have hheap_mid : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a →
      a < mem₀ (nodesBase - 1) → st_mid.mem a = mem₀ a := fun a ha1 _ =>
    hpre_mid a (Or.inr ha1)
  have hsl_disj : ∀ u ∈ sl.toList, u ≠ p_id ∧ u ≠ x ∧ (C.rootId ≠ 0 → u ≠ C.rootId) := fun u hu =>
    ⟨fun h => hdisj_sl_p u hu p_id rfl h,
     fun h => hdisj_all u (Or.inl hu) x (Or.inl (Or.inr rfl)) h,
     fun hcz h => by
       cases C with
       | leaf => exact hcz rfl
       | node cid cl cr =>
           simp only [AuxTree.rootId] at h
           have hm : u ∈ (AuxTree.node cid cl cr).toList := h ▸ by simp [AuxTree.toList]
           exact hdisj_all u (Or.inl hu) u (Or.inl (Or.inl hm)) rfl⟩
  have hD_disj : ∀ u ∈ D.toList, u ≠ p_id ∧ u ≠ x ∧ (C.rootId ≠ 0 → u ≠ C.rootId) := fun u hu =>
    ⟨fun h => hdisj_all p_id (Or.inr rfl) u (Or.inr hu) h.symm,
     fun h => hdisj_Cx_D x (Or.inr rfl) u hu h.symm,
     fun hcz h => by
       cases C with
       | leaf => exact hcz rfl
       | node cid cl cr =>
           simp only [AuxTree.rootId] at h
           have hm : u ∈ (AuxTree.node cid cl cr).toList := h ▸ by simp [AuxTree.toList]
           exact hdisj_Cx_D u (Or.inl hm) u hu rfl⟩
  have hC_disj : ∀ u ∈ C.toList, u ≠ p_id ∧ u ≠ x := fun u hu =>
    ⟨fun h => hdisj_all p_id (Or.inr rfl) u (Or.inl (Or.inl hu)) h.symm,
     fun h => hdisj_C_x u hu x rfl h⟩
  have hsl_mid := sibling_preserve_mid hsl_m hsl_disj
    (fun u off hoff hp hx hc => hagree u off hoff (fun h => absurd h hp) (fun h => absurd h hx) (fun h1 h2 => absurd h2 (hc h1)))
    hle_mid hheap_mid
  have hD_mid := sibling_preserve_mid hD_m hD_disj
    (fun u off hoff hp hx hc => hagree u off hoff (fun h => absurd h hp) (fun h => absurd h hx) (fun h1 h2 => absurd h2 (hc h1)))
    hle_mid hheap_mid
  have hC_mid := movedChild_reparent_mid hC_m hC_nd hC_disj
    (fun hC_ne => hc_par_mid (by cases C with | leaf => exact absurd rfl hC_ne | node _ _ _ => exact Nat.ne_of_gt hC_m.1))
    (fun u off hoff hp hx hc => hagree u off hoff (fun h => absurd h hp) (fun h => absurd h hx) (fun h1 h2 => hc h1 h2))
    hle_mid hheap_mid
  have hx_right_mid : nodeField st_mid.mem nodesBase x OFF_RIGHT = D.rootId := by
    rw [hagree x OFF_RIGHT (by decide) (fun h => absurd h hpx.symm) (fun _ => ⟨by decide, by decide⟩)
      (fun _ h => absurd h hc_ne_x.symm)]
    exact hxR0
  have hp_left_mid : nodeField st_mid.mem nodesBase p_id OFF_LEFT = sl.rootId := by
    rw [hagree p_id OFF_LEFT (by decide) (fun _ => ⟨by decide, by decide⟩) (fun h => absurd h hpx)
      (fun _ h => absurd h hc_ne_p.symm)]
    exact hpL0
  let s' := AuxTree.node x (AuxTree.node p_id sl C) D
  have hs'_eq : s' = (t.findSubtree p_id).rotateAt x := by
    rw [hsub_eq, AuxTree.rotateAt_zigLeft sl C D hpx hsl_cond]
  have hs'_perm : s'.toList.Perm (t.findSubtree p_id).toList := by
    rw [hs'_eq]; exact AuxTree.rotateAt_toList_perm x _
  have hs'_eval : s'.evalInorder (revFlag st_mid.mem nodesBase) false =
      (t.findSubtree p_id).evalInorder (revFlag mem₀ nodesBase) false := by
    have hrev_agree : ∀ u ∈ s'.toList, revFlag st_mid.mem nodesBase u = revFlag mem₀ nodesBase u := fun u hu => by
      have hu_le := (ht.nodup_perm_mem (AuxTree.findSubtree_subset (hs'_perm.mem_iff.1 hu))).2
      simp [revFlag, hns_mid u hu_le OFF_REV (by decide)]
    rw [AuxTree.evalInorder_agree _ (revFlag mem₀ nodesBase) _ false hrev_agree, hsub_eq]
    have hrx : revFlag mem₀ nodesBase x = false := by simp [revFlag, hx_rev0]
    have hrp : revFlag mem₀ nodesBase p_id = false := by simp [revFlag, hp_rev0]
    simp [s', AuxTree.evalInorder, hrx, hrp, List.append_assoc]
  have hout_mid : ∀ u ≤ cap, u ∉ (t.findSubtree p_id).toList → ∀ off < NODE_STRIDE,
      nodeField st_mid.mem nodesBase u off = nodeField mem₀ nodesBase u off := fun u _ hu off hoff => by
    rw [hsub_eq] at hu
    refine hagree u off hoff ?_ ?_ ?_
    · intro h; exact (hu (h ▸ by simp [AuxTree.toList])).elim
    · intro h; exact (hu (h ▸ by simp [AuxTree.toList])).elim
    · intro hcz h
      cases C with
      | leaf => exact absurd rfl hcz
      | node cid _ _ =>
          simp only [AuxTree.rootId] at h
          exact (hu (h ▸ by simp [AuxTree.toList])).elim
  rcases rotateTail_runs pr sp mem₀ hp_ok hbase hnb hL_hdr harena hz hhp_lt h0 ht hnd hx_mem
      hx_ne_root hp_def hg_def hpp_def st_mid
      (Or.inl ⟨rfl, hx_left_mid, hx_right_mid, hD_mid⟩)
      hs'_eq hs'_perm hs'_eval hp_left_mid hp_right_mid hsl_mid hC_mid
      hx_pp_mid hp_pp_mid hx_rev0 hp_rev0 hx_ht0 hp_ht0 hns_mid hout_mid hpre_mid
      (hregs_mid 0 (by decide) |>.trans hr0) (hregs_mid 1 (by decide) |>.trans hr1)
      (hregs_mid 2 (by decide) |>.trans hr2) (hregs_mid 3 (by decide) |>.trans hr3)
      (hregs_mid 4 (by decide) |>.trans hr4) (hregs_mid 5 (by decide) |>.trans hr5) ω with
    ⟨st', c_tail, hr_tail, hc_tail, hhp_ge, hhp_le, ht_rot, hperm_rot, heval_rot,
     hsteps_rot, hns_rot, hout_rot, hlct_rot⟩
  exact ⟨st', (1 + c_br + 1) + c_tail + 1,
    runs_seq_iff.mpr (Or.inr ⟨st_mid, _, _, hr_cond, hr_tail, rfl⟩),
    by omega, hhp_ge, hhp_le, ht_rot, hperm_rot, heval_rot, hsteps_rot, hns_rot, hout_rot, hlct_rot⟩

/-- Executing `rotateBody` performs one auxiliary-tree rotation at `x`, maintaining
`TreeMemMatch`, path sequences, `evalMemSteps`, `LctFrame`, and non-structural/outside fields
within budget `K_ROTATE L` (`8 * L` heap growth). -/
theorem rotateBody_runs {w h L nodesBase cap pp₀ x : ℕ}
    (pr : Program) (sp : SplayProcs) (mem₀ : ℕ → ℕ) (pos : ℕ)
    (hp_ok : SplayProgramOk w h pr sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase)
    (hL_hdr : mem₀ (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₀ (nodesBase - 1))
    (hz : ZeroFrom mem₀ (mem₀ (nodesBase - 1)))
    (hhp_lt : mem₀ (nodesBase - 1) + 8 * L < 2 ^ w)
    (h0 : SlotZeroOk mem₀ nodesBase)
    {t : AuxTree} (ht : TreeMemMatch w h L mem₀ nodesBase cap t 0 pp₀) (hnd : t.toList.Nodup)
    (hx : x ∈ t.toList)
    (hclean : x ≠ t.rootId →
      (revFlag mem₀ nodesBase x = false ∧ nodeField mem₀ nodesBase x OFF_HAS_TAG = 0) ∧
      (revFlag mem₀ nodesBase (t.parentIn x 0) = false ∧
        nodeField mem₀ nodesBase (t.parentIn x 0) OFF_HAS_TAG = 0))
    (ω : ℕ → Bool) :
    ∃ st' c,
      Runs w pr ω (rotateBody sp) (startState [nodesBase, x] mem₀ pos) (.returned 0) st' c ∧
      c + (st'.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤ K_ROTATE L ∧
      mem₀ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      st'.mem (nodesBase - 1) ≤ mem₀ (nodesBase - 1) + 8 * L ∧
      TreeMemMatch w h L st'.mem nodesBase cap (t.rotateAt x) 0 pp₀ ∧
      (t.rotateAt x).toList.Perm t.toList ∧
      (t.rotateAt x).evalInorder (revFlag st'.mem nodesBase) false =
        t.evalInorder (revFlag mem₀ nodesBase) false ∧
      evalMemSteps st'.mem nodesBase h L (t.rotateAt x) false 0 =
        evalMemSteps mem₀ nodesBase h L t false 0 ∧
      (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) mem₀ st'.mem := by
  rcases ht.nodup_perm_mem hx with ⟨hx1, hx2⟩
  by_cases hxr : x = t.rootId
  · have hx_par0 : nodeField mem₀ nodesBase x OFF_PARENT = 0 :=
      (ht.parent_zero_iff_root hnd hx).2 hxr
    rcases rotateBody_zero_runs pr sp mem₀ pos x hbase hx2 hx_par0 ω with ⟨st', c, hr, hc, hm⟩
    have hrot_id : t.rotateAt x = t := by
      cases t with
      | leaf => simp [AuxTree.toList] at hx
      | node r l rr => simp only [AuxTree.rootId] at hxr; subst hxr; exact AuxTree.rotateAt_root x l rr
    have hlct : LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) mem₀ st'.mem := by
      rw [hm]
      exact lctFrame_of_memPreservedOutside (fun _ _ => rfl) (by unfold NODE_STRIDE; omega) harena hz
    refine ⟨st', c, hr, ?_, by rw [hm], by rw [hm]; omega, ?_, ?_, ?_, ?_, ?_, ?_, hlct⟩
    · rw [hm, Nat.sub_self, Nat.add_zero]; unfold K_ROTATE; omega
    · rw [hrot_id, hm]; exact ht
    · rw [hrot_id]
    · rw [hrot_id, hm]
    · rw [hrot_id, hm]
    · intro u _ off _; rw [hm]
    · intro u _ _ off _; rw [hm]
  · let p_id := t.parentIn x 0
    let g_id := t.parentIn p_id 0
    let pp_p := if t.rootId = p_id then pp₀ else 0
    have hp_mem : p_id ∈ t.toList := (AuxTree.parentIn_mem_and_depth hnd hx hxr).1
    rcases ht.nodup_perm_mem hp_mem with ⟨hp1, hp2⟩
    have hx_par : nodeField mem₀ nodesBase x OFF_PARENT = p_id :=
      AuxTree.parentIn_eq_nodeField ht hx
    have hp_par : nodeField mem₀ nodesBase p_id OFF_PARENT = g_id :=
      AuxTree.parentIn_eq_nodeField ht hp_mem
    have hm_p := AuxTree.findSubtree_match ht hp_mem
    have hp_ppar : nodeField mem₀ nodesBase p_id OFF_PPAR = pp_p := by
      rcases AuxTree.findSubtree_mem_toList hp_mem with ⟨hne, hr⟩
      cases hs : t.findSubtree p_id with
      | leaf => exact absurd hs hne
      | node y sl sr =>
          rw [hs] at hm_p hr
          simp only [AuxTree.rootId] at hr; subst hr
          exact hm_p.2.2.2.2.2.1
    rcases hclean hxr with ⟨⟨hx_rev_f, hx_ht0⟩, ⟨hp_rev_f, hp_ht0⟩⟩
    have hx_rev0 : nodeField mem₀ nodesBase x OFF_REV = 0 := by
      simpa [revFlag, bne_eq_false_iff_eq] using hx_rev_f
    have hp_rev0 : nodeField mem₀ nodesBase p_id OFF_REV = 0 := by
      simpa [revFlag, bne_eq_false_iff_eq] using hp_rev_f
    rcases AuxTree.parentIn_child_cases hnd hx hxr (rfl : p_id = _) with ⟨sl, sr, hsub_eq, hcas⟩
    rw [hsub_eq] at hm_p
    rcases hm_p with ⟨_, _, _, hpR0, _⟩
    have hsub_nd := AuxTree.findSubtree_nodup (subId := p_id) hnd
    rw [hsub_eq] at hsub_nd
    let ptrX := nodesBase + NODE_STRIDE * x
    let ptrP := nodesBase + NODE_STRIDE * p_id
    let pRight := nodeField mem₀ nodesBase p_id OFF_RIGHT
    let mem_pre := Function.update (Function.update mem₀ (ptrX + OFF_PPAR) pp_p) (ptrP + OFF_PPAR) 0
    let st_pre : State := {
      mem := mem_pre,
      regs := Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (startState [nodesBase, x] mem₀ pos).regs 2 ptrX) 3 p_id)
        4 ptrP) 5 g_id) 6 pp_p) 7 pRight) 8 (if x = pRight then 1 else 0),
      pos := pos }
    have hr_pre : st_pre.regs 0 = nodesBase ∧ st_pre.regs 1 = x ∧ st_pre.regs 2 = ptrX ∧
        st_pre.regs 3 = p_id ∧ st_pre.regs 4 = ptrP ∧ st_pre.regs 5 = g_id := by
      simp [st_pre, startState]
    have runMid :
        (∃ st' c_rest,
          Runs w pr ω (rotateTailStmt sp) st_pre (.returned 0) st' c_rest ∧
          c_rest + (st'.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤ 2 * K_PULL L + 95 ∧
          mem₀ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
          st'.mem (nodesBase - 1) ≤ mem₀ (nodesBase - 1) + 8 * L ∧
          TreeMemMatch w h L st'.mem nodesBase cap (t.rotateAt x) 0 pp₀ ∧
          (t.rotateAt x).toList.Perm t.toList ∧
          (t.rotateAt x).evalInorder (revFlag st'.mem nodesBase) false =
            t.evalInorder (revFlag mem₀ nodesBase) false ∧
          evalMemSteps st'.mem nodesBase h L (t.rotateAt x) false 0 =
            evalMemSteps mem₀ nodesBase h L t false 0 ∧
          (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
            nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
          (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
            nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
          LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
            (nodesBase - 1) mem₀ st'.mem) →
        ∃ st' c,
          Runs w pr ω (rotateBody sp) (startState [nodesBase, x] mem₀ pos) (.returned 0) st' c ∧
          c + (st'.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤ K_ROTATE L ∧
          mem₀ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
          st'.mem (nodesBase - 1) ≤ mem₀ (nodesBase - 1) + 8 * L ∧
          TreeMemMatch w h L st'.mem nodesBase cap (t.rotateAt x) 0 pp₀ ∧
          (t.rotateAt x).toList.Perm t.toList ∧
          (t.rotateAt x).evalInorder (revFlag st'.mem nodesBase) false =
            t.evalInorder (revFlag mem₀ nodesBase) false ∧
          evalMemSteps st'.mem nodesBase h L (t.rotateAt x) false 0 =
            evalMemSteps mem₀ nodesBase h L t false 0 ∧
          (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
            nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
          (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
            nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
          LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
            (nodesBase - 1) mem₀ st'.mem := by
      intro res
      rcases res with ⟨st', c_rest, hr_rest, hc_rest, hge, hle, ht', hperm', hev', hst', hns', hout', hlct'⟩
      rcases rotatePrefix_exec pr mem₀ pos hbase hx2 hp1 hp2
          hx_par hp_par hp_ppar (rotateTailStmt sp) ω (.returned 0) st' c_rest hr_rest with
        ⟨c_full, hc_full, hr_full⟩
      exact ⟨st', c_full, hr_full, by unfold K_ROTATE; omega,
        hge, hle, ht', hperm', hev', hst', hns', hout', hlct'⟩
    rcases hcas with ⟨A, B, rfl⟩ | ⟨hsl_cond, C, D, rfl⟩
    · have hne_pR : x ≠ pRight := by
        intro h
        have hx_sr : x = sr.rootId := h.trans hpR0
        simp only [AuxTree.toList, List.nodup_append, List.nodup_cons, List.mem_append,
          List.mem_singleton] at hsub_nd
        cases sr with
        | leaf => simp [AuxTree.rootId] at hx_sr; omega
        | node sid _ _ =>
            simp only [AuxTree.rootId] at hx_sr; subst hx_sr
            exact hsub_nd.2.2 x (Or.inl (Or.inl (Or.inr rfl))) x (by simp [AuxTree.toList]) rfl
      have hr8 : st_pre.regs 8 = 0 := by simp [st_pre, hne_pR]
      exact runMid (rotateMid_zigRight pr sp mem₀ hp_ok hbase hnb hL_hdr harena hz hhp_lt h0
        ht hnd hx hxr rfl rfl rfl hx_rev0 hp_rev0 hx_ht0 hp_ht0 hsub_eq st_pre rfl
        hr_pre.1 hr_pre.2.1 hr_pre.2.2.1 hr_pre.2.2.2.1 hr_pre.2.2.2.2.1 hr_pre.2.2.2.2.2 hr8 ω)
    · have heq_pR : x = pRight := by
        simpa [AuxTree.rootId] using hpR0.symm
      have hr8 : st_pre.regs 8 = 1 := by simp [st_pre, heq_pR]
      exact runMid (rotateMid_zigLeft pr sp mem₀ hp_ok hbase hnb hL_hdr harena hz hhp_lt h0
        ht hnd hx hxr rfl rfl rfl hx_rev0 hp_rev0 hx_ht0 hp_ht0 hsl_cond hsub_eq st_pre rfl
        hr_pre.1 hr_pre.2.1 hr_pre.2.2.1 hr_pre.2.2.2.1 hr_pre.2.2.2.2.1 hr_pre.2.2.2.2.2 hr8 ω)

end

end MinCostFlow.LinkCut.Prog
